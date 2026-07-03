"""Server-side Verso rendering of the number field Lean certificates.

The 'Verso certificate' download renders the same generated Lean code as
the Lean certificate zip into an interactive HTML page (accurate syntax
highlighting, hovers, and Alectryon-style proof states).  Producing the
page requires elaborating the certificate through the Lean kernel, so a
successfully rendered page *is* a verification of the interpolated
database values -- with no setup on the reader's side.

A render takes minutes (a lake build), so it runs as a detached
``verso_build.py render`` worker against a persistent, pre-built Lake
project (the "build root", created once with ``verso_build.py
bootstrap``); requests observe the worker through a ``status.json`` state
machine and serve the published static site from a per-certificate cache
directory.  The feature is off unless ``LMFDB_VERSO_CERT_ENABLED`` is set
and the build root exists, so deployments without a Lean toolchain are
unaffected.

This module deliberately does not touch ``lean_certificate.py``: editing
that file would change ``_source_digest`` and invalidate every cached
certificate project.
"""

import functools
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

from flask import abort, send_from_directory

from lmfdb.number_fields.lean_certificate import (
    LeanCertificateError,
    _certificate_digest,
    _file_lock,
    _read_text,
    _write_text,
    _zk_strings,
    get_or_create_certificate_project,
    label_to_lean_name,
    lean_certificate_available,
    lean_interpolate,
)

_HERE = os.path.dirname(os.path.abspath(__file__))
_WORKER = os.path.join(_HERE, "verso_build.py")
_DEFAULT_CACHE = os.path.join("/tmp", "lmfdb_verso_certificates")
_BOOTSTRAP_SENTINEL = ".bootstrap_ready"
# The worker refreshes status.json at least every ~20s (heartbeat), so a
# 'running' render whose file has not moved in this long is dead.
_STALE_SECONDS = 300
_LOG_TAIL_LINES = 50


class VersoCertificateError(LeanCertificateError):
    pass


def verso_certificate_enabled():
    """Cheap gate (env var + two stat calls), safe on every page render."""
    if os.environ.get("LMFDB_VERSO_CERT_ENABLED", "").lower() in ("", "0", "false", "no"):
        return False
    root = _build_root()
    return (bool(root)
            and os.path.isfile(os.path.join(root, _BOOTSTRAP_SENTINEL))
            and shutil.which("lake") is not None)


def verso_certificate_available(label, nf):
    """A Verso certificate can be offered either by rendering it here (the
    full pipeline is enabled) or by linking a pre-rendered copy hosted
    elsewhere -- the latter lets deployments without a Lean toolchain (such
    as the lmfdb.xyz dev servers) still serve the demo fields."""
    if not lean_certificate_available(label, nf):
        return False
    return verso_certificate_enabled() or prebuilt_verso_url(label) is not None


def prebuilt_verso_url(label):
    """URL of an externally hosted pre-rendered Verso certificate, if one is
    registered for this label in verso_prebuilt.json."""
    return _prebuilt_renders().get(label)


@functools.lru_cache(maxsize=None)
def _prebuilt_renders():
    try:
        with open(os.path.join(_HERE, "verso_prebuilt.json")) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return {}


def get_verso_render_status(label, nf):
    """The render's state as seen from the web process: a dict with
    ``state`` in absent/running/failed/ready plus supporting fields."""
    render_dir = _render_dir(label, nf)
    if os.path.isfile(os.path.join(render_dir, ".ready")) and \
            os.path.isdir(os.path.join(render_dir, "html")):
        meta = _render_meta(render_dir)
        return {"state": "ready",
                "entry_html": meta.get("entry_html") or _default_entry(label)}
    status_path = os.path.join(render_dir, "status.json")
    if not os.path.isfile(status_path):
        return {"state": "absent"}
    try:
        with open(status_path) as fh:
            data = json.load(fh)
    except (OSError, ValueError):
        return {"state": "failed", "error": "Unreadable render status file",
                "log_tail": _log_tail(render_dir)}
    status = {"state": data.get("state"), "phase": data.get("phase"),
              "started": data.get("started"), "updated": data.get("updated"),
              "error": data.get("error")}
    if status["state"] == "running" and _worker_disappeared(data):
        status.update(state="failed",
                      error="The render process disappeared without reporting an error")
    if status["state"] not in ("running", "failed"):
        # 'ready' without the .ready sentinel, or an unknown state
        status.update(state="failed",
                      error=status.get("error") or "Render finished in an inconsistent state")
    if status["state"] == "failed":
        status["log_tail"] = _log_tail(render_dir)
    return status


def start_verso_render(label, nf):
    """Start a detached render worker unless one is running or done;
    returns the resulting status.  Raises the lean_certificate errors if
    the certificate itself cannot be generated."""
    if not (verso_certificate_enabled() and lean_certificate_available(label, nf)):
        raise VersoCertificateError(f"Verso certificates are not enabled for {label}")
    render_dir = _render_dir(label, nf)
    os.makedirs(os.path.dirname(render_dir), exist_ok=True)
    with _file_lock(render_dir + ".spawn.lock"):
        status = get_verso_render_status(label, nf)
        if status["state"] in ("ready", "running"):
            return status
        if status["state"] == "failed":
            _discard_render_dir(render_dir)
        cert_dir = get_or_create_certificate_project(label, nf)
        u = label_to_lean_name(label)
        nf_name = f"NF{u}"
        src_dir = os.path.join(render_dir, "src")
        os.makedirs(render_dir, exist_ok=True)
        shutil.copytree(os.path.join(cert_dir, "IdealArithmetic", "Examples", nf_name),
                        src_dir)
        # The kernel must check the actual database values, so stage the
        # entry point with the placeholders filled in (exactly the file the
        # Lean certificate zip would contain).
        entry_path = os.path.join(src_dir, f"Results{u}.lean")
        _write_text(entry_path, lean_interpolate(_read_text(entry_path), nf))
        status_path = os.path.join(render_dir, "status.json")
        # Written before the spawn; the worker merges over it and records
        # its own pid, so this must not be rewritten afterwards.
        _write_json(status_path, {"state": "running", "phase": "spawned",
                                  "started": time.time(), "updated": time.time()})
        with open(os.path.join(render_dir, "render.log"), "a") as log_fh:
            subprocess.Popen(
                [sys.executable, _WORKER, "render",
                 "--build-root", _build_root(),
                 "--src", src_dir,
                 "--nf-name", nf_name,
                 "--out", render_dir,
                 "--status", status_path],
                stdout=log_fh, stderr=subprocess.STDOUT,
                start_new_session=True)
    return get_verso_render_status(label, nf)


def reset_failed_render(label, nf):
    """Move a failed render aside so the next request starts clean."""
    render_dir = _render_dir(label, nf)
    if get_verso_render_status(label, nf)["state"] == "failed":
        _discard_render_dir(render_dir)


def serve_verso_asset(label, nf, asset):
    render_dir = _render_dir(label, nf)
    if not os.path.isfile(os.path.join(render_dir, ".ready")):
        return abort(404, f"No rendered Verso certificate for {label}")
    # send_from_directory refuses paths that escape the directory
    return send_from_directory(os.path.join(render_dir, "html"), asset)


def verso_entry_url_asset(label, nf):
    """The asset path of the certificate's entry page, for redirects."""
    meta = _render_meta(_render_dir(label, nf))
    return meta.get("entry_html") or _default_entry(label)


# ---------------------------------------------------------------------------


def _build_root():
    return os.environ.get("LMFDB_VERSO_BUILD_ROOT", "")


def _bootstrap_meta():
    path = os.path.join(_build_root(), _BOOTSTRAP_SENTINEL)
    try:
        with open(path) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        raise VersoCertificateError(f"Verso build root is not bootstrapped ({path})")


def _render_dir(label, nf):
    root = os.environ.get("LMFDB_VERSO_CERT_CACHE", _DEFAULT_CACHE)
    return os.path.join(root, label, _render_digest(label, nf))


def _render_digest(label, nf):
    boot = _bootstrap_meta()
    h = hashlib.sha256()
    h.update(_certificate_digest(label, nf, _zk_strings(nf)).encode())
    h.update(_pipeline_digest().encode())
    h.update(str(boot.get("verso_rev")).encode())
    h.update(str(boot.get("lean_toolchain")).encode())
    return h.hexdigest()[:16]


@functools.lru_cache(maxsize=None)
def _pipeline_digest():
    h = hashlib.sha256()
    for path in [__file__, _WORKER]:
        h.update(_read_text(path).encode())
    return h.hexdigest()


def _default_entry(label):
    u = label_to_lean_name(label)
    return f"IdealArithmetic/Examples/NF{u}/Results{u}/index.html"


def _render_meta(render_dir):
    try:
        with open(os.path.join(render_dir, "meta.json")) as fh:
            return json.load(fh)
    except (OSError, ValueError):
        return {}


def _worker_disappeared(status_data):
    updated = status_data.get("updated") or 0
    if time.time() - updated > _STALE_SECONDS:
        return True
    pid = status_data.get("pid")
    if not pid:
        return False
    try:
        os.kill(int(pid), 0)
    except ProcessLookupError:
        return True
    except (PermissionError, ValueError):
        pass
    return False


def _log_tail(render_dir, lines=_LOG_TAIL_LINES):
    path = os.path.join(render_dir, "render.log")
    try:
        with open(path, "rb") as fh:
            fh.seek(0, os.SEEK_END)
            fh.seek(max(0, fh.tell() - 16384))
            text = fh.read().decode("utf-8", errors="replace")
    except OSError:
        return ""
    return "\n".join(text.splitlines()[-lines:])


def _discard_render_dir(render_dir):
    if os.path.isdir(render_dir):
        os.replace(render_dir, f"{render_dir}.failed-{int(time.time())}")


def _write_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(data, fh, indent=2)
    os.replace(tmp, path)
