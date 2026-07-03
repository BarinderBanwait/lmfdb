#!/usr/bin/env python3
"""Bootstrap and render worker for server-side Verso certificates.

This file is run as a standalone script -- as a one-time ``bootstrap``
command from a terminal, and as a detached ``render`` worker spawned by
``verso_certificate.py`` for each certificate.  It must stay importable
without the lmfdb package (``import lmfdb`` connects to the database) and
without sage, so it only uses the standard library.

The render pipeline (discovered empirically against verso v4.30.0-rc1):

  1. copy the generated ``NF<u>`` sources into the build root's
     ``IdealArithmetic/Examples/``,
  2. ``lake build +IdealArithmetic.Examples.NF<u>.<Mod>`` for every module --
     this is the kernel check of the certificate,
  3. build the modules' ``literate`` facets (verso-literate re-elaborates
     each module, capturing highlighting and proof states as JSON under
     ``.lake/build/literate/``),
  4. run the ``verso-html`` binary on a filtered copy of the literate data
     (it renders *everything* it finds, and the build root accumulates
     other labels' data), producing a static site whose pages carry a
     relative ``<base>`` tag, so it can be served under any URL prefix,
  5. atomically publish the site to the render directory.

Progress is reported through an atomically-rewritten ``status.json`` whose
``updated`` field doubles as a heartbeat while long lake builds run.
"""

import argparse
import json
import os
import shutil
import subprocess
import sys
import time

_HERE = os.path.dirname(os.path.abspath(__file__))
_DEFAULT_TEMPLATE = os.path.join(_HERE, "lean_certificates", "project_template")
_VERSO_GIT_URL = "https://github.com/leanprover/verso.git"
_BOOTSTRAP_SENTINEL = ".bootstrap_ready"
_RENDER_LOCK = ".render.lock"
_LOCK_POLL_SECONDS = 2.0
_HEARTBEAT_SECONDS = 20.0
_EXAMPLES_REL = os.path.join("IdealArithmetic", "Examples")
_VERSO_HTML_BIN_REL = os.path.join(".lake", "packages", "verso", ".lake", "build", "bin", "verso-html")


class VersoBuildError(RuntimeError):
    pass


def _log(msg):
    print(f"[verso_build {time.strftime('%H:%M:%S')}] {msg}", flush=True)


def _run(cmd, cwd, timeout=None, status=None, phase=None):
    """Run a subprocess with output inherited (the worker's stdout is the
    render log), refreshing the status heartbeat while it runs."""
    _log("$ " + " ".join(cmd))
    proc = subprocess.Popen(cmd, cwd=cwd)
    deadline = time.time() + timeout if timeout else None
    while True:
        try:
            proc.wait(timeout=_HEARTBEAT_SECONDS)
            break
        except subprocess.TimeoutExpired:
            if status:
                _write_status(status, state="running", phase=phase)
            if deadline and time.time() > deadline:
                proc.kill()
                proc.wait()
                raise VersoBuildError(f"Timed out after {timeout}s: {' '.join(cmd)}")
    if proc.returncode != 0:
        raise VersoBuildError(f"Command failed (exit {proc.returncode}): {' '.join(cmd)}")


def _write_status(path, **fields):
    now = time.time()
    current = {}
    if os.path.isfile(path):
        try:
            with open(path) as fh:
                current = json.load(fh)
        except (OSError, ValueError):
            current = {}
    current.setdefault("started", now)
    current.setdefault("pid", os.getpid())
    current.update(fields)
    current["updated"] = now
    tmp = path + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(current, fh, indent=2)
    os.replace(tmp, path)


def _read_toolchain(project_dir):
    with open(os.path.join(project_dir, "lean-toolchain")) as fh:
        return fh.read().strip()


def _verso_tag(toolchain):
    # "leanprover/lean4:v4.30.0-rc1" -> "v4.30.0-rc1"; verso tags track Lean releases.
    return toolchain.rsplit(":", 1)[-1]


# ---------------------------------------------------------------------------
# bootstrap


def _copy_template(template_dir, build_root):
    ignored = {"__pycache__", ".DS_Store", ".git", ".lake", "metadata.json"}

    def ignore(path, names):
        skip = set(ignored)
        if os.path.normpath(path) == os.path.normpath(template_dir):
            skip.add("README.md")
        if os.path.basename(path) == "Examples":
            skip.update(n for n in names if n.startswith("NF"))
        return skip.intersection(names)

    shutil.copytree(template_dir, build_root, ignore=ignore, dirs_exist_ok=True)


def bootstrap_build_root(build_root, template_dir=_DEFAULT_TEMPLATE, force=False):
    build_root = os.path.abspath(build_root)
    sentinel = os.path.join(build_root, _BOOTSTRAP_SENTINEL)
    if os.path.isfile(sentinel) and not force:
        _log(f"Build root {build_root} already bootstrapped (use --force to redo)")
        return
    _log(f"Bootstrapping Verso build root at {build_root}")
    _copy_template(template_dir, build_root)

    toolchain = _read_toolchain(build_root)
    tag = _verso_tag(toolchain)
    lakefile = os.path.join(build_root, "lakefile.lean")
    with open(lakefile) as fh:
        lakefile_src = fh.read()
    if "require verso" not in lakefile_src:
        with open(lakefile, "a") as fh:
            fh.write(f'\nrequire verso from git\n  "{_VERSO_GIT_URL}" @ "{tag}"\n')
        _log(f"Added verso @ {tag} to lakefile.lean")

    # Verified on v4.30.0-rc1: `lake update verso` adds only verso, MD4Lean and
    # subverso to the manifest, leaving the mathlib pin and toolchain untouched.
    _run(["lake", "update", "verso"], cwd=build_root)
    _run(["lake", "exe", "cache", "get"], cwd=build_root)
    _log("Building the IdealArithmetic library (this is the slow, one-time step)...")
    _run(["lake", "build"], cwd=build_root)
    _log("Building verso executables...")
    _run(["lake", "build", "verso-html", "verso-literate"], cwd=build_root)
    if not os.path.isfile(os.path.join(build_root, _VERSO_HTML_BIN_REL)):
        raise VersoBuildError(f"verso-html binary not found at {_VERSO_HTML_BIN_REL} after build")

    with open(os.path.join(build_root, "lake-manifest.json")) as fh:
        packages = json.load(fh)["packages"]
    verso_rev = next(p["rev"] for p in packages if p["name"] == "verso")
    meta = {"verso_rev": verso_rev, "verso_tag": tag, "lean_toolchain": toolchain,
            "completed": time.time()}
    tmp = sentinel + ".tmp"
    with open(tmp, "w") as fh:
        json.dump(meta, fh, indent=2)
    os.replace(tmp, sentinel)
    _log(f"Bootstrap complete; verso rev {verso_rev}")


# ---------------------------------------------------------------------------
# render


def _acquire_lock(path, timeout, status=None, phase=None):
    deadline = time.time() + timeout
    while True:
        try:
            fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.write(fd, str(os.getpid()).encode())
            os.close(fd)
            return
        except FileExistsError:
            if time.time() >= deadline:
                raise VersoBuildError(
                    f"Timed out after {timeout}s waiting for the build slot ({path})")
            if status:
                _write_status(status, state="running", phase=phase)
            time.sleep(_LOCK_POLL_SECONDS)


def _module_names(src_dir, nf_name):
    stems = sorted(os.path.splitext(f)[0] for f in os.listdir(src_dir) if f.endswith(".lean"))
    if not stems:
        raise VersoBuildError(f"No .lean files in {src_dir}")
    return [f"IdealArithmetic.Examples.{nf_name}.{stem}" for stem in stems]


def render_certificate(build_root, src_dir, nf_name, out_dir, status_path,
                       lock_timeout, build_timeout):
    build_root = os.path.abspath(build_root)
    src_dir = os.path.abspath(src_dir)
    out_dir = os.path.abspath(out_dir)
    modules = _module_names(src_dir, nf_name)
    entry_rel = None
    for mod in modules:
        if mod.rsplit(".", 1)[-1].startswith("Results"):
            entry_rel = os.path.join(*mod.split(".")) + os.sep + "index.html"
    if entry_rel is None:
        raise VersoBuildError(f"No Results module among {modules}")

    lock_path = os.path.join(build_root, _RENDER_LOCK)
    _write_status(status_path, state="running", phase="waiting-for-build-slot")
    _acquire_lock(lock_path, lock_timeout, status=status_path,
                  phase="waiting-for-build-slot")
    try:
        _write_status(status_path, state="running", phase="staging")
        dest = os.path.join(build_root, _EXAMPLES_REL, nf_name)
        if os.path.isdir(dest):
            shutil.rmtree(dest)
        shutil.copytree(src_dir, dest)

        # The olean builds are the kernel check of the certificate's theorems
        # (whose statements carry the interpolated database values).
        _write_status(status_path, state="running", phase="lake-build")
        _run(["lake", "build"] + [f"+{m}" for m in modules], cwd=build_root,
             timeout=build_timeout, status=status_path, phase="lake-build")

        _write_status(status_path, state="running", phase="literate")
        _run(["lake", "build"] + [f"+{m}:literate" for m in modules], cwd=build_root,
             timeout=build_timeout, status=status_path, phase="literate")

        _write_status(status_path, state="running", phase="verso-html")
        # verso-html renders every module it finds in its input directory, and
        # the shared build root accumulates literate data for other labels, so
        # render from a filtered copy containing only this certificate.
        lit_src = os.path.join(build_root, ".lake", "build", "literate",
                               _EXAMPLES_REL, nf_name)
        if not os.path.isdir(lit_src):
            raise VersoBuildError(f"Literate data missing at {lit_src}")
        lit_tmp = os.path.join(out_dir, "lit.tmp")
        html_tmp = os.path.join(out_dir, "html.tmp")
        for tmp in (lit_tmp, html_tmp):
            if os.path.isdir(tmp):
                shutil.rmtree(tmp)
        shutil.copytree(lit_src, os.path.join(lit_tmp, _EXAMPLES_REL, nf_name))
        _run([os.path.join(build_root, _VERSO_HTML_BIN_REL), lit_tmp, html_tmp],
             cwd=build_root, timeout=build_timeout, status=status_path, phase="verso-html")

        _write_status(status_path, state="running", phase="publish")
        entry = os.path.join(html_tmp, entry_rel)
        if not os.path.isfile(entry):
            raise VersoBuildError(f"Rendered site is missing the entry page {entry_rel}")
        meta = {"entry_html": entry_rel.replace(os.sep, "/"), "nf_name": nf_name,
                "modules": modules, "finished": time.time()}
        with open(os.path.join(out_dir, "meta.json"), "w") as fh:
            json.dump(meta, fh, indent=2)
        shutil.rmtree(lit_tmp)
        html_dir = os.path.join(out_dir, "html")
        if os.path.isdir(html_dir):
            shutil.rmtree(html_dir)
        os.replace(html_tmp, html_dir)
        with open(os.path.join(out_dir, ".ready"), "w"):
            pass
        _write_status(status_path, state="ready", phase="done", error=None)
        _log("Render complete")
    finally:
        try:
            with open(lock_path) as fh:
                owner = fh.read().strip()
            if owner == str(os.getpid()):
                os.unlink(lock_path)
        except FileNotFoundError:
            pass


# ---------------------------------------------------------------------------


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    boot = sub.add_parser("bootstrap", help="Create and fully build the persistent build root")
    boot.add_argument("--build-root", required=True)
    boot.add_argument("--template", default=_DEFAULT_TEMPLATE)
    boot.add_argument("--force", action="store_true")

    rend = sub.add_parser("render", help="Render one certificate (spawned by the web server)")
    rend.add_argument("--build-root", required=True)
    rend.add_argument("--src", required=True, help="Directory of generated NF<u> .lean sources")
    rend.add_argument("--nf-name", required=True, help="Example directory name, e.g. NF2_0_231_1")
    rend.add_argument("--out", required=True, help="Render directory (html/, meta.json, .ready)")
    rend.add_argument("--status", required=True, help="Path of status.json to maintain")
    rend.add_argument("--lock-timeout", type=float,
                      default=float(os.environ.get("LMFDB_VERSO_LOCK_TIMEOUT", 1800)))
    rend.add_argument("--build-timeout", type=float,
                      default=float(os.environ.get("LMFDB_VERSO_BUILD_TIMEOUT", 3600)))

    args = parser.parse_args(argv)
    if args.command == "bootstrap":
        bootstrap_build_root(args.build_root, args.template, args.force)
        return 0
    try:
        render_certificate(args.build_root, args.src, args.nf_name, args.out,
                           args.status, args.lock_timeout, args.build_timeout)
        return 0
    except Exception as err:  # the status file is the worker's error channel
        _log(f"FAILED: {err}")
        _write_status(args.status, state="failed", error=str(err))
        return 1


if __name__ == "__main__":
    sys.exit(main())
