import contextlib
import functools
import hashlib
import io
import json
import math
import os
import re
import shutil
import time
import zipfile

from flask import abort, send_file
from sage.all import ZZ, PolynomialRing, NumberField, sage_eval

from lmfdb.number_fields.class_group_lean import generate_class_group_lean


_HERE = os.path.dirname(os.path.abspath(__file__))
_LEAN_CERT_ROOT = os.path.join(_HERE, "lean_certificates")
_PROJECT_TEMPLATE = os.path.join(_LEAN_CERT_ROOT, "project_template")
_DEFAULT_CACHE = os.path.join("/tmp", "lmfdb_lean_certificates")
_LOCK_POLL_SECONDS = 0.25
_LOCK_TIMEOUT_SECONDS = 30
# The certificate generator enumerates and certifies every prime ideal of norm
# below the Minkowski bound, so the bound is the natural feasibility measure.
# The default keeps first-time generation to roughly O(10s) of CPU on current
# hardware (see LMFDB_LEAN_CERT_MAX_MINKOWSKI to override).
_DEFAULT_MAX_MINKOWSKI_BOUND = 150.0
# The certificate materializes every power J^k of each class group generator,
# with entries growing exponentially in k, so Lean's `decide` steps stop
# scaling once the exponent of the class group is large: generator orders up
# to 128 are verified to compile, while a generator of order 188 breaks the
# build (see LMFDB_LEAN_CERT_MAX_CLASS_EXPONENT to override).
_DEFAULT_MAX_CLASS_EXPONENT = 128


class LeanCertificateError(RuntimeError):
    pass


class LeanCertificateUnavailable(LeanCertificateError):
    pass


def label_to_lean_name(label):
    return label.replace(".", "_")


def lean_entry_rel(label, meta=None):
    if meta and meta.get("entry_point"):
        return meta["entry_point"]
    u = label_to_lean_name(label)
    return f"IdealArithmetic/Examples/NF{u}/Results{u}.lean"


def lean_metadata(label, nf=None):
    return {
        "label": label,
        "polynomial": str(nf.poly()) if nf is not None else None,
        "entry_point": lean_entry_rel(label),
        "lean_toolchain": _read_text(os.path.join(_PROJECT_TEMPLATE, "lean-toolchain")).strip(),
    }


def lean_certificate_available(label, nf):
    """Decide (cheaply -- this runs on every field page render) whether we can
    generate a Lean certificate for this field on demand.  Uses only database
    columns already loaded on the WebNumberField; in particular it must not
    trigger the ``zk()`` fallback, which computes an integral basis in pari.
    """
    try:
        if nf.is_null() or nf.degree() < 2 or not nf.can_class_number():
            return False
        if not nf.coeffs():
            return False
        if _class_group_exponent(nf) > _max_class_exponent():
            return False
        return _minkowski_bound(nf) <= _max_minkowski_bound()
    except (AttributeError, KeyError, TypeError, ValueError):
        return False


def _class_group_exponent(nf):
    """The exponent of the class group per the database, falling back to the
    class number (which the exponent divides) when the structure is unknown."""
    cg = nf._data.get("class_group")
    if isinstance(cg, list):
        return int(max(cg)) if cg else 1
    return int(nf._data["class_number"])


def _minkowski_bound(nf):
    """The Minkowski bound n!/n^n (4/pi)^r2 sqrt|d|, computed in log space so
    that fields with huge discriminants do not overflow floats."""
    n = int(nf.degree())
    r2 = int(nf.signature()[1])
    d = abs(int(nf.disc()))
    if d == 0:
        return float("inf")
    log_bound = (math.lgamma(n + 1) - n * math.log(n)
                 + r2 * math.log(4 / math.pi) + 0.5 * math.log(d))
    try:
        return math.exp(log_bound)
    except OverflowError:
        return float("inf")


def _max_minkowski_bound():
    try:
        return float(os.environ.get("LMFDB_LEAN_CERT_MAX_MINKOWSKI", ""))
    except ValueError:
        return _DEFAULT_MAX_MINKOWSKI_BOUND


def _max_class_exponent():
    try:
        return int(os.environ.get("LMFDB_LEAN_CERT_MAX_CLASS_EXPONENT", ""))
    except ValueError:
        return _DEFAULT_MAX_CLASS_EXPONENT


def get_or_create_certificate_project(label, nf):
    if not lean_certificate_available(label, nf):
        raise LeanCertificateUnavailable(f"No Lean certificate available for {label}")
    zk = _zk_strings(nf)
    cache_dir = _cache_project_dir(label, nf, zk)
    ready = os.path.join(cache_dir, ".ready")
    if os.path.isfile(ready):
        return cache_dir
    os.makedirs(os.path.dirname(cache_dir), exist_ok=True)
    lock_path = cache_dir + ".lock"
    with _file_lock(lock_path):
        if os.path.isfile(ready):
            return cache_dir
        tmp_dir = cache_dir + ".tmp"
        if os.path.isdir(tmp_dir):
            shutil.rmtree(tmp_dir)
        shutil.copytree(_PROJECT_TEMPLATE, tmp_dir, ignore=_copy_ignore)
        examples_dir = os.path.join(tmp_dir, "IdealArithmetic", "Examples")
        os.makedirs(examples_dir, exist_ok=True)
        T, basis = _sage_polynomial_and_basis(nf, zk)
        try:
            generate_class_group_lean(T, basis, label_to_lean_name(label), output_dir=examples_dir)
        except Exception as err:
            raise LeanCertificateError(f"Lean certificate generation failed for {label}: {err}")
        entry_path = os.path.join(tmp_dir, lean_entry_rel(label))
        if not os.path.isfile(entry_path):
            raise LeanCertificateError(f"Lean generator did not create {lean_entry_rel(label)}")
        _reject_incomplete_proofs(label, os.path.join(examples_dir, f"NF{label_to_lean_name(label)}"))
        _write_text(entry_path, lean_deinterpolate(_read_text(entry_path)))
        # Import the entry point from the library root so that a plain
        # `lake build` checks the certificate itself, as the README promises.
        u = label_to_lean_name(label)
        with open(os.path.join(tmp_dir, "IdealArithmetic.lean"), "a") as fh:
            fh.write(f"import IdealArithmetic.Examples.NF{u}.Results{u}\n")
        _write_text(os.path.join(tmp_dir, "metadata.json"), json.dumps(lean_metadata(label, nf), indent=2) + "\n")
        _write_text(os.path.join(tmp_dir, ".ready"), "")
        if os.path.isdir(cache_dir):
            shutil.rmtree(cache_dir)
        os.replace(tmp_dir, cache_dir)
    return cache_dir


def send_lean_certificate_zip(label, nf):
    try:
        cert_dir = get_or_create_certificate_project(label, nf)
    except LeanCertificateUnavailable as err:
        return abort(404, str(err))
    except LeanCertificateError as err:
        return abort(503, str(err))
    meta = _lean_metadata_from_project(cert_dir)
    entry_rel = lean_entry_rel(label, meta)
    entry_path = os.path.join(cert_dir, entry_rel)
    results_src = _read_text(entry_path) if os.path.isfile(entry_path) else ""
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer, "w", zipfile.ZIP_DEFLATED) as zf:
        for root, dirs, files in os.walk(cert_dir):
            dirs[:] = sorted(d for d in dirs if d != "__pycache__")
            for fname in sorted(files):
                if fname == ".ready":
                    continue
                path = os.path.join(root, fname)
                rel = os.path.relpath(path, cert_dir).replace(os.sep, "/")
                if rel == entry_rel:
                    continue
                zf.write(path, arcname=f"{label}/{rel}")
        if results_src:
            zf.writestr(f"{label}/{entry_rel}", lean_interpolate(results_src, nf))
        zf.writestr(f"{label}/README.txt", lean_certificate_readme(label, nf, meta))
    buffer.seek(0)
    return send_file(buffer, download_name=f"{label}_lean_certificate.zip",
                     as_attachment=True, mimetype="application/zip")


LEAN_README_TEMPLATE = """Lean certificate for the number field {label}
=============================================
LMFDB page:          https://www.lmfdb.org/NumberField/{label}
Defining polynomial: {poly}

How this certificate verifies the LMFDB entry
---------------------------------------------
The certificate's source carries NO numbers of its own -- its theorems are
stated with placeholders:

    theorem K_discr'         : discr K = LMFDB_discriminant := K_discr
    theorem class_number_...  : classNumber K = LMFDB_classNumber := class_number_K_eq_4

At download time LMFDB filled the placeholders with the live nf_fields database
values for this field:

    discr K        = {disc}
    classNumber K  = {cn}

The proof terms (K_discr, class_number_K_eq_4) are independently checked by
Lean, so a successful build verifies these LMFDB values.

To build it (needs a Lean 4 + Mathlib setup); from a terminal in this folder:
  lake exe cache get
  lake build

Entry point:
  {entry}
"""


def lean_certificate_readme(label, nf, meta):
    disc = int(nf.disc())
    cn = int(nf.class_number()) if nf.can_class_number() else "n/a"
    return LEAN_README_TEMPLATE.format(
        label=label, poly=meta.get("polynomial") or nf.poly(),
        entry=lean_entry_rel(label, meta), disc=disc, cn=cn)


def lean_interpolate(src, nf):
    src = re.sub(r'(discr K = )(?:LMFDB_discriminant|-?\d+)',
                 lambda m: f'{m.group(1)}{int(nf.disc())}', src)
    if nf.can_class_number():
        src = re.sub(r'(classNumber K = )(?:LMFDB_classNumber|\d+)',
                     lambda m: f'{m.group(1)}{int(nf.class_number())}', src)
    return src


def lean_deinterpolate(src):
    src = re.sub(r'(discr K = )-?\d+', r'\1LMFDB_discriminant', src)
    src = re.sub(r'(classNumber K = )\d+', r'\1LMFDB_classNumber', src)
    return src


def _cache_project_dir(label, nf, zk):
    root = os.environ.get("LMFDB_LEAN_CERT_CACHE", _DEFAULT_CACHE)
    digest = _certificate_digest(label, nf, zk)
    return os.path.join(root, label, digest)


def _certificate_digest(label, nf, zk):
    h = hashlib.sha256()
    h.update(_source_digest().encode())
    h.update(label.encode())
    h.update(repr(nf.coeffs()).encode())
    h.update(repr(zk).encode())
    return h.hexdigest()[:16]


def _reject_incomplete_proofs(label, generated_dir):
    """The generator falls back to ``sorry`` in a few corner cases (e.g. an
    irreducibility witness prime too large for its norm_num proof) and only
    prints a warning; an incomplete certificate must never be served."""
    for root, _, files in os.walk(generated_dir):
        for fname in files:
            if fname.endswith(".lean") and re.search(r"\bsorry\b", _read_text(os.path.join(root, fname))):
                raise LeanCertificateError(
                    f"Lean certificate for {label} is incomplete ({fname} contains sorry)")


@contextlib.contextmanager
def _file_lock(path):
    deadline = time.time() + _LOCK_TIMEOUT_SECONDS
    while True:
        try:
            fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            os.close(fd)
            break
        except FileExistsError:
            if time.time() >= deadline:
                raise LeanCertificateError("Timed out waiting for Lean certificate generation lock")
            time.sleep(_LOCK_POLL_SECONDS)
    try:
        yield
    finally:
        with contextlib.suppress(FileNotFoundError):
            os.unlink(path)


def _zk_strings(nf):
    # Database records spell the integral basis in ``a``; the ``zk()`` fallback
    # (pari nfbasis, used when the record has no zk column) spells it in ``x``.
    return [str(b) for b in nf.zk()]


def _sage_polynomial_and_basis(nf, zk=None):
    R = PolynomialRing(ZZ, "x")
    x = R.gen()
    coeffs = [ZZ(c) for c in nf.coeffs()]
    T = sum(coeffs[i] * x**i for i in range(len(coeffs)))
    K = NumberField(T, "a")
    a = K.gen()
    basis = [K(sage_eval(b, locals={"a": a, "x": a}))
             for b in (zk if zk is not None else _zk_strings(nf))]
    return T, basis


def _copy_ignore(path, names):
    ignored = {"__pycache__", ".DS_Store", ".git", ".lake", "metadata.json"}
    if os.path.normpath(path) == os.path.normpath(_PROJECT_TEMPLATE):
        # Upstream project readme; the download gets its own README.txt.
        ignored.add("README.md")
    if os.path.basename(path) == "Examples":
        ignored.update(name for name in names if name.startswith("NF"))
    return ignored.intersection(names)


def _lean_metadata_from_project(cert_dir):
    path = os.path.join(cert_dir, "metadata.json")
    if os.path.isfile(path):
        with open(path) as fh:
            return json.load(fh)
    return {}


@functools.lru_cache(maxsize=None)
def _source_digest():
    # The generator source and project template are immutable for the lifetime
    # of the server process, so hash them once.
    h = hashlib.sha256()
    for path in [__file__, os.path.join(_HERE, "class_group_lean.py")]:
        h.update(_read_text(path).encode())
    for root, dirs, files in os.walk(_PROJECT_TEMPLATE):
        dirs[:] = sorted(d for d in dirs if d not in {".git", ".lake", "__pycache__"})
        for fname in sorted(files):
            if fname == ".DS_Store":
                continue
            path = os.path.join(root, fname)
            h.update(os.path.relpath(path, _PROJECT_TEMPLATE).encode())
            with open(path, "rb") as fh:
                h.update(fh.read())
    return h.hexdigest()


def _read_text(path):
    with open(path) as fh:
        return fh.read()


def _write_text(path, content):
    with open(path, "w") as fh:
        fh.write(content)
