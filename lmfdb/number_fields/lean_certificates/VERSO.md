# Verso certificates (server-side rendered Lean certificates)

The 'Verso certificate' entry in a number field's Downloads sidebar renders
the same Lean code as the 'Lean certificate' zip into an interactive HTML
page using [Verso](https://github.com/leanprover/verso)'s experimental
Lean-to-HTML renderer: accurately highlighted code with hovers, clickable
go-to-definition links, and Alectryon-style intermediate proof states.

Producing the page requires elaborating every certificate module through
the Lean kernel -- with the live LMFDB discriminant and class number
interpolated into the theorem statements -- so a successfully rendered
page is itself a machine-checked verification of those database values,
with no setup on the reader's side.

## Enabling the feature

The feature is **off by default** (deployments without a Lean toolchain,
including lmfdb.org, are unaffected). It needs:

1. [elan](https://github.com/leanprover/elan) installed, with `lake` on
   the web server's PATH.
2. A one-time bootstrap of the persistent build root (expect 10-40
   minutes and ~10 GB of disk, dominated by downloading the mathlib
   cache and compiling Verso):

       python3 lmfdb/number_fields/verso_build.py bootstrap \
           --build-root ~/lmfdb_verso_build

   This copies `project_template/`, adds `verso` (at the tag matching the
   project's `lean-toolchain`) as a Lake dependency, fetches the mathlib
   cache, fully builds the `IdealArithmetic` library and the verso
   executables, and writes a `.bootstrap_ready` sentinel. It is
   idempotent; re-run with `--force` after changing the template.

3. Environment for the web server:

       export LMFDB_VERSO_CERT_ENABLED=1
       export LMFDB_VERSO_BUILD_ROOT=~/lmfdb_verso_build

## How a render works

`GET /NumberField/<label>/verso` starts a detached `verso_build.py render`
worker (there is no job-queue infrastructure in LMFDB; the worker is a
plain stdlib-only subprocess observed through a `status.json` file) and
shows an auto-refreshing progress page. The worker, serialized by a lock
so only one lake build runs in the build root at a time:

1. copies the generated `NF<u>` sources -- with the interpolated entry
   point -- into the build root's `IdealArithmetic/Examples/`,
2. `lake build +IdealArithmetic.Examples.NF<u>.<Mod>` for every module
   (the kernel check; ~2-5 minutes for a typical certificate),
3. builds the modules' `literate` facets (verso-literate re-elaborates
   each module to capture highlighting and proof states),
4. runs the `verso-html` binary on a filtered copy of the literate data
   (it renders everything it is shown, and the build root accumulates
   other labels' data),
5. atomically publishes the static site (~8 MB) to the render cache.

Results are cached per (certificate digest, verso revision, toolchain,
pipeline source) under `LMFDB_VERSO_CERT_CACHE` (default
`/tmp/lmfdb_verso_certificates`), so subsequent visits redirect straight
to the rendered page. The rendered site's pages carry a relative `<base>`
tag and are served from `/NumberField/<label>/verso/<path>`.

## Environment variables

| Variable | Default | Meaning |
|---|---|---|
| `LMFDB_VERSO_CERT_ENABLED` | unset (off) | Master switch for the feature |
| `LMFDB_VERSO_BUILD_ROOT` | unset | The bootstrapped persistent Lake project |
| `LMFDB_VERSO_CERT_CACHE` | `/tmp/lmfdb_verso_certificates` | Render results + status files |
| `LMFDB_VERSO_LOCK_TIMEOUT` | 1800 | Seconds a worker waits for the build slot |
| `LMFDB_VERSO_BUILD_TIMEOUT` | 3600 | Seconds allowed per lake/verso command |

## Prebuilt renders (deployments without a Lean toolchain)

`verso_prebuilt.json` (next to `verso_certificate.py`) maps field labels to
externally hosted pre-rendered certificates. On a deployment where the
local pipeline is not enabled, those labels still show the 'Verso
certificate' button and `/NumberField/<label>/verso` redirects to the
hosted page. This is how the lmfdb.xyz dev servers can demo the feature
with no Lean toolchain installed: render locally, publish the static
output (any static host works -- the pages use relative links), and add
the entry-page URLs to the JSON. A deployment with the live pipeline
enabled ignores the prebuilt map and renders locally.

## Notes

- The downloadable Lean certificate zip is untouched: `project_template/`
  never gains the verso dependency (it is added only to the build-root
  copy during bootstrap), and `lean_certificate.py` is deliberately not
  edited (its source is hashed into every certificate cache key).
- Feasibility gating is inherited from the Lean certificate
  (`lean_certificate_available`): class-group exponent and Minkowski
  bound limits apply, and certificates containing `sorry` are refused
  before any render starts.
- Failed renders show the tail of `render.log` on the progress page and
  offer a retry; the failed render directory is moved aside as
  `<digest>.failed-<timestamp>` for post-mortems.
