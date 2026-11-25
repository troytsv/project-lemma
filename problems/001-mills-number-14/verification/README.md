# Reproduce Problem 001

Start in `problems/001-mills-number-14/`. The [problem README](../README.md) lists the independent Python certificate and numerical checks. The [Lean verification report](../formal/VERIFICATION.md) gives the pinned toolchain, dependency manifest, theorem statements, build and axiom audits. The [supplement](../results/README.md) explains how to regenerate the full comparison from the versioned source dataset.

## Manuscript

The canonical manuscript is [paper/paper.pdf](../paper/paper.pdf). From `paper/`, set `SOURCE_DATE_EPOCH=1795564800` and run `tectonic --keep-intermediates paper.tex`. Tectonic 0.17.0+20260731 and its TeX bundle generated the distributed PDF and BibTeX output. Add `--only-cached` for a previously populated TeX cache. Alternatively, run XeLaTeX, BibTeX and two further XeLaTeX passes. Different TeX distributions can change PDF bytes.

## Release archive

From a Git checkout run `python tools/package_release.py ../release-output --rev mills-14-v1.0.0` at the repository root. The command packages the committed tree, copies the exact manuscript and writes SHA-256 checksums. The ZIP comment gives the source commit. [Source licenses](../../../LICENSING.md) · [Workflow](../../../.github/workflows/mills-14.yml)
