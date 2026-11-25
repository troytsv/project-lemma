# Project Lemma

The exact covering number **C(70,21,2) is 15**. Any family of 14 blocks of 21 points on a 70-point set misses at least one pair. A published 15-block construction covers all 2,415 pairs.

- [Paper](paper.pdf) and [LaTeX source](paper.tex) by Troy Valiyaparampil and GPT-6.2 Astra.
- [Lean theorem](formal/Lemma.lean) for the lower bound, with an independent [statement and axiom audit](formal/Audit.lean).
- [Certificate](baseline/known15.txt) by Arhan Canli (Quantavane), with two independent Python verifiers for the upper bound.

## Reproduce the checks

From the repository root with Python 3.10 or later, run the commands below. CI uses Python 3.14.5. The verifiers and tests use the standard library.

```text
python verify_pairs.py baseline/known15.txt
python search/verify_dual.py baseline/known15.txt
python -B -m unittest discover -s search -v
python check_ranks.py
```

`verify_pairs.py` enumerates pairs within each block. `search/verify_dual.py` checks whether the incidence masks of each pair intersect. The regression tests check the published certificate and reject malformed blocks, a removed block and a valid-size point swap that uncovers a pair. The [certificate provenance](baseline/README.md) gives the optional replay of explicit isomorphisms to the IRSI and Meliwat records. `check_ranks.py` uses exact rational arithmetic to check the numerical case analysis in the paper.

To replay the lower bound, follow the [Lean build instructions](formal/README.md) for Lean 4.24.0 and the pinned mathlib dependencies. The [replay record](formal/REPLAY.txt) gives the source hashes and axiom output. The [GitHub Actions workflow](.github/workflows/verify.yml) runs the certificate checks, numerical checks and Lean proof audit.

To typeset the paper, run `tectonic paper.tex`. A standard LaTeX installation with the packages listed in the preamble also works.

## Credit and licensing

Troy Valiyaparampil posed the research question and requested formal verification. GPT-6.2 Astra developed the lower-bound argument and drafted the paper in OpenAI Codex. GPT-6.2 Sol sessions reviewed the argument, checked certificates and contributed Lean proof modules. The [references](REFERENCES.md) credit prior work and the published constructions.

The [MIT License](LICENSE) applies to original project code and writing. The certificate in [baseline/known15.txt](baseline/known15.txt), also printed in the paper, is by Arhan Canli (Quantavane) under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Upstream Lean and mathlib dependencies retain their own licenses.
