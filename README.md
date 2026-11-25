# Project Lemma

The exact covering number **C(70,21,2) is 15**. Any family of 14 blocks of 21 points on a 70-point set misses at least one pair. A published 15-block construction covers all 2,415 pairs.

- [Paper](paper.pdf) and [LaTeX source](paper.tex) by Troy Valiyaparampil and GPT-6.2 Astra.
- [Lean theorem](formal/Lemma.lean) for the lower bound, with an independent [statement and axiom audit](formal/Audit.lean).
- [Certificate](baseline/known15.txt) by Arhan Canli (Quantavane), with two independent Python verifiers for the upper bound.

## The first Mills number on fourteen vertices

The exact all-to-all comparison data limit **L(14) is 7/23**. Equivalently, the largest fractional matching number of an intersecting hypergraph on fourteen vertices is **23/7**. This is the $q=3$ case of Füredi's conjecture. [Füredi, 1990, Conjecture 6.3](https://doi.org/10.1016/0097-3165(90)90034-T) · [Füredi, 1994, Conjecture 4.9](https://doi.org/10.1016/0012-365X(92)00478-A)

The [L(14) paper and verification guide](l14/README.md) gives the Lean proof, the witness, and the attribution to Colin Barker's 2008 covering.

## Reproduce the checks

From the repository root with Python 3.10 or later, run the commands below. CI uses Python 3.14.5. The verifiers and tests use the standard library.

```text
python verify_pairs.py baseline/known15.txt
python search/verify_dual.py baseline/known15.txt
python -B -m unittest discover -s search -v
python check_ranks.py
```

`verify_pairs.py` enumerates pairs within each block. `search/verify_dual.py` checks whether the incidence masks of each pair intersect. The regression tests check the published certificate and reject malformed blocks, a removed block and a valid-size point swap that uncovers a pair. The [certificate provenance](baseline/README.md) gives the optional replay of explicit isomorphisms to the IRSI and Meliwat records. `check_ranks.py` uses exact rational arithmetic to check the numerical case analysis in the paper.

Follow the [Lean build instructions](formal/README.md) to replay the C(70,21,2) lower bound. The [original replay record](formal/REPLAY.txt) gives the hashes and axiom output for commit `034715f`. The [GitHub Actions workflow](.github/workflows/verify.yml) runs the certificate checks, numerical checks, and both Lean audits.

To typeset the paper, run `tectonic paper.tex`. A standard LaTeX installation with the packages listed in the preamble also works.

## Credit and licensing

Troy Valiyaparampil posed the research question and requested formal verification. GPT-6.2 Astra developed the lower-bound argument and drafted the paper in OpenAI Codex. GPT-6.2 Sol sessions reviewed the argument, checked certificates and contributed Lean proof modules. The [references](REFERENCES.md) credit prior work and the published constructions.

The [MIT License](LICENSE) applies to original project code and writing. Arhan Canli's [15-block certificate](baseline/known15.txt) and the archived data for Colin Barker's 14-block covering are under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). Upstream Lean and mathlib dependencies retain their own licenses.
