# The first Mills number on fourteen vertices

For any intersecting family on fourteen vertices with total edge weight one, some vertex carries weight at least **7/23**. Colin Barker’s 2008 covering attains this load. Equivalently, the maximum fractional matching mass under unit vertex capacities is **23/7**. This establishes the $q=3$ case of Füredi’s conjecture. In an all-to-all comparison system on fourteen machines, the optimal largest share of data held by one machine is about 30.43%. [Manuscript](paper/paper.pdf) · [LaTeX](paper/paper.tex) · [Bibliography](paper/references.bib)

The universal lower bound applies to arbitrary nonnegative real weights. For $2\le k\le v$, it implies $C(v,k,2)\ge15$ whenever $7v>23k$. Known constructions then give $C(70n,21n,2)=15$ and $C(69n,21n,2)=14$ for every positive integer $n$. The [comparison with published records](results/README.md) distinguishes archived bounds, previously available inequalities, and consequences of the sharp bound.

## Inspect the proof

- [Walk through the argument](research/understanding-the-proof.md), including the final packing of pairs.
- [Read the adversarial proof review](research/proof-audit.md) and [priority assessment](l14/prior-work.md). Füredi predicted the value in 1990, and Barker supplied an attaining construction. The search located no earlier proof of the universal lower bound. [Original conjecture](https://doi.org/10.1016/0097-3165(90)90034-T) · [Construction archive](https://doi.org/10.5281/zenodo.24119701)
- [Inspect the Lean endpoints](formal/L14/Sharp.lean), the [independently stated contracts](formal/AuditL14.lean), and the [verification report](formal/VERIFICATION.md). The [proof map](l14/README.md) links the cases to their source.
- [Review the contribution disclosure](../../AI_DISCLOSURE.md). Troy Valiyaparampil initiated and directed the project. OpenAI models contributed to problem and hypothesis selection, developed the mathematical argument, ran searches, wrote Lean proofs and drafted the paper.

**Status.** Public research preprint, version 1.0.0, 25 November 2026. The proof is formally verified in Lean. Independent peer review remains open.

[Publication record, recommended citation and subsequent notifications](PUBLICATION.md)

## Reproduce the results

With Python 3.10 or later, run these commands from the problem directory.

```sh
python l14/classify/verify_witness.py
python l14/classify/verify_barker.py
python verification/verify_pairs.py certificates/known15.txt
python verification/search/verify_dual.py certificates/known15.txt
python -B -m unittest discover -s verification/search -v
python verification/check_ranks.py
python results/verify_covering_certificates.py
```

The first two commands check all 2,346 pairs of Barker’s covering, its relabeling and the order-three plane underlying the presentation. The next two independently check all 2,415 pairs in the 70-point certificate. The tests exercise malformed examples as well as valid ones. Two comparison certificates can be supplied separately under the instructions in [certificate provenance](certificates/README.md). The rank check replays the numerical cases of the original proof. The final command verifies all pairs in ten further fifteen-block constructions.

With Lean 4.24.0 and Lake available, a new checkout can reproduce the formal results as follows. The manifest pins Mathlib and its dependencies.

```sh
cd formal
lake exe cache get Mathlib.Tactic Mathlib.Data.Real.Basic Mathlib.LinearAlgebra.FiniteDimensional.Basic Mathlib.LinearAlgebra.Dimension.Constructions
lake --wfail build
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true AuditL14.lean
```

The verification report lists any additional audits and exact toolchain revisions. The [GitHub Actions workflow](../../.github/workflows/mills-14.yml) runs the checks for changes to this investigation.

## Build and cite the paper

From the `paper/` directory the LaTeX entry point is `paper.tex`. It uses standard packages and a BibTeX database, with a prebuilt `paper.bbl` for submission systems. Build with `tectonic paper.tex`, or with `xelatex paper`, `bibtex paper`, and two further `xelatex paper` runs. The verified Tectonic build used version 0.17.0+20260731 and the fixed environment variable `SOURCE_DATE_EPOCH=1795564800`. [Release packaging](verification/README.md) · [Citation metadata](CITATION.cff)

## License and provenance

Original software is MIT-licensed and the original manuscript and research documentation are available under CC BY 4.0. Reproduced construction data retain their separate attributions. [License scope](../../LICENSING.md) · [Sources and attribution](REFERENCES.md) · [Project history](research/history.md)
