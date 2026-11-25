# The first Mills number on fourteen vertices

The all-to-all comparison data limit is $L(14)=7/23$. The largest fractional matching number over intersecting hypergraphs on fourteen vertices is $23/7$. This establishes the $q=3$ case of Füredi's conjecture. [Füredi, 1990, Conjecture 6.3](https://doi.org/10.1016/0097-3165(90)90034-T) · [Füredi, 1994, Conjecture 4.9](https://doi.org/10.1016/0012-365X(92)00478-A)

The consolidated [paper](../paper/paper.pdf) and its [LaTeX source](../paper/paper.tex) give the mathematical argument. The [contribution disclosure](../../../AI_DISCLOSURE.md) records Troy Valiyaparampil’s direction of the project and the models’ mathematical and formalization work.

## Reproduce the checks

Run the integer verifiers from the problem directory with Python 3.10 or later.

```text
python l14/classify/verify_witness.py
python l14/classify/verify_barker.py
```

The first verifier checks that fourteen distinct 21-point blocks cover all 2,346 pairs on 69 points. The second checks Barker's archived covering and verifies the relabeling. The weighted incidence masks are in the first verifier and the [Lean witness](../formal/L14/Witness.lean).

With Lean 4.24.0 and its matching Lake on the path, run these commands from `formal`.

```text
lake exe cache get Mathlib.Tactic Mathlib.Data.Real.Basic Mathlib.LinearAlgebra.FiniteDimensional.Basic Mathlib.LinearAlgebra.Dimension.Constructions
lake --wfail build
lake env lean -DwarningAsError=true AuditL14.lean
```

The audit independently states the infimum and maximum contracts. It rejects transitive axiom dependencies beyond `propext`, `Classical.choice`, and `Quot.sound`. The project pins mathlib in [lake-manifest.json](../formal/lake-manifest.json).

## Proof map

| Lean source | What it proves |
| --- | --- |
| [Sparse](../formal/L14/Sparse.lean) | A positive weighted intersecting family on fourteen vertices can retain its total mass on at most fourteen distinct edges without increasing any vertex load. |
| [ThresholdCore](../formal/L14/ThresholdCore.lean), [SharpData](../formal/L14/SharpData.lean), [Outside](../formal/L14/Outside.lean) | Bound the rank, mass, and load deficits above total weight 69 when each load is at most 21. |
| [Eleven](../formal/L14/Eleven.lean), [HighRanks](../formal/L14/HighRanks.lean), [TwoQuints](../formal/L14/TwoQuints.lean) | Exclude every sparse family above the threshold by its rank counts and incidences. |
| [Sharp](../formal/L14/Sharp.lean) | Combine the sparse bound with the witness to prove `L14.mills_eq_seven_twentyThree` and `L14.fractional_matching_maximum`. |
| [Covering](../formal/L14/Covering.lean), [CoveringWitnesses](../formal/L14/CoveringWitnesses.lean) | Prove the general covering lower bound and the two exact families for every positive replication factor. |
| [Plane](../formal/L14/Plane.lean) | Check the earlier projective-plane witness with mass $13/4$ under unit vertex capacities. |
| [AuditL14](../formal/AuditL14.lean) | Check the sharp extremal theorem contracts, covering corollaries and axiom requirements. |

## Witness provenance

The [exploratory search source](classify/Search.cs) and [recorded run](classify/search-run.txt) document how the project recovered the weighted witness. The search mutates supports and solves floating-point linear programs. The witness passes exact integer verification in Python and Lean.

The La Jolla archive dates Colin Barker's isomorphic 14-block covering to 28 December 2008. The [provenance note](prior-work.md) records the exact relabeling and the projective-plane construction it recovers. Daniel M. Gordon maintains the archived dataset under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). [Archived covering record](https://doi.org/10.5281/zenodo.24119701)

To replay the historical index check, download `coverdata.json` from archive version 1.2.1. Pass its path to the script from the problem directory.

```text
python l14/classify/check_archive.py /path/to/coverdata.json
```

The script verifies the archive checksum and compares exact ratios for all 716 listed pair coverings with at most fourteen blocks. The minimum listed ratio is 7/23 for Barker's covering.

## Rebuild the paper

The [release instructions](../verification/README.md) give the build command for the consolidated manuscript.
