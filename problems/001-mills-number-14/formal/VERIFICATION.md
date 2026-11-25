# Lean verification

The formal development proves the weighted extremum on fourteen vertices, verifies an attaining witness, and proves the covering-number consequences stated below.

## Reproduce the checks

For the Palomar port, use Lean and Lake 4.36.0 as specified by [lean-toolchain](lean-toolchain). [lake-manifest.json](lake-manifest.json) pins Mathlib v4.36.0 at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` and fixes the eight transitive dependency revisions. In a fresh checkout, run these commands from `formal`.

```sh
lean --version
lake exe cache get Mathlib.Tactic Mathlib.Algebra.Order.Archimedean.Real.Basic Mathlib.LinearAlgebra.FiniteDimensional.Basic Mathlib.LinearAlgebra.Dimension.Constructions
lake --wfail build
lake env lean -DwarningAsError=true Audit.lean
lake env lean -DwarningAsError=true AuditL14.lean
```

The cache command retrieves dependency artifacts. The build elaborates the project's proof sources. The two audits restate the contracts with their predicates expanded and reject an axiom outside the allowlist. GitHub Actions runs the same build and audits on Ubuntu. The [older replay](REPLAY.txt) records the original proof of the 70-point lower bound.

The [standalone Challenge](Challenge.lean) uses only upstream mathematical definitions. Its seven deliberate proof holes are the inputs to Comparator. Each corresponding declaration in [Solution](Solution.lean) applies a released theorem at the expanded type. The [Comparator configuration](comparator.json) names all seven. The [formalization metadata](formalization.yaml) records the proof and construction provenance. The original [version 1.0.0 verification report](https://github.com/troytsv/project-lemma/blob/mills-14-v1.0.0/problems/001-mills-number-14/formal/VERIFICATION.md) preserves the Lean 4.24.0 replay instructions.

## Checked statements

| Lean theorem | Statement |
| --- | --- |
| `L14.mills_eq_seven_twentyThree` | The infimum of the maximum vertex load is `7 / 23`. The domain is every intersecting family of subsets of `Fin 14` with arbitrary nonnegative real weights summing to one. |
| `L14.witness_mem_millsValues` | The witness attains that infimum. Its fourteen distinct incidence patterns have integer weights summing to 69 and load 21 at every vertex before normalization. |
| `L14.fractional_matching_maximum` | Among the same intersecting families with arbitrary nonnegative real weights and vertex loads at most one, `23 / 7` is the greatest total weight and is attained. |
| `L14.covering_card_lower_bound` | If `v ≥ 2` and `23 * k < 7 * v`, every indexed pair cover on `Fin v` with blocks of size at most `k` uses at least fifteen blocks. |
| `L14.covering70_exact_scaled` | For every positive integer `n`, fifteen is the least number of blocks of size `21 * n` needed to cover the pairs on `70 * n` points. |
| `L14.covering69_exact_scaled` | For every positive integer `n`, fourteen is the least number of blocks of size `21 * n` needed to cover the pairs on `69 * n` points. |
| `C7021.noFourteenBlockCover` | The original, separate rational proof that fourteen indexed blocks of size 21 cannot cover the pairs on 70 points. |

## Quantifiers and proof dependencies

The weighted contract uses `Finset (Finset (Fin 14))`. The intersection condition includes a pattern paired with itself, which excludes empty patterns. Any family on fewer vertices embeds by adding isolated vertices. Repeated patterns in indexed presentations can be merged by summing their weights. Zero weights are allowed by the theorem and removed before the support argument. Including intersection only among patterns of positive weight gives the same optimization domain after zero patterns are dropped.

[`Sparse.lean`](L14/Sparse.lean) finds a dependence over the reals in the fourteen-dimensional load space. The chosen sign of the dependence lets each support reduction preserve the loads and weakly increase the total mass. A final rescaling restores the original positive mass and weakly decreases each load. [`Sharp.lean`](L14/Sharp.lean) proves the bound for the resulting positive support of at most fourteen patterns. Its two cases split the deficit at four, including equality in the second case. The threshold argument excludes total mass strictly greater than 69 under the load cap of 21. [`Witness.lean`](L14/Witness.lean) checks attainment by kernel reduction and exact arithmetic.

[`Covering.lean`](L14/Covering.lean) accepts repeated blocks and pads the index set with unused vertices when there are fewer than fourteen blocks. Every point belongs to a block, since it has a distinct partner when `v ≥ 2`. The proof groups points by incidence pattern, divides the multiplicities by `k`, and invokes the unit-capacity maximum. It derives `k > 0` from the existence of a cover. The replication proof handles two distinct copies of the same original point. The 69-point family uses an elementary incidence count to exclude thirteen blocks.

[`CoveringWitnesses.lean`](L14/CoveringWitnesses.lean) expands the weighted Barker witness and checks the Canli covering by its incidence columns. The Canli columns transcribe [the attributed source certificate](../certificates/README.md). The independent witness and relabeling scripts validate the original Barker construction by integer arithmetic.

## Version 1.0.0 replay results

The 2026-11-25 Windows replay used Lean 4.24.0, commit `797c613eb9b6d4ec95db23e3e00af9ac6657f24b`. All nine local dependency checkouts matched the pinned commits and had clean tracked files. The import path contained only those dependencies' precompiled libraries and a newly created project output directory. Lean compiled all 21 local source files with `-DwarningAsError=true`, including both audits. The replay reused third-party library objects. It rebuilt all local proof objects from source.

Each theorem in the table has the same printed transitive axiom dependencies.

```text
[propext, Classical.choice, Quot.sound]
```

The source scan found no proof placeholders, local axioms, `native_decide`, or unsafe proof code. The local option overrides increase elaboration limits. Witness checks use ordinary `decide`. The stand-alone integer checks independently verified all 2,346 Barker point pairs and all 2,415 Canli point pairs. The replay also matched every weighted Lean Barker row to the independent checker and reconstructed all fifteen Canli blocks from the Lean incidence columns for comparison with the source certificate.

The weighted incidence contract and fractional-matching contract are formalized directly. The interpretation of the incidence contract as a data-distribution model, the connection to the historical conjecture, and construction attribution are mathematical and bibliographic arguments in the accompanying text. The Lean development assumes the correctness of the Lean kernel and its three listed standard axioms. Before the public release, a second clean Windows replay in the new problem directory again built all 21 local sources and audited all seven statements against the same nine exact dependency revisions. Hosted workflow results are available separately in the [GitHub Actions history](https://github.com/troytsv/project-lemma/actions/workflows/mills-14.yml).
