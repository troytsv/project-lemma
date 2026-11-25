# Lean 4 proof that fourteen blocks are impossible

`C7021.noFourteenBlockCover` quantifies over every function assigning a finite subset of 70 points to each of 14 block indices. If each block has 21 elements, some two distinct points share no block. Indexed blocks may even repeat.

```lean
theorem C7021.noFourteenBlockCover (B : Fin 14 → Finset (Fin 70))
    (size : ∀ i, (B i).card = 21) :
    ¬ (∀ x y : Fin 70, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i)
```

## Reproduce

With Lean 4.24.0 and its matching Lake available on the path, open a shell in the directory containing `lakefile.toml`. The project pins its dependencies in `lake-manifest.json`. On a fresh checkout, the first command retrieves the precompiled library dependencies, and the second compiles the local proof modules. The final command checks the theorem contract and axiom allowlist.

```text
lake exe cache get Mathlib.Tactic Mathlib.LinearAlgebra.FiniteDimensional.Basic Mathlib.LinearAlgebra.Dimension.Constructions
lake build
lake env lean Audit.lean
```

The audit prints the theorem's transitive axiom dependencies.

```text
'C7021.noFourteenBlockCover' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The audit fails on any additional axiom, including a proof placeholder. These three standard Lean axioms express propositional extensionality, classical choice and quotient soundness.

## Proof map

| Source | What Lean checks |
| --- | --- |
| Lemma/Sparse.lean | Start with rational weight 3/7 per point. A linear dependence allows a weight adjustment that preserves every block load, keeps all weights nonnegative and drops a point from the support. Iterate, then rescale to total weight 30. |
| Lemma/Incidence.lean | Count weighted incidences in two orders. Derive the rank and weight bounds, the excess budget of 6, and equality of all block loads to 9 when the budget is saturated. |
| Lemma/Ranks.lean | The budget and the support bound force the rank-four points to have weight 2. At most two remaining points have positive weight, both of rank five if there are two, and the budget is saturated. |
| Lemma.lean | Turn an arbitrary pair covering into incidence patterns, find a block outside the rank-five patterns, and derive that a natural number times 2 equals 9. |
| Audit.lean | Restate the finite covering contract independently and inspect the final theorem's transitive axiom dependencies. |

This formalization checks the lower bound. The paper's upper bound uses a published 15-block certificate and is checked separately by the project's two Python verifiers. The formal proof uses finite elimination over rational weights for the paper's support-reduction step. Codex developed the formalization with GPT-6.2 Sol agents, and Lean checked the resulting terms locally.

The pinned mathlib commit is `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The [official Lean release](https://github.com/leanprover/lean4/releases/expanded_assets/v4.24.0) lists SHA-256 checksums for each platform archive.
