module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

public section

open Finset

namespace MillsFourteen

/-- The infimum of the heaviest vertex load among intersecting probability distributions on fourteen vertices is 7/23. -/
theorem mills_eq_seven_twentyThree : sInf {c : ℝ | ∃ (s : Finset (Finset (Fin 14))) (w : Finset (Fin 14) → ℝ),
    (∀ p ∈ s, ∀ q ∈ s, (p ∩ q).Nonempty) ∧
    (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p) = 1 ∧
    c = univ.sup' univ_nonempty (fun i : Fin 14 => ∑ p ∈ s, if i ∈ p then w p else 0)} =
      (7 / 23 : ℝ) :=
  by sorry

/-- The greatest feasible fractional matching mass of an intersecting hypergraph on fourteen vertices is 23/7. -/
theorem fractional_matching_maximum : IsGreatest {m : ℝ | ∃ (s : Finset (Finset (Fin 14))) (w : Finset (Fin 14) → ℝ),
    (∀ p ∈ s, ∀ q ∈ s, (p ∩ q).Nonempty) ∧
    (∀ p ∈ s, 0 ≤ w p) ∧
    (∀ i : Fin 14, (∑ p ∈ s, if i ∈ p then w p else 0) ≤ 1) ∧
    (∑ p ∈ s, w p) = m} (23 / 7) :=
  by sorry

/-- An intersecting probability distribution attains the load 7/23. -/
theorem witness_mem_millsValues : ∃ (s : Finset (Finset (Fin 14))) (w : Finset (Fin 14) → ℝ),
    (∀ p ∈ s, ∀ q ∈ s, (p ∩ q).Nonempty) ∧
    (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p) = 1 ∧
    (7 / 23 : ℝ) = univ.sup' univ_nonempty (fun i : Fin 14 => ∑ p ∈ s, if i ∈ p then w p else 0) :=
  by sorry

/-- Every pair covering with at most k points per block needs at least fifteen blocks if 23k < 7v and v ≥ 2. -/
theorem covering_card_lower_bound {v k b : ℕ} (hv : 2 ≤ v) (hstrict : 23 * k < 7 * v)
    (B : Fin b → Finset (Fin v)) (hsize : ∀ i, (B i).card ≤ k)
    (hcover : ∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i) : 15 ≤ b :=
  by sorry

/-- For every positive scale n, the minimum number of 21n-subsets covering all pairs of 70n points is fifteen. -/
theorem covering70_exact_scaled {n : ℕ} (hn : 0 < n) :
    IsLeast {b : ℕ | ∃ B : Fin b → Finset (Fin (70 * n)),
      (∀ i, (B i).card = 21 * n) ∧ (∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i)} 15 :=
  by sorry

/-- For every positive scale n, the corresponding minimum on 69n points is fourteen. -/
theorem covering69_exact_scaled {n : ℕ} (hn : 0 < n) :
    IsLeast {b : ℕ | ∃ B : Fin b → Finset (Fin (69 * n)),
      (∀ i, (B i).card = 21 * n) ∧ (∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i)} 14 :=
  by sorry

/-- Fourteen 21-subsets cannot cover every pair of seventy points. -/
theorem noFourteenBlockCover : ∀ blocks : Fin 14 → Finset (Fin 70),
    (∀ i, (blocks i).card = 21) →
    ¬ (∀ x y : Fin 70, x ≠ y → ∃ i, x ∈ blocks i ∧ y ∈ blocks i) :=
  by sorry

end MillsFourteen
