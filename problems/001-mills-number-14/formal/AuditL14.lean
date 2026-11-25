module

public import L14
public import Lean.Util.CollectAxioms

@[expose] public section

open Finset

-- State the infimum contract using finite sets and vertex loads directly.
example : sInf {c : ℝ | ∃ (s : Finset (Finset (Fin 14))) (w : Finset (Fin 14) → ℝ),
    (∀ p ∈ s, ∀ q ∈ s, (p ∩ q).Nonempty) ∧
    (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p) = 1 ∧
    c = univ.sup' univ_nonempty (fun i : Fin 14 => ∑ p ∈ s, if i ∈ p then w p else 0)} =
      (7 / 23 : ℝ) :=
  L14.mills_eq_seven_twentyThree

example : IsGreatest {m : ℝ | ∃ (s : Finset (Finset (Fin 14))) (w : Finset (Fin 14) → ℝ),
    (∀ p ∈ s, ∀ q ∈ s, (p ∩ q).Nonempty) ∧
    (∀ p ∈ s, 0 ≤ w p) ∧
    (∀ i : Fin 14, (∑ p ∈ s, if i ∈ p then w p else 0) ≤ 1) ∧
    (∑ p ∈ s, w p) = m} (23 / 7) :=
  L14.fractional_matching_maximum

example {v k b : ℕ} (hv : 2 ≤ v) (hstrict : 23 * k < 7 * v)
    (B : Fin b → Finset (Fin v)) (hsize : ∀ i, (B i).card ≤ k)
    (hcover : ∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i) : 15 ≤ b :=
  L14.covering_card_lower_bound hv hstrict B hsize hcover

example {n : ℕ} (hn : 0 < n) :
    IsLeast {b : ℕ | ∃ B : Fin b → Finset (Fin (70 * n)),
      (∀ i, (B i).card = 21 * n) ∧ (∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i)} 15 :=
  L14.covering70_exact_scaled hn

example {n : ℕ} (hn : 0 < n) :
    IsLeast {b : ℕ | ∃ B : Fin b → Finset (Fin (69 * n)),
      (∀ i, (B i).card = 21 * n) ∧ (∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i)} 14 :=
  L14.covering69_exact_scaled hn

#print axioms L14.mills_eq_seven_twentyThree
#print axioms L14.fractional_matching_maximum
#print axioms L14.witness_mem_millsValues
#print axioms L14.covering_card_lower_bound
#print axioms L14.covering70_exact_scaled
#print axioms L14.covering69_exact_scaled

open Lean in
run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for theoremName in [``L14.mills_eq_seven_twentyThree, ``L14.fractional_matching_maximum,
      ``L14.witness_mem_millsValues, ``L14.covering_card_lower_bound,
      ``L14.covering70_exact_scaled, ``L14.covering69_exact_scaled] do
    for name in ← collectAxioms theoremName do
      unless allowed.contains name do
        throwError "Unexpected axiom in {theoremName}: {name}"
