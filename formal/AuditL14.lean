import L14
import Lean.Util.CollectAxioms

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

#print axioms L14.mills_eq_seven_twentyThree
#print axioms L14.fractional_matching_maximum

open Lean in
run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  for theoremName in [``L14.mills_eq_seven_twentyThree, ``L14.fractional_matching_maximum] do
    for name in ← collectAxioms theoremName do
      unless allowed.contains name do
        throwError "Unexpected axiom in {theoremName}: {name}"
