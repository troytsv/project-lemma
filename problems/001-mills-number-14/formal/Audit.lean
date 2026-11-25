import Lemma
import Lean.Util.CollectAxioms

-- State the user-facing contract independently of any auxiliary definition.
example : ∀ blocks : Fin 14 → Finset (Fin 70),
    (∀ i, (blocks i).card = 21) →
    ¬ (∀ x y : Fin 70, x ≠ y → ∃ i, x ∈ blocks i ∧ y ∈ blocks i) :=
  C7021.noFourteenBlockCover

#print axioms C7021.noFourteenBlockCover

open Lean in
run_cmd do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let used ← collectAxioms ``C7021.noFourteenBlockCover
  for name in used do
    unless allowed.contains name do
      throwError "Unexpected axiom in the covering proof: {name}"
