import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace C7021

theorem rankCases (s : Finset (Fin 70)) (w : Fin 70 → ℚ) (r : Fin 70 → ℕ)
    (hs : s.card ≤ 14) (hw : ∀ p ∈ s, 0 < w p) (hm : (∑ p ∈ s, w p) = 30)
    (hr : ∀ p ∈ s, 4 ≤ r p) (h4 : ∀ p ∈ s, r p = 4 → w p ≤ 2)
    (h5 : ∀ p ∈ s, r p = 5 → w p ≤ 15 / 4)
    (he : (∑ p ∈ s, ((r p : ℚ) - 4) * w p) ≤ 6) :
    (∀ p ∈ s, r p = 4 → w p = 2) ∧ (∀ p ∈ s, r p ≠ 4 → r p = 5) ∧
      (s.filter (fun p => r p ≠ 4)).card ≤ 2 ∧
      (∑ p ∈ s, ((r p : ℚ) - 4) * w p) = 6 := by
  let rankFour := s.filter fun p => r p = 4
  let higher := s.filter fun p => r p ≠ 4
  let excess (p : Fin 70) : ℚ := ((r p : ℚ) - 4) * w p
  change (∑ p ∈ s, excess p) ≤ 6 at he
  have cardSplit : rankFour.card + higher.card = s.card := by
    apply Finset.filter_card_add_filter_neg_card_eq_card
  have weightSplit : (∑ p ∈ rankFour, w p) + (∑ p ∈ higher, w p) = 30 := by
    rw [← hm]
    apply Finset.sum_filter_add_sum_filter_not
  have excessSplit : (∑ p ∈ rankFour, excess p) + (∑ p ∈ higher, excess p) =
      ∑ p ∈ s, excess p := by
    apply Finset.sum_filter_add_sum_filter_not
  have excessFour : (∑ p ∈ rankFour, excess p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [excess, (Finset.mem_filter.mp hp).2]
  rw [excessFour, zero_add] at excessSplit
  have higherBudget : (∑ p ∈ higher, excess p) ≤ 6 := excessSplit.trans_le he
  have higherRank : ∀ p ∈ higher, 5 ≤ r p := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hp4⟩
    have := hr p hps
    omega
  have higherPositive : ∀ p ∈ higher, 0 < w p := by
    intro p hp
    exact hw p (Finset.mem_filter.mp hp).1
  have weight_le_excess : ∀ p ∈ higher, w p ≤ excess p := by
    intro p hp
    have rankBound : (5 : ℚ) ≤ r p := by exact_mod_cast higherRank p hp
    have factorBound : (1 : ℚ) ≤ (r p : ℚ) - 4 := by linarith
    simpa only [excess, one_mul] using
      mul_le_mul_of_nonneg_right factorBound (higherPositive p hp).le
  have higherWeightBound : (∑ p ∈ higher, w p) ≤ ∑ p ∈ higher, excess p :=
    Finset.sum_le_sum weight_le_excess
  have fourWeightBound : ∀ p ∈ rankFour, w p ≤ 2 := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hps, hp4⟩
    exact h4 p hps hp4
  have fourTotalBound : (∑ p ∈ rankFour, w p) ≤ 2 * (rankFour.card : ℚ) := by
    calc
      (∑ p ∈ rankFour, w p) ≤ ∑ _p ∈ rankFour, (2 : ℚ) :=
        Finset.sum_le_sum fourWeightBound
      _ = _ := by simp [mul_comm]
  have fourCardMin : 12 ≤ rankFour.card := by
    by_contra! h
    have hcast : (rankFour.card : ℚ) < 12 := by exact_mod_cast h
    linarith
  have higherCardMax : higher.card ≤ 2 := by omega
  have fourCardMax : rankFour.card ≤ 12 := by
    by_contra! h
    have higherCardOne : (higher.card : ℚ) ≤ 1 := by
      exact_mod_cast (show higher.card ≤ 1 by omega)
    have totalCardBound : (rankFour.card : ℚ) + (higher.card : ℚ) ≤ 14 := by
      exact_mod_cast (show rankFour.card + higher.card ≤ 14 by omega)
    have pointBound : ∀ p ∈ higher, w p ≤ 15 / 4 := by
      intro p hp
      by_cases hp5 : r p = 5
      · exact h5 p (Finset.mem_filter.mp hp).1 hp5
      · have rankBound : (6 : ℚ) ≤ r p := by
          have := higherRank p hp
          exact_mod_cast (show 6 ≤ r p by omega)
        have factorBound : (2 : ℚ) ≤ (r p : ℚ) - 4 := by linarith
        have weightBound : 2 * w p ≤ excess p :=
          mul_le_mul_of_nonneg_right factorBound (higherPositive p hp).le
        have singleBound : excess p ≤ ∑ q ∈ higher, excess q :=
          Finset.single_le_sum
            (fun q hq => (higherPositive q hq).le.trans (weight_le_excess q hq)) hp
        linarith
    have higherTotalBound : (∑ p ∈ higher, w p) ≤ (15 / 4 : ℚ) * (higher.card : ℚ) := by
      calc
        (∑ p ∈ higher, w p) ≤ ∑ _p ∈ higher, (15 / 4 : ℚ) :=
          Finset.sum_le_sum pointBound
        _ = _ := by simp [mul_comm]
    linarith
  have fourCard : rankFour.card = 12 := le_antisymm fourCardMax fourCardMin
  simp only [fourCard, Nat.cast_ofNat] at fourTotalBound
  have fourWeight : (∑ p ∈ rankFour, w p) = 24 := by linarith
  have higherWeight : (∑ p ∈ higher, w p) = 6 := by linarith
  have higherExcess : (∑ p ∈ higher, excess p) = 6 := by linarith
  refine ⟨?_, ?_, higherCardMax, excessSplit.symm.trans higherExcess⟩
  · intro p hp hp4
    have hmem : p ∈ rankFour := Finset.mem_filter.mpr ⟨hp, hp4⟩
    have tight : (∑ q ∈ rankFour, w q) = ∑ _q ∈ rankFour, (2 : ℚ) := by
      norm_num [fourWeight, fourCard]
    exact (Finset.sum_eq_sum_iff_of_le fourWeightBound).mp tight p hmem
  · intro p hp hp4
    have hmem : p ∈ higher := Finset.mem_filter.mpr ⟨hp, hp4⟩
    have tight := (Finset.sum_eq_sum_iff_of_le weight_le_excess).mp
      (higherWeight.trans higherExcess.symm) p hmem
    have productEq : 1 * w p = ((r p : ℚ) - 4) * w p := by
      simpa only [excess, one_mul] using tight
    have factorEq := mul_right_cancel₀ (higherPositive p hmem).ne' productEq
    exact_mod_cast (show (r p : ℚ) = 5 by linarith)

end C7021
