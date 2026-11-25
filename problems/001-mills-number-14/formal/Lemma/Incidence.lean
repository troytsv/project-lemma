import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace C7021

theorem incidence
    (P : Fin 70 → Finset (Fin 14)) (s : Finset (Fin 70)) (w : Fin 70 → ℚ)
    (hi : ∀ p q, (P p ∩ P q).Nonempty)
    (hw : ∀ p ∈ s, 0 < w p)
    (hm : (∑ p ∈ s, w p) = 30)
    (hc : ∀ i, (∑ p ∈ s, if i ∈ P p then w p else 0) ≤ 9) :
    (∀ p ∈ s, 4 ≤ (P p).card) ∧
    (∀ p ∈ s, (P p).card = 4 → w p ≤ 2) ∧
    (∀ p ∈ s, (P p).card = 5 → w p ≤ 15 / 4) ∧
    (∑ p ∈ s, (((P p).card : ℚ) - 4) * w p) ≤ 6 ∧
    ((∑ p ∈ s, (((P p).card : ℚ) - 4) * w p) = 6 →
      ∀ i, (∑ p ∈ s, if i ∈ P p then w p else 0) = 9) := by
  let load (i : Fin 14) : ℚ := ∑ p ∈ s, if i ∈ P p then w p else 0
  have sum_load (A : Finset (Fin 14)) :
      (∑ i ∈ A, load i) = ∑ q ∈ s, ((A ∩ P q).card : ℚ) * w q := by
    dsimp only [load]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  have upper (A : Finset (Fin 14)) : (∑ i ∈ A, load i) ≤ (A.card : ℚ) * 9 := by
    calc
      (∑ i ∈ A, load i) ≤ ∑ _i ∈ A, (9 : ℚ) :=
        Finset.sum_le_sum fun i _ => hc i
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  have pair_card (p q : Fin 70) : (1 : ℚ) ≤ ((P p ∩ P q).card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr (hi p q)
  have individual (p : Fin 70) (hp : p ∈ s) :
      30 + (((P p).card : ℚ) - 1) * w p ≤ ((P p).card : ℚ) * 9 := by
    calc
      _ = ∑ q ∈ s, (w q + if q = p then (((P p).card : ℚ) - 1) * w q else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hp, hm]
      _ ≤ ∑ q ∈ s, ((P p ∩ P q).card : ℚ) * w q := by
        apply Finset.sum_le_sum
        intro q hq
        by_cases heq : q = p
        · subst q
          simp only [Finset.inter_self, if_true]
          ring_nf
          exact le_rfl
        · simpa only [if_neg heq, add_zero, one_mul] using
            (mul_le_mul_of_nonneg_right (pair_card p q) (hw q hq).le)
      _ = ∑ i ∈ P p, load i := (sum_load (P p)).symm
      _ ≤ _ := upper (P p)
  have excess :
      (∑ p ∈ s, (((P p).card : ℚ) - 4) * w p) = (∑ i : Fin 14, load i) - 120 := by
    calc
      _ = (∑ p ∈ s, ((P p).card : ℚ) * w p) - 4 * (∑ p ∈ s, w p) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by
        rw [hm, sum_load Finset.univ]
        norm_num [Finset.univ_inter]
  have all_upper : (∑ i : Fin 14, load i) ≤ 126 := by
    have h := upper Finset.univ
    norm_num at h
    exact h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    have hcard : (1 : ℚ) ≤ ((P p).card : ℚ) := by
      simpa only [Finset.inter_self] using pair_card p p
    by_contra! hsmall
    have hsmallNat : (P p).card ≤ 3 := by omega
    have hsmallRat : ((P p).card : ℚ) ≤ 3 := by exact_mod_cast hsmallNat
    have hnonneg := mul_nonneg (sub_nonneg.mpr hcard) (hw p hp).le
    linarith [individual p hp]
  · intro p hp hcard
    have h := individual p hp
    norm_num [hcard] at h
    linarith
  · intro p hp hcard
    have h := individual p hp
    norm_num [hcard] at h
    linarith
  · rw [excess]
    linarith
  · intro heq i
    rw [excess] at heq
    have hsum : (∑ j : Fin 14, load j) = ∑ _j : Fin 14, (9 : ℚ) := by
      calc
        _ = (126 : ℚ) := by linarith
        _ = _ := by norm_num [Finset.sum_const, nsmul_eq_mul]
    exact (Finset.sum_eq_sum_iff_of_le (fun j _ => hc j)).mp hsum i (Finset.mem_univ i)

end C7021
