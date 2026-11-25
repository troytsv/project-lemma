import L14.Sparse

open Finset

namespace L14

/-- Unit vertex capacities impose these restrictions on any mass above thirteen fourths. -/
theorem largeMassStructure (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 < w p) (hm : (∑ p ∈ s, w p) = W)
    (hW : 13 / 4 < W) (hc : ∀ i, load s w i ≤ 1) :
    (∀ p ∈ s, 4 ≤ p.card) ∧
    (∀ p ∈ s, p.card = 4 → w p < 1 / 4) ∧
    (∑ p ∈ s, ((p.card : ℝ) - 4) * w p) ≤ 14 - 4 * W ∧
    (∑ p ∈ s.filter (fun p => 4 < p.card), w p) < 1 ∧
    10 ≤ (s.filter (fun p => p.card = 4)).card := by
  have sumLoads (a : Edge) :
      (∑ i ∈ a, load s w i) = ∑ q ∈ s, ((a ∩ q).card : ℝ) * w q := by
    dsimp only [load]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  have capacity (a : Edge) : (∑ i ∈ a, load s w i) ≤ (a.card : ℝ) := calc
    _ ≤ ∑ _i ∈ a, (1 : ℝ) := sum_le_sum fun i _ => hc i
    _ = _ := by simp [sum_const, nsmul_eq_mul]
  have pairCard (p : Edge) (hp : p ∈ s) (q : Edge) (hq : q ∈ s) :
      (1 : ℝ) ≤ ((p ∩ q).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hi p hp q hq)
  have individual (p : Edge) (hp : p ∈ s) :
      W + ((p.card : ℝ) - 1) * w p ≤ (p.card : ℝ) := by
    calc
      _ = ∑ q ∈ s, (w q + if q = p then ((p.card : ℝ) - 1) * w q else 0) := by
        rw [sum_add_distrib, sum_ite_eq', if_pos hp, hm]
      _ ≤ ∑ q ∈ s, ((p ∩ q).card : ℝ) * w q := by
        apply sum_le_sum
        intro q hq
        by_cases heq : q = p
        · subst q
          simp only [inter_self, if_true]
          ring_nf
          exact le_rfl
        · simpa only [if_neg heq, add_zero, one_mul] using
            (mul_le_mul_of_nonneg_right (pairCard p hp q hq) (hw q hq).le)
      _ = ∑ i ∈ p, load s w i := (sumLoads p).symm
      _ ≤ _ := capacity p
  have rankMin (p : Edge) (hp : p ∈ s) : 4 ≤ p.card := by
    have hcard : (1 : ℝ) ≤ (p.card : ℝ) := by
      simpa only [inter_self] using pairCard p hp p hp
    have hnonneg := mul_nonneg (sub_nonneg.mpr hcard) (hw p hp).le
    by_contra! hsmall
    have hsmallNat : p.card ≤ 3 := by omega
    have hsmallReal : (p.card : ℝ) ≤ 3 := by exact_mod_cast hsmallNat
    linarith [individual p hp]
  have weightFour (p : Edge) (hp : p ∈ s) (hcard : p.card = 4) : w p < 1 / 4 := by
    have h := individual p hp
    norm_num [hcard] at h
    linarith
  have excess : (∑ p ∈ s, ((p.card : ℝ) - 4) * w p) ≤ 14 - 4 * W := by
    have hcap := capacity univ
    simp only [card_univ, Fintype.card_fin, Nat.cast_ofNat] at hcap
    rw [sumLoads univ] at hcap
    simp only [univ_inter] at hcap
    simp only [sub_mul, sum_sub_distrib, ← mul_sum, hm]
    linarith
  have highMass : (∑ p ∈ s.filter (fun p => 4 < p.card), w p) < 1 := by
    have hbound : (∑ p ∈ s.filter (fun p => 4 < p.card), w p) ≤
        ∑ p ∈ s, ((p.card : ℝ) - 4) * w p := by
      rw [sum_filter]
      apply sum_le_sum
      intro p hp
      by_cases hr : 4 < p.card
      · have hfive : 5 ≤ p.card := by omega
        have hfiveReal : (5 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast hfive
        simpa only [if_pos hr, one_mul] using
          mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (p.card : ℝ) - 4 by linarith)
            (hw p hp).le
      · have hfourReal : (4 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast rankMin p hp
        simpa only [if_neg hr] using mul_nonneg (sub_nonneg.mpr hfourReal) (hw p hp).le
    linarith [hbound.trans excess]
  let four := s.filter (fun p => p.card = 4)
  have partition :
      (∑ p ∈ four, w p) + (∑ p ∈ s.filter (fun p => 4 < p.card), w p) = W := by
    simp only [four, sum_filter, ← sum_add_distrib, ← hm]
    apply sum_congr rfl
    intro p hp
    by_cases hfour : p.card = 4
    · simp [hfour]
    · have hfive : 4 < p.card := lt_of_le_of_ne (rankMin p hp) (Ne.symm hfour)
      simp [hfour, hfive]
  have fourBound : (∑ p ∈ four, w p) ≤ (four.card : ℝ) * (1 / 4) := calc
    _ ≤ ∑ p ∈ four, (1 / 4 : ℝ) := sum_le_sum fun p hp =>
      (weightFour p (mem_filter.mp hp).1 (mem_filter.mp hp).2).le
    _ = _ := by simp [sum_const, nsmul_eq_mul]
  have manyFour : 10 ≤ four.card := by
    by_contra! h
    have hnine : four.card ≤ 9 := by omega
    have hnineReal : (four.card : ℝ) ≤ 9 := by exact_mod_cast hnine
    linarith
  exact ⟨rankMin, weightFour, excess, highMass, manyFour⟩

/-- A putative improvement over the projective plane can be carried by at most fourteen edges. -/
theorem sparseReduction (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (hW : 13 / 4 < W) (hc : ∀ i, load s w i ≤ 1) :
    ∃ (t : Finset Edge) (v : Edge → ℝ),
      t ⊆ s ∧ t.card ≤ 14 ∧ Intersecting t ∧
      (∀ p ∈ t, 0 < v p) ∧ (∑ p ∈ t, v p) = W ∧ (∀ i, load t v i ≤ 1) ∧
      (∀ p ∈ t, 4 ≤ p.card) ∧
      (∀ p ∈ t, p.card = 4 → v p < 1 / 4) ∧
      (∑ p ∈ t, ((p.card : ℝ) - 4) * v p) ≤ 14 - 4 * W ∧
      (∑ p ∈ t.filter (fun p => 4 < p.card), v p) < 1 ∧
      10 ≤ (t.filter (fun p => p.card = 4)).card := by
  obtain ⟨t, v, hsub, hcard, hv, hmass, hload⟩ := sparse s w hi hw hm (by linarith)
  have ht := hi.mono hsub
  have hcap i := (hload i).trans (hc i)
  exact ⟨t, v, hsub, hcard, ht, hv, hmass, hcap, largeMassStructure t v W ht hv hmass hW hcap⟩

end L14
