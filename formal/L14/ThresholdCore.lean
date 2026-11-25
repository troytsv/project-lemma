import L14.Reduction

open Finset

namespace L14

theorem sumLoadsOn (s : Finset Edge) (w : Edge → ℝ) (a : Edge) :
    (∑ i ∈ a, load s w i) = ∑ q ∈ s, ((a ∩ q).card : ℝ) * w q := by
  dsimp only [load]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]

theorem loadNonneg (s : Finset Edge) (w : Edge → ℝ)
    (hw : ∀ p ∈ s, 0 ≤ w p) (i : Fin 14) : 0 ≤ load s w i := by
  apply sum_nonneg
  intro p hp
  split_ifs
  · exact hw p hp
  · exact le_rfl

theorem sumLoadsCap (s : Finset Edge) (w : Edge → ℝ) (C : ℝ)
    (hc : ∀ i, load s w i ≤ C) (a : Edge) :
    (∑ i ∈ a, load s w i) ≤ (a.card : ℝ) * C := calc
  _ ≤ ∑ _i ∈ a, C := sum_le_sum fun i _ => hc i
  _ = _ := by simp [sum_const, nsmul_eq_mul]

theorem edgeLoadLower (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (p : Edge) (hp : p ∈ s) :
    W + ((p.card : ℝ) - 1) * w p ≤ ∑ i ∈ p, load s w i := by
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
      · have hcard : (1 : ℝ) ≤ ((p ∩ q).card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr (hi p hp q hq)
        simpa only [if_neg heq, add_zero, one_mul] using
          mul_le_mul_of_nonneg_right hcard (hw q hq)
    _ = ∑ i ∈ p, load s w i := (sumLoadsOn s w p).symm

theorem edgeCapacity (s : Finset Edge) (w : Edge → ℝ) (W C : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (hc : ∀ i, load s w i ≤ C) (p : Edge) (hp : p ∈ s) :
    W + ((p.card : ℝ) - 1) * w p ≤ (p.card : ℝ) * C :=
  (edgeLoadLower s w W hi hw hm p hp).trans (sumLoadsCap s w C hc p)

theorem edgeLoadOverlap (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hm : (∑ p ∈ s, w p) = W) (p : Edge) (hp : p ∈ s) :
    (∑ i ∈ p, load s w i) = W + ((p.card : ℝ) - 1) * w p +
      ∑ q ∈ s.erase p, (((p ∩ q).card : ℝ) - 1) * w q := by
  have overlap :
      (∑ q ∈ s.erase p, (((p ∩ q).card : ℝ) - 1) * w q) + ((p.card : ℝ) - 1) * w p =
        ∑ q ∈ s, (((p ∩ q).card : ℝ) - 1) * w q := by
    simpa only [inter_self] using
      sum_erase_add s (fun q => (((p ∩ q).card : ℝ) - 1) * w q) hp
  rw [add_assoc, add_comm (((p.card : ℝ) - 1) * w p), overlap, sumLoadsOn]
  simp only [sub_mul, one_mul, sum_sub_distrib, hm]
  ring

theorem weightedSumLoads (s : Finset Edge) (w : Edge → ℝ) (f : Fin 14 → ℝ) :
    (∑ i, f i * load s w i) = ∑ p ∈ s, w p * ∑ i ∈ p, f i := by
  calc
    _ = ∑ i : Fin 14, ∑ p ∈ s, if i ∈ p then f i * w p else 0 := by
      simp only [load, mul_sum, mul_ite, mul_zero]
    _ = ∑ p ∈ s, ∑ i : Fin 14, if i ∈ p then f i * w p else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro p _
      rw [← sum_filter, ← sum_mul, filter_mem_eq_inter, univ_inter, mul_comm]

/-- The load-square moment retains the extra self-intersection of each support edge. -/
theorem loadSquareMoment (s : Finset Edge) (w : Edge → ℝ) (W C : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (hc : ∀ i, load s w i ≤ C) :
    W ^ 2 + (∑ p ∈ s, ((p.card : ℝ) - 1) * w p ^ 2) ≤ (∑ i, load s w i ^ 2) ∧
    (∑ i, load s w i ^ 2) ≤ C * (∑ p ∈ s, (p.card : ℝ) * w p) := by
  have hmoment : (∑ i, load s w i ^ 2) = ∑ p ∈ s, w p * ∑ i ∈ p, load s w i := by
    simpa only [pow_two] using weightedSumLoads s w (load s w)
  rw [hmoment]
  constructor
  · calc
      _ = ∑ p ∈ s, (w p * W + ((p.card : ℝ) - 1) * w p ^ 2) := by
        rw [sum_add_distrib, ← sum_mul, hm, pow_two]
      _ = ∑ p ∈ s, w p * (W + ((p.card : ℝ) - 1) * w p) := by
        apply sum_congr rfl
        intro p _
        ring
      _ ≤ _ := sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_left (edgeLoadLower s w W hi hw hm p hp) (hw p hp)
  · calc
      _ ≤ ∑ p ∈ s, w p * ((p.card : ℝ) * C) := sum_le_sum fun p hp =>
        mul_le_mul_of_nonneg_left (sumLoadsCap s w C hc p) (hw p hp)
      _ = _ := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        ring

/-- The excess over rank four is limited by the total load remaining under the cap. -/
theorem capTenExcess (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hm : (∑ p ∈ s, w p) = W) (hc : ∀ i, load s w i ≤ 10) :
    (∑ p ∈ s, ((p.card : ℝ) - 4) * w p) ≤ 140 - 4 * W := by
  have hcap := sumLoadsCap s w 10 hc univ
  rw [sumLoadsOn] at hcap
  norm_num [univ_inter] at hcap
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, hm]
  linarith

/-- Mass above 33 under cap ten requires at least eleven rank-four edges. -/
theorem capTenStructure (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (hW : 33 < W) (hc : ∀ i, load s w i ≤ 10) :
    (∀ p ∈ s, 4 ≤ p.card) ∧
    (∀ p ∈ s, p.card = 4 → w p < 7 / 3) ∧
    (∑ p ∈ s, ((p.card : ℝ) - 4) * w p) ≤ 140 - 4 * W ∧
    (∑ p ∈ s.filter (fun p => 4 < p.card), w p) < 8 ∧
    11 ≤ (s.filter (fun p => p.card = 4)).card := by
  have individual := edgeCapacity s w W 10 hi hw hm hc
  have rankMin (p : Edge) (hp : p ∈ s) : 4 ≤ p.card := by
    have hn : p.Nonempty := by simpa using hi p hp p hp
    have hcard : (1 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast card_pos.mpr hn
    have hnonneg := mul_nonneg (sub_nonneg.mpr hcard) (hw p hp)
    by_contra! hsmall
    have hsmallNat : p.card ≤ 3 := by omega
    have hsmallReal : (p.card : ℝ) ≤ 3 := by exact_mod_cast hsmallNat
    linarith [individual p hp]
  have weightFour (p : Edge) (hp : p ∈ s) (hcard : p.card = 4) : w p < 7 / 3 := by
    have h := individual p hp
    norm_num [hcard] at h
    linarith
  have excess := capTenExcess s w W hm hc
  have highMass : (∑ p ∈ s.filter (fun p => 4 < p.card), w p) < 8 := by
    have hbound : (∑ p ∈ s.filter (fun p => 4 < p.card), w p) ≤
        ∑ p ∈ s, ((p.card : ℝ) - 4) * w p := by
      rw [sum_filter]
      apply sum_le_sum
      intro p hp
      by_cases hr : 4 < p.card
      · have hfive : 5 ≤ p.card := by omega
        have hfiveReal : (5 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast hfive
        simpa only [if_pos hr, one_mul] using
          mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (p.card : ℝ) - 4 by linarith) (hw p hp)
      · have hfourReal : (4 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast rankMin p hp
        simpa only [if_neg hr] using mul_nonneg (sub_nonneg.mpr hfourReal) (hw p hp)
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
  have fourBound : (∑ p ∈ four, w p) ≤ (four.card : ℝ) * (7 / 3) := calc
    _ ≤ ∑ p ∈ four, (7 / 3 : ℝ) := sum_le_sum fun p hp =>
      (weightFour p (mem_filter.mp hp).1 (mem_filter.mp hp).2).le
    _ = _ := by simp [sum_const, nsmul_eq_mul]
  have manyFour : 11 ≤ four.card := by
    by_contra! h
    have hten : four.card ≤ 10 := by omega
    have htenReal : (four.card : ℝ) ≤ 10 := by exact_mod_cast hten
    linarith
  exact ⟨rankMin, weightFour, excess, highMass, manyFour⟩

/-- Above thirteen fourths of the cap, every vertex contained only in fours has degree at least five. -/
theorem rankFourStar (s : Finset Edge) (w : Edge → ℝ) (W C : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (hW : 13 * C < 4 * W) (hc : ∀ i, load s w i ≤ C) (rankMin : ∀ p ∈ s, 4 ≤ p.card)
    (x : Fin 14) (hx : ∀ p ∈ s, x ∈ p → p.card = 4) :
    5 ≤ (s.filter (fun p => x ∈ p)).card := by
  let star := s.filter (fun p => x ∈ p)
  change 5 ≤ star.card
  have hstarMass : (∑ p ∈ star, w p) = load s w x := by simp [star, load, sum_filter]
  have hoffMass : (∑ p ∈ s, if x ∈ p then 0 else w p) = W - load s w x := by
    rw [← hm, load, ← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    by_cases hp : x ∈ p <;> simp [hp]
  by_contra! hsmall
  by_cases hzero : star.card = 0
  · let a : Edge := univ.erase x
    have haCard : a.card = 13 := by simp [a, Finset.card_erase_of_mem]
    have hno : ∀ p ∈ s, x ∉ p := by
      intro p hp hpx
      have hmem : p ∈ star := mem_filter.mpr ⟨hp, hpx⟩
      exact (Finset.notMem_empty p) (Finset.card_eq_zero.mp hzero ▸ hmem)
    have hsum : 4 * W ≤ ∑ i ∈ a, load s w i := by
      rw [← hm, mul_sum, sumLoadsOn]
      apply sum_le_sum
      intro p hp
      have hin : p ⊆ a := by
        intro i hi
        exact mem_erase.mpr ⟨fun heq => hno p hp (heq ▸ hi), mem_univ i⟩
      rw [inter_eq_right.mpr hin]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast rankMin p hp) (hw p hp)
    have hcap := sumLoadsCap s w C hc a
    norm_num [haCard] at hcap
    linarith
  have hlocal (p : Edge) (hp : p ∈ star) :
      W - load s w x + 3 * w p ≤ 3 * C := by
    obtain ⟨hps, hpx⟩ := mem_filter.mp hp
    have hcard : (p.erase x).card = 3 := by rw [card_erase_of_mem hpx, hx p hps hpx]
    have hlower : W - load s w x + 3 * w p ≤ ∑ i ∈ p.erase x, load s w i := by
      have hdiag : (∑ q ∈ s, if q = p then 3 * w q else 0) = 3 * w p := by
        rw [sum_ite_eq', if_pos hps]
      rw [← hoffMass, ← hdiag, ← sum_add_distrib, sumLoadsOn]
      apply sum_le_sum
      intro q hq
      by_cases hqp : q = p
      · subst q
        rw [if_pos hpx, if_pos rfl, zero_add, inter_eq_left.mpr (erase_subset _ _), hcard]
        norm_num
      · rw [if_neg hqp, add_zero]
        by_cases hqx : x ∈ q
        · rw [if_pos hqx]
          exact mul_nonneg (Nat.cast_nonneg _) (hw q hq)
        · rw [if_neg hqx]
          obtain ⟨i, hiq⟩ := hi p hps q hq
          obtain ⟨hip, hiq⟩ := mem_inter.mp hiq
          have hiq' : i ∈ p.erase x ∩ q :=
            mem_inter.mpr ⟨mem_erase.mpr ⟨fun heq => hqx (heq ▸ hiq), hip⟩, hiq⟩
          have hpos : (1 : ℝ) ≤ (((p.erase x ∩ q).card : ℕ) : ℝ) := by
            exact_mod_cast card_pos.mpr (show (p.erase x ∩ q).Nonempty from ⟨i, hiq'⟩)
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hpos (hw q hq)
    have hcap := sumLoadsCap s w C hc (p.erase x)
    norm_num [hcard] at hcap
    exact hlower.trans hcap
  have hsum : (star.card : ℝ) * (W - load s w x) + 3 * load s w x ≤ (star.card : ℝ) * (3 * C) := by
    have h := sum_le_sum (fun p hp => hlocal p hp)
    simpa only [sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, hstarMass] using h
  have hpos : 1 ≤ star.card := by omega
  have hnonneg := loadNonneg s w hw x
  have hcap := hc x
  have hC := hnonneg.trans hcap
  interval_cases star.card <;> norm_num at hsum <;> linarith

/-- Under the cap of ten, a vertex contained only in rank-four edges is in at least five edges. -/
theorem capTenStar (s : Finset Edge) (w : Edge → ℝ) (W : ℝ)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 ≤ w p) (hm : (∑ p ∈ s, w p) = W)
    (hW : 33 < W) (hc : ∀ i, load s w i ≤ 10) (rankMin : ∀ p ∈ s, 4 ≤ p.card)
    (x : Fin 14) (hx : ∀ p ∈ s, x ∈ p → p.card = 4) :
    5 ≤ (s.filter (fun p => x ∈ p)).card :=
  rankFourStar s w W 10 hi hw hm (by linarith) hc rankMin x hx

end L14
