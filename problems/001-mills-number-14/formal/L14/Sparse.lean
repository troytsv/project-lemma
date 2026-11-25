import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

open Finset

namespace L14

abbrev Edge := Finset (Fin 14)

def Intersecting (s : Finset Edge) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, (p ∩ q).Nonempty

def load (s : Finset Edge) (w : Edge → ℝ) (i : Fin 14) : ℝ :=
  ∑ p ∈ s, if i ∈ p then w p else 0

private theorem load_eq (s : Finset Edge) (w : Edge → ℝ) (i : Fin 14) :
    load s w i = ∑ p ∈ s.filter (fun p => i ∈ p), w p := by
  simp only [load, sum_filter]

private theorem direction (s : Finset Edge) (hlarge : 14 < s.card) :
    ∃ d : Edge → ℝ, (∃ p ∈ s, d p ≠ 0) ∧ (∀ i, load s d i = 0) ∧
      (∑ p ∈ s, d p) ≤ 0 := by
  classical
  let incidence (p : Edge) (i : Fin 14) : ℝ := if i ∈ p then 1 else 0
  have dependent : ¬ LinearIndepOn ℝ incidence (s : Set Edge) := by
    intro independent
    change LinearIndependent ℝ (fun p : s => incidence p) at independent
    exact (not_le_of_gt hlarge) (by simpa [Module.finrank_pi] using
      independent.fintype_card_le_finrank)
  rw [linearIndepOn_finset_iff] at dependent
  push_neg at dependent
  obtain ⟨d, hzero, p, hp, hdp⟩ := dependent
  have hload (i : Fin 14) : load s d i = 0 := by
    have hcoord := congrFun hzero i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, incidence,
      mul_ite, mul_one, mul_zero, Pi.zero_apply, load] using hcoord
  by_cases hsum : (∑ p ∈ s, d p) ≤ 0
  · exact ⟨d, ⟨p, hp, hdp⟩, hload, hsum⟩
  · refine ⟨fun p => -d p, ⟨p, hp, neg_ne_zero.mpr hdp⟩, ?_, ?_⟩
    · intro i
      rw [load_eq, sum_neg_distrib, ← load_eq s d i, hload i, neg_zero]
    · rw [sum_neg_distrib]
      exact neg_nonpos.mpr (le_of_lt (lt_of_not_ge hsum))

/-- Shrink a positive support to at most fourteen members without losing mass or changing loads. -/
theorem reduceSupport (s : Finset Edge) (w : Edge → ℝ)
    (hn : ∀ p ∈ s, p.Nonempty) (hw : ∀ p ∈ s, 0 < w p) :
    ∃ (t : Finset Edge) (v : Edge → ℝ), t ⊆ s ∧ t.card ≤ 14 ∧
      (∀ p ∈ t, 0 < v p) ∧ (∑ p ∈ s, w p) ≤ (∑ p ∈ t, v p) ∧
      ∀ i, load t v i = load s w i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with | _ s ih
  by_cases hs : s.card ≤ 14
  · exact ⟨s, w, Subset.rfl, hs, hw, le_rfl, fun _ => rfl⟩
  obtain ⟨d, hd, hdload, hdsum⟩ := direction s (lt_of_not_ge hs)
  let decreasing := s.filter (fun p => 0 < d p)
  have hdecreasing : decreasing.Nonempty := by
    by_contra! h
    obtain ⟨p, hp, hdp⟩ := hd
    obtain ⟨i, hi⟩ := hn p hp
    have nonpos (q : Edge) (hq : q ∈ s) : d q ≤ 0 := by
      apply le_of_not_gt
      intro hdq
      exact h ⟨q, mem_filter.mpr ⟨hq, hdq⟩⟩
    have negative : load s d i < 0 := calc
      _ < ∑ q ∈ s, (0 : ℝ) := by
        apply sum_lt_sum
        · intro q hq
          by_cases hqi : i ∈ q
          · simp [hqi, nonpos q hq]
          · simp [hqi]
        · exact ⟨p, hp, by simpa [hi] using lt_of_le_of_ne (nonpos p hp) hdp⟩
      _ = 0 := by simp
    exact (ne_of_lt negative) (hdload i)
  obtain ⟨p, hp, smallest⟩ := exists_min_image decreasing (fun q => w q / d q) hdecreasing
  obtain ⟨hps, hpd⟩ := mem_filter.mp hp
  let step := w p / d p
  have hstep : 0 < step := div_pos (hw p hps) hpd
  let v (q : Edge) := w q - step * d q
  have hv (q : Edge) (hq : q ∈ s) : 0 ≤ v q := by
    apply sub_nonneg.mpr
    by_cases hqd : 0 < d q
    · exact (le_div_iff₀ hqd).mp (smallest q (mem_filter.mpr ⟨hq, hqd⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos hstep.le (le_of_not_gt hqd)).trans (hw q hq).le
  have hvp : v p = 0 := by
    simp [v, step, div_mul_cancel₀ _ (ne_of_gt hpd)]
  let t := s.filter (fun q => 0 < v q)
  have ht : t ⊂ s := (ssubset_iff_of_subset (filter_subset _ _)).2
    ⟨p, hps, by simp [hvp]⟩
  have eraseZeros (f : Edge → ℝ) (hf : ∀ q ∈ s, v q = 0 → f q = 0) :
      (∑ q ∈ t, f q) = ∑ q ∈ s, f q := by
    apply sum_subset (filter_subset _ _)
    intro q hq hqt
    have hnonpos : v q ≤ 0 := le_of_not_gt fun hpos => hqt (mem_filter.mpr ⟨hq, hpos⟩)
    exact hf q hq (le_antisymm hnonpos (hv q hq))
  have mass : (∑ q ∈ s, w q) ≤ ∑ q ∈ t, v q := by
    rw [eraseZeros v (fun _ _ h => h)]
    simp only [v, sum_sub_distrib, ← mul_sum]
    linarith [mul_nonpos_of_nonneg_of_nonpos hstep.le hdsum]
  have loads (i : Fin 14) : load t v i = load s w i := calc
    _ = load s v i := eraseZeros _ (fun q _ hq => by simp [hq])
    _ = _ := by
      simp only [load_eq, v, sum_sub_distrib, ← mul_sum]
      rw [← load_eq s d i, hdload i, mul_zero, sub_zero]
  obtain ⟨u, z, hus, hu, hz, hmass, hloads⟩ :=
    ih t ht v (fun q hq => hn q (ht.subset hq)) (fun q hq => (mem_filter.mp hq).2)
  exact ⟨u, z, hus.trans ht.subset, hu, hz, mass.trans hmass, fun i => (hloads i).trans (loads i)⟩

theorem Intersecting.mono {s t : Finset Edge} (hi : Intersecting s) (hst : t ⊆ s) :
    Intersecting t := by
  intro p hp q hq
  exact hi p (hst hp) q (hst hq)

/-- An intersecting distribution has a sparse distribution with no larger vertex loads. -/
theorem sparse (s : Finset Edge) (w : Edge → ℝ) (hi : Intersecting s)
    (hw : ∀ p ∈ s, 0 ≤ w p) {m : ℝ} (hm : (∑ p ∈ s, w p) = m) (hmpos : 0 < m) :
    ∃ (t : Finset Edge) (v : Edge → ℝ), t ⊆ s ∧ t.card ≤ 14 ∧
      (∀ p ∈ t, 0 < v p) ∧ (∑ p ∈ t, v p) = m ∧ ∀ i, load t v i ≤ load s w i := by
  classical
  let u := s.filter (fun p => 0 < w p)
  have hsub : u ⊆ s := filter_subset _ _
  have eraseZeros (f : Edge → ℝ) (hf : ∀ p ∈ s, w p = 0 → f p = 0) :
      (∑ p ∈ u, f p) = ∑ p ∈ s, f p := by
    apply sum_subset hsub
    intro p hp hpu
    exact hf p hp (le_antisymm (le_of_not_gt fun hpos => hpu (mem_filter.mpr ⟨hp, hpos⟩))
      (hw p hp))
  have hnonempty (p : Edge) (hp : p ∈ u) : p.Nonempty := by
    simpa using hi p (hsub hp) p (hsub hp)
  obtain ⟨t, z, htu, htc, hz, hmass, hload⟩ := reduceSupport u w hnonempty
    (fun p hp => (mem_filter.mp hp).2)
  rw [eraseZeros w (fun _ _ h => h), hm] at hmass
  let total := ∑ p ∈ t, z p
  have htotal : 0 < total := lt_of_lt_of_le hmpos hmass
  let scale := m / total
  have hscale : 0 < scale := div_pos hmpos htotal
  have hscale_le : scale ≤ 1 := (div_le_one htotal).2 hmass
  refine ⟨t, fun p => scale * z p, htu.trans hsub, htc,
    fun p hp => mul_pos hscale (hz p hp), ?_, ?_⟩
  · rw [← mul_sum]
    exact div_mul_cancel₀ m (ne_of_gt htotal)
  · intro i
    have hnonneg : 0 ≤ load t z i := by
      apply sum_nonneg
      intro p hp
      split_ifs
      · exact (hz p hp).le
      · exact le_rfl
    calc
      load t (fun p => scale * z p) i = scale * load t z i := by
        simp only [load_eq, mul_sum]
      _ ≤ load t z i := by simpa using mul_le_mul_of_nonneg_right hscale_le hnonneg
      _ = load u w i := hload i
      _ = load s w i := eraseZeros _ (fun p _ hp => by simp [hp])

end L14
