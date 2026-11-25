module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

@[expose] public section

open Finset

namespace C7021

private def load (P : Fin 70 → Finset (Fin 14)) (s : Finset (Fin 70))
    (w : Fin 70 → ℚ) (i : Fin 14) : ℚ :=
  ∑ p ∈ s, if i ∈ P p then w p else 0

private theorem load_eq (P : Fin 70 → Finset (Fin 14)) (s : Finset (Fin 70))
    (w : Fin 70 → ℚ) (i : Fin 14) :
    load P s w i = ∑ p ∈ s.filter (fun p => i ∈ P p), w p := by
  simp only [load, sum_filter]

private theorem direction (P : Fin 70 → Finset (Fin 14)) (s : Finset (Fin 70))
    (hlarge : 14 < s.card) :
    ∃ d : Fin 70 → ℚ, (∃ p ∈ s, d p ≠ 0) ∧ (∀ i, load P s d i = 0) ∧
      (∑ p ∈ s, d p) ≤ 0 := by
  classical
  let incidence (p : Fin 70) (i : Fin 14) : ℚ := if i ∈ P p then 1 else 0
  have dependent : ¬ LinearIndepOn ℚ incidence (s : Set (Fin 70)) := by
    intro independent
    change LinearIndependent ℚ (fun p : s => incidence p) at independent
    exact (not_le_of_gt hlarge) (by simpa [Module.finrank_pi] using
      independent.fintype_card_le_finrank)
  rw [linearIndepOn_finset_iff] at dependent
  push Not at dependent
  obtain ⟨d, hzero, p, hp, hdp⟩ := dependent
  have hload (i : Fin 14) : load P s d i = 0 := by
    have hcoord := congrFun hzero i
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, incidence,
      mul_ite, mul_one, mul_zero, Pi.zero_apply, load] using hcoord
  by_cases hsum : (∑ p ∈ s, d p) ≤ 0
  · exact ⟨d, ⟨p, hp, hdp⟩, hload, hsum⟩
  · refine ⟨fun p => -d p, ⟨p, hp, neg_ne_zero.mpr hdp⟩, ?_, ?_⟩
    · intro i
      rw [load_eq, sum_neg_distrib, ← load_eq P s d i, hload i, neg_zero]
    · rw [sum_neg_distrib]
      exact neg_nonpos.mpr (le_of_lt (lt_of_not_ge hsum))

private theorem reduceSupport (P : Fin 70 → Finset (Fin 14))
    (hn : ∀ p, (P p).Nonempty) (s : Finset (Fin 70)) (w : Fin 70 → ℚ)
    (hw : ∀ p ∈ s, 0 < w p) :
    ∃ (t : Finset (Fin 70)) (v : Fin 70 → ℚ), t.card ≤ 14 ∧
      (∀ p ∈ t, 0 < v p) ∧ (∑ p ∈ s, w p) ≤ (∑ p ∈ t, v p) ∧
      ∀ i, load P t v i = load P s w i := by
  classical
  induction s using Finset.strongInductionOn generalizing w with | _ s ih
  by_cases hs : s.card ≤ 14
  · exact ⟨s, w, hs, hw, le_rfl, fun _ => rfl⟩
  obtain ⟨d, hd, hdload, hdsum⟩ := direction P s (lt_of_not_ge hs)
  let decreasing := s.filter (fun p => 0 < d p)
  have hdecreasing : decreasing.Nonempty := by
    by_contra h
    obtain ⟨p, hp, hdp⟩ := hd
    obtain ⟨i, hi⟩ := hn p
    have nonpos (q : Fin 70) (hq : q ∈ s) : d q ≤ 0 := by
      apply le_of_not_gt
      intro hdq
      exact h ⟨q, mem_filter.mpr ⟨hq, hdq⟩⟩
    have negative : load P s d i < 0 := calc
      _ < ∑ q ∈ s, (0 : ℚ) := by
        apply sum_lt_sum
        · intro q hq
          by_cases hqi : i ∈ P q
          · simp [hqi, nonpos q hq]
          · simp [hqi]
        · exact ⟨p, hp, by simpa [hi] using lt_of_le_of_ne (nonpos p hp) hdp⟩
      _ = 0 := by simp
    exact (ne_of_lt negative) (hdload i)
  obtain ⟨p, hp, smallest⟩ := exists_min_image decreasing (fun q => w q / d q) hdecreasing
  obtain ⟨hps, hpd⟩ := mem_filter.mp hp
  let step := w p / d p
  have hstep : 0 < step := div_pos (hw p hps) hpd
  let v (q : Fin 70) := w q - step * d q
  have hv (q : Fin 70) (hq : q ∈ s) : 0 ≤ v q := by
    apply sub_nonneg.mpr
    by_cases hqd : 0 < d q
    · exact (le_div_iff₀ hqd).mp (smallest q (mem_filter.mpr ⟨hq, hqd⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos hstep.le (le_of_not_gt hqd)).trans (hw q hq).le
  have hvp : v p = 0 := by
    simp [v, step, div_mul_cancel₀ _ (ne_of_gt hpd)]
  let t := s.filter (fun q => 0 < v q)
  have ht : t ⊂ s := (ssubset_iff_of_subset (filter_subset _ _)).2
    ⟨p, hps, by simp [hvp]⟩
  have eraseZeros (f : Fin 70 → ℚ) (hf : ∀ q ∈ s, v q = 0 → f q = 0) :
      (∑ q ∈ t, f q) = ∑ q ∈ s, f q := by
    apply sum_subset (filter_subset _ _)
    intro q hq hqt
    have hnonpos : v q ≤ 0 := le_of_not_gt fun hpos => hqt (mem_filter.mpr ⟨hq, hpos⟩)
    exact hf q hq (le_antisymm hnonpos (hv q hq))
  have mass : (∑ q ∈ s, w q) ≤ ∑ q ∈ t, v q := by
    rw [eraseZeros v (fun _ _ h => h)]
    simp only [v, sum_sub_distrib, ← mul_sum]
    linarith [mul_nonpos_of_nonneg_of_nonpos hstep.le hdsum]
  have loads (i : Fin 14) : load P t v i = load P s w i := calc
    _ = load P s v i := eraseZeros _ (fun q _ hq => by simp [hq])
    _ = _ := by
      simp only [load_eq, v, sum_sub_distrib, ← mul_sum]
      rw [← load_eq P s d i, hdload i, mul_zero, sub_zero]
  obtain ⟨u, z, hu, hz, hmass, hloads⟩ := ih t ht v (fun q hq => (mem_filter.mp hq).2)
  exact ⟨u, z, hu, hz, mass.trans hmass, fun i => (hloads i).trans (loads i)⟩

/-- Uniform weights on 70 points can be replaced by at most 14 positive weights. -/
theorem sparse (P : Fin 70 → Finset (Fin 14)) (hn : ∀ p, (P p).Nonempty)
    (hdeg : ∀ i, (Finset.univ.filter (fun p => i ∈ P p)).card = 21) :
    ∃ (s : Finset (Fin 70)) (w : Fin 70 → ℚ), s.card ≤ 14 ∧
      (∀ p ∈ s, 0 < w p) ∧ (∑ p ∈ s, w p) = 30 ∧
      ∀ i, (∑ p ∈ s, if i ∈ P p then w p else 0) ≤ 9 := by
  classical
  let initial (_ : Fin 70) : ℚ := 3 / 7
  have initialMass : (∑ p : Fin 70, initial p) = 30 := by norm_num [initial]
  have initialLoad (i : Fin 14) : load P univ initial i = 9 := by
    rw [load_eq]
    norm_num [initial, hdeg i]
  obtain ⟨s, v, hs, hv, mass, loads⟩ := reduceSupport P hn univ initial (by
    intro p _
    norm_num [initial])
  rw [initialMass] at mass
  let total := ∑ p ∈ s, v p
  have htotal : 0 < total := lt_of_lt_of_le (by norm_num) mass
  let scale := 30 / total
  have scalePos : 0 < scale := div_pos (by norm_num) htotal
  have scaleLe : scale ≤ 1 := (div_le_one htotal).2 mass
  refine ⟨s, fun p => scale * v p, hs, fun p hp => mul_pos scalePos (hv p hp), ?_, ?_⟩
  · rw [← mul_sum]
    exact div_mul_cancel₀ 30 (ne_of_gt htotal)
  · intro i
    change load P s (fun p => scale * v p) i ≤ 9
    rw [load_eq, ← mul_sum, ← load_eq P s v i, loads i, initialLoad i]
    linarith

end C7021
