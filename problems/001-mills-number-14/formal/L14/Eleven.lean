import L14.SharpData

open Finset

namespace L14.SharpData

private theorem degreeAsLoad (z : SharpData) (i : Fin 14) :
    load z.F (fun _ => 1) i = (z.degree i : ℝ) := by
  simp [load, SharpData.degree]

private theorem fourDegreeLe (z : SharpData) (hD : z.D < 4) (i : Fin 14) :
    z.degree i ≤ 4 := by
  let pencil := z.F.filter (fun p => i ∈ p)
  have hsub : pencil ⊆ z.F := filter_subset _ _
  have hcap : (∑ p ∈ pencil, z.w p) ≤ 21 := by
    apply le_trans _ (z.hc i)
    rw [load, ← sum_filter]
    apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpF, hi⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨z.fourSubset hpF, hi⟩
    · intro p hp _
      exact (z.hw p (mem_filter.mp hp).1).le
  have hdef : (∑ p ∈ pencil, z.deficit p) ≤ z.D := by
    rw [← z.sum_deficit]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => (z.deficitPos p hp).le)
  have hmass : (∑ p ∈ pencil, z.w p) =
      5 * (z.degree i : ℝ) - ∑ p ∈ pencil, z.deficit p := by
    simp [SharpData.deficit, SharpData.degree, pencil, sum_sub_distrib, nsmul_eq_mul]
    ring
  by_contra! h
  have hfive : (5 : ℝ) ≤ (z.degree i : ℝ) := by exact_mod_cast (show 5 ≤ z.degree i by omega)
  linarith

private theorem sumDegreesOnFour (z : SharpData) (p : Edge) (hp : p ∈ z.F) :
    (z.F.card : ℝ) + 3 ≤ ∑ i ∈ p, (z.degree i : ℝ) := by
  have hmass : (∑ q ∈ z.F, (1 : ℝ)) = (z.F.card : ℝ) := by simp
  have h := edgeLoadLower z.F (fun _ => 1) (z.F.card : ℝ) (z.hi.mono z.fourSubset)
    (fun _ _ => zero_le_one) hmass p hp
  have hcard := (z.mem_F.mp hp).2
  norm_num [hcard, degreeAsLoad] at h
  exact h

/-- A support with at least eleven rank-four edges must have total four-deficit at least four. -/
theorem false_of_deficit_lt_four (z : SharpData) (hD : z.D < 4) : False := by
  have hflo : 11 ≤ z.F.card := z.manyFour
  have hfhi : z.F.card ≤ 14 := (card_le_card z.fourSubset).trans z.hs
  let d (i : Fin 14) : ℝ := z.degree i
  let δ (i : Fin 14) : ℝ := 4 - d i
  have hmax (i : Fin 14) : d i ≤ 4 := by
    change (z.degree i : ℝ) ≤ 4
    exact_mod_cast fourDegreeLe z hD i
  have hδ (i : Fin 14) : 0 ≤ δ i := sub_nonneg.mpr (hmax i)
  have hmin (i : Fin 14) : (z.F.card : ℝ) - 9 ≤ d i := by
    obtain ⟨p, hp⟩ := card_pos.mp (z.fourAtVertex i)
    obtain ⟨hpF, hip⟩ := mem_filter.mp hp
    have hcard : (p.erase i).card = 3 := by rw [card_erase_of_mem hip, (z.mem_F.mp hpF).2]
    have herase : (∑ j ∈ p.erase i, d j) ≤ 12 := calc
      _ ≤ ∑ _j ∈ p.erase i, (4 : ℝ) := sum_le_sum fun j _ => hmax j
      _ = _ := by norm_num [sum_const, nsmul_eq_mul, hcard]
    have hsum := sumDegreesOnFour z p hpF
    change (z.F.card : ℝ) + 3 ≤ ∑ j ∈ p, d j at hsum
    rw [← sum_erase_add p d hip] at hsum
    linarith
  have hdouble (g : Fin 14 → ℝ) :
      (∑ i, g i * d i) = ∑ p ∈ z.F, ∑ i ∈ p, g i := by
    simpa only [d, degreeAsLoad, one_mul] using weightedSumLoads z.F (fun _ => 1) g
  have hdsum : (∑ i, d i) = 4 * (z.F.card : ℝ) := by
    have h := hdouble (fun _ => 1)
    rw [show (∑ p ∈ z.F, ∑ _i ∈ p, (1 : ℝ)) = ∑ _p ∈ z.F, (4 : ℝ) by
      apply sum_congr rfl
      intro p hp
      norm_num [sum_const, nsmul_eq_mul, (z.mem_F.mp hp).2]] at h
    simpa [sum_const, nsmul_eq_mul, mul_comm] using h
  have hδsum : (∑ i, δ i) = 56 - 4 * (z.F.card : ℝ) := by
    norm_num [δ, sum_sub_distrib, hdsum, sum_const, nsmul_eq_mul]
  have hbelow : ((z.F.card : ℝ) - 9) * (56 - 4 * (z.F.card : ℝ)) ≤
      ∑ i, δ i * d i := by
    rw [← hδsum, mul_sum]
    exact sum_le_sum fun i _ => by
      rw [mul_comm ((z.F.card : ℝ) - 9)]
      exact mul_le_mul_of_nonneg_left (hmin i) (hδ i)
  have habove : (∑ i, δ i * d i) ≤ (z.F.card : ℝ) * (13 - (z.F.card : ℝ)) := by
    rw [hdouble δ]
    calc
      _ ≤ ∑ _p ∈ z.F, (13 - (z.F.card : ℝ)) := by
        apply sum_le_sum
        intro p hp
        have hline := sumDegreesOnFour z p hp
        norm_num [δ, d, sum_sub_distrib, sum_const, nsmul_eq_mul, (z.mem_F.mp hp).2]
        linarith
      _ = _ := by simp only [sum_const, nsmul_eq_mul]
  have himpossible := hbelow.trans habove
  interval_cases z.F.card <;> norm_num at himpossible

theorem eleven_impossible (z : SharpData) (hcard : z.F.card = 11) : False := by
  apply z.false_of_deficit_lt_four
  have hH := z.high_le_excess.trans_lt z.excess_lt
  norm_num [SharpData.D, hcard]
  linarith [z.hW]

end L14.SharpData
