module

public import L14.Outside

@[expose] public section

open Finset

namespace L14.SharpData

variable (z : SharpData)

private theorem oneHigh (q : Edge) (hg : z.G = {q}) (hD : 4 ≤ z.D) : False := by
  have hq : q ∈ z.G := by simp [hg]
  have hmass : z.H = z.w q := by simp [H, hg]
  have hE : z.E = ((q.card : ℝ) - 4) * z.w q := by simp [z.excessHigh, hg]
  have hc : z.F.card ≤ 13 := by
    have h := z.card_parts
    simp [hg] at h
    have hs := z.hs
    omega
  have hc' : (z.F.card : ℝ) ≤ 13 := by exact_mod_cast hc
  have hD' : z.D = 5 * z.F.card - z.W + z.H := rfl
  have hw : 8 < z.w q := by linarith [z.hW]
  have hpos := (z.hw q (z.highSubset hq)).le
  have hsize : q.card ≤ 6 := by
    by_contra! bad
    have seven : (7 : ℝ) ≤ q.card := by exact_mod_cast (show 7 ≤ q.card by omega)
    nlinarith [z.excess_lt, mul_nonneg (sub_nonneg.mpr seven) hpos]
  have hweight : z.w q < 9 := by
    have five := (z.mem_G.mp hq).2
    rcases (show q.card = 5 ∨ q.card = 6 by omega) with h | h
    · exact z.weightFive q hq h
    · norm_num [h] at hE
      linarith [z.excess_lt]
  let o : Edge := univ \ q
  have ho : o.card + q.card = 14 := by
    simpa [o] using card_sdiff_add_card_eq_card (subset_univ q)
  have hout := z.outsideDeficit o ⟨q,hq⟩ (by
    intro x hx p hp
    simp only [hg, mem_singleton] at hp
    subst p
    exact (mem_sdiff.mp hx).2)
  have height : (8 : ℝ) ≤ o.card := by exact_mod_cast (show 8 ≤ o.card by omega)
  linarith [z.hW]

private theorem highPair (q r : Edge) (hne : q ≠ r) (hg : z.G = {q,r})
    (hF : z.F.card = 12) (hD : 4 ≤ z.D) : q.card = 5 ∧ r.card = 5 := by
  have hq : q ∈ z.G := by simp [hg]
  have hr : r ∈ z.G := by simp [hg]
  have pq := (z.hw q (z.highSubset hq)).le
  have pr := (z.hw r (z.highSubset hr)).le
  have hmass : z.H = z.w q + z.w r := by simp [H, hg, hne]
  have hE : z.E = ((q.card : ℝ) - 4) * z.w q + ((r.card : ℝ) - 4) * z.w r := by
    simp [z.excessHigh, hg, hne]
  have hD' : z.D = 60 - z.W + z.H := by norm_num [D, hF]
  have hH : 13 < z.H := by linarith [z.hW]
  have minq := (z.mem_G.mp hq).2
  have minr := (z.mem_G.mp hr).2
  have six (a b : Edge) (ha : a ∈ z.G) (h5 : a.card = 5) (hb : 6 ≤ b.card)
      (hbpos : 0 ≤ z.w b) (hm : z.H = z.w a + z.w b)
      (he : z.E = z.w a + ((b.card : ℝ) - 4) * z.w b)
      (hpair : z.G = {a,b}) : False := by
    have hwa := z.weightFive a ha h5
    have hwb : 4 < z.w b := by linarith
    have hb6 : b.card = 6 := by
      by_contra bad
      have hb7 : (7 : ℝ) ≤ b.card := by exact_mod_cast (show 7 ≤ b.card by omega)
      nlinarith [mul_nonneg (sub_nonneg.mpr hb7) hbpos, z.excess_lt]
    norm_num [hb6] at he
    let o : Edge := univ \ (a ∪ b)
    have hbG : b ∈ z.G := by simp [hpair]
    have hinter := Finset.card_pos.mpr (z.hi a (z.highSubset ha) b (z.highSubset hbG))
    have hu := card_union_add_card_inter a b
    have ho : o.card + (a ∪ b).card = 14 := by
      simpa [o] using card_sdiff_add_card_eq_card (subset_univ (a ∪ b))
    have ho4 : (4 : ℝ) ≤ o.card := by exact_mod_cast (show 4 ≤ o.card by omega)
    have hout := z.outsideDeficit o ⟨a,ha⟩ (by
      intro x hx p hp
      have hno := (mem_sdiff.mp hx).2
      simp only [hpair, mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact fun h => hno (mem_union_left _ h)
      · exact fun h => hno (mem_union_right _ h))
    linarith [z.excess_lt, z.hW]
  by_cases hq5 : q.card = 5
  · refine ⟨hq5, ?_⟩
    by_contra bad
    apply six q r hq hq5 (by omega) pr hmass _ hg
    norm_num [hq5] at hE
    exact hE
  by_cases hr5 : r.card = 5
  · exfalso
    apply six r q hr hr5 (by omega) pq (by linarith) _ (hg.trans (pair_comm q r))
    norm_num [hr5] at hE
    linarith only [hE]
  have sq : (6 : ℝ) ≤ q.card := by exact_mod_cast (show 6 ≤ q.card by omega)
  have sr : (6 : ℝ) ≤ r.card := by exact_mod_cast (show 6 ≤ r.card by omega)
  exfalso
  nlinarith [mul_nonneg (sub_nonneg.mpr sq) pq, mul_nonneg (sub_nonneg.mpr sr) pr, z.excess_lt]

theorem twoQuints_of_large_deficit (hD : 4 ≤ z.D) :
    z.F.card = 12 ∧ ∃ q r : Edge, q ≠ r ∧ z.G = {q,r} ∧ q.card = 5 ∧ r.card = 5 := by
  have hD' : z.D = 5 * z.F.card - z.W + z.H := rfl
  have hF : 12 ≤ z.F.card := by
    by_contra! bad
    have h : (z.F.card : ℝ) ≤ 11 := by exact_mod_cast (show z.F.card ≤ 11 by omega)
    linarith [z.high_le_excess, z.excess_lt, z.hW]
  have cards := z.card_parts
  have hs := z.hs
  have two : z.G.card = 2 := by
    by_contra bad
    by_cases zero : z.G.card = 0
    · have empty := card_eq_zero.mp zero
      have noMass : z.H = 0 := by simp [H, empty]
      have hf14 : (z.F.card : ℝ) ≤ 14 := by exact_mod_cast (show z.F.card ≤ 14 by omega)
      linarith [z.hW]
    · obtain ⟨q,hq⟩ := card_eq_one.mp (show z.G.card = 1 by omega)
      exact z.oneHigh q hq hD
  obtain ⟨q,r,hne,hg⟩ := card_eq_two.mp two
  have hf12 : z.F.card = 12 := by omega
  exact ⟨hf12, q, r, hne, hg, z.highPair q r hne hg hf12 hD⟩

end L14.SharpData
