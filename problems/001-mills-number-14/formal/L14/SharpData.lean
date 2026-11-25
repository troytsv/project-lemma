module

public import L14.ThresholdCore

@[expose] public section

open Finset

namespace L14

/-- A sparse positive intersecting distribution above the proposed cap-21 threshold. -/
structure SharpData where
  s : Finset Edge
  w : Edge → ℝ
  W : ℝ
  hs : s.card ≤ 14
  hi : Intersecting s
  hw : ∀ p ∈ s, 0 < w p
  hm : (∑ p ∈ s, w p) = W
  hW : 69 < W
  hc : ∀ i, load s w i ≤ 21

namespace SharpData

variable (z : SharpData)

def F : Finset Edge := z.s.filter (fun p => p.card = 4)

def G : Finset Edge := z.s.filter (fun p => 4 < p.card)

noncomputable def H : ℝ := ∑ p ∈ z.G, z.w p

noncomputable def D : ℝ := 5 * (z.F.card : ℝ) - z.W + z.H

noncomputable def E : ℝ := ∑ p ∈ z.s, ((p.card : ℝ) - 4) * z.w p

noncomputable def S : ℝ := 294 - 4 * z.W - z.E

noncomputable def deficit (p : Edge) : ℝ := 5 - z.w p

noncomputable def slack (i : Fin 14) : ℝ := 21 - load z.s z.w i

def degree (i : Fin 14) : ℕ := (z.F.filter (fun p => i ∈ p)).card

theorem rankMin (p : Edge) (hp : p ∈ z.s) : 4 ≤ p.card := by
  have hn : p.Nonempty := by simpa using z.hi p hp p hp
  have hcard : (1 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast card_pos.mpr hn
  have hnonneg := mul_nonneg (sub_nonneg.mpr hcard) (z.hw p hp).le
  have hcap := edgeCapacity z.s z.w z.W 21 z.hi (fun p hp => (z.hw p hp).le) z.hm z.hc p hp
  by_contra! hsmall
  have hsmallNat : p.card ≤ 3 := by omega
  have hsmallReal : (p.card : ℝ) ≤ 3 := by exact_mod_cast hsmallNat
  linarith [z.hW]

theorem mem_F {p : Edge} : p ∈ z.F ↔ p ∈ z.s ∧ p.card = 4 := Finset.mem_filter

theorem mem_G {p : Edge} : p ∈ z.G ↔ p ∈ z.s ∧ 4 < p.card := Finset.mem_filter

theorem fourSubset : z.F ⊆ z.s := filter_subset _ _

theorem highSubset : z.G ⊆ z.s := filter_subset _ _

theorem disjointFG : Disjoint z.F z.G := by
  apply disjoint_left.mpr
  intro p hp hq
  have hfour := (z.mem_F.mp hp).2
  have hhigh := (z.mem_G.mp hq).2
  omega

theorem unionFG : z.F ∪ z.G = z.s := by
  ext p
  simp only [mem_union, z.mem_F, z.mem_G]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · intro hp
    have hrank := z.rankMin p hp
    rcases eq_or_lt_of_le hrank with h | h
    · exact Or.inl ⟨hp, h.symm⟩
    · exact Or.inr ⟨hp, h⟩

theorem card_parts : z.F.card + z.G.card = z.s.card := by
  rw [← card_union_of_disjoint z.disjointFG, z.unionFG]

theorem sum_parts (f : Edge → ℝ) :
    (∑ p ∈ z.F, f p) + (∑ p ∈ z.G, f p) = ∑ p ∈ z.s, f p := by
  rw [← sum_union z.disjointFG, z.unionFG]

theorem mass_parts : (∑ p ∈ z.F, z.w p) + z.H = z.W := (z.sum_parts z.w).trans z.hm

theorem weightFour (p : Edge) (hp : p ∈ z.F) : z.w p < 5 := by
  obtain ⟨hps, hr⟩ := z.mem_F.mp hp
  have h := edgeCapacity z.s z.w z.W 21 z.hi (fun p hp => (z.hw p hp).le) z.hm z.hc p hps
  norm_num [hr] at h
  linarith [z.hW]

theorem weightFive (p : Edge) (hp : p ∈ z.G) (hr : p.card = 5) : z.w p < 9 := by
  have h := edgeCapacity z.s z.w z.W 21 z.hi (fun p hp => (z.hw p hp).le) z.hm z.hc p
    (z.highSubset hp)
  norm_num [hr] at h
  linarith [z.hW]

theorem slackNonneg (i : Fin 14) : 0 ≤ z.slack i := sub_nonneg.mpr (z.hc i)

theorem deficitPos (p : Edge) (hp : p ∈ z.F) : 0 < z.deficit p := sub_pos.mpr (z.weightFour p hp)

theorem sum_deficit : (∑ p ∈ z.F, z.deficit p) = z.D := by
  unfold deficit D
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  linarith [z.mass_parts]

theorem sum_slack : (∑ i, z.slack i) = z.S := by
  unfold slack S E
  simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sumLoadsOn, univ_inter, sub_mul, ← mul_sum, z.hm]
  push_cast
  ring

theorem slack_sum_nonneg : 0 ≤ z.S := by
  rw [← z.sum_slack]
  exact sum_nonneg fun i _ => z.slackNonneg i

theorem high_le_excess : z.H ≤ z.E := by
  unfold H E G
  rw [sum_filter]
  apply sum_le_sum
  intro p hp
  by_cases hr : 4 < p.card
  · have hfive : 5 ≤ p.card := by omega
    have hfiveReal : (5 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast hfive
    simpa only [ite_eq_left hr, one_mul] using
      mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (p.card : ℝ) - 4 by linarith) (z.hw p hp).le
  · have hfourReal : (4 : ℝ) ≤ (p.card : ℝ) := by exact_mod_cast z.rankMin p hp
    simpa only [ite_eq_right hr] using mul_nonneg (sub_nonneg.mpr hfourReal) (z.hw p hp).le

theorem excess_lt : z.E < 18 := by
  have hs := z.slack_sum_nonneg
  unfold S at hs
  linarith [z.hW]

theorem manyFour : 11 ≤ z.F.card := by
  by_contra! h
  have hn : z.F.card ≤ 10 := by omega
  have hnR : (z.F.card : ℝ) ≤ 10 := by exact_mod_cast hn
  have hfourMass : (∑ p ∈ z.F, z.w p) ≤ (z.F.card : ℝ) * 5 := by
    calc
      _ ≤ ∑ _p ∈ z.F, (5 : ℝ) := sum_le_sum fun p hp => (z.weightFour p hp).le
      _ = _ := by simp [sum_const, nsmul_eq_mul]
  linarith [z.mass_parts, z.high_le_excess.trans_lt z.excess_lt, z.hW]

theorem loadLower (i : Fin 14) : 3 + z.E < load z.s z.w i := by
  have h := single_le_sum (f := z.slack) (fun j _ => z.slackNonneg j) (mem_univ i)
  rw [z.sum_slack] at h
  unfold slack S at h
  linarith [z.hW]

theorem fourAtVertex (i : Fin 14) : 0 < z.degree i := by
  by_contra! h
  have hz : (z.F.filter (fun p => i ∈ p)).card = 0 := by
    unfold degree at h
    omega
  have hno (p : Edge) (hp : p ∈ z.F) : i ∉ p := by
    intro hi
    have ht : p ∈ z.F.filter (fun q => i ∈ q) := mem_filter.mpr ⟨hp, hi⟩
    exact (notMem_empty p) (card_eq_zero.mp hz ▸ ht)
  have hload : load z.s z.w i ≤ z.H := by
    unfold load H
    rw [← z.sum_parts]
    have hvanish : (∑ p ∈ z.F, if i ∈ p then z.w p else 0) = 0 := by
      exact sum_eq_zero fun p hp => ite_eq_right (hno p hp)
    rw [hvanish, zero_add]
    apply sum_le_sum
    intro p hp
    split_ifs
    · exact le_rfl
    · exact (z.hw p (z.highSubset hp)).le
  linarith [z.loadLower i, z.high_le_excess]

theorem star (x : Fin 14) (hx : ∀ p ∈ z.G, x ∉ p) : 5 ≤ z.degree x := by
  have hfour (p : Edge) (hp : p ∈ z.s) (hpx : x ∈ p) : p.card = 4 := by
    have hrank := z.rankMin p hp
    by_contra! hneq
    exact hx p (z.mem_G.mpr ⟨hp, by omega⟩) hpx
  have hstar := rankFourStar z.s z.w z.W 21 z.hi (fun p hp => (z.hw p hp).le) z.hm
    (by linarith [z.hW]) z.hc z.rankMin x hfour
  have heq : z.F.filter (fun p => x ∈ p) = z.s.filter (fun p => x ∈ p) := by
    ext p
    constructor
    · intro hp
      exact mem_filter.mpr ⟨z.fourSubset (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
    · intro hp
      obtain ⟨hps, hpx⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨z.mem_F.mpr ⟨hps, hfour p hps hpx⟩, hpx⟩
  simpa only [degree, heq] using hstar

theorem overlap (p : Edge) (hp : p ∈ z.F) :
    (∑ q ∈ z.s.erase p, (((p ∩ q).card : ℝ) - 1) * z.w q) < 3 * z.deficit p := by
  obtain ⟨hps, hr⟩ := z.mem_F.mp hp
  have h := sumLoadsCap z.s z.w 21 z.hc p
  rw [edgeLoadOverlap z.s z.w z.W z.hm p hps] at h
  norm_num [hr, deficit] at h ⊢
  linarith [z.hW]

end SharpData
end L14
