module

public import L14.Normalization
public import L14.Eleven
public import L14.HighRanks
public import L14.TwoQuints

@[expose] public section

open Finset

namespace L14

theorem sparse_capacity (s : Finset Edge) (w : Edge → ℝ) (hs : s.card ≤ 14)
    (hi : Intersecting s) (hw : ∀ p ∈ s, 0 < w p) (hc : ∀ i, load s w i ≤ 21) :
    ∑ p ∈ s, w p ≤ 69 := by
  by_contra! hW
  let z : SharpData := ⟨s, w, _, hs, hi, hw, rfl, hW, hc⟩
  by_cases h : z.D < 4
  · exact z.false_of_deficit_lt_four h
  · obtain ⟨hf, q, r, hne, hg, hq, hr⟩ := z.twoQuints_of_large_deficit (le_of_not_gt h)
    exact twoQuints z hf hne hg hq hr

/-- The first Mills number and the all-to-all comparison data limit on fourteen vertices. -/
theorem mills_eq_seven_twentyThree : mills = 7 / 23 :=
  mills_eq_of_sparse_capacity sparse_capacity

/-- The same optimum in Füredi's unit-capacity fractional-matching convention.
The objective ranges over all finite supports, including zero weights. -/
theorem fractional_matching_maximum : IsGreatest
    {m : ℝ | ∃ (s : Finset Edge) (w : Edge → ℝ), Intersecting s ∧
      (∀ p ∈ s, 0 ≤ w p) ∧ (∀ i, load s w i ≤ 1) ∧ (∑ p ∈ s, w p) = m}
    (23 / 7) := by
  constructor
  · refine ⟨witness, fun p => (23 / 7) * witnessProbability p, witness_intersecting, ?_, ?_, ?_⟩
    · intro p _
      unfold witnessProbability
      positivity
    · intro i
      calc
        _ = (23 / 7) * load witness witnessProbability i := by
          simp only [load, mul_sum, mul_ite, mul_zero]
        _ ≤ 1 := by rw [witness_probability_load]; norm_num
    · rw [← mul_sum, witness_probability_mass, mul_one]
  · rintro m ⟨s, w, hi, hw, hc, hm⟩
    by_contra! bad
    obtain ⟨t,v,hsub,hcard,hv,hvsum,hvc⟩ := sparse s w hi hw hm (by linarith)
    have hcap (i) : load t (fun p => 21 * v p) i ≤ 21 := calc
      _ = 21 * load t v i := by simp only [load, mul_sum, mul_ite, mul_zero]
      _ ≤ _ := by linarith [(hvc i).trans (hc i)]
    have h := sparse_capacity t (fun p => 21 * v p) hcard (hi.mono hsub)
      (fun p hp => mul_pos (by norm_num) (hv p hp)) hcap
    rw [← mul_sum, hvsum] at h
    linarith

end L14
