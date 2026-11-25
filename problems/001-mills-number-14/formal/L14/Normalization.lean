module

public import L14.Witness

@[expose] public section

open Finset

namespace L14

/-- A cap-21 packing bound on sparse supports determines the normalized data limit. -/
theorem mills_eq_of_sparse_capacity
    (bound : ∀ (t : Finset Edge) (v : Edge → ℝ), t.card ≤ 14 → Intersecting t →
      (∀ p ∈ t, 0 < v p) → (∀ i, load t v i ≤ 21) → ∑ p ∈ t, v p ≤ 69) :
    mills = 7 / 23 := by
  apply le_antisymm mills_le_seven_twentyThree
  apply le_csInf ⟨_, witness_mem_millsValues⟩
  rintro c ⟨s, w, hi, hw, hm, rfl⟩
  by_contra! hsmall
  let a := (maxLoad s w + 7 / 23) / 2
  have hn : 0 ≤ maxLoad s w := by
    apply le_trans _ (le_sup' (load s w) (mem_univ 0))
    apply sum_nonneg
    intro p hp
    split_ifs
    · exact hw p hp
    · exact le_rfl
  have ha : 0 < a := by dsimp [a]; linarith
  have hma : maxLoad s w ≤ a := by dsimp [a]; linarith
  have has : a < 7 / 23 := by dsimp [a]; linarith
  let k := 21 / a
  have hk : 0 < k := div_pos (by norm_num) ha
  have hkm : k * a = 21 := div_mul_cancel₀ _ ha.ne'
  have hk69 : 69 < k := (lt_div_iff₀ ha).2 (by linarith)
  obtain ⟨t, v, hsub, hcard, hv, hmass, hload⟩ := sparse s w hi hw hm zero_lt_one
  have cap (i) : load t (fun p => k * v p) i ≤ 21 := calc
    _ = k * load t v i := by simp only [load, mul_sum, mul_ite, mul_zero]
    _ ≤ k * a := mul_le_mul_of_nonneg_left
      ((hload i).trans ((le_sup' (load s w) (mem_univ i)).trans hma)) hk.le
    _ = _ := hkm
  have hb := bound t (fun p => k * v p) hcard (hi.mono hsub)
    (fun p hp => mul_pos hk (hv p hp)) cap
  rw [← mul_sum, hmass, mul_one] at hb
  exact hk69.not_ge hb

end L14
