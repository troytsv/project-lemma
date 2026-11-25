import L14.Sparse

open Finset

namespace L14

def maxLoad (s : Finset Edge) (w : Edge → ℝ) : ℝ :=
  univ.sup' univ_nonempty (load s w)

def millsValues : Set ℝ :=
  {c | ∃ (s : Finset Edge) (w : Edge → ℝ), Intersecting s ∧
    (∀ p ∈ s, 0 ≤ w p) ∧ (∑ p ∈ s, w p) = 1 ∧ c = maxLoad s w}

/-- The infimum of the maximum vertex load among intersecting probability distributions. -/
noncomputable def mills : ℝ := sInf millsValues

theorem millsValues_bddBelow : BddBelow millsValues := by
  refine ⟨0, ?_⟩
  rintro c ⟨s, w, _, hw, _, rfl⟩
  have hnonneg : (0 : ℝ) ≤ load s w 0 := by
    apply sum_nonneg
    intro p hp
    split_ifs
    · exact hw p hp
    · exact le_rfl
  exact hnonneg.trans (le_sup' (load s w) (mem_univ 0))

/-- An edge and its integer weight, with vertices numbered from zero. -/
def witnessData (i : Fin 14) : Edge × ℕ :=
  (![({9, 10, 11, 12}, 5),
     ({0, 5, 7, 11}, 3),
     ({3, 4, 5, 12}, 5),
     ({6, 7, 8, 12}, 5),
     ({2, 5, 8, 9}, 5),
     ({2, 4, 6, 11}, 5),
     ({1, 5, 6, 10}, 5),
     ({2, 3, 7, 10}, 5),
     ({0, 4, 8, 10, 13}, 6),
     ({1, 4, 7, 9}, 5),
     ({1, 3, 8, 11}, 5),
     ({0, 3, 6, 9, 13}, 6),
     ({0, 1, 2, 12, 13}, 6),
     ({5, 7, 11, 13}, 3)] : Fin 14 → Edge × ℕ) i

def witness : Finset Edge := univ.image (fun i => (witnessData i).1)

def witnessWeight (p : Edge) : ℕ := ∑ i : Fin 14,
  if (witnessData i).1 = p then (witnessData i).2 else 0

noncomputable def witnessProbability (p : Edge) : ℝ := (witnessWeight p : ℝ) / 69

set_option maxRecDepth 10000 in
private theorem witnessPairs : ∀ a b : Fin 14,
    ((witnessData a).1 ∩ (witnessData b).1).Nonempty := by
  decide

theorem witness_intersecting : Intersecting witness := by
  intro p hp q hq
  obtain ⟨a, _, rfl⟩ := mem_image.mp hp
  obtain ⟨b, _, rfl⟩ := mem_image.mp hq
  exact witnessPairs a b

theorem witness_card : witness.card = 14 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem witness_mass : (∑ p ∈ witness, witnessWeight p) = 69 := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem witness_loads : ∀ i : Fin 14,
    (∑ p ∈ witness, if i ∈ p then witnessWeight p else 0) = 21 := by
  decide

theorem witness_probability_mass : (∑ p ∈ witness, witnessProbability p) = 1 := by
  simp only [witnessProbability, ← sum_div, ← Nat.cast_sum, witness_mass]
  norm_num

theorem witness_probability_load (i : Fin 14) : load witness witnessProbability i = 7 / 23 := by
  calc
    _ = ((∑ p ∈ witness, if i ∈ p then witnessWeight p else 0 : ℕ) : ℝ) / 69 := by
      rw [Nat.cast_sum, sum_div, load]
      apply sum_congr rfl
      intro p hp
      by_cases hi : i ∈ p <;> simp [witnessProbability, hi]
    _ = _ := by rw [witness_loads i]; norm_num

theorem witness_mem_millsValues : (7 / 23 : ℝ) ∈ millsValues := by
  refine ⟨witness, witnessProbability, witness_intersecting, ?_, witness_probability_mass, ?_⟩
  · intro p _
    unfold witnessProbability
    positivity
  · simp only [maxLoad, witness_probability_load, sup'_const]

theorem mills_le_seven_twentyThree : mills ≤ 7 / 23 :=
  csInf_le millsValues_bddBelow witness_mem_millsValues

end L14
