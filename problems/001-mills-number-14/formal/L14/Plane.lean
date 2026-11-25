import L14.Sparse

open Finset

namespace L14

/-- Affine points are indexed by coordinates in F₃², followed by four directions at infinity. -/
def planeLine (i : Fin 13) : Edge :=
  (![{0, 3, 6, 9},
     {1, 4, 7, 9},
     {2, 5, 8, 9},
     {0, 4, 8, 10},
     {1, 5, 6, 10},
     {2, 3, 7, 10},
     {0, 5, 7, 11},
     {1, 3, 8, 11},
     {2, 4, 6, 11},
     {0, 1, 2, 12},
     {3, 4, 5, 12},
     {6, 7, 8, 12},
     {9, 10, 11, 12}] : Fin 13 → Edge) i

def plane : Finset Edge := univ.image planeLine

set_option maxRecDepth 10000 in
private theorem plane_pairs : ∀ p q : Fin 13, (planeLine p ∩ planeLine q).Nonempty := by
  decide

private theorem plane_card : plane.card = 13 := by decide

set_option maxRecDepth 10000 in
private theorem plane_degrees : ∀ i : Fin 14, (plane.filter fun p => i ∈ p).card ≤ 4 := by
  decide

theorem plane_intersecting : Intersecting plane := by
  intro p hp q hq
  obtain ⟨a, _, rfl⟩ := mem_image.mp hp
  obtain ⟨b, _, rfl⟩ := mem_image.mp hq
  exact plane_pairs a b

/-- The projective plane of order three has mass thirteen fourths with unit load bounds. -/
theorem plane_witness :
    Intersecting plane ∧ (∀ p ∈ plane, (0 : ℝ) < 1 / 4) ∧
      (∑ _p ∈ plane, (1 / 4 : ℝ)) = 13 / 4 ∧
      ∀ i, load plane (fun _ => 1 / 4) i ≤ 1 := by
  refine ⟨plane_intersecting, fun _ _ => by norm_num, ?_, ?_⟩
  · norm_num [sum_const, nsmul_eq_mul, plane_card]
  · intro i
    rw [load, ← sum_filter]
    have hdegree : ((plane.filter fun p => i ∈ p).card : ℝ) ≤ 4 := by
      exact_mod_cast plane_degrees i
    simp only [sum_const, nsmul_eq_mul]
    linarith

/-- The same witness as a probability distribution. -/
theorem plane_probability :
    Intersecting plane ∧ (∀ p ∈ plane, (0 : ℝ) < 1 / 13) ∧
      (∑ _p ∈ plane, (1 / 13 : ℝ)) = 1 ∧
      ∀ i, load plane (fun _ => 1 / 13) i ≤ 4 / 13 := by
  refine ⟨plane_intersecting, fun _ _ => by norm_num, ?_, ?_⟩
  · norm_num [sum_const, nsmul_eq_mul, plane_card]
  · intro i
    rw [load, ← sum_filter]
    have hdegree : ((plane.filter fun p => i ∈ p).card : ℝ) ≤ 4 := by
      exact_mod_cast plane_degrees i
    simp only [sum_const, nsmul_eq_mul]
    linarith

end L14
