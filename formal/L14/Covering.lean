import L14.Sharp

open Finset

namespace L14

/-- A cover of all unordered pairs, presented as an indexed family of blocks. -/
def CoversPairs {α : Type*} {ι : Type*} (B : ι → Finset α) : Prop :=
  ∀ x y, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i

private theorem commonBlock {v b : ℕ} {B : Fin b → Finset (Fin v)}
    (hv : 2 ≤ v) (hcover : CoversPairs B) (x y : Fin v) : ∃ i, x ∈ B i ∧ y ∈ B i := by
  by_cases hxy : x = y
  · subst y
    let z : Fin v := ⟨if x.val = 0 then 1 else 0, by split <;> omega⟩
    have hxz : x ≠ z := by
      intro heq
      have hval := congrArg Fin.val heq
      change x.val = (if x.val = 0 then 1 else 0) at hval
      split at hval <;> omega
    obtain ⟨i, hi, _⟩ := hcover x z hxz
    exact ⟨i, hi, hi⟩
  · exact hcover x y hxy

/-- Fourteen blocks of size at most `k` can cover at most `23k/7` points. -/
theorem covering_ratio_bound {v k b : ℕ} (hv : 2 ≤ v) (hb : b ≤ 14)
    (B : Fin b → Finset (Fin v)) (hsize : ∀ i, (B i).card ≤ k)
    (hcover : CoversPairs B) : 7 * v ≤ 23 * k := by
  let P (x : Fin v) : Edge :=
    univ.filter fun i => ∃ j : Fin b, j.val = i.val ∧ x ∈ B j
  have hP (x : Fin v) (j : Fin b) : Fin.castLE hb j ∈ P x ↔ x ∈ B j := by
    simp only [P, mem_filter, mem_univ, true_and]
    change (∃ l : Fin b, l.val = j.val ∧ x ∈ B l) ↔ x ∈ B j
    constructor
    · rintro ⟨l, hl, hx⟩
      rwa [Fin.ext hl] at hx
    · exact fun hx => ⟨j, rfl, hx⟩
  have hmeet (x y : Fin v) : (P x ∩ P y).Nonempty := by
    obtain ⟨j, hx, hy⟩ := commonBlock hv hcover x y
    exact ⟨Fin.castLE hb j, mem_inter.mpr ⟨(hP x j).mpr hx, (hP y j).mpr hy⟩⟩
  have hk : 0 < k := by
    let a : Fin v := ⟨0, by omega⟩
    obtain ⟨j, ha, _⟩ := commonBlock hv hcover a a
    exact (card_pos.mpr ⟨a, ha⟩).trans_le (hsize j)
  classical
  let s := univ.image P
  let n (p : Edge) := (univ.filter (fun x => P x = p)).card
  have hfiber (t : Finset Edge) :
      (∑ p ∈ t, n p) = (univ.filter (fun x => P x ∈ t)).card :=
    sum_card_fiberwise_eq_card_filter univ t P
  have hmass : (∑ p ∈ s, n p) = v := by
    rw [hfiber]
    simp [s]
  have hi : Intersecting s := by
    intro p hp q hq
    obtain ⟨x, _, rfl⟩ := mem_image.mp hp
    obtain ⟨y, _, rfl⟩ := mem_image.mp hq
    exact hmeet x y
  let w (p : Edge) : ℝ := (n p : ℝ) / k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hload (i : Fin 14) : load s w i ≤ 1 := by
    have hcount : (univ.filter (fun x => i ∈ P x)).card ≤ k := by
      by_cases hib : i.val < b
      · let j : Fin b := ⟨i.val, hib⟩
        have hij : Fin.castLE hb j = i := Fin.ext rfl
        have hfilter : univ.filter (fun x => i ∈ P x) = B j := by
          ext x
          rw [mem_filter, ← hij, hP]
          simp
        exact hfilter ▸ hsize j
      · have hfilter : univ.filter (fun x => i ∈ P x) = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro x hx
          obtain ⟨j, hj, _⟩ := (mem_filter.mp (mem_filter.mp hx).2).2
          exact hib (hj ▸ j.isLt)
        simp [hfilter]
    have hcount' : (∑ p ∈ s.filter (fun p => i ∈ p), n p) ≤ k := by
      rw [hfiber]
      simpa only [mem_filter, s, mem_image, mem_univ, true_and, exists_apply_eq_apply,
        true_and] using hcount
    rw [load, ← sum_filter]
    simp only [w, ← sum_div, ← Nat.cast_sum]
    exact (div_le_one hkR).mpr (by exact_mod_cast hcount')
  have hobj : (∑ p ∈ s, w p) = (v : ℝ) / k := by
    simp only [w, ← sum_div, ← Nat.cast_sum, hmass]
  have hbound := fractional_matching_maximum.2
    ⟨s, w, hi, fun p _ => div_nonneg (Nat.cast_nonneg (n p)) hkR.le, hload, hobj⟩
  have hcross := (div_le_iff₀ hkR).mp hbound
  have hnat : (7 : ℝ) * v ≤ 23 * k := by linarith
  exact_mod_cast hnat

theorem covering_card_lower_bound {v k b : ℕ} (hv : 2 ≤ v) (hstrict : 23 * k < 7 * v)
    (B : Fin b → Finset (Fin v)) (hsize : ∀ i, (B i).card ≤ k)
    (hcover : CoversPairs B) : 15 ≤ b := by
  by_contra! h
  exact hstrict.not_ge (covering_ratio_bound hv (by omega) B hsize hcover)

/-- Replace each point by `n` copies while preserving the number of block indices. -/
theorem replicate_cover {v k b : ℕ} (hv : 2 ≤ v) (B : Fin b → Finset (Fin v))
    (hsize : ∀ i, (B i).card = k) (hcover : CoversPairs B) (n : ℕ) :
    ∃ D : Fin b → Finset (Fin (v * n)), (∀ i, (D i).card = k * n) ∧ CoversPairs D := by
  let e : Fin v × Fin n ≃ Fin (v * n) := finProdFinEquiv
  refine ⟨fun i => ((B i) ×ˢ (univ : Finset (Fin n))).map e.toEmbedding, ?_, ?_⟩
  · intro i
    simp [hsize]
  · intro x y _
    let a := e.symm x
    let c := e.symm y
    obtain ⟨i, hx, hy⟩ := commonBlock hv hcover a.1 c.1
    exact ⟨i, mem_map.mpr ⟨a, mem_product.mpr ⟨hx, mem_univ _⟩, e.apply_symm_apply x⟩,
      mem_map.mpr ⟨c, mem_product.mpr ⟨hy, mem_univ _⟩, e.apply_symm_apply y⟩⟩

/-- The feasible numbers of indexed blocks of exactly size `k`. -/
def coveringBlockCounts (v k : ℕ) : Set ℕ :=
  {b | ∃ B : Fin b → Finset (Fin v), (∀ i, (B i).card = k) ∧ CoversPairs B}

/-- The thirteen-block obstruction from counting incidences at each point. -/
theorem incidence_card_lower_bound {v k b : ℕ} (hv : 2 ≤ v)
    (hthree : 3 * k < v) (hthirteen : 13 * k < 4 * v)
    (B : Fin b → Finset (Fin v)) (hsize : ∀ i, (B i).card ≤ k) (hcover : CoversPairs B) :
    14 ≤ b := by
  let S (x : Fin v) := univ.filter (fun i => x ∈ B i)
  have hdegree (x : Fin v) : 4 ≤ (S x).card := by
    have hunion : (S x).biUnion B = univ := by
      apply eq_univ_iff_forall.mpr
      intro y
      obtain ⟨i, hx, hy⟩ := commonBlock hv hcover x y
      exact mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ i, hx⟩, hy⟩
    have hcount : v ≤ (S x).card * k := calc
      _ = ((S x).biUnion B).card := by simp [hunion]
      _ ≤ ∑ i ∈ S x, (B i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ S x, k := sum_le_sum fun i _ => hsize i
      _ = _ := by simp
    by_contra! h
    exact hthree.not_ge (hcount.trans (Nat.mul_le_mul_right k (by omega)))
  have htotal : 4 * v ≤ b * k := calc
    _ = ∑ _x : Fin v, (4 : ℕ) := by simp [Nat.mul_comm]
    _ ≤ ∑ x : Fin v, (S x).card := sum_le_sum fun x _ => hdegree x
    _ = ∑ i : Fin b, (B i).card := by
      simp only [S, card_eq_sum_ones, sum_filter]
      rw [sum_comm]
      simp [sum_ite_mem]
    _ ≤ ∑ _i : Fin b, k := sum_le_sum fun i _ => hsize i
    _ = _ := by simp
  by_contra! h
  exact hthirteen.not_ge (htotal.trans (Nat.mul_le_mul_right k (by omega)))

theorem covering70_scaled (base : 15 ∈ coveringBlockCounts 70 21) {n : ℕ} (hn : 0 < n) :
    IsLeast (coveringBlockCounts (70 * n) (21 * n)) 15 := by
  constructor
  · obtain ⟨B, hsize, hcover⟩ := base
    exact replicate_cover (by decide) B hsize hcover n
  · rintro b ⟨B, hsize, hcover⟩
    exact covering_card_lower_bound (by omega) (by omega) B
      (fun i => (hsize i).le) hcover

theorem covering69_scaled (base : 14 ∈ coveringBlockCounts 69 21) {n : ℕ} (hn : 0 < n) :
    IsLeast (coveringBlockCounts (69 * n) (21 * n)) 14 := by
  constructor
  · obtain ⟨B, hsize, hcover⟩ := base
    exact replicate_cover (by decide) B hsize hcover n
  · rintro b ⟨B, hsize, hcover⟩
    exact incidence_card_lower_bound (by omega) (by omega) (by omega) B
      (fun i => (hsize i).le) hcover

end L14
