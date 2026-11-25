import L14.SharpData

open Finset

namespace L14.SharpData

variable (z : SharpData)

theorem deficitAt (x : Fin 14) :
    load z.F z.deficit x + load z.F z.w x = 5 * (z.degree x : ℝ) := by
  simp only [load, ← sum_filter, deficit, sum_sub_distrib, sum_const, nsmul_eq_mul, degree]
  ring

theorem lowCap (x : Fin 14) : load z.F z.w x ≤ 21 := by
  have h := z.sum_parts (fun p => if x ∈ p then z.w p else 0)
  change load z.F z.w x + load z.G z.w x = load z.s z.w x at h
  linarith [z.hc x, loadNonneg z.G z.w (fun p hp => (z.hw p (z.highSubset hp)).le) x]

/-- Each vertex outside all high edges receives at least four units of low-edge deficit.
A four-edge can spend its deficit at most three times outside. -/
theorem outsideDeficit (o : Edge) (hg : z.G.Nonempty)
    (ho : ∀ x ∈ o, ∀ q ∈ z.G, x ∉ q) : 4 * (o.card : ℝ) ≤ 3 * z.D := by
  obtain ⟨q,hq⟩ := hg
  have lower (x : Fin 14) (hx : x ∈ o) : 4 ≤ load z.F z.deficit x := by
    have hd : (5 : ℝ) ≤ (z.degree x : ℝ) := by exact_mod_cast z.star x (ho x hx)
    linarith [z.deficitAt x, z.lowCap x]
  have upper (p : Edge) (hp : p ∈ z.F) : (o ∩ p).card ≤ 3 := by
    obtain ⟨x,hx⟩ := z.hi p (z.fourSubset hp) q (z.highSubset hq)
    obtain ⟨hxp,hxq⟩ := mem_inter.mp hx
    have hxnot : x ∉ o := fun hxo => ho x hxo q hq hxq
    have hsub : o ∩ p ⊆ p.erase x := by
      intro y hy
      obtain ⟨hyo,hyp⟩ := mem_inter.mp hy
      exact mem_erase.mpr ⟨fun heq => hxnot (heq ▸ hyo), hyp⟩
    simpa only [card_erase_of_mem hxp, (z.mem_F.mp hp).2] using card_le_card hsub
  calc
    _ = ∑ _x ∈ o, (4 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ x ∈ o, load z.F z.deficit x := sum_le_sum lower
    _ = _ := sumLoadsOn z.F z.deficit o
    _ ≤ ∑ p ∈ z.F, 3 * z.deficit p := sum_le_sum fun p hp =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast upper p hp) (z.deficitPos p hp).le
    _ = _ := by rw [← mul_sum, z.sum_deficit]

theorem excessHigh : z.E = ∑ p ∈ z.G, ((p.card : ℝ) - 4) * z.w p := by
  unfold E
  rw [← z.sum_parts]
  have h : (∑ p ∈ z.F, ((p.card : ℝ) - 4) * z.w p) = 0 := by
    apply sum_eq_zero
    intro p hp
    simp [(z.mem_F.mp hp).2]
  rw [h, zero_add]

end L14.SharpData
