import L14.Outside

open Finset

namespace L14

private theorem sumIncidences (f : Finset Edge) (u : Edge) :
    (∑ x ∈ u, (f.filter (fun p => x ∈ p)).card) =
      ∑ p ∈ f, (p ∩ u).card := by
  have h := sumLoadsOn f (fun _ => (1 : ℝ)) u
  simp only [load, ← sum_filter, sum_const, nsmul_eq_mul, mul_one, inter_comm u] at h
  exact_mod_cast h

private theorem localPigeonhole (f : Finset Edge) (y u : Edge)
    (hy : y.card = 4) (hu : u.card = 5) (hdisj : Disjoint y u)
    (hyHit : ∀ p ∈ f, (p ∩ y).card = 1)
    (huHit : ∀ p ∈ f, (p ∩ u).card = 2)
    (hlin : ∀ p ∈ f, ∀ q ∈ f, p ≠ q → (p ∩ q).card ≤ 1) :
    f.card ≤ 8 := by
  have hsmall (x : Fin 14) (hx : x ∈ y) : (f.filter (fun p => x ∈ p)).card ≤ 2 := by
    let fx := f.filter (fun p => x ∈ p)
    have hunique (z : Fin 14) (hz : z ∈ u) : (fx.filter (fun p => z ∈ p)).card ≤ 1 := by
      rw [card_le_one]
      intro p hp q hq
      by_contra hne
      obtain ⟨⟨hp, hxp⟩, hzp⟩ := (mem_filter.mp hp).imp (fun h => mem_filter.mp h) id
      obtain ⟨⟨hq, hxq⟩, hzq⟩ := (mem_filter.mp hq).imp (fun h => mem_filter.mp h) id
      have hxz : x ≠ z := by
        intro heq
        exact disjoint_left.mp hdisj hx (heq ▸ hz)
      have htwo : ({x, z} : Edge) ⊆ p ∩ q := by
        intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact mem_inter.mpr ⟨hxp, hxq⟩
        · obtain rfl := mem_singleton.mp ha
          exact mem_inter.mpr ⟨hzp, hzq⟩
      have hcard := card_le_card htwo
      simp [hxz] at hcard
      have hlimit := hlin p hp q hq hne
      exact (by omega : False)
    have h := sumIncidences fx u
    have hright : (∑ p ∈ fx, (p ∩ u).card) = fx.card * 2 := by
      calc
        _ = ∑ _p ∈ fx, 2 := sum_congr rfl (fun p hp => huHit p (mem_filter.mp hp).1)
        _ = _ := by simp [Nat.mul_comm]
    have hupper : (∑ x ∈ u, (fx.filter (fun p => x ∈ p)).card) ≤ 5 := by
      calc
        _ ≤ ∑ _x ∈ u, 1 := sum_le_sum hunique
        _ = _ := by simp [hu]
    rw [hright] at h
    change fx.card ≤ 2
    omega
  have h := sumIncidences f y
  have hright : (∑ p ∈ f, (p ∩ y).card) = f.card := by
    calc
      _ = ∑ _p ∈ f, 1 := sum_congr rfl hyHit
      _ = _ := by simp
  rw [hright] at h
  have hupper : (∑ x ∈ y, (f.filter (fun p => x ∈ p)).card) ≤ 8 := by
    calc
      _ ≤ ∑ _x ∈ y, 2 := sum_le_sum hsmall
      _ = _ := by simp [hy]
  omega

private theorem outsideCounts (p a b : Edge) (hp : p.card = 4)
    (ha : (p ∩ a).Nonempty) (hb : (p ∩ b).Nonempty) :
    let u := univ \ (a ∪ b)
    (p ∩ u).card ≤ 3 ∧
      (Disjoint p (a ∩ b) → (p ∩ u).card ≤ 2) ∧
      ((p ∩ a).card = 1 → (p ∩ b).card = 1 → Disjoint p (a ∩ b) →
        (p ∩ u).card = 2) := by
  let u : Edge := univ \ (a ∪ b)
  have heq : p ∩ u = p \ (a ∪ b) := by
    ext x
    simp [u]
  have hsum : (p ∩ u).card + (p ∩ (a ∪ b)).card = 4 := by
    rw [heq, card_sdiff_add_card_inter, hp]
  have hpos : 0 < (p ∩ (a ∪ b)).card :=
    card_pos.mpr (ha.mono fun _ hx => mem_inter.mpr
      ⟨(mem_inter.mp hx).1, mem_union_left _ (mem_inter.mp hx).2⟩)
  have hab (hd : Disjoint p (a ∩ b)) :
      (p ∩ (a ∪ b)).card = (p ∩ a).card + (p ∩ b).card := by
    rw [inter_union_distrib_left, card_union_of_disjoint]
    rw [disjoint_left] at hd ⊢
    intro x hx hy
    obtain ⟨hxp, hxa⟩ := mem_inter.mp hx
    exact hd hxp (mem_inter.mpr ⟨hxa, (mem_inter.mp hy).2⟩)
  change (p ∩ u).card ≤ 3 ∧
    (Disjoint p (a ∩ b) → (p ∩ u).card ≤ 2) ∧
    ((p ∩ a).card = 1 → (p ∩ b).card = 1 → Disjoint p (a ∩ b) → (p ∩ u).card = 2)
  refine ⟨by omega, ?_, ?_⟩
  · intro hd
    have hpa := card_pos.mpr ha
    have hpb := card_pos.mpr hb
    have h := hab hd
    omega
  · intro hpa hpb hd
    have h := hab hd
    omega

private theorem repeatedWeight (z : SharpData) (p q : Edge) (hp : p ∈ z.F)
    (hq : q ∈ z.s) (hne : q ≠ p) (hr : 2 ≤ (p ∩ q).card) :
    z.w q < 3 * z.deficit p := by
  have hq' := mem_erase.mpr ⟨hne, hq⟩
  have hterm : z.w q ≤ (((p ∩ q).card : ℝ) - 1) * z.w q := by
    have hr' : (2 : ℝ) ≤ ((p ∩ q).card : ℝ) := by exact_mod_cast hr
    nlinarith [mul_nonneg (show 0 ≤ ((p ∩ q).card : ℝ) - 2 by linarith) (z.hw q hq).le]
  have hsum :
      (((p ∩ q).card : ℝ) - 1) * z.w q ≤
        ∑ r ∈ z.s.erase p, (((p ∩ r).card : ℝ) - 1) * z.w r := by
    apply single_le_sum _ hq'
    intro r hr
    have hrs := (mem_erase.mp hr).2
    have hc : (1 : ℝ) ≤ ((p ∩ r).card : ℝ) := by
      exact_mod_cast card_pos.mpr (z.hi p (z.fourSubset hp) r hrs)
    exact mul_nonneg (sub_nonneg.mpr hc) (z.hw r hrs).le
  exact hterm.trans_lt (hsum.trans_lt (z.overlap p hp))

set_option maxHeartbeats 1500000 in
theorem twoQuints (z : SharpData) (hf : z.F.card = 12) {a b : Edge} (hne : a ≠ b)
    (hg : z.G = {a, b}) (ha : a.card = 5) (hb : b.card = 5) : False := by
  let j := a ∩ b
  let u : Edge := univ \ (a ∪ b)
  have hag : a ∈ z.G := by simp [hg]
  have hbg : b ∈ z.G := by simp [hg]
  have has := z.highSubset hag
  have hbs := z.highSubset hbg
  have hfg : z.s = insert a (insert b z.F) := by
    rw [← z.unionFG, hg]
    ext p
    simp
  have hload (x : Fin 14) :
      load z.s z.w x = load z.F z.w x + (if x ∈ a then z.w a else 0) +
        (if x ∈ b then z.w b else 0) := by
    have haf : a ∉ z.F := by
      intro h
      have hk := (z.mem_F.mp h).2
      omega
    have hbf : b ∉ z.F := by
      intro h
      have hk := (z.mem_F.mp h).2
      omega
    simp only [load, hfg]
    rw [sum_insert (by simpa [hne] using haf), sum_insert hbf]
    ring
  have hH : z.H = z.w a + z.w b := by simp [SharpData.H, hg, hne]
  have hD : z.D = 60 - z.W + z.H := by norm_num [SharpData.D, hf]
  have hE : z.E = z.H := by
    rw [z.excessHigh, hg]
    norm_num [ha, hb, hne, hH]
  have hS : z.H + z.S = 294 - 4 * z.W := by rw [← hE, SharpData.S]; ring
  have hHlt : z.H < 18 := by
    rw [← hE]
    exact z.excess_lt
  have hDlt : z.D < 9 := by linarith [z.hW]
  have hjpos : 0 < j.card := card_pos.mpr (z.hi a has b hbs)
  have huj : u.card = 4 + j.card := by
    have hpart := card_union_add_card_inter a b
    change (a ∪ b).card + j.card = a.card + b.card at hpart
    have hcompl : u.card + (a ∪ b).card = 14 := by
      simpa only [union_eq_left.mpr (subset_univ (a ∪ b)), card_univ, Fintype.card_fin] using
        card_sdiff_add_card (univ : Edge) (a ∪ b)
    omega
  have hcounts (p : Edge) (hp : p ∈ z.F) :
      (p ∩ u).card ≤ 3 ∧
        (Disjoint p (a ∩ b) → (p ∩ u).card ≤ 2) ∧
        ((p ∩ a).card = 1 → (p ∩ b).card = 1 → Disjoint p (a ∩ b) → (p ∩ u).card = 2) :=
    outsideCounts p a b (z.mem_F.mp hp).2
      (z.hi p (z.fourSubset hp) a has) (z.hi p (z.fourSubset hp) b hbs)
  have houtside (x : Fin 14) (hx : x ∈ u) (p : Edge) (hp : p ∈ z.G) : x ∉ p := by
    have hx' : x ∉ a ∧ x ∉ b := by simpa [u, not_or] using hx
    rw [hg] at hp
    simpa using (mem_insert.mp hp).elim
      (fun h => h.symm ▸ hx'.1) (fun h => (mem_singleton.mp h).symm ▸ hx'.2)
  have hu5 (x : Fin 14) (hx : x ∈ u) : 5 ≤ z.degree x := z.star x (houtside x hx)
  have hdeflo :
      4 * (u.card : ℝ) ≤ ∑ p ∈ z.F, ((p ∩ u).card : ℝ) * z.deficit p := by
    calc
      _ = ∑ _x ∈ u, (4 : ℝ) := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ x ∈ u, load z.F z.deficit x := by
        apply sum_le_sum
        intro x hx
        have hdeg : (5 : ℝ) ≤ z.degree x := by exact_mod_cast hu5 x hx
        linarith [z.deficitAt x, z.lowCap x]
      _ = _ := by simpa [inter_comm u] using sumLoadsOn z.F z.deficit u
  have hdefcoarse := z.outsideDeficit u ⟨a, hag⟩ houtside
  have hjle : j.card ≤ 2 := by
    by_contra! h
    have huc : (7 : ℝ) ≤ u.card := by exact_mod_cast (show 7 ≤ u.card by omega)
    linarith
  by_cases hj2 : j.card = 2
  · have hu6 : u.card = 6 := by omega
    let f3 := z.F.filter (fun p => (p ∩ u).card = 3)
    have hinc := sumIncidences z.F u
    have hlo : 30 ≤ ∑ p ∈ z.F, (p ∩ u).card := by
      rw [← hinc]
      calc
        _ = ∑ _x ∈ u, 5 := by simp [hu6]
        _ ≤ _ := sum_le_sum hu5
    have hup : (∑ p ∈ z.F, (p ∩ u).card) ≤ 24 + f3.card := by
      calc
        _ ≤ ∑ p ∈ z.F, (2 + if (p ∩ u).card = 3 then 1 else 0) := by
          apply sum_le_sum
          intro p hp
          have h := (hcounts p hp).1
          split_ifs <;> omega
        _ = _ := by simp [sum_add_distrib, hf, f3]
    have hf3 : 6 ≤ f3.card := by omega
    have hd3 : (∑ p ∈ f3, z.deficit p) ≤ z.D := by
      rw [← z.sum_deficit]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ =>
        (z.deficitPos p hp).le
    have hw3 : (∑ p ∈ f3, z.w p) = 5 * (f3.card : ℝ) - ∑ p ∈ f3, z.deficit p := by
      simp [SharpData.deficit, sum_sub_distrib, nsmul_eq_mul]
      ring
    have hbig : (21 : ℝ) < ∑ p ∈ f3, z.w p := by
      have h : (6 : ℝ) ≤ f3.card := by exact_mod_cast hf3
      linarith
    have hbound : (∑ p ∈ f3, z.w p) ≤ ∑ x ∈ j, load z.F z.w x := by
      rw [sumLoadsOn]
      calc
        _ ≤ ∑ p ∈ f3, ((j ∩ p).card : ℝ) * z.w p := by
          apply sum_le_sum
          intro p hp
          obtain ⟨hpf, hpc⟩ := mem_filter.mp hp
          have hn : (j ∩ p).Nonempty := by
            by_contra h
            have hd : Disjoint p (a ∩ b) := by
              rw [disjoint_iff_inter_eq_empty, inter_comm]
              exact not_nonempty_iff_eq_empty.mp h
            have hh := (hcounts p hpf).2.1 hd
            omega
          have hcard : (1 : ℝ) ≤ ((j ∩ p).card : ℝ) := by exact_mod_cast card_pos.mpr hn
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hcard (z.hw p (z.fourSubset hpf)).le
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun p hp _ =>
          mul_nonneg (Nat.cast_nonneg _) (z.hw p (z.fourSubset hp)).le
    have hcap : (∑ x ∈ j, load z.F z.w x) ≤ 2 * (21 - z.H) := by
      calc
        _ ≤ ∑ _x ∈ j, (21 - z.H) := by
          apply sum_le_sum
          intro x hx
          have ⟨hxa, hxb⟩ := mem_inter.mp hx
          have hh := hload x
          simp [hxa, hxb] at hh
          linarith [z.hc x]
        _ = _ := by simp [hj2, nsmul_eq_mul]; ring
    have hd8 : 8 ≤ z.D := by have h := hdefcoarse; norm_num [hu6] at h; linarith
    linarith [z.hW]
  · have hj1 : j.card = 1 := by omega
    obtain ⟨x, hx⟩ := card_eq_one.mp hj1
    have hxab : x ∈ a ∧ x ∈ b := by
      have h : x ∈ j := hx.symm ▸ mem_singleton_self x
      exact mem_inter.mp h
    have hu5card : u.card = 5 := by omega
    let fx := z.F.filter (fun p => x ∈ p)
    let f0 := z.F.filter (fun p => x ∉ p)
    let dx := ∑ p ∈ fx, z.deficit p
    have hpart : fx ∪ f0 = z.F := by ext p; by_cases h : x ∈ p <;> simp [fx, f0, h]
    have hdisj : Disjoint fx f0 := by
      rw [disjoint_left]
      intro p hp hq
      exact (mem_filter.mp hq).2 (mem_filter.mp hp).2
    have hpcard : fx.card + f0.card = 12 := by rw [← card_union_of_disjoint hdisj, hpart, hf]
    have hdpart : dx + (∑ p ∈ f0, z.deficit p) = z.D := by
      dsimp only [dx]
      rw [← sum_union hdisj, hpart, z.sum_deficit]
    have hdx : dx ≤ z.D := by
      have h : 0 ≤ ∑ p ∈ f0, z.deficit p :=
        sum_nonneg (fun p hp => (z.deficitPos p (mem_filter.mp hp).1).le)
      linarith
    have hdxload : dx = 5 * (fx.card : ℝ) - 21 + z.H + z.slack x := by
      have hh := hload x
      have hl := z.deficitAt x
      have hxload : dx = load z.F z.deficit x := by simp [dx, fx, load, sum_filter]
      rw [hxload]
      simp only [hxab.1, hxab.2, if_true] at hh
      have heq : z.degree x = fx.card := rfl
      rw [heq] at hl
      linarith [show z.slack x = 21 - load z.s z.w x from rfl]
    have hmiss (p : Edge) (hp : x ∉ p) : Disjoint p (a ∩ b) := by
      change Disjoint p j
      rw [hx, disjoint_left]
      intro y hyp hyx
      exact hp ((mem_singleton.mp hyx) ▸ hyp)
    have hrefined : (20 : ℝ) ≤ 2 * z.D + dx := by
      have h := hdeflo
      norm_num [hu5card] at h
      apply h.trans
      calc
        _ ≤ ∑ p ∈ z.F, (2 * z.deficit p + if x ∈ p then z.deficit p else 0) := by
          apply sum_le_sum
          intro p hp
          by_cases hpx : x ∈ p
          · have hc : ((p ∩ u).card : ℝ) ≤ 3 := by exact_mod_cast (hcounts p hp).1
            have hbound := mul_le_mul_of_nonneg_right hc (z.deficitPos p hp).le
            simp [hpx]
            linarith
          · have hc : ((p ∩ u).card : ℝ) ≤ 2 := by exact_mod_cast (hcounts p hp).2.1 (hmiss p hpx)
            simpa only [if_neg hpx, add_zero] using mul_le_mul_of_nonneg_right hc (z.deficitPos p hp).le
        _ = _ := by
          rw [sum_add_distrib, ← mul_sum, z.sum_deficit, ← sum_filter]
    have hfxpos : 0 < fx.card := z.fourAtVertex x
    have hfxle : fx.card ≤ 2 := by
      by_contra! h
      have hr : (3 : ℝ) ≤ fx.card := by exact_mod_cast h
      linarith [z.slackNonneg x, z.hW]
    have hfxne : fx.card ≠ 1 := by
      intro h1
      norm_num [h1] at hdxload
      have hslack : z.slack x ≤ z.S := by
        rw [← z.sum_slack]
        exact single_le_sum (fun i _ => z.slackNonneg i) (mem_univ x)
      linarith [z.slack_sum_nonneg, z.hW]
    have hfx2 : fx.card = 2 := by omega
    have hsmallD : (∑ p ∈ f0, z.deficit p) < 2 := by
      norm_num [hfx2] at hdxload
      linarith [z.slackNonneg x, z.hW]
    have hdefsum (p : Edge) (hp : p ∈ f0) : z.deficit p < 2 := by
      refine lt_of_le_of_lt (single_le_sum (fun q hq =>
        (z.deficitPos q (mem_filter.mp hq).1).le) hp) hsmallD
    have hhigh : (20 / 3 : ℝ) < z.w a ∧ (20 / 3 : ℝ) < z.w b := by
      have ha9 := z.weightFive a hag ha
      have hb9 := z.weightFive b hbg hb
      constructor <;> linarith [z.hW]
    have hlin (p : Edge) (hp : p ∈ f0) (q : Edge) (hq : q ∈ f0) (hpq : p ≠ q) :
        (p ∩ q).card ≤ 1 := by
      by_contra! hh
      have hpF := (mem_filter.mp hp).1
      have hqF := (mem_filter.mp hq).1
      have hpqtwo : 2 ≤ (p ∩ q).card := by omega
      have hqptwo : 2 ≤ (q ∩ p).card := by simpa [inter_comm] using hpqtwo
      have h1 := repeatedWeight z p q hpF (z.fourSubset hqF) hpq.symm hpqtwo
      have h2 := repeatedWeight z q p hqF (z.fourSubset hpF) hpq hqptwo
      have hsub : {p, q} ⊆ f0 := by
        intro r hr
        rcases mem_insert.mp hr with rfl | hr
        · exact hp
        · simpa using (mem_singleton.mp hr).symm ▸ hq
      have hsum := sum_le_sum_of_subset_of_nonneg hsub
        (fun r hr _ => (z.deficitPos r (mem_filter.mp hr).1).le)
      simp [hpq] at hsum
      dsimp only [SharpData.deficit] at h1 h2
      have hdp : z.deficit p = 5 - z.w p := rfl
      have hdq : z.deficit q = 5 - z.w q := rfl
      linarith
    have hquint (p : Edge) (hp : p ∈ f0) (q : Edge) (hq : q ∈ z.G)
        (hh : (20 / 3 : ℝ) < z.w q) : (p ∩ q).card = 1 := by
      have hpF := (mem_filter.mp hp).1
      have hpos := card_pos.mpr (z.hi p (z.fourSubset hpF) q (z.highSubset hq))
      by_contra h
      have hr : 2 ≤ (p ∩ q).card := by omega
      have hne' : q ≠ p := by
        intro heq
        exact disjoint_left.mp z.disjointFG hpF (heq ▸ hq)
      linarith [repeatedWeight z p q hpF (z.highSubset hq) hne' hr, hdefsum p hp]
    have hpc := localPigeonhole f0 (a.erase x) u
      (by simp [card_erase_of_mem hxab.1, ha]) hu5card
      (by
        rw [disjoint_left]
        intro y hya hyu
        exact (mem_sdiff.mp hyu).2 (mem_union_left _ (mem_erase.mp hya).2))
      (fun p hp => by
        have hpa := hquint p hp a hag hhigh.1
        have heq : p ∩ a.erase x = p ∩ a := by
          ext y
          have hpx := (mem_filter.mp hp).2
          by_cases hy : y = x
          · subst y
            simp [hpx]
          · simp [hy]
        rw [heq, hpa])
      (fun p hp => by
        obtain ⟨hpF, hpx⟩ := mem_filter.mp hp
        exact (hcounts p hpF).2.2 (hquint p hp a hag hhigh.1)
          (hquint p hp b hbg hhigh.2) (hmiss p hpx))
      hlin
    omega

end L14
