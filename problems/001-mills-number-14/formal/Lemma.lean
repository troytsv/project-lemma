module

public import Lemma.Sparse
public import Lemma.Ranks
public import Lemma.Incidence

@[expose] public section

open Finset
namespace C7021

/-- Fourteen indexed blocks of size 21 on 70 points miss a pair.
The blocks may repeat and there is no restriction on point incidences. -/
theorem noFourteenBlockCover (B : Fin 14 → Finset (Fin 70))
    (size : ∀ i, (B i).card = 21) :
    ¬ (∀ x y : Fin 70, x ≠ y → ∃ i, x ∈ B i ∧ y ∈ B i) := by
  classical
  intro cover
  let P (x : Fin 70) : Finset (Fin 14) := univ.filter (fun i => x ∈ B i)
  have memP (x : Fin 70) (i : Fin 14) : i ∈ P x ↔ x ∈ B i := by simp [P]
  have nonempty (x : Fin 70) : (P x).Nonempty := by
    obtain ⟨y, hy⟩ := exists_ne x
    obtain ⟨i, hx, _⟩ := cover x y (Ne.symm hy)
    exact ⟨i, (memP x i).2 hx⟩
  have intersect (x y : Fin 70) : (P x ∩ P y).Nonempty := by
    by_cases h : x = y
    · simpa [h] using nonempty y
    · obtain ⟨i, hx, hy⟩ := cover x y h
      exact ⟨i, mem_inter.mpr ⟨(memP x i).2 hx, (memP y i).2 hy⟩⟩
  have degrees (i : Fin 14) : (univ.filter (fun x => i ∈ P x)).card = 21 := by
    have eq : univ.filter (fun x => i ∈ P x) = B i := by ext x; simp [memP]
    rw [eq, size]
  obtain ⟨s, w, hs, hw, hm, hc⟩ := sparse P nonempty degrees
  obtain ⟨hr, h4, h5, he, tight⟩ := incidence P s w intersect hw hm hc
  obtain ⟨two, five, few, saturated⟩ :=
    rankCases s w (fun p => (P p).card) hs hw hm hr h4 h5 he
  let high := s.filter (fun p => (P p).card ≠ 4)
  have highCard : (high.biUnion P).card ≤ 10 := calc
    (high.biUnion P).card ≤ ∑ p ∈ high, (P p).card := card_biUnion_le
    _ = ∑ _p ∈ high, 5 := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨hps, hn⟩ := mem_filter.mp hp
      exact five p hps hn
    _ ≤ 10 := by simp; change high.card ≤ 2 at few; omega
  obtain ⟨i, hi⟩ : ∃ i : Fin 14, i ∉ high.biUnion P := by
    by_contra! hall
    have hu : high.biUnion P = univ := eq_univ_of_forall hall
    rw [hu] at highCard
    norm_num at highCard
  have evenLoad : (∑ p ∈ s, if i ∈ P p then w p else 0) =
      ((s.filter (fun p => i ∈ P p)).card : ℚ) * 2 := by
    calc
      _ = ∑ p ∈ s, if i ∈ P p then (2 : ℚ) else 0 := by
        apply sum_congr rfl
        intro p hp
        by_cases h : i ∈ P p
        · have four : (P p).card = 4 := by
            by_contra hn
            exact hi (mem_biUnion.mpr ⟨p, mem_filter.mpr ⟨hp, hn⟩, h⟩)
          simp [h, two p hp four]
        · simp [h]
      _ = _ := by rw [← sum_filter]; simp
  rw [tight saturated i] at evenLoad
  have impossible : 9 = (s.filter (fun p => i ∈ P p)).card * 2 := by
    exact_mod_cast evenLoad
  omega

end C7021
