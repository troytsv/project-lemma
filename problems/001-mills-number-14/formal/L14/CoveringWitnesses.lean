module

public import L14.Covering

@[expose] public section

open Finset

namespace L14

private def barkerPoints : List (Fin 14) :=
  (List.ofFn (fun i : Fin 14 => i)).flatMap fun i => List.replicate (witnessData i).2 i

private theorem barkerPointCount : barkerPoints.length = 69 := by decide

private def barkerPattern (x : Fin 69) : Edge :=
  (witnessData (barkerPoints.get (Fin.cast barkerPointCount.symm x))).1

private def barkerBlocks (i : Fin 14) : Finset (Fin 69) :=
  univ.filter fun x => i ∈ barkerPattern x

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem barkerSizes : ∀ i, (barkerBlocks i).card = 21 := by
  decide

theorem barkerCover : 14 ∈ coveringBlockCounts 69 21 := by
  refine ⟨barkerBlocks, barkerSizes, ?_⟩
  intro x y _
  have hx (z : Fin 69) : barkerPattern z ∈ witness :=
    mem_image.mpr ⟨_, mem_univ _, rfl⟩
  obtain ⟨i, hi⟩ := witness_intersecting _ (hx x) _ (hx y)
  exact ⟨i, mem_filter.mpr ⟨mem_univ _, (mem_inter.mp hi).1⟩,
    mem_filter.mpr ⟨mem_univ _, (mem_inter.mp hi).2⟩⟩

theorem covering69_exact_scaled {n : ℕ} (hn : 0 < n) :
    IsLeast (coveringBlockCounts (69 * n) (21 * n)) 14 :=
  covering69_scaled barkerCover hn

-- The incidence columns of baseline/known15.txt, attributed to Arhan Canli (CC BY 4.0).
-- Bit i records membership in the ith block, and column x represents point x + 1.
private def canliMask (p : Fin 20) : Nat :=
  (![401, 1110, 1334, 2188, 3585, 4632, 6434, 6465, 6472, 6496,
     8235, 8964, 13440, 14656, 17120, 17672, 19074, 20485, 21122, 26640] :
      Fin 20 → Nat) p

private def canliColumn (x : Fin 70) : Fin 20 :=
  (![12, 10, 11, 11, 0, 9, 3, 1, 4, 6,
     10, 14, 4, 5, 9, 1, 12, 3, 19, 7,
     15, 14, 8, 19, 1, 17, 1, 15, 0, 0,
     16, 10, 10, 5, 18, 12, 15, 17, 4, 4,
     17, 13, 1, 11, 11, 10, 17, 9, 3, 0,
     14, 5, 2, 19, 14, 14, 6, 1, 12, 10,
     1, 19, 5, 10, 3, 14, 1, 10, 15, 14] : Fin 70 → Fin 20) x

private def canliBlocks (i : Fin 15) : Finset (Fin 70) :=
  univ.filter fun x => (canliMask (canliColumn x)).testBit i = true

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem canliSizes : ∀ i, (canliBlocks i).card = 21 := by
  decide

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem canliMeet : ∀ p q : Fin 20, ∃ i : Fin 15,
    (canliMask p).testBit i = true ∧ (canliMask q).testBit i = true := by
  decide

theorem canliCover : 15 ∈ coveringBlockCounts 70 21 := by
  refine ⟨canliBlocks, canliSizes, ?_⟩
  intro x y _
  obtain ⟨i, hx, hy⟩ := canliMeet (canliColumn x) (canliColumn y)
  exact ⟨i, mem_filter.mpr ⟨mem_univ _, hx⟩, mem_filter.mpr ⟨mem_univ _, hy⟩⟩

theorem covering70_exact_scaled {n : ℕ} (hn : 0 < n) :
    IsLeast (coveringBlockCounts (70 * n) (21 * n)) 15 :=
  covering70_scaled canliCover hn

end L14
