import Mathlib.Tactic

/-!
Finite direction pigeonhole for the close-pair input.

The manuscript uses the elementary fact that among four stem directions in the
plane, two differ by at most a right angle.  This file formalizes the
one-dimensional normalized-angle core of that fact: for four numbers in
cyclic order in `[0, 1)`, one adjacent cyclic gap is at most `1 / 4`.
-/

namespace Lollipop
namespace TheoremOneEndToEnd
namespace CloseDirection

/-- Two normalized directions are close when their circular distance on
`R/Z` is at most `1 / 4`. -/
def cyclicClosePair (a b : ℝ) : Prop :=
  |a - b| ≤ (1 / 4 : ℝ) ∨ (3 / 4 : ℝ) ≤ |a - b|

/-- The canonical close relation from a normalized direction map. -/
def cyclicClose {V : Type*} (theta : V → ℝ) (i j : V) : Prop :=
  cyclicClosePair (theta i) (theta j)

theorem cyclicClosePair_symm (a b : ℝ) :
    cyclicClosePair a b ↔ cyclicClosePair b a := by
  unfold cyclicClosePair
  rw [abs_sub_comm a b]

theorem cyclicClose_symm {V : Type*} (theta : V → ℝ) (i j : V) :
    cyclicClose theta i j ↔ cyclicClose theta j i := by
  exact cyclicClosePair_symm (theta i) (theta j)

/-- If the ordinary normalized-angle distance lies strictly between the two
close thresholds, then the cyclic-close predicate is false. -/
theorem not_cyclicClosePair_of_abs_between
    {a b : ℝ}
    (hlo : (1 / 4 : ℝ) < |a - b|)
    (hhi : |a - b| < (3 / 4 : ℝ)) :
    ¬ cyclicClosePair a b := by
  intro hclose
  rcases hclose with hle | hge
  · linarith
  · linarith

/-- Map-valued version of `not_cyclicClosePair_of_abs_between`. -/
theorem not_cyclicClose_of_abs_between
    {V : Type*} {theta : V → ℝ} {i j : V}
    (hlo : (1 / 4 : ℝ) < |theta i - theta j|)
    (hhi : |theta i - theta j| < (3 / 4 : ℝ)) :
    ¬ cyclicClose theta i j :=
  not_cyclicClosePair_of_abs_between hlo hhi

private theorem cyclicClosePair_of_ordered_sub_le
    {a b : ℝ} (hab : a ≤ b) (h : b - a ≤ (1 / 4 : ℝ)) :
    cyclicClosePair a b := by
  left
  have habs : |a - b| = b - a := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rwa [habs]

private theorem cyclicClosePair_of_wrap_gap_le
    {a b : ℝ} (_hab : a ≤ b) (h : a + 1 - b ≤ (1 / 4 : ℝ)) :
    cyclicClosePair b a := by
  right
  have habs : |b - a| = b - a := by
    rw [abs_of_nonneg]
    linarith
  rw [habs]
  linarith

/-- Four normalized directions in cyclic order contain a close adjacent pair. -/
theorem sorted_four_has_cyclicClose
    (theta : Fin 4 → ℝ)
    (h0 : 0 ≤ theta 0)
    (h01 : theta 0 ≤ theta 1)
    (h12 : theta 1 ≤ theta 2)
    (h23 : theta 2 ≤ theta 3)
    (h3 : theta 3 < 1) :
    ∃ i : Fin 4, ∃ j : Fin 4, i ≠ j ∧ cyclicClose theta i j := by
  by_cases h01gap : theta 1 - theta 0 ≤ (1 / 4 : ℝ)
  · exact ⟨0, 1, by decide,
      cyclicClosePair_of_ordered_sub_le h01 h01gap⟩
  · by_cases h12gap : theta 2 - theta 1 ≤ (1 / 4 : ℝ)
    · exact ⟨1, 2, by decide,
        cyclicClosePair_of_ordered_sub_le h12 h12gap⟩
    · by_cases h23gap : theta 3 - theta 2 ≤ (1 / 4 : ℝ)
      · exact ⟨2, 3, by decide,
          cyclicClosePair_of_ordered_sub_le h23 h23gap⟩
      · by_cases hwrap : theta 0 + 1 - theta 3 ≤ (1 / 4 : ℝ)
        · have h03 : theta 0 ≤ theta 3 := by linarith
          exact ⟨3, 0, by decide,
            cyclicClosePair_of_wrap_gap_le h03 hwrap⟩
        · have h01gt : (1 / 4 : ℝ) < theta 1 - theta 0 :=
            lt_of_not_ge h01gap
          have h12gt : (1 / 4 : ℝ) < theta 2 - theta 1 :=
            lt_of_not_ge h12gap
          have h23gt : (1 / 4 : ℝ) < theta 3 - theta 2 :=
            lt_of_not_ge h23gap
          have hwrapgt : (1 / 4 : ℝ) < theta 0 + 1 - theta 3 :=
            lt_of_not_ge hwrap
          nlinarith

/-- Cyclic ordering data for a four-element subset.  The enumeration lists the
four directions in nondecreasing normalized-angle order. -/
structure FourSetCyclicOrderData {V : Type*} (theta : V → ℝ)
    (t : Finset V) where
  enumerate : Fin 4 ≃ {x : V // x ∈ t}
  sorted01 : theta (enumerate 0) ≤ theta (enumerate 1)
  sorted12 : theta (enumerate 1) ≤ theta (enumerate 2)
  sorted23 : theta (enumerate 2) ≤ theta (enumerate 3)

namespace FourSetCyclicOrderData

/-- Ordered direction data on a four-set yields a close pair in that four-set. -/
theorem exists_cyclicClose_pair
    {V : Type*} {theta : V → ℝ} {t : Finset V}
    (D : FourSetCyclicOrderData theta t)
    (htheta_nonneg : ∀ x ∈ t, 0 ≤ theta x)
    (htheta_lt_one : ∀ x ∈ t, theta x < 1) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ cyclicClose theta x y := by
  let localTheta : Fin 4 → ℝ := fun i => theta (D.enumerate i)
  have h0 : 0 ≤ localTheta 0 :=
    htheta_nonneg (D.enumerate 0) (D.enumerate 0).property
  have h3 : localTheta 3 < 1 :=
    htheta_lt_one (D.enumerate 3) (D.enumerate 3).property
  rcases sorted_four_has_cyclicClose localTheta h0
      D.sorted01 D.sorted12 D.sorted23 h3 with
    ⟨i, j, hij, hclose⟩
  refine ⟨D.enumerate i, (D.enumerate i).property,
    D.enumerate j, (D.enumerate j).property, ?_, hclose⟩
  intro hval
  exact hij (D.enumerate.injective (Subtype.ext hval))

end FourSetCyclicOrderData

/-- Any four normalized directions contain a close pair.  This packages the
sorting step with mathlib's `List.mergeSort`, so later geometric certificates
only need a normalized direction map rather than sorted order data for every
four-subset. -/
theorem exists_cyclicClose_pair_of_card_four
    {V : Type*} [DecidableEq V]
    (theta : V → ℝ) {t : Finset V} (ht : t.card = 4)
    (htheta_nonneg : ∀ x ∈ t, 0 ≤ theta x)
    (htheta_lt_one : ∀ x ∈ t, theta x < 1) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ cyclicClose theta x y := by
  classical
  let r : V → V → Prop := fun x y => theta x ≤ theta y
  letI : IsTrans V r :=
    ⟨fun _x _y _z hxy hyz => le_trans hxy hyz⟩
  letI : Std.Total r :=
    ⟨fun x y => le_total (theta x) (theta y)⟩
  let l : List V := t.toList.mergeSort (fun x y => theta x ≤ theta y)
  have hperm : List.Perm l t.toList := by
    simpa [l] using List.mergeSort_perm t.toList (fun x y => theta x ≤ theta y)
  have hlen : l.length = 4 := by
    simp [l, Finset.length_toList, ht]
  have hsorted : l.Pairwise r := by
    simpa [l, r] using List.pairwise_mergeSort' r t.toList
  have hnodup : l.Nodup := by
    simpa [l] using
      (Finset.nodup_toList t).mergeSort
        (le := fun x y => theta x ≤ theta y)
  let idx : Fin 4 → Fin l.length := fun i => Fin.cast hlen.symm i
  let localTheta : Fin 4 → ℝ := fun i => theta (l.get (idx i))
  have hmem : ∀ i : Fin 4, l.get (idx i) ∈ t := by
    intro i
    have hmem_l : l.get (idx i) ∈ l := List.get_mem l (idx i)
    have hmem_toList : l.get (idx i) ∈ t.toList :=
      hperm.mem_iff.mp hmem_l
    simpa using hmem_toList
  have h0 : 0 ≤ localTheta 0 :=
    htheta_nonneg (l.get (idx 0)) (hmem 0)
  have h3 : localTheta 3 < 1 :=
    htheta_lt_one (l.get (idx 3)) (hmem 3)
  have h01 : localTheta 0 ≤ localTheta 1 := by
    exact hsorted.rel_get_of_lt (show idx 0 < idx 1 by
      rw [Fin.lt_def]
      norm_num [idx])
  have h12 : localTheta 1 ≤ localTheta 2 := by
    exact hsorted.rel_get_of_lt (show idx 1 < idx 2 by
      rw [Fin.lt_def]
      norm_num [idx])
  have h23 : localTheta 2 ≤ localTheta 3 := by
    exact hsorted.rel_get_of_lt (show idx 2 < idx 3 by
      rw [Fin.lt_def]
      norm_num [idx])
  rcases sorted_four_has_cyclicClose localTheta h0 h01 h12 h23 h3 with
    ⟨i, j, hij, hclose⟩
  refine ⟨l.get (idx i), hmem i, l.get (idx j), hmem j, ?_, hclose⟩
  intro hxy
  have hidx : idx i = idx j := hnodup.get_inj_iff.mp hxy
  exact hij (Fin.cast_injective hlen.symm hidx)

end CloseDirection
end TheoremOneEndToEnd
end Lollipop
