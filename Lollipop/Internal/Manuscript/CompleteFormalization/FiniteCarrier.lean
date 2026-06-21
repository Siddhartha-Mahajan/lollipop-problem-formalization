import Lollipop.Internal.Manuscript.PrimitiveGeometry.ComponentBounds
import Mathlib.Data.Set.Card

/-!
Finite carrier witnesses from the proved component bounds.

The primitive geometry layer proves that every finite subset of the lifted
circle/ray components has the expected cardinality bound.  This file converts
those bounds into actual `Set.Finite` and `Finset` witnesses.  It is kept in the
`CompleteFormalization` folder so it refines the theorem boundary without
changing the older proof stack.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace FiniteCarrier

noncomputable section

/-- If every finite subset of a set has bounded cardinality, then the set is
finite.  Mathlib supplies the contrapositive direction via
`Set.Infinite.exists_subset_card_eq`. -/
theorem finite_of_forall_finset_subset_card_le
    {α : Type*} {s : Set α} {N : Nat}
    (h : ∀ T : Finset α, (T : Set α) ⊆ s → T.card ≤ N) :
    s.Finite := by
  by_contra hfinite
  have hinfinite : s.Infinite := hfinite
  rcases hinfinite.exists_subset_card_eq (N + 1) with ⟨T, hTsub, hTcard⟩
  have hle : T.card ≤ N := h T hTsub
  omega

/-- A lifted circle-circle component is finite when the two lifted circles are
distinct. -/
theorem euclideanCircleCircleSet_finite
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius) :
    (euclideanCircleCircleSet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 2) ?_
  intro S hS
  exact finset_card_le_two_of_forall_mem_euclideanCircleCircleSet hLM S
    (by
      intro p hp
      exact hS hp)

/-- A lifted circle-ray component is finite. -/
theorem euclideanCircleRaySet_finite
    (L M : EuclideanLollipop) :
    (euclideanCircleRaySet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 2) ?_
  intro S hS
  exact finset_card_le_two_of_forall_mem_euclideanCircleRaySet S
    (by
      intro p hp
      exact hS hp)

/-- A lifted ray-circle component is finite. -/
theorem euclideanRayCircleSet_finite
    (L M : EuclideanLollipop) :
    (euclideanRayCircleSet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 2) ?_
  intro S hS
  exact finset_card_le_two_of_forall_mem_euclideanRayCircleSet S
    (by
      intro p hp
      exact hS hp)

/-- A lifted ray-ray component is finite when the supporting ray lines are
distinct. -/
theorem euclideanRayRaySet_finite
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (euclideanRayRaySet L M).Finite := by
  refine finite_of_forall_finset_subset_card_le (N := 1) ?_
  intro S hS
  exact finset_card_le_one_of_forall_mem_euclideanRayRaySet hline S
    (by
      intro p hp
      exact hS hp)

/-- The whole lifted carrier intersection is finite under the two generic
noncoincidence hypotheses used throughout the upper-bound proof. -/
theorem euclideanPairIntersectionSet_finite
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (euclideanPairIntersectionSet L M).Finite := by
  let U : Set EuclideanR2 :=
    euclideanCircleCircleSet L M ∪ euclideanCircleRaySet L M ∪
      euclideanRayCircleSet L M ∪ euclideanRayRaySet L M
  have hUfinite : U.Finite := by
    dsimp [U]
    exact (((euclideanCircleCircleSet_finite hLM).union
      (euclideanCircleRaySet_finite L M)).union
      (euclideanRayCircleSet_finite L M)).union
      (euclideanRayRaySet_finite hline)
  refine hUfinite.subset ?_
  intro p hp
  rcases mem_euclideanPairIntersectionSet_iff.1 hp with hcc | hcr | hrc | hrr
  · exact Or.inl (Or.inl (Or.inl hcc))
  · exact Or.inl (Or.inl (Or.inr hcr))
  · exact Or.inl (Or.inr hrc)
  · exact Or.inr hrr

/-- The primitive carrier intersection is finite under the generic
noncoincidence hypotheses. -/
theorem pairIntersectionSet_finite
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (pairIntersectionSet L M).Finite := by
  have hE : (euclideanPairIntersectionSet L M).Finite :=
    euclideanPairIntersectionSet_finite hLM hline
  have hpre :
      ({p : R2 | toEuclideanR2 p ∈ euclideanPairIntersectionSet L M}).Finite := by
    exact hE.preimage
      (by
        intro x _hx y _hy hxy
        exact toEuclideanR2_injective hxy)
  simpa [pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet] using hpre

/-- The finite primitive carrier-intersection witness produced from the generic
noncoincidence hypotheses. -/
noncomputable def pairIntersectionFinset
    (L M : EuclideanLollipop)
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) : Finset R2 :=
  (pairIntersectionSet_finite hLM hline).toFinset

/-- The automatically produced finite witness is exactly the primitive carrier
intersection. -/
theorem pairIntersectionFinset_spec
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (pairIntersectionFinset L M hLM hline : Set R2) =
      pairIntersectionSet L M := by
  exact (pairIntersectionSet_finite hLM hline).coe_toFinset

/-- Any primitive finite subset of a generic carrier intersection has at most
seven points. -/
theorem finset_card_le_seven_of_forall_mem_pairIntersectionSet
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset R2)
    (hS : ∀ p ∈ S, p ∈ pairIntersectionSet L M) :
    S.card ≤ 7 := by
  have hlift :
      (liftedCrossingFinset S).card ≤ 7 := by
    refine finset_card_le_seven_of_forall_mem_euclideanPairIntersectionSet
      hLM hline (liftedCrossingFinset S) ?_
    intro p hp
    rcases Finset.mem_image.1 hp with ⟨x, hxS, rfl⟩
    have hx : x ∈ pairIntersectionSet L M := hS x hxS
    have hxpre :
        x ∈ {x : R2 | toEuclideanR2 x ∈
          euclideanPairIntersectionSet L M} := by
      simpa [pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet]
        using hx
    simpa using hxpre
  simpa using hlift

/-- The automatically produced finite witness has at most seven points. -/
theorem pairIntersectionFinset_card_le_seven
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (pairIntersectionFinset L M hLM hline).card ≤ 7 := by
  refine finset_card_le_seven_of_forall_mem_pairIntersectionSet
    hLM hline (pairIntersectionFinset L M hLM hline) ?_
  intro p hp
  have hp_set :
      p ∈ ((pairIntersectionFinset L M hLM hline : Finset R2) : Set R2) := by
    simpa using hp
  simpa [pairIntersectionFinset_spec hLM hline] using hp_set

/-- If a seven-point finite set lies inside a generic carrier intersection,
then the automatic finite carrier witness has cardinality at least seven. -/
theorem seven_le_pairIntersectionFinset_card_of_subset
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset R2)
    (hScard : S.card = 7)
    (hS : ∀ p ∈ S, p ∈ pairIntersectionSet L M) :
    7 ≤ (pairIntersectionFinset L M hLM hline).card := by
  have hsubset :
      S ⊆ pairIntersectionFinset L M hLM hline := by
    intro p hp
    have hp_set :
        p ∈ pairIntersectionSet L M := hS p hp
    have hp_auto :
        p ∈ ((pairIntersectionFinset L M hLM hline : Finset R2) :
          Set R2) := by
      simpa [pairIntersectionFinset_spec hLM hline] using hp_set
    simpa using hp_auto
  rw [← hScard]
  exact Finset.card_le_card hsubset

/-- A seven-point finite subset of a generic carrier intersection pins the
automatic finite carrier witness down to exactly seven points. -/
theorem pairIntersectionFinset_card_eq_seven_of_subset
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    (S : Finset R2)
    (hScard : S.card = 7)
    (hS : ∀ p ∈ S, p ∈ pairIntersectionSet L M) :
    (pairIntersectionFinset L M hLM hline).card = 7 := by
  exact Nat.le_antisymm
    (pairIntersectionFinset_card_le_seven hLM hline)
    (seven_le_pairIntersectionFinset_card_of_subset hLM hline S hScard hS)

/-- Local arrangement-indexed finite witness for one unordered pair. -/
noncomputable def arrangementPairIntersectionFinset
    {n : Nat} (A : EuclideanLollipopArrangement n)
    {i j : Fin n} (_hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    Finset R2 :=
  pairIntersectionFinset (A.lollipop i) (A.lollipop j) hLM hline

/-- The arrangement-indexed finite witness is exactly that pair's primitive
carrier intersection. -/
theorem arrangementPairIntersectionFinset_spec
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    (arrangementPairIntersectionFinset A hij hLM hline : Set R2) =
      A.pairIntersectionSet i j := by
  simpa [arrangementPairIntersectionFinset,
    EuclideanLollipopArrangement.pairIntersectionSet] using
    pairIntersectionFinset_spec hLM hline

/-- The arrangement-indexed finite witness has at most seven points. -/
theorem arrangementPairIntersectionFinset_card_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    (arrangementPairIntersectionFinset A hij hLM hline).card ≤ 7 :=
  pairIntersectionFinset_card_le_seven hLM hline

/-- A seven-point finite subset of one arrangement pair's carrier
intersection pins the automatic arrangement-indexed witness down to exactly
seven points. -/
theorem arrangementPairIntersectionFinset_card_eq_seven_of_subset
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (S : Finset R2)
    (hScard : S.card = 7)
    (hS : ∀ p ∈ S, p ∈ A.pairIntersectionSet i j) :
    (arrangementPairIntersectionFinset A hij hLM hline).card = 7 := by
  refine pairIntersectionFinset_card_eq_seven_of_subset
    hLM hline S hScard ?_
  intro p hp
  simpa [EuclideanLollipopArrangement.pairIntersectionSet] using hS p hp

/-- If a crossing table is defined as the cardinality of the automatic finite
witness for one pair, that pair has a local carrier-crossing certificate. -/
noncomputable def localPairCarrierCrossingDataOfFiniteCarrier
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j)) :
    LocalPairCarrierCrossingData A
      (fun a b =>
        if _h : a = i ∧ b = j then
          ((arrangementPairIntersectionFinset A hij hLM hline).card : Rat)
        else 0)
      i j hij where
  crossingPoints := arrangementPairIntersectionFinset A hij hLM hline
  crossingPoints_spec := arrangementPairIntersectionFinset_spec hLM hline
  cross_eq_card := by
    simp

/-- A more flexible local certificate constructor: any crossing table whose
selected entry is the cardinality of the automatic finite witness gets a local
carrier-crossing certificate for that pair. -/
noncomputable def localPairCarrierCrossingDataOfFiniteCarrierEq
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    {i j : Fin n} (hij : i < j)
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (hcross :
      cross i j =
        ((arrangementPairIntersectionFinset A hij hLM hline).card : Rat)) :
    LocalPairCarrierCrossingData A cross i j hij where
  crossingPoints := arrangementPairIntersectionFinset A hij hLM hline
  crossingPoints_spec := arrangementPairIntersectionFinset_spec hLM hline
  cross_eq_card := hcross

/-- The automatic pairwise crossing table obtained by counting each finite
carrier intersection.  Unordered pairs `i < j` get their exact finite-witness
cardinality; other entries are set to zero because the formal upper pipeline
only consumes increasing pairs. -/
noncomputable def automaticCarrierCrossingTable
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j)) :
    Fin n → Fin n → Rat :=
  fun i j =>
    if hij : i < j then
      ((arrangementPairIntersectionFinset A hij (hLM i j hij)
        (hline i j hij)).card : Rat)
    else
      0

/-- Each increasing entry of the automatic crossing table is the cardinality of
the corresponding automatic finite witness. -/
theorem automaticCarrierCrossingTable_eq_card
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j) :
    automaticCarrierCrossingTable A hLM hline i j =
      ((arrangementPairIntersectionFinset A hij (hLM i j hij)
        (hline i j hij)).card : Rat) := by
  simp [automaticCarrierCrossingTable, hij]

/-- The automatic crossing table has a bundled pairwise carrier-crossing
certificate. -/
noncomputable def pairwiseCarrierCrossingDataOfFiniteCarrier
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j)) :
    PairwiseCarrierCrossingData A
      (automaticCarrierCrossingTable A hLM hline) where
  crossingPoints := fun i j hij =>
    arrangementPairIntersectionFinset A hij (hLM i j hij) (hline i j hij)
  crossingPoints_spec := by
    intro i j hij
    exact arrangementPairIntersectionFinset_spec (hLM i j hij) (hline i j hij)
  cross_eq_card := by
    intro i j hij
    exact automaticCarrierCrossingTable_eq_card hLM hline hij

/-- Every increasing entry of the automatic crossing table is at most seven. -/
theorem automaticCarrierCrossingTable_le_seven
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j) :
    automaticCarrierCrossingTable A hLM hline i j ≤ 7 := by
  rw [automaticCarrierCrossingTable_eq_card hLM hline hij]
  exact_mod_cast arrangementPairIntersectionFinset_card_le_seven
    (hLM i j hij) (hline i j hij)

end

end FiniteCarrier
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
