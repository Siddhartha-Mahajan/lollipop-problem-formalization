import Lollipop.Internal.Manuscript.CompleteFormalization.FiniteCarrier
import Lollipop.Internal.Manuscript.ExplicitInputs.KarlssonOEISGeometry

/-!
Seven-point lower witnesses for the non-exceptional OEIS base pairs.

The automatic finite-carrier construction proves `<= 7` for any generic pair.
For the five non-exceptional OEIS/Karlsson base pairs, it remains to prove
`>= 7`.  This file records the exact reusable bridge: a seven-point finite set
inside the primitive carrier intersection immediately yields the required
coordinate crossing certificate by taking the automatic finite witness.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

open PrimitiveGeometry

namespace OEISSevenPoint

noncomputable section

open ExplicitInputs

/-- A concrete seven-point lower witness for one OEIS/Karlsson base pair. -/
structure SevenPointSubset (i j : Fin 4) where
  points : Finset R2
  card_eq_seven : points.card = 7
  points_subset :
    ∀ p ∈ points, p ∈ karlssonOEISBaseArrangement.pairIntersectionSet i j

theorem pair_mem_of_euclideanCircleCircle
    {i j : Fin 4} {p : R2}
    (hp :
      toEuclideanR2 p ∈
        euclideanCircleCircleSet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j)) :
    p ∈ karlssonOEISBaseArrangement.pairIntersectionSet i j := by
  have hE :
      toEuclideanR2 p ∈
        euclideanPairIntersectionSet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j) := by
    exact mem_euclideanPairIntersectionSet_iff.2 (Or.inl hp)
  simpa [EuclideanLollipopArrangement.pairIntersectionSet,
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet] using hE

theorem pair_mem_of_euclideanCircleRay
    {i j : Fin 4} {p : R2}
    (hp :
      toEuclideanR2 p ∈
        euclideanCircleRaySet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j)) :
    p ∈ karlssonOEISBaseArrangement.pairIntersectionSet i j := by
  have hE :
      toEuclideanR2 p ∈
        euclideanPairIntersectionSet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j) := by
    exact mem_euclideanPairIntersectionSet_iff.2 (Or.inr (Or.inl hp))
  simpa [EuclideanLollipopArrangement.pairIntersectionSet,
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet] using hE

theorem pair_mem_of_euclideanRayCircle
    {i j : Fin 4} {p : R2}
    (hp :
      toEuclideanR2 p ∈
        euclideanRayCircleSet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j)) :
    p ∈ karlssonOEISBaseArrangement.pairIntersectionSet i j := by
  have hE :
      toEuclideanR2 p ∈
        euclideanPairIntersectionSet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j) := by
    exact mem_euclideanPairIntersectionSet_iff.2 (Or.inr (Or.inr (Or.inl hp)))
  simpa [EuclideanLollipopArrangement.pairIntersectionSet,
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet] using hE

theorem pair_mem_of_euclideanRayRay
    {i j : Fin 4} {p : R2}
    (hp :
      toEuclideanR2 p ∈
        euclideanRayRaySet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j)) :
    p ∈ karlssonOEISBaseArrangement.pairIntersectionSet i j := by
  have hE :
      toEuclideanR2 p ∈
        euclideanPairIntersectionSet
          (karlssonOEISBaseArrangement.lollipop i)
          (karlssonOEISBaseArrangement.lollipop j) := by
    exact mem_euclideanPairIntersectionSet_iff.2
      (Or.inr (Or.inr (Or.inr hp)))
  simpa [EuclideanLollipopArrangement.pairIntersectionSet,
    pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet] using hE

/-- Component-shaped version of a seven-point lower witness.  It matches the
generic `2 + 2 + 2 + 1` upper bound: two circle-circle points, two circle-ray
points, two ray-circle points, and one ray-ray point. -/
structure SevenComponentWitness (i j : Fin 4) where
  cc1 : R2
  cc2 : R2
  cr1 : R2
  cr2 : R2
  rc1 : R2
  rc2 : R2
  rr : R2
  cc1_mem :
    toEuclideanR2 cc1 ∈
      euclideanCircleCircleSet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  cc2_mem :
    toEuclideanR2 cc2 ∈
      euclideanCircleCircleSet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  cr1_mem :
    toEuclideanR2 cr1 ∈
      euclideanCircleRaySet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  cr2_mem :
    toEuclideanR2 cr2 ∈
      euclideanCircleRaySet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  rc1_mem :
    toEuclideanR2 rc1 ∈
      euclideanRayCircleSet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  rc2_mem :
    toEuclideanR2 rc2 ∈
      euclideanRayCircleSet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  rr_mem :
    toEuclideanR2 rr ∈
      euclideanRayRaySet
        (karlssonOEISBaseArrangement.lollipop i)
        (karlssonOEISBaseArrangement.lollipop j)
  nodup : [cc1, cc2, cr1, cr2, rc1, rc2, rr].Nodup

namespace SevenComponentWitness

/-- The seven labelled component points as a finite set. -/
noncomputable def points {i j : Fin 4}
    (W : SevenComponentWitness i j) : Finset R2 := by
  classical
  exact [W.cc1, W.cc2, W.cr1, W.cr2, W.rc1, W.rc2, W.rr].toFinset

/-- The labelled component witness really has seven distinct points. -/
theorem points_card_eq_seven {i j : Fin 4}
    (W : SevenComponentWitness i j) :
    W.points.card = 7 := by
  classical
  rw [points, List.toFinset_card_of_nodup W.nodup]
  rfl

/-- Every labelled component point lies in the primitive carrier intersection. -/
theorem points_subset {i j : Fin 4}
    (W : SevenComponentWitness i j) :
    ∀ p ∈ W.points, p ∈ karlssonOEISBaseArrangement.pairIntersectionSet i j := by
  classical
  intro p hp
  simp [points] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pair_mem_of_euclideanCircleCircle W.cc1_mem
  · exact pair_mem_of_euclideanCircleCircle W.cc2_mem
  · exact pair_mem_of_euclideanCircleRay W.cr1_mem
  · exact pair_mem_of_euclideanCircleRay W.cr2_mem
  · exact pair_mem_of_euclideanRayCircle W.rc1_mem
  · exact pair_mem_of_euclideanRayCircle W.rc2_mem
  · exact pair_mem_of_euclideanRayRay W.rr_mem

/-- Forget the component labels and keep only the seven-point lower witness
needed by the automatic finite-carrier exactness bridge. -/
noncomputable def toSevenPointSubset {i j : Fin 4}
    (W : SevenComponentWitness i j) : SevenPointSubset i j where
  points := W.points
  card_eq_seven := W.points_card_eq_seven
  points_subset := W.points_subset

end SevenComponentWitness

/-- A seven-point lower witness pins the automatic finite carrier witness down
to exactly seven points. -/
theorem automatic_witness_card_eq_seven
    {i j : Fin 4} {hij : i < j}
    (W : SevenPointSubset i j) :
    (FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement hij
      (karlssonOEISBase_spheres_distinct hij)
      (karlssonOEISBase_rayLines_distinct hij)).card = 7 :=
  FiniteCarrier.arrangementPairIntersectionFinset_card_eq_seven_of_subset
    (karlssonOEISBase_spheres_distinct hij)
    (karlssonOEISBase_rayLines_distinct hij)
    W.points W.card_eq_seven W.points_subset

/-- A direct exact `7` pair-coordinate certificate from a seven-point lower
witness.  The certificate uses the automatic finite carrier witness, so its
set equality is already provided by `FiniteCarrier`. -/
noncomputable def pairCoordinateCrossingCertificate
    {i j : Fin 4} (hij : i < j)
    (hbase : karlssonBasePairCrossing i j = 7)
    (W : SevenPointSubset i j) :
    KarlssonOEISBasePairCoordinateCrossingCertificate i j hij where
  crossingPoints :=
    FiniteCarrier.arrangementPairIntersectionFinset
      karlssonOEISBaseArrangement hij
      (karlssonOEISBase_spheres_distinct hij)
      (karlssonOEISBase_rayLines_distinct hij)
  crossingPoints_spec :=
    FiniteCarrier.arrangementPairIntersectionFinset_spec
      (karlssonOEISBase_spheres_distinct hij)
      (karlssonOEISBase_rayLines_distinct hij)
  cross_eq_card := by
    rw [automatic_witness_card_eq_seven (hij := hij) W]
    exact hbase

/-- Specialized constructor for the OEIS base pair `(Q0,Q2)`. -/
noncomputable def pair02Certificate
    (W : SevenPointSubset (0 : Fin 4) (2 : Fin 4)) :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (2 : Fin 4) (by decide) :=
  pairCoordinateCrossingCertificate (by decide)
    karlssonBasePairCrossing_zero_two W

/-- Specialized constructor for the OEIS base pair `(Q0,Q3)`. -/
noncomputable def pair03Certificate
    (W : SevenPointSubset (0 : Fin 4) (3 : Fin 4)) :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (0 : Fin 4) (3 : Fin 4) (by decide) :=
  pairCoordinateCrossingCertificate (by decide)
    karlssonBasePairCrossing_zero_three W

/-- Specialized constructor for the OEIS base pair `(Q1,Q2)`. -/
noncomputable def pair12Certificate
    (W : SevenPointSubset (1 : Fin 4) (2 : Fin 4)) :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (1 : Fin 4) (2 : Fin 4) (by decide) :=
  pairCoordinateCrossingCertificate (by decide)
    karlssonBasePairCrossing_one_two W

/-- Specialized constructor for the OEIS base pair `(Q1,Q3)`. -/
noncomputable def pair13Certificate
    (W : SevenPointSubset (1 : Fin 4) (3 : Fin 4)) :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (1 : Fin 4) (3 : Fin 4) (by decide) :=
  pairCoordinateCrossingCertificate (by decide)
    karlssonBasePairCrossing_one_three W

/-- Specialized constructor for the OEIS base pair `(Q2,Q3)`. -/
noncomputable def pair23Certificate
    (W : SevenPointSubset (2 : Fin 4) (3 : Fin 4)) :
    KarlssonOEISBasePairCoordinateCrossingCertificate
      (2 : Fin 4) (3 : Fin 4) (by decide) :=
  pairCoordinateCrossingCertificate (by decide)
    karlssonBasePairCrossing_two_three W

end

end OEISSevenPoint
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
