import Lollipop.Internal.Manuscript.CompleteFormalization.FiniteCarrier
import Lollipop.Internal.Manuscript.FirstPrinciples.LocalBoundary
import Lollipop.Internal.Manuscript.PrimitiveGeometry.LowerWitness

/-!
Automatic lower witnesses from finite primitive carrier subsets.

This module refines the theorem-facing monotone lower boundary.  Instead of
asking the construction to prove pair-crossing lower inequalities directly, it
can supply finite subsets inside each primitive pair carrier.  Mathlib's
`Finset.card_le_card` monotonicity, already packaged in
`PrimitiveGeometry.LowerWitness`, then turns those subsets into the local
Karlsson lower certificates consumed by Theorem 1.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace EndToEndFormalization
namespace AutomaticLower

open PrimitiveGeometry

universe u

noncomputable section

/-- Stepwise monotone lower certificate generated from automatic finite
carrier intersections.

For each sorted blow-up arrangement and each unordered copy pair, the
construction supplies a finite lower subset of the corresponding primitive
carrier.  The pair table used by the region recurrence is required to agree
on produced arrangements with the automatic finite-carrier table.  Lean then
derives the monotone Karlsson lower pair inequality for every copy pair. -/
structure StepwiseMonotoneCarrierSubsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  local_lower_bound :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ∀ i j : Fin n, i < j → Nat
  cluster_le_local_lower_bound :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.karlssonClusterPairCrossing
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j) ≤
          (local_lower_bound n q hq i j hij : Rat)
  lower_subset :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalPairCarrierLowerSubsetData
          (primitive_arrangement n q hq) i j hij
          (local_lower_bound n q hq i j hij)
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseMonotoneCarrierSubsetLowerCertificate

/-- The automatic finite carrier table gives a local carrier-crossing
certificate for every produced copy pair. -/
noncomputable def localCarrierCrossingData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    LocalPairCarrierCrossingData (h.primitive_arrangement n q hq)
      (h.pair_cross n (h.arrangement n q hq)) i j hij := by
  refine
    CompleteFormalization.FiniteCarrier.localPairCarrierCrossingDataOfFiniteCarrierEq
      (A := h.primitive_arrangement n q hq)
      (cross := h.pair_cross n (h.arrangement n q hq))
      hij
      (h.spheres_distinct n q hq i j hij)
      (h.rayLines_distinct n q hq i j hij)
      ?_
  calc
    h.pair_cross n (h.arrangement n q hq) i j =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (h.primitive_arrangement n q hq)
          (h.spheres_distinct n q hq)
          (h.rayLines_distinct n q hq) i j := by
      exact congrFun (congrFun (h.pair_cross_eq_automatic n q hq) i) j
    _ =
        ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          (h.primitive_arrangement n q hq) hij
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)).card : Rat) := by
      exact CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
        (h.spheres_distinct n q hq) (h.rayLines_distinct n q hq) hij

/-- The finite lower subset supplied for one pair gives the local monotone
Karlsson lower certificate for that pair. -/
noncomputable def localClusterPairLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ExplicitInputs.LocalClusterPairLowerBoundData
      ((h.cluster_witness n q hq).cluster)
      (h.pair_cross n (h.arrangement n q hq)) i j hij :=
  (h.lower_subset n q hq i j hij).toLocalClusterPairLowerBoundData
    (h.localCarrierCrossingData hij)
    (h.cluster_le_local_lower_bound n q hq i j hij)

/-- Assemble automatic finite carrier lower subsets into the local monotone
lower boundary already consumed by the final Theorem 1 pipeline. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P where
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  local_pair_cross_ge_cluster := by
    intro n q hq i j hij
    exact h.localClusterPairLowerBoundData hij
  region_increment := h.region_increment

/-- Direct conversion to the monotone pairwise lower package used by the
Theorem 1 subtheorem stack. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P :=
  h.toStepwisePairLocalKarlssonLowerBoundCertificate
    |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

/-- The automatic finite carrier lower-subset boundary proves lower-bound
attainment in the displayed candidate form. -/
theorem lower_bound_attainment_choose
    (P : TheoremOne.ProblemFamily.{u})
    (h : StepwiseMonotoneCarrierSubsetLowerCertificate P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A :=
  ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData.lower_bound_attainment_choose
    P
    h.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end StepwiseMonotoneCarrierSubsetLowerCertificate

/-- Common automatic-lower specialization where each finite lower subset is
required to have exactly the Nat-valued Karlsson cluster-table size
`4`, `5`, or `7`.  Lean proves internally that this Nat size coerces to the
rational lower table used by the theorem stack. -/
structure StepwiseKarlssonCarrierSubsetLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  lower_subset :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalPairCarrierLowerSubsetData
          (primitive_arrangement n q hq) i j hij
          (ExplicitInputs.karlssonClusterPairCrossingNat
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j))
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseKarlssonCarrierSubsetLowerCertificate

/-- A Karlsson-sized lower-subset certificate is a special case of the more
flexible automatic monotone carrier-subset lower certificate. -/
noncomputable def toStepwiseMonotoneCarrierSubsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierSubsetLowerCertificate P) :
    StepwiseMonotoneCarrierSubsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  cluster_witness := h.cluster_witness
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  local_lower_bound := by
    intro n q hq i j _hij
    exact ExplicitInputs.karlssonClusterPairCrossingNat
      ((h.cluster_witness n q hq).cluster i)
      ((h.cluster_witness n q hq).cluster j)
  cluster_le_local_lower_bound := by
    intro n q hq i j _hij
    rw [ExplicitInputs.karlssonClusterPairCrossing_eq_nat]
  lower_subset := h.lower_subset
  region_increment := h.region_increment

/-- Convert Karlsson-sized carrier lower subsets directly to the monotone
local lower boundary. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierSubsetLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P :=
  h.toStepwiseMonotoneCarrierSubsetLowerCertificate
    |>.toStepwisePairLocalKarlssonLowerBoundCertificate

/-- Direct conversion to the monotone pairwise lower package. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierSubsetLowerCertificate P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P :=
  h.toStepwisePairLocalKarlssonLowerBoundCertificate
    |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end StepwiseKarlssonCarrierSubsetLowerCertificate

/-- Automatic lower specialization where the construction proves the
automatic carrier finset itself has at least the Nat-valued Karlsson
`4/5/7` size.  Lean then uses that automatic finset as the lower subset. -/
structure StepwiseKarlssonCarrierCardLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  automatic_card_ge :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.karlssonClusterPairCrossingNat
            ((cluster_witness n q hq).cluster i)
            ((cluster_witness n q hq).cluster j) ≤
          (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (primitive_arrangement n q hq) hij
            (spheres_distinct n q hq i j hij)
            (rayLines_distinct n q hq i j hij)).card
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseKarlssonCarrierCardLowerCertificate

/-- The automatic carrier finset supplies the lower subset when its
cardinality reaches the Nat-valued Karlsson table size. -/
noncomputable def toStepwiseKarlssonCarrierSubsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierCardLowerCertificate P) :
    StepwiseKarlssonCarrierSubsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  cluster_witness := h.cluster_witness
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  lower_subset := by
    intro n q hq i j hij
    refine
      { lowerPoints :=
          CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (h.primitive_arrangement n q hq) hij
            (h.spheres_distinct n q hq i j hij)
            (h.rayLines_distinct n q hq i j hij)
        lowerPoints_subset := ?_
        bound_le_card := h.automatic_card_ge n q hq i j hij }
    intro p hp
    have hp_set :
        p ∈ ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          (h.primitive_arrangement n q hq) hij
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij) : Finset R2) : Set R2) := by
      simpa using hp
    simpa
      [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (h.spheres_distinct n q hq i j hij)
        (h.rayLines_distinct n q hq i j hij)]
      using hp_set
  region_increment := h.region_increment

/-- Convert automatic carrier-cardinality lower data to the monotone local
lower boundary. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseKarlssonCarrierCardLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P :=
  h.toStepwiseKarlssonCarrierSubsetLowerCertificate
    |>.toStepwisePairLocalKarlssonLowerBoundCertificate

end StepwiseKarlssonCarrierCardLowerCertificate

/-- Automatic lower specialization with the canonical sorted-quad cluster
witness built in.

Compared with `StepwiseKarlssonCarrierCardLowerCertificate`, this removes the
`cluster_witness` input from the theorem-facing boundary.  The lower
construction only has to prove that each automatic carrier finset has
cardinality at least the Nat-valued Karlsson table entry for the canonical
cluster labels of the sorted quadruple. -/
structure StepwiseCanonicalKarlssonCarrierCardLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  primitive_arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanSphere
            ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius ≠
          euclideanSphere
            ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius
  rayLines_distinct :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        euclideanRayLine ((primitive_arrangement n q hq).lollipop i) ≠
          euclideanRayLine ((primitive_arrangement n q hq).lollipop j)
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_automatic :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (primitive_arrangement n q hq)
          (spheres_distinct n q hq)
          (rayLines_distinct n q hq)
  automatic_card_ge :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.karlssonClusterPairCrossingNat
            ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
              q hq).cluster i)
            ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
              q hq).cluster j) ≤
          (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (primitive_arrangement n q hq) hij
            (spheres_distinct n q hq i j hij)
            (rayLines_distinct n q hq i j hij)).card
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonCarrierCardLowerCertificate

/-- Add the canonical sorted-quad cluster witness to obtain the previous
automatic carrier-cardinality lower certificate. -/
noncomputable def toStepwiseKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonCarrierCardLowerCertificate P) :
    StepwiseKarlssonCarrierCardLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  cluster_witness := fun _ q hq =>
    ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad q hq
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  automatic_card_ge := h.automatic_card_ge
  region_increment := h.region_increment

/-- Canonical automatic carrier-cardinality lower data assemble to the
monotone local lower boundary. -/
noncomputable def toStepwisePairLocalKarlssonLowerBoundCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonCarrierCardLowerCertificate P) :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate P :=
  h.toStepwiseKarlssonCarrierCardLowerCertificate
    |>.toStepwisePairLocalKarlssonLowerBoundCertificate

end StepwiseCanonicalKarlssonCarrierCardLowerCertificate

end

end AutomaticLower
end EndToEndFormalization
end TheoremOneManuscript
end Lollipop
