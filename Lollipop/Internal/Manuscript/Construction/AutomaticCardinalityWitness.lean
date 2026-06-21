import Lollipop.Internal.Manuscript.CompleteFormalization.FiniteCarrier
import Lollipop.Internal.Manuscript.Construction.IndexedCarrier
import Lollipop.Internal.Manuscript.Construction.IndexedLowerWitness
import Lollipop.Internal.Manuscript.Construction.LowerAnchorWitness
import Lollipop.Internal.Manuscript.EndToEndFormalization.AutomaticLower

/-!
Automatic-carrier cardinality lower bounds from explicit points.

The strongest current lower boundary asks the construction to prove lower
cardinality bounds on the automatic finite carrier witnesses.  This module
turns explicit indexed carrier points into exactly those bounds.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

universe u

noncomputable section

/-- The Nat-valued canonical Karlsson lower-table entry for one pair in a
sorted quadruple, using Lean's canonical sorted-quad cluster witness. -/
def canonicalKarlssonLowerSize
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) : Nat :=
  ExplicitInputs.karlssonClusterPairCrossingNat
    ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
      q hq).cluster i)
    ((ExplicitInputs.cardinalityClusteredKarlssonTableWitnessOfSortedQuad
      q hq).cluster j)

/-- The canonical rational lower table used by the theorem-facing exact-carrier
boundary.  Increasing entries are the canonical Karlsson `4/5/7` sizes and
non-increasing entries are `0`, matching the pair-sum convention. -/
def canonicalKarlssonLowerTable
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n) :
    Fin n → Fin n → Rat :=
  fun i j =>
    if i < j then
      (canonicalKarlssonLowerSize q hq i j : Rat)
    else
      0

/-- On increasing pairs, the canonical rational lower table is the canonical
Nat-valued Karlsson size coerced to `Rat`. -/
theorem canonicalKarlssonLowerTable_eq_size
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    {i j : Fin n} (hij : i < j) :
    canonicalKarlssonLowerTable q hq i j =
      (canonicalKarlssonLowerSize q hq i j : Rat) := by
  simp [canonicalKarlssonLowerTable, hij]

/-- Non-increasing entries of the canonical rational lower table are zero. -/
theorem canonicalKarlssonLowerTable_eq_zero_of_not_lt
    {n : Nat} (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    {i j : Fin n} (hij : ¬ i < j) :
    canonicalKarlssonLowerTable q hq i j = 0 := by
  simp [canonicalKarlssonLowerTable, hij]

/-- An injective indexed family of carrier-intersection points gives the same
lower bound on the automatically produced finite carrier witness. -/
theorem indexed_points_le_arrangementPairIntersectionFinset_card
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j) :
    bound ≤
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card := by
  classical
  let S : Finset R2 := Finset.univ.image points
  have hSsub :
      S ⊆
        CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          A hij hLM hline := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
    have hp_pair : points k ∈ A.pairIntersectionSet i j := hmem k
    have hp_auto :
        points k ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            A hij hLM hline : Finset R2) : Set R2) := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          hLM hline]
        using hp_pair
    simpa using hp_auto
  have hScard : S.card = bound := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_fin bound
  rw [← hScard]
  exact Finset.card_le_card hSsub

/-- Indexed carrier points give a rational lower bound on the automatic
carrier crossing table. -/
theorem indexed_points_le_automaticCarrierCrossingTable
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j) :
    (bound : Rat) ≤
      CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    indexed_points_le_arrangementPairIntersectionFinset_card
      (hLM i j hij) (hline i j hij) points hinj hmem

/-- A shared primitive anchor gives a one-point lower bound on the automatic
finite carrier witness for that pair. -/
theorem one_le_arrangementPairIntersectionFinset_card_of_common_anchor
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    1 ≤
      (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card := by
  classical
  let p : R2 := (A.lollipop i).anchor
  let S : Finset R2 := {p}
  have hSsub :
      S ⊆
        CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          A hij hLM hline := by
    intro q hq
    have hqeq : q = p := by
      simpa [S] using hq
    subst q
    have hp_pair : p ∈ A.pairIntersectionSet i j := by
      exact arrangement_left_anchor_mem_pairIntersectionSet_of_common_anchor
        A hanchor
    have hp_auto :
        p ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            A hij hLM hline : Finset R2) : Set R2) := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          hLM hline]
        using hp_pair
    simpa using hp_auto
  have hScard : S.card = 1 := by
    simp [S]
  rw [← hScard]
  exact Finset.card_le_card hSsub

/-- A shared primitive anchor gives a rational `>= 1` lower bound on the
automatic carrier crossing table. -/
theorem one_le_automaticCarrierCrossingTable_of_common_anchor
    {n : Nat} {A : EuclideanLollipopArrangement n}
    (hLM :
      ∀ i j : Fin n, i < j →
        euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
          euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      ∀ i j : Fin n, i < j →
        euclideanRayLine (A.lollipop i) ≠
          euclideanRayLine (A.lollipop j))
    {i j : Fin n} (hij : i < j)
    (hanchor : (A.lollipop i).anchor = (A.lollipop j).anchor) :
    (1 : Rat) ≤
      CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    one_le_arrangementPairIntersectionFinset_card_of_common_anchor
      (hLM i j hij) (hline i j hij) hanchor

/-- Canonical lower certificate whose local lower data are explicit indexed
families of distinct primitive carrier-intersection points.

This is a construction-facing replacement for the raw
`automatic_card_ge` field: the construction gives the actual points, and Lean
converts them into the automatic carrier-cardinality inequalities. -/
structure StepwiseCanonicalKarlssonIndexedPointLowerCertificate
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
  lower_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        Fin (canonicalKarlssonLowerSize q hq i j) → R2
  lower_points_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (lower_points n q hq i j hij)
  lower_points_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (canonicalKarlssonLowerSize q hq i j),
          lower_points n q hq i j hij k ∈
            (primitive_arrangement n q hq).pairIntersectionSet i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- Explicit indexed lower points imply the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonIndexedPointLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  automatic_card_ge := by
    intro n q hq i j hij
    simpa [canonicalKarlssonLowerSize] using
      indexed_points_le_arrangementPairIntersectionFinset_card
        (h.spheres_distinct n q hq i j hij)
        (h.rayLines_distinct n q hq i j hij)
        (h.lower_points n q hq i j hij)
        (h.lower_points_injective n q hq i j hij)
        (h.lower_points_mem n q hq i j hij)
  region_increment := h.region_increment

end StepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- Canonical lower certificate whose local lower data are split into four
component-indexed point families.

Unlike the exact component-finset boundaries below, this lower-bound endpoint
does not ask the construction to cover the whole primitive carrier.  It only
asks for enough distinct points lying in the four component intersections.
Pairwise disjointness of the four indexed images and the component-size sum
let Lean enumerate their union as the canonical indexed lower-point family. -/
structure StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate
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
  circle_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_circle_size n q hq i j hij) → R2
  circle_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_ray_size n q hq i j hij) → R2
  ray_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_circle_size n q hq i j hij) → R2
  ray_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_ray_size n q hq i j hij) → R2
  circle_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_circle_points n q hq i j hij)
  circle_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_ray_points n q hq i j hij)
  ray_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_circle_points n q hq i j hij)
  ray_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_ray_points n q hq i j hij)
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_circle_size n q hq i j hij),
          circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_ray_size n q hq i j hij),
          circle_ray_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_circle_size n q hq i j hij),
          ray_circle_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_ray_size n q hq i j hij),
          ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  disjoint_circle_circle_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
  disjoint_circle_circle_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_circle_ray_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_ray_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_ray_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  component_size_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        circle_circle_size n q hq i j hij +
          circle_ray_size n q hq i j hij +
          ray_circle_size n q hq i j hij +
          ray_ray_size n q hq i j hij =
            canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate

/-- The finite union of the four component indexed images. -/
def lower_point_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  componentCarrierFinset
    (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
    (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
    (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
    (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))

/-- Every point in the component-indexed union lies in the primitive pair
carrier. -/
theorem lower_point_finset_mem_pairIntersectionSet
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ∀ p : R2, p ∈ h.lower_point_finset n q hq i j hij →
      p ∈ (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
  classical
  refine
    componentCarrierFinset_mem_pairIntersectionSet
      (A := h.primitive_arrangement n q hq) (i := i) (j := j)
      (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
      (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
      (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
      (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))
      ?_ ?_ ?_ ?_
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_circle_size n q hq i j hij),
            h.circle_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_circle_mem n q hq i j hij k
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_ray_size n q hq i j hij),
            h.circle_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_ray_mem n q hq i j hij k
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_circle_size n q hq i j hij),
            h.ray_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_circle_mem n q hq i j hij k
  · intro p hp
    rcases
        (by
          simpa [indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_ray_size n q hq i j hij),
            h.ray_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_ray_mem n q hq i j hij k

/-- The component-indexed union has exactly the canonical lower size. -/
theorem lower_point_finset_card
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    (h.lower_point_finset n q hq i j hij).card =
      canonicalKarlssonLowerSize q hq i j := by
  unfold lower_point_finset
  calc
    (componentCarrierFinset
        (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
        (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
        (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
        (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))).card =
        h.circle_circle_size n q hq i j hij +
          h.circle_ray_size n q hq i j hij +
          h.ray_circle_size n q hq i j hij +
          h.ray_ray_size n q hq i j hij := by
      exact
        componentCarrierFinset_card_eq_of_disjoint
          (indexedCarrierFinset (h.circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (h.circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (h.ray_circle_points n q hq i j hij))
          (indexedCarrierFinset (h.ray_ray_points n q hq i j hij))
          (h.disjoint_circle_circle_circle_ray n q hq i j hij)
          (h.disjoint_circle_circle_ray_circle n q hq i j hij)
          (h.disjoint_circle_circle_ray_ray n q hq i j hij)
          (h.disjoint_circle_ray_ray_circle n q hq i j hij)
          (h.disjoint_circle_ray_ray_ray n q hq i j hij)
          (h.disjoint_ray_circle_ray_ray n q hq i j hij)
          (indexedCarrierFinset_card
            (h.circle_circle_points n q hq i j hij)
            (h.circle_circle_injective n q hq i j hij))
          (indexedCarrierFinset_card
            (h.circle_ray_points n q hq i j hij)
            (h.circle_ray_injective n q hq i j hij))
          (indexedCarrierFinset_card
            (h.ray_circle_points n q hq i j hij)
            (h.ray_circle_injective n q hq i j hij))
          (indexedCarrierFinset_card
            (h.ray_ray_points n q hq i j hij)
            (h.ray_ray_injective n q hq i j hij))
    _ = canonicalKarlssonLowerSize q hq i j := by
      exact h.component_size_sum n q hq i j hij

/-- Enumerate the component-indexed lower-point union by the canonical lower
size. -/
noncomputable def lower_points
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) :
    Fin (canonicalKarlssonLowerSize q hq i j) → R2 :=
  fun k =>
    (((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
      (h.lower_point_finset_card hij)).symm k : R2)

/-- The canonical enumeration of the component-indexed union is injective. -/
theorem lower_points_injective
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    Function.Injective (h.lower_points n q hq i j hij) := by
  intro a b hab
  have hsub :
      ((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
          (h.lower_point_finset_card hij)).symm a =
        ((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
          (h.lower_point_finset_card hij)).symm b := by
    exact Subtype.ext hab
  exact
    ((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
      (h.lower_point_finset_card hij)).symm.injective hsub

/-- The canonical enumeration of the component-indexed union consists of
primitive carrier-intersection points. -/
theorem lower_points_mem
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j)
    (k : Fin (canonicalKarlssonLowerSize q hq i j)) :
    h.lower_points n q hq i j hij k ∈
      (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
  have hp :
      h.lower_points n q hq i j hij k ∈
        h.lower_point_finset n q hq i j hij := by
    dsimp [lower_points]
    exact
      (((h.lower_point_finset n q hq i j hij).equivFinOfCardEq
        (h.lower_point_finset_card hij)).symm k).property
  exact h.lower_point_finset_mem_pairIntersectionSet hij
    (h.lower_points n q hq i j hij k) hp

/-- Component-indexed lower points are a special case of the canonical
indexed lower-point boundary. -/
noncomputable def toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P) :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := h.pair_cross_eq_automatic
  lower_points := h.lower_points
  lower_points_injective := by
    intro n q hq i j hij
    exact h.lower_points_injective hij
  lower_points_mem := by
    intro n q hq i j hij k
    exact h.lower_points_mem hij k
  region_increment := h.region_increment

/-- Component-indexed lower points give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonComponentIndexedPointLowerCertificate

/-- Canonical lower certificate whose local data are exact indexed
enumerations of the whole primitive pair carrier, of the canonical
Nat-valued Karlsson `4/5/7` sizes.

Compared with `StepwiseCanonicalKarlssonIndexedPointLowerCertificate`, this
boundary asks the coordinate construction to prove that the indexed points are
not merely lower witnesses but enumerate the entire primitive carrier.  Lean
then derives membership in the carrier and equality with the automatic
finite-carrier table. -/
structure StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
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
  pair_cross_eq_size :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        pair_cross n (arrangement n q hq) i j =
          (canonicalKarlssonLowerSize q hq i j : Rat)
  pair_cross_eq_zero_of_not_lt :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ¬ i < j →
        pair_cross n (arrangement n q hq) i j = 0
  carrier_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        Fin (canonicalKarlssonLowerSize q hq i j) → R2
  carrier_points_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (carrier_points n q hq i j hij)
  carrier_points_spec :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ((indexedCarrierFinset
          (carrier_points n q hq i j hij) : Finset R2) : Set R2) =
          (primitive_arrangement n q hq).pairIntersectionSet i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical exact indexed carrier lower certificate whose pair table is
given by one equality to the canonical rational Karlsson table.

This is a construction-facing variant of
`StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate`: instead of
separate increasing-entry and non-increasing-entry pair-table fields, the
construction proves a single pointwise table equality. -/
structure StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate
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
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  carrier_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j,
        Fin (canonicalKarlssonLowerSize q hq i j) → R2
  carrier_points_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (carrier_points n q hq i j hij)
  carrier_points_spec :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ((indexedCarrierFinset
          (carrier_points n q hq i j hij) : Finset R2) : Set R2) =
          (primitive_arrangement n q hq).pairIntersectionSet i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical exact carrier lower certificate whose local data are finite
carrier sets rather than indexed enumerations.

For each increasing pair, the construction supplies the finite primitive
carrier itself, proves its coercion is exactly the pair carrier, and computes
its cardinality as the canonical Nat-valued Karlsson `4/5/7` size.  This
boundary is often closer to component-by-component coordinate calculations
than an explicit `Fin k -> R2` enumeration. -/
structure StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
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
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  carrier_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  carrier_finset_spec :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ((carrier_finset n q hq i j hij : Finset R2) : Set R2) =
          (primitive_arrangement n q hq).pairIntersectionSet i j
  carrier_finset_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (carrier_finset n q hq i j hij).card =
          canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical finite-carrier lower certificate whose exact carrier equality is
proved from membership plus exhaustive component coverage.

For each increasing pair, the construction supplies a finite primitive carrier
set, proves every listed point is in the pair carrier, covers each of the four
circle/ray component cases, and computes the cardinality as the canonical
Nat-valued Karlsson `4/5/7` size.  Lean derives the exact carrier equality
needed by `StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate`. -/
structure StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
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
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  carrier_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  carrier_finset_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ p : R2, p ∈ carrier_finset n q hq i j hij →
          p ∈ (primitive_arrangement n q hq).pairIntersectionSet i j
  carrier_finset_covers_circle_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_covers_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_covers_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_covers_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ carrier_finset n q hq i j hij
  carrier_finset_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (carrier_finset n q hq i j hij).card =
          canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical finite-carrier lower certificate whose data are separated by
the four primitive circle/ray components.

For each increasing pair, the construction supplies four component finsets,
proves membership and coverage for the corresponding circle-circle,
circle-ray, ray-circle, and ray-ray components, and computes the cardinality
of their union as the canonical Nat-valued Karlsson `4/5/7` size.  Lean
assembles the carrier finset and derives the exact carrier equality. -/
structure StepwiseCanonicalKarlssonComponentFinsetLowerCertificate
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
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  circle_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_circle_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_ray_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_circle_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_ray_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  circle_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ circle_circle_finset n q hq i j hij
  circle_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ circle_ray_finset n q hq i j hij
  ray_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ ray_circle_finset n q hq i j hij
  ray_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ ray_ray_finset n q hq i j hij
  carrier_finset_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (componentCarrierFinset
          (circle_circle_finset n q hq i j hij)
          (circle_ray_finset n q hq i j hij)
          (ray_circle_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)).card =
          canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical component-finset lower certificate where Lean derives the union
cardinality from pairwise disjointness and individual component counts. -/
structure StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
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
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  circle_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_circle_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  ray_ray_finset :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Finset R2
  circle_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_circle_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circle_ray_finset n q hq i j hij →
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
              ((primitive_arrangement n q hq).lollipop i).radius ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_circle_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
              ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ ray_ray_finset n q hq i j hij →
          p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
              ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
          p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
              ((primitive_arrangement n q hq).lollipop j).rayDirection
  circle_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ circle_circle_finset n q hq i j hij
  circle_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ circle_ray_finset n q hq i j hij
  ray_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          p ∈ ray_circle_finset n q hq i j hij
  ray_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          p ∈ ray_ray_finset n q hq i j hij
  disjoint_circle_circle_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_circle_finset n q hq i j hij)
          (circle_ray_finset n q hq i j hij)
  disjoint_circle_circle_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_circle_finset n q hq i j hij)
          (ray_circle_finset n q hq i j hij)
  disjoint_circle_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_circle_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)
  disjoint_circle_ray_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_ray_finset n q hq i j hij)
          (ray_circle_finset n q hq i j hij)
  disjoint_circle_ray_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (circle_ray_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)
  disjoint_ray_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (ray_circle_finset n q hq i j hij)
          (ray_ray_finset n q hq i j hij)
  circle_circle_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (circle_circle_finset n q hq i j hij).card =
          circle_circle_size n q hq i j hij
  circle_ray_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (circle_ray_finset n q hq i j hij).card =
          circle_ray_size n q hq i j hij
  ray_circle_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (ray_circle_finset n q hq i j hij).card =
          ray_circle_size n q hq i j hij
  ray_ray_card :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        (ray_ray_finset n q hq i j hij).card =
          ray_ray_size n q hq i j hij
  component_size_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        circle_circle_size n q hq i j hij +
          circle_ray_size n q hq i j hij +
          ray_circle_size n q hq i j hij +
          ray_ray_size n q hq i j hij =
            canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

/-- Canonical lower certificate where each component finset is generated from
an injective indexed list of concrete component points.

This is the coordinate-facing refinement of the disjoint component boundary:
the construction enumerates the four circle/ray components separately, proves
membership and coverage for each component, proves that the four images are
pairwise disjoint, and supplies the component-size sum.  Lean turns the
indexed images into finite component sets and derives all component
cardinality fields. -/
structure StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
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
  pair_cross_eq_canonical_table :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      pair_cross n (arrangement n q hq) =
        canonicalKarlssonLowerTable q hq
  circle_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_circle_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  ray_ray_size :
    ∀ (n : Nat) (q : QuadVec n) (_hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ _hij : i < j, Nat
  circle_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_circle_size n q hq i j hij) → R2
  circle_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (circle_ray_size n q hq i j hij) → R2
  ray_circle_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_circle_size n q hq i j hij) → R2
  ray_ray_points :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (ray_ray_size n q hq i j hij) → R2
  circle_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_circle_points n q hq i j hij)
  circle_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (circle_ray_points n q hq i j hij)
  ray_circle_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_circle_points n q hq i j hij)
  ray_ray_injective :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (ray_ray_points n q hq i j hij)
  circle_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_circle_size n q hq i j hij),
          circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  circle_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (circle_ray_size n q hq i j hij),
          circle_ray_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop i).center
                ((primitive_arrangement n q hq).lollipop i).radius ∧
            circle_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  ray_circle_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_circle_size n q hq i j hij),
          ray_circle_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_circle_points n q hq i j hij k ∈
              circleSet ((primitive_arrangement n q hq).lollipop j).center
                ((primitive_arrangement n q hq).lollipop j).radius
  ray_ray_mem :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ∀ k : Fin (ray_ray_size n q hq i j hij),
          ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop i).anchor
                ((primitive_arrangement n q hq).lollipop i).rayDirection ∧
            ray_ray_points n q hq i j hij k ∈
              raySet ((primitive_arrangement n q hq).lollipop j).anchor
                ((primitive_arrangement n q hq).lollipop j).rayDirection
  circle_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          ∃ k : Fin (circle_circle_size n q hq i j hij),
            circle_circle_points n q hq i j hij k = p
  circle_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop i).center
            ((primitive_arrangement n q hq).lollipop i).radius →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          ∃ k : Fin (circle_ray_size n q hq i j hij),
            circle_ray_points n q hq i j hij k = p
  ray_circle_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ circleSet ((primitive_arrangement n q hq).lollipop j).center
            ((primitive_arrangement n q hq).lollipop j).radius →
          ∃ k : Fin (ray_circle_size n q hq i j hij),
            ray_circle_points n q hq i j hij k = p
  ray_ray_cover :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j, ∀ p : R2,
        p ∈ raySet ((primitive_arrangement n q hq).lollipop i).anchor
            ((primitive_arrangement n q hq).lollipop i).rayDirection →
        p ∈ raySet ((primitive_arrangement n q hq).lollipop j).anchor
            ((primitive_arrangement n q hq).lollipop j).rayDirection →
          ∃ k : Fin (ray_ray_size n q hq i j hij),
            ray_ray_points n q hq i j hij k = p
  disjoint_circle_circle_circle_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
  disjoint_circle_circle_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_circle_ray_ray_circle :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
  disjoint_circle_ray_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (circle_ray_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  disjoint_ray_circle_ray_ray :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        Disjoint
          (indexedCarrierFinset (ray_circle_points n q hq i j hij))
          (indexedCarrierFinset (ray_ray_points n q hq i j hij))
  component_size_sum :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        circle_circle_size n q hq i j hij +
          circle_ray_size n q hq i j hij +
          ray_circle_size n q hq i j hij +
          ray_ray_size n q hq i j hij =
            canonicalKarlssonLowerSize q hq i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate

/-- Exact indexed carrier lower data are a special case of the indexed
lower-point certificate. -/
noncomputable def toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate P) :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := by
    intro n q hq
    funext i j
    by_cases hij : i < j
    · calc
        h.pair_cross n (h.arrangement n q hq) i j =
            (canonicalKarlssonLowerSize q hq i j : Rat) := by
          exact h.pair_cross_eq_size n q hq i j hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          exact
            (automaticCarrierCrossingTable_eq_of_indexedCarrier
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq)
              hij
              (h.carrier_points n q hq i j hij)
              (h.carrier_points_injective n q hq i j hij)
              (h.carrier_points_spec n q hq i j hij)).symm
    · calc
        h.pair_cross n (h.arrangement n q hq) i j = 0 := by
          exact h.pair_cross_eq_zero_of_not_lt n q hq i j hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          simp [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable,
            hij]
  lower_points := h.carrier_points
  lower_points_injective := h.carrier_points_injective
  lower_points_mem := by
    intro n q hq i j hij k
    exact
      indexedCarrier_mem_pairIntersectionSet_of_spec
        (h.carrier_points n q hq i j hij)
        (h.carrier_points_spec n q hq i j hij) k
  region_increment := h.region_increment

/-- Exact indexed carrier lower data imply the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate

namespace StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate

/-- A one-equation canonical-table exact carrier certificate implies the
existing exact indexed carrier lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate P) :
    StepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_size := by
    intro n q hq i j hij
    rw [h.pair_cross_eq_canonical_table n q hq]
    exact canonicalKarlssonLowerTable_eq_size q hq hij
  pair_cross_eq_zero_of_not_lt := by
    intro n q hq i j hij
    rw [h.pair_cross_eq_canonical_table n q hq]
    exact canonicalKarlssonLowerTable_eq_zero_of_not_lt q hq hij
  carrier_points := h.carrier_points
  carrier_points_injective := h.carrier_points_injective
  carrier_points_spec := h.carrier_points_spec
  region_increment := h.region_increment

/-- A one-equation canonical-table exact carrier certificate also gives the
indexed lower-point certificate. -/
noncomputable def toStepwiseCanonicalKarlssonIndexedPointLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate P) :
    StepwiseCanonicalKarlssonIndexedPointLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    |>.toStepwiseCanonicalKarlssonIndexedPointLowerCertificate

/-- A one-equation canonical-table exact carrier certificate gives the
canonical automatic carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonExactIndexedCarrierLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonTableExactIndexedCarrierLowerCertificate

namespace StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- The automatic finite carrier produced from generic noncoincidence is the
same finset as the construction-supplied exact carrier. -/
theorem automaticCarrierFinset_eq_carrierFinset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        (h.primitive_arrangement n q hq) hij
        (h.spheres_distinct n q hq i j hij)
        (h.rayLines_distinct n q hq i j hij) =
      h.carrier_finset n q hq i j hij := by
  classical
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hp_set :
        p ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (h.primitive_arrangement n q hq) hij
            (h.spheres_distinct n q hq i j hij)
            (h.rayLines_distinct n q hq i j hij) : Finset R2) : Set R2) := by
      simpa using hp
    have hp_pair :
        p ∈ (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)]
        using hp_set
    have hp_carrier :
        p ∈ ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) := by
      simpa [h.carrier_finset_spec n q hq i j hij] using hp_pair
    simpa using hp_carrier
  · intro hp
    have hp_carrier :
        p ∈ ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) := by
      simpa using hp
    have hp_pair :
        p ∈ (h.primitive_arrangement n q hq).pairIntersectionSet i j := by
      simpa [h.carrier_finset_spec n q hq i j hij] using hp_carrier
    have hp_auto :
        p ∈
          ((CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
            (h.primitive_arrangement n q hq) hij
            (h.spheres_distinct n q hq i j hij)
            (h.rayLines_distinct n q hq i j hij) : Finset R2) : Set R2) := by
      simpa
        [CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)]
        using hp_pair
    simpa using hp_auto

/-- Finset-exact carrier lower data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_automatic := by
    intro n q hq
    funext i j
    by_cases hij : i < j
    · calc
        h.pair_cross n (h.arrangement n q hq) i j =
            canonicalKarlssonLowerTable q hq i j := by
          rw [h.pair_cross_eq_canonical_table n q hq]
        _ = (canonicalKarlssonLowerSize q hq i j : Rat) := by
          exact canonicalKarlssonLowerTable_eq_size q hq hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
            (h.spheres_distinct n q hq) (h.rayLines_distinct n q hq) hij]
          rw [h.automaticCarrierFinset_eq_carrierFinset hij]
          exact_mod_cast (h.carrier_finset_card n q hq i j hij).symm
    · calc
        h.pair_cross n (h.arrangement n q hq) i j =
            canonicalKarlssonLowerTable q hq i j := by
          rw [h.pair_cross_eq_canonical_table n q hq]
        _ = 0 := canonicalKarlssonLowerTable_eq_zero_of_not_lt q hq hij
        _ =
            CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
              (h.primitive_arrangement n q hq)
              (h.spheres_distinct n q hq)
              (h.rayLines_distinct n q hq) i j := by
          simp [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable,
            hij]
  automatic_card_ge := by
    intro n q hq i j hij
    have hcard :
        (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
          (h.primitive_arrangement n q hq) hij
          (h.spheres_distinct n q hq i j hij)
          (h.rayLines_distinct n q hq i j hij)).card =
          canonicalKarlssonLowerSize q hq i j := by
      rw [h.automaticCarrierFinset_eq_carrierFinset hij]
      exact h.carrier_finset_card n q hq i j hij
    simpa [canonicalKarlssonLowerSize] using le_of_eq hcard.symm
  region_increment := h.region_increment

end StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

namespace StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

/-- Component coverage supplies the exact carrier equality required by the
finset-exact lower boundary. -/
theorem carrier_finset_spec
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) =
      (h.primitive_arrangement n q hq).pairIntersectionSet i j :=
  carrierFinset_spec_of_component_covers
    (A := h.primitive_arrangement n q hq) (i := i) (j := j)
    (h.carrier_finset n q hq i j hij)
    (h.carrier_finset_mem n q hq i j hij)
    (h.carrier_finset_covers_circle_circle n q hq i j hij)
    (h.carrier_finset_covers_circle_ray n q hq i j hij)
    (h.carrier_finset_covers_ray_circle n q hq i j hij)
    (h.carrier_finset_covers_ray_ray n q hq i j hij)

/-- Component-covered finite carrier data are a special case of finset-exact
carrier lower data. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  carrier_finset := h.carrier_finset
  carrier_finset_spec := by
    intro n q hq i j hij
    exact h.carrier_finset_spec hij
  carrier_finset_card := h.carrier_finset_card
  region_increment := h.region_increment

/-- Component-covered finite carrier data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

namespace StepwiseCanonicalKarlssonComponentFinsetLowerCertificate

/-- The carrier finset assembled from the four construction-supplied component
finsets. -/
def carrier_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  componentCarrierFinset
    (h.circle_circle_finset n q hq i j hij)
    (h.circle_ray_finset n q hq i j hij)
    (h.ray_circle_finset n q hq i j hij)
    (h.ray_ray_finset n q hq i j hij)

/-- The component finsets assemble to the full primitive pair carrier. -/
theorem carrier_finset_spec
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    ((h.carrier_finset n q hq i j hij : Finset R2) : Set R2) =
      (h.primitive_arrangement n q hq).pairIntersectionSet i j :=
  componentCarrierFinset_spec_of_component_covers
    (A := h.primitive_arrangement n q hq) (i := i) (j := j)
    (h.circle_circle_finset n q hq i j hij)
    (h.circle_ray_finset n q hq i j hij)
    (h.ray_circle_finset n q hq i j hij)
    (h.ray_ray_finset n q hq i j hij)
    (h.circle_circle_mem n q hq i j hij)
    (h.circle_ray_mem n q hq i j hij)
    (h.ray_circle_mem n q hq i j hij)
    (h.ray_ray_mem n q hq i j hij)
    (h.circle_circle_cover n q hq i j hij)
    (h.circle_ray_cover n q hq i j hij)
    (h.ray_circle_cover n q hq i j hij)
    (h.ray_ray_cover n q hq i j hij)

/-- Component-separated finite carrier data are a special case of the
component-covered finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  carrier_finset := h.carrier_finset
  carrier_finset_mem := by
    intro n q hq i j hij p hp
    exact
      componentCarrierFinset_mem_pairIntersectionSet
        (A := h.primitive_arrangement n q hq) (i := i) (j := j)
        (h.circle_circle_finset n q hq i j hij)
        (h.circle_ray_finset n q hq i j hij)
        (h.ray_circle_finset n q hq i j hij)
        (h.ray_ray_finset n q hq i j hij)
        (h.circle_circle_mem n q hq i j hij)
        (h.circle_ray_mem n q hq i j hij)
        (h.ray_circle_mem n q hq i j hij)
        (h.ray_ray_mem n q hq i j hij) p hp
  carrier_finset_covers_circle_circle := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.circle_circle_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_covers_circle_ray := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.circle_ray_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_covers_ray_circle := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.ray_circle_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_covers_ray_ray := by
    intro n q hq i j hij p hp_i hp_j
    simp [carrier_finset, componentCarrierFinset,
      h.ray_ray_cover n q hq i j hij p hp_i hp_j]
  carrier_finset_card := h.carrier_finset_card
  region_increment := h.region_increment

/-- Component-separated finite carrier data are a special case of the
finset-exact carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- Component-separated finite carrier data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonComponentFinsetLowerCertificate

namespace StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate

/-- The carrier finset assembled from the four disjoint construction-supplied
component finsets. -/
def carrier_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  componentCarrierFinset
    (h.circle_circle_finset n q hq i j hij)
    (h.circle_ray_finset n q hq i j hij)
    (h.ray_circle_finset n q hq i j hij)
    (h.ray_ray_finset n q hq i j hij)

/-- Pairwise disjointness and the four component cardinalities compute the
canonical lower carrier size. -/
theorem carrier_finset_card
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P)
    {n : Nat} {q : QuadVec n} {hq : q ∈ sortedQuadVecs n}
    {i j : Fin n} (hij : i < j) :
    (h.carrier_finset n q hq i j hij).card =
      canonicalKarlssonLowerSize q hq i j := by
  unfold carrier_finset
  calc
    (componentCarrierFinset
        (h.circle_circle_finset n q hq i j hij)
        (h.circle_ray_finset n q hq i j hij)
        (h.ray_circle_finset n q hq i j hij)
        (h.ray_ray_finset n q hq i j hij)).card =
        h.circle_circle_size n q hq i j hij +
          h.circle_ray_size n q hq i j hij +
          h.ray_circle_size n q hq i j hij +
          h.ray_ray_size n q hq i j hij := by
      exact
        componentCarrierFinset_card_eq_of_disjoint
          (h.circle_circle_finset n q hq i j hij)
          (h.circle_ray_finset n q hq i j hij)
          (h.ray_circle_finset n q hq i j hij)
          (h.ray_ray_finset n q hq i j hij)
          (h.disjoint_circle_circle_circle_ray n q hq i j hij)
          (h.disjoint_circle_circle_ray_circle n q hq i j hij)
          (h.disjoint_circle_circle_ray_ray n q hq i j hij)
          (h.disjoint_circle_ray_ray_circle n q hq i j hij)
          (h.disjoint_circle_ray_ray_ray n q hq i j hij)
          (h.disjoint_ray_circle_ray_ray n q hq i j hij)
          (h.circle_circle_card n q hq i j hij)
          (h.circle_ray_card n q hq i j hij)
          (h.ray_circle_card n q hq i j hij)
          (h.ray_ray_card n q hq i j hij)
    _ = canonicalKarlssonLowerSize q hq i j := by
      exact h.component_size_sum n q hq i j hij

/-- Disjoint component-count lower data are a special case of the
component-separated finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  circle_circle_finset := h.circle_circle_finset
  circle_ray_finset := h.circle_ray_finset
  ray_circle_finset := h.ray_circle_finset
  ray_ray_finset := h.ray_ray_finset
  circle_circle_mem := h.circle_circle_mem
  circle_ray_mem := h.circle_ray_mem
  ray_circle_mem := h.ray_circle_mem
  ray_ray_mem := h.ray_ray_mem
  circle_circle_cover := h.circle_circle_cover
  circle_ray_cover := h.circle_ray_cover
  ray_circle_cover := h.ray_circle_cover
  ray_ray_cover := h.ray_ray_cover
  carrier_finset_card := by
    intro n q hq i j hij
    exact h.carrier_finset_card hij
  region_increment := h.region_increment

/-- Disjoint component-count lower data also give the component-covered
finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

/-- Disjoint component-count lower data also give the finset-exact carrier
lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- Disjoint component-count lower data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate

namespace StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate

/-- The circle-circle component finset generated by the indexed component
points. -/
def circle_circle_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.circle_circle_points n q hq i j hij)

/-- The circle-ray component finset generated by the indexed component
points. -/
def circle_ray_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.circle_ray_points n q hq i j hij)

/-- The ray-circle component finset generated by the indexed component
points. -/
def ray_circle_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.ray_circle_points n q hq i j hij)

/-- The ray-ray component finset generated by the indexed component points. -/
def ray_ray_finset
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P)
    (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n)
    (i j : Fin n) (hij : i < j) : Finset R2 :=
  indexedCarrierFinset (h.ray_ray_points n q hq i j hij)

/-- Indexed disjoint component data are a special case of the disjoint
component-finset lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate P where
  arrangement := h.arrangement
  primitive_arrangement := h.primitive_arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  pair_cross := h.pair_cross
  pair_cross_eq_canonical_table := h.pair_cross_eq_canonical_table
  circle_circle_finset := h.circle_circle_finset
  circle_ray_finset := h.circle_ray_finset
  ray_circle_finset := h.ray_circle_finset
  ray_ray_finset := h.ray_ray_finset
  circle_circle_size := h.circle_circle_size
  circle_ray_size := h.circle_ray_size
  ray_circle_size := h.ray_circle_size
  ray_ray_size := h.ray_ray_size
  circle_circle_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [circle_circle_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_circle_size n q hq i j hij),
            h.circle_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_circle_mem n q hq i j hij k
  circle_ray_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [circle_ray_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.circle_ray_size n q hq i j hij),
            h.circle_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.circle_ray_mem n q hq i j hij k
  ray_circle_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [ray_circle_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_circle_size n q hq i j hij),
            h.ray_circle_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_circle_mem n q hq i j hij k
  ray_ray_mem := by
    intro n q hq i j hij p hp
    rcases
        (by
          simpa [ray_ray_finset, indexedCarrierFinset] using hp :
          ∃ k : Fin (h.ray_ray_size n q hq i j hij),
            h.ray_ray_points n q hq i j hij k = p) with
      ⟨k, rfl⟩
    exact h.ray_ray_mem n q hq i j hij k
  circle_circle_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.circle_circle_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [circle_circle_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  circle_ray_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.circle_ray_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [circle_ray_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  ray_circle_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.ray_circle_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [ray_circle_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  ray_ray_cover := by
    intro n q hq i j hij p hp_i hp_j
    rcases h.ray_ray_cover n q hq i j hij p hp_i hp_j with ⟨k, hk⟩
    exact
      (by
        simpa [ray_ray_finset, indexedCarrierFinset] using
          (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩))
  disjoint_circle_circle_circle_ray := by
    intro n q hq i j hij
    simpa [circle_circle_finset, circle_ray_finset] using
      h.disjoint_circle_circle_circle_ray n q hq i j hij
  disjoint_circle_circle_ray_circle := by
    intro n q hq i j hij
    simpa [circle_circle_finset, ray_circle_finset] using
      h.disjoint_circle_circle_ray_circle n q hq i j hij
  disjoint_circle_circle_ray_ray := by
    intro n q hq i j hij
    simpa [circle_circle_finset, ray_ray_finset] using
      h.disjoint_circle_circle_ray_ray n q hq i j hij
  disjoint_circle_ray_ray_circle := by
    intro n q hq i j hij
    simpa [circle_ray_finset, ray_circle_finset] using
      h.disjoint_circle_ray_ray_circle n q hq i j hij
  disjoint_circle_ray_ray_ray := by
    intro n q hq i j hij
    simpa [circle_ray_finset, ray_ray_finset] using
      h.disjoint_circle_ray_ray_ray n q hq i j hij
  disjoint_ray_circle_ray_ray := by
    intro n q hq i j hij
    simpa [ray_circle_finset, ray_ray_finset] using
      h.disjoint_ray_circle_ray_ray n q hq i j hij
  circle_circle_card := by
    intro n q hq i j hij
    simpa [circle_circle_finset] using
      indexedCarrierFinset_card
        (h.circle_circle_points n q hq i j hij)
        (h.circle_circle_injective n q hq i j hij)
  circle_ray_card := by
    intro n q hq i j hij
    simpa [circle_ray_finset] using
      indexedCarrierFinset_card
        (h.circle_ray_points n q hq i j hij)
        (h.circle_ray_injective n q hq i j hij)
  ray_circle_card := by
    intro n q hq i j hij
    simpa [ray_circle_finset] using
      indexedCarrierFinset_card
        (h.ray_circle_points n q hq i j hij)
        (h.ray_circle_injective n q hq i j hij)
  ray_ray_card := by
    intro n q hq i j hij
    simpa [ray_ray_finset] using
      indexedCarrierFinset_card
        (h.ray_ray_points n q hq i j hij)
        (h.ray_ray_injective n q hq i j hij)
  component_size_sum := h.component_size_sum
  region_increment := h.region_increment

/-- Indexed disjoint component data also give the component-separated
finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonComponentFinsetLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonComponentFinsetLowerCertificate

/-- Indexed disjoint component data also give the component-covered
finite-carrier lower boundary. -/
noncomputable def toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonComponentCoveredFinsetLowerCertificate

/-- Indexed disjoint component data also give the finset-exact carrier lower
boundary. -/
noncomputable def toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    StepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonFinsetExactCarrierLowerCertificate

/-- Indexed disjoint component data give the canonical automatic
carrier-cardinality lower certificate. -/
noncomputable def toStepwiseCanonicalKarlssonCarrierCardLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h :
      StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate
        P) :
    EndToEndFormalization.AutomaticLower.StepwiseCanonicalKarlssonCarrierCardLowerCertificate
      P :=
  h.toStepwiseCanonicalKarlssonDisjointComponentFinsetLowerCertificate
    |>.toStepwiseCanonicalKarlssonCarrierCardLowerCertificate

end StepwiseCanonicalKarlssonIndexedDisjointComponentFinsetLowerCertificate

end

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop
