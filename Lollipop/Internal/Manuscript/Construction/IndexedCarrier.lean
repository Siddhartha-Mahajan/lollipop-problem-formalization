import Lollipop.Internal.Manuscript.CompleteFormalization.FiniteCarrier
import Lollipop.Internal.Manuscript.Construction.IndexedLowerWitness

/-!
Indexed exact carrier certificates.

Concrete coordinate proofs often enumerate a pair carrier by an indexed family
`Fin k -> R2`.  The theorem stack, however, consumes `Finset` carrier
certificates.  This module records the reusable conversion from an injective
indexed enumeration whose image is exactly the primitive carrier intersection
to the local and pairwise carrier-crossing certificates used elsewhere.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace ConstructionFormalization

open PrimitiveGeometry

noncomputable section

/-- The finite set underlying an indexed carrier enumeration. -/
def indexedCarrierFinset
    {bound : Nat} (points : Fin bound → R2) : Finset R2 :=
  Finset.univ.image points

/-- An injective indexed carrier enumeration has the expected cardinality. -/
theorem indexedCarrierFinset_card
    {bound : Nat} (points : Fin bound → R2)
    (hinj : Function.Injective points) :
    (indexedCarrierFinset points).card = bound := by
  dsimp [indexedCarrierFinset]
  rw [Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin bound

/-- An indexed carrier image is exactly a target pair carrier once every
indexed point lies in the carrier and every carrier point is covered by some
index. -/
theorem indexedCarrierFinset_spec_of_mem_and_cover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (points : Fin bound → R2)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p) :
    ((indexedCarrierFinset points : Finset R2) : Set R2) =
      A.pairIntersectionSet i j := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨k, _hk, rfl⟩
    exact hmem k
  · intro hp
    rcases hcover p hp with ⟨k, hk⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩

/-- A component-wise coverage proof is enough to identify an indexed carrier
image with the whole primitive pair carrier. -/
theorem indexedCarrierFinset_spec_of_component_covers
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (points : Fin bound → R2)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcc :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        ∃ k : Fin bound, points k = p)
    (hcr :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        ∃ k : Fin bound, points k = p)
    (hrc :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        ∃ k : Fin bound, points k = p)
    (hrr :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        ∃ k : Fin bound, points k = p) :
    ((indexedCarrierFinset points : Finset R2) : Set R2) =
      A.pairIntersectionSet i j := by
  refine indexedCarrierFinset_spec_of_mem_and_cover points hmem ?_
  intro p hp
  rcases (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
      A (i := i) (j := j) (p := p)).1 hp with hccp | hcrp | hrcp | hrrp
  · exact hcc p hccp.1 hccp.2
  · exact hcr p hcrp.1 hcrp.2
  · exact hrc p hrcp.1 hrcp.2
  · exact hrr p hrrp.1 hrrp.2

/-- A finite carrier set is exactly a target pair carrier once every point in
the finite set lies in the carrier and every carrier point is covered by the
finite set. -/
theorem carrierFinset_spec_of_mem_and_cover
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (carrier : Finset R2)
    (hmem : ∀ p : R2, p ∈ carrier → p ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j → p ∈ carrier) :
    ((carrier : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
  ext p
  constructor
  · intro hp
    exact hmem p (by simpa using hp)
  · intro hp
    simpa using hcover p hp

/-- The finite carrier set assembled from the four primitive circle/ray
components of one pair. -/
def componentCarrierFinset
    (circleCircle circleRay rayCircle rayRay : Finset R2) : Finset R2 :=
  circleCircle ∪ circleRay ∪ rayCircle ∪ rayRay

/-- If each component finset contains only points in its named component, then
their union contains only points in the primitive pair carrier. -/
theorem componentCarrierFinset_mem_pairIntersectionSet
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (circleCircle circleRay rayCircle rayRay : Finset R2)
    (hcc :
      ∀ p : R2, p ∈ circleCircle →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr :
      ∀ p : R2, p ∈ circleRay →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc :
      ∀ p : R2, p ∈ rayCircle →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr :
      ∀ p : R2, p ∈ rayRay →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection) :
    ∀ p : R2, p ∈ componentCarrierFinset
        circleCircle circleRay rayCircle rayRay →
      p ∈ A.pairIntersectionSet i j := by
  classical
  intro p hp
  simp [componentCarrierFinset] at hp
  rcases hp with hpcc | hpcr | hprc | hprr
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inl (hcc p hpcc))
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inr (Or.inl (hcr p hpcr)))
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inr (Or.inr (Or.inl (hrc p hprc))))
  · exact
      (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
        A (i := i) (j := j) (p := p)).2
        (Or.inr (Or.inr (Or.inr (hrr p hprr))))

/-- Component finsets identify the whole primitive pair carrier once they
contain only points of their component and cover every point in that
component. -/
theorem componentCarrierFinset_spec_of_component_covers
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (circleCircle circleRay rayCircle rayRay : Finset R2)
    (hcc_mem :
      ∀ p : R2, p ∈ circleCircle →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hcr_mem :
      ∀ p : R2, p ∈ circleRay →
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hrc_mem :
      ∀ p : R2, p ∈ rayCircle →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius)
    (hrr_mem :
      ∀ p : R2, p ∈ rayRay →
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection)
    (hcc_cover :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ circleCircle)
    (hcr_cover :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ circleRay)
    (hrc_cover :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ rayCircle)
    (hrr_cover :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ rayRay) :
    ((componentCarrierFinset
      circleCircle circleRay rayCircle rayRay : Finset R2) : Set R2) =
      A.pairIntersectionSet i j := by
  refine carrierFinset_spec_of_mem_and_cover
    (componentCarrierFinset circleCircle circleRay rayCircle rayRay)
    (componentCarrierFinset_mem_pairIntersectionSet
      circleCircle circleRay rayCircle rayRay
      hcc_mem hcr_mem hrc_mem hrr_mem)
    ?_
  intro p hp
  rcases (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
      A (i := i) (j := j) (p := p)).1 hp with hccp | hcrp | hrcp | hrrp
  · simp [componentCarrierFinset, hcc_cover p hccp.1 hccp.2]
  · simp [componentCarrierFinset, hcr_cover p hcrp.1 hcrp.2]
  · simp [componentCarrierFinset, hrc_cover p hrcp.1 hrcp.2]
  · simp [componentCarrierFinset, hrr_cover p hrrp.1 hrrp.2]

/-- If the four component finsets are pairwise disjoint and have prescribed
cardinalities, then their carrier union has the sum of those cardinalities. -/
theorem componentCarrierFinset_card_eq_of_disjoint
    (circleCircle circleRay rayCircle rayRay : Finset R2)
    {cc cr rc rr : Nat}
    (hcc_cr : Disjoint circleCircle circleRay)
    (hcc_rc : Disjoint circleCircle rayCircle)
    (hcc_rr : Disjoint circleCircle rayRay)
    (hcr_rc : Disjoint circleRay rayCircle)
    (hcr_rr : Disjoint circleRay rayRay)
    (hrc_rr : Disjoint rayCircle rayRay)
    (hcc_card : circleCircle.card = cc)
    (hcr_card : circleRay.card = cr)
    (hrc_card : rayCircle.card = rc)
    (hrr_card : rayRay.card = rr) :
    (componentCarrierFinset
      circleCircle circleRay rayCircle rayRay).card = cc + cr + rc + rr := by
  classical
  have hcccr_rc : Disjoint (circleCircle ∪ circleRay) rayCircle := by
    rw [Finset.disjoint_left]
    intro p hp hprc
    rw [Finset.mem_union] at hp
    rcases hp with hpcc | hpcr
    · exact (Finset.disjoint_left.mp hcc_rc) hpcc hprc
    · exact (Finset.disjoint_left.mp hcr_rc) hpcr hprc
  have hcccrrc_rr : Disjoint (circleCircle ∪ circleRay ∪ rayCircle) rayRay := by
    rw [Finset.disjoint_left]
    intro p hp hprr
    rw [Finset.mem_union] at hp
    rcases hp with hpcccr | hprc
    · rw [Finset.mem_union] at hpcccr
      rcases hpcccr with hpcc | hpcr
      · exact (Finset.disjoint_left.mp hcc_rr) hpcc hprr
      · exact (Finset.disjoint_left.mp hcr_rr) hpcr hprr
    · exact (Finset.disjoint_left.mp hrc_rr) hprc hprr
  calc
    (componentCarrierFinset
        circleCircle circleRay rayCircle rayRay).card =
        (circleCircle ∪ circleRay ∪ rayCircle).card + rayRay.card := by
      rw [componentCarrierFinset]
      exact Finset.card_union_of_disjoint hcccrrc_rr
    _ = (circleCircle ∪ circleRay).card + rayCircle.card + rayRay.card := by
      rw [Finset.card_union_of_disjoint hcccr_rc]
    _ = circleCircle.card + circleRay.card + rayCircle.card + rayRay.card := by
      rw [Finset.card_union_of_disjoint hcc_cr]
    _ = cc + cr + rc + rr := by
      omega

/-- Component-wise coverage proves that a finite carrier set is the whole
primitive pair carrier. -/
theorem carrierFinset_spec_of_component_covers
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (carrier : Finset R2)
    (hmem : ∀ p : R2, p ∈ carrier → p ∈ A.pairIntersectionSet i j)
    (hcc :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ carrier)
    (hcr :
      ∀ p : R2,
        p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ carrier)
    (hrc :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius →
        p ∈ carrier)
    (hrr :
      ∀ p : R2,
        p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection →
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection →
        p ∈ carrier) :
    ((carrier : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
  refine carrierFinset_spec_of_mem_and_cover carrier hmem ?_
  intro p hp
  rcases (EuclideanLollipopArrangement.mem_pairIntersectionSet_iff
      A (i := i) (j := j) (p := p)).1 hp with hccp | hcrp | hrcp | hrrp
  · exact hcc p hccp.1 hccp.2
  · exact hcr p hcrp.1 hcrp.2
  · exact hrc p hrcp.1 hrcp.2
  · exact hrr p hrrp.1 hrrp.2

/-- If a finite carrier set is exactly the primitive pair carrier, then every
point of that finite set is a primitive carrier-intersection point. -/
theorem carrierFinset_mem_pairIntersectionSet_of_spec
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (carrier : Finset R2)
    (hspec : ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    {p : R2} (hp : p ∈ carrier) :
    p ∈ A.pairIntersectionSet i j := by
  have hpSet : p ∈ ((carrier : Finset R2) : Set R2) := by
    simpa using hp
  simpa [hspec] using hpSet

/-- If the indexed carrier image is exactly the primitive pair carrier, then
each indexed point is a primitive carrier-intersection point. -/
theorem indexedCarrier_mem_pairIntersectionSet_of_spec
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n}
    (points : Fin bound → R2)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    (k : Fin bound) :
    points k ∈ A.pairIntersectionSet i j := by
  have hp : points k ∈ indexedCarrierFinset points := by
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩
  have hpSet :
      points k ∈ ((indexedCarrierFinset points : Finset R2) : Set R2) := by
    simpa using hp
  simpa [hspec] using hpSet

/-- An exact indexed carrier enumeration gives the local carrier-crossing
certificate for one pair. -/
def localPairCarrierCrossingDataOfIndexedCarrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierCrossingData A cross i j hij where
  crossingPoints := indexedCarrierFinset points
  crossingPoints_spec := hspec
  cross_eq_card := by
    rw [indexedCarrierFinset_card points hinj]
    exact hcross

/-- Membership and coverage data for an indexed carrier enumeration give the
local carrier-crossing certificate for one pair. -/
def localPairCarrierCrossingDataOfIndexedCarrierFromMemCover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierCrossingData A cross i j hij :=
  localPairCarrierCrossingDataOfIndexedCarrier
    hij points hinj
    (indexedCarrierFinset_spec_of_mem_and_cover points hmem hcover)
    hcross

/-- An exact indexed carrier enumeration gives the lower subset of the same
size without needing a separate membership proof for each point. -/
def indexed_lower_subset_of_exact_carrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    LocalPairCarrierLowerSubsetData A i j hij bound :=
  indexed_lower_subset_of_mem_pairIntersectionSet
    hij points hinj
    (indexedCarrier_mem_pairIntersectionSet_of_spec points hspec)

/-- Membership data for an indexed carrier enumeration give the lower subset
of the same size.  Coverage is not needed for the lower subset, but this
wrapper matches the fields used by the exact-carrier constructor above. -/
def indexed_lower_subset_of_mem_cover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (_hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p) :
    LocalPairCarrierLowerSubsetData A i j hij bound :=
  indexed_lower_subset_of_mem_pairIntersectionSet hij points hinj hmem

/-- An exact indexed carrier enumeration gives the local lower witness for
the same pair-crossing table entry. -/
def indexed_lower_witness_of_exact_carrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierLowerWitnessData A cross i j hij bound :=
  (indexed_lower_subset_of_exact_carrier hij points hinj hspec)
    |>.toLocalPairCarrierLowerWitnessData
      (localPairCarrierCrossingDataOfIndexedCarrier
        hij points hinj hspec hcross)

/-- Membership and coverage data for an indexed carrier enumeration give the
local lower witness for the same pair-crossing table entry. -/
def indexed_lower_witness_of_mem_cover
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n}
    (hij : i < j)
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hmem : ∀ k : Fin bound, points k ∈ A.pairIntersectionSet i j)
    (hcover :
      ∀ p : R2, p ∈ A.pairIntersectionSet i j →
        ∃ k : Fin bound, points k = p)
    (hcross : cross i j = (bound : Rat)) :
    LocalPairCarrierLowerWitnessData A cross i j hij bound :=
  (indexed_lower_subset_of_mem_cover hij points hinj hmem hcover)
    |>.toLocalPairCarrierLowerWitnessData
      (localPairCarrierCrossingDataOfIndexedCarrierFromMemCover
        hij points hinj hmem hcover hcross)

/-- An exact indexed carrier enumeration identifies the automatic finite
carrier witness with the indexed finset. -/
theorem arrangementPairIntersectionFinset_eq_indexedCarrierFinset_of_exact_carrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (points : Fin bound → R2)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline =
      indexedCarrierFinset points := by
  classical
  let auto :
      Finset R2 :=
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      A hij hLM hline
  have hauto :
      ((auto : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
    simpa [auto] using
      CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (A := A) (i := i) (j := j) (hij := hij) hLM hline
  have hsets :
      ((auto : Finset R2) : Set R2) =
        ((indexedCarrierFinset points : Finset R2) : Set R2) := by
    rw [hauto, ← hspec]
  change auto = indexedCarrierFinset points
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa using hp
    have hpIndexed :
        p ∈ ((indexedCarrierFinset points : Finset R2) : Set R2) := by
      simpa [hsets] using hpSet
    simpa using hpIndexed
  · intro hp
    have hpIndexed :
        p ∈ ((indexedCarrierFinset points : Finset R2) : Set R2) := by
      simpa using hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa [hsets] using hpIndexed
    simpa using hpSet

/-- An exact finite carrier set identifies the automatic finite carrier
witness with that finite set. -/
theorem arrangementPairIntersectionFinset_eq_carrierFinset_of_exact_carrier
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (carrier : Finset R2)
    (hspec :
      ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline =
      carrier := by
  classical
  let auto :
      Finset R2 :=
    CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
      A hij hLM hline
  have hauto :
      ((auto : Finset R2) : Set R2) = A.pairIntersectionSet i j := by
    simpa [auto] using
      CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset_spec
        (A := A) (i := i) (j := j) (hij := hij) hLM hline
  have hsets :
      ((auto : Finset R2) : Set R2) =
        ((carrier : Finset R2) : Set R2) := by
    rw [hauto, ← hspec]
  change auto = carrier
  apply Finset.ext
  intro p
  constructor
  · intro hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa using hp
    have hpCarrier :
        p ∈ ((carrier : Finset R2) : Set R2) := by
      simpa [hsets] using hpSet
    simpa using hpCarrier
  · intro hp
    have hpCarrier : p ∈ ((carrier : Finset R2) : Set R2) := by
      simpa using hp
    have hpSet : p ∈ ((auto : Finset R2) : Set R2) := by
      simpa [hsets] using hpCarrier
    simpa using hpSet

/-- An exact injective indexed carrier enumeration computes the cardinality
of the automatic finite carrier witness. -/
theorem arrangementPairIntersectionFinset_card_eq_of_indexedCarrier
    {n bound : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (points : Fin bound → R2)
    (hinj : Function.Injective points)
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card = bound := by
  rw [arrangementPairIntersectionFinset_eq_indexedCarrierFinset_of_exact_carrier
    hLM hline points hspec]
  exact indexedCarrierFinset_card points hinj

/-- An exact finite carrier set computes the cardinality of the automatic
finite carrier witness. -/
theorem arrangementPairIntersectionFinset_card_eq_of_carrierFinset
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {i j : Fin n} {hij : i < j}
    (hLM :
      euclideanSphere (A.lollipop i).center (A.lollipop i).radius ≠
        euclideanSphere (A.lollipop j).center (A.lollipop j).radius)
    (hline :
      euclideanRayLine (A.lollipop i) ≠ euclideanRayLine (A.lollipop j))
    (carrier : Finset R2)
    (hspec :
      ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    (CompleteFormalization.FiniteCarrier.arrangementPairIntersectionFinset
        A hij hLM hline).card = carrier.card := by
  rw [arrangementPairIntersectionFinset_eq_carrierFinset_of_exact_carrier
    hLM hline carrier hspec]

/-- An exact injective indexed carrier enumeration computes the automatic
carrier crossing-table entry. -/
theorem automaticCarrierCrossingTable_eq_of_indexedCarrier
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
    (hspec :
      ((indexedCarrierFinset points : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j = (bound : Rat) := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    arrangementPairIntersectionFinset_card_eq_of_indexedCarrier
      (hLM i j hij) (hline i j hij) points hinj hspec

/-- An exact finite carrier set computes the automatic carrier crossing-table
entry. -/
theorem automaticCarrierCrossingTable_eq_card_of_carrierFinset
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
    (carrier : Finset R2)
    (hspec :
      ((carrier : Finset R2) : Set R2) =
        A.pairIntersectionSet i j) :
    CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
        A hLM hline i j = (carrier.card : Rat) := by
  rw [CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable_eq_card
    hLM hline hij]
  exact_mod_cast
    arrangementPairIntersectionFinset_card_eq_of_carrierFinset
      (hLM i j hij) (hline i j hij) carrier hspec

/-- Exact indexed carriers assemble into the global pairwise carrier-crossing
certificate. -/
def pairwiseCarrierCrossingDataOfIndexedCarriers
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (bound : ∀ i j : Fin n, i < j → Nat)
    (points :
      ∀ i j : Fin n, ∀ hij : i < j,
        Fin (bound i j hij) → R2)
    (hinj :
      ∀ i j : Fin n, ∀ hij : i < j,
        Function.Injective (points i j hij))
    (hspec :
      ∀ i j : Fin n, ∀ hij : i < j,
        ((indexedCarrierFinset (points i j hij) : Finset R2) : Set R2) =
          A.pairIntersectionSet i j)
    (hcross :
      ∀ i j : Fin n, ∀ hij : i < j,
        cross i j = (bound i j hij : Rat)) :
    PairwiseCarrierCrossingData A cross :=
  PairwiseCarrierCrossingData.ofLocal fun i j hij =>
    localPairCarrierCrossingDataOfIndexedCarrier
      hij (points i j hij) (hinj i j hij)
      (hspec i j hij) (hcross i j hij)

end

end ConstructionFormalization
end TheoremOneManuscript
end Lollipop
