import old_lean_folder.Concrete.EndToEnd.Coordinate
import Mathlib.Data.Finite.Card
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# One-point compactification and the robust pair excess

For arbitrary, possibly degenerate arrangements, a finite crossing-point count
is not the correct pair invariant.  We use

`q(L,M) = #π₀(Ĺ ∩ M̂) - 1`,

where every compactified carrier contains the common point at infinity.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

abbrev Sphere2 := OnePoint Point

def finitePoint (x : Point) : Sphere2 := OnePoint.some x

def infinity : Sphere2 := OnePoint.infty

@[simp] theorem finitePoint_injective : Function.Injective finitePoint := by
  intro x y h
  simpa [finitePoint] using h

@[simp] theorem finitePoint_ne_infinity (x : Point) :
    finitePoint x ≠ infinity := by simp [finitePoint, infinity]

def finiteLift (S : Set Point) : Set Sphere2 := finitePoint '' S

@[simp] theorem mem_finiteLift_iff {S : Set Point} {x : Point} :
    finitePoint x ∈ finiteLift S ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact finitePoint_injective hxy ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

@[simp] theorem infinity_not_mem_finiteLift (S : Set Point) :
    infinity ∉ finiteLift S := by
  rintro ⟨x, _, hx⟩
  exact finitePoint_ne_infinity x hx

/-- Compactified carrier. -/
def hatCarrier (L : Lollipop) : Set Sphere2 :=
  finiteLift L.carrier ∪ {infinity}

@[simp] theorem infinity_mem_hatCarrier (L : Lollipop) :
    infinity ∈ hatCarrier L := by simp [hatCarrier]

@[simp] theorem finitePoint_mem_hatCarrier_iff (L : Lollipop) (x : Point) :
    finitePoint x ∈ hatCarrier L ↔ x ∈ L.carrier := by
  simp [hatCarrier]

/-- Compactified arrangement union.  The explicit infinity term also makes the
empty arrangement correct. -/
def hatOccupied {n : ℕ} (A : Arrangement n) : Set Sphere2 :=
  (⋃ i, hatCarrier (A i)) ∪ {infinity}

@[simp] theorem infinity_mem_hatOccupied {n : ℕ} (A : Arrangement n) :
    infinity ∈ hatOccupied A := by simp [hatOccupied]

@[simp] theorem finitePoint_mem_hatOccupied_iff {n : ℕ}
    (A : Arrangement n) (x : Point) :
    finitePoint x ∈ hatOccupied A ↔ x ∈ occupied A := by
  simp [hatOccupied, occupied]

/-- Number of connected components of a subspace. -/
def componentCount {X : Type*} [TopologicalSpace X] (S : Set X) : ℕ :=
  Nat.card (ConnectedComponents S)

/-- Region count is component count of the ordinary occupied complement. -/
theorem regionCount_eq_componentCount_compl {n : ℕ} (A : Arrangement n) :
    regionCount A = componentCount ((occupied A)ᶜ) := by
  rfl

/-- Rational region count as component count of the ordinary occupied
complement. -/
theorem regionCountRat_eq_componentCount_compl {n : ℕ} (A : Arrangement n) :
    regionCountRat A = (componentCount ((occupied A)ᶜ) : ℚ) := by
  rw [regionCountRat, regionCount_eq_componentCount_compl]

def hatPairIntersection (L M : Lollipop) : Set Sphere2 :=
  hatCarrier L ∩ hatCarrier M

@[simp] theorem infinity_mem_hatPairIntersection (L M : Lollipop) :
    infinity ∈ hatPairIntersection L M :=
  ⟨infinity_mem_hatCarrier L, infinity_mem_hatCarrier M⟩

/-- Robust pair excess, valid for tangent, coincident, and overlapping pairs. -/
def pairExcessNat (L M : Lollipop) : ℕ :=
  componentCount (hatPairIntersection L M) - 1

def pairExcess (L M : Lollipop) : ℚ := pairExcessNat L M

@[simp] theorem hatPairIntersection_symm (L M : Lollipop) :
    hatPairIntersection L M = hatPairIntersection M L := by
  simp [hatPairIntersection, inter_comm]

@[simp] theorem pairExcessNat_symm (L M : Lollipop) :
    pairExcessNat L M = pairExcessNat M L := by
  simp [pairExcessNat, hatPairIntersection_symm]

@[simp] theorem pairExcess_symm (L M : Lollipop) :
    pairExcess L M = pairExcess M L := by
  simp [pairExcess, pairExcessNat_symm]

def pairExcessTable {n : ℕ} (A : Arrangement n) : Fin n → Fin n → ℚ :=
  fun i j => pairExcess (A i) (A j)

@[simp] theorem pairExcessTable_symm {n : ℕ} (A : Arrangement n)
    (i j : Fin n) : pairExcessTable A i j = pairExcessTable A j i :=
  pairExcess_symm (A i) (A j)

/-- Set-level finite-chart complement identity. -/
theorem finitePoint_preimage_compl_hatOccupied {n : ℕ} (A : Arrangement n) :
    finitePoint ⁻¹' (hatOccupied A)ᶜ = (occupied A)ᶜ := by
  ext x
  simp

/-- Equivalence between the original free space and the compactified
complement.  `PlanarTopology` upgrades it to a homeomorphism. -/
def freeSpaceEquivHatComplement {n : ℕ} (A : Arrangement n) :
    FreeSpace A ≃ {x : Sphere2 // x ∉ hatOccupied A} where
  toFun x := ⟨finitePoint x, by simpa using x.property⟩
  invFun y := by
    rcases y with ⟨y, hy⟩
    cases y using OnePoint.rec with
    | infty => exact False.elim (hy (infinity_mem_hatOccupied A))
    | coe x =>
        exact ⟨x, by
          intro hx
          exact hy (by
            simpa [finitePoint] using (finitePoint_mem_hatOccupied_iff A x).2 hx)⟩
  left_inv x := by ext; rfl
  right_inv y := by
    rcases y with ⟨y, hy⟩
    cases y using OnePoint.rec with
    | infty => exact False.elim (hy (infinity_mem_hatOccupied A))
    | coe x => rfl

end EndToEnd
end Concrete
end Lollipop
