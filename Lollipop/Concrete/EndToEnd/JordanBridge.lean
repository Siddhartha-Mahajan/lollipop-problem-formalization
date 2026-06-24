import Lollipop.Concrete.EndToEnd.ComponentLifting
import JordanCurveTheorem.JordanCurveTheoremStatement
import Mathlib.Topology.Connected.Clopen
import Mathlib.Tactic

/-!
# Jordan-curve bridge for the concrete endpoint

This file imports the checked local Jordan-curve development and exposes only
the small facts needed by the lollipop topology route:

* a simple closed curve has two complement components;
* a closed-set complement component is equivalently witnessed by an avoiding
  simple arc;
* avoiding simple arcs give equality in Mathlib's `ConnectedComponents`
  quotient.

The larger stale `Lollipop.Concrete.Actual` topology draft is intentionally
not imported here.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace JordanBridge

open Set Function Topology
open JordanCurveTheorem

/-- The complement of a planar carrier, as a subtype. -/
abbrev Complement (C : Set Point) := (Cᶜ : Set Point)

/-- The two Jordan sides, regarded as subsets of the complement subtype. -/
def side (C A B : Set Point) : Bool → Set (Complement C)
  | false => Subtype.val ⁻¹' A
  | true  => Subtype.val ⁻¹' B

@[simp] theorem mem_side_false {C A B : Set Point}
    (x : Complement C) :
    x ∈ side C A B false ↔ x.1 ∈ A := Iff.rfl

@[simp] theorem mem_side_true {C A B : Set Point}
    (x : Complement C) :
    x ∈ side C A B true ↔ x.1 ∈ B := Iff.rfl

/-- A point outside the Jordan curve lies in one of the two sides. -/
theorem mem_left_or_right
    {C A B : Set Point}
    (hcover : A ∪ B ∪ C = Set.univ)
    (x : Complement C) :
    x.1 ∈ A ∨ x.1 ∈ B := by
  have hx : x.1 ∈ A ∪ B ∪ C := by
    rw [hcover]
    exact Set.mem_univ _
  rcases hx with (hxA | hxB) | hxC
  · exact Or.inl hxA
  · exact Or.inr hxB
  · exact False.elim (x.2 hxC)

/-- In the complement subtype, either side is the complement of the other. -/
theorem side_compl
    {C A B : Set Point}
    (hAB : Disjoint A B)
    (hcover : A ∪ B ∪ C = Set.univ) :
    ∀ b : Bool, (side C A B b)ᶜ = side C A B (!b) := by
  intro b
  cases b
  · ext x
    simp only [Bool.not_false, Set.mem_compl_iff, mem_side_false,
      mem_side_true]
    constructor
    · intro hxA
      rcases mem_left_or_right hcover x with hx | hx
      · exact False.elim (hxA hx)
      · exact hx
    · intro hxB hxA
      exact Set.disjoint_left.mp hAB hxA hxB
  · ext x
    simp only [Bool.not_true, Set.mem_compl_iff, mem_side_true,
      mem_side_false]
    constructor
    · intro hxB
      rcases mem_left_or_right hcover x with hx | hx
      · exact hx
      · exact False.elim (hxB hx)
    · intro hxA hxB
      exact Set.disjoint_left.mp hAB hxA hxB

/-- Both Jordan sides are open in the complement subtype. -/
theorem side_isOpen
    {C A B : Set Point}
    (hA : IsOpen A) (hB : IsOpen B) :
    ∀ b : Bool, IsOpen (side C A B b) := by
  intro b
  cases b
  · exact hA.preimage continuous_subtype_val
  · exact hB.preimage continuous_subtype_val

/-- Both Jordan sides are clopen in the complement subtype. -/
theorem side_isClopen
    {C A B : Set Point}
    (hA : IsOpen A) (hB : IsOpen B)
    (hAB : Disjoint A B)
    (hcover : A ∪ B ∪ C = Set.univ) :
    ∀ b : Bool, IsClopen (side C A B b) := by
  intro b
  refine ⟨?_, side_isOpen hA hB b⟩
  rw [← isOpen_compl_iff, side_compl hAB hcover]
  exact side_isOpen hA hB (!b)

/-- The image of the left subtype side under the inclusion is exactly `A`. -/
theorem image_side_false
    {C A B : Set Point}
    (hAC : Disjoint A C) :
    Subtype.val '' side C A B false = A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hxA
    have hxC : x ∉ C := fun hx => Set.disjoint_left.mp hAC hxA hx
    exact ⟨⟨x, hxC⟩, hxA, rfl⟩

/-- The image of the right subtype side under the inclusion is exactly `B`. -/
theorem image_side_true
    {C A B : Set Point}
    (hBC : Disjoint B C) :
    Subtype.val '' side C A B true = B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hxB
    have hxC : x ∉ C := fun hx => Set.disjoint_left.mp hBC hxB hx
    exact ⟨⟨x, hxC⟩, hxB, rfl⟩

/-- Connectedness of either Jordan side transports to the corresponding
subset of the complement subtype. -/
theorem side_isConnected
    {C A B : Set Point}
    (hA : IsConnected A) (hB : IsConnected B)
    (hAC : Disjoint A C) (hBC : Disjoint B C) :
    ∀ b : Bool, IsConnected (side C A B b) := by
  intro b
  cases b
  · have himage : Subtype.val '' side C A B false = A :=
      image_side_false hAC
    have hpreImage : IsPreconnected
        (Subtype.val '' side C A B false) := by
      rw [himage]
      exact hA.isPreconnected
    have hpre : IsPreconnected (side C A B false) :=
      (Topology.IsInducing.subtypeVal.isPreconnected_image).mp hpreImage
    rcases hA.nonempty with ⟨x, hxA⟩
    have hxC : x ∉ C := fun hx => Set.disjoint_left.mp hAC hxA hx
    exact ⟨⟨⟨x, hxC⟩, hxA⟩, hpre⟩
  · have himage : Subtype.val '' side C A B true = B :=
      image_side_true hBC
    have hpreImage : IsPreconnected
        (Subtype.val '' side C A B true) := by
      rw [himage]
      exact hB.isPreconnected
    have hpre : IsPreconnected (side C A B true) :=
      (Topology.IsInducing.subtypeVal.isPreconnected_image).mp hpreImage
    rcases hB.nonempty with ⟨x, hxB⟩
    have hxC : x ∉ C := fun hx => Set.disjoint_left.mp hBC hxB hx
    exact ⟨⟨⟨x, hxC⟩, hxB⟩, hpre⟩

/-- The two subtype sides are pairwise disjoint. -/
theorem side_pairwise_disjoint
    {C A B : Set Point}
    (hAB : Disjoint A B) :
    Pairwise (Function.onFun Disjoint (side C A B)) := by
  intro b c hbc
  cases b <;> cases c
  · exact False.elim (hbc rfl)
  · refine Set.disjoint_left.mpr ?_
    intro x hxA hxB
    exact Set.disjoint_left.mp hAB hxA hxB
  · refine Set.disjoint_left.mpr ?_
    intro x hxB hxA
    exact Set.disjoint_left.mp hAB hxA hxB
  · exact False.elim (hbc rfl)

/-- The two subtype sides cover the whole complement. -/
theorem iUnion_side
    {C A B : Set Point}
    (hcover : A ∪ B ∪ C = Set.univ) :
    (⋃ b : Bool, side C A B b) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases mem_left_or_right hcover x with hxA | hxB
  · exact ⟨false, hxA⟩
  · exact ⟨true, hxB⟩

/-- The connected components of a Jordan complement are indexed by `Bool`. -/
noncomputable def componentsEquivBool
    {C A B : Set Point}
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hAconn : IsConnected A) (hBconn : IsConnected B)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = Set.univ) :
    ConnectedComponents (Complement C) ≃ Bool :=
  ConnectedComponents.equivOfIsClopenOfIsConnected
    (side_isClopen hAopen hBopen hAB hcover)
    (side_pairwise_disjoint hAB)
    (iUnion_side hcover)
    (side_isConnected hAconn hBconn hAC hBC)

/-- Component-count form of the separation data returned by the Jordan curve
theorem. -/
theorem componentCount_complement_eq_two_of_sides
    {C A B : Set Point}
    (hAopen : IsOpen A) (hBopen : IsOpen B)
    (hAconn : IsConnected A) (hBconn : IsConnected B)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = Set.univ) :
    Nat.card (ConnectedComponents (Complement C)) = 2 := by
  calc
    Nat.card (ConnectedComponents (Complement C)) = Nat.card Bool :=
      Nat.card_congr
        (componentsEquivBool hAopen hBopen hAconn hBconn
          hAB hAC hBC hcover)
    _ = 2 := by norm_num

/-- A simple closed curve has exactly two complementary connected components,
expressed in the concrete endpoint's component-count model. -/
theorem jordan_complement_componentCount_eq_two
    {C : Set Point} (hC : IsSimpleClosedCurve C) :
    componentCount (Cᶜ) = 2 := by
  rcases JordanCurveTheorem.jordan_curve_theorem hC with
    ⟨A, B, hAopen, hBopen, hAconn, hBconn,
      hAB, hAC, hBC, hcover⟩
  simpa [componentCount, Complement] using
    componentCount_complement_eq_two_of_sides
      hAopen hBopen hAconn hBconn hAB hAC hBC hcover

/-- The Jordan complement component type is finite. -/
theorem finite_components_jordan_complement
    {C : Set Point} (hC : IsSimpleClosedCurve C) :
    Finite (ConnectedComponents (Cᶜ : Set Point)) := by
  rcases JordanCurveTheorem.jordan_curve_theorem hC with
    ⟨A, B, hAopen, hBopen, hAconn, hBconn,
      hAB, hAC, hBC, hcover⟩
  simpa [Complement] using
    Finite.of_injective
      (componentsEquivBool hAopen hBopen hAconn hBconn
        hAB hAC hBC hcover)
      (componentsEquivBool hAopen hBopen hAconn hBconn
        hAB hAC hBC hcover).injective

/-- Closed-set complement membership in a connected component is equivalent
to an avoiding simple arc. -/
theorem mem_connectedComponentIn_iff_exists_simpleArcEnd_disjoint
    {G : Set Point} {x y : Point}
    (hG : IsClosed G) (hxy : x ≠ y) :
    y ∈ connectedComponentIn Gᶜ x ↔
      ∃ C : Set Point, IsSimpleArcEnd C x y ∧ Disjoint C G := by
  simpa using
    JordanCurveTheorem.component_simple_arc_ver2
      (G := G) (x := x) (y := y) hG hxy

/-- A simple arc disjoint from a carrier proves equality in the connected-
component quotient of the carrier complement. -/
theorem connectedComponents_mk_eq_of_simpleArcEnd_disjoint
    {K P : Set Point} {x y : Point}
    (hP : IsSimpleArcEnd P x y) (hPK : Disjoint P K) :
    ConnectedComponents.mk
        (⟨x, fun hxK => Set.disjoint_left.mp hPK
          (isSimpleArcEnd_mem_left hP) hxK⟩ : (Kᶜ : Set Point)) =
      ConnectedComponents.mk
        (⟨y, fun hyK => Set.disjoint_left.mp hPK
          (isSimpleArcEnd_mem_right hP) hyK⟩ : (Kᶜ : Set Point)) := by
  have hPsub : P ⊆ Kᶜ := by
    intro z hzP hzK
    exact Set.disjoint_left.mp hPK hzP hzK
  exact ComponentLifting.connectedComponents_mk_eq_of_isConnected_subset
    (isSimpleArc_isConnected (isSimpleArcEnd_isSimpleArc hP)) hPsub
    (isSimpleArcEnd_mem_left hP) (isSimpleArcEnd_mem_right hP)

/-- Extensional form of the previous theorem for already-typed complement
points. -/
theorem connectedComponents_mk_eq_of_simpleArcLifting
    {K P : Set Point} (x y : (Kᶜ : Set Point))
    (hP : IsSimpleArcEnd P x.1 y.1) (hPK : Disjoint P K) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  have h := connectedComponents_mk_eq_of_simpleArcEnd_disjoint hP hPK
  simpa only [Subtype.coe_eta] using h

/-- In the complement of a closed planar carrier, quotient equality of two
distinct points is witnessed by an actual simple arc avoiding the carrier. -/
theorem exists_simpleArcEnd_disjoint_of_connectedComponents_mk_eq
    {C : Set Point} (hC : IsClosed C) (x y : (Cᶜ : Set Point))
    (hxy : ConnectedComponents.mk x = ConnectedComponents.mk y)
    (hne : x.1 ≠ y.1) :
    ∃ P : Set Point, IsSimpleArcEnd P x.1 y.1 ∧ Disjoint P C := by
  exact (mem_connectedComponentIn_iff_exists_simpleArcEnd_disjoint hC hne).mp
    (ComponentLifting.mem_connectedComponentIn_of_connectedComponents_mk_eq
      x y hxy)

end JordanBridge
end EndToEnd
end Concrete
end Lollipop
