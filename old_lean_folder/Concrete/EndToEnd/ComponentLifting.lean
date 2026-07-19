import old_lean_folder.Concrete.EndToEnd.ComponentFibers
import Mathlib.Tactic

/-!
# Component lifting criteria

`ComponentFibers` proves the cardinality consequences of one-component
splitting once the relevant fibres of the component map are controlled.  This
file supplies a small topology bridge for building those fibre controls from
actual connected witnesses in the complement.

The intended later use is the local planar insertion theorem: if two points
of the new complement lie over the same old complement component, and a
connected set in the new complement joins them, then they are already equal in
the new `ConnectedComponents` quotient.  Therefore such joining data make the
corresponding fibre subsingleton.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ComponentLifting

open Set Function

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Points of a connected ambient subset have the same connected-component
class after including that subset into a larger set. -/
theorem connectedComponents_mk_eq_of_isConnected_subset
    {P S : Set X} (hP : IsConnected P) (hPS : P ⊆ S)
    {x y : X} (hx : x ∈ P) (hy : y ∈ P) :
    ConnectedComponents.mk (⟨x, hPS hx⟩ : S) =
      ConnectedComponents.mk (⟨y, hPS hy⟩ : S) := by
  let f : P → S := fun z => ⟨z.1, hPS z.2⟩
  have hf : Continuous f :=
    Continuous.subtype_mk continuous_subtype_val (fun z => hPS z.2)
  let xP : P := ⟨x, hx⟩
  let yP : P := ⟨y, hy⟩
  letI : ConnectedSpace P := Subtype.connectedSpace hP
  have hxy : ConnectedComponents.mk xP = ConnectedComponents.mk yP :=
    Subsingleton.elim _ _
  have hmap := congrArg hf.connectedComponentsMap hxy
  simpa [f, xP, yP] using hmap

/-- Equality in the connected-component quotient of a subtype gives ambient
membership in the corresponding relative connected component. -/
theorem mem_connectedComponentIn_of_connectedComponents_mk_eq
    {F : Set X} (x y : F)
    (hxy : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    y.1 ∈ connectedComponentIn F x.1 := by
  have hcomp : connectedComponent x = connectedComponent y :=
    ConnectedComponents.coe_eq_coe.mp hxy
  have hy : y ∈ connectedComponent x := by
    rw [hcomp]
    exact mem_connectedComponent
  rw [connectedComponentIn_eq_image x.2]
  exact ⟨y, hy, rfl⟩

/-- A concrete lifting condition for one fibre of an inclusion-induced
component map.  Whenever two points of `S` map to the same target component
`b`, and they are not literally the same point, there is an actual connected
set inside `S` joining them. -/
def FiberConnectedLifting {S T : Set X} (hST : S ⊆ T)
    (b : ConnectedComponents T) : Prop :=
  ∀ (x y : S),
    ComponentFibers.inclusionMap hST (ConnectedComponents.mk x) = b →
    ComponentFibers.inclusionMap hST (ConnectedComponents.mk y) = b →
    x.1 ≠ y.1 →
      ∃ P : Set X, IsConnected P ∧ P ⊆ S ∧ x.1 ∈ P ∧ y.1 ∈ P

/-- Connected lifting data make the corresponding fibre of the component map
subsingleton. -/
theorem fiber_subsingleton_of_connectedLifting
    {S T : Set X} {hST : S ⊆ T} {b : ConnectedComponents T}
    (hlift : FiberConnectedLifting hST b) :
    Subsingleton (ComponentFibers.Fiber
      (ComponentFibers.inclusionMap hST) b) := by
  constructor
  rintro ⟨d, hd⟩ ⟨e, he⟩
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe d
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe e
  by_cases hxy : x.1 = y.1
  · have hxy' : x = y := Subtype.ext hxy
    simp [hxy']
  · obtain ⟨P, hP, hPS, hxP, hyP⟩ := hlift x y hd he hxy
    exact connectedComponents_mk_eq_of_isConnected_subset hP hPS hxP hyP

/-- Connected lifting data for every inactive target component. -/
def InactiveConnectedLifting {S T : Set X} (hST : S ⊆ T)
    (active : ConnectedComponents T) : Prop :=
  ∀ b : ConnectedComponents T, b ≠ active → FiberConnectedLifting hST b

/-- Inactive connected lifting supplies the inactive-fibre field required by
`OneComponentSplitData`. -/
theorem inactive_subsingleton_of_connectedLifting
    {S T : Set X} {hST : S ⊆ T} {active : ConnectedComponents T}
    (hlift : InactiveConnectedLifting hST active) :
    ∀ b : ConnectedComponents T, b ≠ active →
      Subsingleton (ComponentFibers.Fiber
        (ComponentFibers.inclusionMap hST) b) := by
  intro b hb
  exact fiber_subsingleton_of_connectedLifting (hlift b hb)

/-- Constructor for one-component split data from a two-valued classifier on
the active fibre and connected lifting on all inactive fibres. -/
def oneComponentSplitDataOfConnectedLifting
    {S T : Set X} (hST : S ⊆ T)
    (active : ConnectedComponents T)
    (activeClassifier :
      ComponentFibers.Fiber
        (ComponentFibers.inclusionMap hST) active → Fin 2)
    (active_injective : Injective activeClassifier)
    (hinactive : InactiveConnectedLifting hST active) :
    ComponentFibers.OneComponentSplitData hST where
  active := active
  activeClassifier := activeClassifier
  active_injective := active_injective
  inactive_subsingleton :=
    inactive_subsingleton_of_connectedLifting hinactive

end ComponentLifting
end EndToEnd
end Concrete
end Lollipop
