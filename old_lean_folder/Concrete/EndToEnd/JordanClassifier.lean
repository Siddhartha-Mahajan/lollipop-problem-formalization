import old_lean_folder.Concrete.EndToEnd.JordanBridge
import old_lean_folder.Concrete.EndToEnd.LocalInsertion
import Mathlib.Tactic

/-!
# Jordan-side classifiers for localized edge insertions

`LocalInsertion` reduces a one-edge carrier insertion to an active
two-valued classifier on one fibre of the complement-component map.  This file
builds that classifier from Jordan sides.

The remaining geometric obligation is now explicit: for two descendants of the
active old component on the same Jordan side, produce an avoiding simple arc
in the enlarged complement.  Once that arc-lifting statement is proved for
subdivided lollipop edges, the classifier is automatically injective and the
existing split-chain API applies.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace JordanClassifier

open Set Function
open JordanCurveTheorem

/-- A fixed injection from `Bool` into `Fin 2`, used to present Jordan sides in
the component-split API. -/
def boolToFin2 (b : Bool) : Fin 2 :=
  if b then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

theorem boolToFin2_injective : Injective boolToFin2 := by
  intro a b h
  cases a <;> cases b <;> simp [boolToFin2] at h ⊢

/-- The connected components of a Jordan complement, indexed by `Bool`.
The witnesses returned by the Jordan theorem are hidden inside this
noncomputable equivalence; the theorem itself is kernel checked. -/
noncomputable def jordanComplementComponentsEquivBool
    {J : Set Point} (hJ : IsSimpleClosedCurve J) :
    ConnectedComponents (Jᶜ : Set Point) ≃ Bool :=
  let h := JordanCurveTheorem.jordan_curve_theorem hJ
  let A : Set Point := Classical.choose h
  let hA := Classical.choose_spec h
  let B : Set Point := Classical.choose hA
  let hB := Classical.choose_spec hA
  JordanBridge.componentsEquivBool (C := J) (A := A) (B := B)
    hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
    hB.2.2.2.2.2.1 hB.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.2

/-- The Jordan side occupied by a connected component of the complement of a
larger carrier `K` containing the Jordan curve `J`. -/
noncomputable def sideOfComponent
    {K J : Set Point} (hJK : J ⊆ K) (hJ : IsSimpleClosedCurve J) :
    ConnectedComponents (Kᶜ : Set Point) → Fin 2 :=
  fun c =>
    boolToFin2
      (jordanComplementComponentsEquivBool hJ
        (ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset hJK) c))

@[simp] theorem sideOfComponent_mk
    {K J : Set Point} (hJK : J ⊆ K) (hJ : IsSimpleClosedCurve J)
    (x : (Kᶜ : Set Point)) :
    sideOfComponent hJK hJ (ConnectedComponents.mk x) =
      boolToFin2
        (jordanComplementComponentsEquivBool hJ
          (ConnectedComponents.mk
            (ComponentFibers.inclusion
              (ComponentSurjectivity.complementSubset hJK) x))) := by
  rfl

/-- Arc-lifting obligation inside the active old component.  Equal Jordan side
must be witnessed by a simple arc avoiding the enlarged carrier. -/
def ActiveSideArcLifting
    {C K J : Set Point} (hCK : C ⊆ K)
    (hJK : J ⊆ K) (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point)) : Prop :=
  ∀ (x y : (Kᶜ : Set Point)),
    ComponentFibers.inclusionMap
        (ComponentSurjectivity.complementSubset hCK)
        (ConnectedComponents.mk x) = active →
    ComponentFibers.inclusionMap
        (ComponentSurjectivity.complementSubset hCK)
        (ConnectedComponents.mk y) = active →
    sideOfComponent hJK hJ (ConnectedComponents.mk x) =
      sideOfComponent hJK hJ (ConnectedComponents.mk y) →
    x.1 ≠ y.1 →
      ∃ P : Set Point,
        IsSimpleArcEnd P x.1 y.1 ∧ Disjoint P K

/-- Exactness obligation for the active fibre: both Jordan sides occur among
descendants of the active old component. -/
def ActiveSideSurjective
    {C K J : Set Point} (hCK : C ⊆ K)
    (hJK : J ⊆ K) (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point)) : Prop :=
  Surjective
    (fun a : ComponentFibers.Fiber
        (ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset hCK)) active =>
      sideOfComponent hJK hJ a.1)

/-- Active-side arc lifting makes the Jordan-side classifier injective on the
active fibre. -/
theorem activeSide_injective_of_arcLifting
    {C K J : Set Point} (hCK : C ⊆ K)
    (hJK : J ⊆ K) (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hlift : ActiveSideArcLifting hCK hJK hJ active) :
    Injective
      (fun a : ComponentFibers.Fiber
          (ComponentFibers.inclusionMap
            (ComponentSurjectivity.complementSubset hCK)) active =>
        sideOfComponent hJK hJ a.1) := by
  rintro ⟨d, hd⟩ ⟨e, he⟩ hside
  apply Subtype.ext
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe d
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe e
  change sideOfComponent hJK hJ (ConnectedComponents.mk x) =
    sideOfComponent hJK hJ (ConnectedComponents.mk y) at hside
  by_cases hxy : x.1 = y.1
  · have hxy' : x = y := Subtype.ext hxy
    simp [hxy']
  · obtain ⟨P, hP, hPK⟩ := hlift x y hd he hside hxy
    exact JordanBridge.connectedComponents_mk_eq_of_simpleArcLifting
      x y hP hPK

/-- Bounded split data for a localized edge, with the active classifier
supplied by Jordan sides. -/
def oneComponentSplitDataOfJordanLocalizedEdge
    {C E J : Set Point}
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    ComponentFibers.OneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension C E)) :=
  LocalInsertion.oneComponentSplitDataOfLocalizedEdge active hloc
    (fun a => sideOfComponent hJK hJ a.1)
    (activeSide_injective_of_arcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active
      hlift)

/-- Exact split data for a localized edge, with the active classifier supplied
by Jordan sides. -/
def exactOneComponentSplitDataOfJordanLocalizedEdge
    {C E J : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active)
    (hside : ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension C E)) :=
  LocalInsertion.exactOneComponentSplitDataOfLocalizedEdge hCclosed L hE
    active hloc (fun a => sideOfComponent hJK hJ a.1)
    (activeSide_injective_of_arcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active
      hlift)
    hside

/-- A localized edge with Jordan-side arc lifting gives a bounded one-step
split chain. -/
def boundedChainOfJordanLocalizedEdge
    {C E J : Set Point}
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    ComponentSplitChain.Chain 1
      ((LocalInsertion.carrierExtension C E)ᶜ) (Cᶜ) :=
  LocalInsertion.boundedChainOfLocalizedEdge active hloc
    (fun a => sideOfComponent hJK hJ a.1)
    (activeSide_injective_of_arcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active
      hlift)

/-- A localized edge with exact Jordan-side data gives an exact one-step split
chain. -/
def exactChainOfJordanLocalizedEdge
    {C E J : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active)
    (hside : ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    ComponentSplitChain.ExactChain 1
      ((LocalInsertion.carrierExtension C E)ᶜ) (Cᶜ) :=
  LocalInsertion.exactChainOfLocalizedEdge hCclosed L hE active hloc
    (fun a => sideOfComponent hJK hJ a.1)
    (activeSide_injective_of_arcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active
      hlift)
    hside

end JordanClassifier
end EndToEnd
end Concrete
end Lollipop
