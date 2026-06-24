import Lollipop.Concrete.EndToEnd.ComponentSplitChain
import Lollipop.Concrete.EndToEnd.ComponentSurjectivity

/-!
# Localized one-edge insertions

The insertion-fan route eventually subdivides a new lollipop carrier into
effective edges.  This file records the topology API for one such edge.

If an edge set `E` lies in a lollipop carrier and, relative to the old carrier
`C`, every point of `E \ C` lies in one old complement component, then all
inactive fibres of the complement inclusion are already controlled.  The only
remaining input for an exact one-component split is the active two-side
classifier.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace LocalInsertion

open Set Function

/-- Enlarge an old carrier `C` by one local inserted edge `E`. -/
def carrierExtension (C E : Set Point) : Set Point :=
  C ∪ E

/-- The old carrier is contained in its one-edge extension. -/
theorem old_subset_carrierExtension (C E : Set Point) :
    C ⊆ carrierExtension C E :=
  fun _ hx => Or.inl hx

/-- If the edge lies in a lollipop carrier, the one-edge extension is
contained in the old carrier plus the whole lollipop carrier. -/
theorem carrierExtension_subset_union_carrier
    {C E : Set Point} {L : Lollipop} (hE : E ⊆ L.carrier) :
    carrierExtension C E ⊆ C ∪ L.carrier := by
  intro z hz
  rcases hz with hzC | hzE
  · exact Or.inl hzC
  · exact Or.inr (hE hzE)

/-- Localized edge condition: every point of the inserted edge that was not
already in the old carrier lies in the active old complement component. -/
def EdgeLocalized (C E : Set Point)
    (active : ConnectedComponents (Cᶜ : Set Point)) : Prop :=
  ∀ z : Point, z ∈ E → (hzC : z ∉ C) →
    ConnectedComponents.mk (⟨z, hzC⟩ : (Cᶜ : Set Point)) = active

/-- Edge localization is exactly the `NewPartLocalized` condition for the
extension `C ∪ E`. -/
theorem newPartLocalized_of_edgeLocalized
    {C E : Set Point} {active : ConnectedComponents (Cᶜ : Set Point)}
    (hloc : EdgeLocalized C E active) :
    ComponentSurjectivity.NewPartLocalized
      (old_subset_carrierExtension C E) active := by
  intro z hzK hzC
  rcases hzK with hzOld | hzE
  · exact False.elim (hzC hzOld)
  · exact hloc z hzE hzC

/-- Exact split data for a localized one-edge carrier extension, assuming the
active two-side classifier has already been built and proved bijective. -/
def exactOneComponentSplitDataOfLocalizedEdge
    {C E : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : EdgeLocalized C E active)
    (activeClassifier :
      ComponentFibers.Fiber
        (ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (old_subset_carrierExtension C E))) active →
          Fin 2)
    (active_injective : Injective activeClassifier)
    (active_surjective : Surjective activeClassifier) :
    ComponentFibers.ExactOneComponentSplitData
      (ComponentSurjectivity.complementSubset
        (old_subset_carrierExtension C E)) :=
  ComponentSurjectivity.exactOneComponentSplitDataOfLocalizedConnectedLifting
    (old_subset_carrierExtension C E) hCclosed L
    (carrierExtension_subset_union_carrier hE) active
    (newPartLocalized_of_edgeLocalized hloc)
    activeClassifier active_injective active_surjective

/-- A localized exact edge split gives a one-step exact split chain.  This is
the chain-level object that a later carrier-subdivision proof will concatenate
over all effective inserted edges. -/
def exactChainOfLocalizedEdge
    {C E : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : EdgeLocalized C E active)
    (activeClassifier :
      ComponentFibers.Fiber
        (ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (old_subset_carrierExtension C E))) active →
          Fin 2)
    (active_injective : Injective activeClassifier)
    (active_surjective : Surjective activeClassifier) :
    ComponentSplitChain.ExactChain 1
      ((carrierExtension C E)ᶜ) (Cᶜ) :=
  ComponentSplitChain.ExactChain.singleton
    (ComponentSurjectivity.complementSubset
      (old_subset_carrierExtension C E))
    (exactOneComponentSplitDataOfLocalizedEdge hCclosed L hE active hloc
      activeClassifier active_injective active_surjective)

/-- Forget exactness from a localized one-edge split chain. -/
def chainOfLocalizedEdge
    {C E : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : EdgeLocalized C E active)
    (activeClassifier :
      ComponentFibers.Fiber
        (ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (old_subset_carrierExtension C E))) active →
          Fin 2)
    (active_injective : Injective activeClassifier)
    (active_surjective : Surjective activeClassifier) :
    ComponentSplitChain.Chain 1
      ((carrierExtension C E)ᶜ) (Cᶜ) :=
  (exactChainOfLocalizedEdge hCclosed L hE active hloc
    activeClassifier active_injective active_surjective).toChain

end LocalInsertion
end EndToEnd
end Concrete
end Lollipop
