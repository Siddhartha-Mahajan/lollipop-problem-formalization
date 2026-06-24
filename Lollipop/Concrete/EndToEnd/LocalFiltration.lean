import Lollipop.Concrete.EndToEnd.LocalInsertion

/-!
# Finite localized edge filtrations

This file compiles a finite sequence of localized one-edge carrier extensions
into the split-chain objects used by the region-count insertion lemmas.

It is still not the geometric subdivision theorem.  Instead, it is the finite
bookkeeping layer that the subdivision theorem should target.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace LocalFiltration

open Set Function

/-- Active fibre for the complement inclusion associated to extending `C` by
one edge set `E`. -/
abbrev ActiveFiber (C E : Set Point)
    (active : ConnectedComponents (Cᶜ : Set Point)) :=
  ComponentFibers.Fiber
    (ComponentFibers.inclusionMap
      (ComponentSurjectivity.complementSubset
        (LocalInsertion.old_subset_carrierExtension C E))) active

/-- Two-valued classifier on the active fibre of a one-edge extension. -/
abbrev ActiveClassifier (C E : Set Point)
    (active : ConnectedComponents (Cᶜ : Set Point)) :=
  ActiveFiber C E active → Fin 2

/-- Bounded one-edge data.  This is enough for the arbitrary upper-bound
direction: at most one old complement component can split. -/
structure LocalizedEdgeStep (C E : Set Point) where
  active : ConnectedComponents (Cᶜ : Set Point)
  localized : LocalInsertion.EdgeLocalized C E active
  activeClassifier : ActiveClassifier C E active
  active_injective : Injective activeClassifier

namespace LocalizedEdgeStep

/-- Compile one bounded localized edge step to a one-step split chain. -/
def toChain {C E : Set Point} (s : LocalizedEdgeStep C E) :
    ComponentSplitChain.Chain 1
      ((LocalInsertion.carrierExtension C E)ᶜ) (Cᶜ) :=
  LocalInsertion.boundedChainOfLocalizedEdge
    s.active s.localized s.activeClassifier s.active_injective

end LocalizedEdgeStep

/-- Exact one-edge data.  This is the generic-position version: the active
component really splits into two nonempty sides. -/
structure LocalizedExactEdgeStep (L : Lollipop) (C E : Set Point) where
  old_closed : IsClosed C
  edge_subset_carrier : E ⊆ L.carrier
  active : ConnectedComponents (Cᶜ : Set Point)
  localized : LocalInsertion.EdgeLocalized C E active
  activeClassifier : ActiveClassifier C E active
  active_injective : Injective activeClassifier
  active_surjective : Surjective activeClassifier

namespace LocalizedExactEdgeStep

/-- Forget exactness. -/
def toLocalizedEdgeStep {L : Lollipop} {C E : Set Point}
    (s : LocalizedExactEdgeStep L C E) :
    LocalizedEdgeStep C E where
  active := s.active
  localized := s.localized
  activeClassifier := s.activeClassifier
  active_injective := s.active_injective

/-- Compile one exact localized edge step to a one-step exact split chain. -/
def toExactChain {L : Lollipop} {C E : Set Point}
    (s : LocalizedExactEdgeStep L C E) :
    ComponentSplitChain.ExactChain 1
      ((LocalInsertion.carrierExtension C E)ᶜ) (Cᶜ) :=
  LocalInsertion.exactChainOfLocalizedEdge
    s.old_closed L s.edge_subset_carrier s.active s.localized
    s.activeClassifier s.active_injective s.active_surjective

/-- Compile one exact step to a bounded split chain. -/
def toChain {L : Lollipop} {C E : Set Point}
    (s : LocalizedExactEdgeStep L C E) :
    ComponentSplitChain.Chain 1
      ((LocalInsertion.carrierExtension C E)ᶜ) (Cᶜ) :=
  s.toExactChain.toChain

end LocalizedExactEdgeStep

/-- A finite sequence of localized edge extensions from initial carrier `C` to
final carrier `D`. -/
inductive LocalizedEdgeFiltration :
    ℕ → Set Point → Set Point → Type
  | nil (C : Set Point) : LocalizedEdgeFiltration 0 C C
  | snoc {m : ℕ} {C D : Set Point}
      (head : LocalizedEdgeFiltration m C D)
      (E : Set Point)
      (step : LocalizedEdgeStep D E) :
      LocalizedEdgeFiltration (m + 1) C
        (LocalInsertion.carrierExtension D E)

namespace LocalizedEdgeFiltration

/-- Compile a finite localized edge filtration to a bounded split chain from
the final complement to the initial complement. -/
def toChain :
    ∀ {m : ℕ} {C D : Set Point},
      LocalizedEdgeFiltration m C D →
        ComponentSplitChain.Chain m (Dᶜ) (Cᶜ)
  | 0, C, _, .nil _ => by
      simpa using ComponentSplitChain.Chain.nil (Cᶜ)
  | _m + 1, _C, _, .snoc head _E step => by
      have hstep := step.toChain
      have hhead := toChain head
      simpa [Nat.add_comm] using
        ComponentSplitChain.Chain.trans hstep hhead

end LocalizedEdgeFiltration

/-- Exact finite sequence of localized edge extensions. -/
inductive LocalizedExactEdgeFiltration (L : Lollipop) :
    ℕ → Set Point → Set Point → Type
  | nil (C : Set Point) : LocalizedExactEdgeFiltration L 0 C C
  | snoc {m : ℕ} {C D : Set Point}
      (head : LocalizedExactEdgeFiltration L m C D)
      (E : Set Point)
      (step : LocalizedExactEdgeStep L D E) :
      LocalizedExactEdgeFiltration L (m + 1) C
        (LocalInsertion.carrierExtension D E)

namespace LocalizedExactEdgeFiltration

/-- Compile an exact localized edge filtration to an exact split chain from
the final complement to the initial complement. -/
def toExactChain {L : Lollipop} :
    ∀ {m : ℕ} {C D : Set Point},
      LocalizedExactEdgeFiltration L m C D →
        ComponentSplitChain.ExactChain m (Dᶜ) (Cᶜ)
  | 0, C, _, .nil _ => by
      simpa using ComponentSplitChain.ExactChain.nil (Cᶜ)
  | _m + 1, _C, _, .snoc head _E step => by
      have hstep := step.toExactChain
      have hhead := toExactChain head
      simpa [Nat.add_comm] using
        ComponentSplitChain.ExactChain.trans hstep hhead

/-- Forget exactness after compiling to an exact chain. -/
def toChain {L : Lollipop}
    {m : ℕ} {C D : Set Point}
    (f : LocalizedExactEdgeFiltration L m C D) :
    ComponentSplitChain.Chain m (Dᶜ) (Cᶜ) :=
  f.toExactChain.toChain

end LocalizedExactEdgeFiltration

end LocalFiltration
end EndToEnd
end Concrete
end Lollipop

