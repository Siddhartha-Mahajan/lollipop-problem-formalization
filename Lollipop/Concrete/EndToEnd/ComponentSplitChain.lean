import Lollipop.Concrete.EndToEnd.ComponentFibers
import Mathlib.Tactic

/-!
# Finite chains of one-component splits

This file iterates the quotient-level fibre-count theorem from
`ComponentFibers`.  A chain runs from the smaller free set to the larger free
set.  Each step is an inclusion whose component map has at most one
two-element fibre, so an `m`-step chain raises component count by at most `m`;
exact split data give equality.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ComponentSplitChain

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A finite sequence of inclusions, each carrying a one-component split
certificate.  `snoc` appends the last inclusion. -/
inductive Chain : (m : ℕ) → Set X → Set X → Type u
  | nil (S : Set X) : Chain 0 S S
  | snoc {m : ℕ} {S T U : Set X}
      (head : Chain m S T)
      (hTU : T ⊆ U)
      (split : ComponentFibers.OneComponentSplitData hTU) :
      Chain (m + 1) S U

/-- A one-step chain. -/
noncomputable def Chain.singleton {S T : Set X}
    (hST : S ⊆ T) (split : ComponentFibers.OneComponentSplitData hST) :
    Chain 1 S T := by
  simpa using Chain.snoc (Chain.nil S) hST split

/-- Concatenation of split chains. -/
noncomputable def Chain.trans {m : ℕ} {S T : Set X}
    (left : Chain m S T) :
    ∀ {k : ℕ} {U : Set X}, Chain k T U → Chain (m + k) S U
  | 0, _, .nil _ => by simpa using left
  | _, _, .snoc head hVU split => by
      simpa [Nat.add_assoc] using
        Chain.snoc (Chain.trans left head) hVU split

/-- Explicit finiteness propagation along a chain. -/
@[reducible] noncomputable def Chain.finiteSourceExplicit :
    ∀ {m : ℕ} {S T : Set X}, Chain m S T →
      Finite (ConnectedComponents T) → Finite (ConnectedComponents S)
  | 0, _, _, .nil _, hfinite => hfinite
  | _, _, _, .snoc head hTU split, hfinite => by
      letI : Finite (ConnectedComponents _) := hfinite
      let hmiddle : Finite (ConnectedComponents _) :=
        ComponentFibers.finite_source_of_oneComponentSplit hTU split
      exact Chain.finiteSourceExplicit head hmiddle

/-- Typeclass form of finiteness propagation. -/
theorem Chain.finite_source {m : ℕ} {S T : Set X}
    (_chain : Chain m S T) [Finite (ConnectedComponents T)] :
    Finite (ConnectedComponents S) :=
  Chain.finiteSourceExplicit _chain inferInstance

/-- Explicit component-count bound along a chain. -/
theorem Chain.componentCount_le_explicit :
    ∀ {m : ℕ} {S T : Set X} (_chain : Chain m S T),
      Finite (ConnectedComponents T) →
      componentCount S ≤ componentCount T + m
  | 0, _, _, .nil _, _ => by simp
  | _, _, _, .snoc head hTU split, hfinite => by
      letI : Finite (ConnectedComponents _) := hfinite
      let hmiddle : Finite (ConnectedComponents _) :=
        ComponentFibers.finite_source_of_oneComponentSplit hTU split
      letI : Finite (ConnectedComponents _) := hmiddle
      have hhead := Chain.componentCount_le_explicit head hmiddle
      have hlast :=
        ComponentFibers.componentCount_le_add_one_of_oneComponentSplit hTU split
      omega

/-- An `m`-step split chain raises component count by at most `m`. -/
theorem Chain.componentCount_le {m : ℕ} {S T : Set X}
    (chain : Chain m S T) [Finite (ConnectedComponents T)] :
    componentCount S ≤ componentCount T + m :=
  Chain.componentCount_le_explicit chain inferInstance

/-- Exact analogue of `Chain`. -/
inductive ExactChain : (m : ℕ) → Set X → Set X → Type u
  | nil (S : Set X) : ExactChain 0 S S
  | snoc {m : ℕ} {S T U : Set X}
      (head : ExactChain m S T)
      (hTU : T ⊆ U)
      (split : ComponentFibers.ExactOneComponentSplitData hTU) :
      ExactChain (m + 1) S U

/-- Forget exactness. -/
noncomputable def ExactChain.toChain :
    ∀ {m : ℕ} {S T : Set X}, ExactChain m S T → Chain m S T
  | 0, _, _, .nil S => .nil S
  | _, _, _, .snoc head hTU split =>
      .snoc (ExactChain.toChain head) hTU split.toOneComponentSplitData

/-- A one-step exact chain. -/
noncomputable def ExactChain.singleton {S T : Set X}
    (hST : S ⊆ T) (split : ComponentFibers.ExactOneComponentSplitData hST) :
    ExactChain 1 S T := by
  simpa using ExactChain.snoc (ExactChain.nil S) hST split

/-- Concatenation of exact chains. -/
noncomputable def ExactChain.trans {m : ℕ} {S T : Set X}
    (left : ExactChain m S T) :
    ∀ {k : ℕ} {U : Set X}, ExactChain k T U → ExactChain (m + k) S U
  | 0, _, .nil _ => by simpa using left
  | _, _, .snoc head hVU split => by
      simpa [Nat.add_assoc] using
        ExactChain.snoc (ExactChain.trans left head) hVU split

/-- Exact chains inherit finiteness propagation. -/
theorem ExactChain.finite_source {m : ℕ} {S T : Set X}
    (_chain : ExactChain m S T) [Finite (ConnectedComponents T)] :
    Finite (ConnectedComponents S) :=
  _chain.toChain.finite_source

/-- Explicit exact component-count recurrence. -/
theorem ExactChain.componentCount_eq_explicit :
    ∀ {m : ℕ} {S T : Set X} (_chain : ExactChain m S T),
      Finite (ConnectedComponents T) →
      componentCount S = componentCount T + m
  | 0, _, _, .nil _, _ => by simp
  | _, _, _, .snoc head hTU split, hfinite => by
      letI : Finite (ConnectedComponents _) := hfinite
      let hmiddle : Finite (ConnectedComponents _) :=
        ComponentFibers.finite_source_of_oneComponentSplit hTU
          split.toOneComponentSplitData
      letI : Finite (ConnectedComponents _) := hmiddle
      have hhead := ExactChain.componentCount_eq_explicit head hmiddle
      have hlast :=
        ComponentFibers.componentCount_eq_add_one_of_exactOneComponentSplit hTU split
      omega

/-- An exact `m`-step chain raises component count by exactly `m`. -/
theorem ExactChain.componentCount_eq {m : ℕ} {S T : Set X}
    (chain : ExactChain m S T) [Finite (ConnectedComponents T)] :
    componentCount S = componentCount T + m :=
  ExactChain.componentCount_eq_explicit chain inferInstance

end ComponentSplitChain
end EndToEnd
end Concrete
end Lollipop
