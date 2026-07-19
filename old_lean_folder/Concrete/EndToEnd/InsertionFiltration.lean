import old_lean_folder.Concrete.EndToEnd.Insertion
import old_lean_folder.Concrete.EndToEnd.LocalFiltration

/-!
# Local filtrations as insertion split chains

The ordered-insertion topology reduction consumes
`Insertion.InsertionSplitChain` and `Insertion.ExactInsertionSplitChain`.
This file shows that a localized finite edge filtration whose final carrier is
the whole inserted lollipop carrier produces exactly those objects.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace InsertionFiltration

/-- Bounded localized filtration for inserting `L` into an arrangement `A`. -/
abbrev LocalizedInsertionFiltration {n : ℕ}
    (A : Arrangement n) (L : Lollipop) (m : ℕ) :=
  LocalFiltration.LocalizedEdgeFiltration m
    (occupied A) (occupied A ∪ L.carrier)

/-- Exact localized filtration for inserting `L` into an arrangement `A`. -/
abbrev LocalizedExactInsertionFiltration {n : ℕ}
    (A : Arrangement n) (L : Lollipop) (m : ℕ) :=
  LocalFiltration.LocalizedExactEdgeFiltration L m
    (occupied A) (occupied A ∪ L.carrier)

/-- A localized insertion filtration compiles to the insertion split-chain
object used by the global topology reduction. -/
def insertionSplitChainOfLocalizedFiltration
    {n m : ℕ} {A : Arrangement n} {L : Lollipop}
    (f : LocalizedInsertionFiltration A L m) :
    Insertion.InsertionSplitChain A L where
  edgeCount := m
  chain := f.toChain

/-- An exact localized insertion filtration compiles to the exact insertion
split-chain object used by the generic Euler equality reduction. -/
def exactInsertionSplitChainOfLocalizedFiltration
    {n m : ℕ} {A : Arrangement n} {L : Lollipop}
    (f : LocalizedExactInsertionFiltration A L m) :
    Insertion.ExactInsertionSplitChain A L where
  edgeCount := m
  chain := f.toExactChain

end InsertionFiltration
end EndToEnd
end Concrete
end Lollipop

