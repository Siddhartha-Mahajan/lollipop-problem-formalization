import Lollipop.Concrete.EndToEnd.ComponentSurjectivity
import Lollipop.Concrete.EndToEnd.Insertion
import Mathlib.Tactic

/-!
# Closed occupied sets for concrete arrangements

This file supplies the finite-union topology needed by the insertion split
route.  The old occupied carrier of any finite concrete arrangement is closed,
so the exact insertion-surjectivity lemma from `ComponentSurjectivity` applies
to the actual complement inclusion used by `Insertion.InsertionSplitChain`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace OccupiedTopology

open Set

/-- The occupied set is a finite union of concrete lollipop carriers. -/
theorem occupied_eq_iUnion {n : ℕ} (A : Arrangement n) :
    occupied A = ⋃ i : Fin n, (A i).carrier := rfl

/-- Every finite concrete arrangement has a closed occupied carrier. -/
theorem isClosed_occupied {n : ℕ} (A : Arrangement n) :
    IsClosed (occupied A) := by
  rw [occupied_eq_iUnion]
  exact isClosed_iUnion_of_finite fun i => Lollipop.isClosed_carrier (A i)

/-- The ambient complement of an arrangement is open. -/
theorem isOpen_occupied_compl {n : ℕ} (A : Arrangement n) :
    IsOpen (occupied A)ᶜ :=
  (isClosed_occupied A).isOpen_compl

/-- The old carrier is contained in the carrier after inserting one lollipop. -/
theorem occupied_subset_inserted {n : ℕ} (A : Arrangement n)
    (L : Lollipop) :
    occupied A ⊆ occupied A ∪ L.carrier :=
  fun _ hx => Or.inl hx

/-- The generic complement inclusion from `ComponentSurjectivity` specializes
definitionally to the insertion complement inclusion used by
`Insertion.InsertionSplitChain`. -/
theorem complementSubset_occupied_subset_inserted
    {n : ℕ} (A : Arrangement n) (L : Lollipop) :
    ComponentSurjectivity.complementSubset
        (occupied_subset_inserted A L) =
      Insertion.union_compl_subset_occupied_compl A L := by
  rfl

/-- Inserting one lollipop carrier does not erase any connected component of
the old complement. -/
theorem insertion_componentMap_surjective
    {n : ℕ} (A : Arrangement n) (L : Lollipop) :
    Function.Surjective
      (ComponentFibers.inclusionMap
        (Insertion.union_compl_subset_occupied_compl A L)) := by
  have h :
      Function.Surjective
        (ComponentFibers.inclusionMap
          (ComponentSurjectivity.complementSubset
            (occupied_subset_inserted A L))) :=
    ComponentSurjectivity.componentMap_surjective_of_closed_of_subset_union_carrier
      (occupied_subset_inserted A L) (isClosed_occupied A) L
      (by intro x hx; exact hx)
  simpa [complementSubset_occupied_subset_inserted] using h

end OccupiedTopology
end EndToEnd
end Concrete
end Lollipop
