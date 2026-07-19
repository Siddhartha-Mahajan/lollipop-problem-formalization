import old_lean_folder.Concrete.EndToEnd.ComponentSplitChain
import old_lean_folder.Concrete.EndToEnd.Support
import Mathlib.Tactic

/-!
# Insertion bookkeeping for the concrete endpoint

This module records the set-level append operation and connects split-chain
component estimates to the actual `regionCount` of lollipop arrangements.
It is deliberately independent of the untrusted Jordan-curve draft code.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Insertion

open Set

/-- Append one lollipop to a finite arrangement. -/
def snocArrangement {n : ℕ} (A : Arrangement n) (L : Lollipop) :
    Arrangement (n + 1) :=
  fun i => if h : i.1 < n then A ⟨i.1, h⟩ else L

@[simp] theorem snocArrangement_castSucc {n : ℕ}
    (A : Arrangement n) (L : Lollipop) (i : Fin n) :
    snocArrangement A L i.castSucc = A i := by
  simp [snocArrangement, i.2]

@[simp] theorem snocArrangement_last {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    snocArrangement A L (Fin.last n) = L := by
  simp [snocArrangement]

/-- An index of `Fin (n+1)` which is not below `n` is the last index. -/
theorem fin_eq_last_of_not_lt {n : ℕ} {i : Fin (n + 1)}
    (hi : ¬ i.1 < n) : i = Fin.last n := by
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- Appending a lollipop adds exactly its carrier to the occupied set. -/
theorem occupied_snocArrangement {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    occupied (snocArrangement A L) = occupied A ∪ L.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_occupied_iff.mp hx
    by_cases hlt : i.1 < n
    · apply Or.inl
      apply mem_occupied_iff.mpr
      refine ⟨⟨i.1, hlt⟩, ?_⟩
      simpa [snocArrangement, hlt] using hi
    · apply Or.inr
      have hieq : i = Fin.last n := fin_eq_last_of_not_lt hlt
      subst i
      simpa using hi
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_occupied_iff.mp hx
      apply mem_occupied_iff.mpr
      exact ⟨i.castSucc, by simpa using hi⟩
    · apply mem_occupied_iff.mpr
      exact ⟨Fin.last n, by simpa using hx⟩

/-- Region count after an append is component count of the complement of the
old occupied carrier union the inserted carrier. -/
theorem regionCount_snoc_eq_componentCount_union_compl
    {n : ℕ} (A : Arrangement n) (L : Lollipop) :
    regionCount (snocArrangement A L) =
      componentCount ((occupied A ∪ L.carrier)ᶜ) := by
  rw [regionCount_eq_componentCount_compl, occupied_snocArrangement]

/-- `FreeSpace A` is the ordinary occupied complement, with the equivalent
predicate made explicit. -/
def freeSpaceHomeomorphOccupiedCompl {n : ℕ} (A : Arrangement n) :
    FreeSpace A ≃ₜ (((occupied A : Set Point)ᶜ) : Set Point) :=
  Homeomorph.setCongr (by
    ext x
    rfl)

/-- Component quotients are invariant under the complement-predicate
homeomorphism. -/
noncomputable def freeSpaceComponentsEquivOccupiedCompl {n : ℕ}
    (A : Arrangement n) :
    ConnectedComponents (FreeSpace A) ≃
      ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point) :=
  connectedComponentsEquivOfHomeomorph
    (freeSpaceHomeomorphOccupiedCompl A)

/-- Finiteness transfer from `FreeSpace A` to the ordinary occupied
complement subtype. -/
theorem finite_occupiedCompl_of_freeSpace {n : ℕ} (A : Arrangement n)
    [Finite (ConnectedComponents (FreeSpace A))] :
    Finite (ConnectedComponents
      (((occupied A : Set Point)ᶜ) : Set Point)) :=
  Finite.of_equiv _ (freeSpaceComponentsEquivOccupiedCompl A)

/-- The appended free space is homeomorphic to the complement of the union of
the old occupied set with the inserted carrier. -/
def freeSpaceSnocHomeomorphUnionCompl {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    FreeSpace (snocArrangement A L) ≃ₜ
      ((((occupied A : Set Point) ∪ L.carrier)ᶜ) : Set Point) :=
  (freeSpaceHomeomorphOccupiedCompl (snocArrangement A L)).trans
    (Homeomorph.setCongr (by
      rw [occupied_snocArrangement]))

/-- Component quotient equivalence for the appended free space. -/
noncomputable def freeSpaceSnocComponentsEquivUnionCompl {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    ConnectedComponents (FreeSpace (snocArrangement A L)) ≃
      ConnectedComponents
        ((((occupied A : Set Point) ∪ L.carrier)ᶜ) : Set Point) :=
  connectedComponentsEquivOfHomeomorph
    (freeSpaceSnocHomeomorphUnionCompl A L)

/-- The new complement is a subset of the old complement after inserting a
carrier. -/
theorem union_compl_subset_occupied_compl {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    (occupied A ∪ L.carrier)ᶜ ⊆ (occupied A)ᶜ := by
  intro x hx hxOld
  exact hx (Or.inl hxOld)

/-- A finite chain of one-component splits for one insertion.  It runs from
the new complement to the old complement. -/
structure InsertionSplitChain {n : ℕ}
    (A : Arrangement n) (L : Lollipop) where
  edgeCount : ℕ
  chain : ComponentSplitChain.Chain edgeCount
    ((occupied A ∪ L.carrier)ᶜ) ((occupied A)ᶜ)

/-- Exact version of `InsertionSplitChain`. -/
structure ExactInsertionSplitChain {n : ℕ}
    (A : Arrangement n) (L : Lollipop) where
  edgeCount : ℕ
  chain : ComponentSplitChain.ExactChain edgeCount
    ((occupied A ∪ L.carrier)ᶜ) ((occupied A)ᶜ)

/-- Exact insertion chains can be used as bounded insertion chains. -/
def ExactInsertionSplitChain.toInsertionSplitChain
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    (h : ExactInsertionSplitChain A L) : InsertionSplitChain A L where
  edgeCount := h.edgeCount
  chain := h.chain.toChain

/-- Finiteness of old complement components propagates through a split-chain
insertion. -/
theorem finite_newComponents_of_insertionSplitChain
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    [Finite (ConnectedComponents (FreeSpace A))]
    (h : InsertionSplitChain A L) :
    Finite (ConnectedComponents
      (FreeSpace (snocArrangement A L))) := by
  haveI : Finite
      (ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point)) :=
    finite_occupiedCompl_of_freeSpace A
  have hnew : Finite
      (ConnectedComponents
        ((((occupied A : Set Point) ∪ L.carrier)ᶜ) : Set Point)) :=
    h.chain.finite_source
  exact Finite.of_equiv _
    (freeSpaceSnocComponentsEquivUnionCompl A L).symm

/-- A bounded split-chain insertion raises region count by at most the chain
length. -/
theorem regionCount_snoc_le_add_edgeCount
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    [Finite (ConnectedComponents (FreeSpace A))]
    (h : InsertionSplitChain A L) :
    regionCount (snocArrangement A L) ≤ regionCount A + h.edgeCount := by
  haveI : Finite
      (ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point)) :=
    finite_occupiedCompl_of_freeSpace A
  rw [regionCount_snoc_eq_componentCount_union_compl,
    regionCount_eq_componentCount_compl A]
  exact h.chain.componentCount_le

/-- An exact split-chain insertion gives the exact region-count increment. -/
theorem regionCount_snoc_eq_add_edgeCount
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    [Finite (ConnectedComponents (FreeSpace A))]
    (h : ExactInsertionSplitChain A L) :
    regionCount (snocArrangement A L) = regionCount A + h.edgeCount := by
  haveI : Finite
      (ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point)) :=
    finite_occupiedCompl_of_freeSpace A
  rw [regionCount_snoc_eq_componentCount_union_compl,
    regionCount_eq_componentCount_compl A]
  exact h.chain.componentCount_eq

end Insertion
end EndToEnd
end Concrete
end Lollipop
