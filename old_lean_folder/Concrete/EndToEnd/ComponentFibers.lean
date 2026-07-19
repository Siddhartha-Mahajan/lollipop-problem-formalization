import old_lean_folder.Concrete.EndToEnd.Compactification
import Mathlib.Data.Finite.Card
import Mathlib.Tactic

/-!
# Connected-component fibre bookkeeping

This module contains generic quotient-level cardinality lemmas for inclusions
of subspaces.  It is intended for the eventual planar insertion proof: if a
new carrier splits at most one old complementary component into two pieces,
then the total number of connected components rises by at most one, and exact
two-sided splitting gives equality.

No planar geometry is assumed here.  All maps are induced by actual continuous
subtype inclusions and Mathlib's `ConnectedComponents` quotient.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ComponentFibers

open Set Function BigOperators

universe u v

/-- The fibre of a function over a point, packaged as a subtype. -/
abbrev Fiber {A : Type u} {B : Type v} (f : A → B) (b : B) :=
  {a : A // f a = b}

/-- Every type is equivalent to the sigma type of the fibres of a function. -/
noncomputable def fiberSigmaEquiv {A : Type u} {B : Type v} (f : A → B) :
    A ≃ Σ b : B, Fiber f b where
  toFun a := ⟨f a, ⟨a, rfl⟩⟩
  invFun x := x.2.1
  left_inv := by intro a; rfl
  right_inv := by rintro ⟨b, a, ha⟩; subst b; rfl

section ComponentMaps

variable {X : Type u} [TopologicalSpace X]

/-- Inclusion of one set into another, as a continuous subtype map. -/
def inclusion {S T : Set X} (hST : S ⊆ T) : S → T :=
  fun x => ⟨x.1, hST x.2⟩

theorem continuous_inclusion {S T : Set X} (hST : S ⊆ T) :
    Continuous (inclusion hST) :=
  Continuous.subtype_mk continuous_subtype_val (fun x => hST x.2)

/-- Component map induced by a set inclusion. -/
def inclusionMap {S T : Set X} (hST : S ⊆ T) :
    ConnectedComponents S → ConnectedComponents T :=
  (continuous_inclusion hST).connectedComponentsMap

@[simp] theorem inclusionMap_mk {S T : Set X}
    (hST : S ⊆ T) (x : S) :
    inclusionMap hST (ConnectedComponents.mk x) =
      ConnectedComponents.mk (inclusion hST x) := by
  simp [inclusionMap]

/-- A component map is surjective once every target point is component-related
to a point in the source. -/
theorem inclusionMap_surjective_of_component_meets
    {S T : Set X} (hST : S ⊆ T)
    (hmeet : ∀ y : T, ∃ x : S,
      ConnectedComponents.mk (inclusion hST x) = ConnectedComponents.mk y) :
    Surjective (inclusionMap hST) := by
  intro c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨x, hx⟩ := hmeet y
  exact ⟨ConnectedComponents.mk x, by simpa [inclusionMap] using hx⟩

end ComponentMaps

section FibreCardinality

variable {A : Type u} {B : Type v}
variable (f : A → B)

/-- A subsingleton fibre is finite. -/
theorem finite_fiber_of_subsingleton
    (b : B) [Subsingleton (Fiber f b)] :
    Finite (Fiber f b) :=
  Finite.of_injective (fun _ : Fiber f b => PUnit.unit)
    (fun a c _ => Subsingleton.elim a c)

/-- Fibrewise finiteness implies finiteness of the source. -/
theorem finite_source_of_finite_fibers
    [Finite B]
    (hfinite : ∀ b : B, Finite (Fiber f b)) :
    Finite A := by
  letI : ∀ b : B, Finite (Fiber f b) := hfinite
  exact Finite.of_injective (fiberSigmaEquiv f).toFun
    (fiberSigmaEquiv f).injective

/-- Cardinality of a source as a sum of cardinalities of its fibres. -/
theorem natCard_eq_sum_fibers
    [Fintype B]
    (hfinite : ∀ b : B, Finite (Fiber f b)) :
    Nat.card A = ∑ b : B, Nat.card (Fiber f b) := by
  letI : ∀ b : B, Finite (Fiber f b) := hfinite
  rw [Nat.card_congr (fiberSigmaEquiv f), Nat.card_sigma]

end FibreCardinality

private theorem sum_if_eq_two_else_one
    {β : Type*} [Fintype β] [DecidableEq β] (a : β) :
    (∑ b : β, if b = a then (2 : ℕ) else 1) = Fintype.card β + 1 := by
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ) (i := a)
    (f := fun b => if b = a then (2 : ℕ) else 1) (by simp)]
  have hsum :
      (∑ x ∈ Finset.univ \ {a}, if x = a then (2 : ℕ) else 1) =
        ∑ x ∈ Finset.univ \ {a}, (1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp at hx
    simp [hx]
  rw [hsum]
  have hsumConst :
      (∑ x ∈ Finset.univ \ {a}, (1 : ℕ)) =
        (Finset.univ \ {a}).card := by
    simp
  rw [hsumConst]
  have hcard :
      (Finset.univ \ {a}).card = Fintype.card β - 1 := by
    rw [Finset.card_sdiff]
    simp
  have hpos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hcard]
  simp only [if_true]
  omega

section SplitBound

variable {X : Type u} [TopologicalSpace X]
variable {S T : Set X} (hST : S ⊆ T)

/-- Quotient-level data saying that only one target component may split, and
it has at most two source components above it. -/
structure OneComponentSplitData where
  active : ConnectedComponents T
  activeClassifier : Fiber (inclusionMap hST) active → Fin 2
  active_injective : Injective activeClassifier
  inactive_subsingleton :
    ∀ b : ConnectedComponents T, b ≠ active →
      Subsingleton (Fiber (inclusionMap hST) b)

/-- Exact splitting data: every target component survives and the active fibre
contains both values of its two-valued classifier. -/
structure ExactOneComponentSplitData extends OneComponentSplitData hST where
  componentMap_surjective : Surjective (inclusionMap hST)
  activeSide_surjective : Surjective activeClassifier

/-- The split data make every source fibre finite. -/
theorem finite_fiber_of_oneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    ∀ b : ConnectedComponents T,
      Finite (Fiber (inclusionMap hST) b) := by
  intro b
  by_cases hb : b = d.active
  · subst b
    exact Finite.of_injective d.activeClassifier d.active_injective
  · letI : Subsingleton (Fiber (inclusionMap hST) b) :=
      d.inactive_subsingleton b hb
    exact finite_fiber_of_subsingleton (inclusionMap hST) b

/-- In particular, finite target component count implies finite source
component count under one-component split data. -/
theorem finite_source_of_oneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    Finite (ConnectedComponents S) :=
  finite_source_of_finite_fibers (inclusionMap hST)
    (finite_fiber_of_oneComponentSplit hST d)

/-- The active fibre has cardinality at most two. -/
theorem active_fiber_natCard_le_two
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    Nat.card (Fiber (inclusionMap hST) d.active) ≤ 2 := by
  simpa using
    (Nat.card_le_card_of_injective d.activeClassifier d.active_injective)

/-- Every inactive fibre has cardinality at most one. -/
theorem inactive_fiber_natCard_le_one
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST)
    (b : ConnectedComponents T) (hb : b ≠ d.active) :
    Nat.card (Fiber (inclusionMap hST) b) ≤ 1 := by
  letI : Subsingleton (Fiber (inclusionMap hST) b) :=
    d.inactive_subsingleton b hb
  calc
    Nat.card (Fiber (inclusionMap hST) b) ≤ Nat.card Unit :=
      Nat.card_le_card_of_injective
        (fun _ : Fiber (inclusionMap hST) b => ())
        (fun a c _ => Subsingleton.elim a c)
    _ = 1 := by simp

/-- One target component with at most two descendants and all other target
components with at most one descendant give the sharp `+1` upper bound. -/
theorem componentCount_le_add_one_of_oneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    componentCount S ≤ componentCount T + 1 := by
  classical
  letI : Fintype (ConnectedComponents T) :=
    Fintype.ofFinite (ConnectedComponents T)
  let hfinite := finite_fiber_of_oneComponentSplit hST d
  letI : ∀ b : ConnectedComponents T,
      Finite (Fiber (inclusionMap hST) b) := hfinite
  letI : Finite (ConnectedComponents S) :=
    finite_source_of_oneComponentSplit hST d
  unfold componentCount
  rw [natCard_eq_sum_fibers (inclusionMap hST) hfinite]
  calc
    (∑ b : ConnectedComponents T,
        Nat.card (Fiber (inclusionMap hST) b)) ≤
        ∑ b : ConnectedComponents T,
          (if b = d.active then 2 else 1) := by
      exact Finset.sum_le_sum fun b _ => by
        by_cases hb : b = d.active
        · subst b
          simpa using active_fiber_natCard_le_two hST d
        · simpa [hb] using inactive_fiber_natCard_le_one hST d b hb
    _ = Nat.card (ConnectedComponents T) + 1 := by
      simpa [Nat.card_eq_fintype_card] using
        sum_if_eq_two_else_one d.active

/-- Exact data force the active fibre to have exactly two elements. -/
theorem active_fiber_natCard_eq_two
    [Finite (ConnectedComponents T)]
    (d : ExactOneComponentSplitData hST) :
    Nat.card (Fiber (inclusionMap hST) d.active) = 2 := by
  let e : Fiber (inclusionMap hST) d.active ≃ Fin 2 :=
    Equiv.ofBijective d.activeClassifier
      ⟨d.active_injective, d.activeSide_surjective⟩
  calc
    Nat.card (Fiber (inclusionMap hST) d.active) = Nat.card (Fin 2) :=
      Nat.card_congr e
    _ = 2 := by simp

/-- Surjectivity of the component map makes every inactive subsingleton fibre
have exactly one element. -/
theorem inactive_fiber_natCard_eq_one
    [Finite (ConnectedComponents T)]
    (d : ExactOneComponentSplitData hST)
    (b : ConnectedComponents T) (hb : b ≠ d.active) :
    Nat.card (Fiber (inclusionMap hST) b) = 1 := by
  letI : Subsingleton (Fiber (inclusionMap hST) b) :=
    d.inactive_subsingleton b hb
  have hnon : Nonempty (Fiber (inclusionMap hST) b) := by
    obtain ⟨a, ha⟩ := d.componentMap_surjective b
    exact ⟨⟨a, ha⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hnon⟩

/-- Exact one-component splitting raises component count by exactly one. -/
theorem componentCount_eq_add_one_of_exactOneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : ExactOneComponentSplitData hST) :
    componentCount S = componentCount T + 1 := by
  classical
  letI : Fintype (ConnectedComponents T) :=
    Fintype.ofFinite (ConnectedComponents T)
  let hfinite := finite_fiber_of_oneComponentSplit hST d.toOneComponentSplitData
  letI : ∀ b : ConnectedComponents T,
      Finite (Fiber (inclusionMap hST) b) := hfinite
  letI : Finite (ConnectedComponents S) :=
    finite_source_of_oneComponentSplit hST d.toOneComponentSplitData
  unfold componentCount
  rw [natCard_eq_sum_fibers (inclusionMap hST) hfinite]
  calc
    (∑ b : ConnectedComponents T,
        Nat.card (Fiber (inclusionMap hST) b)) =
        ∑ b : ConnectedComponents T,
          (if b = d.active then 2 else 1) := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hb : b = d.active
      · subst b
        simpa using active_fiber_natCard_eq_two hST d
      · simpa [hb] using inactive_fiber_natCard_eq_one hST d b hb
    _ = Nat.card (ConnectedComponents T) + 1 := by
      simpa [Nat.card_eq_fintype_card] using
        sum_if_eq_two_else_one d.active

end SplitBound

end ComponentFibers
end EndToEnd
end Concrete
end Lollipop
