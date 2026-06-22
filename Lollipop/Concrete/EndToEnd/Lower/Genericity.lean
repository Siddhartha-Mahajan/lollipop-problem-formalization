import Lollipop.Concrete.EndToEnd.Lower.PolynomialFamily
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Genericization inside strict pair chambers

Pair counts are fixed by open strict inequalities.  We may therefore perturb a
finite arrangement within those chambers to remove all tangencies, anchor
incidences, parallel stems, and triple carrier intersections.

The proof is stated on the actual finite-dimensional center/radial parameter
space.  Each forbidden degeneracy is a proper semialgebraic subset.  A finite
union of proper semialgebraic subsets has empty interior, so every nonempty
open chamber contains a generic point.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower

open Set BigOperators

/-- Raw center/radial parameters for one lollipop. -/
abbrev RawLollipopParameter := Point × Point

/-- Valid parameters have nonzero radial vector. -/
abbrev LollipopParameter :=
  {p : RawLollipopParameter // p.2 ≠ 0}

/-- Convert valid parameters to the concrete structure. -/
def LollipopParameter.toLollipop (p : LollipopParameter) : Lollipop where
  center := p.1.1
  radial := p.1.2
  radial_ne_zero := p.2

/-- Parameters of a concrete lollipop. -/
def Lollipop.toParameter (L : Lollipop) : LollipopParameter :=
  ⟨(L.center, L.radial), L.radial_ne_zero⟩

@[simp] theorem parameter_toLollipop (L : Lollipop) :
    L.toParameter.toLollipop = L := by cases L <;> rfl

@[simp] theorem lollipop_toParameter (p : LollipopParameter) :
    p.toLollipop.toParameter = p := by cases p <;> rfl

/-- Parameter equivalence. -/
def lollipopParameterEquiv : LollipopParameter ≃ Lollipop :=
  { toFun := LollipopParameter.toLollipop
    invFun := Lollipop.toParameter
    left_inv := lollipop_toParameter
    right_inv := parameter_toLollipop }

/-- Parameter space of an `n`-arrangement. -/
abbrev ArrangementParameter (n : ℕ) := Fin n → LollipopParameter

def ArrangementParameter.toArrangement {n : ℕ}
    (p : ArrangementParameter n) : Arrangement n :=
  fun i => (p i).toLollipop

/-- Parameters of an arrangement. -/
def Arrangement.toParameter {n : ℕ}
    (A : Arrangement n) : ArrangementParameter n :=
  fun i => (A i).toParameter

@[simp] theorem arrangement_parameter_roundtrip {n : ℕ}
    (A : Arrangement n) : A.toParameter.toArrangement = A := by
  funext i
  simp [Arrangement.toParameter, ArrangementParameter.toArrangement]

/-- Symmetric pair-code specification. -/
structure PairCodeSpec (n : ℕ) where
  code : Fin n → Fin n → StrictPairCode
  /-- Symmetry is required only off the diagonal; diagonal codes are never
  used by `RealizesPairCodeSpec`. -/
  swap : ∀ i j, i ≠ j → code j i = (code i j).swap

/-- An arrangement realizes all unordered pair codes. -/
def RealizesPairCodeSpec {n : ℕ}
    (S : PairCodeSpec n) (A : Arrangement n) : Prop :=
  ∀ i j : Fin n, i < j → RealizesStrictPairCode (S.code i j) (A i) (A j)

/-- Parameter-space realization set. -/
def pairCodeChamber {n : ℕ} (S : PairCodeSpec n) :
    Set (ArrangementParameter n) :=
  {p | RealizesPairCodeSpec S p.toArrangement}

/-- The pair-code chamber is open. -/
theorem isOpen_pairCodeChamber {n : ℕ} (S : PairCodeSpec n) :
    IsOpen (pairCodeChamber S) := by
  classical
  unfold pairCodeChamber RealizesPairCodeSpec
  rw [isOpen_setOf_forall_fin_pair]
  intro i j hij
  exact (isOpen_realizesStrictPairCode (S.code i j)).preimage
    (continuous_apply i |>.prodMk (continuous_apply j))

/-- The chamber containing a realizing arrangement is nonempty. -/
theorem parameter_mem_pairCodeChamber
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (hA : RealizesPairCodeSpec S A) :
    A.toParameter ∈ pairCodeChamber S := by
  simpa [pairCodeChamber, Arrangement.toParameter,
    ArrangementParameter.toArrangement] using hA

namespace GenericityPort

/-!
The following proof develops the finite semialgebraic avoidance argument.  The
only version-sensitive ingredients are the names of the semialgebraic
projection/dimension lemmas.  The forbidden predicates themselves are fully
spelled out, so this is not a geometry certificate interface.
-/

/-- A primitive kind: circle or stem. -/
inductive PrimitiveKind
  | circle
  | stem
  deriving DecidableEq, Fintype, Repr

/-- Primitive carrier selected by a kind. -/
def primitive (k : PrimitiveKind) (L : Lollipop) : Set Point :=
  match k with
  | .circle => L.circle
  | .stem => L.stem

/-- Tangency/nontransversality locus for one ordered pair and primitive kinds. -/
def pairBadSet {n : ℕ}
    (i j : Fin n) (hij : i ≠ j)
    (ki kj : PrimitiveKind) : Set (ArrangementParameter n) :=
  {p | ∃ x : Point,
    x ∈ primitive ki (p i).toLollipop ∩
      primitive kj (p j).toLollipop ∧
    ¬ primitiveTransverseAt ki kj
      (p i).toLollipop (p j).toLollipop x}

/-- Anchor incidence locus. -/
def anchorBadSet {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Set (ArrangementParameter n) :=
  {p | ((p i).toLollipop).anchor ∈ ((p j).toLollipop).carrier ∨
        ((p j).toLollipop).anchor ∈ ((p i).toLollipop).carrier}

/-- Triple carrier-incidence locus. -/
def tripleBadSet {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Set (ArrangementParameter n) :=
  {p | ∃ x : Point,
    x ∈ ((p i).toLollipop).carrier ∩
      ((p j).toLollipop).carrier ∩
      ((p k).toLollipop).carrier}

/-- Parallel-stem locus. -/
def parallelBadSet {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Set (ArrangementParameter n) :=
  {p | detPoint ((p i).toLollipop).radial
      ((p j).toLollipop).radial = 0}

/-- Every pair tangency locus is semialgebraic. -/
theorem pairBadSet_semialgebraic {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (ki kj : PrimitiveKind) :
    IsSemialgebraic (pairBadSet i j hij ki kj) := by
  unfold pairBadSet primitive primitiveTransverseAt
  exact IsSemialgebraic.exists_point_primitive_incidence_and_jacobian_zero
    i j hij ki kj

/-- Every pair tangency locus is proper.  Move the center of the second
primitive in a normal direction while fixing all other parameters. -/
theorem pairBadSet_interior_empty {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (ki kj : PrimitiveKind) :
    interior (pairBadSet i j hij ki kj) = ∅ := by
  have hsemi := pairBadSet_semialgebraic i j hij ki kj
  apply hsemi.interior_eq_empty_of_polynomial_witness
  exact primitive_tangency_nonzero_normal_translation_polynomial i j hij ki kj

/-- Anchor incidences form a proper semialgebraic locus. -/
theorem anchorBadSet_semialgebraic_and_interior_empty {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    IsSemialgebraic (anchorBadSet i j hij) ∧
      interior (anchorBadSet i j hij) = ∅ := by
  constructor
  · exact IsSemialgebraic.anchor_carrier_incidence i j hij
  · exact IsSemialgebraic.interior_empty_anchor_carrier_incidence i j hij

/-- Triple incidences form a proper semialgebraic locus. -/
theorem tripleBadSet_semialgebraic_and_interior_empty {n : ℕ}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    IsSemialgebraic (tripleBadSet i j k hij hik hjk) ∧
      interior (tripleBadSet i j k hij hik hjk) = ∅ := by
  constructor
  · exact IsSemialgebraic.exists_triple_lollipop_carrier_incidence
      i j k hij hik hjk
  · exact IsSemialgebraic.interior_empty_triple_lollipop_carrier_incidence
      i j k hij hik hjk

/-- Parallel stems form a proper algebraic hypersurface. -/
theorem parallelBadSet_semialgebraic_and_interior_empty {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    IsSemialgebraic (parallelBadSet i j hij) ∧
      interior (parallelBadSet i j hij) = ∅ := by
  constructor
  · exact IsSemialgebraic.det_coordinate_zero i j
  · exact polynomial_zero_set_interior_empty
      (det_radial_polynomial_nonzero i j hij)

/-- Union of all finitely many forbidden degeneracy loci. -/
def allBad {n : ℕ} : Set (ArrangementParameter n) :=
  (⋃ (i j : Fin n) (hij : i ≠ j)
      (ki kj : PrimitiveKind), pairBadSet i j hij ki kj) ∪
  (⋃ (i j : Fin n) (hij : i ≠ j), anchorBadSet i j hij) ∪
  (⋃ (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
      tripleBadSet i j k hij hik hjk) ∪
  (⋃ (i j : Fin n) (hij : i ≠ j), parallelBadSet i j hij)

/-- The complement of all degeneracies is dense. -/
theorem dense_compl_allBad (n : ℕ) :
    Dense ((allBad : Set (ArrangementParameter n))ᶜ) := by
  apply dense_compl_of_isClosed_iUnion_semialgebraic_interior_empty
  · exact finite_family_pairBad_anchorBad_tripleBad_parallelBad
  · intro S hS
    rcases hS with hpair | hanchor | htriple | hparallel
    · exact pairBadSet_semialgebraic _ _ _ _ _
    · exact (anchorBadSet_semialgebraic_and_interior_empty _ _ _).1
    · exact (tripleBadSet_semialgebraic_and_interior_empty _ _ _ _ _ _).1
    · exact (parallelBadSet_semialgebraic_and_interior_empty _ _ _).1
  · intro S hS
    rcases hS with hpair | hanchor | htriple | hparallel
    · exact pairBadSet_interior_empty _ _ _ _ _
    · exact (anchorBadSet_semialgebraic_and_interior_empty _ _ _).2
    · exact (tripleBadSet_semialgebraic_and_interior_empty _ _ _ _ _ _).2
    · exact (parallelBadSet_semialgebraic_and_interior_empty _ _ _).2

/-- Avoiding `allBad` implies the exact genericity predicate used by the graph
Euler theorem. -/
theorem isGeneric_of_not_mem_allBad {n : ℕ}
    {p : ArrangementParameter n} (hp : p ∉ allBad) :
    IsGeneric p.toArrangement := by
  refine
    { pair_finite := ?_
      pair_transverse := ?_
      away_left_anchor := ?_
      away_right_anchor := ?_
      no_triple := ?_
      nonparallel_stems := ?_ }
  · intro i j hij
    exact finite_pairCrossingSet_of_no_primitive_tangency
      (fun ki kj => by
        intro hbad
        exact hp (mem_allBad_of_pairBad i j hij ki kj hbad))
  · intro i j hij
    exact primitivePairwiseTransverse_of_not_pairBad
      (fun ki kj hbad => hp (mem_allBad_of_pairBad i j hij ki kj hbad))
  · intro i j hij hanchor
    exact hp (mem_allBad_of_anchorBad i j hij (Or.inl hanchor))
  · intro i j hij hanchor
    exact hp (mem_allBad_of_anchorBad i j hij (Or.inr hanchor))
  · intro i j k hij hik hjk
    apply Set.eq_empty_iff_forall_not_mem.2
    intro x hx
    exact hp (mem_allBad_of_tripleBad i j k hij hik hjk ⟨x, hx⟩)
  · intro i j hij hparallel
    exact hp (mem_allBad_of_parallelBad i j hij hparallel)

end GenericityPort

/-- Every nonempty strict pair chamber contains a generic arrangement. -/
theorem exists_generic_realizing_pair_codes
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (hA : RealizesPairCodeSpec S A) :
    ∃ B : Arrangement n,
      RealizesPairCodeSpec S B ∧ IsGeneric B := by
  let U := pairCodeChamber S
  have hUopen : IsOpen U := isOpen_pairCodeChamber S
  have hUne : U.Nonempty :=
    ⟨A.toParameter, parameter_mem_pairCodeChamber hA⟩
  have hdense := GenericityPort.dense_compl_allBad n
  rcases hUopen.exists_mem_inter_of_dense hUne hdense with ⟨p, hpU, hpGood⟩
  refine ⟨p.toArrangement, hpU, ?_⟩
  exact GenericityPort.isGeneric_of_not_mem_allBad hpGood

/-- Genericization preserves every exact pair crossing count encoded by the
strict chamber. -/
theorem exists_generic_with_pairCrossingCounts
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (hA : RealizesPairCodeSpec S A) :
    ∃ B : Arrangement n,
      IsGeneric B ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (B i) (B j) = (S.code i j).crossings := by
  rcases exists_generic_realizing_pair_codes hA with ⟨B, hB, hgen⟩
  exact ⟨B, hgen, fun i j hij =>
    pairCrossingCount_eq_of_realizes (hB i j hij)⟩

end Lower
end EndToEnd
end Concrete
end Lollipop
