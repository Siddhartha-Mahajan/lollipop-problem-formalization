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
def lollipopToParameter (L : Lollipop) : LollipopParameter :=
  ⟨(L.center, L.radial), L.radial_ne_zero⟩

@[simp] theorem parameter_toLollipop (L : Lollipop) :
    (lollipopToParameter L).toLollipop = L := by cases L <;> rfl

@[simp] theorem lollipop_toParameter (p : LollipopParameter) :
    lollipopToParameter p.toLollipop = p := by cases p <;> rfl

/-- Parameter equivalence. -/
def lollipopParameterEquiv : LollipopParameter ≃ Lollipop :=
  { toFun := LollipopParameter.toLollipop
    invFun := lollipopToParameter
    left_inv := lollipop_toParameter
    right_inv := parameter_toLollipop }

/-- The parameter-to-lollipop map is continuous for the induced lollipop
topology. -/
theorem continuous_toLollipop :
    Continuous LollipopParameter.toLollipop := by
  rw [continuous_induced_rng]
  change Continuous (fun p : LollipopParameter => (p.1.1, p.1.2))
  fun_prop

/-- Parameter space of an `n`-arrangement. -/
abbrev ArrangementParameter (n : ℕ) := Fin n → LollipopParameter

def ArrangementParameter.toArrangement {n : ℕ}
    (p : ArrangementParameter n) : Arrangement n :=
  fun i => (p i).toLollipop

/-- Parameters of an arrangement. -/
def arrangementToParameter {n : ℕ}
    (A : Arrangement n) : ArrangementParameter n :=
  fun i => lollipopToParameter (A i)

@[simp] theorem arrangement_parameter_roundtrip {n : ℕ}
    (A : Arrangement n) :
    (arrangementToParameter A).toArrangement = A := by
  funext i
  simp [arrangementToParameter, ArrangementParameter.toArrangement]

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
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro _hij
  have hmap : Continuous (fun p : ArrangementParameter n =>
      ((p i).toLollipop, (p j).toLollipop)) :=
    (continuous_toLollipop.comp (continuous_apply i)).prodMk
      (continuous_toLollipop.comp (continuous_apply j))
  simpa [strictPairChamberSet, RealizesStrictPairCode,
    ArrangementParameter.toArrangement, Set.setOf_and] using
    (isOpen_realizesStrictPairCode (S.code i j)).preimage hmap

/-- The chamber containing a realizing arrangement is nonempty. -/
theorem parameter_mem_pairCodeChamber
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (hA : RealizesPairCodeSpec S A) :
    arrangementToParameter A ∈ pairCodeChamber S := by
  simpa [pairCodeChamber, arrangementToParameter,
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

/-- Pointwise transversality predicate for a chosen pair of primitive pieces. -/
def primitiveTransverseAt
    (ki kj : PrimitiveKind) (L M : Lollipop) (x : Point) : Prop :=
  match ki, kj with
  | .circle, .circle => CircleCircleTransverseAt L M x
  | .circle, .stem => StemCircleTransverseAt M L x
  | .stem, .circle => StemCircleTransverseAt L M x
  | .stem, .stem => StemStemTransverse L M

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

/-- Union of all primitive-pair tangency loci. -/
def pairBadUnion {n : ℕ} : Set (ArrangementParameter n) :=
  ⋃ i : Fin n, ⋃ j : Fin n, ⋃ hij : i ≠ j,
    ⋃ ki : PrimitiveKind, ⋃ kj : PrimitiveKind,
      pairBadSet i j hij ki kj

/-- Union of all anchor-incidence loci. -/
def anchorBadUnion {n : ℕ} : Set (ArrangementParameter n) :=
  ⋃ i : Fin n, ⋃ j : Fin n, ⋃ hij : i ≠ j,
    anchorBadSet i j hij

/-- Union of all triple-incidence loci. -/
def tripleBadUnion {n : ℕ} : Set (ArrangementParameter n) :=
  ⋃ i : Fin n, ⋃ j : Fin n, ⋃ k : Fin n,
    ⋃ hij : i ≠ j, ⋃ hik : i ≠ k, ⋃ hjk : j ≠ k,
      tripleBadSet i j k hij hik hjk

/-- Union of all parallel-stem loci. -/
def parallelBadUnion {n : ℕ} : Set (ArrangementParameter n) :=
  ⋃ i : Fin n, ⋃ j : Fin n, ⋃ hij : i ≠ j,
    parallelBadSet i j hij

/-- Union of all finitely many forbidden degeneracy loci. -/
def allBad {n : ℕ} : Set (ArrangementParameter n) :=
  pairBadUnion ∪ (anchorBadUnion ∪ (tripleBadUnion ∪ parallelBadUnion))

/-- Membership constructor for the pair-tangency part of `allBad`. -/
theorem mem_allBad_of_pairBad {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (ki kj : PrimitiveKind)
    {p : ArrangementParameter n}
    (hbad : p ∈ pairBadSet i j hij ki kj) :
    p ∈ (allBad : Set (ArrangementParameter n)) := by
  apply Or.inl
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hij,
        Set.mem_iUnion.mpr ⟨ki,
          Set.mem_iUnion.mpr ⟨kj, hbad⟩⟩⟩⟩⟩

/-- Membership constructor for the anchor-incidence part of `allBad`. -/
theorem mem_allBad_of_anchorBad {n : ℕ}
    (i j : Fin n) (hij : i ≠ j)
    {p : ArrangementParameter n}
    (hbad : p ∈ anchorBadSet i j hij) :
    p ∈ (allBad : Set (ArrangementParameter n)) := by
  apply Or.inr
  apply Or.inl
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hij, hbad⟩⟩⟩

/-- Membership constructor for the triple-incidence part of `allBad`. -/
theorem mem_allBad_of_tripleBad {n : ℕ}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {p : ArrangementParameter n}
    (hbad : p ∈ tripleBadSet i j k hij hik hjk) :
    p ∈ (allBad : Set (ArrangementParameter n)) := by
  apply Or.inr
  apply Or.inr
  apply Or.inl
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨k,
        Set.mem_iUnion.mpr ⟨hij,
          Set.mem_iUnion.mpr ⟨hik,
            Set.mem_iUnion.mpr ⟨hjk, hbad⟩⟩⟩⟩⟩⟩

/-- Membership constructor for the parallel-stem part of `allBad`. -/
theorem mem_allBad_of_parallelBad {n : ℕ}
    (i j : Fin n) (hij : i ≠ j)
    {p : ArrangementParameter n}
    (hbad : p ∈ parallelBadSet i j hij) :
    p ∈ (allBad : Set (ArrangementParameter n)) := by
  apply Or.inr
  apply Or.inr
  apply Or.inr
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hij, hbad⟩⟩⟩

/-- The remaining finite-avoidance theorem needed to finish the lower
genericization step.

This is intentionally a proposition, not an axiom and not a caller-facing
certificate for the final endpoint.  It records the concrete theorem still to
prove: the complement of the explicitly defined bad locus is dense, and every
point outside that locus satisfies the genericity predicate used by the graph
Euler theorem. -/
structure GenericityAvoidance (n : ℕ) : Prop where
  dense_good : Dense ((allBad : Set (ArrangementParameter n))ᶜ)
  good_is_generic :
    ∀ {p : ArrangementParameter n}, p ∉ allBad → IsGeneric p.toArrangement

end GenericityPort

/-- Every nonempty strict pair chamber contains a generic arrangement, assuming
the remaining concrete finite-avoidance theorem. -/
theorem exists_generic_realizing_pair_codes_of_avoidance
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (havoid : GenericityPort.GenericityAvoidance n)
    (hA : RealizesPairCodeSpec S A) :
    ∃ B : Arrangement n,
      RealizesPairCodeSpec S B ∧ IsGeneric B := by
  let U := pairCodeChamber S
  have hUopen : IsOpen U := isOpen_pairCodeChamber S
  have hUne : U.Nonempty :=
    ⟨arrangementToParameter A, parameter_mem_pairCodeChamber hA⟩
  rcases havoid.dense_good.exists_mem_open hUopen hUne with
    ⟨p, hpGood, hpU⟩
  refine ⟨p.toArrangement, hpU, ?_⟩
  exact havoid.good_is_generic hpGood

/-- Genericization preserves every exact pair crossing count encoded by the
strict chamber, assuming the remaining concrete finite-avoidance theorem. -/
theorem exists_generic_with_pairCrossingCounts_of_avoidance
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (havoid : GenericityPort.GenericityAvoidance n)
    (hA : RealizesPairCodeSpec S A) :
    ∃ B : Arrangement n,
      IsGeneric B ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (B i) (B j) = (S.code i j).crossings := by
  rcases exists_generic_realizing_pair_codes_of_avoidance havoid hA with
    ⟨B, hB, hgen⟩
  exact ⟨B, hgen, fun i j hij =>
    pairCrossingCount_eq_of_realizes (hB i j hij)⟩

end Lower
end EndToEnd
end Concrete
end Lollipop
