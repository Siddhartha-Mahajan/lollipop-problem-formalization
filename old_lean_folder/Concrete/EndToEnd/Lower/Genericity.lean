import old_lean_folder.Concrete.EndToEnd.Lower.PolynomialFamily
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
open scoped Topology

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

/-- Smaller bad locus needed after the arrangement is already constrained to
a strict pair-code chamber.  The strict pair chamber itself supplies pair
finiteness, transversality, and anchor avoidance; only triple incidences and
parallel stems still have to be avoided by the generic perturbation. -/
def chamberBadUnion {n : ℕ} : Set (ArrangementParameter n) :=
  tripleBadUnion ∪ parallelBadUnion

theorem isOpen_compl_parallelBadSet {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    IsOpen ((parallelBadSet i j hij : Set (ArrangementParameter n))ᶜ) := by
  have hdet : Continuous (fun p : ArrangementParameter n =>
      detPoint ((p i).toLollipop).radial ((p j).toLollipop).radial) :=
    continuous_detPoint_comp
      (continuous_lollipop_radial_comp
        (continuous_toLollipop.comp (continuous_apply i)))
      (continuous_lollipop_radial_comp
        (continuous_toLollipop.comp (continuous_apply j)))
  rw [show ((parallelBadSet i j hij : Set (ArrangementParameter n))ᶜ) =
      {p : ArrangementParameter n |
        detPoint ((p i).toLollipop).radial
          ((p j).toLollipop).radial ≠ 0} by
    ext p
    change (¬ detPoint ((p i).toLollipop).radial
        ((p j).toLollipop).radial = 0) ↔
      detPoint ((p i).toLollipop).radial
        ((p j).toLollipop).radial ≠ 0
    rfl]
  exact isOpen_ne_fun hdet continuous_const

theorem isOpen_compl_parallelBadUnion {n : ℕ} :
    IsOpen ((parallelBadUnion : Set (ArrangementParameter n))ᶜ) := by
  unfold parallelBadUnion
  simp only [Set.compl_iUnion]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_iInter_of_finite
  intro hij
  exact isOpen_compl_parallelBadSet i j hij

theorem dense_compl_allBad_of_piece_complements {n : ℕ}
    (hpairOpen : IsOpen ((pairBadUnion : Set (ArrangementParameter n))ᶜ))
    (hpairDense : Dense ((pairBadUnion : Set (ArrangementParameter n))ᶜ))
    (hanchorOpen : IsOpen ((anchorBadUnion : Set (ArrangementParameter n))ᶜ))
    (hanchorDense : Dense ((anchorBadUnion : Set (ArrangementParameter n))ᶜ))
    (htripleOpen : IsOpen ((tripleBadUnion : Set (ArrangementParameter n))ᶜ))
    (htripleDense : Dense ((tripleBadUnion : Set (ArrangementParameter n))ᶜ))
    (hparallelDense : Dense ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)) :
    Dense ((allBad : Set (ArrangementParameter n))ᶜ) := by
  have htp : Dense
      (((tripleBadUnion : Set (ArrangementParameter n))ᶜ) ∩
        ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)) :=
    htripleDense.inter_of_isOpen_left hparallelDense htripleOpen
  have hatp : Dense
      (((anchorBadUnion : Set (ArrangementParameter n))ᶜ) ∩
        (((tripleBadUnion : Set (ArrangementParameter n))ᶜ) ∩
          ((parallelBadUnion : Set (ArrangementParameter n))ᶜ))) :=
    hanchorDense.inter_of_isOpen_left htp hanchorOpen
  have hall : Dense
      (((pairBadUnion : Set (ArrangementParameter n))ᶜ) ∩
        (((anchorBadUnion : Set (ArrangementParameter n))ᶜ) ∩
          (((tripleBadUnion : Set (ArrangementParameter n))ᶜ) ∩
            ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)))) :=
    hpairDense.inter_of_isOpen_left hatp hpairOpen
  simpa [allBad, Set.compl_union, Set.inter_assoc] using hall

theorem dense_compl_chamberBad_of_piece_complements {n : ℕ}
    (htripleOpen : IsOpen ((tripleBadUnion : Set (ArrangementParameter n))ᶜ))
    (htripleDense : Dense ((tripleBadUnion : Set (ArrangementParameter n))ᶜ))
    (hparallelDense : Dense ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)) :
    Dense ((chamberBadUnion : Set (ArrangementParameter n))ᶜ) := by
  have htp : Dense
      (((tripleBadUnion : Set (ArrangementParameter n))ᶜ) ∩
        ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)) :=
    htripleDense.inter_of_isOpen_left hparallelDense htripleOpen
  simpa [chamberBadUnion, Set.compl_union] using htp

/-- Piecewise version of the genericity avoidance theorem.  The parallel
openness field is proved by `isOpen_compl_parallelBadUnion`; the remaining
fields isolate the semialgebraic density/closedness work still needed for the
pair, anchor, and triple loci. -/
structure GenericityAvoidancePieces (n : ℕ) : Prop where
  pair_open : IsOpen ((pairBadUnion : Set (ArrangementParameter n))ᶜ)
  pair_dense : Dense ((pairBadUnion : Set (ArrangementParameter n))ᶜ)
  anchor_open : IsOpen ((anchorBadUnion : Set (ArrangementParameter n))ᶜ)
  anchor_dense : Dense ((anchorBadUnion : Set (ArrangementParameter n))ᶜ)
  triple_open : IsOpen ((tripleBadUnion : Set (ArrangementParameter n))ᶜ)
  triple_dense : Dense ((tripleBadUnion : Set (ArrangementParameter n))ᶜ)
  parallel_dense : Dense ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)

/-- Reduced finite-avoidance theorem needed when strict pair chambers are
already fixed. -/
structure ChamberGenericityAvoidance (n : ℕ) : Prop where
  dense_good : Dense ((chamberBadUnion : Set (ArrangementParameter n))ᶜ)

/-- Piecewise version of the reduced strict-chamber genericity theorem.  After
strict pair chambers supply pair-local facts, only triple contacts and
parallel stems remain in the bad locus. -/
structure ChamberGenericityAvoidancePieces (n : ℕ) : Prop where
  triple_open : IsOpen ((tripleBadUnion : Set (ArrangementParameter n))ᶜ)
  triple_dense : Dense ((tripleBadUnion : Set (ArrangementParameter n))ᶜ)
  parallel_dense : Dense ((parallelBadUnion : Set (ArrangementParameter n))ᶜ)

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

/-- Membership constructor for the triple-incidence part of the reduced
strict-chamber bad locus. -/
theorem mem_chamberBad_of_tripleBad {n : ℕ}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {p : ArrangementParameter n}
    (hbad : p ∈ tripleBadSet i j k hij hik hjk) :
    p ∈ (chamberBadUnion : Set (ArrangementParameter n)) := by
  apply Or.inl
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨k,
        Set.mem_iUnion.mpr ⟨hij,
          Set.mem_iUnion.mpr ⟨hik,
            Set.mem_iUnion.mpr ⟨hjk, hbad⟩⟩⟩⟩⟩⟩

/-- Membership constructor for the parallel-stem part of the reduced
strict-chamber bad locus. -/
theorem mem_chamberBad_of_parallelBad {n : ℕ}
    (i j : Fin n) (hij : i ≠ j)
    {p : ArrangementParameter n}
    (hbad : p ∈ parallelBadSet i j hij) :
    p ∈ (chamberBadUnion : Set (ArrangementParameter n)) := by
  apply Or.inr
  exact Set.mem_iUnion.mpr ⟨i,
    Set.mem_iUnion.mpr ⟨j,
      Set.mem_iUnion.mpr ⟨hij, hbad⟩⟩⟩

theorem realizesPairCodeSpec_of_ne {n : ℕ}
    {S : PairCodeSpec n} {A : Arrangement n}
    (hA : RealizesPairCodeSpec S A)
    (i j : Fin n) (hij : i ≠ j) :
    RealizesStrictPairCode (S.code i j) (A i) (A j) := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hA i j hlt
  · have hji : RealizesStrictPairCode (S.code j i) (A j) (A i) :=
      hA j i hgt
    have hswap : S.code j i = (S.code i j).swap :=
      S.swap i j hij
    have hji' :
        RealizesStrictPairCode ((S.code i j).swap) (A j) (A i) := by
      simpa [hswap] using hji
    exact (realizes_swap_iff (S.code i j) (A i) (A j)).2 hji'

/-- A point in a strict pair-code chamber outside the reduced bad locus is
generic.  The strict pair chamber supplies all pair-local finiteness,
transversality, and anchor-avoidance facts; the reduced bad locus excludes
triple contacts and parallel stems. -/
theorem good_is_generic_in_pair_chamber {n : ℕ}
    {S : PairCodeSpec n} {p : ArrangementParameter n}
    (hreal : RealizesPairCodeSpec S p.toArrangement)
    (hgood : p ∉ chamberBadUnion) :
    IsGeneric p.toArrangement := by
  refine
    { pair_finite := ?_
      pair_transverse := ?_
      away_left_anchor := ?_
      away_right_anchor := ?_
      no_triple := ?_
      nonparallel_stems := ?_ }
  · intro i j hij
    exact pairCrossingSet_finite_of_realizes
      (realizesPairCodeSpec_of_ne hreal i j hij)
  · intro i j hij
    exact primitivePairwiseTransverse_of_realizes
      (realizesPairCodeSpec_of_ne hreal i j hij)
  · intro i j hij
    exact left_anchor_not_mem_pairCrossingSet_of_realizes
      (realizesPairCodeSpec_of_ne hreal i j hij)
  · intro i j hij
    exact right_anchor_not_mem_pairCrossingSet_of_realizes
      (realizesPairCodeSpec_of_ne hreal i j hij)
  · intro i j k hij hik hjk
    ext x
    constructor
    · intro hx
      exact False.elim (hgood
        (mem_chamberBad_of_tripleBad i j k hij hik hjk
          ⟨x, by
            simpa only [ArrangementParameter.toArrangement, pairCrossingSet,
              Set.mem_inter_iff] using hx⟩))
    · intro hx
      exact False.elim hx
  · intro i j hij hdet
    exact hgood (mem_chamberBad_of_parallelBad i j hij (by
      change detPoint ((p i).toLollipop).radial
        ((p j).toLollipop).radial = 0
      simpa only [ArrangementParameter.toArrangement] using hdet))

theorem primitivePairwiseTransverse_of_not_allBad {n : ℕ}
    {p : ArrangementParameter n} (hgood : p ∉ allBad)
    (i j : Fin n) (hij : i ≠ j) :
    PrimitivePairwiseTransverse (p.toArrangement i) (p.toArrangement j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hnot
    exact hgood (mem_allBad_of_pairBad i j hij
      PrimitiveKind.circle PrimitiveKind.circle
      ⟨x, by simpa [ArrangementParameter.toArrangement, primitive, cc] using hx,
        by
          intro ht
          change detPoint (x - (p.toArrangement i).center)
            (x - (p.toArrangement j).center) ≠ 0 at ht
          exact ht hnot⟩)
  · intro x hx hnot
    exact hgood (mem_allBad_of_pairBad i j hij
      PrimitiveKind.circle PrimitiveKind.stem
      ⟨x, by simpa [ArrangementParameter.toArrangement, primitive, cr] using hx,
        by
          intro ht
          change dotPoint (p.toArrangement j).radial
            (x - (p.toArrangement i).center) ≠ 0 at ht
          exact ht hnot⟩)
  · intro x hx hnot
    exact hgood (mem_allBad_of_pairBad i j hij
      PrimitiveKind.stem PrimitiveKind.circle
      ⟨x, by simpa [ArrangementParameter.toArrangement, primitive, rc] using hx,
        by
          intro ht
          change dotPoint (p.toArrangement i).radial
            (x - (p.toArrangement j).center) ≠ 0 at ht
          exact ht hnot⟩)
  · intro hnon hnot
    rcases hnon with ⟨x, hx⟩
    exact hgood (mem_allBad_of_pairBad i j hij
      PrimitiveKind.stem PrimitiveKind.stem
      ⟨x, by simpa [ArrangementParameter.toArrangement, primitive, rr] using hx,
        by
          intro ht
          change detPoint (p.toArrangement i).radial
            (p.toArrangement j).radial ≠ 0 at ht
          exact ht hnot⟩)

theorem pairCrossingSet_finite_of_not_allBad {n : ℕ}
    {p : ArrangementParameter n} (hgood : p ∉ allBad)
    (i j : Fin n) (hij : i ≠ j) :
    (pairCrossingSet (p.toArrangement i) (p.toArrangement j)).Finite := by
  let L := p.toArrangement i
  let M := p.toArrangement j
  have htrans : PrimitivePairwiseTransverse L M := by
    simpa [L, M] using primitivePairwiseTransverse_of_not_allBad hgood i j hij
  have hccFin : (cc L M).Finite := by
    by_cases hcc : (cc L M).Nonempty
    · rcases hcc with ⟨x, hx⟩
      have hsphere : concreteSphere L ≠ concreteSphere M := by
        intro hsphere
        have hcenter : L.center = M.center :=
          congrArg EuclideanGeometry.Sphere.center hsphere
        have hzero : detPoint (x - L.center) (x - M.center) = 0 := by
          rw [hcenter]
          unfold detPoint
          ring
        exact (htrans.cc x hx) hzero
      apply finite_of_forall_mem_eq_left_or_right
      intro a b y ha hb hy hab
      exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hy
    · rw [Set.not_nonempty_iff_eq_empty.mp hcc]
      exact finite_empty
  have hrcFin : (rc L M).Finite := finite_ray_circle_intersection L M
  have hcrFin : (cr L M).Finite := finite_circle_ray_intersection L M
  have hrrFin : (rr L M).Finite := by
    by_cases hrr : (rr L M).Nonempty
    · exact finite_of_subsingleton_of_mem
        (rr_subsingleton_of_transverse (htrans.rr hrr)) hrr.some_mem
    · rw [Set.not_nonempty_iff_eq_empty.mp hrr]
      exact finite_empty
  rw [pairCrossingSet_decompose]
  exact ((hccFin.union hrcFin).union hcrFin).union hrrFin

theorem good_is_generic {n : ℕ}
    {p : ArrangementParameter n} (hgood : p ∉ allBad) :
    IsGeneric p.toArrangement := by
  refine
    { pair_finite := ?_
      pair_transverse := ?_
      away_left_anchor := ?_
      away_right_anchor := ?_
      no_triple := ?_
      nonparallel_stems := ?_ }
  · intro i j hij
    exact pairCrossingSet_finite_of_not_allBad hgood i j hij
  · intro i j hij
    exact primitivePairwiseTransverse_of_not_allBad hgood i j hij
  · intro i j hij hx
    exact hgood (mem_allBad_of_anchorBad i j hij (Or.inl (by
      simpa [ArrangementParameter.toArrangement, pairCrossingSet] using hx.2)))
  · intro i j hij hx
    exact hgood (mem_allBad_of_anchorBad i j hij (Or.inr (by
      simpa [ArrangementParameter.toArrangement, pairCrossingSet] using hx.1)))
  · intro i j k hij hik hjk
    ext x
    constructor
    · intro hx
      exact False.elim (hgood (mem_allBad_of_tripleBad i j k hij hik hjk
        ⟨x, by
          simpa only [ArrangementParameter.toArrangement, pairCrossingSet,
            Set.mem_inter_iff] using hx⟩))
    · intro hx
      exact False.elim hx
  · intro i j hij hdet
    exact hgood (mem_allBad_of_parallelBad i j hij (by
      change detPoint ((p i).toLollipop).radial ((p j).toLollipop).radial = 0
      simpa only [ArrangementParameter.toArrangement] using hdet))

/-- The remaining finite-avoidance theorem needed to finish the lower
genericization step.

This is intentionally a proposition, not an axiom and not a caller-facing
certificate for the final endpoint.  It records the concrete theorem still to
prove: the complement of the explicitly defined bad locus is dense. -/
structure GenericityAvoidance (n : ℕ) : Prop where
  dense_good : Dense ((allBad : Set (ArrangementParameter n))ᶜ)

theorem GenericityAvoidancePieces.toGenericityAvoidance {n : ℕ}
    (h : GenericityAvoidancePieces n) : GenericityAvoidance n where
  dense_good :=
    dense_compl_allBad_of_piece_complements
      h.pair_open h.pair_dense
      h.anchor_open h.anchor_dense
      h.triple_open h.triple_dense
      h.parallel_dense

theorem GenericityAvoidance.toChamberGenericityAvoidance {n : ℕ}
    (h : GenericityAvoidance n) : ChamberGenericityAvoidance n where
  dense_good := by
    apply Dense.mono ?_ h.dense_good
    intro p hp hbad
    apply hp
    rcases hbad with htriple | hparallel
    · exact Or.inr (Or.inr (Or.inl htriple))
    · exact Or.inr (Or.inr (Or.inr hparallel))

theorem ChamberGenericityAvoidancePieces.toChamberGenericityAvoidance {n : ℕ}
    (h : ChamberGenericityAvoidancePieces n) :
    ChamberGenericityAvoidance n where
  dense_good :=
    dense_compl_chamberBad_of_piece_complements
      h.triple_open h.triple_dense h.parallel_dense

/-- If the index type has no three pairwise-distinct elements, then the
triple-contact bad locus is empty. -/
theorem tripleBadUnion_eq_empty_of_no_three_distinct {n : ℕ}
    (hno :
      ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → False) :
    (tripleBadUnion : Set (ArrangementParameter n)) = ∅ := by
  ext p
  constructor
  · intro hp
    rw [tripleBadUnion] at hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨j, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨k, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hij, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hik, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hjk, _hbad⟩
    exact False.elim (hno i j k hij hik hjk)
  · intro hp
    exact False.elim hp

/-- There are no three pairwise-distinct elements of `Fin 2`. -/
theorem no_three_distinct_fin_two :
    ∀ i j k : Fin 2, i ≠ j → i ≠ k → j ≠ k → False := by
  intro i j k hij hik hjk
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk

/-- With two lollipops, the triple-contact bad locus is empty. -/
theorem tripleBadUnion_eq_empty_two :
    (tripleBadUnion : Set (ArrangementParameter 2)) = ∅ :=
  tripleBadUnion_eq_empty_of_no_three_distinct no_three_distinct_fin_two

/-- With two lollipops, reduced chamber badness is exactly parallel stems. -/
theorem chamberBadUnion_eq_parallelBadUnion_two :
    (chamberBadUnion : Set (ArrangementParameter 2)) =
      parallelBadUnion := by
  rw [chamberBadUnion, tripleBadUnion_eq_empty_two]
  simp

/-- With two lollipops, the parallel-stem bad locus is just the determinant
of the two radial vectors being zero. -/
theorem parallelBadUnion_two_eq_det_zero :
    (parallelBadUnion : Set (ArrangementParameter 2)) =
      {p | detPoint ((p (0 : Fin 2)).toLollipop).radial
          ((p (1 : Fin 2)).toLollipop).radial = 0} := by
  ext p
  constructor
  · intro hp
    rw [parallelBadUnion] at hp
    rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨j, hp⟩
    rcases Set.mem_iUnion.mp hp with ⟨hij, hbad⟩
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · change
        detPoint ((p (0 : Fin 2)).toLollipop).radial
          ((p (1 : Fin 2)).toLollipop).radial = 0 at hbad
      exact hbad
    · have h10 :
          detPoint ((p (1 : Fin 2)).toLollipop).radial
            ((p (0 : Fin 2)).toLollipop).radial = 0 := by
        change
          detPoint ((p (1 : Fin 2)).toLollipop).radial
            ((p (0 : Fin 2)).toLollipop).radial = 0 at hbad
        exact hbad
      rw [detPoint_skew] at h10
      exact neg_eq_zero.mp h10
    · exact False.elim (hij rfl)
  · intro hdet
    rw [parallelBadUnion]
    exact Set.mem_iUnion.mpr ⟨(0 : Fin 2),
      Set.mem_iUnion.mpr ⟨(1 : Fin 2),
        Set.mem_iUnion.mpr ⟨by decide,
          by
            change
              detPoint ((p (0 : Fin 2)).toLollipop).radial
                ((p (1 : Fin 2)).toLollipop).radial = 0
            exact hdet⟩⟩⟩

/-- With two lollipops, reduced chamber badness is the single determinant-zero
condition on the two radial vectors. -/
theorem chamberBadUnion_two_eq_det_zero :
    (chamberBadUnion : Set (ArrangementParameter 2)) =
      {p | detPoint ((p (0 : Fin 2)).toLollipop).radial
          ((p (1 : Fin 2)).toLollipop).radial = 0} := by
  rw [chamberBadUnion_eq_parallelBadUnion_two,
    parallelBadUnion_two_eq_det_zero]

/-- For two lollipops, chamber-genericity avoidance is reduced to density of
the nonparallel-stem locus. -/
theorem chamberGenericityAvoidance_two_of_parallel_dense
    (hparallel :
      Dense ((parallelBadUnion : Set (ArrangementParameter 2))ᶜ)) :
    ChamberGenericityAvoidance 2 where
  dense_good := by
    rwa [chamberBadUnion_eq_parallelBadUnion_two]

/-- Equivalent two-lollipop chamber-genericity reduction stated directly with
the determinant-nonzero locus. -/
theorem chamberGenericityAvoidance_two_of_det_ne_dense
    (hdet :
      Dense ({p : ArrangementParameter 2 |
        detPoint ((p (0 : Fin 2)).toLollipop).radial
          ((p (1 : Fin 2)).toLollipop).radial ≠ 0})) :
    ChamberGenericityAvoidance 2 where
  dense_good := by
    rw [chamberBadUnion_two_eq_det_zero]
    have hset :
        ({p : ArrangementParameter 2 |
          detPoint ((p (0 : Fin 2)).toLollipop).radial
            ((p (1 : Fin 2)).toLollipop).radial = 0}ᶜ) =
          {p : ArrangementParameter 2 |
            detPoint ((p (0 : Fin 2)).toLollipop).radial
              ((p (1 : Fin 2)).toLollipop).radial ≠ 0} := by
      rfl
    rw [hset]
    exact hdet

/-- Rotate a displayed point by a quarter turn. -/
def rotate90 (u : Point) : Point :=
  R2.toPoint (fun i : Fin 2 => if i = 0 then -u 1 else u 0)

@[simp] theorem rotate90_zero (u : Point) : rotate90 u 0 = -u 1 := by
  simp [rotate90]

@[simp] theorem rotate90_one (u : Point) : rotate90 u 1 = u 0 := by
  simp [rotate90]

/-- The determinant of a vector with its quarter turn is its squared length in
coordinates. -/
theorem detPoint_self_rotate90 (u : Point) :
    detPoint u (rotate90 u) = u 0 ^ 2 + u 1 ^ 2 := by
  unfold detPoint
  simp [pow_two]

theorem detPoint_self_rotate90_ne_zero {u : Point} (hu : u ≠ 0) :
    detPoint u (rotate90 u) ≠ 0 := by
  rw [detPoint_self_rotate90]
  intro hsum
  have h0 : u 0 = 0 := by
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  have h1 : u 1 = 0 := by
    nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]
  apply hu
  have hR : R2.ofPoint u = (0 : R2) := by
    ext i
    fin_cases i <;> simp [R2.ofPoint, h0, h1]
  rw [← R2.toPoint_ofPoint u, hR]
  change R2.toPoint (0 : R2) = (0 : Point)
  have h0R : (0 : R2) = R2.ofPoint (0 : Point) := by
    ext i
    rfl
  rw [h0R]
  exact R2.toPoint_ofPoint (0 : Point)

/-- If the two radials are parallel, perturb the second radial in the
quarter-turn direction of the first. -/
def perturbSecondRadialOfParallel
    (p : ArrangementParameter 2)
    (hparallel :
      detPoint (p (0 : Fin 2)).1.2 (p (1 : Fin 2)).1.2 = 0)
    (t : ℝ) : ArrangementParameter 2
  | 0 => p 0
  | 1 =>
      ⟨((p (1 : Fin 2)).1.1,
        (p (1 : Fin 2)).1.2 +
          t • rotate90 (p (0 : Fin 2)).1.2),
        by
          by_cases ht : t = 0
          · simpa [ht] using (p (1 : Fin 2)).2
          · intro hzero
            have hdet_zero :
                detPoint (p (0 : Fin 2)).1.2
                  ((p (1 : Fin 2)).1.2 +
                    t • rotate90 (p (0 : Fin 2)).1.2) = 0 := by
              change (p (1 : Fin 2)).1.2 +
                    t • rotate90 (p (0 : Fin 2)).1.2 = 0 at hzero
              rw [hzero]
              unfold detPoint
              simp
            have hformula :
                detPoint (p (0 : Fin 2)).1.2
                  ((p (1 : Fin 2)).1.2 +
                    t • rotate90 (p (0 : Fin 2)).1.2) =
                  t * detPoint (p (0 : Fin 2)).1.2
                    (rotate90 (p (0 : Fin 2)).1.2) := by
              unfold detPoint at hparallel ⊢
              simp
              ring_nf at hparallel ⊢
              nlinarith
            have hprod :
                t * detPoint (p (0 : Fin 2)).1.2
                  (rotate90 (p (0 : Fin 2)).1.2) = 0 := by
              rwa [hformula] at hdet_zero
            rcases mul_eq_zero.mp hprod with htzero | hrot
            · exact ht htzero
            · exact detPoint_self_rotate90_ne_zero (p (0 : Fin 2)).2 hrot⟩

@[simp] theorem perturbSecondRadialOfParallel_zero
    (p : ArrangementParameter 2) (hparallel) (t : ℝ) :
    perturbSecondRadialOfParallel p hparallel t (0 : Fin 2) = p 0 := rfl

@[simp] theorem perturbSecondRadialOfParallel_one_val
    (p : ArrangementParameter 2) (hparallel) (t : ℝ) :
    (perturbSecondRadialOfParallel p hparallel t (1 : Fin 2)).1 =
      ((p (1 : Fin 2)).1.1,
        (p (1 : Fin 2)).1.2 +
          t • rotate90 (p (0 : Fin 2)).1.2) := rfl

@[simp] theorem perturbSecondRadialOfParallel_zero_time
    (p : ArrangementParameter 2) (hparallel) :
    perturbSecondRadialOfParallel p hparallel 0 = p := by
  funext i
  fin_cases i
  · rfl
  · apply Subtype.ext
    simp

theorem continuous_perturbSecondRadialOfParallel
    (p : ArrangementParameter 2) (hparallel) :
    Continuous (fun t : ℝ =>
      perturbSecondRadialOfParallel p hparallel t) := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · rw [continuous_induced_rng]
    change Continuous (fun t : ℝ =>
      ((p (1 : Fin 2)).1.1,
        (p (1 : Fin 2)).1.2 +
          t • rotate90 (p (0 : Fin 2)).1.2))
    fun_prop

theorem detPoint_perturbSecondRadialOfParallel
    (p : ArrangementParameter 2) (hparallel) (t : ℝ) :
    detPoint
        ((perturbSecondRadialOfParallel p hparallel t
          (0 : Fin 2)).toLollipop).radial
        ((perturbSecondRadialOfParallel p hparallel t
          (1 : Fin 2)).toLollipop).radial =
      t * detPoint (p (0 : Fin 2)).1.2
        (rotate90 (p (0 : Fin 2)).1.2) := by
  change
    detPoint (p (0 : Fin 2)).1.2
        ((p (1 : Fin 2)).1.2 +
          t • rotate90 (p (0 : Fin 2)).1.2) =
      t * detPoint (p (0 : Fin 2)).1.2
        (rotate90 (p (0 : Fin 2)).1.2)
  unfold detPoint at hparallel ⊢
  simp
  ring_nf at hparallel ⊢
  nlinarith

theorem detPoint_perturbSecondRadialOfParallel_ne_zero
    (p : ArrangementParameter 2) (hparallel) {t : ℝ} (ht : t ≠ 0) :
    detPoint
        ((perturbSecondRadialOfParallel p hparallel t
          (0 : Fin 2)).toLollipop).radial
        ((perturbSecondRadialOfParallel p hparallel t
          (1 : Fin 2)).toLollipop).radial ≠ 0 := by
  rw [detPoint_perturbSecondRadialOfParallel]
  exact mul_ne_zero ht
    (detPoint_self_rotate90_ne_zero (p (0 : Fin 2)).2)

/-- Nonparallel two-radial parameters are dense. -/
theorem dense_det_ne_two :
    Dense ({p : ArrangementParameter 2 |
      detPoint ((p (0 : Fin 2)).toLollipop).radial
        ((p (1 : Fin 2)).toLollipop).radial ≠ 0}) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases hUne with ⟨p, hpU⟩
  by_cases hdet :
      detPoint ((p (0 : Fin 2)).toLollipop).radial
        ((p (1 : Fin 2)).toLollipop).radial ≠ 0
  · exact ⟨p, hpU, hdet⟩
  · have hparallel :
        detPoint (p (0 : Fin 2)).1.2 (p (1 : Fin 2)).1.2 = 0 := by
      change detPoint ((p (0 : Fin 2)).toLollipop).radial
        ((p (1 : Fin 2)).toLollipop).radial = 0
      exact not_not.mp hdet
    let γ : ℝ → ArrangementParameter 2 :=
      fun t => perturbSecondRadialOfParallel p hparallel t
    have hγcont : Continuous γ :=
      continuous_perturbSecondRadialOfParallel p hparallel
    have hpreOpen : IsOpen (γ ⁻¹' U) := hU.preimage hγcont
    have hzero_mem : (0 : ℝ) ∈ γ ⁻¹' U := by
      change γ 0 ∈ U
      have hγ0 : γ 0 = p := by
        simpa [γ] using
          perturbSecondRadialOfParallel_zero_time p hparallel
      simpa [hγ0] using hpU
    have hnhds : γ ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hpreOpen.mem_nhds hzero_mem
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
    let t : ℝ := ε / 2
    have htpos : 0 < t := by
      positivity
    have htne : t ≠ 0 := ne_of_gt htpos
    have htball : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have htlt : t < ε := by
        dsimp [t]
        linarith
      rw [sub_zero, abs_of_pos htpos]
      exact htlt
    refine ⟨γ t, hεsub htball, ?_⟩
    exact detPoint_perturbSecondRadialOfParallel_ne_zero p hparallel htne

/-- The reduced genericity port is fully proved for two lollipops. -/
theorem chamberGenericityAvoidance_two : ChamberGenericityAvoidance 2 :=
  chamberGenericityAvoidance_two_of_det_ne_dense dense_det_ne_two

/-- Finite intersections of open dense sets are dense.  This local form avoids
the stronger countable Baire theorem. -/
theorem dense_biInter_finset_of_open_dense
    {α X : Type*} [TopologicalSpace X] [DecidableEq α]
    (s : Finset α) (U : α → Set X)
    (hopen : ∀ a ∈ s, IsOpen (U a))
    (hdense : ∀ a ∈ s, Dense (U a)) :
    Dense (⋂ a ∈ s, U a) := by
  classical
  revert hopen hdense
  refine Finset.induction_on s ?_ ?_
  · intro _hopen _hdense
    simpa using (dense_univ : Dense (Set.univ : Set X))
  · intro a s ha ih hopen hdense
    have hopena : IsOpen (U a) :=
      hopen a (Finset.mem_insert_self a s)
    have hdensea : Dense (U a) :=
      hdense a (Finset.mem_insert_self a s)
    have hopenS : ∀ b ∈ s, IsOpen (U b) := by
      intro b hb
      exact hopen b (Finset.mem_insert_of_mem hb)
    have hdenseS : ∀ b ∈ s, Dense (U b) := by
      intro b hb
      exact hdense b (Finset.mem_insert_of_mem hb)
    have hS : Dense (⋂ b ∈ s, U b) := ih hopenS hdenseS
    have hInter : Dense (U a ∩ ⋂ b ∈ s, U b) :=
      hdensea.inter_of_isOpen_left hS hopena
    have hEq : (U a ∩ ⋂ b ∈ s, U b) =
        (⋂ b ∈ insert a s, U b) := by
      ext x
      constructor
      · rintro ⟨hxa, hxs⟩
        rw [Set.mem_iInter]
        intro b
        rw [Set.mem_iInter]
        intro hb
        rw [Finset.mem_insert] at hb
        rcases hb with rfl | hb
        · exact hxa
        · exact Set.mem_iInter.mp (Set.mem_iInter.mp hxs b) hb
      · intro hx
        constructor
        · exact Set.mem_iInter.mp
            (Set.mem_iInter.mp hx a) (Finset.mem_insert_self a s)
        · rw [Set.mem_iInter]
          intro b
          rw [Set.mem_iInter]
          intro hb
          exact Set.mem_iInter.mp
            (Set.mem_iInter.mp hx b) (Finset.mem_insert_of_mem hb)
    rw [← hEq]
    exact hInter

/-- Fintype form of finite open-dense intersection. -/
theorem dense_iInter_fintype_of_open_dense
    {α X : Type*} [TopologicalSpace X] [Fintype α] [DecidableEq α]
    (U : α → Set X)
    (hopen : ∀ a, IsOpen (U a))
    (hdense : ∀ a, Dense (U a)) :
    Dense (⋂ a, U a) := by
  classical
  have h := dense_biInter_finset_of_open_dense
    (Finset.univ : Finset α) U
    (by intro a _ha; exact hopen a)
    (by intro a _ha; exact hdense a)
  simpa using h

/-- Perturb the radial of the selected second index in the quarter-turn
direction of the first selected radial. -/
def perturbRadialAtOfParallel {n : ℕ}
    (p : ArrangementParameter n) (i j : Fin n)
    (hparallel : detPoint (p i).1.2 (p j).1.2 = 0)
    (t : ℝ) : ArrangementParameter n :=
  fun a =>
    if h : a = j then
      ⟨((p j).1.1,
        (p j).1.2 + t • rotate90 (p i).1.2),
        by
          by_cases ht : t = 0
          · simpa [ht] using (p j).2
          · intro hzero
            have hdet_zero :
                detPoint (p i).1.2
                  ((p j).1.2 + t • rotate90 (p i).1.2) = 0 := by
              change (p j).1.2 + t • rotate90 (p i).1.2 = 0 at hzero
              rw [hzero]
              unfold detPoint
              simp
            have hformula :
                detPoint (p i).1.2
                  ((p j).1.2 + t • rotate90 (p i).1.2) =
                  t * detPoint (p i).1.2 (rotate90 (p i).1.2) := by
              unfold detPoint at hparallel ⊢
              simp
              ring_nf at hparallel ⊢
              nlinarith
            have hprod :
                t * detPoint (p i).1.2 (rotate90 (p i).1.2) = 0 := by
              rwa [hformula] at hdet_zero
            rcases mul_eq_zero.mp hprod with htzero | hrot
            · exact ht htzero
            · exact detPoint_self_rotate90_ne_zero (p i).2 hrot⟩
    else p a

theorem perturbRadialAtOfParallel_apply_ne {n : ℕ}
    (p : ArrangementParameter n) (i j a : Fin n) (hparallel)
    (t : ℝ) (ha : a ≠ j) :
    perturbRadialAtOfParallel p i j hparallel t a = p a := by
  unfold perturbRadialAtOfParallel
  rw [dif_neg ha]

theorem perturbRadialAtOfParallel_apply_j_val {n : ℕ}
    (p : ArrangementParameter n) (i j : Fin n) (hparallel) (t : ℝ) :
    (perturbRadialAtOfParallel p i j hparallel t j).1 =
      ((p j).1.1, (p j).1.2 + t • rotate90 (p i).1.2) := by
  unfold perturbRadialAtOfParallel
  rw [dif_pos rfl]

@[simp] theorem perturbRadialAtOfParallel_zero_time {n : ℕ}
    (p : ArrangementParameter n) (i j : Fin n) (hparallel) :
    perturbRadialAtOfParallel p i j hparallel 0 = p := by
  funext a
  by_cases ha : a = j
  · subst a
    apply Subtype.ext
    simp [perturbRadialAtOfParallel]
  · simp [perturbRadialAtOfParallel, ha]

theorem continuous_perturbRadialAtOfParallel {n : ℕ}
    (p : ArrangementParameter n) (i j : Fin n) (hparallel) :
    Continuous (fun t : ℝ =>
      perturbRadialAtOfParallel p i j hparallel t) := by
  apply continuous_pi
  intro a
  by_cases ha : a = j
  · subst a
    rw [continuous_induced_rng]
    change Continuous (fun t : ℝ =>
      (perturbRadialAtOfParallel p i j hparallel t j).1)
    rw [show (fun t : ℝ =>
        (perturbRadialAtOfParallel p i j hparallel t j).1) =
        (fun t : ℝ =>
          ((p j).1.1, (p j).1.2 + t • rotate90 (p i).1.2)) by
      funext t
      exact perturbRadialAtOfParallel_apply_j_val p i j hparallel t]
    fun_prop
  · rw [show (fun t : ℝ =>
        perturbRadialAtOfParallel p i j hparallel t a) =
        (fun _ : ℝ => p a) by
      funext t
      exact perturbRadialAtOfParallel_apply_ne p i j a hparallel t ha]
    exact continuous_const

theorem detPoint_perturbRadialAtOfParallel {n : ℕ}
    (p : ArrangementParameter n) {i j : Fin n} (hij : i ≠ j)
    (hparallel : detPoint (p i).1.2 (p j).1.2 = 0) (t : ℝ) :
    detPoint
        ((perturbRadialAtOfParallel p i j hparallel t
          i).toLollipop).radial
        ((perturbRadialAtOfParallel p i j hparallel t
          j).toLollipop).radial =
      t * detPoint (p i).1.2 (rotate90 (p i).1.2) := by
  change
    detPoint
        ((perturbRadialAtOfParallel p i j hparallel t i).1.2)
        ((perturbRadialAtOfParallel p i j hparallel t j).1.2) =
      t * detPoint (p i).1.2 (rotate90 (p i).1.2)
  unfold perturbRadialAtOfParallel
  rw [dif_neg hij, dif_pos rfl]
  change detPoint (p i).1.2
      ((p j).1.2 + t • rotate90 (p i).1.2) =
    t * detPoint (p i).1.2 (rotate90 (p i).1.2)
  unfold detPoint at hparallel ⊢
  simp
  ring_nf at hparallel ⊢
  nlinarith

theorem detPoint_perturbRadialAtOfParallel_ne_zero {n : ℕ}
    (p : ArrangementParameter n) {i j : Fin n} (hij : i ≠ j)
    (hparallel : detPoint (p i).1.2 (p j).1.2 = 0)
    {t : ℝ} (ht : t ≠ 0) :
    detPoint
        ((perturbRadialAtOfParallel p i j hparallel t
          i).toLollipop).radial
        ((perturbRadialAtOfParallel p i j hparallel t
          j).toLollipop).radial ≠ 0 := by
  rw [detPoint_perturbRadialAtOfParallel p hij hparallel]
  exact mul_ne_zero ht (detPoint_self_rotate90_ne_zero (p i).2)

/-- For every fixed ordered distinct pair of indices, nonparallel radials are
dense. -/
theorem dense_compl_parallelBadSet {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) :
    Dense ((parallelBadSet i j hij : Set (ArrangementParameter n))ᶜ) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases hUne with ⟨p, hpU⟩
  by_cases hdet :
      detPoint ((p i).toLollipop).radial
        ((p j).toLollipop).radial ≠ 0
  · refine ⟨p, hpU, ?_⟩
    change detPoint ((p i).toLollipop).radial
      ((p j).toLollipop).radial ≠ 0
    exact hdet
  · have hparallel : detPoint (p i).1.2 (p j).1.2 = 0 := by
      change detPoint ((p i).toLollipop).radial
        ((p j).toLollipop).radial = 0
      exact not_not.mp hdet
    let γ : ℝ → ArrangementParameter n :=
      fun t => perturbRadialAtOfParallel p i j hparallel t
    have hγcont : Continuous γ :=
      continuous_perturbRadialAtOfParallel p i j hparallel
    have hpreOpen : IsOpen (γ ⁻¹' U) := hU.preimage hγcont
    have hzero_mem : (0 : ℝ) ∈ γ ⁻¹' U := by
      change γ 0 ∈ U
      have hγ0 : γ 0 = p := by
        simpa [γ] using
          perturbRadialAtOfParallel_zero_time p i j hparallel
      simpa [hγ0] using hpU
    have hnhds : γ ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
      hpreOpen.mem_nhds hzero_mem
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
    let t : ℝ := ε / 2
    have htpos : 0 < t := by
      dsimp [t]
      linarith
    have htne : t ≠ 0 := ne_of_gt htpos
    have htball : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have htlt : t < ε := by
        dsimp [t]
        linarith
      rw [sub_zero, abs_of_pos htpos]
      exact htlt
    refine ⟨γ t, hεsub htball, ?_⟩
    change detPoint ((γ t i).toLollipop).radial
      ((γ t j).toLollipop).radial ≠ 0
    exact detPoint_perturbRadialAtOfParallel_ne_zero p hij hparallel htne

/-- The complement of the parallel-stem bad locus is dense for every finite
arrangement size. -/
theorem dense_compl_parallelBadUnion {n : ℕ} :
    Dense ((parallelBadUnion : Set (ArrangementParameter n))ᶜ) := by
  classical
  let Good : {ij : Fin n × Fin n // ij.1 ≠ ij.2} →
      Set (ArrangementParameter n) :=
    fun ij => (parallelBadSet ij.1.1 ij.1.2 ij.2)ᶜ
  have hgood : Dense (⋂ ij, Good ij) :=
    dense_iInter_fintype_of_open_dense Good
      (by
        intro ij
        exact isOpen_compl_parallelBadSet ij.1.1 ij.1.2 ij.2)
      (by
        intro ij
        exact dense_compl_parallelBadSet ij.1.1 ij.1.2 ij.2)
  have hEq :
      (⋂ ij, Good ij) =
        ((parallelBadUnion : Set (ArrangementParameter n))ᶜ) := by
    ext p
    constructor
    · intro hp
      change p ∉ (parallelBadUnion : Set (ArrangementParameter n))
      intro hbad
      rw [parallelBadUnion] at hbad
      rcases Set.mem_iUnion.mp hbad with ⟨i, hbad⟩
      rcases Set.mem_iUnion.mp hbad with ⟨j, hbad⟩
      rcases Set.mem_iUnion.mp hbad with ⟨hij, hbad⟩
      have hpij : p ∈ Good ⟨(i, j), hij⟩ :=
        Set.mem_iInter.mp hp ⟨(i, j), hij⟩
      exact hpij hbad
    · intro hp
      rw [Set.mem_iInter]
      intro ij
      change p ∉ parallelBadSet ij.1.1 ij.1.2 ij.2
      intro hbad
      exact hp (Set.mem_iUnion.mpr ⟨ij.1.1,
        Set.mem_iUnion.mpr ⟨ij.1.2,
          Set.mem_iUnion.mpr ⟨ij.2, hbad⟩⟩⟩)
  rwa [← hEq]

/-- Chamber genericity now only needs the triple-contact open/dense facts; the
parallel-stem density is proved above. -/
theorem chamberGenericityAvoidance_of_triple_open_dense {n : ℕ}
    (htripleOpen : IsOpen ((tripleBadUnion : Set (ArrangementParameter n))ᶜ))
    (htripleDense : Dense ((tripleBadUnion : Set (ArrangementParameter n))ᶜ)) :
    ChamberGenericityAvoidance n :=
  ChamberGenericityAvoidancePieces.toChamberGenericityAvoidance
    { triple_open := htripleOpen
      triple_dense := htripleDense
      parallel_dense := dense_compl_parallelBadUnion }

theorem not_mem_allBad_of_subsingleton {n : ℕ} [Subsingleton (Fin n)]
    (p : ArrangementParameter n) :
    p ∉ (allBad : Set (ArrangementParameter n)) := by
  intro hp
  rcases hp with hpair | hrest
  · rw [pairBadUnion] at hpair
    rcases Set.mem_iUnion.mp hpair with ⟨i, hpair⟩
    rcases Set.mem_iUnion.mp hpair with ⟨j, hpair⟩
    rcases Set.mem_iUnion.mp hpair with ⟨hij, _⟩
    exact hij (Subsingleton.elim i j)
  rcases hrest with hanchor | hrest
  · rw [anchorBadUnion] at hanchor
    rcases Set.mem_iUnion.mp hanchor with ⟨i, hanchor⟩
    rcases Set.mem_iUnion.mp hanchor with ⟨j, hanchor⟩
    rcases Set.mem_iUnion.mp hanchor with ⟨hij, _⟩
    exact hij (Subsingleton.elim i j)
  rcases hrest with htriple | hparallel
  · rw [tripleBadUnion] at htriple
    rcases Set.mem_iUnion.mp htriple with ⟨i, htriple⟩
    rcases Set.mem_iUnion.mp htriple with ⟨j, htriple⟩
    rcases Set.mem_iUnion.mp htriple with ⟨_k, htriple⟩
    rcases Set.mem_iUnion.mp htriple with ⟨hij, _⟩
    exact hij (Subsingleton.elim i j)
  · rw [parallelBadUnion] at hparallel
    rcases Set.mem_iUnion.mp hparallel with ⟨i, hparallel⟩
    rcases Set.mem_iUnion.mp hparallel with ⟨j, hparallel⟩
    rcases Set.mem_iUnion.mp hparallel with ⟨hij, _⟩
    exact hij (Subsingleton.elim i j)

theorem allBad_eq_empty_of_subsingleton {n : ℕ} [Subsingleton (Fin n)] :
    (allBad : Set (ArrangementParameter n)) = ∅ := by
  ext p
  constructor
  · intro hp
    exact False.elim (not_mem_allBad_of_subsingleton p hp)
  · intro hp
    exact False.elim hp

theorem genericityAvoidance_of_subsingleton {n : ℕ} [Subsingleton (Fin n)] :
    GenericityAvoidance n where
  dense_good := by
    rw [allBad_eq_empty_of_subsingleton]
    simp

theorem genericityAvoidance_zero : GenericityAvoidance 0 :=
  genericityAvoidance_of_subsingleton

theorem genericityAvoidance_one : GenericityAvoidance 1 :=
  genericityAvoidance_of_subsingleton

theorem chamberGenericityAvoidance_of_subsingleton {n : ℕ}
    [Subsingleton (Fin n)] :
    ChamberGenericityAvoidance n :=
  GenericityAvoidance.toChamberGenericityAvoidance
    genericityAvoidance_of_subsingleton

theorem chamberGenericityAvoidance_zero : ChamberGenericityAvoidance 0 :=
  chamberGenericityAvoidance_of_subsingleton

theorem chamberGenericityAvoidance_one : ChamberGenericityAvoidance 1 :=
  chamberGenericityAvoidance_of_subsingleton

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
  exact GenericityPort.good_is_generic hpGood

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

/-- Every nonempty strict pair chamber contains a generic arrangement, using
only the reduced chamber bad-locus avoidance theorem. -/
theorem exists_generic_realizing_pair_codes_of_chamber_avoidance
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (havoid : GenericityPort.ChamberGenericityAvoidance n)
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
  exact GenericityPort.good_is_generic_in_pair_chamber hpU hpGood

/-- Genericization inside a strict chamber preserves every encoded pair
crossing count and requires only the reduced chamber bad-locus avoidance
theorem. -/
theorem exists_generic_with_pairCrossingCounts_of_chamber_avoidance
    {n : ℕ} {S : PairCodeSpec n} {A : Arrangement n}
    (havoid : GenericityPort.ChamberGenericityAvoidance n)
    (hA : RealizesPairCodeSpec S A) :
    ∃ B : Arrangement n,
      IsGeneric B ∧
      ∀ i j : Fin n, i < j →
        pairCrossingCount (B i) (B j) = (S.code i j).crossings := by
  rcases exists_generic_realizing_pair_codes_of_chamber_avoidance havoid hA with
    ⟨B, hB, hgen⟩
  exact ⟨B, hgen, fun i j hij =>
    pairCrossingCount_eq_of_realizes (hB i j hij)⟩

end Lower
end EndToEnd
end Concrete
end Lollipop
