import Lollipop.Lemma_8_3.Proof
import Lollipop.Lemma_3_4.Proof
import Mathlib.Topology.Separation.Connected
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
This is the substantive proof compilation unit for `Lemma_8_4`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `EndToEnd.Lower.Genericity`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

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

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Lemma 8.4 (`lem:genericize`): every nonempty strict pair chamber
contains a generic arrangement with the same pairwise component counts.
-/


/-! Ported from the archived development (`old_lean_folder`): carrier avoidance,
translation genericity, and the unconditional chamber-genericity theorem. -/

/-! ### Ported from `old_lean_folder/Concrete/EndToEnd/CarrierAvoidance.lean` -/

/-!
# Carrier avoidance

A concrete lollipop carrier has empty interior.  This is the local geometric
fact needed by finite triple-contact avoidance: a finite list of translated
carriers cannot fill a nonempty open set of translation parameters.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

namespace Lollipop

/-- The point opposite the stem anchor on the circle. -/
def opposite (L : Lollipop) : Point :=
  L.center - L.radial

theorem opposite_mem_circle (L : Lollipop) : opposite L ∈ L.circle := by
  unfold opposite
  change ‖(L.center - L.radial) - L.center‖ = ‖L.radial‖
  rw [show (L.center - L.radial) - L.center = -L.radial by module]
  simp

theorem anchor_ne_opposite (L : Lollipop) : L.anchor ≠ opposite L := by
  intro h
  apply L.radial_ne_zero
  have h' : L.center + L.radial = L.center - L.radial := by
    simpa [Lollipop.anchor, opposite] using h
  have htwo : (2 : ℝ) • L.radial = 0 := by
    calc
      (2 : ℝ) • L.radial = L.radial + L.radial := by module
      _ = (L.center + L.radial) - (L.center - L.radial) := by module
      _ = 0 := by
        rw [h']
        module
  rcases smul_eq_zero.mp htwo with htwoZero | hradial
  · norm_num at htwoZero
  · exact hradial

theorem circle_infinite (L : Lollipop) : L.circle.Infinite := by
  have hnontrivial : L.circle.Nontrivial :=
    ⟨L.anchor, L.anchor_mem_circle,
      opposite L, opposite_mem_circle L, anchor_ne_opposite L⟩
  exact L.isConnected_circle.isPreconnected.infinite_of_nontrivial hnontrivial

/-- A circle whose radius differs from `L.radius` meets `L.carrier` in a
finite set. -/
theorem circle_inter_carrier_finite_of_radius_ne
    (M L : Lollipop) (hradius : M.radius ≠ L.radius) :
    (M.circle ∩ L.carrier).Finite := by
  have hsphere : concreteSphere M ≠ concreteSphere L := by
    intro h
    exact hradius (congrArg EuclideanGeometry.Sphere.radius h)
  have hcc : (M.circle ∩ L.circle).Finite := by
    change (cc M L).Finite
    apply finite_of_forall_mem_eq_left_or_right
    intro a b x ha hb hx hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx
  have hcr : (M.circle ∩ L.stem).Finite := by
    change (cr M L).Finite
    exact finite_circle_ray_intersection M L
  apply (hcc.union hcr).subset
  intro z hz
  change z ∈ M.circle ∧ (z ∈ L.circle ∨ z ∈ L.stem) at hz
  rcases hz with ⟨hzM, hzLcircle | hzLstem⟩
  · exact Or.inl ⟨hzM, hzLcircle⟩
  · exact Or.inr ⟨hzM, hzLstem⟩

/-- Every nonempty open set contains a point outside a fixed concrete
lollipop carrier. -/
theorem exists_mem_open_not_mem_carrier
    (L : Lollipop) {U : Set Point}
    (hUopen : IsOpen U) {x : Point} (hxU : x ∈ U) :
    ∃ z : Point, z ∈ U ∧ z ∉ L.carrier := by
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  let ρ : ℝ := min ε L.radius / 4
  have hminpos : 0 < min ε L.radius := lt_min hεpos L.radius_pos
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρltε : ρ < ε := by
    have hle := min_le_left ε L.radius
    dsimp [ρ]
    nlinarith
  have hρltRadius : ρ < L.radius := by
    have hle := min_le_right ε L.radius
    dsimp [ρ]
    nlinarith
  let M : Lollipop :=
    { center := x
      radial := ρ • L.unitRadial
      radial_ne_zero := smul_ne_zero (ne_of_gt hρpos) L.unitRadial_ne_zero }
  have hMradius : M.radius = ρ := by
    simp [M, Lollipop.radius, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρpos]
  have hcircleU : M.circle ⊆ U := by
    intro z hz
    apply hball
    rw [Metric.mem_ball]
    have hz' : ‖z - x‖ = ρ := by
      simpa [M, Lollipop.circle, hMradius] using hz
    simpa [dist_eq_norm, hz'] using hρltε
  have hMRadiusNe : M.radius ≠ L.radius := by
    rw [hMradius]
    exact ne_of_lt hρltRadius
  have hinterFinite : (M.circle ∩ L.carrier).Finite :=
    circle_inter_carrier_finite_of_radius_ne M L hMRadiusNe
  by_contra hno
  push Not at hno
  have hcircleSubset : M.circle ⊆ M.circle ∩ L.carrier := by
    intro z hz
    exact ⟨hz, hno z (hcircleU hz)⟩
  exact circle_infinite M (hinterFinite.subset hcircleSubset)

end Lollipop

end EndToEnd
end Concrete
end Lollipop

/-! ### Ported from `old_lean_folder/Concrete/EndToEnd/TranslationGenericity.lean` -/

/-!
# Translation genericity

This module proves the finite-avoidance step used to remove triple contacts
when inserting one lollipop into an arrangement whose old pair-contact sets
are finite.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace TranslationGenericity

open Set

/-- Translate a concrete lollipop by moving its center and retaining its
radial vector. -/
def translate (L : Lollipop) (v : Point) : Lollipop where
  center := L.center + v
  radial := L.radial
  radial_ne_zero := L.radial_ne_zero

/-- The lollipop carrier in translation-parameter space forbidden by one
ambient point `p`. -/
def translationForbidden (L : Lollipop) (p : Point) : Lollipop where
  center := p - L.center
  radial := -L.radial
  radial_ne_zero := by
    intro h
    exact L.radial_ne_zero (neg_eq_zero.mp h)

@[simp] theorem translate_radius (L : Lollipop) (v : Point) :
    (translate L v).radius = L.radius := by
  rfl

@[simp] theorem translationForbidden_radius (L : Lollipop) (p : Point) :
    (translationForbidden L p).radius = L.radius := by
  simp [translationForbidden, Lollipop.radius]

theorem mem_translate_circle_iff (L : Lollipop) (v x : Point) :
    x ∈ (translate L v).circle ↔ x - v ∈ L.circle := by
  have hvec : x - (L.center + v) = (x - v) - L.center := by
    module
  change ‖x - (L.center + v)‖ = L.radius ↔
    ‖(x - v) - L.center‖ = L.radius
  rw [hvec]

theorem mem_translate_stem_iff (L : Lollipop) (v x : Point) :
    x ∈ (translate L v).stem ↔ x - v ∈ L.stem := by
  constructor
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, ?_⟩
    rw [htx]
    change L.center + v + t • L.radial - v =
      L.center + t • L.radial
    module
  · rintro ⟨t, ht, htx⟩
    refine ⟨t, ht, ?_⟩
    change x = L.center + v + t • L.radial
    calc
      x = (x - v) + v := by module
      _ = (L.center + t • L.radial) + v := by rw [htx]
      _ = L.center + v + t • L.radial := by module

theorem mem_translate_carrier_iff (L : Lollipop) (v x : Point) :
    x ∈ (translate L v).carrier ↔ x - v ∈ L.carrier := by
  simp only [Lollipop.carrier, mem_union,
    mem_translate_circle_iff, mem_translate_stem_iff]

theorem mem_translationForbidden_circle_iff
    (L : Lollipop) (p v : Point) :
    v ∈ (translationForbidden L p).circle ↔ p - v ∈ L.circle := by
  have hvec :
      v - (p - L.center) = -((p - v) - L.center) := by
    module
  unfold translationForbidden
  change ‖v - (p - L.center)‖ = ‖-L.radial‖ ↔
    ‖(p - v) - L.center‖ = L.radius
  rw [hvec, norm_neg]
  simp [Lollipop.radius]

theorem mem_translationForbidden_stem_iff
    (L : Lollipop) (p v : Point) :
    v ∈ (translationForbidden L p).stem ↔ p - v ∈ L.stem := by
  constructor
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, ht, ?_⟩
    rw [htv]
    change p - (p - L.center + t • -L.radial) =
      L.center + t • L.radial
    module
  · rintro ⟨t, ht, htp⟩
    refine ⟨t, ht, ?_⟩
    change v = p - L.center + t • -L.radial
    calc
      v = p - (p - v) := by module
      _ = p - (L.center + t • L.radial) := by rw [htp]
      _ = p - L.center + t • -L.radial := by module

theorem mem_translationForbidden_carrier_iff
    (L : Lollipop) (p v : Point) :
    v ∈ (translationForbidden L p).carrier ↔ p - v ∈ L.carrier := by
  simp only [Lollipop.carrier, mem_union,
    mem_translationForbidden_circle_iff,
    mem_translationForbidden_stem_iff]

theorem mem_translate_carrier_iff_mem_translationForbidden
    (L : Lollipop) (p v : Point) :
    p ∈ (translate L v).carrier ↔
      v ∈ (translationForbidden L p).carrier := by
  rw [mem_translate_carrier_iff,
    mem_translationForbidden_carrier_iff]

/-- Avoid finitely many prescribed points on a translated carrier while
choosing the translation vector in an arbitrary nonempty open set. -/
theorem exists_mem_open_forall_not_mem_translate_carrier
    (L : Lollipop) (P : Finset Point)
    {U : Set Point} (hU : IsOpen U) {v₀ : Point} (hv₀ : v₀ ∈ U) :
    ∃ v : Point, v ∈ U ∧
      ∀ p : Point, p ∈ P → p ∉ (translate L v).carrier := by
  classical
  induction P using Finset.induction_on generalizing U v₀ with
  | empty =>
      exact ⟨v₀, hv₀, by simp⟩
  | insert p P hp ih =>
      obtain ⟨w, hwU, hwp⟩ :=
        EndToEnd.Lollipop.exists_mem_open_not_mem_carrier
          (translationForbidden L p) hU hv₀
      let V : Set Point := U ∩ (translationForbidden L p).carrierᶜ
      have hVopen : IsOpen V :=
        hU.inter ((translationForbidden L p).isClosed_carrier).isOpen_compl
      have hwV : w ∈ V := ⟨hwU, hwp⟩
      obtain ⟨v, hvV, havoid⟩ := ih hVopen hwV
      refine ⟨v, hvV.1, ?_⟩
      intro q hq
      rw [Finset.mem_insert] at hq
      rcases hq with rfl | hq
      · intro hpv
        exact hvV.2
          ((mem_translate_carrier_iff_mem_translationForbidden L q v).mp hpv)
      · exact havoid q hq

/-- Pairwise finiteness of old carrier intersections. -/
def PairFiniteArrangement {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ i j : Fin n, i ≠ j → ((A i).carrier ∩ (A j).carrier).Finite

/-- No finite point of the inserted carrier lies on two distinct old
carriers. -/
def NoTripleContactWithInserted {n : ℕ}
    (A : Arrangement n) (L : Lollipop) : Prop :=
  ∀ ⦃i j : Fin n⦄, i ≠ j →
    Disjoint ((A i).carrier ∩ L.carrier)
      ((A j).carrier ∩ L.carrier)

/-- Contact finiteness between every old carrier and one inserted carrier. -/
def PairContactsFinite {n : ℕ} (A : Arrangement n) (L : Lollipop) : Prop :=
  ∀ i : Fin n, ((A i).carrier ∩ L.carrier).Finite

/-- No point lies on three pairwise-distinct carriers.  This unordered form is
the invariant used by the insertion-order genericization route. -/
def NoTripleCarrierPoints {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ i j k : Fin n,
    i ≠ j → i ≠ k → j ≠ k →
      Disjoint
        ((A i).carrier ∩ (A k).carrier)
        ((A j).carrier ∩ (A k).carrier)

/-- The empty arrangement is pairwise finite. -/
theorem pairFiniteArrangement_empty (A : Arrangement 0) :
    PairFiniteArrangement A := by
  intro i
  exact Fin.elim0 i

/-- The empty arrangement has no triple carrier points. -/
theorem noTripleCarrierPoints_empty (A : Arrangement 0) :
    NoTripleCarrierPoints A := by
  intro i
  exact Fin.elim0 i

/-- Pairwise finiteness restricts to every ordered prefix. -/
theorem pairFiniteArrangement_prefix
    {n k : ℕ} (A : Arrangement n) (hk : k ≤ n)
    (hA : PairFiniteArrangement A) :
    PairFiniteArrangement (PlanarInsertion.prefixArrangement A k hk) := by
  intro i j hij
  have hij' :
      (⟨i.1, i.2.trans_le hk⟩ : Fin n) ≠
        ⟨j.1, j.2.trans_le hk⟩ := by
    intro h
    apply hij
    exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
  simpa [PlanarInsertion.prefixArrangement] using
    hA ⟨i.1, i.2.trans_le hk⟩
      ⟨j.1, j.2.trans_le hk⟩ hij'

/-- Absence of triple carrier points restricts to every ordered prefix. -/
theorem noTripleCarrierPoints_prefix
    {n k : ℕ} (A : Arrangement n) (hk : k ≤ n)
    (hA : NoTripleCarrierPoints A) :
    NoTripleCarrierPoints (PlanarInsertion.prefixArrangement A k hk) := by
  intro i j l hij hil hjl
  have hij' :
      (⟨i.1, i.2.trans_le hk⟩ : Fin n) ≠
        ⟨j.1, j.2.trans_le hk⟩ := by
    intro h
    apply hij
    exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
  have hil' :
      (⟨i.1, i.2.trans_le hk⟩ : Fin n) ≠
        ⟨l.1, l.2.trans_le hk⟩ := by
    intro h
    apply hil
    exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
  have hjl' :
      (⟨j.1, j.2.trans_le hk⟩ : Fin n) ≠
        ⟨l.1, l.2.trans_le hk⟩ := by
    intro h
    apply hjl
    exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
  simpa [PlanarInsertion.prefixArrangement] using
    hA ⟨i.1, i.2.trans_le hk⟩
      ⟨j.1, j.2.trans_le hk⟩
      ⟨l.1, l.2.trans_le hk⟩ hij' hil' hjl'

/-- Pairwise finiteness is preserved when the appended lollipop has finite
contact with every old carrier. -/
theorem pairFiniteArrangement_snoc
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    (hA : PairFiniteArrangement A)
    (hL : PairContactsFinite A L) :
    PairFiniteArrangement (Insertion.snocArrangement A L) := by
  intro i j hij
  by_cases hi : i.1 < n
  · by_cases hj : j.1 < n
    · have hijOld : (⟨i.1, hi⟩ : Fin n) ≠ ⟨j.1, hj⟩ := by
        intro h
        apply hij
        exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
      simpa [Insertion.snocArrangement, hi, hj] using
        hA ⟨i.1, hi⟩ ⟨j.1, hj⟩ hijOld
    · simpa [Insertion.snocArrangement, hi, hj] using hL ⟨i.1, hi⟩
  · by_cases hj : j.1 < n
    · simpa [Insertion.snocArrangement, hi, hj, inter_comm] using
        hL ⟨j.1, hj⟩
    · have hieq := Insertion.fin_eq_last_of_not_lt hi
      have hjeq := Insertion.fin_eq_last_of_not_lt hj
      exact (hij (hieq.trans hjeq.symm)).elim

/-- Global no-triple position is preserved by appending a lollipop satisfying
the old/new no-triple contact condition. -/
theorem noTripleCarrierPoints_snoc
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    (hA : NoTripleCarrierPoints A)
    (hL : NoTripleContactWithInserted A L) :
    NoTripleCarrierPoints (Insertion.snocArrangement A L) := by
  intro i j k hij hik hjk
  rw [Set.disjoint_left]
  intro x hxi hxj
  by_cases hkOld : k.1 < n
  · by_cases hiOld : i.1 < n
    · by_cases hjOld : j.1 < n
      · have hijOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨j.1, hjOld⟩ := by
          intro h
          apply hij
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hikOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
          intro h
          apply hik
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hjkOld : (⟨j.1, hjOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
          intro h
          apply hjk
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hd := hA ⟨i.1, hiOld⟩ ⟨j.1, hjOld⟩
          ⟨k.1, hkOld⟩ hijOld hikOld hjkOld
        exact Set.disjoint_left.mp hd
          ⟨by simpa [Insertion.snocArrangement, hiOld] using hxi.1,
            by simpa [Insertion.snocArrangement, hkOld] using hxi.2⟩
          ⟨by simpa [Insertion.snocArrangement, hjOld] using hxj.1,
            by simpa [Insertion.snocArrangement, hkOld] using hxj.2⟩
      · have hikOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
          intro h
          apply hik
          exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
        have hd := hL hikOld
        exact Set.disjoint_left.mp hd
          ⟨by simpa [Insertion.snocArrangement, hiOld] using hxi.1,
            by simpa [Insertion.snocArrangement, hjOld] using hxj.1⟩
          ⟨by simpa [Insertion.snocArrangement, hkOld] using hxi.2,
            by simpa [Insertion.snocArrangement, hjOld] using hxj.1⟩
    · have hiLast := Insertion.fin_eq_last_of_not_lt hiOld
      have hjOld : j.1 < n := by
        by_contra hjNotOld
        have hjLast := Insertion.fin_eq_last_of_not_lt hjNotOld
        exact hij (hiLast.trans hjLast.symm)
      have hjkOld : (⟨j.1, hjOld⟩ : Fin n) ≠ ⟨k.1, hkOld⟩ := by
        intro h
        apply hjk
        exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
      have hd := hL hjkOld
      exact Set.disjoint_left.mp hd
        ⟨by simpa [Insertion.snocArrangement, hjOld] using hxj.1,
          by simpa [Insertion.snocArrangement, hiOld] using hxi.1⟩
        ⟨by simpa [Insertion.snocArrangement, hkOld] using hxi.2,
          by simpa [Insertion.snocArrangement, hiOld] using hxi.1⟩
  · have hkLast := Insertion.fin_eq_last_of_not_lt hkOld
    have hiOld : i.1 < n := by
      by_contra hiNotOld
      have hiLast := Insertion.fin_eq_last_of_not_lt hiNotOld
      exact hik (hiLast.trans hkLast.symm)
    have hjOld : j.1 < n := by
      by_contra hjNotOld
      have hjLast := Insertion.fin_eq_last_of_not_lt hjNotOld
      exact hjk (hjLast.trans hkLast.symm)
    have hijOld : (⟨i.1, hiOld⟩ : Fin n) ≠ ⟨j.1, hjOld⟩ := by
      intro h
      apply hij
      exact Fin.ext (congrArg (fun x : Fin n => x.1) h)
    have hd := hL hijOld
    exact Set.disjoint_left.mp hd
      ⟨by simpa [Insertion.snocArrangement, hiOld] using hxi.1,
        by simpa [Insertion.snocArrangement, hkOld] using hxi.2⟩
      ⟨by simpa [Insertion.snocArrangement, hjOld] using hxj.1,
        by simpa [Insertion.snocArrangement, hkOld] using hxj.2⟩

/-- Union of old pair-contact sets over a finite collection of index pairs. -/
def oldPairContactUnionOn {n : ℕ} (A : Arrangement n)
    (s : Finset (Fin n × Fin n)) : Set Point :=
  InsertionFan.finsetSetUnion s
    (fun p => (A p.1).carrier ∩ (A p.2).carrier)

/-- The finite set of all contacts between distinct old lollipops. -/
def oldDoublePointSet {n : ℕ} (A : Arrangement n) : Set Point :=
  oldPairContactUnionOn A (pairFinset n)

theorem oldPairContactUnionOn_finite
    {n : ℕ} {A : Arrangement n}
    (hfinite : PairFiniteArrangement A)
    (s : Finset (Fin n × Fin n))
    (hdiag : ∀ p ∈ s, p.1 ≠ p.2) :
    (oldPairContactUnionOn A s).Finite := by
  exact InsertionFan.finite_finsetSetUnion s
    (fun p => (A p.1).carrier ∩ (A p.2).carrier)
    (fun p hp => hfinite p.1 p.2 (hdiag p hp))

theorem oldDoublePointSet_finite
    {n : ℕ} {A : Arrangement n}
    (hfinite : PairFiniteArrangement A) :
    (oldDoublePointSet A).Finite := by
  apply oldPairContactUnionOn_finite hfinite
  intro p hp
  rw [pairFinset, Finset.mem_filter] at hp
  exact ne_of_lt hp.2

theorem pair_inter_subset_oldDoublePointSet
    {n : ℕ} (A : Arrangement n) {i j : Fin n} (hij : i ≠ j) :
    (A i).carrier ∩ (A j).carrier ⊆ oldDoublePointSet A := by
  intro x hx
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · apply (InsertionFan.mem_finsetSetUnion_iff (pairFinset n)
      (fun p => (A p.1).carrier ∩ (A p.2).carrier) x).2
    exact ⟨(i, j), by simp [pairFinset, hijlt], hx⟩
  · apply (InsertionFan.mem_finsetSetUnion_iff (pairFinset n)
      (fun p => (A p.1).carrier ∩ (A p.2).carrier) x).2
    exact ⟨(j, i), by simp [pairFinset, hjilt], ⟨hx.2, hx.1⟩⟩

theorem noTripleContactWithInserted_translate_of_disjoint_oldDoublePointSet
    {n : ℕ} (A : Arrangement n) (L : Lollipop) (v : Point)
    (hdisj : Disjoint (translate L v).carrier (oldDoublePointSet A)) :
    NoTripleContactWithInserted A (translate L v) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact Set.disjoint_left.mp hdisj hxi.2
    (pair_inter_subset_oldDoublePointSet A hij ⟨hxi.1, hxj.1⟩)

/-- In every nonempty open neighborhood of translation space there is a
translation eliminating all triple contacts with a pairwise-finite old
arrangement. -/
theorem exists_mem_open_noTripleContactWithInserted_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    {U : Set Point} (hU : IsOpen U) {v₀ : Point} (hv₀ : v₀ ∈ U) :
    ∃ v : Point, v ∈ U ∧
      NoTripleContactWithInserted A (translate L v) := by
  classical
  let P : Set Point := oldDoublePointSet A
  have hP : P.Finite := oldDoublePointSet_finite hfinite
  obtain ⟨v, hvU, havoid⟩ :=
    exists_mem_open_forall_not_mem_translate_carrier
      L hP.toFinset hU hv₀
  have hdisj : Disjoint (translate L v).carrier P := by
    rw [Set.disjoint_left]
    intro p hpL hpP
    exact havoid p (hP.mem_toFinset.mpr hpP) hpL
  exact ⟨v, hvU,
    noTripleContactWithInserted_translate_of_disjoint_oldDoublePointSet
      A L v hdisj⟩

/-- Metric form: the triple-removing translation can be chosen with
arbitrarily small norm. -/
theorem exists_norm_lt_noTripleContactWithInserted_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : Point, ‖v‖ < ε ∧
      NoTripleContactWithInserted A (translate L v) := by
  have hzero : (0 : Point) ∈ Metric.ball (0 : Point) ε := by
    simpa [Metric.mem_ball] using hε
  obtain ⟨v, hv, htriple⟩ :=
    exists_mem_open_noTripleContactWithInserted_translate
      A L hfinite Metric.isOpen_ball hzero
  refine ⟨v, ?_, htriple⟩
  simpa [Metric.mem_ball, dist_eq_norm] using hv

/-- The old/new pair profiles are constant throughout a prescribed open ball
of translation parameters.  This is the stability input needed when the lower
construction removes triple contacts without changing the extremal pair
table. -/
def PairProfilesStableInBall {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (ε : ℝ) : Prop :=
  ∀ v : Point, ‖v‖ < ε → ∀ i : Fin n,
    pairExcess (A i) (translate L v) = pairExcess (A i) L

/-- One insertion-order genericization step.

If all sufficiently small translations retain finite contact with every old
carrier, then one can choose such a translation which simultaneously preserves
pairwise finiteness and extends global no-triple position. -/
theorem exists_norm_lt_pairFinite_noTriple_snoc_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    (htriple : NoTripleCarrierPoints A)
    {ε : ℝ} (hε : 0 < ε)
    (hcontacts : ∀ v : Point, ‖v‖ < ε →
      PairContactsFinite A (translate L v)) :
    ∃ v : Point, ‖v‖ < ε ∧
      PairFiniteArrangement (Insertion.snocArrangement A (translate L v)) ∧
      NoTripleCarrierPoints (Insertion.snocArrangement A (translate L v)) := by
  obtain ⟨v, hv, hnewTriple⟩ :=
    exists_norm_lt_noTripleContactWithInserted_translate A L hfinite hε
  exact ⟨v, hv,
    pairFiniteArrangement_snoc hfinite (hcontacts v hv),
    noTripleCarrierPoints_snoc htriple hnewTriple⟩

/-- The same one-step choice can retain every old/new pair profile.

The stability hypothesis is deliberately explicit: this theorem supplies the
finite avoidance and append bookkeeping, while the analytic proof that a
suitable profile-stability ball exists remains a separate target. -/
theorem exists_norm_lt_preservePairProfiles_pairFinite_noTriple_snoc_translate
    {n : ℕ} (A : Arrangement n) (L : Lollipop)
    (hfinite : PairFiniteArrangement A)
    (htriple : NoTripleCarrierPoints A)
    {ε : ℝ} (hε : 0 < ε)
    (hcontacts : ∀ v : Point, ‖v‖ < ε →
      PairContactsFinite A (translate L v))
    (hprofiles : PairProfilesStableInBall A L ε) :
    ∃ v : Point, ‖v‖ < ε ∧
      (∀ i : Fin n,
        pairExcess (A i) (translate L v) = pairExcess (A i) L) ∧
      PairFiniteArrangement (Insertion.snocArrangement A (translate L v)) ∧
      NoTripleCarrierPoints (Insertion.snocArrangement A (translate L v)) := by
  obtain ⟨v, hv, hpair, hglobal⟩ :=
    exists_norm_lt_pairFinite_noTriple_snoc_translate
      A L hfinite htriple hε hcontacts
  exact ⟨v, hv, hprofiles v hv, hpair, hglobal⟩

end TranslationGenericity
end EndToEnd
end Concrete
end Lollipop

/-! ### Ported from `old_lean_folder/Concrete/EndToEnd/MainTheorem/Genericity.lean` -/

/-!
# Main theorem spine: lower genericity

This file states the concrete genericity-avoidance theorem needed by the final
certificate-free endpoint.

The theorem is not a caller-facing certificate.  It is the named target for
the finite bad-locus avoidance proof.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Genericity

/-- There are no three pairwise-distinct indices in `Fin n` when `n < 3`. -/
theorem no_three_distinct_fin_of_lt_three {n : ℕ} (hn : n < 3) :
    ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → False := by
  intro i j k hij hik hjk
  have hijv : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  have hikv : i.1 ≠ k.1 := fun h => hik (Fin.ext h)
  have hjkv : j.1 ≠ k.1 := fun h => hjk (Fin.ext h)
  have hi3 : i.1 < 3 := lt_trans i.2 hn
  have hj3 : j.1 < 3 := lt_trans j.2 hn
  have hk3 : k.1 < 3 := lt_trans k.2 hn
  omega

/-- For `n < 3`, the triple-contact bad locus is empty and hence avoidable. -/
theorem dense_compl_tripleBadUnion_of_lt_three {n : ℕ} (hn : n < 3) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  rw [Lower.GenericityPort.tripleBadUnion_eq_empty_of_no_three_distinct
    (no_three_distinct_fin_of_lt_three hn)]
  simp

/-- Ordered triples of pairwise-distinct indices.  This packages the index
and proof arguments in `Lower.GenericityPort.tripleBadUnion` into one finite
type, so the remaining density theorem can be reduced to finitely many fixed
triple-incidence loci. -/
abbrev OrderedTripleIndex (n : ℕ) :=
  {ijk : Fin n × Fin n × Fin n //
    ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2}

/-- The good locus for one ordered triple of pairwise-distinct indices. -/
def orderedTripleGood {n : ℕ} (t : OrderedTripleIndex n) :
    Set (Lower.ArrangementParameter n) :=
  (Lower.GenericityPort.tripleBadSet
    t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2.1 t.2.2.2)ᶜ

/-- Parameter locus where one selected pair has finite carrier contact. -/
def pairFiniteGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p | ((p.toArrangement i).carrier ∩
    (p.toArrangement j).carrier).Finite}

/-- A stronger, elementary good locus for one pair: unequal circles and
nonparallel stems.  This is the explicit geometric condition currently used
as the next density target for pair-finiteness. -/
def pairRegularGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p |
    (p.toArrangement i).circle ≠ (p.toArrangement j).circle ∧
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0}

/-- Stronger open pair-regular locus: distinct centers and nonparallel stems.
This implies `pairRegularGood`, but is better suited to finite neighborhood
arguments because it is visibly open in the center/radial parameter space. -/
def pairCenterRegularGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p |
    (p.toArrangement i).center ≠ (p.toArrangement j).center ∧
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0}

/-- The center-regular locus is open. -/
theorem isOpen_pairCenterRegularGood {n : ℕ} (i j : Fin n) :
    IsOpen (pairCenterRegularGood i j) := by
  have hcenter_i : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement i).center) :=
    Lower.continuous_lollipop_center_comp
      (Lower.continuous_toLollipop.comp (continuous_apply i))
  have hcenter_j : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement j).center) :=
    Lower.continuous_lollipop_center_comp
      (Lower.continuous_toLollipop.comp (continuous_apply j))
  have hradial_i : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement i).radial) :=
    Lower.continuous_lollipop_radial_comp
      (Lower.continuous_toLollipop.comp (continuous_apply i))
  have hradial_j : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement j).radial) :=
    Lower.continuous_lollipop_radial_comp
      (Lower.continuous_toLollipop.comp (continuous_apply j))
  have hcenterOpen : IsOpen {p : Lower.ArrangementParameter n |
      (p.toArrangement i).center ≠ (p.toArrangement j).center} :=
    isOpen_ne_fun hcenter_i hcenter_j
  have hdet : Continuous (fun p : Lower.ArrangementParameter n =>
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial) :=
    continuous_detPoint_comp hradial_i hradial_j
  have hdetOpen : IsOpen {p : Lower.ArrangementParameter n |
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0} :=
    isOpen_ne_fun hdet continuous_const
  change IsOpen
    ({p : Lower.ArrangementParameter n |
      (p.toArrangement i).center ≠ (p.toArrangement j).center} ∩
    {p : Lower.ArrangementParameter n |
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0})
  exact hcenterOpen.inter hdetOpen

/-- Distinct circles plus nonparallel stems imply finite carrier contact. -/
theorem pairCrossingSet_finite_of_circle_ne_of_nonparallel
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle)
    (hdet : detPoint L.radial M.radial ≠ 0) :
    (pairCrossingSet L M).Finite := by
  have hccFin : (cc L M).Finite :=
    finite_circle_intersection_of_ne hcircle
  have hrcFin : (rc L M).Finite :=
    finite_ray_circle_intersection L M
  have hcrFin : (cr L M).Finite :=
    finite_circle_ray_intersection L M
  have hrrFin : (rr L M).Finite := by
    by_cases hrr : (rr L M).Nonempty
    · exact finite_of_subsingleton_of_mem
        (rr_subsingleton_of_transverse hdet) hrr.some_mem
    · rw [Set.not_nonempty_iff_eq_empty.mp hrr]
      exact Set.finite_empty
  rw [pairCrossingSet_decompose]
  exact ((hccFin.union hrcFin).union hcrFin).union hrrFin

/-- The elementary pair-regular locus is contained in the finite-contact
locus. -/
theorem pairRegularGood_subset_pairFiniteGood {n : ℕ} (i j : Fin n) :
    pairRegularGood i j ⊆ pairFiniteGood i j := by
  intro p hp
  exact pairCrossingSet_finite_of_circle_ne_of_nonparallel hp.1 hp.2

/-- Distinct centers force distinct circle sets. -/
theorem circle_ne_of_center_ne {L M : Lollipop}
    (hcenter : L.center ≠ M.center) :
    L.circle ≠ M.circle := by
  intro hcircle
  have hsphere : concreteSphere L ≠ concreteSphere M := by
    intro hsphere
    exact hcenter (congrArg EuclideanGeometry.Sphere.center hsphere)
  have hccFinite : (cc L M).Finite := by
    apply finite_of_forall_mem_eq_left_or_right
    intro a b x ha hb hx hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx
  have hcircleSubset : L.circle ⊆ cc L M := by
    intro x hx
    exact ⟨hx, by simpa [hcircle] using hx⟩
  exact (_root_.Lollipop.Concrete.EndToEnd.Lollipop.circle_infinite L)
    (hccFinite.subset hcircleSubset)

/-- Center-regular pairs are pair-regular in the carrier-finiteness sense. -/
theorem pairCenterRegularGood_subset_pairRegularGood {n : ℕ}
    (i j : Fin n) :
    pairCenterRegularGood i j ⊆ pairRegularGood i j := by
  intro p hp
  exact ⟨circle_ne_of_center_ne hp.1, hp.2⟩

/-- Center-regular pairs have finite carrier contact. -/
theorem pairCenterRegularGood_subset_pairFiniteGood {n : ℕ}
    (i j : Fin n) :
    pairCenterRegularGood i j ⊆ pairFiniteGood i j :=
  (pairCenterRegularGood_subset_pairRegularGood i j).trans
    (pairRegularGood_subset_pairFiniteGood i j)

/-- Translate one parameter in an arrangement parameter vector. -/
def translateParameterAt {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) (v : Point) :
    Lower.ArrangementParameter n :=
  fun a =>
    if _h : a = k then
      ⟨((p a).1.1 + v, (p a).1.2), (p a).2⟩
    else p a

@[simp] theorem translateParameterAt_zero {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) :
    translateParameterAt p k 0 = p := by
  funext a
  by_cases ha : a = k
  · simp [translateParameterAt, ha]
  · simp [translateParameterAt, ha]

theorem translateParameterAt_apply_self {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) (v : Point) :
    (translateParameterAt p k v).toArrangement k =
      TranslationGenericity.translate (p.toArrangement k) v := by
  ext <;>
    simp [translateParameterAt, Lower.ArrangementParameter.toArrangement,
      Lower.LollipopParameter.toLollipop, TranslationGenericity.translate]

theorem translateParameterAt_apply_ne {n : ℕ}
    (p : Lower.ArrangementParameter n) {a k : Fin n} (v : Point)
    (hak : a ≠ k) :
    (translateParameterAt p k v).toArrangement a =
      p.toArrangement a := by
  simp [translateParameterAt, Lower.ArrangementParameter.toArrangement, hak]

/-- The one-parameter translation path is continuous in the raw center/radial
parameter space. -/
theorem continuous_translateParameterAt {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) :
    Continuous (fun v : Point => translateParameterAt p k v) := by
  apply continuous_pi
  intro a
  by_cases ha : a = k
  · rw [continuous_induced_rng]
    change Continuous (fun v : Point => (translateParameterAt p k v a).1)
    simp [translateParameterAt, ha]
    constructor <;> fun_prop
  · rw [show (fun v : Point => translateParameterAt p k v a) =
        fun _v : Point => p a by
      funext v
      simp [translateParameterAt, ha]]
    exact continuous_const

/-- The center-regular locus is dense for every ordered distinct pair. -/
theorem dense_pairCenterRegularGood {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Dense (pairCenterRegularGood i j) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases
    (Lower.GenericityPort.dense_compl_parallelBadSet i j hij).exists_mem_open
      hU hUne with
    ⟨p, hpParallel, hpU⟩
  have hpDet :
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0 := by
    change p ∉ Lower.GenericityPort.parallelBadSet i j hij at hpParallel
    exact hpParallel
  by_cases hcenter :
      (p.toArrangement i).center ≠ (p.toArrangement j).center
  · exact ⟨p, hpU, hcenter, hpDet⟩
  · have hcenterEq :
        (p.toArrangement i).center = (p.toArrangement j).center :=
      not_not.mp hcenter
    let V : Set (Lower.ArrangementParameter n) :=
      U ∩ (Lower.GenericityPort.parallelBadSet i j hij)ᶜ
    have hVopen : IsOpen V :=
      hU.inter (Lower.GenericityPort.isOpen_compl_parallelBadSet i j hij)
    have hpV : p ∈ V := ⟨hpU, hpParallel⟩
    let γ : Point → Lower.ArrangementParameter n :=
      fun v => translateParameterAt p j v
    have hγcont : Continuous γ :=
      continuous_translateParameterAt p j
    have hpreOpen : IsOpen (γ ⁻¹' V) := hVopen.preimage hγcont
    have hzero : (0 : Point) ∈ γ ⁻¹' V := by
      change γ 0 ∈ V
      simpa [γ] using hpV
    have hnhds : γ ⁻¹' V ∈ nhds (0 : Point) :=
      hpreOpen.mem_nhds hzero
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
    let v : Point := (ε / 2) • (p.toArrangement i).unitRadial
    have hεhalf : 0 < ε / 2 := by linarith
    have hv_ne : v ≠ 0 := by
      exact smul_ne_zero (ne_of_gt hεhalf)
        (p.toArrangement i).unitRadial_ne_zero
    have hvball : v ∈ Metric.ball (0 : Point) ε := by
      have hhalf_lt : |ε| / 2 < ε := by
        rw [abs_of_pos hεpos]
        linarith
      simpa [Metric.mem_ball, dist_eq_norm, v, norm_smul,
        Real.norm_eq_abs, abs_of_pos hεhalf,
        (p.toArrangement i).norm_unitRadial] using hhalf_lt
    have hqV : γ v ∈ V := hεsub hvball
    refine ⟨γ v, hqV.1, ?_⟩
    have hi :
        (γ v).toArrangement i = p.toArrangement i := by
      simpa [γ] using
        translateParameterAt_apply_ne p (a := i) (k := j) v hij
    have hj :
        (γ v).toArrangement j =
          TranslationGenericity.translate (p.toArrangement j) v := by
      simpa [γ] using translateParameterAt_apply_self p j v
    have hcenterNe :
        ((γ v).toArrangement i).center ≠
          ((γ v).toArrangement j).center := by
      intro hcent
      rw [hi, hj] at hcent
      change (p.toArrangement i).center =
        (p.toArrangement j).center + v at hcent
      have hv_zero : v = 0 := by
        calc
          v = ((p.toArrangement j).center + v) -
              (p.toArrangement j).center := by module
          _ = (p.toArrangement i).center -
              (p.toArrangement j).center := by rw [← hcent]
          _ = 0 := by rw [hcenterEq]; module
      exact hv_ne hv_zero
    constructor
    · exact hcenterNe
    · have hqParallel :
          γ v ∉ Lower.GenericityPort.parallelBadSet i j hij := hqV.2
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0 at hqParallel
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0
      exact hqParallel

/-- Finite index type for ordered distinct pairs. -/
abbrev OrderedDistinctPairIndex (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 ≠ ij.2}

/-- All ordered distinct pairs are center-regular. -/
def allPairCenterRegularGood {n : ℕ} :
    Set (Lower.ArrangementParameter n) :=
  ⋂ ij : OrderedDistinctPairIndex n,
    pairCenterRegularGood ij.1.1 ij.1.2

/-- The all-pairs center-regular locus is open. -/
theorem isOpen_allPairCenterRegularGood {n : ℕ} :
    IsOpen (allPairCenterRegularGood (n := n)) := by
  classical
  unfold allPairCenterRegularGood
  apply isOpen_iInter_of_finite
  intro ij
  exact isOpen_pairCenterRegularGood ij.1.1 ij.1.2

/-- The all-pairs center-regular locus is dense. -/
theorem dense_allPairCenterRegularGood {n : ℕ} :
    Dense (allPairCenterRegularGood (n := n)) := by
  classical
  unfold allPairCenterRegularGood
  exact
    Lower.GenericityPort.dense_iInter_fintype_of_open_dense
      (fun ij : OrderedDistinctPairIndex n =>
        pairCenterRegularGood ij.1.1 ij.1.2)
      (by
        intro ij
        exact isOpen_pairCenterRegularGood ij.1.1 ij.1.2)
      (by
        intro ij
        exact dense_pairCenterRegularGood ij.1.1 ij.1.2 ij.2)

/-- An arrangement in the all-pairs center-regular locus has finite contact
between every distinct pair of carriers. -/
theorem pairFiniteArrangement_of_mem_allPairCenterRegularGood {n : ℕ}
    {p : Lower.ArrangementParameter n}
    (hp : p ∈ allPairCenterRegularGood (n := n)) :
    TranslationGenericity.PairFiniteArrangement p.toArrangement := by
  intro i j hij
  have hpij :
      p ∈ pairCenterRegularGood i j := by
    exact Set.mem_iInter.mp hp ⟨(i, j), hij⟩
  exact (pairCenterRegularGood_subset_pairFiniteGood i j hpij)

/-- Around a point in an open all-pairs center-regular neighborhood, small
translations of one selected center remain inside that same neighborhood. -/
theorem exists_norm_ball_translateParameterAt_subset_open_allPairCenterRegularGood
    {n : ℕ} {p : Lower.ArrangementParameter n} (k : Fin n)
    {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hpPair : p ∈ allPairCenterRegularGood (n := n)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : Point, ‖v‖ < ε →
        translateParameterAt p k v ∈
          U ∩ allPairCenterRegularGood (n := n) := by
  let V : Set (Lower.ArrangementParameter n) :=
    U ∩ allPairCenterRegularGood (n := n)
  have hVopen : IsOpen V :=
    hU.inter isOpen_allPairCenterRegularGood
  have hpV : p ∈ V := ⟨hpU, hpPair⟩
  let γ : Point → Lower.ArrangementParameter n :=
    fun v => translateParameterAt p k v
  have hγcont : Continuous γ :=
    continuous_translateParameterAt p k
  have hpreOpen : IsOpen (γ ⁻¹' V) := hVopen.preimage hγcont
  have hzero : (0 : Point) ∈ γ ⁻¹' V := by
    change γ 0 ∈ V
    simpa [γ] using hpV
  have hnhds : γ ⁻¹' V ∈ nhds (0 : Point) :=
    hpreOpen.mem_nhds hzero
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro v hv
  exact hεsub (by simpa [Metric.mem_ball, dist_eq_norm] using hv)

/-- If a translated full parameter remains in the all-pairs center-regular
locus, then every old member of the `k`-prefix has finite contact with the
translated `k`th lollipop. -/
theorem pairContactsFinite_prefix_translate_of_mem_allPairCenterRegularGood
    {n k : ℕ} {p : Lower.ArrangementParameter n} (hk : k < n)
    {v : Point}
    (hp :
      translateParameterAt p ⟨k, hk⟩ v ∈
        allPairCenterRegularGood (n := n)) :
    TranslationGenericity.PairContactsFinite
      (PlanarInsertion.prefixArrangement p.toArrangement k (Nat.le_of_lt hk))
      (TranslationGenericity.translate (p.toArrangement ⟨k, hk⟩) v) := by
  intro i
  let q : Lower.ArrangementParameter n := translateParameterAt p ⟨k, hk⟩ v
  have hqfinite :
      TranslationGenericity.PairFiniteArrangement q.toArrangement :=
    pairFiniteArrangement_of_mem_allPairCenterRegularGood hp
  let ii : Fin n := ⟨i.1, lt_trans i.2 hk⟩
  let kk : Fin n := ⟨k, hk⟩
  have hik : ii ≠ kk := by
    intro h
    have hv := congrArg (fun x : Fin n => x.1) h
    dsimp [ii, kk] at hv
    omega
  have hqi : q.toArrangement ii = p.toArrangement ii := by
    simpa [q, ii, kk] using
      translateParameterAt_apply_ne p (a := ii) (k := kk) v hik
  have hqk :
      q.toArrangement kk =
        TranslationGenericity.translate (p.toArrangement kk) v := by
    simpa [q, kk] using translateParameterAt_apply_self p kk v
  have hfin := hqfinite ii kk hik
  simpa [PlanarInsertion.prefixArrangement, ii, kk, hqi, hqk] using hfin

/-- Updating the `k`th center and then taking the `(k+1)`-prefix is the same
as appending the translated `k`th lollipop to the old `k`-prefix. -/
theorem prefix_translateParameterAt_succ_eq_snoc
    {n k : ℕ} (p : Lower.ArrangementParameter n) (hk : k < n)
    (v : Point) :
    PlanarInsertion.prefixArrangement
        (translateParameterAt p ⟨k, hk⟩ v).toArrangement
        (k + 1) (Nat.succ_le_of_lt hk) =
      Insertion.snocArrangement
        (PlanarInsertion.prefixArrangement p.toArrangement k
          (Nat.le_of_lt hk))
        (TranslationGenericity.translate (p.toArrangement ⟨k, hk⟩) v) := by
  funext i
  by_cases hik : i.1 < k
  · let ii : Fin n := ⟨i.1, i.2.trans_le (Nat.succ_le_of_lt hk)⟩
    let iiOld : Fin n := ⟨i.1, lt_trans hik hk⟩
    let kk : Fin n := ⟨k, hk⟩
    have hii : ii = iiOld := by
      exact Fin.ext rfl
    have hine : ii ≠ kk := by
      intro h
      have hv := congrArg (fun x : Fin n => x.1) h
      dsimp [ii, kk] at hv
      omega
    have happly :
        (translateParameterAt p kk v).toArrangement ii =
          p.toArrangement ii := by
      simpa [kk] using
        translateParameterAt_apply_ne p (a := ii) (k := kk) v hine
    simp [PlanarInsertion.prefixArrangement, Insertion.snocArrangement,
      hik, happly, hii, ii, iiOld, kk]
  · have hi : i = Fin.last k := Insertion.fin_eq_last_of_not_lt hik
    subst i
    let kk : Fin n := ⟨k, hk⟩
    have happly :
        (translateParameterAt p kk v).toArrangement kk =
          TranslationGenericity.translate (p.toArrangement kk) v := by
      simpa [kk] using translateParameterAt_apply_self p kk v
    simp [PlanarInsertion.prefixArrangement, Insertion.snocArrangement,
      happly, kk]

/-- One step of the finite prefix genericization: translate the `k`th
lollipop while staying in the prescribed open all-pairs regular locus, and
extend no-triple position from the `k`-prefix to the `(k+1)`-prefix. -/
theorem exists_translateParameterAt_step_prefix_noTriple
    {n k : ℕ} {p : Lower.ArrangementParameter n} (hk : k < n)
    {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hpPair : p ∈ allPairCenterRegularGood (n := n))
    (htriple :
      TranslationGenericity.NoTripleCarrierPoints
        (PlanarInsertion.prefixArrangement p.toArrangement k
          (Nat.le_of_lt hk))) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∈ allPairCenterRegularGood (n := n) ∧
        TranslationGenericity.NoTripleCarrierPoints
          (PlanarInsertion.prefixArrangement q.toArrangement (k + 1)
            (Nat.succ_le_of_lt hk)) ∧
        ∃ v : Point, q = translateParameterAt p ⟨k, hk⟩ v := by
  obtain ⟨ε, hεpos, hball⟩ :=
    exists_norm_ball_translateParameterAt_subset_open_allPairCenterRegularGood
      ⟨k, hk⟩ hU hpU hpPair
  let Aold : Arrangement k :=
    PlanarInsertion.prefixArrangement p.toArrangement k (Nat.le_of_lt hk)
  let Lnew : Lollipop := p.toArrangement ⟨k, hk⟩
  have hfinite : TranslationGenericity.PairFiniteArrangement Aold := by
    exact TranslationGenericity.pairFiniteArrangement_prefix
      p.toArrangement (Nat.le_of_lt hk)
      (pairFiniteArrangement_of_mem_allPairCenterRegularGood hpPair)
  have hcontacts :
      ∀ v : Point, ‖v‖ < ε →
        TranslationGenericity.PairContactsFinite Aold
          (TranslationGenericity.translate Lnew v) := by
    intro v hv
    have hpvPair :
        translateParameterAt p ⟨k, hk⟩ v ∈
          allPairCenterRegularGood (n := n) := (hball v hv).2
    simpa [Aold, Lnew] using
      pairContactsFinite_prefix_translate_of_mem_allPairCenterRegularGood
        (p := p) hk hpvPair
  obtain ⟨v, hv, _hpair, htri⟩ :=
    TranslationGenericity.exists_norm_lt_pairFinite_noTriple_snoc_translate
      Aold Lnew hfinite htriple hεpos hcontacts
  let q : Lower.ArrangementParameter n := translateParameterAt p ⟨k, hk⟩ v
  have hqOpenPair :
      q ∈ U ∩ allPairCenterRegularGood (n := n) := hball v hv
  refine ⟨q, hqOpenPair.1, hqOpenPair.2, ?_, ⟨v, rfl⟩⟩
  change
    TranslationGenericity.NoTripleCarrierPoints
      (PlanarInsertion.prefixArrangement
        (translateParameterAt p ⟨k, hk⟩ v).toArrangement
        (k + 1) (Nat.succ_le_of_lt hk))
  rw [prefix_translateParameterAt_succ_eq_snoc p hk v]
  simpa [Aold, Lnew] using htri

/-- Finite prefix induction for the concrete triple-genericity construction.

Starting from any point in an open all-pairs center-regular locus, repeatedly
translate the next indexed lollipop by a sufficiently small vector.  The
construction stays in the same open set and extends no-triple position from
the current prefix to the next prefix at each step. -/
theorem exists_mem_open_allPairCenterRegularGood_prefix_noTriple
    {n : ℕ} {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) {p : Lower.ArrangementParameter n}
    (hpU : p ∈ U) (hpPair : p ∈ allPairCenterRegularGood (n := n)) :
    ∀ k : ℕ, ∀ hk : k ≤ n,
      ∃ q : Lower.ArrangementParameter n,
        q ∈ U ∧
          q ∈ allPairCenterRegularGood (n := n) ∧
          TranslationGenericity.NoTripleCarrierPoints
            (PlanarInsertion.prefixArrangement q.toArrangement k hk) := by
  intro k
  induction k with
  | zero =>
      intro hk
      refine ⟨p, hpU, hpPair, ?_⟩
      exact TranslationGenericity.noTripleCarrierPoints_empty
        (PlanarInsertion.prefixArrangement p.toArrangement 0 hk)
  | succ k ih =>
      intro hkSucc
      have hklt : k < n := Nat.lt_of_succ_le hkSucc
      have hk : k ≤ n := Nat.le_of_lt hklt
      rcases ih hk with ⟨p', hp'U, hp'Pair, hp'Triple⟩
      rcases
        exists_translateParameterAt_step_prefix_noTriple
          (p := p') hklt hU hp'U hp'Pair hp'Triple with
        ⟨q, hqU, hqPair, hqTriple, _hv⟩
      refine ⟨q, hqU, hqPair, ?_⟩
      simpa [Nat.succ_eq_add_one] using hqTriple

/-- Every open set meeting the all-pairs center-regular locus also contains a
point whose full concrete arrangement has no triple carrier point. -/
theorem exists_mem_open_allPairCenterRegularGood_noTriple
    {n : ℕ} {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) {p : Lower.ArrangementParameter n}
    (hpU : p ∈ U) (hpPair : p ∈ allPairCenterRegularGood (n := n)) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∈ allPairCenterRegularGood (n := n) ∧
        TranslationGenericity.NoTripleCarrierPoints q.toArrangement := by
  rcases
    exists_mem_open_allPairCenterRegularGood_prefix_noTriple
      hU hpU hpPair n le_rfl with
    ⟨q, hqU, hqPair, hqTriple⟩
  refine ⟨q, hqU, hqPair, ?_⟩
  rw [PlanarInsertion.prefix_full q.toArrangement] at hqTriple
  exact hqTriple

/-- The elementary pair-regular locus is dense for every ordered distinct
pair.  The proof first enters the already-proved nonparallel-stem locus, then
translates only the second center inside that open set.  Radials are unchanged,
so nonparallelness is preserved, while the nonzero center translation forces
the two circle sets to be distinct. -/
theorem dense_pairRegularGood {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Dense (pairRegularGood i j) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases
    (Lower.GenericityPort.dense_compl_parallelBadSet i j hij).exists_mem_open
      hU hUne with
    ⟨p, hpParallel, hpU⟩
  have hpDet :
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0 := by
    change p ∉ Lower.GenericityPort.parallelBadSet i j hij at hpParallel
    exact hpParallel
  by_cases hcircle :
      (p.toArrangement i).circle ≠ (p.toArrangement j).circle
  · exact ⟨p, hpU, hcircle, hpDet⟩
  · have hcircleEq :
        (p.toArrangement i).circle = (p.toArrangement j).circle :=
      not_not.mp hcircle
    have hcenterEq :
        (p.toArrangement i).center = (p.toArrangement j).center := by
      by_contra hcenterNe
      exact hcircle (circle_ne_of_center_ne hcenterNe)
    let V : Set (Lower.ArrangementParameter n) :=
      U ∩ (Lower.GenericityPort.parallelBadSet i j hij)ᶜ
    have hVopen : IsOpen V :=
      hU.inter (Lower.GenericityPort.isOpen_compl_parallelBadSet i j hij)
    have hpV : p ∈ V := ⟨hpU, hpParallel⟩
    let γ : Point → Lower.ArrangementParameter n :=
      fun v => translateParameterAt p j v
    have hγcont : Continuous γ :=
      continuous_translateParameterAt p j
    have hpreOpen : IsOpen (γ ⁻¹' V) := hVopen.preimage hγcont
    have hzero : (0 : Point) ∈ γ ⁻¹' V := by
      change γ 0 ∈ V
      simpa [γ] using hpV
    have hnhds : γ ⁻¹' V ∈ nhds (0 : Point) :=
      hpreOpen.mem_nhds hzero
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
    let v : Point := (ε / 2) • (p.toArrangement i).unitRadial
    have hεhalf : 0 < ε / 2 := by linarith
    have hv_ne : v ≠ 0 := by
      exact smul_ne_zero (ne_of_gt hεhalf)
        (p.toArrangement i).unitRadial_ne_zero
    have hvball : v ∈ Metric.ball (0 : Point) ε := by
      have hhalf_lt : |ε| / 2 < ε := by
        rw [abs_of_pos hεpos]
        linarith
      simpa [Metric.mem_ball, dist_eq_norm, v, norm_smul,
        Real.norm_eq_abs, abs_of_pos hεhalf,
        (p.toArrangement i).norm_unitRadial] using hhalf_lt
    have hqV : γ v ∈ V := hεsub hvball
    refine ⟨γ v, hqV.1, ?_⟩
    have hi :
        (γ v).toArrangement i = p.toArrangement i := by
      simpa [γ] using
        translateParameterAt_apply_ne p (a := i) (k := j) v hij
    have hj :
        (γ v).toArrangement j =
          TranslationGenericity.translate (p.toArrangement j) v := by
      simpa [γ] using translateParameterAt_apply_self p j v
    have hcenterNe :
        ((γ v).toArrangement i).center ≠
          ((γ v).toArrangement j).center := by
      intro hcent
      rw [hi, hj] at hcent
      change (p.toArrangement i).center =
        (p.toArrangement j).center + v at hcent
      have hv_zero : v = 0 := by
        calc
          v = ((p.toArrangement j).center + v) -
              (p.toArrangement j).center := by module
          _ = (p.toArrangement i).center -
              (p.toArrangement j).center := by rw [← hcent]
          _ = 0 := by rw [hcenterEq]; module
      exact hv_ne hv_zero
    constructor
    · exact circle_ne_of_center_ne hcenterNe
    · have hqParallel :
          γ v ∉ Lower.GenericityPort.parallelBadSet i j hij := hqV.2
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0 at hqParallel
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0
      exact hqParallel

/-- Two-lollipop arrangement used to feed the translation-avoidance theorem
for a fixed old pair. -/
def twoArrangement (L M : Lollipop) : Arrangement 2 :=
  fun a => if a = (0 : Fin 2) then L else M

@[simp] theorem twoArrangement_zero (L M : Lollipop) :
    twoArrangement L M (0 : Fin 2) = L := by
  simp [twoArrangement]

@[simp] theorem twoArrangement_one (L M : Lollipop) :
    twoArrangement L M (1 : Fin 2) = M := by
  simp [twoArrangement]

theorem pairFinite_twoArrangement_of_finite {L M : Lollipop}
    (hfinite : (L.carrier ∩ M.carrier).Finite) :
    TranslationGenericity.PairFiniteArrangement (twoArrangement L M) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · simpa using hfinite
  · simpa [Set.inter_comm] using hfinite
  · exact False.elim (hab rfl)

/-- Local triple-contact avoidance for one ordered triple.

If the first two carriers already have finite contact, then translating the
third lollipop inside any open parameter neighborhood avoids common points of
the three selected carriers.  This is the bridge from the tracked
`TranslationGenericity` module to the remaining finite-avoidance theorem. -/
theorem exists_mem_open_not_tripleBadSet_of_pairFinite_at {n : ℕ}
    {p : Lower.ArrangementParameter n} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hfinite :
      ((p.toArrangement i).carrier ∩
        (p.toArrangement j).carrier).Finite)
    {U : Set (Lower.ArrangementParameter n)} (hU : IsOpen U)
    (hpU : p ∈ U) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∉ Lower.GenericityPort.tripleBadSet i j k hij hik hjk := by
  classical
  let Aij : Arrangement 2 :=
    twoArrangement (p.toArrangement i) (p.toArrangement j)
  have hAijFinite : TranslationGenericity.PairFiniteArrangement Aij := by
    simpa [Aij] using pairFinite_twoArrangement_of_finite hfinite
  let γ : Point → Lower.ArrangementParameter n :=
    fun v => translateParameterAt p k v
  have hγcont : Continuous γ :=
    continuous_translateParameterAt p k
  have hpreOpen : IsOpen (γ ⁻¹' U) := hU.preimage hγcont
  have hzero : (0 : Point) ∈ γ ⁻¹' U := by
    change γ 0 ∈ U
    simpa [γ] using hpU
  obtain ⟨v, hvU, havoid⟩ :=
    TranslationGenericity.exists_mem_open_noTripleContactWithInserted_translate
      Aij (p.toArrangement k) hAijFinite hpreOpen hzero
  refine ⟨γ v, hvU, ?_⟩
  intro hbad
  rcases hbad with ⟨x, hx⟩
  rcases hx with ⟨hxij, hxk⟩
  rcases hxij with ⟨hxi, hxj⟩
  have hxiOld : x ∈ (p.toArrangement i).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      hik] using hxi
  have hxjOld : x ∈ (p.toArrangement j).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      hjk] using hxj
  have hxkNew :
      x ∈ (TranslationGenericity.translate (p.toArrangement k) v).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      Lower.LollipopParameter.toLollipop, TranslationGenericity.translate]
      using hxk
  have hdisj := havoid (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  exact Set.disjoint_left.mp hdisj
    (by simpa [Aij] using (show x ∈ (Aij (0 : Fin 2)).carrier ∩
        (TranslationGenericity.translate (p.toArrangement k) v).carrier from
        ⟨hxiOld, hxkNew⟩))
    (by simpa [Aij] using (show x ∈ (Aij (1 : Fin 2)).carrier ∩
        (TranslationGenericity.translate (p.toArrangement k) v).carrier from
        ⟨hxjOld, hxkNew⟩))

/-- Fixed-triple density is reduced to density of finite contact for the
first selected pair. -/
theorem dense_orderedTripleGood_of_pairFiniteGood_dense {n : ℕ}
    (t : OrderedTripleIndex n)
    (hdense : Dense (pairFiniteGood t.1.1 t.1.2.1)) :
    Dense (orderedTripleGood t) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases hdense.exists_mem_open hU hUne with ⟨p, hpfinite, hpU⟩
  rcases
    exists_mem_open_not_tripleBadSet_of_pairFinite_at
      t.2.1 t.2.2.1 t.2.2.2 hpfinite hU hpU with
    ⟨q, hqU, hqgood⟩
  exact ⟨q, hqU, by simpa [orderedTripleGood] using hqgood⟩

/-- Fixed-triple density is also reduced to density of the stronger elementary
pair-regular locus. -/
theorem dense_orderedTripleGood_of_pairRegularGood_dense {n : ℕ}
    (t : OrderedTripleIndex n)
    (hdense : Dense (pairRegularGood t.1.1 t.1.2.1)) :
    Dense (orderedTripleGood t) :=
  dense_orderedTripleGood_of_pairFiniteGood_dense t
    (hdense.mono (pairRegularGood_subset_pairFiniteGood t.1.1 t.1.2.1))

/-- Every fixed ordered-triple good locus is dense. -/
theorem dense_orderedTripleGood {n : ℕ}
    (t : OrderedTripleIndex n) :
    Dense (orderedTripleGood t) :=
  dense_orderedTripleGood_of_pairRegularGood_dense t
    (dense_pairRegularGood t.1.1 t.1.2.1 t.2.1)

/-- The complement of the triple bad union is exactly the finite intersection
of the fixed ordered-triple good loci. -/
theorem compl_tripleBadUnion_eq_iInter_orderedTripleGood {n : ℕ} :
    ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) =
      ⋂ t : OrderedTripleIndex n, orderedTripleGood t := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iInter]
    intro t
    change p ∉
      Lower.GenericityPort.tripleBadSet
        t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2.1 t.2.2.2
    intro hbad
    apply hp
    unfold Lower.GenericityPort.tripleBadUnion
    exact Set.mem_iUnion.mpr ⟨t.1.1,
      Set.mem_iUnion.mpr ⟨t.1.2.1,
        Set.mem_iUnion.mpr ⟨t.1.2.2,
          Set.mem_iUnion.mpr ⟨t.2.1,
            Set.mem_iUnion.mpr ⟨t.2.2.1,
              Set.mem_iUnion.mpr ⟨t.2.2.2, hbad⟩⟩⟩⟩⟩⟩
  · intro hp hbad
    unfold Lower.GenericityPort.tripleBadUnion at hbad
    rcases Set.mem_iUnion.mp hbad with ⟨i, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨j, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨k, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hij, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hik, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hjk, hbad⟩
    let t : OrderedTripleIndex n := ⟨(i, j, k), ⟨hij, hik, hjk⟩⟩
    have hgood : p ∈ orderedTripleGood t := Set.mem_iInter.mp hp t
    change p ∉ Lower.GenericityPort.tripleBadSet i j k hij hik hjk at hgood
    exact hgood hbad

/-- The parameter is outside the explicit triple-bad union iff its concrete
arrangement has no triple carrier points. -/
theorem not_mem_tripleBadUnion_iff_noTripleCarrierPoints {n : ℕ}
    (p : Lower.ArrangementParameter n) :
    p ∉ (Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n)) ↔
      TranslationGenericity.NoTripleCarrierPoints p.toArrangement := by
  constructor
  · intro hnot i j k hij hik hjk
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hnot
    unfold Lower.GenericityPort.tripleBadUnion
    exact Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨k,
          Set.mem_iUnion.mpr ⟨hij,
            Set.mem_iUnion.mpr ⟨hik,
              Set.mem_iUnion.mpr ⟨hjk,
                ⟨x, by
                  simpa only [Lower.ArrangementParameter.toArrangement,
                    Set.mem_inter_iff] using ⟨⟨hxi.1, hxj.1⟩, hxi.2⟩⟩⟩⟩⟩⟩⟩⟩
  · intro htriple hbad
    unfold Lower.GenericityPort.tripleBadUnion at hbad
    rcases Set.mem_iUnion.mp hbad with ⟨i, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨j, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨k, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hij, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hik, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hjk, hbad⟩
    rcases hbad with ⟨x, hx⟩
    have hx' :
        x ∈ (p.toArrangement i).carrier ∩ (p.toArrangement k).carrier :=
      ⟨hx.1.1, hx.2⟩
    have hx'' :
        x ∈ (p.toArrangement j).carrier ∩ (p.toArrangement k).carrier :=
      ⟨hx.1.2, hx.2⟩
    exact Set.disjoint_left.mp (htriple i j k hij hik hjk) hx' hx''

/-- Direct forward form of the triple-bad-union bridge. -/
theorem not_mem_tripleBadUnion_of_noTripleCarrierPoints {n : ℕ}
    {p : Lower.ArrangementParameter n}
    (htriple : TranslationGenericity.NoTripleCarrierPoints p.toArrangement) :
    p ∉ (Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n)) :=
  (not_mem_tripleBadUnion_iff_noTripleCarrierPoints p).2 htriple

/-- Finite-index reduction for the triple-contact density theorem.  It is
enough to prove that every fixed ordered-triple good locus is open dense. -/
theorem dense_compl_tripleBadUnion_of_orderedTriple_open_dense {n : ℕ}
    (hopen : ∀ t : OrderedTripleIndex n, IsOpen (orderedTripleGood t))
    (hdense : ∀ t : OrderedTripleIndex n, Dense (orderedTripleGood t)) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  classical
  have hfinite :
      Dense (⋂ t : OrderedTripleIndex n, orderedTripleGood t) :=
    Lower.GenericityPort.dense_iInter_fintype_of_open_dense
      (orderedTripleGood (n := n)) hopen hdense
  rwa [compl_tripleBadUnion_eq_iInter_orderedTripleGood]

/-- Once the fixed ordered-triple good loci are known to be open, their
density is already proved by `dense_orderedTripleGood`. -/
theorem dense_compl_tripleBadUnion_of_orderedTriple_open {n : ℕ}
    (hopen : ∀ t : OrderedTripleIndex n, IsOpen (orderedTripleGood t)) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) :=
  dense_compl_tripleBadUnion_of_orderedTriple_open_dense
    hopen dense_orderedTripleGood

/-- Remaining triple-contact avoidance theorem for the only nontrivial range
`3 ≤ n`. -/
theorem dense_compl_tripleBadUnion_ge_three (n : ℕ) (_hn : 3 ≤ n) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases dense_allPairCenterRegularGood.exists_mem_open hU hUne with
    ⟨p, hpPair, hpU⟩
  rcases
    exists_mem_open_allPairCenterRegularGood_noTriple
      hU hpU hpPair with
    ⟨q, hqU, _hqPair, hqTriple⟩
  exact ⟨q, hqU, not_mem_tripleBadUnion_of_noTripleCarrierPoints hqTriple⟩

/-- The complement of the triple-contact bad locus is dense in every finite
arrangement parameter space.

This is the remaining concrete finite-avoidance fact needed for the lower
genericization argument.  The nonparallel-stem complement is already proved
open dense in `Lower.GenericityPort.dense_compl_parallelBadUnion`. -/
theorem dense_compl_tripleBadUnion (n : ℕ) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  by_cases hn : n < 3
  · exact dense_compl_tripleBadUnion_of_lt_three hn
  · exact dense_compl_tripleBadUnion_ge_three n (by omega)

/-- The reduced chamber-bad locus is avoidable.

This combines the remaining triple-contact density target with the existing
open dense nonparallel-stem theorem. -/
theorem dense_compl_chamberBadUnion (n : ℕ) :
    Dense
      ((Lower.GenericityPort.chamberBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  have hparallelDense :
      Dense
        ((Lower.GenericityPort.parallelBadUnion :
          Set (Lower.ArrangementParameter n))ᶜ) :=
    Lower.GenericityPort.dense_compl_parallelBadUnion
  have hparallelOpen :
      IsOpen
        ((Lower.GenericityPort.parallelBadUnion :
          Set (Lower.ArrangementParameter n))ᶜ) :=
    Lower.GenericityPort.isOpen_compl_parallelBadUnion
  have htp :
      Dense
        (((Lower.GenericityPort.parallelBadUnion :
            Set (Lower.ArrangementParameter n))ᶜ) ∩
          ((Lower.GenericityPort.tripleBadUnion :
            Set (Lower.ArrangementParameter n))ᶜ)) :=
    hparallelDense.inter_of_isOpen_left
      (dense_compl_tripleBadUnion n) hparallelOpen
  simpa [Lower.GenericityPort.chamberBadUnion, Set.compl_union,
    Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using htp

/-- Every finite strict pair chamber contains a generic arrangement.

This is the all-`n` concrete finite-avoidance theorem needed by the lower
construction after topology supplies the generic Euler equality. -/
theorem chamberGenericityAvoidance_all :
    ∀ n : ℕ, Lower.GenericityPort.ChamberGenericityAvoidance n := by
  intro n
  exact { dense_good := dense_compl_chamberBadUnion n }

theorem chamberGenericityAvoidance (n : ℕ) :
    Lower.GenericityPort.ChamberGenericityAvoidance n :=
  chamberGenericityAvoidance_all n

end Genericity
end MainTheorem
end EndToEnd
end Concrete
end Lollipop

namespace Lollipop.Manuscript.Lemma_8_4

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

abbrev CoreStatement {n : Nat} (S : PairCodeSpec n) (A : Arrangement n) : Prop :=
  RealizesPairCodeSpec S A ->
    exists B : Arrangement n,
      IsGeneric B /\
      forall i j : Fin n, i < j ->
        pairCrossingCount (B i) (B j) = (S.code i j).crossings

end Lollipop.Manuscript.Lemma_8_4

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_8_4

open Concrete Concrete.EndToEnd Concrete.EndToEnd.Lower

theorem proof {n : Nat} (S : PairCodeSpec n) (A : Arrangement n) :
    CoreStatement S A := by
  intro hA
  exact exists_generic_with_pairCrossingCounts_of_chamber_avoidance
    (MainTheorem.Genericity.chamberGenericityAvoidance_all n) hA

end Lollipop.Manuscript.Lemma_8_4
