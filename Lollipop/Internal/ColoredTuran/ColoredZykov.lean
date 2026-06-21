import Lollipop.Internal.PairReduction
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
Local colored Zykov symmetrization primitives.

This module formalizes the local clone operation used in the manuscript's
colored Zykov reduction.  A colored complete graph stores the four pair colors
on ordered pairs, with symmetry and zero diagonal.  From it we recover the two
bad-pair graphs `D` and `E`.  Cloning a vertex along a color-zero pair is proved
to be exactly `SimpleGraph.replaceVertex` on both derived graphs, so the
forbidden-clique hypotheses are preserved by mathlib's existing
`CliqueFree.replaceVertex` theorem.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V : Type u} [DecidableEq V]

instance : Fintype PairColor where
  elems := {PairColor.zero, PairColor.A, PairColor.B, PairColor.X}
  complete := by
    intro c
    cases c <;> simp

/-- A symmetric four-coloring of all unordered pairs, represented as a function
on ordered pairs with a zero diagonal. -/
structure ColoredGraph (V : Type u) [DecidableEq V] where
  color : V → V → PairColor
  color_symm : ∀ v w : V, color v w = color w v
  color_self : ∀ v : V, color v v = PairColor.zero

namespace ColoredGraph

/-- A color contributes to the bad-pair graph `D` iff it is `B` or `X`. -/
def isDColor : PairColor → Bool
  | PairColor.B => true
  | PairColor.X => true
  | _ => false

/-- A color contributes to the bad-pair graph `E` iff it is `A` or `X`. -/
def isEColor : PairColor → Bool
  | PairColor.A => true
  | PairColor.X => true
  | _ => false

/-- A color contributes to the blocker graph `A` iff it is exactly `A`
(`E`-only in the manuscript's convention). -/
def isAColor : PairColor → Bool
  | PairColor.A => true
  | _ => false

/-- A color contributes to the blocker graph `B` iff it is exactly `B`
(`D`-only in the manuscript's convention). -/
def isBColor : PairColor → Bool
  | PairColor.B => true
  | _ => false

@[simp]
theorem isDColor_zero : isDColor PairColor.zero = false := by
  rfl

@[simp]
theorem isEColor_zero : isEColor PairColor.zero = false := by
  rfl

@[simp]
theorem isAColor_zero : isAColor PairColor.zero = false := by
  rfl

@[simp]
theorem isBColor_zero : isBColor PairColor.zero = false := by
  rfl

/-- The `D` graph: colors `B` and `X`. -/
def DGraph (C : ColoredGraph V) : SimpleGraph V where
  Adj v w := isDColor (C.color v w) = true
  symm := by
    intro v w h
    rw [← C.color_symm v w]
    exact h
  loopless := ⟨by
    intro v h
    rw [C.color_self v] at h
    simp at h⟩

/-- The `E` graph: colors `A` and `X`. -/
def EGraph (C : ColoredGraph V) : SimpleGraph V where
  Adj v w := isEColor (C.color v w) = true
  symm := by
    intro v w h
    rw [← C.color_symm v w]
    exact h
  loopless := ⟨by
    intro v h
    rw [C.color_self v] at h
    simp at h⟩

/-- The blocker graph `A`: exactly color `A`. -/
def AGraph (C : ColoredGraph V) : SimpleGraph V where
  Adj v w := isAColor (C.color v w) = true
  symm := by
    intro v w h
    rw [← C.color_symm v w]
    exact h
  loopless := ⟨by
    intro v h
    rw [C.color_self v] at h
    simp at h⟩

/-- The blocker graph `B`: exactly color `B`. -/
def BGraph (C : ColoredGraph V) : SimpleGraph V where
  Adj v w := isBColor (C.color v w) = true
  symm := by
    intro v w h
    rw [← C.color_symm v w]
    exact h
  loopless := ⟨by
    intro v h
    rw [C.color_self v] at h
    simp at h⟩

instance (C : ColoredGraph V) : DecidableRel C.DGraph.Adj := by
  intro v w
  unfold DGraph
  infer_instance

instance (C : ColoredGraph V) : DecidableRel C.EGraph.Adj := by
  intro v w
  unfold EGraph
  infer_instance

instance (C : ColoredGraph V) : DecidableRel C.AGraph.Adj := by
  intro v w
  unfold AGraph
  infer_instance

instance (C : ColoredGraph V) : DecidableRel C.BGraph.Adj := by
  intro v w
  unfold BGraph
  infer_instance

/-- Quotient form has no color-zero pair between distinct vertices. -/
def NoZeroOffDiag (C : ColoredGraph V) : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → C.color v w ≠ PairColor.zero

/-- In quotient form, an off-diagonal non-`A` pair is a `D`-edge. -/
theorem AGraph_compl_le_DGraph
    (C : ColoredGraph V) (hzero : C.NoZeroOffDiag) :
    C.AGraphᶜ ≤ C.DGraph := by
  intro v w h
  rw [SimpleGraph.compl_adj] at h
  rcases h with ⟨hne, hnA⟩
  unfold AGraph at hnA
  unfold DGraph
  have hnzero : C.color v w ≠ PairColor.zero := hzero hne
  cases hc : C.color v w <;> simp [isAColor, isDColor, hc] at hnA hnzero ⊢

/-- In quotient form, an off-diagonal non-`B` pair is an `E`-edge. -/
theorem BGraph_compl_le_EGraph
    (C : ColoredGraph V) (hzero : C.NoZeroOffDiag) :
    C.BGraphᶜ ≤ C.EGraph := by
  intro v w h
  rw [SimpleGraph.compl_adj] at h
  rcases h with ⟨hne, hnB⟩
  unfold BGraph at hnB
  unfold EGraph
  have hnzero : C.color v w ≠ PairColor.zero := hzero hne
  cases hc : C.color v w <;> simp [isBColor, isEColor, hc] at hnB hnzero ⊢

/-- The manuscript's blocker condition `α(A) ≤ 3`: in quotient form, if `D`
is `K_4`-free then the complement of `A` is `K_4`-free. -/
theorem AGraph_compl_cliqueFree_four_of_DGraph
    (C : ColoredGraph V) (hzero : C.NoZeroOffDiag)
    (hD : C.DGraph.CliqueFree 4) :
    C.AGraphᶜ.CliqueFree 4 :=
  hD.anti (AGraph_compl_le_DGraph C hzero)

/-- The manuscript's blocker condition `α(B) ≤ 4`: in quotient form, if `E`
is `K_5`-free then the complement of `B` is `K_5`-free. -/
theorem BGraph_compl_cliqueFree_five_of_EGraph
    (C : ColoredGraph V) (hzero : C.NoZeroOffDiag)
    (hE : C.EGraph.CliqueFree 5) :
    C.BGraphᶜ.CliqueFree 5 :=
  hE.anti (BGraph_compl_le_EGraph C hzero)

/-- The raw color update that clones the adjacency/color pattern of `s` onto
`t`, keeping the diagonal zero. -/
def cloneColor (C : ColoredGraph V) (s t v w : V) : PairColor :=
  if v = t then
    if w = t then PairColor.zero else C.color s w
  else
    if w = t then C.color v s else C.color v w

/-- Clone `t` to `s` in the colored graph. -/
def clone (C : ColoredGraph V) (s t : V) : ColoredGraph V where
  color := cloneColor C s t
  color_symm := by
    intro v w
    by_cases hv : v = t
    · by_cases hw : w = t
      · simp [cloneColor, hv, hw]
      · simp [cloneColor, hv, hw, C.color_symm]
    · by_cases hw : w = t
      · simp [cloneColor, hv, hw, C.color_symm]
      · simp [cloneColor, hv, hw, C.color_symm]
  color_self := by
    intro v
    by_cases hv : v = t
    · simp [cloneColor, hv]
    · simp [cloneColor, hv, C.color_self]

@[simp]
theorem clone_color_target_target (C : ColoredGraph V) (s t : V) :
    (C.clone s t).color t t = PairColor.zero := by
  simp [clone, cloneColor]

@[simp]
theorem clone_color_target_of_ne
    (C : ColoredGraph V) {s t w : V} (hw : w ≠ t) :
    (C.clone s t).color t w = C.color s w := by
  simp [clone, cloneColor, hw]

@[simp]
theorem clone_color_to_target_of_ne
    (C : ColoredGraph V) {s t v : V} (hv : v ≠ t) :
    (C.clone s t).color v t = C.color v s := by
  simp [clone, cloneColor, hv]

@[simp]
theorem clone_color_of_ne
    (C : ColoredGraph V) {s t v w : V} (hv : v ≠ t) (hw : w ≠ t) :
    (C.clone s t).color v w = C.color v w := by
  simp [clone, cloneColor, hv, hw]

/-- Two vertices are twins if their full color rows agree. -/
def SameRow (C : ColoredGraph V) (v w : V) : Prop :=
  ∀ z : V, C.color v z = C.color w z

theorem sameRow_refl (C : ColoredGraph V) (v : V) :
    C.SameRow v v := by
  intro z
  rfl

theorem sameRow_symm
    (C : ColoredGraph V) {v w : V} (h : C.SameRow v w) :
    C.SameRow w v := by
  intro z
  exact (h z).symm

theorem sameRow_trans
    (C : ColoredGraph V) {u v w : V}
    (huv : C.SameRow u v) (hvw : C.SameRow v w) :
    C.SameRow u w := by
  intro z
  exact (huv z).trans (hvw z)

/-- Twin vertices have color zero between them. -/
theorem color_zero_of_sameRow
    (C : ColoredGraph V) {v w : V} (h : C.SameRow v w) :
    C.color v w = PairColor.zero := by
  have hwv : C.color w v = PairColor.zero := by
    simpa [C.color_self v] using (h v).symm
  rw [C.color_symm v w, hwv]

/-- Cloning along a zero pair makes the source and target twins. -/
theorem clone_sameRow_source_target_of_zero
    (C : ColoredGraph V) {s t : V}
    (hst : C.color s t = PairColor.zero) :
    (C.clone s t).SameRow s t := by
  intro z
  by_cases hzt : z = t
  · subst z
    have hts : C.color t s = PairColor.zero := by
      rw [← C.color_symm s t, hst]
    simp [clone, cloneColor, hst, hts, C.color_self]
  · by_cases hstEq : s = t
    · subst t
      rfl
    · simp [clone, cloneColor, hzt, hstEq]

/-- Cloning preserves any old twin relation between two vertices that are not
the clone target. -/
theorem clone_sameRow_of_ne_target
    (C : ColoredGraph V) {s t u v : V}
    (hu : u ≠ t) (hv : v ≠ t)
    (huv : C.SameRow u v) :
    (C.clone s t).SameRow u v := by
  intro z
  by_cases hzt : z = t
  · subst z
    simp [clone, cloneColor, hu, hv, huv s]
  · simp [clone, cloneColor, hu, hv, hzt, huv z]

/-- After cloning `t` to `s`, the target becomes a twin of every old twin of
`s` outside the target. -/
theorem clone_sameRow_target_of_source_twin
    (C : ColoredGraph V) {s t u : V}
    (hst : C.color s t = PairColor.zero)
    (hs : s ≠ t)
    (hu : u ≠ t)
    (hsu : C.SameRow s u) :
    (C.clone s t).SameRow t u := by
  have hst' := clone_sameRow_source_target_of_zero C hst
  have hsu' := clone_sameRow_of_ne_target C
    (s := s) (t := t) (u := s) (v := u)
    hs
    hu hsu
  exact sameRow_trans (C.clone s t) (sameRow_symm (C.clone s t) hst') hsu'

/-- Cloning in the colored graph induces `replaceVertex` on the derived `D`
graph. -/
theorem DGraph_clone_eq_replaceVertex
    (C : ColoredGraph V) (s t : V) :
    (C.clone s t).DGraph = C.DGraph.replaceVertex s t := by
  ext v w
  by_cases hv : v = t
  · subst v
    by_cases hw : w = t
    · subst w
      simp [DGraph, clone, cloneColor, SimpleGraph.replaceVertex]
    · by_cases hws : w = s
      · subst w
        simp [DGraph, clone, cloneColor, SimpleGraph.replaceVertex, hw, C.color_self]
      · simp [DGraph, clone, cloneColor, SimpleGraph.replaceVertex, hw, hws]
  · by_cases hw : w = t
    · subst w
      by_cases hvs : v = s
      · subst v
        simp [DGraph, clone, cloneColor, SimpleGraph.replaceVertex, hv, C.color_self]
      · simp [DGraph, clone, cloneColor, SimpleGraph.replaceVertex, hv, hvs]
    · simp [DGraph, clone, cloneColor, SimpleGraph.replaceVertex, hv, hw]

/-- Cloning in the colored graph induces `replaceVertex` on the derived `E`
graph. -/
theorem EGraph_clone_eq_replaceVertex
    (C : ColoredGraph V) (s t : V) :
    (C.clone s t).EGraph = C.EGraph.replaceVertex s t := by
  ext v w
  by_cases hv : v = t
  · subst v
    by_cases hw : w = t
    · subst w
      simp [EGraph, clone, cloneColor, SimpleGraph.replaceVertex]
    · by_cases hws : w = s
      · subst w
        simp [EGraph, clone, cloneColor, SimpleGraph.replaceVertex, hw, C.color_self]
      · simp [EGraph, clone, cloneColor, SimpleGraph.replaceVertex, hw, hws]
  · by_cases hw : w = t
    · subst w
      by_cases hvs : v = s
      · subst v
        simp [EGraph, clone, cloneColor, SimpleGraph.replaceVertex, hv, C.color_self]
      · simp [EGraph, clone, cloneColor, SimpleGraph.replaceVertex, hv, hvs]
    · simp [EGraph, clone, cloneColor, SimpleGraph.replaceVertex, hv, hw]

/-- The colored clone operation preserves `K_m`-freeness of the derived `D`
graph. -/
theorem DGraph_clone_cliqueFree
    (C : ColoredGraph V) (s t : V) {m : Nat}
    (h : C.DGraph.CliqueFree m) :
    (C.clone s t).DGraph.CliqueFree m := by
  rw [DGraph_clone_eq_replaceVertex]
  exact h.replaceVertex s t

/-- The colored clone operation preserves `K_m`-freeness of the derived `E`
graph. -/
theorem EGraph_clone_cliqueFree
    (C : ColoredGraph V) (s t : V) {m : Nat}
    (h : C.EGraph.CliqueFree m) :
    (C.clone s t).EGraph.CliqueFree m := by
  rw [EGraph_clone_eq_replaceVertex]
  exact h.replaceVertex s t

section Weight

variable [Fintype V]

/-- Weighted colored degree of a vertex, with the manuscript's color weights
`0,1,1,3`. -/
def colorDegree (C : ColoredGraph V) (v : V) : Rat :=
  ∑ w : V, (C.color v w).weight

/-- Ordered total color weight.  This is twice the usual unordered `sigma`
because every unordered pair is counted in both orders; diagonal terms are zero. -/
def orderedColorWeight (C : ColoredGraph V) : Rat :=
  ∑ v : V, C.colorDegree v

/-- Raw weighted degree for a color function before packaging it as a
`ColoredGraph`.  This is used only for the finite extremal-existence argument,
where it is more convenient to maximize over raw functions and then recover the
proof fields. -/
def rawColorDegree (c : V → V → PairColor) (v : V) : Rat :=
  ∑ w : V, (c v w).weight

/-- Raw ordered total color weight for a color function. -/
def rawOrderedColorWeight (c : V → V → PairColor) : Rat :=
  ∑ v : V, rawColorDegree c v

@[simp]
theorem rawColorDegree_color (C : ColoredGraph V) (v : V) :
    rawColorDegree C.color v = C.colorDegree v := by
  rfl

@[simp]
theorem rawOrderedColorWeight_color (C : ColoredGraph V) :
    rawOrderedColorWeight C.color = C.orderedColorWeight := by
  rfl

/-- A colored graph is objective-extremal for the two forbidden-clique
hypotheses if it satisfies them and has maximum ordered color weight among all
colored graphs satisfying them on the same vertex type. -/
def IsColoredObjectiveExtremal (C : ColoredGraph V) : Prop :=
  C.DGraph.CliqueFree 4 ∧ C.EGraph.CliqueFree 5 ∧
    ∀ ⦃H : ColoredGraph V⦄,
      H.DGraph.CliqueFree 4 → H.EGraph.CliqueFree 5 →
        H.orderedColorWeight ≤ C.orderedColorWeight

namespace IsColoredObjectiveExtremal

theorem D_cliqueFree
    {C : ColoredGraph V} (h : C.IsColoredObjectiveExtremal) :
    C.DGraph.CliqueFree 4 :=
  h.1

theorem E_cliqueFree
    {C : ColoredGraph V} (h : C.IsColoredObjectiveExtremal) :
    C.EGraph.CliqueFree 5 :=
  h.2.1

theorem orderedWeight_le
    {C H : ColoredGraph V} (h : C.IsColoredObjectiveExtremal)
    (hD : H.DGraph.CliqueFree 4) (hE : H.EGraph.CliqueFree 5) :
    H.orderedColorWeight ≤ C.orderedColorWeight :=
  h.2.2 hD hE

end IsColoredObjectiveExtremal

/-- The twin class of a vertex, as a finite set. -/
noncomputable def sameRowClass (C : ColoredGraph V) (v : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter (fun w : V => C.SameRow v w)

/-- Size of the twin class of a vertex. -/
noncomputable def sameRowClassSize (C : ColoredGraph V) (v : V) : Nat :=
  (C.sameRowClass v).card

/-- The ordered twin-pair count.  This is the finite version of the
manuscript's "sum of squares of clone-class sizes" tie-breaker: each twin class
of size `m` contributes `m^2` ordered pairs. -/
noncomputable def sameRowPairPotential (C : ColoredGraph V) : Nat :=
  ∑ v : V, C.sameRowClassSize v

/-- Raw row equality before packaging a color function as a `ColoredGraph`. -/
def rawSameRow (c : V → V → PairColor) (v w : V) : Prop :=
  ∀ z : V, c v z = c w z

/-- Raw twin class of a vertex for an unpackaged color function. -/
noncomputable def rawSameRowClass (c : V → V → PairColor) (v : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter (fun w : V => rawSameRow c v w)

/-- Raw twin-class size for an unpackaged color function. -/
noncomputable def rawSameRowClassSize (c : V → V → PairColor) (v : V) : Nat :=
  (rawSameRowClass c v).card

/-- Raw ordered twin-pair potential for an unpackaged color function. -/
noncomputable def rawSameRowPairPotential (c : V → V → PairColor) : Nat :=
  ∑ v : V, rawSameRowClassSize c v

@[simp]
theorem rawSameRow_color (C : ColoredGraph V) (v w : V) :
    rawSameRow C.color v w = C.SameRow v w := by
  rfl

theorem rawSameRowClass_color (C : ColoredGraph V) (v : V) :
    rawSameRowClass C.color v = C.sameRowClass v := by
  classical
  ext w
  simp [rawSameRowClass, sameRowClass, rawSameRow, SameRow]

@[simp]
theorem rawSameRowClassSize_color (C : ColoredGraph V) (v : V) :
    rawSameRowClassSize C.color v = C.sameRowClassSize v := by
  unfold rawSameRowClassSize sameRowClassSize
  rw [rawSameRowClass_color]

@[simp]
theorem rawSameRowPairPotential_color (C : ColoredGraph V) :
    rawSameRowPairPotential C.color = C.sameRowPairPotential := by
  unfold rawSameRowPairPotential sameRowPairPotential
  simp

@[simp]
theorem mem_sameRowClass
    (C : ColoredGraph V) (v w : V) :
    w ∈ C.sameRowClass v ↔ C.SameRow v w := by
  simp [sameRowClass]

theorem self_mem_sameRowClass
    (C : ColoredGraph V) (v : V) :
    v ∈ C.sameRowClass v := by
  rw [mem_sameRowClass]
  exact sameRow_refl C v

theorem sameRowClass_nonempty
    (C : ColoredGraph V) (v : V) :
    (C.sameRowClass v).Nonempty :=
  ⟨v, C.self_mem_sameRowClass v⟩

theorem sameRowClassSize_pos
    (C : ColoredGraph V) (v : V) :
    0 < C.sameRowClassSize v := by
  unfold sameRowClassSize
  exact (C.sameRowClass_nonempty v).card_pos

theorem sameRowClass_eq_of_sameRow
    (C : ColoredGraph V) {v w : V} (hvw : C.SameRow v w) :
    C.sameRowClass v = C.sameRowClass w := by
  ext z
  constructor
  · intro hz
    rw [mem_sameRowClass] at hz ⊢
    exact sameRow_trans C (sameRow_symm C hvw) hz
  · intro hz
    rw [mem_sameRowClass] at hz ⊢
    exact sameRow_trans C hvw hz

theorem sameRowClassSize_eq_of_sameRow
    (C : ColoredGraph V) {v w : V} (hvw : C.SameRow v w) :
    C.sameRowClassSize v = C.sameRowClassSize w := by
  unfold sameRowClassSize
  rw [sameRowClass_eq_of_sameRow C hvw]

theorem not_mem_sameRowClass
    (C : ColoredGraph V) {v w : V} (hvw : ¬ C.SameRow v w) :
    w ∉ C.sameRowClass v := by
  rw [mem_sameRowClass]
  exact hvw

/-- If `v` is not the clone target, then every old twin of `v`, except
possibly the target itself, remains a twin of `v` after cloning. -/
theorem sameRowClass_erase_target_subset_clone
    (C : ColoredGraph V) {s t v : V} (hvt : v ≠ t) :
    (C.sameRowClass v).erase t ⊆ (C.clone s t).sameRowClass v := by
  intro w hw
  rw [Finset.mem_erase, mem_sameRowClass] at hw
  rw [mem_sameRowClass]
  exact clone_sameRow_of_ne_target C hvt hw.1 hw.2

/-- If `v` is an old twin of the clone source and `v` is not the clone target,
then the clone target becomes a twin of `v`. -/
theorem target_mem_clone_sameRowClass_of_source_twin
    (C : ColoredGraph V) {s t v : V}
    (hst : C.color s t = PairColor.zero)
    (hs : s ≠ t)
    (hvt : v ≠ t)
    (hsv : C.SameRow s v) :
    t ∈ (C.clone s t).sameRowClass v := by
  rw [mem_sameRowClass]
  exact sameRow_symm (C.clone s t)
    (clone_sameRow_target_of_source_twin C hst hs hvt hsv)

/-- A source-class vertex gains the clone target as a twin.  This is the local
cardinality gain used by the clone-class square-sum tie-breaker. -/
theorem sameRowClassSize_clone_source_twin_ge_succ_erase
    (C : ColoredGraph V) {s t v : V}
    (hst : C.color s t = PairColor.zero)
    (hs : s ≠ t)
    (hvt : v ≠ t)
    (hsv : C.SameRow s v) :
    ((C.sameRowClass v).erase t).card + 1 ≤
      (C.clone s t).sameRowClassSize v := by
  classical
  unfold sameRowClassSize
  have hsubset := sameRowClass_erase_target_subset_clone C (s := s) (t := t) hvt
  have htmem : t ∈ (C.clone s t).sameRowClass v :=
    target_mem_clone_sameRowClass_of_source_twin C hst hs hvt hsv
  have ht_not_old : t ∉ (C.sameRowClass v).erase t := by
    simp
  have hinsert_subset :
      insert t ((C.sameRowClass v).erase t) ⊆
        (C.clone s t).sameRowClass v := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl | hw
    · exact htmem
    · exact hsubset hw
  have hcard :=
    Finset.card_le_card hinsert_subset
  rw [Finset.card_insert_of_notMem ht_not_old] at hcard
  exact hcard

/-- If the clone target was not already a twin of the source, then every
source-class row gains at least one twin after cloning: the target. -/
theorem sameRowClassSize_clone_source_twin_ge_succ
    (C : ColoredGraph V) {s t v : V}
    (hst : C.color s t = PairColor.zero)
    (hs : s ≠ t)
    (hnst : ¬ C.SameRow s t)
    (hvt : v ≠ t)
    (hsv : C.SameRow s v) :
    C.sameRowClassSize v + 1 ≤
      (C.clone s t).sameRowClassSize v := by
  have ht_not : t ∉ C.sameRowClass v := by
    rw [mem_sameRowClass]
    intro hvtwin
    exact hnst (sameRow_trans C hsv hvtwin)
  have hgain :=
    sameRowClassSize_clone_source_twin_ge_succ_erase
      C hst hs hvt hsv
  unfold sameRowClassSize at hgain ⊢
  rw [Finset.erase_eq_of_notMem ht_not] at hgain
  exact hgain

/-- Any non-target vertex loses at most the target from its twin class after a
clone. -/
theorem sameRowClassSize_erase_le_clone
    (C : ColoredGraph V) {s t v : V} (hvt : v ≠ t) :
    ((C.sameRowClass v).erase t).card ≤
      (C.clone s t).sameRowClassSize v := by
  unfold sameRowClassSize
  exact Finset.card_le_card
    (sameRowClass_erase_target_subset_clone C (s := s) (t := t) hvt)

/-- Any non-target row loses at most one twin after a clone. -/
theorem sameRowClassSize_le_clone_add_one
    (C : ColoredGraph V) {s t v : V} (hvt : v ≠ t) :
    C.sameRowClassSize v ≤
      (C.clone s t).sameRowClassSize v + 1 := by
  classical
  have hle :=
    sameRowClassSize_erase_le_clone C (s := s) (t := t) hvt
  by_cases htmem : t ∈ C.sameRowClass v
  · unfold sameRowClassSize at hle ⊢
    rw [Finset.card_erase_of_mem htmem] at hle
    omega
  · unfold sameRowClassSize at hle ⊢
    rw [Finset.erase_eq_of_notMem htmem] at hle
    omega

/-- A non-target row whose old twin class did not contain the clone target
does not lose any twins after cloning. -/
theorem sameRowClassSize_le_clone_of_not_target_twin
    (C : ColoredGraph V) {s t v : V}
    (hvt : v ≠ t) (hnt : ¬ C.SameRow v t) :
    C.sameRowClassSize v ≤
      (C.clone s t).sameRowClassSize v := by
  classical
  have ht_not : t ∉ C.sameRowClass v := by
    rw [mem_sameRowClass]
    exact hnt
  have hle :=
    sameRowClassSize_erase_le_clone C (s := s) (t := t) hvt
  unfold sameRowClassSize at hle ⊢
  rw [Finset.erase_eq_of_notMem ht_not] at hle
  exact hle

/-- The clone target's new twin class contains the old source twin class plus
the target itself, provided source and target were not already twins. -/
theorem sameRowClassSize_clone_target_ge_source_succ
    (C : ColoredGraph V) {s t : V}
    (hst : C.color s t = PairColor.zero)
    (hs : s ≠ t)
    (hnst : ¬ C.SameRow s t) :
    C.sameRowClassSize s + 1 ≤
      (C.clone s t).sameRowClassSize t := by
  classical
  have ht_not : t ∉ C.sameRowClass s := by
    rw [mem_sameRowClass]
    exact hnst
  unfold sameRowClassSize
  have hsubset :
      insert t (C.sameRowClass s) ⊆
        (C.clone s t).sameRowClass t := by
    intro w hw
    rw [Finset.mem_insert] at hw
    rw [mem_sameRowClass]
    rcases hw with hwt_eq | hw
    · subst w
      exact sameRow_refl (C.clone s t) t
    · rw [mem_sameRowClass] at hw
      have hwt : w ≠ t := by
        intro hwt
        subst w
        exact hnst hw
      exact clone_sameRow_target_of_source_twin C hst hs hwt hw
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_insert_of_notMem ht_not] at hcard
  exact hcard

/-- If `t` is not in the twin class of `a`, then deleting `t` from the
universe does not change the boolean count of `a`'s twin class. -/
theorem sum_sameRow_indicator_erase_eq_classSize_of_not_same
    (C : ColoredGraph V) [DecidableRel C.SameRow] {a t : V}
    (hat : ¬ C.SameRow a t) :
    (∑ v ∈ (Finset.univ : Finset V).erase t,
        if C.SameRow a v then 1 else 0) =
      C.sameRowClassSize a := by
  classical
  unfold sameRowClassSize sameRowClass
  rw [Finset.sum_boole]
  apply congrArg Finset.card
  ext v
  by_cases hvt : v = t
  · subst v
    simp [hat]
  · simp [hvt]

/-- Deleting `t` from the universe removes exactly the reflexive twin-pair
contribution from `t`'s twin class. -/
theorem sum_sameRow_indicator_erase_add_one_eq_classSize
    (C : ColoredGraph V) [DecidableRel C.SameRow] (t : V) :
    (∑ v ∈ (Finset.univ : Finset V).erase t,
        if C.SameRow t v then 1 else 0) + 1 =
      C.sameRowClassSize t := by
  classical
  have hsumAll :
      (∑ v : V, if C.SameRow t v then 1 else 0) =
        C.sameRowClassSize t := by
    unfold sameRowClassSize sameRowClass
    rw [Finset.sum_boole]
    norm_num
    congr 1
    ext v
    simp
  have hsplit :=
    Finset.add_sum_erase (Finset.univ : Finset V)
      (fun v : V => if C.SameRow t v then (1 : Nat) else 0)
      (Finset.mem_univ t)
  have hself : (if C.SameRow t t then (1 : Nat) else 0) = 1 := by
    simp [sameRow_refl]
  rw [hself, hsumAll] at hsplit
  omega

/-- A colored graph after the full finite Zykov tie-breaker: it maximizes the
colored objective, and among objective maximizers it maximizes the ordered
twin-pair potential. -/
def IsColoredZykovExtremal (C : ColoredGraph V) : Prop :=
  C.IsColoredObjectiveExtremal ∧
    ∀ ⦃H : ColoredGraph V⦄,
      H.IsColoredObjectiveExtremal →
        H.sameRowPairPotential ≤ C.sameRowPairPotential

namespace IsColoredZykovExtremal

theorem objective
    {C : ColoredGraph V} (h : C.IsColoredZykovExtremal) :
    C.IsColoredObjectiveExtremal :=
  h.1

theorem D_cliqueFree
    {C : ColoredGraph V} (h : C.IsColoredZykovExtremal) :
    C.DGraph.CliqueFree 4 :=
  h.objective.D_cliqueFree

theorem E_cliqueFree
    {C : ColoredGraph V} (h : C.IsColoredZykovExtremal) :
    C.EGraph.CliqueFree 5 :=
  h.objective.E_cliqueFree

theorem orderedWeight_le
    {C H : ColoredGraph V} (h : C.IsColoredZykovExtremal)
    (hD : H.DGraph.CliqueFree 4) (hE : H.EGraph.CliqueFree 5) :
    H.orderedColorWeight ≤ C.orderedColorWeight :=
  h.objective.orderedWeight_le hD hE

theorem pairPotential_le
    {C H : ColoredGraph V} (h : C.IsColoredZykovExtremal)
    (hH : H.IsColoredObjectiveExtremal) :
    H.sameRowPairPotential ≤ C.sameRowPairPotential :=
  h.2 hH

end IsColoredZykovExtremal

/-- Objective-extremal colored graphs exist whenever the two forbidden-clique
hypotheses are satisfiable.  The proof maximizes over the finite type of raw
color functions and then repackages the maximizing function as a `ColoredGraph`.
-/
theorem exists_isColoredObjectiveExtremal_of_exists
    (hex :
      ∃ C : ColoredGraph V,
        C.DGraph.CliqueFree 4 ∧ C.EGraph.CliqueFree 5) :
    ∃ C : ColoredGraph V, C.IsColoredObjectiveExtremal := by
  classical
  let admissible : (V → V → PairColor) → Prop := fun c =>
    ∃ C : ColoredGraph V,
      C.color = c ∧ C.DGraph.CliqueFree 4 ∧ C.EGraph.CliqueFree 5
  let candidates : Finset (V → V → PairColor) :=
    (Finset.univ : Finset (V → V → PairColor)).filter admissible
  obtain ⟨C₀, hD₀, hE₀⟩ := hex
  have hnonempty : candidates.Nonempty := by
    refine ⟨C₀.color, ?_⟩
    simp [candidates, admissible]
    exact ⟨C₀, rfl, hD₀, hE₀⟩
  obtain ⟨cmax, hcmax_mem, hcmax_max⟩ :=
    Finset.exists_max_image candidates rawOrderedColorWeight hnonempty
  have hcmax_adm : admissible cmax := by
    exact (Finset.mem_filter.mp hcmax_mem).2
  rcases hcmax_adm with ⟨Cmax, hCmax_color, hDmax, hEmax⟩
  refine ⟨Cmax, hDmax, hEmax, ?_⟩
  intro H hDH hEH
  have hH_mem : H.color ∈ candidates := by
    simp [candidates, admissible]
    exact ⟨H, rfl, hDH, hEH⟩
  have hle := hcmax_max H.color hH_mem
  rw [← hCmax_color] at hle
  simpa using hle

/-- Full finite Zykov-extremal colored graphs exist whenever the two
forbidden-clique hypotheses are satisfiable: first maximize the colored
objective, then maximize the ordered twin-pair potential among objective
maximizers. -/
theorem exists_isColoredZykovExtremal_of_exists
    (hex :
      ∃ C : ColoredGraph V,
        C.DGraph.CliqueFree 4 ∧ C.EGraph.CliqueFree 5) :
    ∃ C : ColoredGraph V, C.IsColoredZykovExtremal := by
  classical
  obtain ⟨C₀, hC₀⟩ := exists_isColoredObjectiveExtremal_of_exists hex
  let admissible : (V → V → PairColor) → Prop := fun c =>
    ∃ C : ColoredGraph V,
      C.color = c ∧ C.IsColoredObjectiveExtremal
  let candidates : Finset (V → V → PairColor) :=
    (Finset.univ : Finset (V → V → PairColor)).filter admissible
  have hnonempty : candidates.Nonempty := by
    refine ⟨C₀.color, ?_⟩
    simp [candidates, admissible]
    exact ⟨C₀, rfl, hC₀⟩
  obtain ⟨cmax, hcmax_mem, hcmax_max⟩ :=
    Finset.exists_max_image candidates rawSameRowPairPotential hnonempty
  have hcmax_adm : admissible cmax := by
    exact (Finset.mem_filter.mp hcmax_mem).2
  rcases hcmax_adm with ⟨Cmax, hCmax_color, hObjMax⟩
  refine ⟨Cmax, hObjMax, ?_⟩
  intro H hH
  have hH_mem : H.color ∈ candidates := by
    simp [candidates, admissible]
    exact ⟨H, rfl, hH⟩
  have hle := hcmax_max H.color hH_mem
  rw [← hCmax_color] at hle
  simpa using hle

/-- If `s` and `t` have color zero, then after cloning `t` to `s`, the new
degree of `t` equals the old degree of `s`. -/
theorem colorDegree_clone_target_of_zero
    (C : ColoredGraph V) {s t : V} (hst : C.color s t = PairColor.zero) :
    (C.clone s t).colorDegree t = C.colorDegree s := by
  unfold colorDegree
  apply Finset.sum_congr rfl
  intro w _hw
  by_cases hwt : w = t
  · subst w
    simp [clone, cloneColor, hst, PairColor.weight]
  · simp [clone, cloneColor, hwt]

/-- For a row not being cloned, only the entry at the target vertex changes. -/
theorem colorDegree_clone_ne_target
    (C : ColoredGraph V) {s t v : V} (hvt : v ≠ t) :
    (C.clone s t).colorDegree v =
      C.colorDegree v - (C.color v t).weight + (C.color v s).weight := by
  unfold colorDegree
  rw [← Finset.add_sum_erase Finset.univ
    (fun w : V => ((C.clone s t).color v w).weight)
    (Finset.mem_univ t)]
  rw [← Finset.add_sum_erase Finset.univ
    (fun w : V => (C.color v w).weight)
    (Finset.mem_univ t)]
  have herase :
      (∑ x ∈ Finset.univ.erase t, ((C.clone s t).color v x).weight) =
        ∑ x ∈ Finset.univ.erase t, (C.color v x).weight := by
    apply Finset.sum_congr rfl
    intro w hw
    have hwt : w ≠ t := (Finset.mem_erase.mp hw).1
    simp [clone, cloneColor, hvt, hwt]
  rw [herase]
  simp [clone, cloneColor, hvt]
  ring

/-- Removing the zero diagonal from the sum of weights entering `t` leaves the
weighted degree of `t`. -/
theorem sum_color_to_vertex_erase
    (C : ColoredGraph V) (t : V) :
    (∑ v ∈ Finset.univ.erase t, (C.color v t).weight) =
      C.colorDegree t := by
  unfold colorDegree
  have hzero : (C.color t t).weight = 0 := by
    simp [C.color_self t, PairColor.weight]
  rw [Finset.sum_erase
    (s := Finset.univ)
    (a := t)
    (f := fun v : V => (C.color v t).weight)
    hzero]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [C.color_symm v t]

/-- If `s` and `t` have color zero, removing `t` from the sum of weights
entering `s` still leaves the weighted degree of `s`. -/
theorem sum_color_to_source_erase_of_zero
    (C : ColoredGraph V) {s t : V} (hst : C.color s t = PairColor.zero) :
    (∑ v ∈ Finset.univ.erase t, (C.color v s).weight) =
      C.colorDegree s := by
  unfold colorDegree
  have hts : C.color t s = PairColor.zero := by
    rw [← C.color_symm s t, hst]
  have hzero : (C.color t s).weight = 0 := by
    simp [hts, PairColor.weight]
  rw [Finset.sum_erase
    (s := Finset.univ)
    (a := t)
    (f := fun v : V => (C.color v s).weight)
    hzero]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [C.color_symm v s]

/-- Split the ordered color weight into the row at `t` and all other rows. -/
theorem orderedColorWeight_split_vertex
    (C : ColoredGraph V) (t : V) :
    C.orderedColorWeight =
      C.colorDegree t + ∑ v ∈ Finset.univ.erase t, C.colorDegree v := by
  unfold orderedColorWeight
  rw [← Finset.add_sum_erase Finset.univ
    (fun v : V => C.colorDegree v)
    (Finset.mem_univ t)]

/-- Exact objective change for a colored Zykov clone along a color-zero pair.
The factor `2` appears because `orderedColorWeight` counts each unordered pair
twice. -/
theorem orderedColorWeight_clone_of_zero
    (C : ColoredGraph V) {s t : V} (hst : C.color s t = PairColor.zero) :
    (C.clone s t).orderedColorWeight =
      C.orderedColorWeight + 2 * (C.colorDegree s - C.colorDegree t) := by
  have hcloneSplit := orderedColorWeight_split_vertex (C.clone s t) t
  have hsplit := orderedColorWeight_split_vertex C t
  have htarget := colorDegree_clone_target_of_zero C hst
  have hrows :
      (∑ v ∈ Finset.univ.erase t, (C.clone s t).colorDegree v) =
        (∑ v ∈ Finset.univ.erase t, C.colorDegree v) -
          (∑ v ∈ Finset.univ.erase t, (C.color v t).weight) +
          (∑ v ∈ Finset.univ.erase t, (C.color v s).weight) := by
    calc
      (∑ v ∈ Finset.univ.erase t, (C.clone s t).colorDegree v)
          = ∑ v ∈ Finset.univ.erase t,
              (C.colorDegree v - (C.color v t).weight + (C.color v s).weight) := by
            apply Finset.sum_congr rfl
            intro v hv
            have hvt : v ≠ t := (Finset.mem_erase.mp hv).1
            exact colorDegree_clone_ne_target C hvt
      _ = (∑ v ∈ Finset.univ.erase t, C.colorDegree v) -
            (∑ v ∈ Finset.univ.erase t, (C.color v t).weight) +
            (∑ v ∈ Finset.univ.erase t, (C.color v s).weight) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hloss := sum_color_to_vertex_erase C t
  have hgain := sum_color_to_source_erase_of_zero C hst
  rw [hcloneSplit, hsplit, htarget, hrows, hloss, hgain]
  ring

/-- Objective-extremality forces equal weighted color degrees across every
color-zero pair.  This is the global version of the local clone calculation:
cloning either endpoint preserves the forbidden-clique hypotheses, so the exact
clone objective formula forces both degree inequalities. -/
theorem colorDegree_eq_of_zero_of_objective_extremal
    (C : ColoredGraph V) (hC : C.IsColoredObjectiveExtremal)
    {s t : V} (hst : C.color s t = PairColor.zero) :
    C.colorDegree s = C.colorDegree t := by
  have hclone_st :=
    hC.orderedWeight_le
      (DGraph_clone_cliqueFree C s t hC.D_cliqueFree)
      (EGraph_clone_cliqueFree C s t hC.E_cliqueFree)
  rw [orderedColorWeight_clone_of_zero C hst] at hclone_st
  have hts : C.color t s = PairColor.zero := by
    rw [← C.color_symm s t, hst]
  have hclone_ts :=
    hC.orderedWeight_le
      (DGraph_clone_cliqueFree C t s hC.D_cliqueFree)
      (EGraph_clone_cliqueFree C t s hC.E_cliqueFree)
  rw [orderedColorWeight_clone_of_zero C hts] at hclone_ts
  linarith

/-- In an objective-extremal colored graph, cloning along a color-zero pair is
again objective-extremal: the clone preserves the forbidden-clique hypotheses
and the objective change is zero by degree equality. -/
theorem clone_isColoredObjectiveExtremal_of_zero
    (C : ColoredGraph V) (hC : C.IsColoredObjectiveExtremal)
    {s t : V} (hst : C.color s t = PairColor.zero) :
    (C.clone s t).IsColoredObjectiveExtremal := by
  have hdeg := colorDegree_eq_of_zero_of_objective_extremal C hC hst
  have hweight :
      (C.clone s t).orderedColorWeight = C.orderedColorWeight := by
    rw [orderedColorWeight_clone_of_zero C hst, hdeg]
    ring
  refine ⟨DGraph_clone_cliqueFree C s t hC.D_cliqueFree,
    EGraph_clone_cliqueFree C s t hC.E_cliqueFree, ?_⟩
  intro H hD hE
  rw [hweight]
  exact hC.orderedWeight_le hD hE

/-- The same clone-objective-extremal fact from the stronger two-stage Zykov
extremal package. -/
theorem clone_isColoredObjectiveExtremal_of_zero_of_zykov
    (C : ColoredGraph V) (hC : C.IsColoredZykovExtremal)
    {s t : V} (hst : C.color s t = PairColor.zero) :
    (C.clone s t).IsColoredObjectiveExtremal :=
  clone_isColoredObjectiveExtremal_of_zero C hC.objective hst

/-- If a color-zero pair is not already a twin pair, cloning the smaller twin
class to the larger one strictly increases the ordered twin-pair potential. -/
theorem sameRowPairPotential_clone_gt_of_source_ge_target
    (C : ColoredGraph V) {s t : V}
    (hst : C.color s t = PairColor.zero)
    (hs : s ≠ t)
    (hnst : ¬ C.SameRow s t)
    (hle : C.sameRowClassSize t ≤ C.sameRowClassSize s) :
    C.sameRowPairPotential < (C.clone s t).sameRowPairPotential := by
  classical
  let oldSize : V → Nat := fun v => C.sameRowClassSize v
  let newSize : V → Nat := fun v => (C.clone s t).sameRowClassSize v
  let sourceIndicator : V → Nat :=
    fun v => if C.SameRow s v then 1 else 0
  let targetIndicator : V → Nat :=
    fun v => if C.SameRow t v then 1 else 0
  have hpoint :
      ∀ v ∈ (Finset.univ : Finset V).erase t,
        oldSize v + sourceIndicator v ≤
          newSize v + targetIndicator v := by
    intro v hv
    have hvt : v ≠ t := (Finset.mem_erase.mp hv).1
    by_cases hsv : C.SameRow s v
    · have hnot_t : ¬ C.SameRow t v := by
        intro htv
        exact hnst (sameRow_trans C hsv (sameRow_symm C htv))
      have hgain :
          oldSize v + 1 ≤ newSize v := by
        exact sameRowClassSize_clone_source_twin_ge_succ
          C hst hs hnst hvt hsv
      simp [oldSize, newSize, sourceIndicator, targetIndicator,
        hsv, hnot_t] at hgain ⊢
      exact hgain
    · by_cases htv : C.SameRow t v
      · have hloss :
            oldSize v ≤ newSize v + 1 := by
          exact sameRowClassSize_le_clone_add_one
            C (s := s) (t := t) hvt
        simp [oldSize, newSize, sourceIndicator, targetIndicator,
          hsv, htv] at hloss ⊢
        exact hloss
      · have hnt : ¬ C.SameRow v t := by
          intro hvtwin
          exact htv (sameRow_symm C hvtwin)
        have hle_no_loss :
            oldSize v ≤ newSize v := by
          exact sameRowClassSize_le_clone_of_not_target_twin
            C (s := s) (t := t) hvt hnt
        simp [oldSize, newSize, sourceIndicator, targetIndicator,
          hsv, htv] at hle_no_loss ⊢
        exact hle_no_loss
  have hsum := Finset.sum_le_sum hpoint
  have hsum' :
      (∑ v ∈ (Finset.univ : Finset V).erase t, oldSize v) +
          (∑ v ∈ (Finset.univ : Finset V).erase t,
            sourceIndicator v) ≤
        (∑ v ∈ (Finset.univ : Finset V).erase t, newSize v) +
          (∑ v ∈ (Finset.univ : Finset V).erase t,
            targetIndicator v) := by
    simpa [Finset.sum_add_distrib] using hsum
  have hsource_sum :
      (∑ v ∈ (Finset.univ : Finset V).erase t,
          sourceIndicator v) =
        C.sameRowClassSize s := by
    simpa [sourceIndicator] using
      sum_sameRow_indicator_erase_eq_classSize_of_not_same
        C (a := s) (t := t) hnst
  have htarget_sum :
      (∑ v ∈ (Finset.univ : Finset V).erase t,
          targetIndicator v) + 1 =
        C.sameRowClassSize t := by
    simpa [targetIndicator] using
      sum_sameRow_indicator_erase_add_one_eq_classSize C t
  have hnon_target :
      (∑ v ∈ (Finset.univ : Finset V).erase t, oldSize v) + 1 ≤
        ∑ v ∈ (Finset.univ : Finset V).erase t, newSize v := by
    rw [hsource_sum] at hsum'
    omega
  have htarget_new :
      C.sameRowClassSize t ≤ newSize t := by
    have htarget_gain :=
      sameRowClassSize_clone_target_ge_source_succ C hst hs hnst
    dsimp [newSize]
    omega
  have hold_split :
      C.sameRowPairPotential =
        oldSize t +
          ∑ v ∈ (Finset.univ : Finset V).erase t, oldSize v := by
    unfold sameRowPairPotential
    rw [← Finset.add_sum_erase (Finset.univ : Finset V)
      (fun v : V => C.sameRowClassSize v) (Finset.mem_univ t)]
  have hnew_split :
      (C.clone s t).sameRowPairPotential =
        newSize t +
          ∑ v ∈ (Finset.univ : Finset V).erase t, newSize v := by
    unfold sameRowPairPotential
    rw [← Finset.add_sum_erase (Finset.univ : Finset V)
      (fun v : V => (C.clone s t).sameRowClassSize v) (Finset.mem_univ t)]
  rw [hold_split, hnew_split]
  have htarget_old : oldSize t ≤ newSize t := by
    simpa [oldSize] using htarget_new
  omega

/-- In a two-stage Zykov-extremal colored graph, every color-zero pair is a
twin pair.  Otherwise cloning the smaller twin class to the larger one keeps
the first-stage objective maximal and strictly improves the second-stage
tie-breaker. -/
theorem sameRow_of_zero_of_zykov_extremal
    (C : ColoredGraph V) (hC : C.IsColoredZykovExtremal)
    {s t : V} (hst : C.color s t = PairColor.zero) :
    C.SameRow s t := by
  by_cases hs : s = t
  · subst t
    exact sameRow_refl C s
  by_contra hnst
  by_cases hle : C.sameRowClassSize t ≤ C.sameRowClassSize s
  · have hcloneObj :=
      clone_isColoredObjectiveExtremal_of_zero_of_zykov C hC hst
    have hpot_le := hC.pairPotential_le hcloneObj
    have hgt :=
      sameRowPairPotential_clone_gt_of_source_ge_target
        C hst hs hnst hle
    exact (not_lt_of_ge hpot_le) hgt
  · have hle' : C.sameRowClassSize s ≤ C.sameRowClassSize t :=
      le_of_not_ge hle
    have hts : C.color t s = PairColor.zero := by
      rw [← C.color_symm s t, hst]
    have hnst' : ¬ C.SameRow t s := by
      intro htsrow
      exact hnst (sameRow_symm C htsrow)
    have hcloneObj :=
      clone_isColoredObjectiveExtremal_of_zero_of_zykov C hC hts
    have hpot_le := hC.pairPotential_le hcloneObj
    have hgt :=
      sameRowPairPotential_clone_gt_of_source_ge_target
        C hts (Ne.symm hs) hnst' hle'
    exact (not_lt_of_ge hpot_le) hgt

/-- If the source vertex has at least the target's colored degree, cloning the
target to the source along a color-zero pair does not decrease the objective. -/
theorem orderedColorWeight_le_clone_of_zero_of_degree_le
    (C : ColoredGraph V) {s t : V}
    (hst : C.color s t = PairColor.zero)
    (hle : C.colorDegree t ≤ C.colorDegree s) :
    C.orderedColorWeight ≤ (C.clone s t).orderedColorWeight := by
  rw [orderedColorWeight_clone_of_zero C hst]
  nlinarith

/-- One local colored Zykov clone step preserves the two forbidden-clique
hypotheses and does not decrease the colored objective, provided the source has
at least the target's colored degree. -/
theorem colored_zykov_clone_step
    (C : ColoredGraph V) {s t : V}
    (hst : C.color s t = PairColor.zero)
    (hle : C.colorDegree t ≤ C.colorDegree s)
    (hD : C.DGraph.CliqueFree 4)
    (hE : C.EGraph.CliqueFree 5) :
    C.orderedColorWeight ≤ (C.clone s t).orderedColorWeight ∧
      (C.clone s t).DGraph.CliqueFree 4 ∧
      (C.clone s t).EGraph.CliqueFree 5 := by
  exact ⟨orderedColorWeight_le_clone_of_zero_of_degree_le C hst hle,
    DGraph_clone_cliqueFree C s t hD,
    EGraph_clone_cliqueFree C s t hE⟩

end Weight

end ColoredGraph

end TheoremOneEndToEnd
end Lollipop
