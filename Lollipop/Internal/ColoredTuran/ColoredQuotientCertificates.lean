import Lollipop.Internal.ColoredTuran.ColoredZykovQuotient
import Lollipop.Internal.ColoredTuran.WeightedTuranCertificates

/-!
Colored quotient certificates.

Once colored Zykov has produced a no-zero colored quotient, the blocker graphs
`A` and `B` are read directly from the quotient colors.  The lemmas in
`ColoredZykov` prove that the quotient's `D`/`E` clique-free hypotheses imply
the clique-free complement hypotheses required by the weighted-Turan certificate
layer.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]

/-- Ordered weighted color objective of a finite colored quotient.  It counts
each unordered quotient edge twice and has zero diagonal contribution. -/
def weightedOrderedColorWeight
    (x : Vertex → Nat) (C : ColoredGraph Vertex) : Rat :=
  ∑ v : Vertex, ∑ w : Vertex,
    (x v : Rat) * (x w : Rat) * (C.color v w).weight

/-- Pointwise color-weight identity in a no-zero quotient. -/
theorem color_weight_eq_noZero_formula
    (C : ColoredGraph Vertex) (hzero : C.NoZeroOffDiag)
    (v w : Vertex) :
    (C.color v w).weight =
      3 * (if v ≠ w then (1 : Rat) else 0) -
        2 * (if C.AGraph.Adj v w then (1 : Rat) else 0) -
        2 * (if C.BGraph.Adj v w then (1 : Rat) else 0) := by
  by_cases hvw : v = w
  · subst w
    simp [C.color_self v, ColoredGraph.AGraph, ColoredGraph.BGraph,
      PairColor.weight]
  · have hnzero : C.color v w ≠ PairColor.zero := hzero hvw
    cases hc : C.color v w
    · exact False.elim (hnzero hc)
    · simp [hc, ColoredGraph.AGraph, ColoredGraph.BGraph,
        ColoredGraph.isAColor, ColoredGraph.isBColor, PairColor.weight, hvw]
      norm_num
    · simp [hc, ColoredGraph.AGraph, ColoredGraph.BGraph,
        ColoredGraph.isAColor, ColoredGraph.isBColor, PairColor.weight, hvw]
      norm_num
    · simp [hc, ColoredGraph.AGraph, ColoredGraph.BGraph,
        ColoredGraph.isAColor, ColoredGraph.isBColor, PairColor.weight, hvw]

/-- In a no-zero quotient, the ordered weighted color objective is
`2 * (3P - 2a - 2b)`, where `P` is cross-class mass and `a`, `b` are the
weighted masses of the `A` and `B` blocker graphs. -/
theorem weightedOrderedColorWeight_eq_noZero_formula
    (x : Vertex → Nat) (C : ColoredGraph Vertex)
    (hzero : C.NoZeroOffDiag) :
    weightedOrderedColorWeight x C =
      2 * (3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x C.AGraph.Adj -
        2 * weightedEdgeMass x C.BGraph.Adj) := by
  classical
  calc
    weightedOrderedColorWeight x C =
        ∑ v : Vertex, ∑ w : Vertex,
          (x v : Rat) * (x w : Rat) *
            (3 * (if v ≠ w then (1 : Rat) else 0) -
              2 * (if C.AGraph.Adj v w then (1 : Rat) else 0) -
              2 * (if C.BGraph.Adj v w then (1 : Rat) else 0)) := by
          unfold weightedOrderedColorWeight
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro w _hw
          rw [color_weight_eq_noZero_formula C hzero v w]
    _ = 2 * (3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
          2 * weightedEdgeMass x C.AGraph.Adj -
          2 * weightedEdgeMass x C.BGraph.Adj) := by
          unfold weightedEdgeMass orderedRelWeight
          ring_nf
          simp [Finset.sum_sub_distrib, Finset.sum_mul]

/-- If `sigma` is defined as half the ordered weighted color objective, Lean
derives the manuscript's quotient objective identity. -/
theorem sigma_eq_of_weightedOrderedColorWeight
    {x : Vertex → Nat} {C : ColoredGraph Vertex} {sigma : Rat}
    (hzero : C.NoZeroOffDiag)
    (hsigma : sigma = weightedOrderedColorWeight x C / 2) :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x C.AGraph.Adj -
        2 * weightedEdgeMass x C.BGraph.Adj := by
  rw [hsigma, weightedOrderedColorWeight_eq_noZero_formula x C hzero]
  ring

private theorem sum_fiber_card_mul
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (H : β → Rat) :
    (∑ b : β,
      (((Finset.univ : Finset α).filter
        (fun a : α => f a = b)).card : Rat) * H b) =
      ∑ a : α, H (f a) := by
  classical
  rw [← Finset.sum_fiberwise
    (s := (Finset.univ : Finset α)) (g := f)
    (f := fun a : α => H (f a))]
  apply Finset.sum_congr rfl
  intro b _hb
  have hconst :
      (∑ a ∈ (Finset.univ : Finset α).filter (fun a : α => f a = b),
          H (f a)) =
        ∑ _a ∈ (Finset.univ : Finset α).filter (fun a : α => f a = b),
          H b := by
    apply Finset.sum_congr rfl
    intro a ha
    have hfb : f a = b := (Finset.mem_filter.mp ha).2
    simp [hfb]
  rw [hconst]
  simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The weighted ordered objective of the zero-twin quotient, with class-size
weights, is exactly the original ordered objective. -/
theorem orderedColorWeight_eq_weightedOrderedColorWeight_zeroQuotient
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (h : C.ZeroTwinQuotientReady) :
    C.orderedColorWeight =
      weightedOrderedColorWeight
        (C.zeroClassWeight h) (C.zeroQuotientColoredGraph h) := by
  classical
  let Q := C.ZeroQuotient h
  let f : V → Q := Quotient.mk''
  let Cq : ColoredGraph Q := C.zeroQuotientColoredGraph h
  calc
    C.orderedColorWeight =
        ∑ v : V, ∑ w : V, (Cq.color (f v) (f w)).weight := by
          unfold ColoredGraph.orderedColorWeight ColoredGraph.colorDegree
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro w _hw
          simp [Cq, f, ColoredGraph.zeroQuotientColoredGraph,
            ColoredGraph.quotientColor_mk]
    _ = ∑ v : V, ∑ r : Q,
          ((C.zeroClassWeight h r : Nat) : Rat) *
            (Cq.color (f v) r).weight := by
          apply Finset.sum_congr rfl
          intro v _hv
          symm
          simpa [ColoredGraph.zeroClassWeight, f, Cq, mul_comm] using
            sum_fiber_card_mul (α := V) (β := Q) f
              (fun r : Q => (Cq.color (f v) r).weight)
    _ = ∑ q : Q, ((C.zeroClassWeight h q : Nat) : Rat) *
          (∑ r : Q, ((C.zeroClassWeight h r : Nat) : Rat) *
            (Cq.color q r).weight) := by
          symm
          simpa [ColoredGraph.zeroClassWeight, f, Cq] using
            sum_fiber_card_mul (α := V) (β := Q) f
              (fun q : Q =>
                ∑ r : Q, ((C.zeroClassWeight h r : Nat) : Rat) *
                  (Cq.color q r).weight)
    _ = weightedOrderedColorWeight
          (C.zeroClassWeight h) (C.zeroQuotientColoredGraph h) := by
          unfold weightedOrderedColorWeight
          apply Finset.sum_congr rfl
          intro q _hq
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _hr
          ring

/-- A no-zero colored quotient with weighted class sizes.  The `sigma_eq` field
is the quotient objective identity after colored Zykov has produced the quotient;
the blocker complement clique-free hypotheses are derived, not stored. -/
structure ColoredQuotientCertificate
    (Vertex : Type u) [Fintype Vertex] [DecidableEq Vertex]
    extends QuotientData where
  nNat : Nat
  n_eq : n = (nNat : Rat)
  x : Vertex → Nat
  total_weight : totalWeightNat x = nNat
  Q_eq : Q = weightSquareSumRat x
  C : ColoredGraph Vertex
  no_zero : C.NoZeroOffDiag
  D_cliqueFree : C.DGraph.CliqueFree 4
  E_cliqueFree : C.EGraph.CliqueFree 5
  aOnlyE_eq : aOnlyE = weightedEdgeMass x C.AGraph.Adj
  bOnlyD_eq : bOnlyD = weightedEdgeMass x C.BGraph.Adj
  sigma_eq :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x C.AGraph.Adj -
        2 * weightedEdgeMass x C.BGraph.Adj

/-- Build the colored quotient certificate from a colored graph whose zero
classes are already twin classes.  This packages the formal quotient
construction, class-size weights, objective preservation, no-zero condition,
and inherited `D`/`E` clique-free hypotheses. -/
noncomputable def ColoredGraph.toColoredQuotientCertificate
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (hready : C.ZeroTwinQuotientReady)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    ColoredQuotientCertificate (C.ZeroQuotient hready) := by
  classical
  let Cq : ColoredGraph (C.ZeroQuotient hready) :=
    C.zeroQuotientColoredGraph hready
  let x : C.ZeroQuotient hready → Nat := C.zeroClassWeight hready
  have hno : Cq.NoZeroOffDiag := C.zeroQuotient_noZeroOffDiag hready
  exact
    { n := (Fintype.card V : Rat)
      Q := weightSquareSumRat x
      aOnlyE := weightedEdgeMass x Cq.AGraph.Adj
      bOnlyD := weightedEdgeMass x Cq.BGraph.Adj
      sigma := weightedOrderedColorWeight x Cq / 2
      nNat := Fintype.card V
      n_eq := rfl
      x := x
      total_weight := by
        simpa [x] using C.totalWeightNat_zeroClassWeight hready
      Q_eq := rfl
      C := Cq
      no_zero := hno
      D_cliqueFree := by
        simpa [Cq] using C.zeroQuotient_DGraph_cliqueFree hready hD
      E_cliqueFree := by
        simpa [Cq] using C.zeroQuotient_EGraph_cliqueFree hready hE
      aOnlyE_eq := rfl
      bOnlyD_eq := rfl
      sigma_eq := by
        exact sigma_eq_of_weightedOrderedColorWeight hno rfl }

/-- A colored quotient supplies the weighted-Turan quotient certificate by
deriving the blocker complement clique-free hypotheses from the no-zero quotient
condition and the original `D`/`E` clique-free hypotheses. -/
def ColoredQuotientCertificate.toWeightedTuranCertifiedQuotient
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : ColoredQuotientCertificate Vertex) :
    WeightedTuranCertifiedQuotient Vertex where
  n := q.n
  Q := q.Q
  aOnlyE := q.aOnlyE
  bOnlyD := q.bOnlyD
  sigma := q.sigma
  nNat := q.nNat
  n_eq := q.n_eq
  x := q.x
  total_weight := q.total_weight
  Q_eq := q.Q_eq
  Agraph := q.C.AGraph
  Bgraph := q.C.BGraph
  aOnlyE_eq := q.aOnlyE_eq
  bOnlyD_eq := q.bOnlyD_eq
  A_compl_cliqueFree :=
    ColoredGraph.AGraph_compl_cliqueFree_four_of_DGraph
      q.C q.no_zero q.D_cliqueFree
  B_compl_cliqueFree :=
    ColoredGraph.BGraph_compl_cliqueFree_five_of_EGraph
      q.C q.no_zero q.E_cliqueFree
  sigma_eq := q.sigma_eq

/-- Colored-pair certificate whose quotient is a no-zero colored quotient. -/
structure ColoredQuotientCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  quotient : ColoredQuotientCertificate Vertex
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Convert a colored-quotient pair into the weighted-Turan certificate layer. -/
def ColoredQuotientCertifiedColoredPair.toWeightedTuranCertifiedColoredPair
    (p : ColoredQuotientCertifiedColoredPair.{u}) :
    WeightedTuranCertifiedColoredPair.{u} := by
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  exact
    { nNat := p.nNat
      sigma := p.sigma
      Vertex := p.Vertex
      quotient := p.quotient.toWeightedTuranCertifiedQuotient
      quotient_nNat := p.quotient_nNat
      quotient_preserves_sigma := p.quotient_preserves_sigma }

/-- Colored Turan bound from a no-zero colored quotient, the proved weighted
Turan theorem, partition-intersection bookkeeping, and Section 5. -/
theorem colored_quotient_certified_colored_turan_bound
    (p : ColoredQuotientCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  exact weighted_turan_certified_colored_turan_bound
    p.toWeightedTuranCertifiedColoredPair

/-- Colored Turan bound for a colored graph already in zero-twin quotient form.
The remaining global colored-Zykov task is to prove that every extremal pair can
be transformed into this `ZeroTwinQuotientReady` form. -/
theorem zeroTwin_colored_turan_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (hready : C.ZeroTwinQuotientReady)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    C.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) := by
  classical
  let q := C.toColoredQuotientCertificate hready hD hE
  have hsig :
      q.sigma = C.orderedColorWeight / 2 := by
    change
      weightedOrderedColorWeight
          (C.zeroClassWeight hready)
          (C.zeroQuotientColoredGraph hready) / 2 =
        C.orderedColorWeight / 2
    rw [← orderedColorWeight_eq_weightedOrderedColorWeight_zeroQuotient C hready]
  have hbound :=
    colored_quotient_certified_colored_turan_bound
      { nNat := Fintype.card V
        sigma := C.orderedColorWeight / 2
        Vertex := C.ZeroQuotient hready
        quotient := q
        quotient_nNat := rfl
        quotient_preserves_sigma := by
          rw [hsig] }
  simpa using hbound

/-- Full colored Turan bound for any colored graph satisfying the manuscript's
two forbidden-clique hypotheses.  Lean first selects a finite two-stage
Zykov-extremal graph on the same vertex type, proves it is quotient-ready via
the clone-potential theorem, applies the zero-twin quotient bound, and then
uses first-stage objective maximality to transfer the bound back to `C`. -/
theorem colored_turan_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V)
    (hD : C.DGraph.CliqueFree 4) (hE : C.EGraph.CliqueFree 5) :
    C.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) := by
  classical
  obtain ⟨Cmax, hCmax⟩ :=
    ColoredGraph.exists_isColoredZykovExtremal_of_exists
      (V := V) ⟨C, hD, hE⟩
  have hweight_le : C.orderedColorWeight ≤ Cmax.orderedColorWeight :=
    hCmax.orderedWeight_le hD hE
  have hready : Cmax.ZeroTwinQuotientReady :=
    Cmax.zeroTwinQuotientReady_of_zykov_extremal hCmax
  have hbound :
      Cmax.orderedColorWeight / 2 ≤ concreteS (Fintype.card V) :=
    zeroTwin_colored_turan_bound
      Cmax hready hCmax.D_cliqueFree hCmax.E_cliqueFree
  linarith

/-- Colored-pair certificate at the level of the original colored graph.  The
only graph-theoretic inputs are the two forbidden-clique hypotheses; colored
Zykov, quotienting, weighted Turan, partition-intersection bookkeeping, and the
matrix theorem are all invoked internally by `colored_turan_bound`. -/
structure ColoredGraphCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  C : ColoredGraph Vertex
  D_cliqueFree : C.DGraph.CliqueFree 4
  E_cliqueFree : C.EGraph.CliqueFree 5
  card_eq : Fintype.card Vertex = nNat
  sigma_le_color : sigma ≤ C.orderedColorWeight / 2

/-- Colored Turan bound from an original colored graph certificate. -/
theorem colored_graph_certified_colored_turan_bound
    (p : ColoredGraphCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  have hbound :
      p.C.orderedColorWeight / 2 ≤ concreteS p.nNat := by
    simpa [p.card_eq] using
      colored_turan_bound p.C p.D_cliqueFree p.E_cliqueFree
  exact le_trans p.sigma_le_color hbound

/-- Pairwise lollipop upper certificate using the original colored graph for
the pair score. -/
structure PairwiseColoredGraphCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : ColoredGraphCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Pairwise estimates imply the displayed crossing reduction for colored
graph certificates. -/
theorem pairwise_colored_graph_certified_lollipop_crossing_reduction_choose
    (L : PairwiseColoredGraphCertifiedLollipopUpper.{u}) :
    L.crossings ≤ 4 * ((L.nNat.choose 2 : Nat) : Rat) + L.pair.sigma := by
  have hpair :=
    pairSum_crossing_le_choose_plus_score L.cross L.score
      L.pointwise_crossing_bound
  linarith [L.crossings_le_pairSum, hpair, L.score_sum_le_sigma]

/-- Product-form crossing reduction for colored graph certificates. -/
theorem pairwise_colored_graph_certified_lollipop_crossing_reduction
    (L : PairwiseColoredGraphCertifiedLollipopUpper.{u}) :
    L.crossings ≤
      4 * ((L.nNat : Rat) * ((L.nNat : Rat) - 1) / 2) + L.pair.sigma := by
  have h := pairwise_colored_graph_certified_lollipop_crossing_reduction_choose L
  rw [Nat.cast_choose_two] at h
  exact h

/-- End-to-end upper bound for one arrangement from the original colored graph,
colored Zykov, the quotient construction, weighted Turan, and Section 5. -/
theorem pairwise_colored_graph_certified_lollipop_upper_bound_choose
    (L : PairwiseColoredGraphCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  have ht := colored_graph_certified_colored_turan_bound L.pair
  rw [L.pair_nNat] at ht
  have hc := pairwise_colored_graph_certified_lollipop_crossing_reduction L
  rw [candidateRegionsChoose_eq_candidateRegions]
  unfold candidateRegions
  rw [L.regions_eq]
  linarith

/-- Upper certificates for every arrangement whose two-graph colored pair is
provided as an original colored graph with `D`/`E` clique-free. -/
def PairwiseColoredGraphUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseColoredGraphCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper-bound half of Theorem 1 from original colored graph certificates. -/
theorem upper_bound_of_pairwise_colored_graph_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseColoredGraphUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  rw [← hLreg, ← hLn]
  exact pairwise_colored_graph_certified_lollipop_upper_bound_choose L

/-- Pairwise lollipop upper certificate whose two-graph colored pair is
represented by a no-zero colored quotient. -/
structure PairwiseColoredQuotientCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : ColoredQuotientCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Forget the colored-quotient layer after Lean has derived the blocker
graphs and weighted-Turan hypotheses. -/
def PairwiseColoredQuotientCertifiedLollipopUpper.toPairwiseWeightedTuranCertifiedLollipopUpper
    (L : PairwiseColoredQuotientCertifiedLollipopUpper.{u}) :
    PairwiseWeightedTuranCertifiedLollipopUpper.{u} where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair := L.pair.toWeightedTuranCertifiedColoredPair
  pair_nNat := L.pair_nNat
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := L.score_sum_le_sigma
  regions_eq := L.regions_eq

/-- End-to-end upper bound for one arrangement from a no-zero colored quotient,
the proved weighted Turan theorem, partition-intersection bookkeeping, and
Section 5. -/
theorem pairwise_colored_quotient_certified_lollipop_upper_bound_choose
    (L : PairwiseColoredQuotientCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  exact pairwise_weighted_turan_certified_lollipop_upper_bound_choose
    L.toPairwiseWeightedTuranCertifiedLollipopUpper

/-- Upper certificates for every arrangement whose two-graph colored pair has
a no-zero colored quotient certificate. -/
def PairwiseColoredQuotientUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseColoredQuotientCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert no-zero colored quotient upper certificates into weighted-Turan
upper certificates by deriving the blocker graphs and their clique-free
complement hypotheses. -/
theorem pairwise_colored_quotient_upper_certificates_to_weighted_turan
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseColoredQuotientUpperCertificates P) :
    PairwiseWeightedTuranUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact
    ⟨L.toPairwiseWeightedTuranCertifiedLollipopUpper, hLn, hLreg⟩

/-- Upper-bound half of Theorem 1 from no-zero colored quotient certificates. -/
theorem upper_bound_of_pairwise_colored_quotient_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseColoredQuotientUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_weighted_turan_certificates P
    (pairwise_colored_quotient_upper_certificates_to_weighted_turan hupper)

end TheoremOneEndToEnd
end Lollipop
