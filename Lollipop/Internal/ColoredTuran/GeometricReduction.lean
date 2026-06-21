import Lollipop.Internal.ColoredTuran.ColoredQuotientCertificates

/-!
Geometric-input reduction.

This module moves the remaining upper-bound boundary one step closer to the
manuscript.  Instead of asking for a prebuilt colored graph certificate, it
starts from the geometric predicates used in the paper: `close` and
`intriguing`, a pairwise crossing table, the pointwise geometric crossing
bounds, and the two finite forbidden-pair facts.  Lean then constructs the
four-colored graph and produces the colored-graph upper certificate used by
the fully internalized colored Turan stack.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ColoredGraph

variable {V : Type u} [DecidableEq V]

/-- The four-coloring determined by the manuscript's two geometric predicates.
Color `B` means `D`-only, i.e. not close but intriguing; color `A` means
`E`-only, i.e. close but not intriguing; color `X` means neither close nor
intriguing. -/
def colorOfCloseIntriguing
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (v w : V) : PairColor :=
  if v = w then
    PairColor.zero
  else if close v w then
    if intriguing v w then PairColor.zero else PairColor.A
  else if intriguing v w then
    PairColor.B
  else
    PairColor.X

/-- The colored graph built from the close/intriguing predicates. -/
def ofCloseIntriguing
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v) :
    ColoredGraph V where
  color := colorOfCloseIntriguing close intriguing
  color_symm := by
    intro v w
    by_cases hvw : v = w
    · subst w
      simp [colorOfCloseIntriguing]
    · have hwv : w ≠ v := Ne.symm hvw
      simp [colorOfCloseIntriguing, hvw, hwv,
        hclose_symm v w, hintr_symm v w]
  color_self := by
    intro v
    simp [colorOfCloseIntriguing]

@[simp]
theorem ofCloseIntriguing_color
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    (v w : V) :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).color v w =
      colorOfCloseIntriguing close intriguing v w := by
  rfl

/-- In the close/intriguing coloring, the derived `D` graph is exactly the
off-diagonal relation "not close". -/
theorem ofCloseIntriguing_DGraph_adj_iff
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    {v w : V} :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).DGraph.Adj v w ↔
      v ≠ w ∧ ¬ close v w := by
  by_cases hvw : v = w
  · subst w
    simp [DGraph, colorOfCloseIntriguing, isDColor]
  · by_cases hc : close v w <;>
      by_cases hi : intriguing v w <;>
        simp [DGraph, colorOfCloseIntriguing, isDColor, hvw, hc, hi]

/-- In the close/intriguing coloring, the derived `E` graph is exactly the
off-diagonal relation "not intriguing". -/
theorem ofCloseIntriguing_EGraph_adj_iff
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    {v w : V} :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).EGraph.Adj v w ↔
      v ≠ w ∧ ¬ intriguing v w := by
  by_cases hvw : v = w
  · subst w
    simp [EGraph, colorOfCloseIntriguing, isEColor]
  · by_cases hc : close v w <;>
      by_cases hi : intriguing v w <;>
        simp [EGraph, colorOfCloseIntriguing, isEColor, hvw, hc, hi]

/-- If every four vertices contain a close pair, the `D = not close` graph is
`K_4`-free. -/
theorem ofCloseIntriguing_DGraph_cliqueFree_four
    [Fintype V]
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    (hclose_four :
      ∀ t : Finset V, t.card = 4 →
        ∃ v ∈ t, ∃ w ∈ t, v ≠ w ∧ close v w) :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).DGraph.CliqueFree 4 := by
  intro t ht
  rcases hclose_four t ht.card_eq with ⟨v, hv, w, hw, hvw, hclose⟩
  have hadj := ht.isClique hv hw hvw
  have hnot_close :
      ¬ close v w := by
    exact ((ofCloseIntriguing_DGraph_adj_iff
      close intriguing hclose_symm hintr_symm).mp hadj).2
  exact hnot_close hclose

/-- If every five vertices contain an intriguing pair, the `E = not
intriguing` graph is `K_5`-free. -/
theorem ofCloseIntriguing_EGraph_cliqueFree_five
    [Fintype V]
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    (hintr_five :
      ∀ t : Finset V, t.card = 5 →
        ∃ v ∈ t, ∃ w ∈ t, v ≠ w ∧ intriguing v w) :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).EGraph.CliqueFree 5 := by
  intro t ht
  rcases hintr_five t ht.card_eq with ⟨v, hv, w, hw, hvw, hintr⟩
  have hadj := ht.isClique hv hw hvw
  have hnot_intr :
      ¬ intriguing v w := by
    exact ((ofCloseIntriguing_EGraph_adj_iff
      close intriguing hclose_symm hintr_symm).mp hadj).2
  exact hnot_intr hintr

end ColoredGraph

section PairSums

/-- For a symmetric zero-diagonal table on `Fin n`, the ordered double sum is
twice the increasing-pair sum. -/
theorem two_pairSum_eq_double_sum_of_symm_zero_diag
    (n : Nat) (f : Fin n → Fin n → Rat)
    (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    2 * pairSum n f = ∑ i : Fin n, ∑ j : Fin n, f i j := by
  classical
  let all : Finset (Fin n × Fin n) := Finset.univ
  let ltSet : Finset (Fin n × Fin n) := all.filter (fun p => p.1 < p.2)
  let gtSet : Finset (Fin n × Fin n) := all.filter (fun p => p.2 < p.1)
  let eqSet : Finset (Fin n × Fin n) := all.filter (fun p => p.1 = p.2)
  have hpair : pairFinset n = ltSet := by
    ext p
    simp [pairFinset, ltSet, all]
  have hgt_eq :
      (∑ p ∈ gtSet, f p.1 p.2) =
        ∑ p ∈ ltSet, f p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp [gtSet, ltSet, all] at hp ⊢
      exact hp
    · intro a ha b hb h
      cases a
      cases b
      simp at h
      aesop
    · intro b hb
      refine ⟨(b.2, b.1), ?_, ?_⟩
      · simp [gtSet, ltSet, all] at hb ⊢
        exact hb
      · simp
    · intro p hp
      exact hsymm p.1 p.2
  have heq_zero : (∑ p ∈ eqSet, f p.1 p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [eqSet, all] at hp
    simpa [hp] using hdiag p.1
  have hpartition : all = ltSet ∪ eqSet ∪ gtSet := by
    ext p
    simp [all, ltSet, eqSet, gtSet]
    omega
  have hdisj_lt_eq : Disjoint ltSet eqSet := by
    rw [Finset.disjoint_left]
    intro p hlt heq
    simp [ltSet, eqSet, all] at hlt heq
    omega
  have hdisj_lteq_gt : Disjoint (ltSet ∪ eqSet) gtSet := by
    rw [Finset.disjoint_left]
    intro p hp hgt
    rw [Finset.mem_union] at hp
    simp [ltSet, eqSet, gtSet, all] at hp hgt
    rcases hp with hp | hp <;> omega
  have hfull_parts :
      (∑ p : Fin n × Fin n, f p.1 p.2) =
        (∑ p ∈ ltSet, f p.1 p.2) +
        (∑ p ∈ eqSet, f p.1 p.2) +
        (∑ p ∈ gtSet, f p.1 p.2) := by
    calc
      (∑ p : Fin n × Fin n, f p.1 p.2) =
          ∑ p ∈ all, f p.1 p.2 := by
            simp [all]
      _ = ∑ p ∈ ltSet ∪ eqSet ∪ gtSet, f p.1 p.2 := by
            rw [← hpartition]
      _ = (∑ p ∈ ltSet ∪ eqSet, f p.1 p.2) +
            (∑ p ∈ gtSet, f p.1 p.2) := by
            rw [Finset.sum_union hdisj_lteq_gt]
      _ = ((∑ p ∈ ltSet, f p.1 p.2) +
            (∑ p ∈ eqSet, f p.1 p.2)) +
            (∑ p ∈ gtSet, f p.1 p.2) := by
            rw [Finset.sum_union hdisj_lt_eq]
      _ = (∑ p ∈ ltSet, f p.1 p.2) +
            (∑ p ∈ eqSet, f p.1 p.2) +
            (∑ p ∈ gtSet, f p.1 p.2) := by
            ring
  have hprod :
      (∑ i : Fin n, ∑ j : Fin n, f i j) =
        ∑ p : Fin n × Fin n, f p.1 p.2 := by
    symm
    rw [← Finset.sum_product
      (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin n))
      (fun p : Fin n × Fin n => f p.1 p.2)]
    simp only [Finset.univ_product_univ]
  rw [hprod, hfull_parts, heq_zero, hgt_eq]
  unfold pairSum
  rw [hpair]
  ring

/-- A colored graph on `Fin n` has ordered objective equal to twice the
increasing-pair color-weight sum. -/
theorem two_pairSum_colorWeight_eq_orderedColorWeight
    (n : Nat) (C : ColoredGraph (Fin n)) :
    2 * pairSum n (fun i j => (C.color i j).weight) =
      C.orderedColorWeight := by
  rw [two_pairSum_eq_double_sum_of_symm_zero_diag]
  · rfl
  · intro i j
    rw [C.color_symm i j]
  · intro i
    simp [C.color_self i, PairColor.weight]

end PairSums

/-- The exact geometric data from which Lean can build the current strongest
upper certificate: close/intriguing relations, pairwise crossings, the
pointwise geometric crossing bounds, and the two forbidden-pair facts. -/
structure PairwiseGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  intriguing_pair_in_every_five :
    ∀ t : Finset (Fin nNat), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ intriguing i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

namespace PairwiseGeometricLollipopUpper

/-- The colored graph canonically associated to the geometric predicates. -/
noncomputable def coloredGraph (L : PairwiseGeometricLollipopUpper) :
    ColoredGraph (Fin L.nNat) := by
  letI : DecidableRel L.close := L.close_decidable
  letI : DecidableRel L.intriguing := L.intriguing_decidable
  exact ColoredGraph.ofCloseIntriguing
    L.close L.intriguing L.close_symm L.intriguing_symm

/-- Its pair score is exactly the color weight of the associated pair. -/
noncomputable def score (L : PairwiseGeometricLollipopUpper) :
    Fin L.nNat → Fin L.nNat → Rat :=
  fun i j => ((L.coloredGraph).color i j).weight

/-- The pointwise geometric cases imply the manuscript's
`cross <= 4 + score` estimate. -/
theorem pointwise_crossing_bound
    (L : PairwiseGeometricLollipopUpper) :
    ∀ i j : Fin L.nNat, i < j → L.cross i j ≤ 4 + L.score i j := by
  intro i j hij
  letI : DecidableRel L.close := L.close_decidable
  letI : DecidableRel L.intriguing := L.intriguing_decidable
  have hne : i ≠ j := ne_of_lt hij
  by_cases hc : L.close i j
  · by_cases hi : L.intriguing i j
    · have hcross := L.cross_le_close_intriguing i j hij hc hi
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith
    · have hcross := L.cross_le_close i j hij hc
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith
  · by_cases hi : L.intriguing i j
    · have hcross := L.cross_le_intriguing i j hij hi
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith
    · have hcross := L.cross_le_general i j hij
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith

/-- Convert geometric close/intriguing data into the colored-graph certificate
used by the internalized colored Turan proof. -/
noncomputable def toPairwiseColoredGraphCertifiedLollipopUpper
    (L : PairwiseGeometricLollipopUpper) :
    PairwiseColoredGraphCertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair :=
    { nNat := L.nNat
      sigma := pairSum L.nNat L.score
      Vertex := Fin L.nNat
      C := L.coloredGraph
      D_cliqueFree := by
        letI : DecidableRel L.close := L.close_decidable
        letI : DecidableRel L.intriguing := L.intriguing_decidable
        simpa [coloredGraph] using
          ColoredGraph.ofCloseIntriguing_DGraph_cliqueFree_four
            L.close L.intriguing L.close_symm L.intriguing_symm
            L.close_pair_in_every_four
      E_cliqueFree := by
        letI : DecidableRel L.close := L.close_decidable
        letI : DecidableRel L.intriguing := L.intriguing_decidable
        simpa [coloredGraph] using
          ColoredGraph.ofCloseIntriguing_EGraph_cliqueFree_five
            L.close L.intriguing L.close_symm L.intriguing_symm
            L.intriguing_pair_in_every_five
      card_eq := Fintype.card_fin L.nNat
      sigma_le_color := by
        have hordered :=
          two_pairSum_colorWeight_eq_orderedColorWeight L.nNat L.coloredGraph
        change
          pairSum L.nNat (fun i j => (L.coloredGraph.color i j).weight) ≤
            L.coloredGraph.orderedColorWeight / 2
        linarith }
  pair_nNat := rfl
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := by rfl
  regions_eq := L.regions_eq

end PairwiseGeometricLollipopUpper

/-- Upper certificates for every arrangement from exactly the geometric
close/intriguing data used in the manuscript. -/
def PairwiseGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper-bound half of Theorem 1 from the manuscript's close/intriguing
geometric upper data. -/
theorem upper_bound_of_pairwise_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  rw [← hLreg, ← hLn]
  exact pairwise_colored_graph_certified_lollipop_upper_bound_choose
    L.toPairwiseColoredGraphCertifiedLollipopUpper

end TheoremOneEndToEnd
end Lollipop
