import Lollipop.Concrete.EndToEnd.PairGeometry
import Lollipop.Internal.ColoredTuran.ColoredQuotientCertificates
import Lollipop.Internal.Manuscript.FormulaBridge
import Mathlib.Tactic

/-!
# Unconditional concrete upper bound

For each concrete Euclidean arrangement this module constructs, internally,
the geometric data consumed by the existing colored-Turán backend.  The public
theorem has no geometry-certificate argument.

There is one important boundary issue.  The manuscript calls two circles
*intriguing* when they are disjoint or their squared center distance is at most
the sum of their squared radii.  Thus an external tangency is **not**
intriguing.  The older canonical Paulsen relation is the complement of an open
obtuse interval and includes that tangency boundary.  It cannot be used
verbatim: an externally tangent non-close pair can have six compactified pair
intersection components away from infinity.

We follow the manuscript exactly.  For a fixed finite arrangement, enlarge all
radii by one common factor `λ > 1`, chosen sufficiently close to one.  Every
pair which is non-intriguing for the original circles then lies strictly in the
Paulsen obtuse interval for the enlarged radii.  These enlarged circles are
used only to prove the five-circle obstruction; all pair-component estimates
remain estimates for the original lollipops.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set BigOperators

/-- Candidate formula bridge. -/
theorem candidate_eq_candidateRegionsChoose (n : ℕ) :
    candidate n = Lollipop.candidateRegionsChoose n := by
  unfold candidate Lollipop.candidateRegionsChoose
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]

namespace UpperPort

/-- Failure of the manuscript intriguing relation gives a genuine circle
intersection and the strict lower obtuse-distance inequality. -/
theorem not_intriguing_iff_meet_and_dist_sq_gt
    (L M : Lollipop) :
    ¬ PairGeometry.Intriguing L M ↔
      (cc L M).Nonempty ∧
        L.radius ^ 2 + M.radius ^ 2 <
          TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
            (R2.ofPoint L.center) (R2.ofPoint M.center) := by
  unfold PairGeometry.Intriguing
  push_neg
  constructor <;> rintro ⟨hmeet, hdist⟩ <;> exact ⟨hmeet, hdist⟩

/-- If the two circle curves meet, their center distance is at most the sum of
their radii. -/
theorem distSq2_le_radius_add_sq_of_cc_nonempty
    {L M : Lollipop} (hmeet : (cc L M).Nonempty) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
      (L.radius + M.radius) ^ 2 := by
  rcases hmeet with ⟨x, hxL, hxM⟩
  have hxLc : x ∈ L.circle := hxL.1
  have hxMc : x ∈ M.circle := hxM.2
  have hL : dist L.center x = L.radius := by
    simpa [Lollipop.circle, dist_eq_norm, norm_sub_rev] using hxLc
  have hM : dist x M.center = M.radius := by
    simpa [Lollipop.circle, dist_eq_norm] using hxMc
  have htri : dist L.center M.center ≤ L.radius + M.radius := by
    simpa [hL, hM] using dist_triangle L.center x M.center
  have hnonneg : 0 ≤ L.radius + M.radius :=
    add_nonneg (le_of_lt L.radius_pos) (le_of_lt M.radius_pos)
  rw [← TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq]
  nlinarith [dist_nonneg L.center M.center]

/-- Uniform radius enlargement used only for Paulsen's five-circle argument.

The lower strict inequality holds at `λ = 1` for every non-intriguing pair.
There are finitely many pairs and all inequalities depend continuously on
`λ`, so their common validity set is an open neighborhood of one.  Choose
`λ > 1` in that neighborhood.  The upper strict inequality follows from
circle intersection and `λ > 1`; in particular, an external tangency becomes
a transverse intersection after enlargement.

The helper `isOpen_finite_forall_strict_polynomial` below denotes the routine
finite-intersection/continuity lemma to be adapted to the pinned Mathlib API.
It is deliberately local to this port namespace rather than a hypothesis of
the endpoint. -/
theorem exists_uniform_paulsen_scale {n : ℕ} (A : Arrangement n) :
    ∃ λ : ℝ, 1 < λ ∧
      ∀ i j : Fin n, i ≠ j →
        ¬ PairGeometry.Intriguing (A i) (A j) →
          (λ * (A i).radius) ^ 2 + (λ * (A j).radius) ^ 2 <
              TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
                (R2.ofPoint (A i).center) (R2.ofPoint (A j).center) ∧
            TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
                (R2.ofPoint (A i).center) (R2.ofPoint (A j).center) <
              (λ * (A i).radius + λ * (A j).radius) ^ 2 := by
  classical
  let U : Set ℝ :=
    {λ | ∀ i j : Fin n, i ≠ j →
      ¬ PairGeometry.Intriguing (A i) (A j) →
        (λ * (A i).radius) ^ 2 + (λ * (A j).radius) ^ 2 <
          TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
            (R2.ofPoint (A i).center) (R2.ofPoint (A j).center)}
  have hUopen : IsOpen U := by
    exact isOpen_finite_forall_strict_polynomial
      (fun λ i j =>
        (λ * (A i).radius) ^ 2 + (λ * (A j).radius) ^ 2)
      (fun _λ i j =>
        TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
          (R2.ofPoint (A i).center) (R2.ofPoint (A j).center))
      (by fun_prop) (by fun_prop)
  have h1U : (1 : ℝ) ∈ U := by
    intro i j hij hnot
    have hlow :=
      (not_intriguing_iff_meet_and_dist_sq_gt (A i) (A j)).1 hnot
    simpa using hlow.2
  obtain ⟨λ, hλgt, hλU⟩ :=
    exists_gt_mem_of_isOpen_mem hUopen h1U
  refine ⟨λ, hλgt, ?_⟩
  intro i j hij hnot
  have hlow := hλU i j hij hnot
  have hmeet :=
    ((not_intriguing_iff_meet_and_dist_sq_gt (A i) (A j)).1 hnot).1
  have hupp0 := distSq2_le_radius_add_sq_of_cc_nonempty hmeet
  have hradd : 0 < (A i).radius + (A j).radius := by
    positivity
  have hλpos : 0 < λ := lt_trans (by norm_num) hλgt
  have hscale :
      ((A i).radius + (A j).radius) ^ 2 <
        (λ * ((A i).radius + (A j).radius)) ^ 2 := by
    nlinarith
  refine ⟨hlow, ?_⟩
  calc
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint (A i).center) (R2.ofPoint (A j).center)
        ≤ ((A i).radius + (A j).radius) ^ 2 := hupp0
    _ < (λ * ((A i).radius + (A j).radius)) ^ 2 := hscale
    _ = (λ * (A i).radius + λ * (A j).radius) ^ 2 := by ring

end UpperPort

/-- The common radius scale selected for one finite arrangement. -/
noncomputable def paulsenScale {n : ℕ} (A : Arrangement n) : ℝ :=
  Classical.choose (UpperPort.exists_uniform_paulsen_scale A)

@[simp] theorem one_lt_paulsenScale {n : ℕ} (A : Arrangement n) :
    1 < paulsenScale A :=
  (Classical.choose_spec (UpperPort.exists_uniform_paulsen_scale A)).1

/-- Enlarged radii used only in the Paulsen obstruction. -/
def paulsenRadius {n : ℕ} (A : Arrangement n) : Fin n → ℝ :=
  fun i => paulsenScale A * (A i).radius

@[simp] theorem paulsenRadius_pos {n : ℕ} (A : Arrangement n) :
    ∀ i, 0 < paulsenRadius A i := by
  intro i
  exact mul_pos (lt_trans (by norm_num) (one_lt_paulsenScale A))
    (A i).radius_pos

/-- A non-intriguing original pair lies in the strict Paulsen interval after
the common radius enlargement. -/
theorem paulsen_scaled_nonintriguing_bounds {n : ℕ} (A : Arrangement n)
    (i j : Fin n) (hij : i ≠ j)
    (hnot : ¬ PairGeometry.Intriguing (A i) (A j)) :
    paulsenRadius A i ^ 2 + paulsenRadius A j ^ 2 <
        TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
          (centerR2 A i) (centerR2 A j) ∧
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
          (centerR2 A i) (centerR2 A j) <
        (paulsenRadius A i + paulsenRadius A j) ^ 2 := by
  exact (Classical.choose_spec
    (UpperPort.exists_uniform_paulsen_scale A)).2 i j hij hnot

/-- Any four actual stem directions contain a close pair. -/
theorem close_pair_in_every_four {n : ℕ} (A : Arrangement n) :
    ∀ t : Finset (Fin n), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ PairGeometry.Close (A i) (A j) := by
  intro t ht
  rcases TheoremOneEndToEnd.CloseDirection.exists_cyclicClose_pair_of_card_four
      (direction01 A) ht
      (fun i _hi => direction01_nonneg A i)
      (fun i _hi => direction01_lt_one A i) with
    ⟨i, hi, j, hj, hij, hclose⟩
  exact ⟨i, hi, j, hj, hij,
    radial_dot_nonneg_of_cyclicClose (by simpa [direction01] using hclose)⟩

/-- The four concrete pointwise pair bounds consumed by the old backend. -/
theorem pairExcessTable_le_general {n : ℕ} (A : Arrangement n)
    (i j : Fin n) (_hij : i < j) : pairExcessTable A i j ≤ 7 := by
  simpa [pairExcessTable] using
    PairGeometry.pairExcess_le_seven (A i) (A j)

theorem pairExcessTable_le_close {n : ℕ} (A : Arrangement n)
    (i j : Fin n) (_hij : i < j)
    (hclose : PairGeometry.Close (A i) (A j)) :
    pairExcessTable A i j ≤ 5 := by
  simpa [pairExcessTable] using
    PairGeometry.pairExcess_le_five_of_close hclose

theorem pairExcessTable_le_intriguing {n : ℕ} (A : Arrangement n)
    (i j : Fin n) (_hij : i < j)
    (hintr : PairGeometry.Intriguing (A i) (A j)) :
    pairExcessTable A i j ≤ 5 := by
  simpa [pairExcessTable] using
    PairGeometry.pairExcess_le_five_of_intriguing hintr

theorem pairExcessTable_le_close_intriguing {n : ℕ} (A : Arrangement n)
    (i j : Fin n) (_hij : i < j)
    (hclose : PairGeometry.Close (A i) (A j))
    (hintr : PairGeometry.Intriguing (A i) (A j)) :
    pairExcessTable A i j ≤ 4 := by
  simpa [pairExcessTable] using
    PairGeometry.pairExcess_le_four_of_close_intriguing hclose hintr

/-- Global-circle backend data constructed from an actual arrangement.  The
center/radius data in this record are the uniformly enlarged auxiliary
circles; the crossing table and both geometric relations refer to the original
lollipops. -/
noncomputable def upperData {n : ℕ} (A : Arrangement n) :
    TheoremOneEndToEnd.PairwiseGlobalCircleGeometricLollipopUpper := by
  classical
  exact
    { nNat := n
      crossings := regionCountRat A - (n : ℚ) - 1
      regions := regionCountRat A
      close := fun i j => PairGeometry.Close (A i) (A j)
      intriguing := fun i j => PairGeometry.Intriguing (A i) (A j)
      close_decidable := inferInstance
      intriguing_decidable := inferInstance
      close_symm := fun i j => PairGeometry.close_symm (A i) (A j)
      intriguing_symm := fun i j => PairGeometry.intriguing_symm (A i) (A j)
      center := centerR2 A
      radius := paulsenRadius A
      radius_pos := paulsenRadius_pos A
      nonintriguing_dist_low := by
        intro i j hij hnot
        exact (paulsen_scaled_nonintriguing_bounds A i j hij hnot).1
      nonintriguing_dist_high := by
        intro i j hij hnot
        exact (paulsen_scaled_nonintriguing_bounds A i j hij hnot).2
      cross := pairExcessTable A
      crossings_le_pairSum := crossing_excess_le_pairSum A
      cross_le_general := pairExcessTable_le_general A
      cross_le_close := pairExcessTable_le_close A
      cross_le_intriguing := pairExcessTable_le_intriguing A
      cross_le_close_intriguing := pairExcessTable_le_close_intriguing A
      close_pair_in_every_four := close_pair_in_every_four A
      regions_eq := by ring }

/-- Upper bound for one concrete arrangement. -/
theorem regionCountRat_le_candidate {n : ℕ} (A : Arrangement n) :
    regionCountRat A ≤ candidate n := by
  let G := (upperData A).toPairwiseGeometricLollipopUpper
  let C := G.toPairwiseColoredGraphCertifiedLollipopUpper
  have h := pairwise_colored_graph_certified_lollipop_upper_bound_choose C
  simpa [C, G, upperData, candidate_eq_candidateRegionsChoose] using h

/-- All-size concrete upper theorem. -/
theorem regionUpper (n : ℕ) : RegionUpperStatement n :=
  fun A => regionCountRat_le_candidate A

theorem regionUpper_all : ∀ n : ℕ, RegionUpperStatement n := regionUpper

end EndToEnd
end Concrete
end Lollipop
