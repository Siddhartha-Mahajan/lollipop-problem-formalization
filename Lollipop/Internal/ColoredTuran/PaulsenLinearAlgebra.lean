import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
Paulsen's five-circle linear algebra obstruction.

The manuscript appendix proves that five pairwise non-intriguing circles
cannot exist by translating them to five vectors in `R^4` with Gram values
`1` on the diagonal and in `(-1, 0)` off the diagonal for a symmetric
indefinite bilinear form.  This module formalizes the circle-vector
calculation from centers/radii and distance inequalities, plus the
linear-algebraic contradiction.  The remaining Euclidean boundary is proving
that the manuscript's non-intriguing circle relation supplies those distance
inequalities.
-/

namespace Lollipop
namespace TheoremOneEndToEnd
namespace PaulsenLinearAlgebra

open BigOperators

abbrev R4 := Fin 4 → ℝ

abbrev R2 := Fin 2 → ℝ

/-- The Euclidean dot product on the coordinate model `Fin 2 -> R`. -/
def dot2 (x y : R2) : ℝ :=
  x 0 * y 0 + x 1 * y 1

/-- Squared norm in the coordinate model `Fin 2 -> R`. -/
def normSq2 (x : R2) : ℝ :=
  dot2 x x

/-- Squared Euclidean distance in the coordinate model `Fin 2 -> R`. -/
def distSq2 (x y : R2) : ℝ :=
  normSq2 (x - y)

theorem distSq2_symm (x y : R2) :
    distSq2 x y = distSq2 y x := by
  unfold distSq2 normSq2 dot2
  simp [Pi.sub_apply]
  ring

/-- Paulsen's obtuse-intersection distance condition for two circles. -/
def circleObtuseCondition (r s : ℝ) (x y : R2) : Prop :=
  r ^ 2 + s ^ 2 < distSq2 x y ∧ distSq2 x y < (r + s) ^ 2

/-- The circle relation corresponding to the manuscript's "intriguing"
condition at the level needed by Paulsen's appendix: a pair is intriguing
unless it satisfies the strict obtuse-intersection distance condition. -/
def circleIntriguingPair (r s : ℝ) (x y : R2) : Prop :=
  ¬ circleObtuseCondition r s x y

/-- The canonical circle-coordinate intriguing relation on an indexed family. -/
def circleIntriguing {V : Type*}
    (center : V → R2) (radius : V → ℝ) (i j : V) : Prop :=
  circleIntriguingPair (radius i) (radius j) (center i) (center j)

theorem circleObtuseCondition_symm
    (r s : ℝ) (x y : R2) :
    circleObtuseCondition r s x y ↔
      circleObtuseCondition s r y x := by
  unfold circleObtuseCondition
  rw [distSq2_symm y x]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith [h.1, h.2]

theorem circleIntriguingPair_symm
    (r s : ℝ) (x y : R2) :
    circleIntriguingPair r s x y ↔ circleIntriguingPair s r y x := by
  unfold circleIntriguingPair
  rw [circleObtuseCondition_symm]

theorem circleIntriguing_symm {V : Type*}
    (center : V → R2) (radius : V → ℝ) (i j : V) :
    circleIntriguing center radius i j ↔ circleIntriguing center radius j i := by
  exact circleIntriguingPair_symm (radius i) (radius j) (center i) (center j)

theorem circleObtuseCondition_of_not_circleIntriguing {V : Type*}
    (center : V → R2) (radius : V → ℝ) {i j : V}
    (h : ¬ circleIntriguing center radius i j) :
    circleObtuseCondition (radius i) (radius j) (center i) (center j) := by
  classical
  exact of_not_not h

/-- Paulsen's symmetric bilinear form on `R^4`, written as
`(α, β, x₁, x₂)`. -/
noncomputable def lorentzForm (x y : R4) : ℝ :=
  (2 : ℝ)⁻¹ * x 0 * y 1 +
    (2 : ℝ)⁻¹ * x 1 * y 0 +
      x 2 * y 2 + x 3 * y 3

/-- The vector attached to a circle with center `x` and radius `r` in
Paulsen's appendix: `(1/r) * (1, r^2 - |x|^2, x)`. -/
noncomputable def circleVec (r : ℝ) (x : R2) : R4
  | 0 => r⁻¹
  | 1 => r⁻¹ * (r ^ 2 - normSq2 x)
  | 2 => r⁻¹ * x 0
  | 3 => r⁻¹ * x 1

@[simp]
theorem circleVec_zero (r : ℝ) (x : R2) :
    circleVec r x 0 = r⁻¹ := rfl

@[simp]
theorem circleVec_one (r : ℝ) (x : R2) :
    circleVec r x 1 = r⁻¹ * (r ^ 2 - normSq2 x) := rfl

@[simp]
theorem circleVec_two (r : ℝ) (x : R2) :
    circleVec r x 2 = r⁻¹ * x 0 := rfl

@[simp]
theorem circleVec_three (r : ℝ) (x : R2) :
    circleVec r x 3 = r⁻¹ * x 1 := rfl

theorem circleVec_first_pos {r : ℝ} (hr : 0 < r) (x : R2) :
    0 < circleVec r x 0 := by
  simp [inv_pos.mpr hr]

/-- Direct calculation: Paulsen's vector has Gram value `1` with itself. -/
theorem lorentzForm_circleVec_self {r : ℝ} (x : R2) (hr : r ≠ 0) :
    lorentzForm (circleVec r x) (circleVec r x) = 1 := by
  unfold lorentzForm circleVec normSq2 dot2
  field_simp [hr]
  ring

/-- Direct calculation of the off-diagonal Gram value for two circle vectors. -/
theorem lorentzForm_circleVec_pair
    {r s : ℝ} (x y : R2) (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentzForm (circleVec r x) (circleVec s y) =
      (r ^ 2 + s ^ 2 - distSq2 x y) / (2 * r * s) := by
  unfold lorentzForm circleVec distSq2 normSq2 dot2
  field_simp [hr, hs]
  simp [Pi.sub_apply]
  ring_nf

/-- The lower distance inequality in Paulsen's obtuse-intersection condition
forces the off-diagonal Gram value to be negative. -/
theorem lorentzForm_circleVec_pair_neg
    {r s : ℝ} (x y : R2) (hr : 0 < r) (hs : 0 < s)
    (hdist : r ^ 2 + s ^ 2 < distSq2 x y) :
    lorentzForm (circleVec r x) (circleVec s y) < 0 := by
  rw [lorentzForm_circleVec_pair x y (ne_of_gt hr) (ne_of_gt hs)]
  have hden : 0 < 2 * r * s := by positivity
  have hnum : r ^ 2 + s ^ 2 - distSq2 x y < 0 := by linarith
  exact div_neg_of_neg_of_pos hnum hden

/-- The upper distance inequality in Paulsen's obtuse-intersection condition
forces the off-diagonal Gram value to be greater than `-1`. -/
theorem lorentzForm_circleVec_pair_gt_neg_one
    {r s : ℝ} (x y : R2) (hr : 0 < r) (hs : 0 < s)
    (hdist : distSq2 x y < (r + s) ^ 2) :
    -1 < lorentzForm (circleVec r x) (circleVec s y) := by
  rw [lorentzForm_circleVec_pair x y (ne_of_gt hr) (ne_of_gt hs)]
  have hden : 0 < 2 * r * s := by positivity
  have hnum : -(2 * r * s) < r ^ 2 + s ^ 2 - distSq2 x y := by
    nlinarith
  have hdiv := div_lt_div_of_pos_right hnum hden
  have hminus : (-(2 * r * s)) / (2 * r * s) = -1 := by
    field_simp [ne_of_gt hden]
  linarith

theorem lorentzForm_symm (x y : R4) :
    lorentzForm x y = lorentzForm y x := by
  unfold lorentzForm
  ring_nf

theorem lorentzForm_add_left (x y z : R4) :
    lorentzForm (x + y) z = lorentzForm x z + lorentzForm y z := by
  unfold lorentzForm
  simp [Pi.add_apply]
  ring_nf

theorem lorentzForm_add_right (x y z : R4) :
    lorentzForm x (y + z) = lorentzForm x y + lorentzForm x z := by
  rw [lorentzForm_symm x (y + z), lorentzForm_add_left, lorentzForm_symm y x,
    lorentzForm_symm z x]

theorem lorentzForm_smul_left (a : ℝ) (x y : R4) :
    lorentzForm (a • x) y = a * lorentzForm x y := by
  unfold lorentzForm
  simp [Pi.smul_apply]
  ring_nf

theorem lorentzForm_smul_right (a : ℝ) (x y : R4) :
    lorentzForm x (a • y) = a * lorentzForm x y := by
  rw [lorentzForm_symm x (a • y), lorentzForm_smul_left, lorentzForm_symm y x]

theorem lorentzForm_sum_left {ι : Type*}
    (s : Finset ι) (f : ι → R4) (w : R4) :
    lorentzForm (∑ i ∈ s, f i) w = ∑ i ∈ s, lorentzForm (f i) w := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [lorentzForm]
  · intro a s has hs
    simp [has, hs, lorentzForm_add_left]

theorem lorentzForm_sum_right {ι : Type*}
    (s : Finset ι) (w : R4) (f : ι → R4) :
    lorentzForm w (∑ i ∈ s, f i) = ∑ i ∈ s, lorentzForm w (f i) := by
  calc
    lorentzForm w (∑ i ∈ s, f i) =
        lorentzForm (∑ i ∈ s, f i) w := lorentzForm_symm w _
    _ = ∑ i ∈ s, lorentzForm (f i) w := lorentzForm_sum_left s f w
    _ = ∑ i ∈ s, lorentzForm w (f i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact lorentzForm_symm (f i) w

theorem lorentzForm_weighted_sum_left {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (f : ι → R4) (w : R4) :
    lorentzForm (∑ i ∈ s, a i • f i) w =
      ∑ i ∈ s, a i * lorentzForm (f i) w := by
  rw [lorentzForm_sum_left]
  apply Finset.sum_congr rfl
  intro i _hi
  exact lorentzForm_smul_left (a i) (f i) w

theorem lorentzForm_weighted_sum_right {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (w : R4) (f : ι → R4) :
    lorentzForm w (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, a i * lorentzForm w (f i) := by
  calc
    lorentzForm w (∑ i ∈ s, a i • f i) =
        lorentzForm (∑ i ∈ s, a i • f i) w := lorentzForm_symm w _
    _ = ∑ i ∈ s, a i * lorentzForm (f i) w :=
        lorentzForm_weighted_sum_left s a f w
    _ = ∑ i ∈ s, a i * lorentzForm w (f i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [lorentzForm_symm (f i) w]

theorem lorentzForm_weighted_sum_sum {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (a : ι → ℝ) (f : ι → R4) (g : κ → R4) :
    lorentzForm (∑ i ∈ s, a i • f i) (∑ j ∈ t, g j) =
      ∑ i ∈ s, ∑ j ∈ t, a i * lorentzForm (f i) (g j) := by
  rw [lorentzForm_weighted_sum_left]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lorentzForm_sum_right]
  rw [Finset.mul_sum]

/-- A finite sum of strictly negative real terms is strictly negative when the
indexing finset is nonempty. -/
theorem Finset.sum_lt_zero_of_nonempty_of_forall_neg {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i < 0) :
    (∑ i ∈ s, f i) < 0 := by
  have hpos :
      0 < ∑ i ∈ s, -f i := by
    exact Finset.sum_pos (fun i hi => neg_pos.mpr (hf i hi)) hs
  have hneg : 0 < -(∑ i ∈ s, f i) := by
    simpa [Finset.sum_neg_distrib] using hpos
  exact neg_pos.mp hneg

theorem Finset.sum_lt_zero_of_nonempty_of_forall_neg₂ {ι κ : Type*}
    {s : Finset ι} {t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → κ → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t, f i j < 0) :
    (∑ i ∈ s, ∑ j ∈ t, f i j) < 0 := by
  refine Finset.sum_lt_zero_of_nonempty_of_forall_neg hs
    (fun i => ∑ j ∈ t, f i j) ?_
  intro i hi
  exact Finset.sum_lt_zero_of_nonempty_of_forall_neg ht
    (fun j => f i j) (hf i hi)

/-- The contradiction in Paulsen's proof once a nontrivial relation has already
been split into positive coefficients on two disjoint nonempty sides, and the
left side has at most two vectors. -/
theorem splitRelation_contradiction
    (v : Fin 5 → R4)
    (hself : ∀ i : Fin 5, lorentzForm (v i) (v i) = 1)
    (hneg : ∀ i j : Fin 5, i ≠ j → lorentzForm (v i) (v j) < 0)
    (hgt_neg_one : ∀ i j : Fin 5, i ≠ j → -1 < lorentzForm (v i) (v j))
    (P N : Finset (Fin 5))
    (hPnonempty : P.Nonempty) (hNnonempty : N.Nonempty)
    (hdisj : Disjoint P N) (hPle : P.card ≤ 2)
    (a b : Fin 5 → ℝ)
    (ha : ∀ i ∈ P, 0 < a i)
    (hb : ∀ j ∈ N, 0 < b j)
    (hrel : ∑ i ∈ P, a i • v i = ∑ j ∈ N, b j • v j) :
    False := by
  classical
  let w : R4 := ∑ i ∈ P, v i
  have hleft_pos :
      0 < lorentzForm (∑ i ∈ P, a i • v i) w := by
    have hPcard_pos : 0 < P.card := Finset.card_pos.mpr hPnonempty
    have hPcard : P.card = 1 ∨ P.card = 2 := by omega
    rcases hPcard with hcard | hcard
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
      subst P
      simp only [Finset.sum_singleton] at *
      have hw : w = v p := by simp [w]
      rw [hw, lorentzForm_smul_left, hself p]
      simpa using ha p (by simp)
    · obtain ⟨p, q, hpq, hP⟩ := Finset.card_eq_two.mp hcard
      subst P
      have hpq' : p ≠ q := hpq
      have hqp' : q ≠ p := Ne.symm hpq
      have hpair_symm : lorentzForm (v q) (v p) = lorentzForm (v p) (v q) :=
        lorentzForm_symm (v q) (v p)
      have hfactor_pos :
          0 < 1 + lorentzForm (v p) (v q) := by
        linarith [hgt_neg_one p q hpq']
      have hcoef_pos : 0 < a p + a q := by
        exact add_pos (ha p (by simp [hpq'])) (ha q (by simp [hqp']))
      have hleft_eq :
          lorentzForm (∑ i ∈ ({p, q} : Finset (Fin 5)), a i • v i) w =
            (a p + a q) * (1 + lorentzForm (v p) (v q)) := by
        have hw : w = v p + v q := by
          simp [w, hpq']
        rw [hw]
        simp [hpq', lorentzForm_add_left, lorentzForm_add_right,
          lorentzForm_smul_left, hself p, hself q, hpair_symm]
        ring
      rw [hleft_eq]
      exact mul_pos hcoef_pos hfactor_pos
  have hright_neg :
      lorentzForm (∑ j ∈ N, b j • v j) w < 0 := by
    unfold w
    rw [lorentzForm_weighted_sum_sum]
    exact Finset.sum_lt_zero_of_nonempty_of_forall_neg₂ hNnonempty hPnonempty
      (fun j i => b j * lorentzForm (v j) (v i)) (by
        intro j hj i hi
        have hji : j ≠ i := by
          intro hji
          subst i
          exact (Finset.disjoint_left.mp hdisj) hi hj
        exact mul_neg_of_pos_of_neg (hb j hj) (hneg j i hji))
  have heq :
      lorentzForm (∑ i ∈ P, a i • v i) w =
        lorentzForm (∑ j ∈ N, b j • v j) w := by
    rw [hrel]
  linarith

/-- Any five vectors in Paulsen's `R^4` are linearly dependent. -/
theorem not_linearIndependent_fin_five_R4 (v : Fin 5 → R4) :
    ¬ LinearIndependent ℝ v := by
  intro hlin
  have hle := hlin.fintype_card_le_finrank
  norm_num [R4, Module.finrank_fin_fun] at hle

/-- A nonzero linear relation among vectors whose first coordinates are all
positive has at least one positive and one negative coefficient.  This is the
formal version of the appendix sentence justifying that both sides of the
split relation are nonempty. -/
theorem relation_has_pos_and_neg_coefficients
    (v : Fin 5 → R4) (hfirst : ∀ i : Fin 5, 0 < v i 0)
    (c : Fin 5 → ℝ)
    (hrel : ∑ i : Fin 5, c i • v i = 0)
    (hnonzero : ∃ i : Fin 5, c i ≠ 0) :
    (∃ i : Fin 5, 0 < c i) ∧ (∃ i : Fin 5, c i < 0) := by
  classical
  have hcoord : ∑ i : Fin 5, c i * v i 0 = 0 := by
    have h := congr_fun hrel 0
    simpa [Finset.sum_apply, Pi.smul_apply] using h
  have hweighted_nonzero : ∃ i : Fin 5, c i * v i 0 ≠ 0 := by
    rcases hnonzero with ⟨i, hi⟩
    refine ⟨i, mul_ne_zero hi ?_⟩
    exact ne_of_gt (hfirst i)
  have hweighted_nonzero_univ :
      ∃ i ∈ (Finset.univ : Finset (Fin 5)), c i * v i 0 ≠ 0 := by
    rcases hweighted_nonzero with ⟨i, hi⟩
    exact ⟨i, by simp, hi⟩
  constructor
  · rcases Finset.exists_pos_of_sum_zero_of_exists_nonzero
      (s := (Finset.univ : Finset (Fin 5)))
      (fun i : Fin 5 => c i * v i 0) hcoord hweighted_nonzero_univ with
      ⟨i, _hi_mem, hi⟩
    refine ⟨i, ?_⟩
    nlinarith [hfirst i]
  · have hcoord_neg : ∑ i : Fin 5, -(c i * v i 0) = 0 := by
      simp [Finset.sum_neg_distrib, hcoord]
    have hweighted_neg_nonzero :
        ∃ i ∈ (Finset.univ : Finset (Fin 5)), -(c i * v i 0) ≠ 0 := by
      rcases hweighted_nonzero with ⟨i, hi⟩
      exact ⟨i, by simp, neg_ne_zero.mpr hi⟩
    rcases Finset.exists_pos_of_sum_zero_of_exists_nonzero
      (s := (Finset.univ : Finset (Fin 5)))
      (fun i : Fin 5 => -(c i * v i 0))
      hcoord_neg hweighted_neg_nonzero with ⟨i, _hi_mem, hi⟩
    refine ⟨i, ?_⟩
    nlinarith [hfirst i]

/-- Split a nonzero relation into positive coefficients on the positive and
negative coefficient supports. -/
theorem relation_split
    (v : Fin 5 → R4) (c : Fin 5 → ℝ)
    (hrel : ∑ i : Fin 5, c i • v i = 0) :
    let P : Finset (Fin 5) := Finset.univ.filter (fun i => 0 < c i)
    let N : Finset (Fin 5) := Finset.univ.filter (fun i => c i < 0)
    Disjoint P N ∧
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j := by
  classical
  intro P N
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    simp [P] at hiP
    simp [N] at hiN
    linarith
  have hterm_zero :
      ∀ i : Fin 5, i ∉ P → i ∉ N → c i = 0 := by
    intro i hiP hiN
    simp [P] at hiP
    simp [N] at hiN
    linarith
  have hsum_union :
      (∑ i : Fin 5, c i • v i) =
        ∑ i ∈ P ∪ N, c i • v i := by
    symm
    refine Finset.sum_subset (Finset.subset_univ (P ∪ N)) ?_
    intro i _hiuniv hi_union
    have hiP : i ∉ P := by
      intro hi
      exact hi_union (Finset.mem_union.mpr (Or.inl hi))
    have hiN : i ∉ N := by
      intro hi
      exact hi_union (Finset.mem_union.mpr (Or.inr hi))
    simp [hterm_zero i hiP hiN]
  have hsumPN :
      (∑ i ∈ P, c i • v i) + (∑ i ∈ N, c i • v i) = 0 := by
    rw [hsum_union, Finset.sum_union hdisj] at hrel
    simpa using hrel
  have hP_eq_negN :
      (∑ i ∈ P, c i • v i) = -(∑ i ∈ N, c i • v i) := by
    simpa [eq_neg_iff_add_eq_zero] using hsumPN
  refine ⟨hdisj, ?_⟩
  rw [hP_eq_negN]
  simp [Finset.sum_neg_distrib]

/-- The abstract five-vector obstruction behind Paulsen's forced-intriguing
pair theorem.  The Euclidean circle computation supplies the hypotheses:
positive first coordinate, diagonal Gram value `1`, and off-diagonal Gram
values in `(-1, 0)`. -/
theorem no_paulsen_gram_five
    (v : Fin 5 → R4)
    (hfirst : ∀ i : Fin 5, 0 < v i 0)
    (hself : ∀ i : Fin 5, lorentzForm (v i) (v i) = 1)
    (hneg : ∀ i j : Fin 5, i ≠ j → lorentzForm (v i) (v j) < 0)
    (hgt_neg_one : ∀ i j : Fin 5, i ≠ j → -1 < lorentzForm (v i) (v j)) :
    False := by
  classical
  obtain ⟨c, hrel, hnonzero⟩ :=
    Fintype.not_linearIndependent_iff.mp (not_linearIndependent_fin_five_R4 v)
  let P : Finset (Fin 5) := Finset.univ.filter (fun i => 0 < c i)
  let N : Finset (Fin 5) := Finset.univ.filter (fun i => c i < 0)
  have hposneg := relation_has_pos_and_neg_coefficients v hfirst c hrel hnonzero
  have hPnonempty : P.Nonempty := by
    rcases hposneg.1 with ⟨i, hi⟩
    exact ⟨i, by simp [P, hi]⟩
  have hNnonempty : N.Nonempty := by
    rcases hposneg.2 with ⟨i, hi⟩
    exact ⟨i, by simp [N, hi]⟩
  have hsplit := relation_split v c hrel
  dsimp only at hsplit
  change
    Disjoint P N ∧
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j at hsplit
  have hdisj : Disjoint P N := hsplit.1
  have hrel_split :
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j :=
    hsplit.2
  have haP : ∀ i ∈ P, 0 < c i := by
    intro i hi
    simpa [P] using hi
  have hbN : ∀ j ∈ N, 0 < -c j := by
    intro j hj
    have : c j < 0 := by simpa [N] using hj
    linarith
  have hcard_union_le : (P ∪ N).card ≤ 5 := by
    simpa using Finset.card_le_univ (P ∪ N)
  have hcard_sum_le : P.card + N.card ≤ 5 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact hcard_union_le
  have hsmall : P.card ≤ 2 ∨ N.card ≤ 2 := by
    by_contra h
    push Not at h
    omega
  rcases hsmall with hPle | hNle
  · exact splitRelation_contradiction v hself hneg hgt_neg_one
      P N hPnonempty hNnonempty hdisj hPle c (fun j => -c j)
      haP hbN hrel_split
  · have hrel_split_symm :
        (∑ j ∈ N, (-c j) • v j) = ∑ i ∈ P, c i • v i :=
      hrel_split.symm
    exact splitRelation_contradiction v hself hneg hgt_neg_one
      N P hNnonempty hPnonempty hdisj.symm hNle
      (fun j => -c j) c hbN haP hrel_split_symm

universe u

/-- Data supplied by the Euclidean circle calculation for one five-element
subset.  If all five indexed objects were non-intriguing, these vectors would
satisfy Paulsen's impossible Gram conditions. -/
structure FiveSetPaulsenData {V : Type u} (intriguing : V → V → Prop)
    (t : Finset V) where
  enumerate : Fin 5 ≃ {x : V // x ∈ t}
  vec : Fin 5 → R4
  first_pos : ∀ i : Fin 5, 0 < vec i 0
  self_gram : ∀ i : Fin 5, lorentzForm (vec i) (vec i) = 1
  nonintriguing_gram_neg :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        lorentzForm (vec i) (vec j) < 0
  nonintriguing_gram_gt_neg_one :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        -1 < lorentzForm (vec i) (vec j)

/-- Circle-coordinate data for one five-element subset, in exactly the
distance-inequality form used by Paulsen's appendix. -/
structure FiveSetPaulsenCircleData {V : Type u} (intriguing : V → V → Prop)
    (t : Finset V) where
  enumerate : Fin 5 ≃ {x : V // x ∈ t}
  center : Fin 5 → R2
  radius : Fin 5 → ℝ
  radius_pos : ∀ i : Fin 5, 0 < radius i
  nonintriguing_dist_low :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        radius i ^ 2 + radius j ^ 2 < distSq2 (center i) (center j)
  nonintriguing_dist_high :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        distSq2 (center i) (center j) < (radius i + radius j) ^ 2

namespace FiveSetPaulsenData

/-- Build Paulsen five-set data from the circle-coordinate calculation in the
appendix.  The two distance inequalities are exactly
`r_i^2 + r_j^2 < |x_i - x_j|^2 < (r_i + r_j)^2` for non-intriguing pairs. -/
noncomputable def ofCircleCoordinates
    {V : Type u} {intriguing : V → V → Prop} {t : Finset V}
    (enumerate : Fin 5 ≃ {x : V // x ∈ t})
    (center : Fin 5 → R2) (radius : Fin 5 → ℝ)
    (radius_pos : ∀ i : Fin 5, 0 < radius i)
    (nonintriguing_dist_low :
      ∀ i j : Fin 5, i ≠ j →
        ¬ intriguing (enumerate i) (enumerate j) →
          radius i ^ 2 + radius j ^ 2 < distSq2 (center i) (center j))
    (nonintriguing_dist_high :
      ∀ i j : Fin 5, i ≠ j →
        ¬ intriguing (enumerate i) (enumerate j) →
          distSq2 (center i) (center j) < (radius i + radius j) ^ 2) :
    FiveSetPaulsenData intriguing t where
  enumerate := enumerate
  vec := fun i => circleVec (radius i) (center i)
  first_pos := by
    intro i
    exact circleVec_first_pos (radius_pos i) (center i)
  self_gram := by
    intro i
    exact lorentzForm_circleVec_self (center i) (ne_of_gt (radius_pos i))
  nonintriguing_gram_neg := by
    intro i j hij hnon
    exact lorentzForm_circleVec_pair_neg (center i) (center j)
      (radius_pos i) (radius_pos j)
      (nonintriguing_dist_low i j hij hnon)
  nonintriguing_gram_gt_neg_one := by
    intro i j hij hnon
    exact lorentzForm_circleVec_pair_gt_neg_one (center i) (center j)
      (radius_pos i) (radius_pos j)
      (nonintriguing_dist_high i j hij hnon)

end FiveSetPaulsenData

namespace FiveSetPaulsenCircleData

/-- Convert circle-coordinate five-set data to Paulsen vector data. -/
noncomputable def toFiveSetPaulsenData
    {V : Type u} {intriguing : V → V → Prop} {t : Finset V}
    (D : FiveSetPaulsenCircleData intriguing t) :
    FiveSetPaulsenData intriguing t :=
  FiveSetPaulsenData.ofCircleCoordinates
    D.enumerate D.center D.radius D.radius_pos
    D.nonintriguing_dist_low D.nonintriguing_dist_high

end FiveSetPaulsenCircleData

/-- Paulsen vector data on every five-element subset proves the manuscript's
forbidden-pair fact: every five contain an intriguing pair. -/
theorem intriguing_pair_in_every_five_of_paulsen_data
    {V : Type u} [DecidableEq V]
    (intriguing : V → V → Prop)
    (hdata : ∀ t : Finset V, t.card = 5 →
      FiveSetPaulsenData intriguing t) :
    ∀ t : Finset V, t.card = 5 →
      ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ intriguing x y := by
  classical
  intro t ht
  by_contra hnone
  have hnot_intr :
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ intriguing x y := by
    intro x hx y hy hxy hxy_intr
    exact hnone ⟨x, hx, y, hy, hxy, hxy_intr⟩
  let D := hdata t ht
  have hneg :
      ∀ i j : Fin 5, i ≠ j → lorentzForm (D.vec i) (D.vec j) < 0 := by
    intro i j hij
    refine D.nonintriguing_gram_neg i j hij ?_
    have hne_val : (D.enumerate i : V) ≠ D.enumerate j := by
      intro hval
      exact hij (D.enumerate.injective (Subtype.ext hval))
    exact hnot_intr (D.enumerate i) (D.enumerate i).property
      (D.enumerate j) (D.enumerate j).property hne_val
  have hgt :
      ∀ i j : Fin 5, i ≠ j → -1 < lorentzForm (D.vec i) (D.vec j) := by
    intro i j hij
    refine D.nonintriguing_gram_gt_neg_one i j hij ?_
    have hne_val : (D.enumerate i : V) ≠ D.enumerate j := by
      intro hval
      exact hij (D.enumerate.injective (Subtype.ext hval))
    exact hnot_intr (D.enumerate i) (D.enumerate i).property
      (D.enumerate j) (D.enumerate j).property hne_val
  exact no_paulsen_gram_five D.vec D.first_pos D.self_gram hneg hgt

end PaulsenLinearAlgebra
end TheoremOneEndToEnd
end Lollipop
