import Lollipop.Internal.Formula
import Mathlib.Tactic

/-!
Bridge between the manuscript's sorted four-cluster definition of `S(n)` and
the internal labeled finite extremum `concreteS`.

The internal development optimizes over all labeled quadruples with the
penalized pair in positions `0,1`.  The manuscript instead optimizes over
sorted quadruples `a <= b <= c <= d`, where the penalized pair is the two
smallest clusters.  This file proves that the two finite extrema are equal.
-/

namespace Lollipop
namespace TheoremOneManuscript

open BigOperators

/-- A four-tuple of natural cluster sizes used by the sorting bridge. -/
structure FourNat where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
deriving DecidableEq

namespace FourNat

/-- Sum of a four-tuple. -/
def sum (q : FourNat) : Nat :=
  q.x0 + q.x1 + q.x2 + q.x3

/-- Sum of squares of a four-tuple. -/
def sqSum (q : FourNat) : Nat :=
  q.x0^2 + q.x1^2 + q.x2^2 + q.x3^2

/-- The six pair products, minimized. -/
def minPairProduct (q : FourNat) : Nat :=
  min (q.x0 * q.x1)
    (min (q.x0 * q.x2)
      (min (q.x0 * q.x3)
        (min (q.x1 * q.x2)
          (min (q.x1 * q.x3) (q.x2 * q.x3)))))

def swap01 (q : FourNat) : FourNat where
  x0 := min q.x0 q.x1
  x1 := max q.x0 q.x1
  x2 := q.x2
  x3 := q.x3

def swap23 (q : FourNat) : FourNat where
  x0 := q.x0
  x1 := q.x1
  x2 := min q.x2 q.x3
  x3 := max q.x2 q.x3

def swap02 (q : FourNat) : FourNat where
  x0 := min q.x0 q.x2
  x1 := q.x1
  x2 := max q.x0 q.x2
  x3 := q.x3

def swap13 (q : FourNat) : FourNat where
  x0 := q.x0
  x1 := min q.x1 q.x3
  x2 := q.x2
  x3 := max q.x1 q.x3

def swap12 (q : FourNat) : FourNat where
  x0 := q.x0
  x1 := min q.x1 q.x2
  x2 := max q.x1 q.x2
  x3 := q.x3

/-- A five-comparator sorting network for four natural numbers. -/
def sort4 (q : FourNat) : FourNat :=
  q.swap01.swap23.swap02.swap13.swap12

theorem min_sq_add_max_sq (a b : Nat) :
    (min a b)^2 + (max a b)^2 = a^2 + b^2 := by
  rcases le_total a b with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right h, max_eq_left h, Nat.add_comm]

@[simp] theorem sum_swap01 (q : FourNat) : sum q.swap01 = sum q := by
  simp [sum, swap01, min_add_max]

@[simp] theorem sum_swap23 (q : FourNat) : sum q.swap23 = sum q := by
  unfold sum swap23
  simp
  have h := min_add_max q.x2 q.x3
  omega

@[simp] theorem sum_swap02 (q : FourNat) : sum q.swap02 = sum q := by
  unfold sum swap02
  simp
  have h := min_add_max q.x0 q.x2
  omega

@[simp] theorem sum_swap13 (q : FourNat) : sum q.swap13 = sum q := by
  unfold sum swap13
  simp
  have h := min_add_max q.x1 q.x3
  omega

@[simp] theorem sum_swap12 (q : FourNat) : sum q.swap12 = sum q := by
  unfold sum swap12
  simp
  have h := min_add_max q.x1 q.x2
  omega

@[simp] theorem sqSum_swap01 (q : FourNat) : sqSum q.swap01 = sqSum q := by
  simp [sqSum, swap01, min_sq_add_max_sq]

@[simp] theorem sqSum_swap23 (q : FourNat) : sqSum q.swap23 = sqSum q := by
  unfold sqSum swap23
  simp
  have h := min_sq_add_max_sq q.x2 q.x3
  omega

@[simp] theorem sqSum_swap02 (q : FourNat) : sqSum q.swap02 = sqSum q := by
  unfold sqSum swap02
  simp
  have h := min_sq_add_max_sq q.x0 q.x2
  omega

@[simp] theorem sqSum_swap13 (q : FourNat) : sqSum q.swap13 = sqSum q := by
  unfold sqSum swap13
  simp
  have h := min_sq_add_max_sq q.x1 q.x3
  omega

@[simp] theorem sqSum_swap12 (q : FourNat) : sqSum q.swap12 = sqSum q := by
  unfold sqSum swap12
  simp
  have h := min_sq_add_max_sq q.x1 q.x2
  omega

@[simp] theorem minPairProduct_swap01 (q : FourNat) :
    minPairProduct q.swap01 = minPairProduct q := by
  rcases le_total q.x0 q.x1 with h | h
  · simp only [minPairProduct, swap01, min_eq_left h, max_eq_right h]
  · simp only [minPairProduct, swap01, min_eq_right h, max_eq_left h]
    ac_rfl

@[simp] theorem minPairProduct_swap23 (q : FourNat) :
    minPairProduct q.swap23 = minPairProduct q := by
  rcases le_total q.x2 q.x3 with h | h
  · simp only [minPairProduct, swap23, min_eq_left h, max_eq_right h]
  · simp only [minPairProduct, swap23, min_eq_right h, max_eq_left h]
    ac_rfl

@[simp] theorem minPairProduct_swap02 (q : FourNat) :
    minPairProduct q.swap02 = minPairProduct q := by
  rcases le_total q.x0 q.x2 with h | h
  · simp only [minPairProduct, swap02, min_eq_left h, max_eq_right h]
  · simp only [minPairProduct, swap02, min_eq_right h, max_eq_left h]
    ac_rfl

@[simp] theorem minPairProduct_swap13 (q : FourNat) :
    minPairProduct q.swap13 = minPairProduct q := by
  rcases le_total q.x1 q.x3 with h | h
  · simp only [minPairProduct, swap13, min_eq_left h, max_eq_right h]
  · simp only [minPairProduct, swap13, min_eq_right h, max_eq_left h]
    ac_rfl

@[simp] theorem minPairProduct_swap12 (q : FourNat) :
    minPairProduct q.swap12 = minPairProduct q := by
  rcases le_total q.x1 q.x2 with h | h
  · simp only [minPairProduct, swap12, min_eq_left h, max_eq_right h]
  · simp only [minPairProduct, swap12, min_eq_right h, max_eq_left h]
    ac_rfl

theorem sort4_sum (q : FourNat) : q.sort4.sum = q.sum := by
  simp [sort4]

theorem sort4_sqSum (q : FourNat) : q.sort4.sqSum = q.sqSum := by
  simp [sort4]

theorem sort4_minPairProduct (q : FourNat) :
    q.sort4.minPairProduct = q.minPairProduct := by
  simp [sort4]

theorem sort4_sorted (q : FourNat) :
    q.sort4.x0 ≤ q.sort4.x1 ∧
      q.sort4.x1 ≤ q.sort4.x2 ∧
      q.sort4.x2 ≤ q.sort4.x3 := by
  let q1 := q.swap01
  let q2 := q1.swap23
  let q3 := q2.swap02
  let q4 := q3.swap13
  let q5 := q4.swap12
  change q5.x0 ≤ q5.x1 ∧ q5.x1 ≤ q5.x2 ∧ q5.x2 ≤ q5.x3
  have h1 : q1.x0 ≤ q1.x1 := by simp [q1, swap01]
  have h2a : q2.x0 ≤ q2.x1 := by simpa [q2, swap23] using h1
  have h2b : q2.x2 ≤ q2.x3 := by simp [q2, swap23]
  have h3a : q3.x0 ≤ q3.x1 := by
    have h : q3.x0 ≤ q2.x0 := by simp [q3, swap02]
    exact le_trans h h2a
  have h3b : q3.x0 ≤ q3.x2 := by simp [q3, swap02]
  have h3c : q3.x0 ≤ q3.x3 := by
    have h : q3.x0 ≤ q2.x2 := by simp [q3, swap02]
    exact le_trans h h2b
  have h4a : q4.x0 ≤ q4.x1 := by
    apply le_min
    · simpa [q4, swap13] using h3a
    · simpa [q4, swap13] using h3c
  have h4b : q4.x0 ≤ q4.x2 := by simpa [q4, swap13] using h3b
  have h4c : q4.x1 ≤ q4.x3 := by simp [q4, swap13]
  have h4d : q4.x2 ≤ q4.x3 := by
    have hx0 : q2.x0 ≤ max q2.x1 q2.x3 :=
      le_trans h2a (le_max_left _ _)
    have hx2 : q2.x2 ≤ max q2.x1 q2.x3 :=
      le_trans h2b (le_max_right _ _)
    have hmax : max q2.x0 q2.x2 ≤ max q2.x1 q2.x3 :=
      max_le hx0 hx2
    simpa [q4, q3, swap13, swap02] using hmax
  constructor
  · exact le_min h4a h4b
  constructor
  · simp [q5, swap12]
  · exact max_le h4c h4d

theorem first_product_le_pair_products_of_sorted
    {q : FourNat}
    (h01 : q.x0 ≤ q.x1) (h12 : q.x1 ≤ q.x2) (h23 : q.x2 ≤ q.x3) :
    q.x0 * q.x1 ≤ q.x0 * q.x2 ∧
      q.x0 * q.x1 ≤ q.x0 * q.x3 ∧
      q.x0 * q.x1 ≤ q.x1 * q.x2 ∧
      q.x0 * q.x1 ≤ q.x1 * q.x3 ∧
      q.x0 * q.x1 ≤ q.x2 * q.x3 := by
  have h02 : q.x0 ≤ q.x2 := le_trans h01 h12
  have h03 : q.x0 ≤ q.x3 := le_trans h02 h23
  have h13 : q.x1 ≤ q.x3 := le_trans h12 h23
  constructor
  · exact Nat.mul_le_mul_left q.x0 h12
  constructor
  · exact Nat.mul_le_mul_left q.x0 h13
  constructor
  · calc
      q.x0 * q.x1 ≤ q.x2 * q.x1 := Nat.mul_le_mul_right q.x1 h02
      _ = q.x1 * q.x2 := Nat.mul_comm q.x2 q.x1
  constructor
  · calc
      q.x0 * q.x1 ≤ q.x3 * q.x1 := Nat.mul_le_mul_right q.x1 h03
      _ = q.x1 * q.x3 := Nat.mul_comm q.x3 q.x1
  · exact Nat.mul_le_mul h02 h13

theorem minPairProduct_eq_first_of_sorted
    {q : FourNat}
    (h01 : q.x0 ≤ q.x1) (h12 : q.x1 ≤ q.x2) (h23 : q.x2 ≤ q.x3) :
    q.minPairProduct = q.x0 * q.x1 := by
  rcases first_product_le_pair_products_of_sorted h01 h12 h23 with
    ⟨h02, h03, h12p, h13, h23p⟩
  unfold minPairProduct
  exact min_eq_left
    (le_min h02 (le_min h03 (le_min h12p (le_min h13 h23p))))

theorem minPairProduct_le_first (q : FourNat) :
    q.minPairProduct ≤ q.x0 * q.x1 := by
  unfold minPairProduct
  exact min_le_left _ _

theorem sort4_penalty_le_original_penalty (q : FourNat) :
    q.sort4.x0 * q.sort4.x1 ≤ q.x0 * q.x1 := by
  rcases sort4_sorted q with ⟨h01, h12, h23⟩
  calc
    q.sort4.x0 * q.sort4.x1 = q.sort4.minPairProduct :=
      (minPairProduct_eq_first_of_sorted h01 h12 h23).symm
    _ = q.minPairProduct := sort4_minPairProduct q
    _ ≤ q.x0 * q.x1 := minPairProduct_le_first q

theorem x0_le_sum (q : FourNat) : q.x0 ≤ q.sum := by
  unfold sum
  omega

theorem x1_le_sum (q : FourNat) : q.x1 ≤ q.sum := by
  unfold sum
  omega

theorem x2_le_sum (q : FourNat) : q.x2 ≤ q.sum := by
  unfold sum
  omega

theorem x3_le_sum (q : FourNat) : q.x3 ≤ q.sum := by
  unfold sum
  omega

/-- Turn a bounded Lean quadruple into the natural-number helper type. -/
def ofQuad {n : Nat} (q : QuadVec n) : FourNat where
  x0 := q 0
  x1 := q 1
  x2 := q 2
  x3 := q 3

theorem ofQuad_sum_eq_of_mem {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    (ofQuad q).sum = n := by
  rw [quadVecs, Finset.mem_filter] at hq
  unfold quadVecSum at hq
  simp [Fin.sum_univ_four] at hq
  unfold ofQuad sum
  omega

/-- Turn a natural four-tuple with total `n` back into a bounded Lean
quadruple. -/
def toQuadVec {n : Nat} (q : FourNat) (hsum : q.sum = n) : QuadVec n :=
  fun i =>
    if i = (0 : Fin 4) then
      ⟨q.x0, Nat.lt_succ_of_le (by rw [← hsum]; exact x0_le_sum q)⟩
    else if i = (1 : Fin 4) then
      ⟨q.x1, Nat.lt_succ_of_le (by rw [← hsum]; exact x1_le_sum q)⟩
    else if i = (2 : Fin 4) then
      ⟨q.x2, Nat.lt_succ_of_le (by rw [← hsum]; exact x2_le_sum q)⟩
    else
      ⟨q.x3, Nat.lt_succ_of_le (by rw [← hsum]; exact x3_le_sum q)⟩

@[simp] theorem toQuadVec_zero {n : Nat} (q : FourNat) (hsum : q.sum = n) :
    ((toQuadVec q hsum 0 : Fin (n + 1)) : Nat) = q.x0 := by
  simp [toQuadVec]

@[simp] theorem toQuadVec_one {n : Nat} (q : FourNat) (hsum : q.sum = n) :
    ((toQuadVec q hsum 1 : Fin (n + 1)) : Nat) = q.x1 := by
  simp [toQuadVec]

@[simp] theorem toQuadVec_two {n : Nat} (q : FourNat) (hsum : q.sum = n) :
    ((toQuadVec q hsum 2 : Fin (n + 1)) : Nat) = q.x2 := by
  simp [toQuadVec]

@[simp] theorem toQuadVec_three {n : Nat} (q : FourNat) (hsum : q.sum = n) :
    ((toQuadVec q hsum 3 : Fin (n + 1)) : Nat) = q.x3 := by
  simp [toQuadVec]

theorem toQuadVec_mem {n : Nat} (q : FourNat) (hsum : q.sum = n) :
    toQuadVec q hsum ∈ quadVecs n := by
  rw [quadVecs, Finset.mem_filter]
  constructor
  · simp
  · unfold quadVecSum
    have hnat : q.x0 + q.x1 + q.x2 + q.x3 = n := by
      simpa [sum] using hsum
    simp [Fin.sum_univ_four, toQuadVec]
    omega

end FourNat

/-- Sorted bounded quadruples, matching the manuscript condition
`0 <= a <= b <= c <= d`.  Nonnegativity is automatic for natural entries. -/
def quadVecSorted {n : Nat} (q : QuadVec n) : Prop :=
  (q 0 : Nat) ≤ (q 1 : Nat) ∧
    (q 1 : Nat) ≤ (q 2 : Nat) ∧
    (q 2 : Nat) ≤ (q 3 : Nat)

instance quadVecSorted_decidable {n : Nat} :
    DecidablePred (quadVecSorted (n := n)) := by
  intro q
  unfold quadVecSorted
  infer_instance

/-- The manuscript's sorted finite search space. -/
def sortedQuadVecs (n : Nat) : Finset (QuadVec n) :=
  (quadVecs n).filter (fun q => quadVecSorted q)

theorem endpointQuad_sorted (n : Nat) : quadVecSorted (endpointQuad n) := by
  simp [quadVecSorted, endpointQuad]

theorem sortedQuadVecs_nonempty (n : Nat) : (sortedQuadVecs n).Nonempty := by
  refine ⟨endpointQuad n, ?_⟩
  simp [sortedQuadVecs, quadVecs, quadVecSum, endpointQuad, quadVecSorted,
    Fin.sum_univ_four]

/-- The manuscript's `S(n)`: maximum over sorted nonnegative quadruples. -/
def manuscriptS (n : Nat) : Rat :=
  (sortedQuadVecs n).sup' (sortedQuadVecs_nonempty n) quadVecExcess

/-- Sort/relabel a bounded quadruple so the penalized pair is the two
smallest entries. -/
def sortedRelabel {n : Nat} (q : QuadVec n) (hq : q ∈ quadVecs n) :
    QuadVec n :=
  let r := (FourNat.ofQuad q).sort4
  FourNat.toQuadVec r (by
    rw [FourNat.sort4_sum, FourNat.ofQuad_sum_eq_of_mem hq])

theorem sortedRelabel_in_quadVecs {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    sortedRelabel q hq ∈ quadVecs n := by
  unfold sortedRelabel
  exact FourNat.toQuadVec_mem _ _

theorem sortedRelabel_sorted {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    quadVecSorted (sortedRelabel q hq) := by
  have hs := FourNat.sort4_sorted (FourNat.ofQuad q)
  simpa [quadVecSorted, sortedRelabel] using hs

theorem sortedRelabel_mem_sortedQuadVecs {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    sortedRelabel q hq ∈ sortedQuadVecs n := by
  rw [sortedQuadVecs, Finset.mem_filter]
  exact ⟨sortedRelabel_in_quadVecs hq, sortedRelabel_sorted hq⟩

theorem quadVecCost_sortedRelabel_le {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    quadVecCost (sortedRelabel q hq) ≤ quadVecCost q := by
  let r0 := FourNat.ofQuad q
  let r := r0.sort4
  have hsq_nat : r.sqSum = r0.sqSum := by
    simpa [r, r0] using FourNat.sort4_sqSum r0
  have hpen_nat : r.x0 * r.x1 ≤ r0.x0 * r0.x1 := by
    simpa [r, r0] using FourNat.sort4_penalty_le_original_penalty r0
  have hsq_rat :
      (r.x0 : Rat)^2 + (r.x1 : Rat)^2 + (r.x2 : Rat)^2 + (r.x3 : Rat)^2 =
        (r0.x0 : Rat)^2 + (r0.x1 : Rat)^2 + (r0.x2 : Rat)^2 + (r0.x3 : Rat)^2 := by
    exact_mod_cast hsq_nat
  have hpen_rat : (r.x0 : Rat) * (r.x1 : Rat) ≤ (r0.x0 : Rat) * (r0.x1 : Rat) := by
    exact_mod_cast hpen_nat
  have hsq_rat_expanded :
      ((FourNat.ofQuad q).sort4.x0 : Rat)^2 +
          ((FourNat.ofQuad q).sort4.x1 : Rat)^2 +
          ((FourNat.ofQuad q).sort4.x2 : Rat)^2 +
          ((FourNat.ofQuad q).sort4.x3 : Rat)^2 =
        (((q 0 : Fin (n + 1)) : Nat) : Rat)^2 +
          (((q 1 : Fin (n + 1)) : Nat) : Rat)^2 +
          (((q 2 : Fin (n + 1)) : Nat) : Rat)^2 +
          (((q 3 : Fin (n + 1)) : Nat) : Rat)^2 := by
    simpa [r, r0, FourNat.ofQuad] using hsq_rat
  have hpen_rat_expanded :
      ((FourNat.ofQuad q).sort4.x0 : Rat) *
          ((FourNat.ofQuad q).sort4.x1 : Rat) ≤
        (((q 0 : Fin (n + 1)) : Nat) : Rat) *
          (((q 1 : Fin (n + 1)) : Nat) : Rat) := by
    simpa [r, r0, FourNat.ofQuad] using hpen_rat
  simp [quadVecCost, quadCost, quadEntry, sortedRelabel, FourNat.ofQuad,
    FourNat.toQuadVec]
  change
    (3 / 2 : Rat) *
        (((FourNat.ofQuad q).sort4.x0 : Rat)^2 +
          ((FourNat.ofQuad q).sort4.x1 : Rat)^2 +
          ((FourNat.ofQuad q).sort4.x2 : Rat)^2 +
          ((FourNat.ofQuad q).sort4.x3 : Rat)^2) +
        2 * ((FourNat.ofQuad q).sort4.x0 : Rat) *
          ((FourNat.ofQuad q).sort4.x1 : Rat) ≤
      (3 / 2 : Rat) *
        ((((q 0 : Fin (n + 1)) : Nat) : Rat)^2 +
          (((q 1 : Fin (n + 1)) : Nat) : Rat)^2 +
          (((q 2 : Fin (n + 1)) : Nat) : Rat)^2 +
          (((q 3 : Fin (n + 1)) : Nat) : Rat)^2) +
        2 * (((q 0 : Fin (n + 1)) : Nat) : Rat) *
          (((q 1 : Fin (n + 1)) : Nat) : Rat)
  nlinarith [hsq_rat_expanded, hpen_rat_expanded]

theorem quadVecExcess_le_sortedRelabel {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    quadVecExcess q ≤ quadVecExcess (sortedRelabel q hq) := by
  have hqsorted : sortedRelabel q hq ∈ quadVecs n :=
    sortedRelabel_in_quadVecs hq
  have hcost := quadVecCost_sortedRelabel_le hq
  rw [quadVecExcess_eq_const_sub_cost hq,
    quadVecExcess_eq_const_sub_cost hqsorted]
  linarith

theorem exists_sortedRelabel_ge {n : Nat} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    ∃ q' : QuadVec n,
      q' ∈ sortedQuadVecs n ∧ quadVecExcess q ≤ quadVecExcess q' := by
  refine ⟨sortedRelabel q hq, sortedRelabel_mem_sortedQuadVecs hq, ?_⟩
  exact quadVecExcess_le_sortedRelabel hq

theorem manuscriptS_le_concreteS (n : Nat) :
    manuscriptS n ≤ concreteS n := by
  unfold manuscriptS concreteS
  apply Finset.sup'_le
  intro q hq
  rw [sortedQuadVecs, Finset.mem_filter] at hq
  exact Finset.le_sup' (s := quadVecs n) (f := quadVecExcess) hq.1

theorem concreteS_le_manuscriptS (n : Nat) :
    concreteS n ≤ manuscriptS n := by
  unfold manuscriptS concreteS
  apply Finset.sup'_le
  intro q hq
  rcases exists_sortedRelabel_ge hq with ⟨q', hq', hle⟩
  exact le_trans hle
    (Finset.le_sup' (s := sortedQuadVecs n) (f := quadVecExcess) hq')

/-- The internal labeled extremum equals the manuscript's sorted `S(n)`. -/
theorem concreteS_eq_manuscriptS (n : Nat) :
    concreteS n = manuscriptS n := by
  exact le_antisymm (concreteS_le_manuscriptS n) (manuscriptS_le_concreteS n)

theorem manuscriptS_eq_concreteS (n : Nat) :
    manuscriptS n = concreteS n := by
  exact (concreteS_eq_manuscriptS n).symm

end TheoremOneManuscript
end Lollipop
