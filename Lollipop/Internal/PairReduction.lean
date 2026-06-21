import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Tactic

/-!
Checked finite-sum algebra for the two-graph crossing reduction.

The geometric content is still external: for each unordered pair of lollipops,
geometry supplies the pointwise crossing estimate.  This module verifies the
finite summation step from those pointwise estimates to the total crossing
bound.
-/

namespace Lollipop

open BigOperators

/-- Ordered representation of unordered pairs `{i,j}` with `i < j`. -/
def pairFinset (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)

/-- The pair finset is the increasing half of the off-diagonal. -/
theorem pairFinset_eq_univ_offDiag_filter_lt (n : ℕ) :
    pairFinset n =
      (Finset.univ : Finset (Fin n)).offDiag.filter (fun p => p.1 < p.2) := by
  ext p
  simp [pairFinset, Finset.mem_offDiag]
  exact fun h => ne_of_lt h

/-- The ordered representation `i < j` has the expected number of unordered
pairs. -/
theorem pairFinset_card (n : ℕ) :
    (pairFinset n).card = n.choose 2 := by
  rw [pairFinset_eq_univ_offDiag_filter_lt]
  let s : Finset (Fin n) := Finset.univ
  change (s.offDiag.filter fun p : Fin n × Fin n => p.1 < p.2).card = n.choose 2
  have hsum := Finset.sum_sym2_filter_not_isDiag (s := s) (p := fun _ => (1 : ℕ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hsumNat :
      (s.sym2.filter fun a : Sym2 (Fin n) => ¬a.IsDiag).card =
        (s.offDiag.filter fun p : Fin n × Fin n => p.1 < p.2).card := by
    exact_mod_cast hsum
  rw [← hsumNat]
  have hs : s.sym2 = Finset.univ := by simp [s]
  rw [hs]
  rw [← Fintype.card_subtype (fun a : Sym2 (Fin n) => ¬a.IsDiag)]
  simpa using (Sym2.card_subtype_not_diag (α := Fin n))

/-- Sum a two-variable quantity over unordered pairs represented by `i < j`. -/
def pairSum (n : ℕ) (f : Fin n → Fin n → ℚ) : ℚ :=
  ∑ p ∈ pairFinset n, f p.1 p.2

/-- Four colors used by the two-graph reduction. -/
inductive PairColor where
  | zero
  | A
  | B
  | X
  deriving DecidableEq

/-- Objective weight of a colored pair. -/
def PairColor.weight : PairColor → ℚ
  | .zero => 0
  | .A => 1
  | .B => 1
  | .X => 3

/-- The color determined by membership in the two bad-pair graphs `D` and
`E`.  Here `A` is `E`-only, `B` is `D`-only, and `X` is `D ∩ E`. -/
def colorOfMembership (inD inE : Bool) : PairColor :=
  match inD, inE with
  | false, false => .zero
  | false, true => .A
  | true, false => .B
  | true, true => .X

/-- The color weight is exactly
`1_D + 1_E + 1_{D ∩ E}`. -/
theorem color_weight_eq_indicators (inD inE : Bool) :
    (colorOfMembership inD inE).weight =
      (if inD then (1 : ℚ) else 0) +
      (if inE then (1 : ℚ) else 0) +
      (if inD && inE then (1 : ℚ) else 0) := by
  cases inD <;> cases inE <;> norm_num [colorOfMembership, PairColor.weight]

/-- Summing pointwise pair estimates gives the total two-graph crossing
reduction. -/
theorem pairSum_crossing_le_base_plus_score
    {n : ℕ} (cross score : Fin n → Fin n → ℚ)
    (hpoint : ∀ i j : Fin n, i < j → cross i j ≤ 4 + score i j) :
    pairSum n cross ≤
      4 * ((pairFinset n).card : ℚ) + pairSum n score := by
  unfold pairSum
  calc
    (∑ p ∈ pairFinset n, cross p.1 p.2)
        ≤ ∑ p ∈ pairFinset n, (4 + score p.1 p.2) := by
          apply Finset.sum_le_sum
          intro p hp
          rw [pairFinset, Finset.mem_filter] at hp
          exact hpoint p.1 p.2 hp.2
    _ = 4 * ((pairFinset n).card : ℚ) + ∑ p ∈ pairFinset n, score p.1 p.2 := by
          simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Summed crossing reduction in the manuscript's `4 * binom(n,2)` form. -/
theorem pairSum_crossing_le_choose_plus_score
    {n : ℕ} (cross score : Fin n → Fin n → ℚ)
    (hpoint : ∀ i j : Fin n, i < j → cross i j ≤ 4 + score i j) :
    pairSum n cross ≤
      4 * ((n.choose 2 : ℕ) : ℚ) + pairSum n score := by
  simpa [pairFinset_card n] using
    pairSum_crossing_le_base_plus_score cross score hpoint

/-- Region-count algebra after the crossing bound has been established. -/
theorem regions_le_from_crossing_le
    {regions crossings n sigma : ℚ}
    (hcross : crossings ≤ 4 * (n * (n - 1) / 2) + sigma)
    (hregions : regions = crossings + n + 1) :
    regions ≤ 4 * (n * (n - 1) / 2) + sigma + n + 1 := by
  rw [hregions]
  linarith

end Lollipop
