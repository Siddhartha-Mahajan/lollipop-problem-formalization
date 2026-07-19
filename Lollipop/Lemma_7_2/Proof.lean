import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
Proof component 1: `Algebra`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Algebraic identities used in the lollipop formula paper.

This file records the exact quadratic quantities appearing in the blocker
and matrix steps.
-/

namespace Lollipop

open BigOperators

/-- The four-cluster quadratic cost `M`: this is the term subtracted from
`(3/2)n^2` in the colored Turan bound. -/
def quadCost (a b c d : ℚ) : ℚ :=
  (3 / 2 : ℚ) * (a^2 + b^2 + c^2 + d^2) + 2 * a * b

/-- The four-cluster excess contribution `S` for labeled clusters, with the
penalized pair labeled `(a,b)`. -/
def clusterExcess (a b c d : ℚ) : ℚ :=
  3 * (a*b + a*c + a*d + b*c + b*d + c*d) - 2 * a*b

/-- The elementary identity connecting the two forms of the four-cluster
functional. -/
theorem clusterExcess_eq (a b c d : ℚ) :
    clusterExcess a b c d =
      (3 / 2 : ℚ) * (a + b + c + d)^2 - quadCost a b c d := by
  unfold clusterExcess quadCost
  ring

/-- For a fixed four-element multiset, relabelling the penalized pair to a
pair with smaller product can only increase the excess. -/
theorem clusterExcess_le_relabel_penalty
    {a b c d : ℚ} (h : c * d ≤ a * b) :
    clusterExcess a b c d ≤ clusterExcess c d a b := by
  unfold clusterExcess
  nlinarith

/-- In a sorted nonnegative quadruple, the first two entries have minimum pair
product. -/
theorem sorted_first_product_le_pair_products
    {a b c d : ℚ} (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    a * b ≤ a * c ∧
      a * b ≤ a * d ∧
      a * b ≤ b * c ∧
      a * b ≤ b * d ∧
      a * b ≤ c * d := by
  have hb0 : 0 ≤ b := le_trans ha hab
  have hc0 : 0 ≤ c := le_trans hb0 hbc
  constructor
  · exact mul_le_mul_of_nonneg_left hbc ha
  constructor
  · exact mul_le_mul_of_nonneg_left (le_trans hbc hcd) ha
  constructor
  · have h : a * b ≤ c * b :=
      mul_le_mul_of_nonneg_right (le_trans hab hbc) hb0
    nlinarith
  constructor
  · have h : a * b ≤ d * b :=
      mul_le_mul_of_nonneg_right (le_trans (le_trans hab hbc) hcd) hb0
    nlinarith
  · have h1 : a * b ≤ c * b :=
      mul_le_mul_of_nonneg_right (le_trans hab hbc) hb0
    have h2 : c * b ≤ c * d :=
      mul_le_mul_of_nonneg_left (le_trans hbc hcd) hc0
    nlinarith

/-- Finite max/min duality used to pass from the four-cluster maximum `S` to
the quadratic minimum `M`. -/
theorem sup_const_sub_eq_const_sub_inf
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (C : ℚ) (g : ι → ℚ) :
    s.sup' hs (fun x => C - g x) = C - s.inf' hs g := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro x hx
    have hmin : s.inf' hs g ≤ g x := Finset.inf'_le (f := g) hx
    linarith
  · rw [Finset.le_sup'_iff]
    rcases Finset.exists_mem_eq_inf' hs g with ⟨x, hx, hxinf⟩
    refine ⟨x, hx, ?_⟩
    rw [hxinf]

/-- One algebraic step in the blocker argument: a lower bound for the blocker
cost gives an upper bound for the colored objective. -/
theorem sigma_le_from_blocker
    {n Q a b M S sigma : ℚ}
    (hsigma : sigma = (3 / 2 : ℚ) * n^2 - ((3 / 2 : ℚ) * Q + 2*a + 2*b))
    (hblock : (3 / 2 : ℚ) * Q + 2*a + 2*b ≥ M)
    (hS : S = (3 / 2 : ℚ) * n^2 - M) :
    sigma ≤ S := by
  rw [hsigma, hS]
  linarith

/-- Row sums of a `3 x 4` rational matrix. -/
def rowSum (U : Fin 3 → Fin 4 → ℚ) (i : Fin 3) : ℚ :=
  ∑ j : Fin 4, U i j

/-- Column sums of a `3 x 4` rational matrix. -/
def colSum (U : Fin 3 → Fin 4 → ℚ) (j : Fin 4) : ℚ :=
  ∑ i : Fin 3, U i j

/-- Total mass of a `3 x 4` rational matrix. -/
def matrixTotal (U : Fin 3 → Fin 4 → ℚ) : ℚ :=
  ∑ i : Fin 3, ∑ j : Fin 4, U i j

/-- The matrix quadratic form from the paper. -/
def matrixF (U : Fin 3 → Fin 4 → ℚ) : ℚ :=
  (∑ i : Fin 3, (rowSum U i)^2) +
  (∑ j : Fin 4, (colSum U j)^2) -
  (1 / 2 : ℚ) * (∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2)

/-- The value of `matrixF` on the star normal form. -/
theorem matrixF_star
    (a b c d : ℚ) :
    matrixF (fun i : Fin 3 => fun j : Fin 4 =>
      if i = 0 ∧ j = 0 then a else
      if i = 0 ∧ j = 1 then b else
      if i = 1 ∧ j = 2 then c else
      if i = 2 ∧ j = 3 then d else 0)
    = quadCost a b c d := by
  simp [matrixF, rowSum, colSum, quadCost, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

end Lollipop

/-!
Proof component 2: `Formula`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Concrete finite definitions of the manuscript's four-cluster extrema.

The original skeleton treated `M` and `S` as abstract functions.  This module
defines them as finite extrema over bounded integer quadruples summing to `n`
and proves the exact duality

`S(n) = (3/2)n^2 - M(n)`.
-/

namespace Lollipop

open BigOperators

/-- Bounded quadruples used to enumerate all nonnegative integer quadruples
with total `n`. -/
abbrev QuadVec (n : ℕ) := Fin 4 → Fin (n + 1)

/-- Sum of the four entries of a bounded quadruple. -/
def quadVecSum {n : ℕ} (q : QuadVec n) : ℕ :=
  ∑ i : Fin 4, (q i : ℕ)

/-- All bounded quadruples whose entries sum to `n`. -/
def quadVecs (n : ℕ) : Finset (QuadVec n) :=
  Finset.univ.filter (fun q => quadVecSum q = n)

/-- The quadruple `(0,0,0,n)`, used to witness nonemptiness. -/
def endpointQuad (n : ℕ) : QuadVec n :=
  fun i =>
    if i = (3 : Fin 4) then
      ⟨n, Nat.lt_succ_self n⟩
    else
      ⟨0, Nat.succ_pos n⟩

/-- The finite search space is nonempty for every `n`. -/
theorem quadVecs_nonempty (n : ℕ) : (quadVecs n).Nonempty := by
  refine ⟨endpointQuad n, ?_⟩
  simp [quadVecs, quadVecSum, endpointQuad, Fin.sum_univ_four]

/-- Rational coercion of one component of a bounded quadruple. -/
def quadEntry {n : ℕ} (q : QuadVec n) (i : Fin 4) : ℚ :=
  ((q i : ℕ) : ℚ)

/-- Four-cluster quadratic cost on a bounded quadruple. -/
def quadVecCost {n : ℕ} (q : QuadVec n) : ℚ :=
  quadCost (quadEntry q 0) (quadEntry q 1) (quadEntry q 2) (quadEntry q 3)

/-- Four-cluster excess on a bounded quadruple. -/
def quadVecExcess {n : ℕ} (q : QuadVec n) : ℚ :=
  clusterExcess (quadEntry q 0) (quadEntry q 1) (quadEntry q 2) (quadEntry q 3)

/-- The manuscript's `M(n)`, concretely as a finite minimum. -/
def concreteM (n : ℕ) : ℚ :=
  (quadVecs n).inf' (quadVecs_nonempty n) quadVecCost

/-- The manuscript's `S(n)`, concretely as a finite maximum. -/
def concreteS (n : ℕ) : ℚ :=
  (quadVecs n).sup' (quadVecs_nonempty n) quadVecExcess

/-- Membership in `quadVecs n` says that the rational sum of the entries is
`n`. -/
theorem quadEntry_sum_eq_of_mem {n : ℕ} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    quadEntry q 0 + quadEntry q 1 + quadEntry q 2 + quadEntry q 3 = (n : ℚ) := by
  rw [quadVecs, Finset.mem_filter] at hq
  have hsum : quadVecSum q = n := hq.2
  unfold quadVecSum at hsum
  simp [Fin.sum_univ_four] at hsum
  unfold quadEntry
  exact_mod_cast hsum

/-- On every quadruple summing to `n`, the excess is `(3/2)n^2` minus the
quadratic cost. -/
theorem quadVecExcess_eq_const_sub_cost {n : ℕ} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    quadVecExcess q =
      (3 / 2 : ℚ) * (n : ℚ)^2 - quadVecCost q := by
  unfold quadVecExcess quadVecCost
  rw [clusterExcess_eq]
  rw [quadEntry_sum_eq_of_mem hq]

/-- Concrete finite-extremum form of `S(n) = (3/2)n^2 - M(n)`. -/
theorem concreteS_eq_concreteM (n : ℕ) :
    concreteS n = (3 / 2 : ℚ) * (n : ℚ)^2 - concreteM n := by
  unfold concreteS concreteM
  have hcongr :
      (quadVecs n).sup' (quadVecs_nonempty n) quadVecExcess =
        (quadVecs n).sup' (quadVecs_nonempty n)
          (fun q => (3 / 2 : ℚ) * (n : ℚ)^2 - quadVecCost q) := by
    exact Finset.sup'_congr
      (s := quadVecs n) (t := quadVecs n)
      (H := quadVecs_nonempty n)
      (f := quadVecExcess)
      (g := fun q => (3 / 2 : ℚ) * (n : ℚ)^2 - quadVecCost q)
      rfl
      (fun q hq => quadVecExcess_eq_const_sub_cost hq)
  rw [hcongr]
  exact sup_const_sub_eq_const_sub_inf (quadVecs n) (quadVecs_nonempty n)
    ((3 / 2 : ℚ) * (n : ℚ)^2) quadVecCost

/-- The finite minimum is bounded above by every admissible quadruple. -/
theorem concreteM_le_quadVecCost {n : ℕ} {q : QuadVec n}
    (hq : q ∈ quadVecs n) :
    concreteM n ≤ quadVecCost q := by
  unfold concreteM
  exact Finset.inf'_le (f := quadVecCost) hq

/-- A convenient version of `concreteM_le_quadVecCost` for ordinary natural
quadruples. -/
theorem concreteM_le_quadCost_of_sum
    {a b c d n : ℕ} (hsum : a + b + c + d = n) :
    concreteM n ≤
      quadCost (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) := by
  have ha : a ≤ n := by omega
  have hb : b ≤ n := by omega
  have hc : c ≤ n := by omega
  have hd : d ≤ n := by omega
  let q : QuadVec n := fun i =>
    if i = (0 : Fin 4) then
      ⟨a, Nat.lt_succ_of_le ha⟩
    else if i = (1 : Fin 4) then
      ⟨b, Nat.lt_succ_of_le hb⟩
    else if i = (2 : Fin 4) then
      ⟨c, Nat.lt_succ_of_le hc⟩
    else
      ⟨d, Nat.lt_succ_of_le hd⟩
  have hq : q ∈ quadVecs n := by
    simp [quadVecs, quadVecSum, q, Fin.sum_univ_four, hsum]
  have hmin := concreteM_le_quadVecCost hq
  simpa [quadVecCost, quadEntry, q] using hmin

private theorem quadVecCost_ge_three_halves_entry_sum
    {n : ℕ} (q : QuadVec n) :
    (3 / 2 : ℚ) *
        (quadEntry q 0 + quadEntry q 1 + quadEntry q 2 + quadEntry q 3) ≤
      quadVecCost q := by
  have h0 : ((q 0 : ℕ) : ℚ) ≤ ((q 0 : ℕ) : ℚ) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using Nat.le_mul_self (q 0 : ℕ))
  have h1 : ((q 1 : ℕ) : ℚ) ≤ ((q 1 : ℕ) : ℚ) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using Nat.le_mul_self (q 1 : ℕ))
  have h2 : ((q 2 : ℕ) : ℚ) ≤ ((q 2 : ℕ) : ℚ) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using Nat.le_mul_self (q 2 : ℕ))
  have h3 : ((q 3 : ℕ) : ℚ) ≤ ((q 3 : ℕ) : ℚ) ^ 2 := by
    exact_mod_cast (by simpa [pow_two] using Nat.le_mul_self (q 3 : ℕ))
  have hab : 0 ≤ 2 * ((q 0 : ℕ) : ℚ) * ((q 1 : ℕ) : ℚ) := by
    positivity
  unfold quadVecCost quadEntry quadCost
  nlinarith

private theorem three_halves_mul_le_concreteM (n : ℕ) :
    (3 / 2 : ℚ) * (n : ℚ) ≤ concreteM n := by
  unfold concreteM
  refine Finset.le_inf' (quadVecs_nonempty n) quadVecCost ?_
  intro q hq
  have hsum := quadEntry_sum_eq_of_mem hq
  have hcost := quadVecCost_ge_three_halves_entry_sum q
  rwa [hsum] at hcost

/-- The first small value of `M`. -/
theorem concreteM_zero : concreteM 0 = (0 : ℚ) := by
  apply le_antisymm
  · have h := concreteM_le_quadCost_of_sum
      (a := 0) (b := 0) (c := 0) (d := 0) (n := 0) (by norm_num)
    norm_num [quadCost] at h
    exact h
  · have h := three_halves_mul_le_concreteM 0
    norm_num at h
    exact h

/-- The second small value of `M`. -/
theorem concreteM_one : concreteM 1 = (3 / 2 : ℚ) := by
  apply le_antisymm
  · have h := concreteM_le_quadCost_of_sum
      (a := 0) (b := 0) (c := 0) (d := 1) (n := 1) (by norm_num)
    norm_num [quadCost] at h
    exact h
  · have h := three_halves_mul_le_concreteM 1
    norm_num at h
    exact h

/-- The third small value of `M`. -/
theorem concreteM_two : concreteM 2 = (3 : ℚ) := by
  apply le_antisymm
  · have h := concreteM_le_quadCost_of_sum
      (a := 0) (b := 0) (c := 1) (d := 1) (n := 2) (by norm_num)
    norm_num [quadCost] at h
    exact h
  · have h := three_halves_mul_le_concreteM 2
    norm_num at h
    exact h

/-- The fourth small value of `M`. -/
theorem concreteM_three : concreteM 3 = (9 / 2 : ℚ) := by
  apply le_antisymm
  · have h := concreteM_le_quadCost_of_sum
      (a := 0) (b := 1) (c := 1) (d := 1) (n := 3) (by norm_num)
    norm_num [quadCost] at h
    exact h
  · have h := three_halves_mul_le_concreteM 3
    norm_num at h
    exact h

/-- The boundary values used in the small-`n` branch of the star-forest
argument. -/
theorem concreteM_eq_three_halves_mul_of_le_three
    {n : ℕ} (hn : n ≤ 3) :
    concreteM n = (3 / 2 : ℚ) * (n : ℚ) := by
  interval_cases n <;>
    norm_num [concreteM_zero, concreteM_one, concreteM_two, concreteM_three]

/-- The balanced quadruple gives the estimate `M(n) <= n^2 / 2` for
`n >= 4`, used in the non-exceptional star-forest branch. -/
theorem concreteM_le_half_sq_of_ge_four
    {n : ℕ} (hn : 4 ≤ n) :
    concreteM n ≤ (n : ℚ)^2 / 2 := by
  let q := n / 4
  have hdiv : q * 4 + n % 4 = n := by
    simpa [q, Nat.mul_comm] using Nat.div_add_mod n 4
  have hmod_lt : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases hmod : n % 4
  · have hsum : q + q + q + q = n := by omega
    have hM := concreteM_le_quadCost_of_sum
      (a := q) (b := q) (c := q) (d := q) hsum
    have hnat : n = 4 * q := by omega
    have hq : (n : ℚ) = 4 * (q : ℚ) := by exact_mod_cast hnat
    rw [hq]
    norm_num [quadCost] at hM
    nlinarith
  · have hsum : q + q + q + (q + 1) = n := by omega
    have hM := concreteM_le_quadCost_of_sum
      (a := q) (b := q) (c := q) (d := q + 1) hsum
    have hnat : n = 4 * q + 1 := by omega
    have hq : (n : ℚ) = 4 * (q : ℚ) + 1 := by exact_mod_cast hnat
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    rw [hq]
    norm_num [quadCost] at hM
    nlinarith
  · have hsum : q + q + (q + 1) + (q + 1) = n := by omega
    have hM := concreteM_le_quadCost_of_sum
      (a := q) (b := q) (c := q + 1) (d := q + 1) hsum
    have hnat : n = 4 * q + 2 := by omega
    have hq : (n : ℚ) = 4 * (q : ℚ) + 2 := by exact_mod_cast hnat
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    rw [hq]
    norm_num [quadCost] at hM
    nlinarith
  · have hsum : q + (q + 1) + (q + 1) + (q + 1) = n := by omega
    have hM := concreteM_le_quadCost_of_sum
      (a := q) (b := q + 1) (c := q + 1) (d := q + 1) hsum
    have hnat : n = 4 * q + 3 := by omega
    have hq : (n : ℚ) = 4 * (q : ℚ) + 3 := by exact_mod_cast hnat
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
    rw [hq]
    norm_num [quadCost] at hM
    nlinarith

end Lollipop

/-!
Proof component 3: `Matrix.Basic`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Basic natural-matrix form of the `3 x 4` matrix theorem.

The manuscript's matrix theorem is about nonnegative integer matrices.  This
module fixes that exact type and proves the unconditional small-total and
exceptional-star branches used in Section 5.
-/

namespace Lollipop

open BigOperators

/-- A `3 x 4` matrix with nonnegative integer entries. -/
abbrev NatMatrix := Fin 3 → Fin 4 → ℕ

/-- Coerce a natural matrix to the rational matrix used by `matrixF`. -/
def matrixOfNat (U : NatMatrix) : Fin 3 → Fin 4 → ℚ :=
  fun i j => (U i j : ℚ)

/-- Rational value of the matrix quadratic form on a natural matrix. -/
def matrixFNat (U : NatMatrix) : ℚ :=
  matrixF (matrixOfNat U)

/-- Sum of squares of all entries of a natural matrix, as a rational. -/
def entrySqNat (U : NatMatrix) : ℚ :=
  ∑ i : Fin 3, ∑ j : Fin 4, (U i j : ℚ)^2

/-- Total mass of a natural matrix. -/
def matrixTotalNat (U : NatMatrix) : ℕ :=
  ∑ i : Fin 3, ∑ j : Fin 4, U i j

/-- Section 5's matrix theorem, stated for the exact integer matrix type. -/
def MatrixTheoremStatement : Prop :=
  ∀ U : NatMatrix, matrixFNat U ≥ concreteM (matrixTotalNat U)

/-- Natural numbers satisfy `m <= m^2` after coercion to `ℚ`. -/
theorem nat_cast_le_sq (m : ℕ) : (m : ℚ) ≤ (m : ℚ)^2 := by
  cases m with
  | zero => norm_num
  | succ k =>
      have h : (1 : ℚ) ≤ (Nat.succ k : ℚ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      nlinarith

/-- Every natural `3 x 4` matrix has `F(U) >= 3 * total(U) / 2`.
This is the nonnegativity expansion used for the small-`n` branch of
Section 5. -/
theorem three_halves_total_le_matrixFNat (U : NatMatrix) :
    (3 / 2 : ℚ) * (matrixTotalNat U : ℚ) ≤ matrixFNat U := by
  have h00 := nat_cast_le_sq (U 0 0)
  have h01 := nat_cast_le_sq (U 0 1)
  have h02 := nat_cast_le_sq (U 0 2)
  have h03 := nat_cast_le_sq (U 0 3)
  have h10 := nat_cast_le_sq (U 1 0)
  have h11 := nat_cast_le_sq (U 1 1)
  have h12 := nat_cast_le_sq (U 1 2)
  have h13 := nat_cast_le_sq (U 1 3)
  have h20 := nat_cast_le_sq (U 2 0)
  have h21 := nat_cast_le_sq (U 2 1)
  have h22 := nat_cast_le_sq (U 2 2)
  have h23 := nat_cast_le_sq (U 2 3)
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, matrixTotalNat,
    Fin.sum_univ_three, Fin.sum_univ_four]
  nlinarith

set_option maxHeartbeats 800000 in
/-- The entry-square part alone contributes at least `3/2 * sum u_ij^2` to
`F`; all row/column cross terms are nonnegative for natural matrices. -/
theorem three_halves_entrySqNat_le_matrixFNat (U : NatMatrix) :
    (3 / 2 : ℚ) * entrySqNat U ≤ matrixFNat U := by
  have h00 : 0 ≤ (U 0 0 : ℚ) := by positivity
  have h01 : 0 ≤ (U 0 1 : ℚ) := by positivity
  have h02 : 0 ≤ (U 0 2 : ℚ) := by positivity
  have h03 : 0 ≤ (U 0 3 : ℚ) := by positivity
  have h10 : 0 ≤ (U 1 0 : ℚ) := by positivity
  have h11 : 0 ≤ (U 1 1 : ℚ) := by positivity
  have h12 : 0 ≤ (U 1 2 : ℚ) := by positivity
  have h13 : 0 ≤ (U 1 3 : ℚ) := by positivity
  have h20 : 0 ≤ (U 2 0 : ℚ) := by positivity
  have h21 : 0 ≤ (U 2 1 : ℚ) := by positivity
  have h22 : 0 ≤ (U 2 2 : ℚ) := by positivity
  have h23 : 0 ≤ (U 2 3 : ℚ) := by positivity
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, entrySqNat,
    Fin.sum_univ_three, Fin.sum_univ_four]
  nlinarith [mul_nonneg h00 h01, mul_nonneg h00 h02, mul_nonneg h00 h03,
    mul_nonneg h01 h02, mul_nonneg h01 h03, mul_nonneg h02 h03,
    mul_nonneg h10 h11, mul_nonneg h10 h12, mul_nonneg h10 h13,
    mul_nonneg h11 h12, mul_nonneg h11 h13, mul_nonneg h12 h13,
    mul_nonneg h20 h21, mul_nonneg h20 h22, mul_nonneg h20 h23,
    mul_nonneg h21 h22, mul_nonneg h21 h23, mul_nonneg h22 h23,
    mul_nonneg h00 h10, mul_nonneg h00 h20, mul_nonneg h10 h20,
    mul_nonneg h01 h11, mul_nonneg h01 h21, mul_nonneg h11 h21,
    mul_nonneg h02 h12, mul_nonneg h02 h22, mul_nonneg h12 h22,
    mul_nonneg h03 h13, mul_nonneg h03 h23, mul_nonneg h13 h23]

/-- The matrix theorem for total mass at most three. -/
theorem matrix_theorem_of_total_le_three
    (U : NatMatrix) (hsmall : matrixTotalNat U ≤ 3) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have hF := three_halves_total_le_matrixFNat U
  have hM :=
    concreteM_eq_three_halves_mul_of_le_three
      (n := matrixTotalNat U) hsmall
  rw [hM]
  exact hF

/-- The exceptional `(2,1,1)` star normal form. -/
def exceptionalStarNat (a b c d : ℕ) : NatMatrix :=
  fun i : Fin 3 => fun j : Fin 4 =>
    if i = 0 ∧ j = 0 then a else
    if i = 0 ∧ j = 1 then b else
    if i = 1 ∧ j = 2 then c else
    if i = 2 ∧ j = 3 then d else 0

/-- The exceptional star normal form has total mass `a+b+c+d`. -/
theorem matrixTotalNat_exceptionalStarNat (a b c d : ℕ) :
    matrixTotalNat (exceptionalStarNat a b c d) = a + b + c + d := by
  simp [matrixTotalNat, exceptionalStarNat, Fin.sum_univ_three, Fin.sum_univ_four]

/-- Value of `F` on the exceptional star normal form. -/
theorem matrixFNat_exceptionalStarNat (a b c d : ℕ) :
    matrixFNat (exceptionalStarNat a b c d) =
      quadCost (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ) := by
  unfold matrixFNat matrixOfNat exceptionalStarNat
  simpa using matrixF_star (a : ℚ) (b : ℚ) (c : ℚ) (d : ℚ)

/-- The matrix theorem on the exceptional star normal form. -/
theorem matrix_theorem_exceptionalStarNat (a b c d : ℕ) :
    matrixFNat (exceptionalStarNat a b c d) ≥
      concreteM (matrixTotalNat (exceptionalStarNat a b c d)) := by
  rw [matrixTotalNat_exceptionalStarNat, matrixFNat_exceptionalStarNat]
  exact concreteM_le_quadCost_of_sum (a := a) (b := b) (c := c) (d := d) rfl

end Lollipop

/-!
Proof component 4: `SectionFive.PartitionMatrix`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Intersection matrices for the blocker step.

The weighted blocker lemma intersects a three-partition and a four-partition
of the quotient vertices.  This file proves the bookkeeping that the
manuscript states as "squaring after grouping can only increase the sum of
squares": the intersection matrix has the expected row and column sums, and
its entry-square sum dominates the original square-sum of the vertex weights.
-/

namespace Lollipop

open BigOperators

variable {ι : Type*} [Fintype ι]

private theorem sum_partition_indicator_eq
    (f : ι → Rat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) :
    (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
        if p3 v = i ∧ p4 v = j then f v else 0) =
      ∑ v : ι, f v := by
  classical
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    intro j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  let i3 := p3 v
  let j4 := p4 v
  have hi3 : p3 v = i3 := rfl
  have hj4 : p4 v = j4 := rfl
  rw [hi3, hj4]
  rcases i3 with ⟨i3, hi3lt⟩
  rcases j4 with ⟨j4, hj4lt⟩
  interval_cases i3 <;> interval_cases j4 <;>
    simp [Fin.sum_univ_three]

/-- Natural `3 x 4` matrix obtained by intersecting a `3`-partition and a
`4`-partition of a finite weighted set.  The maps `p3` and `p4` are the part
labels. -/
def partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) : NatMatrix :=
  fun i j => ∑ v : ι, if p3 v = i ∧ p4 v = j then x v else 0

/-- Total weight of the finite weighted set. -/
def totalWeightNat (x : ι → Nat) : Nat :=
  ∑ v : ι, x v

/-- Square-sum of the original vertex weights, as a rational number. -/
def weightSquareSumRat (x : ι → Nat) : Rat :=
  ∑ v : ι, (x v : Rat)^2

/-- The row sum of the intersection matrix is the weight in the corresponding
part of the `3`-partition. -/
theorem rowSum_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) (i : Fin 3) :
    rowSum (matrixOfNat (partitionMatrixNat x p3 p4)) i =
      ∑ v : ι, if p3 v = i then (x v : Rat) else 0 := by
  classical
  simp [rowSum, matrixOfNat, partitionMatrixNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hi : p3 v = i <;> simp [hi]

/-- The column sum of the intersection matrix is the weight in the
corresponding part of the `4`-partition. -/
theorem colSum_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) (j : Fin 4) :
    colSum (matrixOfNat (partitionMatrixNat x p3 p4)) j =
      ∑ v : ι, if p4 v = j then (x v : Rat) else 0 := by
  classical
  simp [colSum, matrixOfNat, partitionMatrixNat]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hj : p4 v = j <;> simp [hj]

/-- The intersection matrix has the same total mass as the original weights. -/
theorem matrixTotalNat_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) :
    matrixTotalNat (partitionMatrixNat x p3 p4) = totalWeightNat x := by
  classical
  apply Nat.cast_injective (R := Rat)
  calc
    (matrixTotalNat (partitionMatrixNat x p3 p4) : Rat)
        = ∑ i : Fin 3, rowSum (matrixOfNat (partitionMatrixNat x p3 p4)) i := by
            simp [matrixTotalNat, rowSum, matrixOfNat]
    _ = ∑ i : Fin 3, ∑ v : ι, if p3 v = i then (x v : Rat) else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact rowSum_partitionMatrixNat x p3 p4 i
    _ = ∑ v : ι, ∑ i : Fin 3, if p3 v = i then (x v : Rat) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ v : ι, (x v : Rat) := by
            apply Finset.sum_congr rfl
            intro v _hv
            simp
    _ = (totalWeightNat x : Rat) := by
            simp [totalWeightNat]

/-- Grouping vertex weights into intersection-matrix cells can only increase
the square sum. -/
theorem weightSquareSumRat_le_entrySqNat_partitionMatrixNat
    (x : ι → Nat) (p3 : ι → Fin 3) (p4 : ι → Fin 4) :
    weightSquareSumRat x ≤ entrySqNat (partitionMatrixNat x p3 p4) := by
  classical
  have hcell : ∀ i : Fin 3, ∀ j : Fin 4,
      (∑ v : ι, (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) ≤
        (∑ v : ι, if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2 := by
    intro i j
    exact Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun v : ι => if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)
      (by intro v _hv; by_cases h : p3 v = i ∧ p4 v = j <;> simp [h])
  have hsum_le :
      (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
          (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) ≤
        (∑ i : Fin 3, ∑ j : Fin 4,
          (∑ v : ι, if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact hcell i j
  have hleft :
      (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
          (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) =
        weightSquareSumRat x := by
    have hsquares :
        (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
            (if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) =
          (∑ i : Fin 3, ∑ j : Fin 4, ∑ v : ι,
            if p3 v = i ∧ p4 v = j then (x v : Rat)^2 else 0) := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases h : p3 v = i ∧ p4 v = j <;> simp [h]
    rw [hsquares]
    simpa [weightSquareSumRat] using
      (sum_partition_indicator_eq (fun v : ι => (x v : Rat)^2) p3 p4)
  have hright :
      (∑ i : Fin 3, ∑ j : Fin 4,
          (∑ v : ι, if p3 v = i ∧ p4 v = j then (x v : Rat) else 0)^2) =
        entrySqNat (partitionMatrixNat x p3 p4) := by
    simp [entrySqNat, partitionMatrixNat]
  rw [← hleft, ← hright]
  exact hsum_le

end Lollipop

/-!
Proof component 5: `Blocker`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Checked algebra for the weighted blocker step.

This file formalizes the numerical chain in manuscript Section 4:

* weighted Turan lower bounds for the two blocker graphs,
* the comparison between the original weight-square sum `Q` and the
  `3 x 4` intersection-matrix square sum,
* the matrix-theorem lower bound.

The graph-theoretic existence of the weighted Turan partitions and the matrix
theorem itself are deliberately hypotheses here; the inequalities connecting
them are machine checked.
-/

namespace Lollipop

/-- The blocker cost appearing in the colored Turan quotient. -/
def blockerCost (Q a b : ℚ) : ℚ :=
  (3 / 2 : ℚ) * Q + 2 * a + 2 * b

/-- The matrix side obtained after intersecting a minimizing 3-partition and
a minimizing 4-partition. -/
def partitionMatrixSide (rho3 rho4 entrySq : ℚ) : ℚ :=
  rho3 + rho4 - (1 / 2 : ℚ) * entrySq

/-- The purely algebraic core of the weighted blocker lemma. -/
theorem blocker_cost_ge_partition_side
    {Q a b rho3 rho4 entrySq : ℚ}
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq) :
    blockerCost Q a b ≥ partitionMatrixSide rho3 rho4 entrySq := by
  unfold blockerCost partitionMatrixSide
  nlinarith

/-- If the matrix side is at least `M`, then the blocker cost is at least
`M`.  This is exactly the last inequality chain in Lemma 5 of the manuscript. -/
theorem blocker_cost_ge_of_matrix_bound
    {Q a b rho3 rho4 entrySq M : ℚ}
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq)
    (hmatrix : partitionMatrixSide rho3 rho4 entrySq ≥ M) :
    blockerCost Q a b ≥ M := by
  have hside : blockerCost Q a b ≥ partitionMatrixSide rho3 rho4 entrySq :=
    blocker_cost_ge_partition_side ha hb hQ
  exact ge_trans hside hmatrix

/-- Same result in the notational shape used by `Core.lean`. -/
theorem blocker_cost_ge_M
    {Q a b rho3 rho4 entrySq M : ℚ}
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq)
    (hmatrix :
      rho3 + rho4 - (1 / 2 : ℚ) * entrySq ≥ M) :
    (3 / 2 : ℚ) * Q + 2 * a + 2 * b ≥ M := by
  exact blocker_cost_ge_of_matrix_bound ha hb hQ hmatrix

/-- The scalar `partitionMatrixSide` is exactly `matrixF` when its arguments
are supplied by the row-square, column-square, and entry-square sums of `U`. -/
theorem partitionMatrixSide_eq_matrixF (U : Fin 3 → Fin 4 → ℚ) :
    partitionMatrixSide
      (∑ i : Fin 3, (rowSum U i)^2)
      (∑ j : Fin 4, (colSum U j)^2)
      (∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2) =
      matrixF U := by
  rfl

/-- Blocker conclusion using an explicit `3 x 4` matrix bound. -/
theorem blocker_cost_ge_of_matrixF_bound
    {Q a b rho3 rho4 entrySq M : ℚ}
    (U : Fin 3 → Fin 4 → ℚ)
    (ha : a ≥ (rho3 - Q) / 2)
    (hb : b ≥ (rho4 - Q) / 2)
    (hQ : Q ≤ entrySq)
    (hrho3 : rho3 = ∑ i : Fin 3, (rowSum U i)^2)
    (hrho4 : rho4 = ∑ j : Fin 4, (colSum U j)^2)
    (hentry : entrySq = ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2)
    (hmatrix : matrixF U ≥ M) :
    blockerCost Q a b ≥ M := by
  apply blocker_cost_ge_of_matrix_bound ha hb hQ
  rw [hrho3, hrho4, hentry, partitionMatrixSide_eq_matrixF]
  exact hmatrix

/-- Algebra behind the quotient objective identity
`sigma = 3P - 2a - 2b = 3/2 (n^2 - Q) - 2a - 2b`. -/
theorem quotient_identity_from_cross_mass
    {n Q P a b sigma : ℚ}
    (hP : P = (n^2 - Q) / 2)
    (hsigma : sigma = 3 * P - 2 * a - 2 * b) :
    sigma =
      (3 / 2 : ℚ) * n^2 - ((3 / 2 : ℚ) * Q + 2 * a + 2 * b) := by
  rw [hsigma, hP]
  ring

end Lollipop

/-!
Proof component 1: `Manuscript.FormulaBridge`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

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



/-!
This is the substantive proof compilation unit for `Lemma_7_2`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `Matrix.SignedMoves`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Generic signed-move algebra for Section 5 compression.

The cycle and four-edge path compressions both move along an integer direction
`D` whose total mass is zero and whose quadratic coefficient for `matrixF` is
nonpositive.  The core analytic fact is independent of the graph bookkeeping:
for a quadratic `q(t) = b t + a t^2` with `a <= 0` and `q(0)=0`, one of the
two endpoints of any interval around zero has `q <= 0`.
-/

namespace Lollipop

open BigOperators

/-- Add a rational direction to a rational matrix. -/
def addDir (U D : Fin 3 → Fin 4 → ℚ) (t : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j => U i j + t * D i j

/-- The quadratic expansion of `matrixF` along an arbitrary direction. -/
theorem matrixF_addDir_sub
    (U D : Fin 3 → Fin 4 → ℚ) (t : ℚ) :
    matrixF (addDir U D t) - matrixF U =
      t * (matrixF (addDir U D 1) - matrixF U - matrixF D) +
        t^2 * matrixF D := by
  simp [matrixF, rowSum, colSum, addDir, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- A concave or linear quadratic vanishing at `0` is nonpositive at one of
two opposite endpoints. -/
theorem endpoint_quadratic_nonpos
    {a b P N : ℚ} (ha : a ≤ 0) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    N * b + N^2 * a ≤ 0 ∨ (-P) * b + (-P)^2 * a ≤ 0 := by
  by_contra h
  push Not at h
  have hNpos : 0 < N := by
    by_contra hNnot
    have hNz : N = 0 := le_antisymm (le_of_not_gt hNnot) hN
    subst N
    norm_num at h
  have hPpos : 0 < P := by
    by_contra hPnot
    have hPz : P = 0 := le_antisymm (le_of_not_gt hPnot) hP
    subst P
    norm_num at h
  have hb_low : -N * a < b := by
    nlinarith [div_pos h.1 hNpos]
  have hb_high : b < P * a := by
    nlinarith [div_pos h.2 hPpos]
  have hpa_nonpos : P * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hP ha
  have hnona : 0 ≤ -N * a := by
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hN ha]
  nlinarith

/-- If the quadratic coefficient of `matrixF` along `D` is nonpositive, then
one of the two endpoint moves has non-increasing `matrixF`. -/
theorem matrixF_addDir_endpoint_nonincreasing
    (U D : Fin 3 → Fin 4 → ℚ) {P N : ℚ}
    (hquad : matrixF D ≤ 0) (hP : 0 ≤ P) (hN : 0 ≤ N) :
    matrixF (addDir U D N) ≤ matrixF U ∨
      matrixF (addDir U D (-P)) ≤ matrixF U := by
  let b := matrixF (addDir U D 1) - matrixF U - matrixF D
  have hend := endpoint_quadratic_nonpos
    (a := matrixF D) (b := b) hquad hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_addDir_sub]
    exact hend
  · right
    rw [← sub_nonpos, matrixF_addDir_sub]
    exact hend

end Lollipop

/-!
Proof component 2: `Matrix.LocalMoves`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Actual `matrixF` identities for the local compression moves in Section 5.

`CompressionAlgebra.lean` proves abstract polynomial fragments.  This module
ties representative moves directly to the `3 x 4` matrix quadratic form.
Permuted versions follow by relabelling rows and columns; the global
bookkeeping still remains to be formalized.
-/

namespace Lollipop

open BigOperators

/-- Canonical four-cycle alternating move on rows `0,1` and columns `0,1`. -/
def cycleMove (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + eps else
    if i = 0 ∧ j = 1 then U i j - eps else
    if i = 1 ∧ j = 1 then U i j + eps else
    if i = 1 ∧ j = 0 then U i j - eps else
    U i j

/-- The canonical four-cycle move has the concave quadratic change asserted
in Section 5. -/
theorem matrixF_cycleMove_sub
    (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) :
    matrixF (cycleMove U eps) - matrixF U =
      eps * (-(U 0 0) + U 0 1 - U 1 1 + U 1 0) - 2 * eps^2 := by
  simp [matrixF, rowSum, colSum, cycleMove, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- For the canonical four-cycle move, one endpoint of any interval around
zero is non-increasing for `matrixF`. -/
theorem matrixF_cycleMove_endpoint_nonincreasing
    (U : Fin 3 → Fin 4 → ℚ) {P N : ℚ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) :
    matrixF (cycleMove U N) ≤ matrixF U ∨
      matrixF (cycleMove U (-P)) ≤ matrixF U := by
  let b := -(U 0 0) + U 0 1 - U 1 1 + U 1 0
  have hend := endpoint_quadratic_nonpos
    (a := (-2 : ℚ)) (b := b) (by norm_num) hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_cycleMove_sub]
    nlinarith
  · right
    rw [← sub_nonpos, matrixF_cycleMove_sub]
    nlinarith

/-- Canonical four-edge path move on the path
`row 0 - col 0 - row 1 - col 1 - row 2`. -/
def pathMove (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + eps else
    if i = 1 ∧ j = 0 then U i j - eps else
    if i = 1 ∧ j = 1 then U i j + eps else
    if i = 2 ∧ j = 1 then U i j - eps else
    U i j

/-- The canonical four-edge path move has zero quadratic coefficient, hence
the change in `F` is linear in the compression parameter. -/
theorem matrixF_pathMove_sub
    (U : Fin 3 → Fin 4 → ℚ) (eps : ℚ) :
    matrixF (pathMove U eps) - matrixF U =
      eps *
        (2 * rowSum U 0 - 2 * rowSum U 2 -
          U 0 0 + U 1 0 - U 1 1 + U 2 1) := by
  simp [matrixF, rowSum, colSum, pathMove, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- For the canonical four-edge path move, one endpoint of any interval around
zero is non-increasing for `matrixF`. -/
theorem matrixF_pathMove_endpoint_nonincreasing
    (U : Fin 3 → Fin 4 → ℚ) {P N : ℚ}
    (hP : 0 ≤ P) (hN : 0 ≤ N) :
    matrixF (pathMove U N) ≤ matrixF U ∨
      matrixF (pathMove U (-P)) ≤ matrixF U := by
  let b :=
    2 * rowSum U 0 - 2 * rowSum U 2 -
      U 0 0 + U 1 0 - U 1 1 + U 2 1
  have hend := endpoint_quadratic_nonpos
    (a := (0 : ℚ)) (b := b) (by norm_num) hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_pathMove_sub]
    nlinarith
  · right
    rw [← sub_nonpos, matrixF_pathMove_sub]
    nlinarith

/-- Canonical double-star component with central edge `(0,0)`, selected
row-side leaf `(0,1)`, selected column-side leaf `(1,0)`, two other row-side
leaf masses, and one other column-side leaf mass. -/
def canonicalDoubleStar (x y z A1 A2 B : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x else
    if i = 0 ∧ j = 0 then y else
    if i = 1 ∧ j = 0 then z else
    if i = 0 ∧ j = 2 then A1 else
    if i = 0 ∧ j = 3 then A2 else
    if i = 2 ∧ j = 0 then B else 0

/-- Delete the central edge and move its mass to the selected row-side leaf. -/
def canonicalDoubleStarMoveX (x y z A1 A2 B : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x + y else
    if i = 0 ∧ j = 0 then 0 else
    if i = 1 ∧ j = 0 then z else
    if i = 0 ∧ j = 2 then A1 else
    if i = 0 ∧ j = 3 then A2 else
    if i = 2 ∧ j = 0 then B else 0

/-- Delete the central edge and move its mass to the selected column-side
leaf. -/
def canonicalDoubleStarMoveZ (x y z A1 A2 B : ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j =>
    if i = 0 ∧ j = 1 then x else
    if i = 0 ∧ j = 0 then 0 else
    if i = 1 ∧ j = 0 then z + y else
    if i = 0 ∧ j = 2 then A1 else
    if i = 0 ∧ j = 3 then A2 else
    if i = 2 ∧ j = 0 then B else 0

/-- Actual `matrixF` identity for the first canonical double-star deletion. -/
theorem matrixF_canonicalDoubleStar_sub_moveX
    (x y z A1 A2 B : ℚ) :
    matrixF (canonicalDoubleStar x y z A1 A2 B) -
      matrixF (canonicalDoubleStarMoveX x y z A1 A2 B) =
      y * (2 * B + 2 * z - x) := by
  simp [matrixF, rowSum, colSum, canonicalDoubleStar, canonicalDoubleStarMoveX,
    Fin.sum_univ_three, Fin.sum_univ_four]
  ring

/-- Actual `matrixF` identity for the second canonical double-star deletion. -/
theorem matrixF_canonicalDoubleStar_sub_moveZ
    (x y z A1 A2 B : ℚ) :
    matrixF (canonicalDoubleStar x y z A1 A2 B) -
      matrixF (canonicalDoubleStarMoveZ x y z A1 A2 B) =
      y * (2 * (A1 + A2) + 2 * x - z) := by
  simp [matrixF, rowSum, colSum, canonicalDoubleStar, canonicalDoubleStarMoveZ,
    Fin.sum_univ_three, Fin.sum_univ_four]
  ring

end Lollipop

/-!
Proof component 3: `Matrix.Relabel`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Relabeling invariance for the `3 x 4` matrix quadratic form.

The local Section 5 moves are proved in canonical coordinates.  These lemmas
show that row and column permutations preserve the row sums, column sums,
entry-square sum, total mass, and `matrixF` after reindexing.
-/

namespace Lollipop

open BigOperators

/-- A permutation sending `a` to `zero` and `b` to `one` when `a ≠ b` and
`zero ≠ one`. -/
def permSendPairToZeroOne
    {α : Type*} [DecidableEq α] (zero one a b : α) : Equiv.Perm α :=
  (Equiv.swap a zero).trans
    (Equiv.swap ((Equiv.swap a zero) b) one)

theorem permSendPairToZeroOne_apply_first
    {α : Type*} [DecidableEq α] {zero one a b : α}
    (hzeroone : zero ≠ one) (hab : a ≠ b) :
    permSendPairToZeroOne zero one a b a = zero := by
  unfold permSendPairToZeroOne
  rw [Equiv.trans_apply, Equiv.swap_apply_left]
  have hswap_ne_zero : (Equiv.swap a zero) b ≠ zero := by
    intro h
    have hba : b = a := by
      apply (Equiv.swap a zero).injective
      simpa [Equiv.swap_apply_left] using h
    exact hab hba.symm
  exact Equiv.swap_apply_of_ne_of_ne hswap_ne_zero.symm hzeroone

theorem permSendPairToZeroOne_apply_second
    {α : Type*} [DecidableEq α] (zero one a b : α) :
    permSendPairToZeroOne zero one a b b = one := by
  unfold permSendPairToZeroOne
  rw [Equiv.trans_apply, Equiv.swap_apply_left]

theorem permSendPairToZeroOne_symm_zero
    {α : Type*} [DecidableEq α] {zero one a b : α}
    (hzeroone : zero ≠ one) (hab : a ≠ b) :
    (permSendPairToZeroOne zero one a b).symm zero = a := by
  exact (Equiv.symm_apply_eq (permSendPairToZeroOne zero one a b)).2
    (permSendPairToZeroOne_apply_first hzeroone hab).symm

theorem permSendPairToZeroOne_symm_one
    {α : Type*} [DecidableEq α] {zero one a b : α} :
    (permSendPairToZeroOne zero one a b).symm one = b := by
  exact (Equiv.symm_apply_eq (permSendPairToZeroOne zero one a b)).2
    (permSendPairToZeroOne_apply_second zero one a b).symm

/-- A permutation sending `a`, `b`, `c` to `zero`, `one`, `two`
respectively, under the corresponding distinctness assumptions. -/
def permSendTripleToZeroOneTwo
    {α : Type*} [DecidableEq α] (zero one two a b c : α) : Equiv.Perm α :=
  let p := permSendPairToZeroOne zero one a b
  p.trans (Equiv.swap (p c) two)

theorem permSendTripleToZeroOneTwo_apply_first
    {α : Type*} [DecidableEq α] {zero one two a b c : α}
    (hzeroone : zero ≠ one) (hzerotwo : zero ≠ two)
    (hab : a ≠ b) (hac : a ≠ c) :
    permSendTripleToZeroOneTwo zero one two a b c a = zero := by
  let p := permSendPairToZeroOne zero one a b
  have hpa : p a = zero := permSendPairToZeroOne_apply_first hzeroone hab
  have hpc_ne_zero : p c ≠ zero := by
    intro hpc
    have hca : c = a := by
      apply p.injective
      rw [hpc, hpa]
    exact hac hca.symm
  unfold permSendTripleToZeroOneTwo
  change (Equiv.swap (p c) two) (p a) = zero
  rw [hpa]
  exact Equiv.swap_apply_of_ne_of_ne hpc_ne_zero.symm hzerotwo

theorem permSendTripleToZeroOneTwo_apply_second
    {α : Type*} [DecidableEq α] {zero one two a b c : α}
    (honetwo : one ≠ two) (hbc : b ≠ c) :
    permSendTripleToZeroOneTwo zero one two a b c b = one := by
  let p := permSendPairToZeroOne zero one a b
  have hpb : p b = one := permSendPairToZeroOne_apply_second zero one a b
  have hpc_ne_one : p c ≠ one := by
    intro hpc
    have hcb : c = b := by
      apply p.injective
      rw [hpc, hpb]
    exact hbc hcb.symm
  unfold permSendTripleToZeroOneTwo
  change (Equiv.swap (p c) two) (p b) = one
  rw [hpb]
  exact Equiv.swap_apply_of_ne_of_ne hpc_ne_one.symm honetwo

theorem permSendTripleToZeroOneTwo_apply_third
    {α : Type*} [DecidableEq α] (zero one two a b c : α) :
    permSendTripleToZeroOneTwo zero one two a b c c = two := by
  let p := permSendPairToZeroOne zero one a b
  unfold permSendTripleToZeroOneTwo
  change (Equiv.swap (p c) two) (p c) = two
  exact Equiv.swap_apply_left (p c) two

/-- Relabel rows and columns of a rational `3 x 4` matrix. -/
def relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) : Fin 3 → Fin 4 → ℚ :=
  fun i j => U (er i) (ec j)

/-- Relabel rows and columns of a natural `3 x 4` matrix. -/
def relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) : NatMatrix :=
  fun i j => U (er i) (ec j)

/-- Coercing a relabeled natural matrix is the same as relabeling after
coercion. -/
theorem matrixOfNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    matrixOfNat (relabelNatMatrix er ec U) =
      relabelMatrix er ec (matrixOfNat U) := by
  rfl

/-- Row sums are relabeled by the row permutation. -/
theorem rowSum_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) (i : Fin 3) :
    rowSum (relabelMatrix er ec U) i = rowSum U (er i) := by
  unfold rowSum relabelMatrix
  exact Equiv.sum_comp ec (fun j : Fin 4 => U (er i) j)

/-- Column sums are relabeled by the column permutation. -/
theorem colSum_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) (j : Fin 4) :
    colSum (relabelMatrix er ec U) j = colSum U (ec j) := by
  unfold colSum relabelMatrix
  exact Equiv.sum_comp er (fun i : Fin 3 => U i (ec j))

/-- Total mass is invariant under row and column relabeling. -/
theorem matrixTotal_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) :
    matrixTotal (relabelMatrix er ec U) = matrixTotal U := by
  unfold matrixTotal relabelMatrix
  calc
    (∑ i : Fin 3, ∑ j : Fin 4, U (er i) (ec j))
        = ∑ i : Fin 3, ∑ j : Fin 4, U i (ec j) := by
          exact Equiv.sum_comp er (fun i : Fin 3 => ∑ j : Fin 4, U i (ec j))
    _ = ∑ i : Fin 3, ∑ j : Fin 4, U i j := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Equiv.sum_comp ec (fun j : Fin 4 => U i j)

/-- Natural total mass is invariant under row and column relabeling. -/
theorem matrixTotalNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    matrixTotalNat (relabelNatMatrix er ec U) = matrixTotalNat U := by
  unfold matrixTotalNat relabelNatMatrix
  calc
    (∑ i : Fin 3, ∑ j : Fin 4, U (er i) (ec j))
        = ∑ i : Fin 3, ∑ j : Fin 4, U i (ec j) := by
          exact Equiv.sum_comp er (fun i : Fin 3 => ∑ j : Fin 4, U i (ec j))
    _ = ∑ i : Fin 3, ∑ j : Fin 4, U i j := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Equiv.sum_comp ec (fun j : Fin 4 => U i j)

/-- The entry-square sum is invariant under row and column relabeling. -/
theorem entrySq_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) :
    (∑ i : Fin 3, ∑ j : Fin 4, (relabelMatrix er ec U i j)^2) =
      ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2 := by
  unfold relabelMatrix
  calc
    (∑ i : Fin 3, ∑ j : Fin 4, (U (er i) (ec j))^2)
        = ∑ i : Fin 3, ∑ j : Fin 4, (U i (ec j))^2 := by
          exact Equiv.sum_comp er
            (fun i : Fin 3 => ∑ j : Fin 4, (U i (ec j))^2)
    _ = ∑ i : Fin 3, ∑ j : Fin 4, (U i j)^2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact Equiv.sum_comp ec (fun j : Fin 4 => (U i j)^2)

/-- The matrix quadratic form is invariant under row and column relabeling. -/
theorem matrixF_relabelMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : Fin 3 → Fin 4 → ℚ) :
    matrixF (relabelMatrix er ec U) = matrixF U := by
  unfold matrixF
  rw [entrySq_relabelMatrix er ec U]
  have hrow :
      (∑ i : Fin 3, (rowSum (relabelMatrix er ec U) i)^2) =
        ∑ i : Fin 3, (rowSum U i)^2 := by
    calc
      (∑ i : Fin 3, (rowSum (relabelMatrix er ec U) i)^2)
          = ∑ i : Fin 3, (rowSum U (er i))^2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [rowSum_relabelMatrix]
      _ = ∑ i : Fin 3, (rowSum U i)^2 := by
            exact Equiv.sum_comp er (fun i : Fin 3 => (rowSum U i)^2)
  have hcol :
      (∑ j : Fin 4, (colSum (relabelMatrix er ec U) j)^2) =
        ∑ j : Fin 4, (colSum U j)^2 := by
    calc
      (∑ j : Fin 4, (colSum (relabelMatrix er ec U) j)^2)
          = ∑ j : Fin 4, (colSum U (ec j))^2 := by
            apply Finset.sum_congr rfl
            intro j _hi
            rw [colSum_relabelMatrix]
      _ = ∑ j : Fin 4, (colSum U j)^2 := by
            exact Equiv.sum_comp ec (fun j : Fin 4 => (colSum U j)^2)
  rw [hrow, hcol]

/-- The natural-matrix quadratic form is invariant under row and column
relabeling. -/
theorem matrixFNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    matrixFNat (relabelNatMatrix er ec U) = matrixFNat U := by
  unfold matrixFNat
  rw [matrixOfNat_relabelNatMatrix]
  exact matrixF_relabelMatrix er ec (matrixOfNat U)

end Lollipop

/-!
Proof component 4: `Matrix.Support`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Finite support graph vocabulary for the `3 x 4` matrix theorem.

The support graph lives on seven vertices: three row vertices and four column
vertices.  A support is a finset of the twelve possible matrix cells.  A
support is a star forest exactly when it has no simple path of length three;
the forward use in the compression proof is that every non-star support
contains such a path, which must be handled by a cycle/path/double-star move.
-/

namespace Lollipop

open BigOperators

/-- Matrix support edges are matrix cells. -/
abbrev MatrixEdge := Fin 3 × Fin 4

/-- Matrix support graph vertices: rows or columns. -/
inductive MatrixVertex where
  | row : Fin 3 → MatrixVertex
  | col : Fin 4 → MatrixVertex
  deriving DecidableEq, Fintype, Repr

/-- The row endpoint of a matrix edge. -/
def MatrixEdge.rowVertex (e : MatrixEdge) : MatrixVertex :=
  MatrixVertex.row e.1

/-- The column endpoint of a matrix edge. -/
def MatrixEdge.colVertex (e : MatrixEdge) : MatrixVertex :=
  MatrixVertex.col e.2

/-- A matrix edge is incident to a support-graph vertex. -/
def MatrixEdge.Incident (e : MatrixEdge) (v : MatrixVertex) : Prop :=
  v = e.rowVertex ∨ v = e.colVertex

instance (e : MatrixEdge) (v : MatrixVertex) : Decidable (e.Incident v) := by
  unfold MatrixEdge.Incident
  infer_instance

/-- Finset support of a natural matrix. -/
def supportOfNat (U : NatMatrix) : Finset MatrixEdge :=
  Finset.univ.filter (fun e : MatrixEdge => 0 < U e.1 e.2)

/-- Support-cardinality descent measure. -/
def supportCardNat (U : NatMatrix) : ℕ :=
  (supportOfNat U).card

/-- Membership in the natural-matrix support is exactly positivity of the
corresponding entry. -/
theorem mem_supportOfNat_iff (U : NatMatrix) (e : MatrixEdge) :
    e ∈ supportOfNat U ↔ 0 < U e.1 e.2 := by
  simp [supportOfNat]

/-- A cell outside the support has zero mass. -/
theorem entry_eq_zero_of_not_mem_support
    (U : NatMatrix) {i : Fin 3} {j : Fin 4}
    (h : (i, j) ∉ supportOfNat U) :
    U i j = 0 := by
  rw [mem_supportOfNat_iff] at h
  exact Nat.eq_zero_of_not_pos h

/-- A cell outside a known support mask has zero mass. -/
theorem entry_eq_zero_of_support_eq
    (U : NatMatrix) {S : Finset MatrixEdge}
    (hU : supportOfNat U = S) {i : Fin 3} {j : Fin 4}
    (h : (i, j) ∉ S) :
    U i j = 0 := by
  exact entry_eq_zero_of_not_mem_support U (by rw [hU]; exact h)

/-- Adjacency in the support graph associated to a support finset. -/
def SupportAdj (S : Finset MatrixEdge) (v w : MatrixVertex) : Prop :=
  v ≠ w ∧ ∃ e ∈ S, e.Incident v ∧ e.Incident w

instance (S : Finset MatrixEdge) (v w : MatrixVertex) :
    Decidable (SupportAdj S v w) := by
  unfold SupportAdj
  infer_instance

/-- Column neighbors of a row in the support graph. -/
def rowNeighbors (S : Finset MatrixEdge) (i : Fin 3) : Finset (Fin 4) :=
  Finset.univ.filter fun j : Fin 4 => (i, j) ∈ S

/-- Row neighbors of a column in the support graph. -/
def colNeighbors (S : Finset MatrixEdge) (j : Fin 4) : Finset (Fin 3) :=
  Finset.univ.filter fun i : Fin 3 => (i, j) ∈ S

/-- Rows of degree at least two in the support graph. -/
def highRows (S : Finset MatrixEdge) : Finset (Fin 3) :=
  Finset.univ.filter fun i : Fin 3 => 1 < (rowNeighbors S i).card

/-- Columns of degree at least two in the support graph. -/
def highCols (S : Finset MatrixEdge) : Finset (Fin 4) :=
  Finset.univ.filter fun j : Fin 4 => 1 < (colNeighbors S j).card

@[simp] theorem mem_rowNeighbors_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    j ∈ rowNeighbors S i ↔ (i, j) ∈ S := by
  simp [rowNeighbors]

@[simp] theorem mem_colNeighbors_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    i ∈ colNeighbors S j ↔ (i, j) ∈ S := by
  simp [colNeighbors]

@[simp] theorem mem_highRows_iff
    (S : Finset MatrixEdge) (i : Fin 3) :
    i ∈ highRows S ↔ 1 < (rowNeighbors S i).card := by
  simp [highRows]

@[simp] theorem mem_highCols_iff
    (S : Finset MatrixEdge) (j : Fin 4) :
    j ∈ highCols S ↔ 1 < (colNeighbors S j).card := by
  simp [highCols]

private theorem sum_if_mem_finset_eq_card_mul_add_compl
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : Finset α) (c : ℕ) :
    (∑ x : α, if x ∈ T then c else 1) =
      T.card * c + (Fintype.card α - T.card) := by
  classical
  have hfilter :
      ((Finset.univ : Finset α).filter fun x => x ∈ T) = T := by
    ext x
    simp
  have hcomp :
      ((Finset.univ : Finset α).filter fun x => x ∉ T).card =
        Fintype.card α - T.card := by
    have h :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset α)) (p := fun x => x ∈ T)
    rw [hfilter] at h
    simp only [Finset.card_univ] at h
    omega
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset α)) (p := fun x => x ∈ T)
    (f := fun x => if x ∈ T then c else 1)]
  calc
    (((Finset.univ : Finset α).filter (fun x => x ∈ T)).sum
        fun x => if x ∈ T then c else 1) +
        (((Finset.univ : Finset α).filter (fun x => ¬x ∈ T)).sum
          fun x => if x ∈ T then c else 1)
        = (T.sum fun _ => c) +
            (((Finset.univ : Finset α).filter (fun x => x ∉ T)).sum
              fun _ => 1) := by
          congr 1
          · rw [hfilter]
            refine Finset.sum_congr rfl ?_
            intro x hx
            simp [hx]
          · refine Finset.sum_congr rfl ?_
            intro x hx
            have hxnot : x ∉ T := (Finset.mem_filter.mp hx).2
            simp [hxnot]
    _ = T.card * c + (Fintype.card α - T.card) := by
          simp [hcomp, Finset.sum_const]

theorem rowFiber_card_eq_rowNeighbors_card
    (S : Finset MatrixEdge) (i : Fin 3) :
    (S.filter fun e : MatrixEdge => e.1 = i).card =
      (rowNeighbors S i).card := by
  let f : MatrixEdge → Fin 4 := fun e => e.2
  have hf : Set.InjOn f (S.filter fun e : MatrixEdge => e.1 = i) := by
    intro a ha b hb hab
    rcases a with ⟨ar, ac⟩
    rcases b with ⟨br, bc⟩
    have har : ar = i := (Finset.mem_filter.mp ha).2
    have hbr : br = i := (Finset.mem_filter.mp hb).2
    have hbc : ac = bc := hab
    exact Prod.ext (by rw [har, hbr]) hbc
  have himage :
      (S.filter fun e : MatrixEdge => e.1 = i).image f =
        rowNeighbors S i := by
    ext j
    constructor
    · rintro hj
      rcases Finset.mem_image.mp hj with ⟨e, he, rfl⟩
      rcases e with ⟨r, c⟩
      have heS : (r, c) ∈ S := (Finset.mem_filter.mp he).1
      have hri : r = i := (Finset.mem_filter.mp he).2
      simpa [rowNeighbors, hri] using heS
    · intro hj
      have hij : (i, j) ∈ S := by simpa using hj
      exact Finset.mem_image.mpr
        ⟨(i, j), by simp [hij], rfl⟩
  rw [← himage]
  exact (Finset.card_image_of_injOn hf).symm

theorem colFiber_card_eq_colNeighbors_card
    (S : Finset MatrixEdge) (j : Fin 4) :
    (S.filter fun e : MatrixEdge => e.2 = j).card =
      (colNeighbors S j).card := by
  let f : MatrixEdge → Fin 3 := fun e => e.1
  have hf : Set.InjOn f (S.filter fun e : MatrixEdge => e.2 = j) := by
    intro a ha b hb hab
    rcases a with ⟨ar, ac⟩
    rcases b with ⟨br, bc⟩
    have hac : ac = j := (Finset.mem_filter.mp ha).2
    have hbc : bc = j := (Finset.mem_filter.mp hb).2
    have hbr : ar = br := hab
    exact Prod.ext hbr (by rw [hac, hbc])
  have himage :
      (S.filter fun e : MatrixEdge => e.2 = j).image f =
        colNeighbors S j := by
    ext i
    constructor
    · rintro hi
      rcases Finset.mem_image.mp hi with ⟨e, he, rfl⟩
      rcases e with ⟨r, c⟩
      have heS : (r, c) ∈ S := (Finset.mem_filter.mp he).1
      have hcj : c = j := (Finset.mem_filter.mp he).2
      simpa [colNeighbors, hcj] using heS
    · intro hi
      have hij : (i, j) ∈ S := by simpa using hi
      exact Finset.mem_image.mpr
        ⟨(i, j), by simp [hij], rfl⟩
  rw [← himage]
  exact (Finset.card_image_of_injOn hf).symm

theorem card_eq_sum_rowNeighbors_card (S : Finset MatrixEdge) :
    S.card = ∑ i : Fin 3, (rowNeighbors S i).card := by
  classical
  have hmaps :
      (S : Set MatrixEdge).MapsTo (fun e : MatrixEdge => e.1)
        ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) := by
    intro e he
    simp
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin 3)))
      (f := fun e : MatrixEdge => e.1) hmaps
  simpa [rowFiber_card_eq_rowNeighbors_card] using h

theorem card_eq_sum_colNeighbors_card (S : Finset MatrixEdge) :
    S.card = ∑ j : Fin 4, (colNeighbors S j).card := by
  classical
  have hmaps :
      (S : Set MatrixEdge).MapsTo (fun e : MatrixEdge => e.2)
        ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) := by
    intro e he
    simp
  have h :=
    Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin 4)))
      (f := fun e : MatrixEdge => e.2) hmaps
  simpa [colFiber_card_eq_colNeighbors_card] using h

theorem exists_one_lt_rowNeighbors_card_of_three_lt_card
    {S : Finset MatrixEdge} (hcard : 3 < S.card) :
    ∃ i : Fin 3, 1 < (rowNeighbors S i).card := by
  by_contra h
  have hle : ∀ i : Fin 3, (rowNeighbors S i).card ≤ 1 := by
    intro i
    exact Nat.le_of_not_gt (by
      intro hi
      exact h ⟨i, hi⟩)
  have hsum := card_eq_sum_rowNeighbors_card S
  rw [Fin.sum_univ_three] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  omega

theorem exists_one_lt_colNeighbors_card_of_four_lt_card
    {S : Finset MatrixEdge} (hcard : 4 < S.card) :
    ∃ j : Fin 4, 1 < (colNeighbors S j).card := by
  by_contra h
  have hle : ∀ j : Fin 4, (colNeighbors S j).card ≤ 1 := by
    intro j
    exact Nat.le_of_not_gt (by
      intro hj
      exact h ⟨j, hj⟩)
  have hsum := card_eq_sum_colNeighbors_card S
  rw [Fin.sum_univ_four] at hsum
  have h0 := hle 0
  have h1 := hle 1
  have h2 := hle 2
  have h3 := hle 3
  omega

@[simp] theorem supportAdj_symm
    (S : Finset MatrixEdge) (v w : MatrixVertex) :
    SupportAdj S v w ↔ SupportAdj S w v := by
  unfold SupportAdj
  constructor
  · rintro ⟨hvw, e, he, hv, hw⟩
    exact ⟨hvw.symm, e, he, hw, hv⟩
  · rintro ⟨hwv, e, he, hw, hv⟩
    exact ⟨hwv.symm, e, he, hv, hw⟩

@[simp] theorem supportAdj_row_col_iff
    (S : Finset MatrixEdge) (i : Fin 3) (j : Fin 4) :
    SupportAdj S (MatrixVertex.row i) (MatrixVertex.col j) ↔
      (i, j) ∈ S := by
  constructor
  · rintro ⟨_hne, e, he, hi, hj⟩
    rcases e with ⟨r, c⟩
    simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
      MatrixEdge.colVertex] at hi hj
    subst r
    subst c
    exact he
  · intro he
    refine ⟨by simp, ⟨(i, j), he, ?_, ?_⟩⟩
    · simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
        MatrixEdge.colVertex]
    · simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
        MatrixEdge.colVertex]

@[simp] theorem supportAdj_col_row_iff
    (S : Finset MatrixEdge) (j : Fin 4) (i : Fin 3) :
    SupportAdj S (MatrixVertex.col j) (MatrixVertex.row i) ↔
      (i, j) ∈ S := by
  rw [supportAdj_symm, supportAdj_row_col_iff]

@[simp] theorem supportAdj_row_row_iff
    (S : Finset MatrixEdge) (i k : Fin 3) :
    SupportAdj S (MatrixVertex.row i) (MatrixVertex.row k) ↔ False := by
  constructor
  · rintro ⟨hne, e, _he, hi, hk⟩
    rcases e with ⟨r, c⟩
    simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
      MatrixEdge.colVertex] at hi hk
    subst i
    subst k
    exact hne rfl
  · intro h
    cases h

@[simp] theorem supportAdj_col_col_iff
    (S : Finset MatrixEdge) (j l : Fin 4) :
    SupportAdj S (MatrixVertex.col j) (MatrixVertex.col l) ↔ False := by
  constructor
  · rintro ⟨hne, e, _he, hj, hl⟩
    rcases e with ⟨r, c⟩
    simp [MatrixEdge.Incident, MatrixEdge.rowVertex,
      MatrixEdge.colVertex] at hj hl
    subst j
    subst l
    exact hne rfl
  · intro h
    cases h

/-- A simple path of length three in a support graph. -/
def HasSupportPath3 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧ SupportAdj S v2 v3

instance (S : Finset MatrixEdge) : Decidable (HasSupportPath3 S) := by
  unfold HasSupportPath3
  infer_instance

/-- A length-three support path is exactly a raw double-star core after
choosing the middle row/column of the path. -/
theorem exists_doubleStarCore_edges_of_hasSupportPath3
    {S : Finset MatrixEdge} (h : HasSupportPath3 S) :
    ∃ i0 i1 : Fin 3, ∃ j0 j1 : Fin 4,
      i0 ≠ i1 ∧ j0 ≠ j1 ∧
        (i0, j0) ∈ S ∧ (i0, j1) ∈ S ∧ (i1, j0) ∈ S := by
  rcases h with ⟨v0, v1, v2, v3, hne01, hne02, hne03,
    hne12, hne13, hne23, hadj01, hadj12, hadj23⟩
  rcases v0 with r0 | c0
  · rcases v1 with r1 | c1
    · exfalso
      simp at hadj01
    · rcases v2 with r2 | c2
      · rcases v3 with r3 | c3
        · exfalso
          simp at hadj23
        · refine ⟨r2, r0, c1, c3, ?_, ?_, ?_, ?_, ?_⟩
          · intro h
            exact hne02 (by simp [h])
          · intro h
            exact hne13 (by simp [h])
          · simpa using hadj12
          · simpa using hadj23
          · simpa using hadj01
      · exfalso
        simp at hadj12
  · rcases v1 with r1 | c1
    · rcases v2 with r2 | c2
      · exfalso
        simp at hadj12
      · rcases v3 with r3 | c3
        · refine ⟨r1, r3, c2, c0, ?_, ?_, ?_, ?_, ?_⟩
          · intro h
            exact hne13 (by simp [h])
          · intro h
            exact hne02 (by simp [h])
          · simpa using hadj12
          · simpa using hadj01
          · simpa using hadj23
        · exfalso
          simp at hadj23
    · exfalso
      simp at hadj01

/-- An edge with degree at least two at both endpoints immediately gives a
simple support path of length three. -/
theorem hasSupportPath3_of_edge_one_lt_degrees
    {S : Finset MatrixEdge} {i : Fin 3} {j : Fin 4}
    (hij : (i, j) ∈ S)
    (hrow : 1 < (rowNeighbors S i).card)
    (hcol : 1 < (colNeighbors S j).card) :
    HasSupportPath3 S := by
  rcases Finset.one_lt_card.mp hrow with ⟨a, ha, b, hb, hab⟩
  obtain ⟨j', hj', hj'ne⟩ :
      ∃ j' ∈ rowNeighbors S i, j' ≠ j := by
    by_cases haj : a = j
    · exact ⟨b, hb, by
        intro hbj
        exact hab (haj.trans hbj.symm)⟩
    · exact ⟨a, ha, haj⟩
  rcases Finset.one_lt_card.mp hcol with ⟨a, ha, b, hb, hab⟩
  obtain ⟨i', hi', hi'ne⟩ :
      ∃ i' ∈ colNeighbors S j, i' ≠ i := by
    by_cases hai : a = i
    · exact ⟨b, hb, by
        intro hbi
        exact hab (hai.trans hbi.symm)⟩
    · exact ⟨a, ha, hai⟩
  refine ⟨MatrixVertex.col j', MatrixVertex.row i,
    MatrixVertex.col j, MatrixVertex.row i', ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp
  · simpa using hj'ne
  · simp
  · simp
  · intro h
    exact hi'ne (by simpa using h.symm)
  · simp
  · simpa using hj'
  · simpa using hij
  · simpa using hi'

/-- Computational star-forest predicate for these bipartite supports.  For a
simple graph, having no simple path of length three is equivalent to every
component being a star or an isolated vertex. -/
def IsSupportStarForest (S : Finset MatrixEdge) : Prop :=
  ¬ HasSupportPath3 S

instance (S : Finset MatrixEdge) : Decidable (IsSupportStarForest S) := by
  unfold IsSupportStarForest
  infer_instance

/-- In a star-forest support, every present edge has a degree-one endpoint. -/
theorem rowNeighbors_card_le_one_or_colNeighbors_card_le_one_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {i : Fin 3} {j : Fin 4} (hij : (i, j) ∈ S) :
    (rowNeighbors S i).card ≤ 1 ∨ (colNeighbors S j).card ≤ 1 := by
  by_contra h
  have hrow_not : ¬ (rowNeighbors S i).card ≤ 1 := fun hrow =>
    h (Or.inl hrow)
  have hcol_not : ¬ (colNeighbors S j).card ≤ 1 := fun hcol =>
    h (Or.inr hcol)
  exact hstar (hasSupportPath3_of_edge_one_lt_degrees hij
    (Nat.lt_of_not_ge hrow_not) (Nat.lt_of_not_ge hcol_not))

theorem not_mem_of_one_lt_row_col_neighbors_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {i : Fin 3} {j : Fin 4}
    (hrow : 1 < (rowNeighbors S i).card)
    (hcol : 1 < (colNeighbors S j).card) :
    (i, j) ∉ S := by
  intro hij
  exact hstar (hasSupportPath3_of_edge_one_lt_degrees hij hrow hcol)

/-- A non-star support contains a raw double-star core. -/
theorem exists_doubleStarCore_edges_of_not_star
    {S : Finset MatrixEdge} (h : ¬ IsSupportStarForest S) :
    ∃ i0 i1 : Fin 3, ∃ j0 j1 : Fin 4,
      i0 ≠ i1 ∧ j0 ≠ j1 ∧
        (i0, j0) ∈ S ∧ (i0, j1) ∈ S ∧ (i1, j0) ∈ S := by
  apply exists_doubleStarCore_edges_of_hasSupportPath3
  by_contra hpath
  exact h hpath

/-- The number of low-degree rows, expressed as a complement count. -/
theorem lowRows_card_eq (S : Finset MatrixEdge) :
    ((Finset.univ : Finset (Fin 3)).filter fun i => i ∉ highRows S).card =
      3 - (highRows S).card := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin 3)).filter fun i => i ∈ highRows S) =
        highRows S := by
    ext i
    simp
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 3)))
      (p := fun i => i ∈ highRows S)
  rw [hfilter] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

/-- The number of low-degree columns, expressed as a complement count. -/
theorem lowCols_card_eq (S : Finset MatrixEdge) :
    ((Finset.univ : Finset (Fin 4)).filter fun j => j ∉ highCols S).card =
      4 - (highCols S).card := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin 4)).filter fun j => j ∈ highCols S) =
        highCols S := by
    ext j
    simp
  have h :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 4)))
      (p := fun j => j ∈ highCols S)
  rw [hfilter] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

theorem highRows_card_le_three (S : Finset MatrixEdge) :
    (highRows S).card ≤ 3 := by
  have h :=
    Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin 3)))
      (p := fun i => 1 < (rowNeighbors S i).card)
  simpa [highRows, Fintype.card_fin] using h

theorem highCols_card_le_four (S : Finset MatrixEdge) :
    (highCols S).card ≤ 4 := by
  have h :=
    Finset.card_filter_le
      (s := (Finset.univ : Finset (Fin 4)))
      (p := fun j => 1 < (colNeighbors S j).card)
  simpa [highCols, Fintype.card_fin] using h

theorem rowNeighbors_card_le_lowCols_card_of_highRow_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {i : Fin 3} (hi : i ∈ highRows S) :
    (rowNeighbors S i).card ≤
      ((Finset.univ : Finset (Fin 4)).filter fun j => j ∉ highCols S).card := by
  refine Finset.card_le_card ?_
  intro j hj
  have hrow : 1 < (rowNeighbors S i).card := by
    simpa using hi
  have hij : (i, j) ∈ S := by
    simpa using hj
  have hjlow : j ∉ highCols S := by
    intro hjhigh
    have hcol : 1 < (colNeighbors S j).card := by
      simpa using hjhigh
    exact not_mem_of_one_lt_row_col_neighbors_of_starForest
      hstar hrow hcol hij
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjlow⟩

theorem colNeighbors_card_le_lowRows_card_of_highCol_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S)
    {j : Fin 4} (hj : j ∈ highCols S) :
    (colNeighbors S j).card ≤
      ((Finset.univ : Finset (Fin 3)).filter fun i => i ∉ highRows S).card := by
  refine Finset.card_le_card ?_
  intro i hi
  have hcol : 1 < (colNeighbors S j).card := by
    simpa using hj
  have hij : (i, j) ∈ S := by
    simpa using hi
  have hilow : i ∉ highRows S := by
    intro hihigh
    have hrow : 1 < (rowNeighbors S i).card := by
      simpa using hihigh
    exact not_mem_of_one_lt_row_col_neighbors_of_starForest
      hstar hrow hcol hij
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hilow⟩

theorem card_le_row_high_bound_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S) :
    S.card ≤
      (highRows S).card * (4 - (highCols S).card) +
        (3 - (highRows S).card) := by
  have hsum_le :
      (∑ i : Fin 3, (rowNeighbors S i).card) ≤
        ∑ i : Fin 3,
          if i ∈ highRows S then 4 - (highCols S).card else 1 := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    by_cases hi : i ∈ highRows S
    · have hle :=
        rowNeighbors_card_le_lowCols_card_of_highRow_starForest
          hstar hi
      rw [lowCols_card_eq] at hle
      simpa [hi] using hle
    · have hle : (rowNeighbors S i).card ≤ 1 := by
        exact Nat.le_of_not_gt fun h =>
          hi ((mem_highRows_iff S i).2 h)
      simpa [hi] using hle
  have hsum_eq :
      (∑ i : Fin 3,
          if i ∈ highRows S then 4 - (highCols S).card else 1) =
        (highRows S).card * (4 - (highCols S).card) +
          (3 - (highRows S).card) := by
    simpa [Fintype.card_fin] using
      (sum_if_mem_finset_eq_card_mul_add_compl
        (T := highRows S) (c := 4 - (highCols S).card))
  calc
    S.card = ∑ i : Fin 3, (rowNeighbors S i).card :=
      card_eq_sum_rowNeighbors_card S
    _ ≤ ∑ i : Fin 3,
          if i ∈ highRows S then 4 - (highCols S).card else 1 :=
      hsum_le
    _ = (highRows S).card * (4 - (highCols S).card) +
          (3 - (highRows S).card) :=
      hsum_eq

theorem card_le_col_high_bound_of_starForest
    {S : Finset MatrixEdge} (hstar : IsSupportStarForest S) :
    S.card ≤
      (highCols S).card * (3 - (highRows S).card) +
        (4 - (highCols S).card) := by
  have hsum_le :
      (∑ j : Fin 4, (colNeighbors S j).card) ≤
        ∑ j : Fin 4,
          if j ∈ highCols S then 3 - (highRows S).card else 1 := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hj : j ∈ highCols S
    · have hle :=
        colNeighbors_card_le_lowRows_card_of_highCol_starForest
          hstar hj
      rw [lowRows_card_eq] at hle
      simpa [hj] using hle
    · have hle : (colNeighbors S j).card ≤ 1 := by
        exact Nat.le_of_not_gt fun h =>
          hj ((mem_highCols_iff S j).2 h)
      simpa [hj] using hle
  have hsum_eq :
      (∑ j : Fin 4,
          if j ∈ highCols S then 3 - (highRows S).card else 1) =
        (highCols S).card * (3 - (highRows S).card) +
          (4 - (highCols S).card) := by
    simpa [Fintype.card_fin] using
      (sum_if_mem_finset_eq_card_mul_add_compl
        (T := highCols S) (c := 3 - (highRows S).card))
  calc
    S.card = ∑ j : Fin 4, (colNeighbors S j).card :=
      card_eq_sum_colNeighbors_card S
    _ ≤ ∑ j : Fin 4,
          if j ∈ highCols S then 3 - (highRows S).card else 1 :=
      hsum_le
    _ = (highCols S).card * (3 - (highRows S).card) +
          (4 - (highCols S).card) :=
      hsum_eq

/-- The support of the zero matrix is a star forest. -/
theorem isSupportStarForest_empty :
    IsSupportStarForest (∅ : Finset MatrixEdge) := by
  intro h
  rcases h with ⟨v0, v1, v2, v3, hne01, hne02, hne03,
    hne12, hne13, hne23, hadj01, hadj12, hadj23⟩
  rcases hadj01.2 with ⟨e, he, _⟩
  simp at he

/-- A finite `K_{3,4}` support whose components are stars has at most five
edges. -/
theorem support_card_le_five_of_starForest :
    ∀ S : Finset MatrixEdge, IsSupportStarForest S → S.card ≤ 5 := by
  intro S hstar
  by_contra hle
  have hcard : 5 < S.card := Nat.lt_of_not_ge hle
  have hrow_exists :
      ∃ i : Fin 3, 1 < (rowNeighbors S i).card :=
    exists_one_lt_rowNeighbors_card_of_three_lt_card (by omega)
  have hcol_exists :
      ∃ j : Fin 4, 1 < (colNeighbors S j).card :=
    exists_one_lt_colNeighbors_card_of_four_lt_card (by omega)
  let a := (highRows S).card
  let b := (highCols S).card
  have ha_pos : 0 < a := by
    rcases hrow_exists with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simpa [a] using hi⟩
  have hb_pos : 0 < b := by
    rcases hcol_exists with ⟨j, hj⟩
    exact Finset.card_pos.mpr ⟨j, by simpa [b] using hj⟩
  have ha_le : a ≤ 3 := by
    simpa [a] using highRows_card_le_three S
  have hb_le : b ≤ 4 := by
    simpa [b] using highCols_card_le_four S
  have hrow_bound : S.card ≤ a * (4 - b) + (3 - a) := by
    simpa [a, b] using card_le_row_high_bound_of_starForest
      (S := S) hstar
  have hcol_bound : S.card ≤ b * (3 - a) + (4 - b) := by
    simpa [a, b] using card_le_col_high_bound_of_starForest
      (S := S) hstar
  have hsmall :
      a * (4 - b) + (3 - a) ≤ 5 ∨
        b * (3 - a) + (4 - b) ≤ 5 := by
    interval_cases a <;> interval_cases b <;> omega
  rcases hsmall with hsmall | hsmall
  · have : S.card ≤ 5 := le_trans hrow_bound hsmall
    omega
  · have : S.card ≤ 5 := le_trans hcol_bound hsmall
    omega

/-- Star-forest supports of natural matrices have at most five positive
entries. -/
theorem supportCardNat_le_five_of_starForest
    (U : NatMatrix)
    (hstar : IsSupportStarForest (supportOfNat U)) :
    supportCardNat U ≤ 5 := by
  exact support_card_le_five_of_starForest (supportOfNat U) hstar

/-- A simple path of length four in a support graph.  This is the graph
configuration used by the four-edge path compression. -/
def HasSupportPath4 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 v4 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧ v0 ≠ v4 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧
    v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧
    SupportAdj S v2 v3 ∧ SupportAdj S v3 v4

instance (S : Finset MatrixEdge) : Decidable (HasSupportPath4 S) := by
  unfold HasSupportPath4
  infer_instance

/-- A four-cycle in a support graph.  Four-cycles use the concave cycle
compression directly; longer cycles contain a simple four-edge path. -/
def HasSupportCycle4 (S : Finset MatrixEdge) : Prop :=
  ∃ v0 v1 v2 v3 : MatrixVertex,
    v0 ≠ v1 ∧ v0 ≠ v2 ∧ v0 ≠ v3 ∧
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v2 ≠ v3 ∧
    SupportAdj S v0 v1 ∧ SupportAdj S v1 v2 ∧
    SupportAdj S v2 v3 ∧ SupportAdj S v3 v0

instance (S : Finset MatrixEdge) : Decidable (HasSupportCycle4 S) := by
  unfold HasSupportCycle4
  infer_instance

end Lollipop

/-!
Proof component 5: `Matrix.Shapes`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Finite support-shape classification for star forests in `K_{3,4}`.

The support graph has only twelve possible edges.  Up to independent row and
column permutations, its star-forest supports fall into sixteen canonical
masks.  This file records that finite classification as a checked theorem.
-/

namespace Lollipop

/-- Relabel a support by row and column permutations. -/
def supportRelabel
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) : Finset MatrixEdge :=
  Finset.univ.filter fun e : MatrixEdge => (er.symm e.1, ec.symm e.2) ∈ S

theorem supportRelabel_eq_image
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) :
    supportRelabel er ec S =
      S.image (fun e : MatrixEdge => (er e.1, ec e.2)) := by
  ext e
  constructor
  · intro he
    refine Finset.mem_image.mpr ?_
    refine ⟨(er.symm e.1, ec.symm e.2), ?_, ?_⟩
    · simpa [supportRelabel] using he
    · simp
  · intro he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    simp [supportRelabel, ha]

/-- Relabeling a support and then relabeling back gives the original support. -/
theorem supportRelabel_symm_relabel
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) :
    supportRelabel er.symm ec.symm (supportRelabel er ec S) = S := by
  ext e
  simp [supportRelabel]

/-- The support of a relabeled natural matrix is the corresponding inverse
relabeling of its support. -/
theorem supportOfNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    supportOfNat (relabelNatMatrix er ec U) =
      supportRelabel er.symm ec.symm (supportOfNat U) := by
  ext e
  simp [supportOfNat, supportRelabel, relabelNatMatrix]

/-- If the support of `U` is a relabeled canonical support, then relabeling
`U` puts the support into canonical coordinates. -/
theorem supportOfNat_relabelNatMatrix_eq_of_supportRelabel
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) (T : Finset MatrixEdge)
    (hU : supportOfNat U = supportRelabel er ec T) :
    supportOfNat (relabelNatMatrix er ec U) = T := by
  rw [supportOfNat_relabelNatMatrix, hU, supportRelabel_symm_relabel]

/-- The canonical empty support. -/
def shape0 : Finset MatrixEdge :=
  ∅

/-- Canonical one-edge support. -/
def shape1 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4))}

/-- Canonical row-centered two-edge star. -/
def shape2_row : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4))}

/-- Canonical column-centered two-edge star. -/
def shape2_col : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4))}

/-- Canonical two disjoint singleton components. -/
def shape2_singletons : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (1 : Fin 4))}

/-- Canonical row-centered three-edge star. -/
def shape3_row : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4))}

/-- Canonical row-centered two-edge star plus a singleton. -/
def shape3_row_plus_singleton : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4))}

/-- Canonical column-centered three-edge star. -/
def shape3_col : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4)),
    ((2 : Fin 3), (0 : Fin 4))}

/-- Canonical column-centered two-edge star plus a singleton. -/
def shape3_col_plus_singleton : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4)),
    ((2 : Fin 3), (1 : Fin 4))}

/-- Canonical three singleton components. -/
def shape3_singletons : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (1 : Fin 4)),
    ((2 : Fin 3), (2 : Fin 4))}

/-- Canonical row-centered four-edge star. -/
def shape4_row : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4)), ((0 : Fin 3), (3 : Fin 4))}

/-- Canonical row-centered three-edge star plus a singleton. -/
def shape4_row3_plus_singleton : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4)), ((1 : Fin 3), (3 : Fin 4))}

/-- Canonical two disjoint row-centered two-edge stars. -/
def shape4_two_row2 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4)), ((1 : Fin 3), (3 : Fin 4))}

/-- Canonical row-centered two-edge star and column-centered two-edge star. -/
def shape4_row2_col2 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4)), ((2 : Fin 3), (2 : Fin 4))}

/-- Canonical exceptional `(2,1,1)` support. -/
def shape4_exceptional : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (2 : Fin 4)), ((2 : Fin 3), (3 : Fin 4))}

/-- Canonical five-edge `(3,2)` star forest. -/
def shape5_row3_col2 : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((0 : Fin 3), (2 : Fin 4)), ((1 : Fin 3), (3 : Fin 4)),
    ((2 : Fin 3), (3 : Fin 4))}

/-- Canonical support masks for star forests in `K_{3,4}`. -/
def canonicalStarForestSupports : Finset (Finset MatrixEdge) :=
  {shape0, shape1, shape2_row, shape2_col, shape2_singletons,
    shape3_row, shape3_row_plus_singleton, shape3_col,
    shape3_col_plus_singleton, shape3_singletons, shape4_row,
    shape4_row3_plus_singleton, shape4_two_row2, shape4_row2_col2,
    shape4_exceptional, shape5_row3_col2}

/-- A support is row/column relabel-equivalent to one of the canonical
star-forest masks. -/
def relabeledStarForestSupportsOf
    (T : Finset MatrixEdge) : Finset (Finset MatrixEdge) :=
  (Finset.univ : Finset (Fin 3 ≃ Fin 3)).biUnion fun er =>
    (Finset.univ : Finset (Fin 4 ≃ Fin 4)).image fun ec =>
      supportRelabel er ec T

/-- All supports obtained by row/column relabeling the canonical masks. -/
def allCanonicalStarForestShapes : Finset (Finset MatrixEdge) :=
  canonicalStarForestSupports.biUnion relabeledStarForestSupportsOf

/-- A support is row/column relabel-equivalent to one of the canonical
star-forest masks. -/
def IsCanonicalStarForestShape (S : Finset MatrixEdge) : Prop :=
  S ∈ allCanonicalStarForestShapes

instance (S : Finset MatrixEdge) : Decidable (IsCanonicalStarForestShape S) := by
  unfold IsCanonicalStarForestShape
  infer_instance

private theorem fin4_eq_three_of_ne_zero_one_two
    {x : Fin 4}
    (h0 : x ≠ (0 : Fin 4)) (h1 : x ≠ (1 : Fin 4))
    (h2 : x ≠ (2 : Fin 4)) :
    x = (3 : Fin 4) := by
  apply Fin.ext
  have hlt : x.val < 4 := x.isLt
  interval_cases h : x.val
  · exfalso
    exact h0 (Fin.ext (by simpa using h))
  · exfalso
    exact h1 (Fin.ext (by simpa using h))
  · exfalso
    exact h2 (Fin.ext (by simpa using h))
  · simp

theorem canonicalShape_of_supportRelabel_eq
    {S T : Finset MatrixEdge}
    (hT : T ∈ canonicalStarForestSupports)
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (hrel : supportRelabel er ec S = T) :
    IsCanonicalStarForestShape S := by
  unfold IsCanonicalStarForestShape allCanonicalStarForestShapes
  refine Finset.mem_biUnion.mpr ⟨T, hT, ?_⟩
  unfold relabeledStarForestSupportsOf
  refine Finset.mem_biUnion.mpr ⟨er.symm, Finset.mem_univ _, ?_⟩
  refine Finset.mem_image.mpr ⟨ec.symm, Finset.mem_univ _, ?_⟩
  rw [← hrel]
  exact supportRelabel_symm_relabel er ec S

theorem canonicalShape_of_card_eq_zero
    {S : Finset MatrixEdge} (hcard : S.card = 0) :
    IsCanonicalStarForestShape S := by
  have hS : S = ∅ := Finset.card_eq_zero.mp hcard
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape0)
    (by simp [canonicalStarForestSupports, shape0])
    (Equiv.refl (Fin 3)) (Equiv.refl (Fin 4))
    (by simp [hS, supportRelabel, shape0])

theorem canonicalShape_of_card_eq_one
    {S : Finset MatrixEdge} (hcard : S.card = 1) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_one.mp hcard with ⟨e, hS⟩
  rcases e with ⟨i, j⟩
  let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  let ec : Fin 4 ≃ Fin 4 := Equiv.swap j 0
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape1)
    (by simp [canonicalStarForestSupports, shape1])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape1, er, ec])

theorem canonicalShape_of_card_eq_two
    {S : Finset MatrixEdge} (hcard : S.card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hcard with ⟨e, f, hef, hS⟩
  rcases e with ⟨i, j⟩
  rcases f with ⟨k, l⟩
  by_cases hrow : i = k
  · subst k
    have hcol : j ≠ l := by
      intro h
      exact hef (by simp [h])
    let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
    let ec : Fin 4 ≃ Fin 4 :=
      permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j l
    have her0 : er i = (0 : Fin 3) := by simp [er]
    have hec0 : ec j = (0 : Fin 4) :=
      permSendPairToZeroOne_apply_first (by decide) hcol
    have hec1 : ec l = (1 : Fin 4) :=
      permSendPairToZeroOne_apply_second (0 : Fin 4) (1 : Fin 4) j l
    exact canonicalShape_of_supportRelabel_eq
      (S := S) (T := shape2_row)
      (by simp [canonicalStarForestSupports, shape2_row])
      er ec
      (by
        rw [hS, supportRelabel_eq_image]
        simp [shape2_row, er, ec, her0, hec0, hec1])
  · by_cases hcol : j = l
    · subst l
      let er : Fin 3 ≃ Fin 3 :=
        permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
      let ec : Fin 4 ≃ Fin 4 := Equiv.swap j 0
      have her0 : er i = (0 : Fin 3) :=
        permSendPairToZeroOne_apply_first (by decide) hrow
      have her1 : er k = (1 : Fin 3) :=
        permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
      have hec0 : ec j = (0 : Fin 4) := by simp [ec]
      exact canonicalShape_of_supportRelabel_eq
        (S := S) (T := shape2_col)
        (by simp [canonicalStarForestSupports, shape2_col])
        er ec
        (by
          rw [hS, supportRelabel_eq_image]
          simp [shape2_col, er, ec, her0, her1, hec0])
    · let er : Fin 3 ≃ Fin 3 :=
        permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
      let ec : Fin 4 ≃ Fin 4 :=
        permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j l
      have her0 : er i = (0 : Fin 3) :=
        permSendPairToZeroOne_apply_first (by decide) hrow
      have her1 : er k = (1 : Fin 3) :=
        permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
      have hec0 : ec j = (0 : Fin 4) :=
        permSendPairToZeroOne_apply_first (by decide) hcol
      have hec1 : ec l = (1 : Fin 4) :=
        permSendPairToZeroOne_apply_second (0 : Fin 4) (1 : Fin 4) j l
      exact canonicalShape_of_supportRelabel_eq
        (S := S) (T := shape2_singletons)
        (by simp [canonicalStarForestSupports, shape2_singletons])
        er ec
        (by
          rw [hS, supportRelabel_eq_image]
          simp [shape2_singletons, er, ec, her0, her1, hec0, hec1])

theorem canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_three
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 3) (hrow : (rowNeighbors S i).card = 3) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hrow with
    ⟨j0, j1, j2, hj01, hj02, hj12, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 3 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  have hfiber_eq : (S.filter fun e : MatrixEdge => e.1 = i) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard, hfiber_card])
  have hj0_mem : j0 ∈ rowNeighbors S i := by rw [hneighbors]; simp
  have hj1_mem : j1 ∈ rowNeighbors S i := by rw [hneighbors]; simp
  have hj2_mem : j2 ∈ rowNeighbors S i := by rw [hneighbors]; simp
  have hS :
      S = {((i, j0) : MatrixEdge), (i, j1), (i, j2)} := by
    ext e
    rcases e with ⟨r, c⟩
    constructor
    · intro he
      have hfilter : (r, c) ∈ S.filter (fun e : MatrixEdge => e.1 = i) := by
        simpa [hfiber_eq] using he
      have hri : r = i := (Finset.mem_filter.mp hfilter).2
      have hc : c ∈ rowNeighbors S i := by
        simpa [hri] using he
      rw [hneighbors] at hc
      simp at hc
      rcases hc with rfl | rfl | rfl <;> simp [hri]
    · intro he
      simp at he
      rcases he with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        simpa using hj0_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hj1_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hj2_mem
  let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i = (0 : Fin 3) := by simp [er]
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_row)
    (by simp [canonicalStarForestSupports, shape3_row])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape3_row, er, ec, her0, hec0, hec1, hec2])

/-- Three edges all incident to one column are canonically the three-edge
column star. -/
theorem canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_three
    {S : Finset MatrixEdge} {j : Fin 4}
    (hcard : S.card = 3) (hcol : (colNeighbors S j).card = 3) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hcol with
    ⟨i0, i1, i2, hi01, hi02, hi12, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.2 = j).card = 3 := by
    rw [colFiber_card_eq_colNeighbors_card, hcol]
  have hfiber_eq : (S.filter fun e : MatrixEdge => e.2 = j) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard, hfiber_card])
  have hi0_mem : i0 ∈ colNeighbors S j := by rw [hneighbors]; simp
  have hi1_mem : i1 ∈ colNeighbors S j := by rw [hneighbors]; simp
  have hi2_mem : i2 ∈ colNeighbors S j := by rw [hneighbors]; simp
  have hS :
      S = {((i0, j) : MatrixEdge), (i1, j), (i2, j)} := by
    ext e
    rcases e with ⟨r, c⟩
    constructor
    · intro he
      have hfilter : (r, c) ∈ S.filter (fun e : MatrixEdge => e.2 = j) := by
        simpa [hfiber_eq] using he
      have hcj : c = j := (Finset.mem_filter.mp hfilter).2
      have hr : r ∈ colNeighbors S j := by
        simpa [hcj] using he
      rw [hneighbors] at hr
      simp at hr
      rcases hr with rfl | rfl | rfl <;> simp [hcj]
    · intro he
      simp at he
      rcases he with h | h | h
      · rcases h with ⟨rfl, rfl⟩
        simpa using hi0_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hi1_mem
      · rcases h with ⟨rfl, rfl⟩
        simpa using hi2_mem
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  let ec : Fin 4 ≃ Fin 4 := Equiv.swap j 0
  have her0 : er i0 = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi01 hi02
  have her1 : er i1 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hi12
  have her2 : er i2 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  have hec0 : ec j = (0 : Fin 4) := by simp [ec]
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_col)
    (by simp [canonicalStarForestSupports, shape3_col])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape3_col, er, ec, her0, her1, her2, hec0])

/-- A three-edge star forest with a degree-two row is a row-two star plus a
singleton after relabeling. -/
theorem canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_two
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 3) (hstar : IsSupportStarForest S)
    (hrow : (rowNeighbors S i).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hrow with ⟨j0, j1, hj01, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 2 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.1 = i) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.1 = i)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hk_ne_i : k ≠ i := by
    intro hki
    have hil : (i, l) ∈ S := by simpa [hki] using heS
    exact he_not_fiber (by simp [hil, hki])
  have hi_ne_k : i ≠ k := fun hik => hk_ne_i hik.symm
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hl_ne_j0 : l ≠ j0 := by
    intro hlj0
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, ?_⟩
      · simpa using hj0_mem
      · simpa [hlj0] using heS
      · exact hi_ne_k
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj0_mem (by omega) hcol)
  have hl_ne_j1 : l ≠ j1 := by
    intro hlj1
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, ?_⟩
      · simpa using hj1_mem
      · simpa [hlj1] using heS
      · exact hi_ne_k
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj1_mem (by omega) hcol)
  let T : Finset MatrixEdge := {((i, j0) : MatrixEdge), (i, j1), (k, l)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact heS
  have hT_card : T.card = 3 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    simp [T, h01, h02, h12]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 l
  have her0 : er i = (0 : Fin 3) :=
    permSendPairToZeroOne_apply_first (by decide) hi_ne_k
  have her1 : er k = (1 : Fin 3) :=
    permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01
      (fun h => hl_ne_j0 h.symm)
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide)
      (fun h => hl_ne_j1 h.symm)
  have hec2 : ec l = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 l
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_row_plus_singleton)
    (by simp [canonicalStarForestSupports, shape3_row_plus_singleton])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape3_row_plus_singleton, er, ec, her0, her1, hec0, hec1, hec2])

/-- A three-edge star forest with a degree-two column is a column-two star
plus a singleton after relabeling. -/
theorem canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_two
    {S : Finset MatrixEdge} {j : Fin 4}
    (hcard : S.card = 3) (hstar : IsSupportStarForest S)
    (hcol : (colNeighbors S j).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hcol with ⟨i0, i1, hi01, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.2 = j).card = 2 := by
    rw [colFiber_card_eq_colNeighbors_card, hcol]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.2 = j) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.2 = j)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hl_ne_j : l ≠ j := by
    intro hlj
    have hkj : (k, j) ∈ S := by simpa [hlj] using heS
    exact he_not_fiber (by simp [hkj, hlj])
  have hj_ne_l : j ≠ l := fun hjl => hl_ne_j hjl.symm
  have hi0_mem : (i0, j) ∈ S := by
    have : i0 ∈ colNeighbors S j := by rw [hneighbors]; simp
    simpa using this
  have hi1_mem : (i1, j) ∈ S := by
    have : i1 ∈ colNeighbors S j := by rw [hneighbors]; simp
    simpa using this
  have hk_ne_i0 : k ≠ i0 := by
    intro hki0
    have hrow : 1 < (rowNeighbors S i0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j, ?_, l, ?_, ?_⟩
      · simpa using hi0_mem
      · simpa [hki0] using heS
      · exact hj_ne_l
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hi0_mem hrow (by omega))
  have hk_ne_i1 : k ≠ i1 := by
    intro hki1
    have hrow : 1 < (rowNeighbors S i1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j, ?_, l, ?_, ?_⟩
      · simpa using hi1_mem
      · simpa [hki1] using heS
      · exact hj_ne_l
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hi1_mem hrow (by omega))
  let T : Finset MatrixEdge := {((i0, j) : MatrixEdge), (i1, j), (k, l)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hi0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hi1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact heS
  have hT_card : T.card = 3 := by
    have h01 : ((i0, j) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    have h02 : ((i0, j) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i0 (congrArg Prod.fst h).symm
    have h12 : ((i1, j) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i1 (congrArg Prod.fst h).symm
    simp [T, h01, h02, h12]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 k
  let ec : Fin 4 ≃ Fin 4 :=
    permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j l
  have her0 : er i0 = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi01
      (fun h => hk_ne_i0 h.symm)
  have her1 : er i1 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide)
      (fun h => hk_ne_i1 h.symm)
  have her2 : er k = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 k
  have hec0 : ec j = (0 : Fin 4) :=
    permSendPairToZeroOne_apply_first (by decide) hj_ne_l
  have hec1 : ec l = (1 : Fin 4) :=
    permSendPairToZeroOne_apply_second (0 : Fin 4) (1 : Fin 4) j l
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_col_plus_singleton)
    (by simp [canonicalStarForestSupports, shape3_col_plus_singleton])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape3_col_plus_singleton, er, ec, her0, her1, her2, hec0, hec1])

/-- Three edges with all row and column degrees at most one are the three
singleton components after relabeling. -/
theorem canonicalShape_of_card_eq_three_of_all_degrees_le_one
    {S : Finset MatrixEdge}
    (hcard : S.card = 3)
    (hrowle : ∀ i : Fin 3, (rowNeighbors S i).card ≤ 1)
    (hcolle : ∀ j : Fin 4, (colNeighbors S j).card ≤ 1) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hcard with
    ⟨e0, e1, e2, he01, he02, he12, hS⟩
  rcases e0 with ⟨i0, j0⟩
  rcases e1 with ⟨i1, j1⟩
  rcases e2 with ⟨i2, j2⟩
  have he0_mem : (i0, j0) ∈ S := by rw [hS]; simp
  have he1_mem : (i1, j1) ∈ S := by rw [hS]; simp
  have he2_mem : (i2, j2) ∈ S := by rw [hS]; simp
  have hi01 : i0 ≠ i1 := by
    intro h
    have hj : j0 ≠ j1 := by
      intro hj
      exact he01 (by simp [h, hj])
    have hrow : 1 < (rowNeighbors S i0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j0, ?_, j1, ?_, hj⟩
      · simpa using he0_mem
      · simpa [h] using he1_mem
    exact (not_lt_of_ge (hrowle i0)) hrow
  have hi02 : i0 ≠ i2 := by
    intro h
    have hj : j0 ≠ j2 := by
      intro hj
      exact he02 (by simp [h, hj])
    have hrow : 1 < (rowNeighbors S i0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j0, ?_, j2, ?_, hj⟩
      · simpa using he0_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hrowle i0)) hrow
  have hi12 : i1 ≠ i2 := by
    intro h
    have hj : j1 ≠ j2 := by
      intro hj
      exact he12 (by simp [h, hj])
    have hrow : 1 < (rowNeighbors S i1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨j1, ?_, j2, ?_, hj⟩
      · simpa using he1_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hrowle i1)) hrow
  have hj01 : j0 ≠ j1 := by
    intro h
    have hi : i0 ≠ i1 := hi01
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i1, ?_, hi⟩
      · simpa using he0_mem
      · simpa [h] using he1_mem
    exact (not_lt_of_ge (hcolle j0)) hcol
  have hj02 : j0 ≠ j2 := by
    intro h
    have hi : i0 ≠ i2 := hi02
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i2, ?_, hi⟩
      · simpa using he0_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hcolle j0)) hcol
  have hj12 : j1 ≠ j2 := by
    intro h
    have hi : i1 ≠ i2 := hi12
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i1, ?_, i2, ?_, hi⟩
      · simpa using he1_mem
      · simpa [h] using he2_mem
    exact (not_lt_of_ge (hcolle j1)) hcol
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i0 = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi01 hi02
  have her1 : er i1 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hi12
  have her2 : er i2 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i0 i1 i2
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape3_singletons)
    (by simp [canonicalStarForestSupports, shape3_singletons])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape3_singletons, er, ec, her0, her1, her2, hec0, hec1, hec2])

/-- Structural classification of every three-edge star-forest support. -/
theorem canonicalShape_of_card_eq_three_of_starForest
    {S : Finset MatrixEdge}
    (hcard : S.card = 3) (hstar : IsSupportStarForest S) :
    IsCanonicalStarForestShape S := by
  by_cases hrow3 : ∃ i : Fin 3, (rowNeighbors S i).card = 3
  · rcases hrow3 with ⟨i, hi⟩
    exact canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_three
      hcard hi
  by_cases hcol3 : ∃ j : Fin 4, (colNeighbors S j).card = 3
  · rcases hcol3 with ⟨j, hj⟩
    exact canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_three
      hcard hj
  by_cases hrow2 : ∃ i : Fin 3, (rowNeighbors S i).card = 2
  · rcases hrow2 with ⟨i, hi⟩
    exact canonicalShape_of_card_eq_three_of_rowNeighbors_card_eq_two
      hcard hstar hi
  by_cases hcol2 : ∃ j : Fin 4, (colNeighbors S j).card = 2
  · rcases hcol2 with ⟨j, hj⟩
    exact canonicalShape_of_card_eq_three_of_colNeighbors_card_eq_two
      hcard hstar hj
  apply canonicalShape_of_card_eq_three_of_all_degrees_le_one hcard
  · intro i
    have hle : (rowNeighbors S i).card ≤ 3 := by
      have hfiber_le : (S.filter fun e : MatrixEdge => e.1 = i).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rwa [rowFiber_card_eq_rowNeighbors_card, hcard] at hfiber_le
    have hne2 : (rowNeighbors S i).card ≠ 2 := by
      intro h
      exact hrow2 ⟨i, h⟩
    have hne3 : (rowNeighbors S i).card ≠ 3 := by
      intro h
      exact hrow3 ⟨i, h⟩
    omega
  · intro j
    have hle : (colNeighbors S j).card ≤ 3 := by
      have hfiber_le : (S.filter fun e : MatrixEdge => e.2 = j).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rwa [colFiber_card_eq_colNeighbors_card, hcard] at hfiber_le
    have hne2 : (colNeighbors S j).card ≠ 2 := by
      intro h
      exact hcol2 ⟨j, h⟩
    have hne3 : (colNeighbors S j).card ≠ 3 := by
      intro h
      exact hcol3 ⟨j, h⟩
    omega

/-- Four edges all incident to one row are canonically the four-edge row
star. -/
theorem canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_four
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 4) (hrow : (rowNeighbors S i).card = 4) :
    IsCanonicalStarForestShape S := by
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 4 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  have hfiber_eq : (S.filter fun e : MatrixEdge => e.1 = i) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      (by rw [hcard, hfiber_card])
  have hneigh : rowNeighbors S i = Finset.univ :=
    Finset.eq_univ_of_card (rowNeighbors S i)
      (by simpa [Fintype.card_fin] using hrow)
  have hS :
      S = {((i, 0) : MatrixEdge), (i, 1), (i, 2), (i, 3)} := by
    ext e
    rcases e with ⟨r, c⟩
    constructor
    · intro he
      have hfilter : (r, c) ∈ S.filter (fun e : MatrixEdge => e.1 = i) := by
        simpa [hfiber_eq] using he
      have hri : r = i := (Finset.mem_filter.mp hfilter).2
      fin_cases c <;> simp [hri]
    · intro he
      simp at he
      rcases he with h | h | h | h
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (0 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (1 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (2 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
      · rcases h with ⟨hr, hc⟩
        rw [hr, hc]
        have : (3 : Fin 4) ∈ rowNeighbors S i := by
          rw [hneigh]
          simp
        simpa using this
  let er : Fin 3 ≃ Fin 3 := Equiv.swap i 0
  let ec : Fin 4 ≃ Fin 4 := Equiv.refl (Fin 4)
  have her0 : er i = (0 : Fin 3) := by simp [er]
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_row)
    (by simp [canonicalStarForestSupports, shape4_row])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [shape4_row, er, ec, her0])

/-- A four-edge star forest with a degree-three row is a row-three star plus
a singleton after relabeling. -/
theorem canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_three
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 4) (hstar : IsSupportStarForest S)
    (hrow : (rowNeighbors S i).card = 3) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hrow with
    ⟨j0, j1, j2, hj01, hj02, hj12, hneighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 3 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.1 = i) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.1 = i)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hk_ne_i : k ≠ i := by
    intro hki
    have hil : (i, l) ∈ S := by simpa [hki] using heS
    exact he_not_fiber (by simp [hil, hki])
  have hi_ne_k : i ≠ k := fun hik => hk_ne_i hik.symm
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hj2_mem : (i, j2) ∈ S := by
    have : j2 ∈ rowNeighbors S i := by rw [hneighbors]; simp
    simpa using this
  have hl_ne_j0 : l ≠ j0 := by
    intro hlj0
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, hi_ne_k⟩
      · simpa using hj0_mem
      · simpa [hlj0] using heS
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj0_mem (by omega) hcol)
  have hl_ne_j1 : l ≠ j1 := by
    intro hlj1
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, hi_ne_k⟩
      · simpa using hj1_mem
      · simpa [hlj1] using heS
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj1_mem (by omega) hcol)
  have hl_ne_j2 : l ≠ j2 := by
    intro hlj2
    have hcol : 1 < (colNeighbors S j2).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k, ?_, hi_ne_k⟩
      · simpa using hj2_mem
      · simpa [hlj2] using heS
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj2_mem (by omega) hcol)
  let T : Finset MatrixEdge :=
    {((i, j0) : MatrixEdge), (i, j1), (i, j2), (k, l)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj2_mem
    · rcases he with ⟨rfl, rfl⟩
      exact heS
  have hT_card : T.card = 4 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (i, j2) := by
      intro h
      exact hj02 (congrArg Prod.snd h)
    have h03 : ((i, j0) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (i, j2) := by
      intro h
      exact hj12 (congrArg Prod.snd h)
    have h13 : ((i, j1) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    have h23 : ((i, j2) : MatrixEdge) ≠ (k, l) := by
      intro h
      exact hk_ne_i (congrArg Prod.fst h).symm
    simp [T, h01, h02, h03, h12, h13, h23]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i k
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i = (0 : Fin 3) :=
    permSendPairToZeroOne_apply_first (by decide) hi_ne_k
  have her1 : er k = (1 : Fin 3) :=
    permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i k
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have hec3 : ec l = (3 : Fin 4) := by
    have hne0 : ec l ≠ (0 : Fin 4) := by
      intro h
      have : ec l = ec j0 := by rw [h, hec0]
      exact hl_ne_j0 (ec.injective this)
    have hne1 : ec l ≠ (1 : Fin 4) := by
      intro h
      have : ec l = ec j1 := by rw [h, hec1]
      exact hl_ne_j1 (ec.injective this)
    have hne2 : ec l ≠ (2 : Fin 4) := by
      intro h
      have : ec l = ec j2 := by rw [h, hec2]
      exact hl_ne_j2 (ec.injective this)
    exact fin4_eq_three_of_ne_zero_one_two hne0 hne1 hne2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_row3_plus_singleton)
    (by simp [canonicalStarForestSupports, shape4_row3_plus_singleton])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape4_row3_plus_singleton, er, ec, her0, her1, hec0, hec1, hec2, hec3])

/-- Two degree-two rows in a four-edge star forest are two disjoint row
two-stars after relabeling. -/
theorem canonicalShape_of_card_eq_four_of_two_rowNeighbors_card_eq_two
    {S : Finset MatrixEdge} {i0 i1 : Fin 3}
    (hcard : S.card = 4) (hstar : IsSupportStarForest S)
    (hi01 : i0 ≠ i1)
    (hrow0 : (rowNeighbors S i0).card = 2)
    (hrow1 : (rowNeighbors S i1).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hrow0 with ⟨j0, j1, hj01, hneighbors0⟩
  rcases Finset.card_eq_two.mp hrow1 with ⟨j2, j3, hj23, hneighbors1⟩
  have hj0_mem : (i0, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i0 := by rw [hneighbors0]; simp
    simpa using this
  have hj1_mem : (i0, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i0 := by rw [hneighbors0]; simp
    simpa using this
  have hj2_mem : (i1, j2) ∈ S := by
    have : j2 ∈ rowNeighbors S i1 := by rw [hneighbors1]; simp
    simpa using this
  have hj3_mem : (i1, j3) ∈ S := by
    have : j3 ∈ rowNeighbors S i1 := by rw [hneighbors1]; simp
    simpa using this
  have hj20 : j2 ≠ j0 := by
    intro h
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i1, ?_, hi01⟩
      · simpa using hj0_mem
      · simpa [h] using hj2_mem
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj0_mem (by omega) hcol)
  have hj21 : j2 ≠ j1 := by
    intro h
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i1, ?_, hi01⟩
      · simpa using hj1_mem
      · simpa [h] using hj2_mem
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj1_mem (by omega) hcol)
  have hj30 : j3 ≠ j0 := by
    intro h
    have hcol : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i1, ?_, hi01⟩
      · simpa using hj0_mem
      · simpa [h] using hj3_mem
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj0_mem (by omega) hcol)
  have hj31 : j3 ≠ j1 := by
    intro h
    have hcol : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i0, ?_, i1, ?_, hi01⟩
      · simpa using hj1_mem
      · simpa [h] using hj3_mem
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      hj1_mem (by omega) hcol)
  let T : Finset MatrixEdge :=
    {((i0, j0) : MatrixEdge), (i0, j1), (i1, j2), (i1, j3)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj2_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj3_mem
  have hT_card : T.card = 4 := by
    have h01 : ((i0, j0) : MatrixEdge) ≠ (i0, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i0, j0) : MatrixEdge) ≠ (i1, j2) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    have h03 : ((i0, j0) : MatrixEdge) ≠ (i1, j3) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    have h12 : ((i0, j1) : MatrixEdge) ≠ (i1, j2) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    have h13 : ((i0, j1) : MatrixEdge) ≠ (i1, j3) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    have h23' : ((i1, j2) : MatrixEdge) ≠ (i1, j3) := by
      intro h
      exact hj23 (congrArg Prod.snd h)
    simp [T, h01, h02, h03, h12, h13, h23']
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i0 i1
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have her0 : er i0 = (0 : Fin 3) :=
    permSendPairToZeroOne_apply_first (by decide) hi01
  have her1 : er i1 = (1 : Fin 3) :=
    permSendPairToZeroOne_apply_second (0 : Fin 3) (1 : Fin 3) i0 i1
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01
      (fun h => hj20 h.symm)
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide)
      (fun h => hj21 h.symm)
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have hec3 : ec j3 = (3 : Fin 4) := by
    have hne0 : ec j3 ≠ (0 : Fin 4) := by
      intro h
      have : ec j3 = ec j0 := by rw [h, hec0]
      exact hj30 (ec.injective this)
    have hne1 : ec j3 ≠ (1 : Fin 4) := by
      intro h
      have : ec j3 = ec j1 := by rw [h, hec1]
      exact hj31 (ec.injective this)
    have hne2 : ec j3 ≠ (2 : Fin 4) := by
      intro h
      have : ec j3 = ec j2 := by rw [h, hec2]
      exact hj23 (ec.injective this).symm
    exact fin4_eq_three_of_ne_zero_one_two hne0 hne1 hne2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_two_row2)
    (by simp [canonicalStarForestSupports, shape4_two_row2])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape4_two_row2, er, ec, her0, her1, hec0, hec1, hec2, hec3])

/-- A degree-two row and a degree-two column in a four-edge star forest are
disjoint, giving the mixed row-two/column-two canonical shape. -/
theorem canonicalShape_of_card_eq_four_of_row_col_neighbors_card_eq_two
    {S : Finset MatrixEdge} {i : Fin 3} {j : Fin 4}
    (hcard : S.card = 4) (hstar : IsSupportStarForest S)
    (hrow : (rowNeighbors S i).card = 2)
    (hcol : (colNeighbors S j).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hrow with ⟨j0, j1, hj01, hrow_neighbors⟩
  rcases Finset.card_eq_two.mp hcol with ⟨i0, i1, hi01, hcol_neighbors⟩
  have hrow_gt : 1 < (rowNeighbors S i).card := by omega
  have hcol_gt : 1 < (colNeighbors S j).card := by omega
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hi0_mem : (i0, j) ∈ S := by
    have : i0 ∈ colNeighbors S j := by rw [hcol_neighbors]; simp
    simpa using this
  have hi1_mem : (i1, j) ∈ S := by
    have : i1 ∈ colNeighbors S j := by rw [hcol_neighbors]; simp
    simpa using this
  have hj_ne_j0 : j ≠ j0 := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hj0_mem) hrow_gt hcol_gt)
  have hj_ne_j1 : j ≠ j1 := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hj1_mem) hrow_gt hcol_gt)
  have hi0_ne_i : i0 ≠ i := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hi0_mem) hrow_gt hcol_gt)
  have hi1_ne_i : i1 ≠ i := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hi1_mem) hrow_gt hcol_gt)
  let T : Finset MatrixEdge :=
    {((i, j0) : MatrixEdge), (i, j1), (i0, j), (i1, j)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hi0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hi1_mem
  have hT_card : T.card = 4 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (i0, j) := by
      intro h
      exact hi0_ne_i (congrArg Prod.fst h).symm
    have h03 : ((i, j0) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi1_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (i0, j) := by
      intro h
      exact hi0_ne_i (congrArg Prod.fst h).symm
    have h13 : ((i, j1) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi1_ne_i (congrArg Prod.fst h).symm
    have h23 : ((i0, j) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    simp [T, h01, h02, h03, h12, h13, h23]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i i0 i1
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j
  have hi_ne_i0 : i ≠ i0 := fun h => hi0_ne_i h.symm
  have hi_ne_i1 : i ≠ i1 := fun h => hi1_ne_i h.symm
  have hj0_ne_j : j0 ≠ j := fun h => hj_ne_j0 h.symm
  have hj1_ne_j : j1 ≠ j := fun h => hj_ne_j1 h.symm
  have her0 : er i = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi_ne_i0 hi_ne_i1
  have her1 : er i0 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hi01
  have her2 : er i1 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i i0 i1
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj0_ne_j
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj1_ne_j
  have hec2 : ec j = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_row2_col2)
    (by simp [canonicalStarForestSupports, shape4_row2_col2])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape4_row2_col2, er, ec, her0, her1, her2, hec0, hec1, hec2])

/-- A four-edge support with one degree-two row and otherwise singleton
components has the exceptional `(2,1,1)` shape. -/
theorem canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_two_singletons
    {S : Finset MatrixEdge} {i : Fin 3}
    (hcard : S.card = 4)
    (hrow : (rowNeighbors S i).card = 2)
    (hrowle : ∀ k : Fin 3, k ≠ i → (rowNeighbors S k).card ≤ 1)
    (hcolle : ∀ j : Fin 4, (colNeighbors S j).card ≤ 1) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_two.mp hrow with ⟨j0, j1, hj01, hrow_neighbors⟩
  have hfiber_card : (S.filter fun e : MatrixEdge => e.1 = i).card = 2 := by
    rw [rowFiber_card_eq_rowNeighbors_card, hrow]
  have hcomp_card : (S.filter fun e : MatrixEdge => e.1 ≠ i).card = 2 := by
    have hsplit :=
      Finset.card_filter_add_card_filter_not
        (s := S) (p := fun e : MatrixEdge => e.1 = i)
    rw [hfiber_card, hcard] at hsplit
    have hsplit' : 2 + (S.filter fun e : MatrixEdge => e.1 ≠ i).card = 4 := by
      simpa using hsplit
    omega
  rcases Finset.card_eq_two.mp hcomp_card with
    ⟨e2, e3, he23, hcomp⟩
  rcases e2 with ⟨k0, l0⟩
  rcases e3 with ⟨k1, l1⟩
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hk0_mem_filter : (k0, l0) ∈ S.filter (fun e : MatrixEdge => e.1 ≠ i) := by
    rw [hcomp]
    simp
  have hk1_mem_filter : (k1, l1) ∈ S.filter (fun e : MatrixEdge => e.1 ≠ i) := by
    rw [hcomp]
    simp
  have hk0_mem : (k0, l0) ∈ S := (Finset.mem_filter.mp hk0_mem_filter).1
  have hk1_mem : (k1, l1) ∈ S := (Finset.mem_filter.mp hk1_mem_filter).1
  have hk0_ne_i : k0 ≠ i := (Finset.mem_filter.mp hk0_mem_filter).2
  have hk1_ne_i : k1 ≠ i := (Finset.mem_filter.mp hk1_mem_filter).2
  have hk01 : k0 ≠ k1 := by
    intro h
    have hl : l0 ≠ l1 := by
      intro hl
      exact he23 (by simp [h, hl])
    have hrow_gt : 1 < (rowNeighbors S k0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨l0, ?_, l1, ?_, hl⟩
      · simpa using hk0_mem
      · simpa [h] using hk1_mem
    exact (not_lt_of_ge (hrowle k0 hk0_ne_i)) hrow_gt
  have hl0_ne_j0 : l0 ≠ j0 := by
    intro h
    have hcol_gt : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k0, ?_, ?_⟩
      · simpa using hj0_mem
      · simpa [h] using hk0_mem
      · exact fun hik => hk0_ne_i hik.symm
    exact (not_lt_of_ge (hcolle j0)) hcol_gt
  have hl0_ne_j1 : l0 ≠ j1 := by
    intro h
    have hcol_gt : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k0, ?_, ?_⟩
      · simpa using hj1_mem
      · simpa [h] using hk0_mem
      · exact fun hik => hk0_ne_i hik.symm
    exact (not_lt_of_ge (hcolle j1)) hcol_gt
  have hl1_ne_j0 : l1 ≠ j0 := by
    intro h
    have hcol_gt : 1 < (colNeighbors S j0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k1, ?_, ?_⟩
      · simpa using hj0_mem
      · simpa [h] using hk1_mem
      · exact fun hik => hk1_ne_i hik.symm
    exact (not_lt_of_ge (hcolle j0)) hcol_gt
  have hl1_ne_j1 : l1 ≠ j1 := by
    intro h
    have hcol_gt : 1 < (colNeighbors S j1).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨i, ?_, k1, ?_, ?_⟩
      · simpa using hj1_mem
      · simpa [h] using hk1_mem
      · exact fun hik => hk1_ne_i hik.symm
    exact (not_lt_of_ge (hcolle j1)) hcol_gt
  have hl01 : l0 ≠ l1 := by
    intro h
    have hcol_gt : 1 < (colNeighbors S l0).card := by
      refine Finset.one_lt_card.mpr ?_
      refine ⟨k0, ?_, k1, ?_, hk01⟩
      · simpa using hk0_mem
      · simpa [h] using hk1_mem
    exact (not_lt_of_ge (hcolle l0)) hcol_gt
  let T : Finset MatrixEdge :=
    {((i, j0) : MatrixEdge), (i, j1), (k0, l0), (k1, l1)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hk0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hk1_mem
  have hT_card : T.card = 4 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (k0, l0) := by
      intro h
      exact hk0_ne_i (congrArg Prod.fst h).symm
    have h03 : ((i, j0) : MatrixEdge) ≠ (k1, l1) := by
      intro h
      exact hk1_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (k0, l0) := by
      intro h
      exact hk0_ne_i (congrArg Prod.fst h).symm
    have h13 : ((i, j1) : MatrixEdge) ≠ (k1, l1) := by
      intro h
      exact hk1_ne_i (congrArg Prod.fst h).symm
    have h23 : ((k0, l0) : MatrixEdge) ≠ (k1, l1) := by
      intro h
      exact hk01 (congrArg Prod.fst h)
    simp [T, h01, h02, h03, h12, h13, h23]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i k0 k1
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 l0
  have hi_ne_k0 : i ≠ k0 := fun h => hk0_ne_i h.symm
  have hi_ne_k1 : i ≠ k1 := fun h => hk1_ne_i h.symm
  have hj0_ne_l0 : j0 ≠ l0 := fun h => hl0_ne_j0 h.symm
  have hj1_ne_l0 : j1 ≠ l0 := fun h => hl0_ne_j1 h.symm
  have her0 : er i = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi_ne_k0 hi_ne_k1
  have her1 : er k0 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hk01
  have her2 : er k1 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i k0 k1
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj0_ne_l0
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj1_ne_l0
  have hec2 : ec l0 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 l0
  have hec3 : ec l1 = (3 : Fin 4) := by
    have hne0 : ec l1 ≠ (0 : Fin 4) := by
      intro h
      have : ec l1 = ec j0 := by rw [h, hec0]
      exact hl1_ne_j0 (ec.injective this)
    have hne1 : ec l1 ≠ (1 : Fin 4) := by
      intro h
      have : ec l1 = ec j1 := by rw [h, hec1]
      exact hl1_ne_j1 (ec.injective this)
    have hne2 : ec l1 ≠ (2 : Fin 4) := by
      intro h
      have : ec l1 = ec l0 := by rw [h, hec2]
      exact hl01 (ec.injective this).symm
    exact fin4_eq_three_of_ne_zero_one_two hne0 hne1 hne2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape4_exceptional)
    (by simp [canonicalStarForestSupports, shape4_exceptional])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape4_exceptional, er, ec, her0, her1, her2, hec0, hec1, hec2, hec3])

/-- A four-edge star forest cannot contain a column of degree three: the
remaining edge would give one of the three incident rows degree at least two,
creating a length-three support path. -/
theorem not_colNeighbors_card_eq_three_of_card_eq_four_starForest
    {S : Finset MatrixEdge} {j : Fin 4}
    (hcard : S.card = 4) (hstar : IsSupportStarForest S)
    (hcol : (colNeighbors S j).card = 3) :
    False := by
  have hfiber_card : (S.filter fun e : MatrixEdge => e.2 = j).card = 3 := by
    rw [colFiber_card_eq_colNeighbors_card, hcol]
  obtain ⟨e, heS, he_not_fiber⟩ :
      ∃ e ∈ S, e ∉ S.filter (fun e : MatrixEdge => e.2 = j) :=
    Finset.exists_mem_notMem_of_card_lt_card (s := S.filter fun e : MatrixEdge => e.2 = j)
      (t := S) (by omega)
  rcases e with ⟨k, l⟩
  have hl_ne_j : l ≠ j := by
    intro hlj
    have hkj : (k, j) ∈ S := by simpa [hlj] using heS
    exact he_not_fiber (by simp [hkj, hlj])
  have hneigh : colNeighbors S j = Finset.univ :=
    Finset.eq_univ_of_card (colNeighbors S j)
      (by simpa [Fintype.card_fin] using hcol)
  have hkj : (k, j) ∈ S := by
    have : k ∈ colNeighbors S j := by
      rw [hneigh]
      simp
    simpa using this
  have hrow_gt : 1 < (rowNeighbors S k).card := by
    refine Finset.one_lt_card.mpr ?_
    refine ⟨j, ?_, l, ?_, ?_⟩
    · simpa using hkj
    · simpa using heS
    · exact fun hjl => hl_ne_j hjl.symm
  exact hstar (hasSupportPath3_of_edge_one_lt_degrees
    hkj hrow_gt (by omega))

/-- Structural classification of every four-edge star-forest support. -/
theorem canonicalShape_of_card_eq_four_of_starForest
    {S : Finset MatrixEdge}
    (hcard : S.card = 4) (hstar : IsSupportStarForest S) :
    IsCanonicalStarForestShape S := by
  by_cases hrow4 : ∃ i : Fin 3, (rowNeighbors S i).card = 4
  · rcases hrow4 with ⟨i, hi⟩
    exact canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_four
      hcard hi
  by_cases hrow3 : ∃ i : Fin 3, (rowNeighbors S i).card = 3
  · rcases hrow3 with ⟨i, hi⟩
    exact canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_three
      hcard hstar hi
  obtain ⟨i, hi_gt⟩ :
      ∃ i : Fin 3, 1 < (rowNeighbors S i).card :=
    exists_one_lt_rowNeighbors_card_of_three_lt_card (by omega)
  have hi_le4 : (rowNeighbors S i).card ≤ 4 := by
    have hfiber_le : (S.filter fun e : MatrixEdge => e.1 = i).card ≤ S.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rwa [rowFiber_card_eq_rowNeighbors_card, hcard] at hfiber_le
  have hi_ne3 : (rowNeighbors S i).card ≠ 3 := by
    intro h
    exact hrow3 ⟨i, h⟩
  have hi_ne4 : (rowNeighbors S i).card ≠ 4 := by
    intro h
    exact hrow4 ⟨i, h⟩
  have hi_eq2 : (rowNeighbors S i).card = 2 := by
    omega
  by_cases hrow2_other :
      ∃ k : Fin 3, k ≠ i ∧ (rowNeighbors S k).card = 2
  · rcases hrow2_other with ⟨k, hki, hk⟩
    exact canonicalShape_of_card_eq_four_of_two_rowNeighbors_card_eq_two
      hcard hstar hki.symm hi_eq2 hk
  by_cases hcol2 : ∃ j : Fin 4, (colNeighbors S j).card = 2
  · rcases hcol2 with ⟨j, hj⟩
    exact canonicalShape_of_card_eq_four_of_row_col_neighbors_card_eq_two
      hcard hstar hi_eq2 hj
  apply canonicalShape_of_card_eq_four_of_rowNeighbors_card_eq_two_singletons
    hcard hi_eq2
  · intro k hki
    have hle4 : (rowNeighbors S k).card ≤ 4 := by
      have hfiber_le : (S.filter fun e : MatrixEdge => e.1 = k).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      rwa [rowFiber_card_eq_rowNeighbors_card, hcard] at hfiber_le
    have hne2 : (rowNeighbors S k).card ≠ 2 := by
      intro h
      exact hrow2_other ⟨k, hki, h⟩
    have hne3 : (rowNeighbors S k).card ≠ 3 := by
      intro h
      exact hrow3 ⟨k, h⟩
    have hne4 : (rowNeighbors S k).card ≠ 4 := by
      intro h
      exact hrow4 ⟨k, h⟩
    omega
  · intro j
    have hle3 : (colNeighbors S j).card ≤ 3 := by
      simpa [Fintype.card_fin] using
        (Finset.card_le_univ (colNeighbors S j))
    have hne2 : (colNeighbors S j).card ≠ 2 := by
      intro h
      exact hcol2 ⟨j, h⟩
    have hne3 : (colNeighbors S j).card ≠ 3 := by
      intro h
      exact not_colNeighbors_card_eq_three_of_card_eq_four_starForest
        hcard hstar h
    omega

/-- A five-edge star forest with a degree-three row and a degree-two column
has the unique canonical `(3,2)` shape. -/
theorem canonicalShape_of_card_eq_five_of_row_three_col_two
    {S : Finset MatrixEdge} {i : Fin 3} {j : Fin 4}
    (hcard : S.card = 5) (hstar : IsSupportStarForest S)
    (hrow : (rowNeighbors S i).card = 3)
    (hcol : (colNeighbors S j).card = 2) :
    IsCanonicalStarForestShape S := by
  rcases Finset.card_eq_three.mp hrow with
    ⟨j0, j1, j2, hj01, hj02, hj12, hrow_neighbors⟩
  rcases Finset.card_eq_two.mp hcol with ⟨i0, i1, hi01, hcol_neighbors⟩
  have hrow_gt : 1 < (rowNeighbors S i).card := by omega
  have hcol_gt : 1 < (colNeighbors S j).card := by omega
  have hj0_mem : (i, j0) ∈ S := by
    have : j0 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hj1_mem : (i, j1) ∈ S := by
    have : j1 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hj2_mem : (i, j2) ∈ S := by
    have : j2 ∈ rowNeighbors S i := by rw [hrow_neighbors]; simp
    simpa using this
  have hi0_mem : (i0, j) ∈ S := by
    have : i0 ∈ colNeighbors S j := by rw [hcol_neighbors]; simp
    simpa using this
  have hi1_mem : (i1, j) ∈ S := by
    have : i1 ∈ colNeighbors S j := by rw [hcol_neighbors]; simp
    simpa using this
  have hj_ne_j0 : j ≠ j0 := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hj0_mem) hrow_gt hcol_gt)
  have hj_ne_j1 : j ≠ j1 := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hj1_mem) hrow_gt hcol_gt)
  have hj_ne_j2 : j ≠ j2 := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hj2_mem) hrow_gt hcol_gt)
  have hi0_ne_i : i0 ≠ i := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hi0_mem) hrow_gt hcol_gt)
  have hi1_ne_i : i1 ≠ i := by
    intro h
    exact hstar (hasSupportPath3_of_edge_one_lt_degrees
      (by simpa [h] using hi1_mem) hrow_gt hcol_gt)
  let T : Finset MatrixEdge :=
    {((i, j0) : MatrixEdge), (i, j1), (i, j2), (i0, j), (i1, j)}
  have hT_subset : T ⊆ S := by
    intro e he
    simp [T] at he
    rcases he with he | he | he | he | he
    · rcases he with ⟨rfl, rfl⟩
      exact hj0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj1_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hj2_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hi0_mem
    · rcases he with ⟨rfl, rfl⟩
      exact hi1_mem
  have hT_card : T.card = 5 := by
    have h01 : ((i, j0) : MatrixEdge) ≠ (i, j1) := by
      intro h
      exact hj01 (congrArg Prod.snd h)
    have h02 : ((i, j0) : MatrixEdge) ≠ (i, j2) := by
      intro h
      exact hj02 (congrArg Prod.snd h)
    have h03 : ((i, j0) : MatrixEdge) ≠ (i0, j) := by
      intro h
      exact hi0_ne_i (congrArg Prod.fst h).symm
    have h04 : ((i, j0) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi1_ne_i (congrArg Prod.fst h).symm
    have h12 : ((i, j1) : MatrixEdge) ≠ (i, j2) := by
      intro h
      exact hj12 (congrArg Prod.snd h)
    have h13 : ((i, j1) : MatrixEdge) ≠ (i0, j) := by
      intro h
      exact hi0_ne_i (congrArg Prod.fst h).symm
    have h14 : ((i, j1) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi1_ne_i (congrArg Prod.fst h).symm
    have h23 : ((i, j2) : MatrixEdge) ≠ (i0, j) := by
      intro h
      exact hi0_ne_i (congrArg Prod.fst h).symm
    have h24 : ((i, j2) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi1_ne_i (congrArg Prod.fst h).symm
    have h34 : ((i0, j) : MatrixEdge) ≠ (i1, j) := by
      intro h
      exact hi01 (congrArg Prod.fst h)
    simp [T, h01, h02, h03, h04, h12, h13, h14, h23, h24, h34]
  have hS : S = T := by
    exact (Finset.eq_of_subset_of_card_le hT_subset (by omega)).symm
  let er : Fin 3 ≃ Fin 3 :=
    permSendTripleToZeroOneTwo (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i i0 i1
  let ec : Fin 4 ≃ Fin 4 :=
    permSendTripleToZeroOneTwo (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have hi_ne_i0 : i ≠ i0 := fun h => hi0_ne_i h.symm
  have hi_ne_i1 : i ≠ i1 := fun h => hi1_ne_i h.symm
  have her0 : er i = (0 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hi_ne_i0 hi_ne_i1
  have her1 : er i0 = (1 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hi01
  have her2 : er i1 = (2 : Fin 3) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 3) (1 : Fin 3) (2 : Fin 3) i i0 i1
  have hec0 : ec j0 = (0 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_first (by decide) (by decide) hj01 hj02
  have hec1 : ec j1 = (1 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_second (by decide) hj12
  have hec2 : ec j2 = (2 : Fin 4) :=
    permSendTripleToZeroOneTwo_apply_third (0 : Fin 4) (1 : Fin 4) (2 : Fin 4) j0 j1 j2
  have hec3 : ec j = (3 : Fin 4) := by
    have hne0 : ec j ≠ (0 : Fin 4) := by
      intro h
      have : ec j = ec j0 := by rw [h, hec0]
      exact hj_ne_j0 (ec.injective this)
    have hne1 : ec j ≠ (1 : Fin 4) := by
      intro h
      have : ec j = ec j1 := by rw [h, hec1]
      exact hj_ne_j1 (ec.injective this)
    have hne2 : ec j ≠ (2 : Fin 4) := by
      intro h
      have : ec j = ec j2 := by rw [h, hec2]
      exact hj_ne_j2 (ec.injective this)
    exact fin4_eq_three_of_ne_zero_one_two hne0 hne1 hne2
  exact canonicalShape_of_supportRelabel_eq
    (S := S) (T := shape5_row3_col2)
    (by simp [canonicalStarForestSupports, shape5_row3_col2])
    er ec
    (by
      rw [hS, supportRelabel_eq_image]
      simp [T, shape5_row3_col2, er, ec, her0, her1, her2, hec0, hec1, hec2, hec3])

/-- Structural classification of every five-edge star-forest support. -/
theorem canonicalShape_of_card_eq_five_of_starForest
    {S : Finset MatrixEdge}
    (hcard : S.card = 5) (hstar : IsSupportStarForest S) :
    IsCanonicalStarForestShape S := by
  have hrow_exists :
      ∃ i : Fin 3, 1 < (rowNeighbors S i).card :=
    exists_one_lt_rowNeighbors_card_of_three_lt_card (by omega)
  have hcol_exists :
      ∃ j : Fin 4, 1 < (colNeighbors S j).card :=
    exists_one_lt_colNeighbors_card_of_four_lt_card (by omega)
  let a := (highRows S).card
  let b := (highCols S).card
  have ha_pos : 0 < a := by
    rcases hrow_exists with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simpa [a] using hi⟩
  have hb_pos : 0 < b := by
    rcases hcol_exists with ⟨j, hj⟩
    exact Finset.card_pos.mpr ⟨j, by simpa [b] using hj⟩
  have ha_le : a ≤ 3 := by
    simpa [a] using highRows_card_le_three S
  have hb_le : b ≤ 4 := by
    simpa [b] using highCols_card_le_four S
  have hrow_bound : 5 ≤ a * (4 - b) + (3 - a) := by
    simpa [a, b, hcard] using
      card_le_row_high_bound_of_starForest (S := S) hstar
  have hcol_bound : 5 ≤ b * (3 - a) + (4 - b) := by
    simpa [a, b, hcard] using
      card_le_col_high_bound_of_starForest (S := S) hstar
  have hab : a = 1 ∧ b = 1 := by
    interval_cases a <;> interval_cases b <;> omega
  have ha_eq : (highRows S).card = 1 := by simpa [a] using hab.1
  have hb_eq : (highCols S).card = 1 := by simpa [b] using hab.2
  obtain ⟨i, hi_high⟩ : (highRows S).Nonempty := by
    exact Finset.card_pos.mp (by simp [ha_eq])
  obtain ⟨j, hj_high⟩ : (highCols S).Nonempty := by
    exact Finset.card_pos.mp (by simp [hb_eq])
  have hi_gt : 1 < (rowNeighbors S i).card := by
    simpa using hi_high
  have hj_gt : 1 < (colNeighbors S j).card := by
    simpa using hj_high
  have hi_le3 : (rowNeighbors S i).card ≤ 3 := by
    have hle :=
      rowNeighbors_card_le_lowCols_card_of_highRow_starForest
        (S := S) hstar hi_high
    rw [lowCols_card_eq] at hle
    simpa [hb_eq] using hle
  have hj_le2 : (colNeighbors S j).card ≤ 2 := by
    have hle :=
      colNeighbors_card_le_lowRows_card_of_highCol_starForest
        (S := S) hstar hj_high
    rw [lowRows_card_eq] at hle
    simpa [ha_eq] using hle
  have hj_eq2 : (colNeighbors S j).card = 2 := by
    omega
  have hrow_other_le :
      ∀ k : Fin 3, k ≠ i → (rowNeighbors S k).card ≤ 1 := by
    intro k hki
    have hk_not_high : k ∉ highRows S := by
      intro hk
      have htwo : 1 < (highRows S).card := by
        exact Finset.one_lt_card.mpr ⟨i, hi_high, k, hk, hki.symm⟩
      omega
    exact Nat.le_of_not_gt fun hkgt =>
      hk_not_high ((mem_highRows_iff S k).2 hkgt)
  have hi_ne2 : (rowNeighbors S i).card ≠ 2 := by
    intro hi2
    have hsum := card_eq_sum_rowNeighbors_card S
    rw [Fin.sum_univ_three, hcard] at hsum
    fin_cases i
    · have h1 := hrow_other_le 1 (by decide)
      have h2 := hrow_other_le 2 (by decide)
      simp at hi2 hsum
      omega
    · have h0 := hrow_other_le 0 (by decide)
      have h2 := hrow_other_le 2 (by decide)
      simp at hi2 hsum
      omega
    · have h0 := hrow_other_le 0 (by decide)
      have h1 := hrow_other_le 1 (by decide)
      simp at hi2 hsum
      omega
  have hi_eq3 : (rowNeighbors S i).card = 3 := by
    omega
  exact canonicalShape_of_card_eq_five_of_row_three_col_two
    hcard hstar hi_eq3 hj_eq2

/-- Forward form of the finite classification. -/
theorem canonicalShape_of_isSupportStarForest
    {S : Finset MatrixEdge}
    (hS : IsSupportStarForest S) :
    IsCanonicalStarForestShape S := by
  have hle : S.card ≤ 5 := support_card_le_five_of_starForest S hS
  interval_cases hcard : S.card
  · exact canonicalShape_of_card_eq_zero hcard
  · exact canonicalShape_of_card_eq_one hcard
  · exact canonicalShape_of_card_eq_two hcard
  · exact canonicalShape_of_card_eq_three_of_starForest hcard hS
  · exact canonicalShape_of_card_eq_four_of_starForest hcard hS
  · exact canonicalShape_of_card_eq_five_of_starForest hcard hS

end Lollipop

/-!
Proof component 6: `Matrix.Strategy`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Section 5 proof strategy.

This module records the exact dependency split of the manuscript's matrix
theorem.  The two remaining global ingredients are:

* support compression to star-forest normal form without increasing `F`;
* the lower bound for matrices already in star-forest normal form.

Once those two statements are proved, `MatrixTheoremStatement` follows by a
short checked argument.
-/

namespace Lollipop

/-- Manuscript Lemma 5.1: support compression to star-forest normal form. -/
def SupportCompressionStatement : Prop :=
  ∀ U : NatMatrix,
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V ≤ matrixFNat U ∧
      IsSupportStarForest (supportOfNat V)

/-- Manuscript Lemma 5.2: the matrix bound on star-forest supports. -/
def StarForestMinimumStatement : Prop :=
  ∀ U : NatMatrix,
    IsSupportStarForest (supportOfNat U) →
      matrixFNat U ≥ concreteM (matrixTotalNat U)

/-- A one-step descent statement: every non-star support has a total-preserving
move that does not increase `F` and strictly decreases support cardinality. -/
def SupportDescentStepStatement : Prop :=
  ∀ U : NatMatrix,
    ¬ IsSupportStarForest (supportOfNat U) →
      ∃ V : NatMatrix,
        matrixTotalNat V = matrixTotalNat U ∧
        matrixFNat V ≤ matrixFNat U ∧
        supportCardNat V < supportCardNat U

/-- A checked termination argument for support compression.  Thus the global
iteration in the manuscript reduces to the one-step descent lemma. -/
theorem support_compression_of_descent_step
    (hstep : SupportDescentStepStatement) :
    SupportCompressionStatement := by
  intro U
  let C : NatMatrix → Prop := fun U =>
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V ≤ matrixFNat U ∧
      IsSupportStarForest (supportOfNat V)
  change C U
  refine (measure supportCardNat).wf.induction U ?_
  intro U ih
  by_cases hstar : IsSupportStarForest (supportOfNat U)
  · exact ⟨U, rfl, le_rfl, hstar⟩
  · rcases hstep U hstar with ⟨V, htotal, hF, hcard⟩
    rcases ih V hcard with ⟨W, hWtotal, hWF, hWstar⟩
    refine ⟨W, ?_, ?_, hWstar⟩
    · rw [hWtotal, htotal]
    · linarith

/-- The Section 5 matrix theorem follows from support compression and the
star-forest minimum. -/
theorem matrix_theorem_of_support_compression_and_star_forest
    (hcompress : SupportCompressionStatement)
    (hstar : StarForestMinimumStatement) :
    MatrixTheoremStatement := by
  intro U
  rcases hcompress U with ⟨V, htotal, hF, hVstar⟩
  have hV := hstar V hVstar
  rw [htotal] at hV
  linarith

/-- The matrix theorem follows from one-step descent plus the star-forest
minimum. -/
theorem matrix_theorem_of_descent_step_and_star_forest
    (hstep : SupportDescentStepStatement)
    (hstar : StarForestMinimumStatement) :
    MatrixTheoremStatement := by
  exact matrix_theorem_of_support_compression_and_star_forest
    (support_compression_of_descent_step hstep) hstar

/-- For total mass at least four, the manuscript's non-exceptional
star-forest estimate `F(U) >= n^2 / 2` is enough. -/
theorem matrix_theorem_of_half_sq_bound_of_total_ge_four
    (U : NatMatrix)
    (hlarge : 4 ≤ matrixTotalNat U)
    (hhalf : (matrixTotalNat U : ℚ)^2 / 2 ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  have hM := concreteM_le_half_sq_of_ge_four
    (n := matrixTotalNat U) hlarge
  linarith

/-- A combined branch lemma for the star-forest proof: either the total is
small, or the `n^2 / 2` estimate is enough. -/
theorem matrix_theorem_of_small_or_half_sq_bound
    (U : NatMatrix)
    (hbranch :
      matrixTotalNat U ≤ 3 ∨
        4 ≤ matrixTotalNat U ∧
          (matrixTotalNat U : ℚ)^2 / 2 ≤ matrixFNat U) :
    matrixFNat U ≥ concreteM (matrixTotalNat U) := by
  rcases hbranch with hsmall | hlarge
  · exact matrix_theorem_of_total_le_three U hsmall
  · exact matrix_theorem_of_half_sq_bound_of_total_ge_four U
      hlarge.1 hlarge.2

end Lollipop



/-!
Compression inequalities needed by the support-descent proof.
-/


/-!
Local algebra for the `3 x 4` matrix compression proof.

The global support-compression theorem still requires graph-theoretic
bookkeeping: finding cycles/paths/double-stars and iterating terminating
operations.  This file formalizes the local polynomial identities used by that
argument.
-/

namespace Lollipop

/-- The part of `F` affected by alternating compression on a four-edge path:
only the two endpoint vertex sums and the four changing edge squares matter. -/
def pathCompressionPart
    (R S x1 x2 x3 x4 eps : ℚ) : ℚ :=
  (R + eps)^2 + (S - eps)^2 -
    (1 / 2 : ℚ) *
      ((x1 + eps)^2 + (x2 - eps)^2 + (x3 + eps)^2 + (x4 - eps)^2)

/-- Four-edge path compression is linear in the compression parameter.  This
checks the manuscript's `2 - (1/2) * 4 = 0` coefficient calculation. -/
theorem pathCompressionPart_sub_zero
    (R S x1 x2 x3 x4 eps : ℚ) :
    pathCompressionPart R S x1 x2 x3 x4 eps -
      pathCompressionPart R S x1 x2 x3 x4 0 =
      eps * (2 * R - 2 * S - x1 + x2 - x3 + x4) := by
  unfold pathCompressionPart
  ring

/-- The part of `F` affected by alternating compression around a four-cycle,
after row and column sums have cancelled out. -/
def cycleCompressionSquarePart
    (x1 x2 x3 x4 eps : ℚ) : ℚ :=
  - (1 / 2 : ℚ) *
    ((x1 + eps)^2 + (x2 - eps)^2 + (x3 + eps)^2 + (x4 - eps)^2)

/-- Four-cycle compression is a concave quadratic in the compression
parameter.  Longer even cycles have the same sign pattern with a more negative
quadratic coefficient. -/
theorem cycleCompressionSquarePart_sub_zero
    (x1 x2 x3 x4 eps : ℚ) :
    cycleCompressionSquarePart x1 x2 x3 x4 eps -
      cycleCompressionSquarePart x1 x2 x3 x4 0 =
      eps * (-x1 + x2 - x3 + x4) - 2 * eps^2 := by
  unfold cycleCompressionSquarePart
  ring

/-- Relevant contribution of a double-star before deleting the central edge.
`A` and `B` are the sums of the other leaf-edge masses on the two sides. -/
def doubleStarOld (A B x y z : ℚ) : ℚ :=
  (3 / 2 : ℚ) * (x^2 + y^2 + z^2) +
    2 * (x * y + y * z + y * A + y * B + x * A + z * B)

/-- Contribution after moving the central mass `y` to the `x`-leaf edge. -/
def doubleStarMoveToX (A B x y z : ℚ) : ℚ :=
  (3 / 2 : ℚ) * ((x + y)^2 + z^2) +
    2 * ((x + y) * A + z * B)

/-- Contribution after moving the central mass `y` to the `z`-leaf edge. -/
def doubleStarMoveToZ (A B x y z : ℚ) : ℚ :=
  (3 / 2 : ℚ) * (x^2 + (z + y)^2) +
    2 * (x * A + (z + y) * B)

/-- First double-star deletion identity from the manuscript. -/
theorem doubleStarOld_sub_moveToX
    (A B x y z : ℚ) :
    doubleStarOld A B x y z - doubleStarMoveToX A B x y z =
      y * (2 * B + 2 * z - x) := by
  unfold doubleStarOld doubleStarMoveToX
  ring

/-- Second double-star deletion identity from the manuscript. -/
theorem doubleStarOld_sub_moveToZ
    (A B x y z : ℚ) :
    doubleStarOld A B x y z - doubleStarMoveToZ A B x y z =
      y * (2 * A + 2 * x - z) := by
  unfold doubleStarOld doubleStarMoveToZ
  ring

/-- At least one of the two double-star coefficients is nonnegative. -/
theorem doubleStar_coeff_nonneg
    {A B x z : ℚ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (_hx0 : 0 ≤ x) (hz0 : 0 ≤ z) :
    0 ≤ 2 * B + 2 * z - x ∨
      0 ≤ 2 * A + 2 * x - z := by
  by_contra h
  push Not at h
  have hx : x > 2 * z := by nlinarith
  have hz : z > 2 * x := by nlinarith
  nlinarith

/-- Consequently one double-star deletion does not increase `F`, provided the
central mass is nonnegative. -/
theorem doubleStar_some_move_not_increasing
    {A B x y z : ℚ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx0 : 0 ≤ x) (hy : 0 ≤ y) (hz0 : 0 ≤ z) :
    doubleStarMoveToX A B x y z ≤ doubleStarOld A B x y z ∨
      doubleStarMoveToZ A B x y z ≤ doubleStarOld A B x y z := by
  rcases doubleStar_coeff_nonneg hA hB hx0 hz0 with hcoef | hcoef
  · left
    rw [← sub_nonneg, doubleStarOld_sub_moveToX]
    exact mul_nonneg hy hcoef
  · right
    rw [← sub_nonneg, doubleStarOld_sub_moveToZ]
    exact mul_nonneg hy hcoef

/-- Cost of a two-edge star of masses `a,b`. -/
def twoEdgeStarCost (a b : ℚ) : ℚ :=
  (a + b)^2 + (1 / 2 : ℚ) * (a^2 + b^2)

/-- The degree-two star efficiency inequality, specialized to the only
nontrivial star degree needed by the exceptional normal form. -/
theorem twoEdgeStarCost_efficiency (a b : ℚ) :
    (5 / 4 : ℚ) * (a + b)^2 ≤ twoEdgeStarCost a b := by
  unfold twoEdgeStarCost
  nlinarith [sq_nonneg (a - b)]

/-- The exceptional `(2,1,1)` star forest has exactly the four-cluster cost
from the definition of `M`. -/
theorem exceptionalStarCost_eq_quadCost (a b c d : ℚ) :
    twoEdgeStarCost a b + (3 / 2 : ℚ) * c^2 + (3 / 2 : ℚ) * d^2 =
      quadCost a b c d := by
  unfold twoEdgeStarCost quadCost
  ring

/-- Cost of a star with `t` edge masses. -/
def starCostFin {t : ℕ} (z : Fin t → ℚ) : ℚ :=
  (∑ i : Fin t, z i)^2 + (1 / 2 : ℚ) * ∑ i : Fin t, (z i)^2

/-- A star component always costs at least the square of its total mass. -/
theorem starCostFin_ge_total_sq {t : ℕ} (z : Fin t → ℚ) :
    (∑ i : Fin t, z i)^2 ≤ starCostFin z := by
  have hsumsq : 0 ≤ ∑ i : Fin t, (z i)^2 := by
    exact Finset.sum_nonneg fun i _hi => sq_nonneg (z i)
  unfold starCostFin
  nlinarith

/-- A one-edge star has cost `3/2` times the square of its mass. -/
theorem starCostFin_one (z : Fin 1 → ℚ) :
    starCostFin z = (3 / 2 : ℚ) * (∑ i : Fin 1, z i)^2 := by
  simp [starCostFin]
  ring

/-- The lower bound used when a star forest has at most two components. -/
theorem two_component_half_bound
    {s₀ s₁ c₀ c₁ : ℚ}
    (hc₀ : s₀^2 ≤ c₀) (hc₁ : s₁^2 ≤ c₁) :
    (s₀ + s₁)^2 / 2 ≤ c₀ + c₁ := by
  nlinarith [sq_nonneg (s₀ - s₁)]

/-- The lower bound used for three singleton components. -/
theorem three_singleton_component_half_bound
    {s₀ s₁ s₂ c₀ c₁ c₂ : ℚ}
    (hc₀ : (3 / 2 : ℚ) * s₀^2 ≤ c₀)
    (hc₁ : (3 / 2 : ℚ) * s₁^2 ≤ c₁)
    (hc₂ : (3 / 2 : ℚ) * s₂^2 ≤ c₂) :
    (s₀ + s₁ + s₂)^2 / 2 ≤ c₀ + c₁ + c₂ := by
  nlinarith [sq_nonneg (s₀ - s₁), sq_nonneg (s₀ - s₂),
    sq_nonneg (s₁ - s₂)]

/-- General Cauchy efficiency inequality for a star component:
`s^2 + (1/2) sum z_i^2 >= (1 + 1/(2t)) s^2`.
This is the formal version of equation (13) in the manuscript. -/
theorem starCostFin_efficiency {t : ℕ} (ht : 0 < t) (z : Fin t → ℚ) :
    (1 + 1 / (2 * (t : ℚ))) * (∑ i : Fin t, z i)^2 ≤
      starCostFin z := by
  have htq : 0 < (t : ℚ) := by exact_mod_cast ht
  have hcauchy :
      (∑ i : Fin t, z i)^2 ≤
        (t : ℚ) * ∑ i : Fin t, (z i)^2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := Finset.univ) (f := fun i : Fin t => z i))
  unfold starCostFin
  field_simp [htq.ne']
  nlinarith

/-- Efficiency parameter for a star of degree `t`. -/
def starEta (t : ℕ) : ℚ :=
  (2 * (t : ℚ)) / (2 * (t : ℚ) + 1)

/-- Every star efficiency parameter is at most `1`. -/
theorem starEta_le_one (t : ℕ) : starEta t ≤ 1 := by
  unfold starEta
  have hden : 0 < (2 * (t : ℚ) + 1) := by positivity
  rw [div_le_one hden]
  linarith

/-- With at most two star components, the sum of the efficiency parameters is
at most `2`. -/
theorem starGamma_le_two_of_components_le_two
    {m : ℕ} (t : Fin m → ℕ) (hm : m ≤ 2) :
    (∑ i : Fin m, starEta (t i)) ≤ 2 := by
  calc
    (∑ i : Fin m, starEta (t i)) ≤ ∑ _i : Fin m, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact starEta_le_one (t i)
    _ = (m : ℚ) := by simp
    _ ≤ 2 := by exact_mod_cast hm

/-- For three positive star components using at most seven vertices, either
the efficiency sum is at most `2`, or the degree list is the exceptional
`(2,1,1)` pattern up to order. -/
theorem starGamma_three_le_two_or_exceptional
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hverts : (a + 1) + (b + 1) + (c + 1) ≤ 7) :
    starEta a + starEta b + starEta c ≤ 2 ∨
      (a = 2 ∧ b = 1 ∧ c = 1) ∨
      (a = 1 ∧ b = 2 ∧ c = 1) ∨
      (a = 1 ∧ b = 1 ∧ c = 2) := by
  have ha_le : a ≤ 2 := by omega
  have hb_le : b ≤ 2 := by omega
  have hc_le : c ≤ 2 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    norm_num [starEta] at *

end Lollipop

/-!
The complete support-descent proof used by Lemma 7.2 follows here.  The
final matrix-theorem assembly is deliberately left to Theorem 7.1.
-/


set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
Finite support-descent bookkeeping for the `3 x 4` matrix theorem.

The local polynomial moves live in `Lollipop.Matrix.LocalMoves`.  This file
adds the finite graph classification needed to apply those moves to an
arbitrary non-star support: up to row/column relabeling, such a support
contains a canonical four-cycle, a row-oriented four-edge path, a
column-oriented four-edge path, or a bounded double-star configuration.
-/

namespace Lollipop

open BigOperators

/-- Canonical four-cycle support used by `cycleMove`. -/
def descentCycleSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (1 : Fin 4))}

/-- Canonical row-oriented four-edge path support used by `pathMove`. -/
def descentRowPathSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((1 : Fin 3), (0 : Fin 4)),
    ((1 : Fin 3), (1 : Fin 4)), ((2 : Fin 3), (1 : Fin 4))}

/-- Canonical column-oriented four-edge path support. -/
def descentColPathSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (1 : Fin 4)), ((1 : Fin 3), (2 : Fin 4))}

/-- The three required edges of the canonical double-star branch. -/
def descentDoubleStarCore : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (0 : Fin 4))}

/-- The allowed support envelope for the canonical double-star branch,
including possible disconnected leftover edges on the unused row/columns. -/
def descentDoubleStarSupport : Finset MatrixEdge :=
  {((0 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (1 : Fin 4)),
    ((1 : Fin 3), (0 : Fin 4)), ((0 : Fin 3), (2 : Fin 4)),
    ((0 : Fin 3), (3 : Fin 4)), ((2 : Fin 3), (0 : Fin 4)),
    ((2 : Fin 3), (2 : Fin 4)), ((2 : Fin 3), (3 : Fin 4))}

/-- Relabeling preserves support cardinality. -/
theorem supportRelabel_card :
    ∀ (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
      (S : Finset MatrixEdge),
        (supportRelabel er ec S).card = S.card := by
  intro er ec S
  let f : MatrixEdge → MatrixEdge := fun e => (er e.1, ec e.2)
  have hf : Function.Injective f := by
    intro a b h
    exact Prod.ext (er.injective (congrArg Prod.fst h))
      (ec.injective (congrArg Prod.snd h))
  have hrel : supportRelabel er ec S = S.image f := by
    ext e
    constructor
    · intro he
      refine Finset.mem_image.mpr ?_
      refine ⟨(er.symm e.1, ec.symm e.2), ?_, ?_⟩
      · simpa [supportRelabel] using he
      · simp [f]
    · intro he
      rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
      simp [supportRelabel, f, ha]
  rw [hrel]
  exact Finset.card_image_of_injective S hf

/-- Relabeling a natural matrix preserves support cardinality. -/
theorem supportCardNat_relabelNatMatrix
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix) :
    supportCardNat (relabelNatMatrix er ec U) = supportCardNat U := by
  unfold supportCardNat
  rw [supportOfNat_relabelNatMatrix, supportRelabel_card er.symm ec.symm]

theorem supportRelabel_supportRelabel
    (er₁ er₂ : Fin 3 ≃ Fin 3) (ec₁ ec₂ : Fin 4 ≃ Fin 4)
    (S : Finset MatrixEdge) :
    supportRelabel er₂ ec₂ (supportRelabel er₁ ec₁ S) =
      supportRelabel (er₁.trans er₂) (ec₁.trans ec₂) S := by
  ext e
  simp [supportRelabel]

/-- Any raw double-star core can be put into the canonical coordinates used by
the local descent lemmas. -/
theorem exists_relabel_descentDoubleStarCore_subset_of_raw
    {S : Finset MatrixEdge} {i0 i1 : Fin 3} {j0 j1 : Fin 4}
    (hrow : i0 ≠ i1) (hcol : j0 ≠ j1)
    (h00 : (i0, j0) ∈ S) (h01 : (i0, j1) ∈ S) (h10 : (i1, j0) ∈ S) :
    ∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
      descentDoubleStarCore ⊆ supportRelabel er ec S := by
  let er : Fin 3 ≃ Fin 3 :=
    permSendPairToZeroOne (0 : Fin 3) (1 : Fin 3) i0 i1
  let ec : Fin 4 ≃ Fin 4 :=
    permSendPairToZeroOne (0 : Fin 4) (1 : Fin 4) j0 j1
  have her0 : er.symm 0 = i0 := by
    exact permSendPairToZeroOne_symm_zero (by decide) hrow
  have her1 : er.symm 1 = i1 := by
    exact permSendPairToZeroOne_symm_one
  have hec0 : ec.symm 0 = j0 := by
    exact permSendPairToZeroOne_symm_zero (by decide) hcol
  have hec1 : ec.symm 1 = j1 := by
    exact permSendPairToZeroOne_symm_one
  refine ⟨er, ec, ?_⟩
  intro e he
  simp [descentDoubleStarCore] at he
  rcases he with rfl | rfl | rfl
  · simp [supportRelabel, her0, hec0, h00]
  · simp [supportRelabel, her0, hec1, h01]
  · simp [supportRelabel, her1, hec0, h10]

/-- Structural core of the non-star support classification: every non-star
support contains the canonical double-star core after row/column relabeling. -/
theorem nonstar_support_has_relabelled_doubleStarCore
    {S : Finset MatrixEdge} (hnotstar : ¬ IsSupportStarForest S) :
    ∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
      descentDoubleStarCore ⊆ supportRelabel er ec S := by
  rcases exists_doubleStarCore_edges_of_not_star hnotstar with
    ⟨i0, i1, j0, j1, hrow, hcol, h00, h01, h10⟩
  exact exists_relabel_descentDoubleStarCore_subset_of_raw
    hrow hcol h00 h01 h10

theorem descent_shape_or_doubleStar_envelope_of_core
    {T : Finset MatrixEdge} (hcore : descentDoubleStarCore ⊆ T) :
    (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
      descentCycleSupport ⊆ supportRelabel er ec T) ∨
    (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
      descentRowPathSupport ⊆ supportRelabel er ec T) ∨
    (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
      descentColPathSupport ⊆ supportRelabel er ec T) ∨
    T ⊆ descentDoubleStarSupport := by
  by_cases henv : T ⊆ descentDoubleStarSupport
  · exact Or.inr <| Or.inr <| Or.inr henv
  · have h00 : ((0 : Fin 3), (0 : Fin 4)) ∈ T :=
      hcore (by simp [descentDoubleStarCore])
    have h01 : ((0 : Fin 3), (1 : Fin 4)) ∈ T :=
      hcore (by simp [descentDoubleStarCore])
    have h10 : ((1 : Fin 3), (0 : Fin 4)) ∈ T :=
      hcore (by simp [descentDoubleStarCore])
    rcases Finset.not_subset.mp henv with ⟨e, heT, heEnv⟩
    rcases e with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [descentDoubleStarSupport] at heEnv
    · refine Or.inl ⟨Equiv.refl (Fin 3), Equiv.refl (Fin 4), ?_⟩
      intro e he
      simp [descentCycleSupport] at he
      rcases he with rfl | rfl | rfl | rfl
      · simpa [supportRelabel] using h00
      · simpa [supportRelabel] using h01
      · simpa [supportRelabel] using h10
      · simpa [supportRelabel] using heT
    · refine Or.inr <| Or.inr <| Or.inl ?_
      let er : Fin 3 ≃ Fin 3 := Equiv.swap (0 : Fin 3) 1
      let p : Fin 4 ≃ Fin 4 :=
        (Equiv.swap (0 : Fin 4) 2).trans (Equiv.swap (0 : Fin 4) 1)
      let ec : Fin 4 ≃ Fin 4 := p.symm
      refine ⟨er, ec, ?_⟩
      have her0 : er.symm 0 = (1 : Fin 3) := by simp [er]
      have her1 : er.symm 1 = (0 : Fin 3) := by simp [er]
      have hec0 : ec.symm 0 = (2 : Fin 4) := by decide
      have hec1 : ec.symm 1 = (0 : Fin 4) := by decide
      have hec2 : ec.symm 2 = (1 : Fin 4) := by decide
      intro e he
      simp [descentColPathSupport] at he
      rcases he with rfl | rfl | rfl | rfl
      · simpa [supportRelabel, her0, hec0] using heT
      · simp [supportRelabel, her0, hec1, h10]
      · simp [supportRelabel, her1, hec1, h00]
      · simp [supportRelabel, her1, hec2, h01]
    · refine Or.inr <| Or.inr <| Or.inl ?_
      let er : Fin 3 ≃ Fin 3 := Equiv.swap (0 : Fin 3) 1
      let p : Fin 4 ≃ Fin 4 :=
        ((Equiv.swap (0 : Fin 4) 3).trans
          (Equiv.swap (0 : Fin 4) 2)).trans
            (Equiv.swap (0 : Fin 4) 1)
      let ec : Fin 4 ≃ Fin 4 := p.symm
      refine ⟨er, ec, ?_⟩
      have her0 : er.symm 0 = (1 : Fin 3) := by simp [er]
      have her1 : er.symm 1 = (0 : Fin 3) := by simp [er]
      have hec0 : ec.symm 0 = (3 : Fin 4) := by decide
      have hec1 : ec.symm 1 = (0 : Fin 4) := by decide
      have hec2 : ec.symm 2 = (1 : Fin 4) := by decide
      intro e he
      simp [descentColPathSupport] at he
      rcases he with rfl | rfl | rfl | rfl
      · simpa [supportRelabel, her0, hec0] using heT
      · simp [supportRelabel, her0, hec1, h10]
      · simp [supportRelabel, her1, hec1, h00]
      · simp [supportRelabel, her1, hec2, h01]
    · refine Or.inr <| Or.inl ?_
      let er : Fin 3 ≃ Fin 3 := Equiv.swap (0 : Fin 3) 1
      refine ⟨er, Equiv.refl (Fin 4), ?_⟩
      have her0 : er.symm 0 = (1 : Fin 3) := by simp [er]
      have her1 : er.symm 1 = (0 : Fin 3) := by simp [er]
      have her2 : er.symm 2 = (2 : Fin 3) := by decide
      intro e he
      simp [descentRowPathSupport] at he
      rcases he with rfl | rfl | rfl | rfl
      · simp [supportRelabel, her0, h10]
      · simp [supportRelabel, her1, h00]
      · simp [supportRelabel, her1, h01]
      · simpa [supportRelabel, her2] using heT

/-- Finite classification of non-star supports into the local descent shapes. -/
theorem nonstar_support_has_descent_shape :
    ∀ S : Finset MatrixEdge,
      ¬ IsSupportStarForest S →
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentCycleSupport ⊆ supportRelabel er ec S) ∨
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentRowPathSupport ⊆ supportRelabel er ec S) ∨
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentColPathSupport ⊆ supportRelabel er ec S) ∨
        (∃ er : Fin 3 ≃ Fin 3, ∃ ec : Fin 4 ≃ Fin 4,
          descentDoubleStarCore ⊆ supportRelabel er ec S ∧
            supportRelabel er ec S ⊆ descentDoubleStarSupport) := by
  intro S hnotstar
  rcases nonstar_support_has_relabelled_doubleStarCore hnotstar with
    ⟨er, ec, hcore⟩
  rcases descent_shape_or_doubleStar_envelope_of_core hcore with
    hcycle | hrow | hcol | hdouble
  · rcases hcycle with ⟨er₂, ec₂, hcycle⟩
    refine Or.inl ⟨er.trans er₂, ec.trans ec₂, ?_⟩
    rw [← supportRelabel_supportRelabel er er₂ ec ec₂ S]
    exact hcycle
  · rcases hrow with ⟨er₂, ec₂, hrow⟩
    refine Or.inr <| Or.inl ⟨er.trans er₂, ec.trans ec₂, ?_⟩
    rw [← supportRelabel_supportRelabel er er₂ ec ec₂ S]
    exact hrow
  · rcases hcol with ⟨er₂, ec₂, hcol⟩
    refine Or.inr <| Or.inr <| Or.inl ⟨er.trans er₂, ec.trans ec₂, ?_⟩
    rw [← supportRelabel_supportRelabel er er₂ ec ec₂ S]
    exact hcol
  · exact Or.inr <| Or.inr <| Or.inr ⟨er, ec, hcore, hdouble⟩

/-- Positive endpoint of the canonical four-cycle move, as a natural matrix. -/
def cycleMoveNatPlus (U : NatMatrix) (N : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + N else
    if i = 0 ∧ j = 1 then U i j - N else
    if i = 1 ∧ j = 1 then U i j + N else
    if i = 1 ∧ j = 0 then U i j - N else
    U i j

/-- Negative endpoint of the canonical four-cycle move, as a natural matrix. -/
def cycleMoveNatMinus (U : NatMatrix) (P : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j - P else
    if i = 0 ∧ j = 1 then U i j + P else
    if i = 1 ∧ j = 1 then U i j - P else
    if i = 1 ∧ j = 0 then U i j + P else
    U i j

theorem matrixTotalNat_cycleMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h10 : N <= U 1 0) :
    matrixTotalNat (cycleMoveNatPlus U N) = matrixTotalNat U := by
  simp [matrixTotalNat, cycleMoveNatPlus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_cycleMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixTotalNat (cycleMoveNatMinus U P) = matrixTotalNat U := by
  simp [matrixTotalNat, cycleMoveNatMinus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixOfNat_cycleMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h10 : N <= U 1 0) :
    matrixOfNat (cycleMoveNatPlus U N) =
      cycleMove (matrixOfNat U) (N : Rat) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, cycleMoveNatPlus, cycleMove, h01, h10, Nat.cast_sub]

theorem matrixOfNat_cycleMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixOfNat (cycleMoveNatMinus U P) =
      cycleMove (matrixOfNat U) (-(P : Rat)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, cycleMoveNatMinus, cycleMove, h00, h11, Nat.cast_sub] <;>
      ring

theorem supportCardNat_lt_of_support_ssubset
    {V U : NatMatrix} (h : supportOfNat V ⊂ supportOfNat U) :
    supportCardNat V < supportCardNat U := by
  unfold supportCardNat
  exact Finset.card_lt_card h

theorem supportOfNat_cycleMoveNatPlus_subset
    (U : NatMatrix) (N : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U) :
    supportOfNat (cycleMoveNatPlus U N) ⊆ supportOfNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [cycleMoveNatPlus] at he ⊢ <;> omega

theorem supportOfNat_cycleMoveNatMinus_subset
    (U : NatMatrix) (P : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U) :
    supportOfNat (cycleMoveNatMinus U P) ⊆ supportOfNat U := by
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [cycleMoveNatMinus] at he ⊢ <;> omega

theorem supportCardNat_cycleMoveNatPlus_lt
    (U : NatMatrix) (N : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U)
    (hNpos : 0 < N) (h01 : N <= U 0 1) (h10 : N <= U 1 0)
    (hNmin : N = Nat.min (U 0 1) (U 1 0)) :
    supportCardNat (cycleMoveNatPlus U N) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_cycleMoveNatPlus_subset U N hcycle, ?_⟩
  intro hsubset
  have h01mem : ((0 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  have h10mem : ((1 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  by_cases hle : U 0 1 <= U 1 0
  · have hN : N = U 0 1 := by simpa [hNmin, hle] using hNmin
    have hkilled : ((0 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (cycleMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatPlus, hN]
    exact hkilled (hsubset h01mem)
  · have hlt : U 1 0 < U 0 1 := Nat.lt_of_not_ge hle
    have hN : N = U 1 0 := by
      simpa [hNmin, Nat.min_eq_right (le_of_lt hlt)] using hNmin
    have hkilled : ((1 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (cycleMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatPlus, hN]
    exact hkilled (hsubset h10mem)

theorem supportCardNat_cycleMoveNatMinus_lt
    (U : NatMatrix) (P : Nat)
    (hcycle : descentCycleSupport ⊆ supportOfNat U)
    (hPpos : 0 < P) (h00 : P <= U 0 0) (h11 : P <= U 1 1)
    (hPmin : P = Nat.min (U 0 0) (U 1 1)) :
    supportCardNat (cycleMoveNatMinus U P) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_cycleMoveNatMinus_subset U P hcycle, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  have h11mem : ((1 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hcycle (by simp [descentCycleSupport])
  by_cases hle : U 0 0 <= U 1 1
  · have hP : P = U 0 0 := by simpa [hPmin, hle] using hPmin
    have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (cycleMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatMinus, hP]
    exact hkilled (hsubset h00mem)
  · have hlt : U 1 1 < U 0 0 := Nat.lt_of_not_ge hle
    have hP : P = U 1 1 := by
      simpa [hPmin, Nat.min_eq_right (le_of_lt hlt)] using hPmin
    have hkilled : ((1 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (cycleMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [cycleMoveNatMinus, hP]
    exact hkilled (hsubset h11mem)

/-- A support containing the canonical four-cycle has a one-step descent. -/
theorem canonical_cycle_descent
    (U : NatMatrix)
    (hcycle : descentCycleSupport ⊆ supportOfNat U) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hcycle (by simp [descentCycleSupport])
  let P : Nat := Nat.min (U 0 0) (U 1 1)
  let N : Nat := Nat.min (U 0 1) (U 1 0)
  have hPpos : 0 < P := by
    dsimp [P]
    exact lt_min h00pos h11pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact lt_min h01pos h10pos
  have hP00 : P <= U 0 0 := by
    dsimp [P]
    exact Nat.min_le_left _ _
  have hP11 : P <= U 1 1 := by
    dsimp [P]
    exact Nat.min_le_right _ _
  have hN01 : N <= U 0 1 := by
    dsimp [N]
    exact Nat.min_le_left _ _
  have hN10 : N <= U 1 0 := by
    dsimp [N]
    exact Nat.min_le_right _ _
  have hend := matrixF_cycleMove_endpoint_nonincreasing
    (matrixOfNat U) (P := (P : Rat)) (N := (N : Rat))
    (by positivity) (by positivity)
  rcases hend with hplus | hminus
  · refine ⟨cycleMoveNatPlus U N, ?_, ?_, ?_⟩
    · exact matrixTotalNat_cycleMoveNatPlus U N hN01 hN10
    · unfold matrixFNat
      rw [matrixOfNat_cycleMoveNatPlus U N hN01 hN10]
      exact hplus
    · exact supportCardNat_cycleMoveNatPlus_lt U N hcycle hNpos hN01 hN10 rfl
  · refine ⟨cycleMoveNatMinus U P, ?_, ?_, ?_⟩
    · exact matrixTotalNat_cycleMoveNatMinus U P hP00 hP11
    · unfold matrixFNat
      rw [matrixOfNat_cycleMoveNatMinus U P hP00 hP11]
      exact hminus
    · exact supportCardNat_cycleMoveNatMinus_lt U P hcycle hPpos hP00 hP11 rfl

/-- Positive endpoint of the canonical row-oriented path move. -/
def rowPathMoveNatPlus (U : NatMatrix) (N : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + N else
    if i = 1 ∧ j = 0 then U i j - N else
    if i = 1 ∧ j = 1 then U i j + N else
    if i = 2 ∧ j = 1 then U i j - N else
    U i j

/-- Negative endpoint of the canonical row-oriented path move. -/
def rowPathMoveNatMinus (U : NatMatrix) (P : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j - P else
    if i = 1 ∧ j = 0 then U i j + P else
    if i = 1 ∧ j = 1 then U i j - P else
    if i = 2 ∧ j = 1 then U i j + P else
    U i j

theorem matrixTotalNat_rowPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h10 : N <= U 1 0) (h21 : N <= U 2 1) :
    matrixTotalNat (rowPathMoveNatPlus U N) = matrixTotalNat U := by
  simp [matrixTotalNat, rowPathMoveNatPlus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_rowPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixTotalNat (rowPathMoveNatMinus U P) = matrixTotalNat U := by
  simp [matrixTotalNat, rowPathMoveNatMinus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixOfNat_rowPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h10 : N <= U 1 0) (h21 : N <= U 2 1) :
    matrixOfNat (rowPathMoveNatPlus U N) =
      pathMove (matrixOfNat U) (N : Rat) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, rowPathMoveNatPlus, pathMove, h10, h21, Nat.cast_sub]

theorem matrixOfNat_rowPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixOfNat (rowPathMoveNatMinus U P) =
      pathMove (matrixOfNat U) (-(P : Rat)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, rowPathMoveNatMinus, pathMove, h00, h11, Nat.cast_sub] <;>
      ring

theorem supportOfNat_rowPathMoveNatPlus_subset
    (U : NatMatrix) (N : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U) :
    supportOfNat (rowPathMoveNatPlus U N) ⊆ supportOfNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rowPathMoveNatPlus] at he ⊢ <;> omega

theorem supportOfNat_rowPathMoveNatMinus_subset
    (U : NatMatrix) (P : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U) :
    supportOfNat (rowPathMoveNatMinus U P) ⊆ supportOfNat U := by
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h21pos : 0 < U 2 1 := by
    rw [← mem_supportOfNat_iff U ((2 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [rowPathMoveNatMinus] at he ⊢ <;> omega

theorem supportCardNat_rowPathMoveNatPlus_lt
    (U : NatMatrix) (N : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U)
    (_hNpos : 0 < N) (_h10 : N <= U 1 0) (_h21 : N <= U 2 1)
    (hNmin : N = Nat.min (U 1 0) (U 2 1)) :
    supportCardNat (rowPathMoveNatPlus U N) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_rowPathMoveNatPlus_subset U N hpath, ?_⟩
  intro hsubset
  have h10mem : ((1 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  have h21mem : ((2 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  by_cases hle : U 1 0 <= U 2 1
  · have hN : N = U 1 0 := by simpa [hNmin, hle] using hNmin
    have hkilled : ((1 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatPlus, hN]
    exact hkilled (hsubset h10mem)
  · have hlt : U 2 1 < U 1 0 := Nat.lt_of_not_ge hle
    have hN : N = U 2 1 := by
      simpa [hNmin, Nat.min_eq_right (le_of_lt hlt)] using hNmin
    have hkilled : ((2 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatPlus, hN]
    exact hkilled (hsubset h21mem)

theorem supportCardNat_rowPathMoveNatMinus_lt
    (U : NatMatrix) (P : Nat)
    (hpath : descentRowPathSupport ⊆ supportOfNat U)
    (_hPpos : 0 < P) (_h00 : P <= U 0 0) (_h11 : P <= U 1 1)
    (hPmin : P = Nat.min (U 0 0) (U 1 1)) :
    supportCardNat (rowPathMoveNatMinus U P) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_rowPathMoveNatMinus_subset U P hpath, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  have h11mem : ((1 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentRowPathSupport])
  by_cases hle : U 0 0 <= U 1 1
  · have hP : P = U 0 0 := by simpa [hPmin, hle] using hPmin
    have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatMinus, hP]
    exact hkilled (hsubset h00mem)
  · have hlt : U 1 1 < U 0 0 := Nat.lt_of_not_ge hle
    have hP : P = U 1 1 := by
      simpa [hPmin, Nat.min_eq_right (le_of_lt hlt)] using hPmin
    have hkilled : ((1 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (rowPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [rowPathMoveNatMinus, hP]
    exact hkilled (hsubset h11mem)

/-- A support containing the canonical row-oriented four-edge path descends. -/
theorem canonical_row_path_descent
    (U : NatMatrix)
    (hpath : descentRowPathSupport ⊆ supportOfNat U) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  have h21pos : 0 < U 2 1 := by
    rw [← mem_supportOfNat_iff U ((2 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentRowPathSupport])
  let P : Nat := Nat.min (U 0 0) (U 1 1)
  let N : Nat := Nat.min (U 1 0) (U 2 1)
  have hPpos : 0 < P := by
    dsimp [P]
    exact lt_min h00pos h11pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact lt_min h10pos h21pos
  have hP00 : P <= U 0 0 := by
    dsimp [P]
    exact Nat.min_le_left _ _
  have hP11 : P <= U 1 1 := by
    dsimp [P]
    exact Nat.min_le_right _ _
  have hN10 : N <= U 1 0 := by
    dsimp [N]
    exact Nat.min_le_left _ _
  have hN21 : N <= U 2 1 := by
    dsimp [N]
    exact Nat.min_le_right _ _
  have hend := matrixF_pathMove_endpoint_nonincreasing
    (matrixOfNat U) (P := (P : Rat)) (N := (N : Rat))
    (by positivity) (by positivity)
  rcases hend with hplus | hminus
  · refine ⟨rowPathMoveNatPlus U N, ?_, ?_, ?_⟩
    · exact matrixTotalNat_rowPathMoveNatPlus U N hN10 hN21
    · unfold matrixFNat
      rw [matrixOfNat_rowPathMoveNatPlus U N hN10 hN21]
      exact hplus
    · exact supportCardNat_rowPathMoveNatPlus_lt U N hpath hNpos hN10 hN21 rfl
  · refine ⟨rowPathMoveNatMinus U P, ?_, ?_, ?_⟩
    · exact matrixTotalNat_rowPathMoveNatMinus U P hP00 hP11
    · unfold matrixFNat
      rw [matrixOfNat_rowPathMoveNatMinus U P hP00 hP11]
      exact hminus
    · exact supportCardNat_rowPathMoveNatMinus_lt U P hpath hPpos hP00 hP11 rfl

/-- Canonical column-oriented four-edge path move on the path
`col 0 - row 0 - col 1 - row 1 - col 2`. -/
def colPathMove (U : Fin 3 → Fin 4 → Rat) (eps : Rat) : Fin 3 → Fin 4 → Rat :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + eps else
    if i = 0 ∧ j = 1 then U i j - eps else
    if i = 1 ∧ j = 1 then U i j + eps else
    if i = 1 ∧ j = 2 then U i j - eps else
    U i j

theorem matrixF_colPathMove_sub
    (U : Fin 3 → Fin 4 → Rat) (eps : Rat) :
    matrixF (colPathMove U eps) - matrixF U =
      eps *
        (2 * colSum U 0 - 2 * colSum U 2 -
          U 0 0 + U 0 1 - U 1 1 + U 1 2) := by
  simp [matrixF, rowSum, colSum, colPathMove, Fin.sum_univ_three, Fin.sum_univ_four]
  ring

theorem matrixF_colPathMove_endpoint_nonincreasing
    (U : Fin 3 → Fin 4 → Rat) {P N : Rat}
    (hP : 0 <= P) (hN : 0 <= N) :
    matrixF (colPathMove U N) <= matrixF U ∨
      matrixF (colPathMove U (-P)) <= matrixF U := by
  let b :=
    2 * colSum U 0 - 2 * colSum U 2 -
      U 0 0 + U 0 1 - U 1 1 + U 1 2
  have hend := endpoint_quadratic_nonpos
    (a := (0 : Rat)) (b := b) (by norm_num) hP hN
  rcases hend with hend | hend
  · left
    rw [← sub_nonpos, matrixF_colPathMove_sub]
    nlinarith
  · right
    rw [← sub_nonpos, matrixF_colPathMove_sub]
    nlinarith

/-- Positive endpoint of the canonical column-oriented path move. -/
def colPathMoveNatPlus (U : NatMatrix) (N : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j + N else
    if i = 0 ∧ j = 1 then U i j - N else
    if i = 1 ∧ j = 1 then U i j + N else
    if i = 1 ∧ j = 2 then U i j - N else
    U i j

/-- Negative endpoint of the canonical column-oriented path move. -/
def colPathMoveNatMinus (U : NatMatrix) (P : Nat) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 0 then U i j - P else
    if i = 0 ∧ j = 1 then U i j + P else
    if i = 1 ∧ j = 1 then U i j - P else
    if i = 1 ∧ j = 2 then U i j + P else
    U i j

theorem matrixTotalNat_colPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h12 : N <= U 1 2) :
    matrixTotalNat (colPathMoveNatPlus U N) = matrixTotalNat U := by
  simp [matrixTotalNat, colPathMoveNatPlus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_colPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixTotalNat (colPathMoveNatMinus U P) = matrixTotalNat U := by
  simp [matrixTotalNat, colPathMoveNatMinus, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixOfNat_colPathMoveNatPlus
    (U : NatMatrix) (N : Nat)
    (h01 : N <= U 0 1) (h12 : N <= U 1 2) :
    matrixOfNat (colPathMoveNatPlus U N) =
      colPathMove (matrixOfNat U) (N : Rat) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, colPathMoveNatPlus, colPathMove, h01, h12, Nat.cast_sub]

theorem matrixOfNat_colPathMoveNatMinus
    (U : NatMatrix) (P : Nat)
    (h00 : P <= U 0 0) (h11 : P <= U 1 1) :
    matrixOfNat (colPathMoveNatMinus U P) =
      colPathMove (matrixOfNat U) (-(P : Rat)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixOfNat, colPathMoveNatMinus, colPathMove, h00, h11, Nat.cast_sub] <;>
      ring

theorem supportOfNat_colPathMoveNatPlus_subset
    (U : NatMatrix) (N : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U) :
    supportOfNat (colPathMoveNatPlus U N) ⊆ supportOfNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [colPathMoveNatPlus] at he ⊢ <;> omega

theorem supportOfNat_colPathMoveNatMinus_subset
    (U : NatMatrix) (P : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U) :
    supportOfNat (colPathMoveNatMinus U P) ⊆ supportOfNat U := by
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h12pos : 0 < U 1 2 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (2 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [colPathMoveNatMinus] at he ⊢ <;> omega

theorem supportCardNat_colPathMoveNatPlus_lt
    (U : NatMatrix) (N : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U)
    (_hNpos : 0 < N) (_h01 : N <= U 0 1) (_h12 : N <= U 1 2)
    (hNmin : N = Nat.min (U 0 1) (U 1 2)) :
    supportCardNat (colPathMoveNatPlus U N) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_colPathMoveNatPlus_subset U N hpath, ?_⟩
  intro hsubset
  have h01mem : ((0 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  have h12mem : ((1 : Fin 3), (2 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  by_cases hle : U 0 1 <= U 1 2
  · have hN : N = U 0 1 := by simpa [hNmin, hle] using hNmin
    have hkilled : ((0 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (colPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatPlus, hN]
    exact hkilled (hsubset h01mem)
  · have hlt : U 1 2 < U 0 1 := Nat.lt_of_not_ge hle
    have hN : N = U 1 2 := by
      simpa [hNmin, Nat.min_eq_right (le_of_lt hlt)] using hNmin
    have hkilled : ((1 : Fin 3), (2 : Fin 4)) ∉
        supportOfNat (colPathMoveNatPlus U N) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatPlus, hN]
    exact hkilled (hsubset h12mem)

theorem supportCardNat_colPathMoveNatMinus_lt
    (U : NatMatrix) (P : Nat)
    (hpath : descentColPathSupport ⊆ supportOfNat U)
    (_hPpos : 0 < P) (_h00 : P <= U 0 0) (_h11 : P <= U 1 1)
    (hPmin : P = Nat.min (U 0 0) (U 1 1)) :
    supportCardNat (colPathMoveNatMinus U P) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_colPathMoveNatMinus_subset U P hpath, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  have h11mem : ((1 : Fin 3), (1 : Fin 4)) ∈ supportOfNat U :=
    hpath (by simp [descentColPathSupport])
  by_cases hle : U 0 0 <= U 1 1
  · have hP : P = U 0 0 := by simpa [hPmin, hle] using hPmin
    have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
        supportOfNat (colPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatMinus, hP]
    exact hkilled (hsubset h00mem)
  · have hlt : U 1 1 < U 0 0 := Nat.lt_of_not_ge hle
    have hP : P = U 1 1 := by
      simpa [hPmin, Nat.min_eq_right (le_of_lt hlt)] using hPmin
    have hkilled : ((1 : Fin 3), (1 : Fin 4)) ∉
        supportOfNat (colPathMoveNatMinus U P) := by
      rw [mem_supportOfNat_iff]
      simp [colPathMoveNatMinus, hP]
    exact hkilled (hsubset h11mem)

/-- A support containing the canonical column-oriented four-edge path descends. -/
theorem canonical_col_path_descent
    (U : NatMatrix)
    (hpath : descentColPathSupport ⊆ supportOfNat U) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h00pos : 0 < U 0 0 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (0 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h11pos : 0 < U 1 1 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (1 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  have h12pos : 0 < U 1 2 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (2 : Fin 4))]
    exact hpath (by simp [descentColPathSupport])
  let P : Nat := Nat.min (U 0 0) (U 1 1)
  let N : Nat := Nat.min (U 0 1) (U 1 2)
  have hPpos : 0 < P := by
    dsimp [P]
    exact lt_min h00pos h11pos
  have hNpos : 0 < N := by
    dsimp [N]
    exact lt_min h01pos h12pos
  have hP00 : P <= U 0 0 := by
    dsimp [P]
    exact Nat.min_le_left _ _
  have hP11 : P <= U 1 1 := by
    dsimp [P]
    exact Nat.min_le_right _ _
  have hN01 : N <= U 0 1 := by
    dsimp [N]
    exact Nat.min_le_left _ _
  have hN12 : N <= U 1 2 := by
    dsimp [N]
    exact Nat.min_le_right _ _
  have hend := matrixF_colPathMove_endpoint_nonincreasing
    (matrixOfNat U) (P := (P : Rat)) (N := (N : Rat))
    (by positivity) (by positivity)
  rcases hend with hplus | hminus
  · refine ⟨colPathMoveNatPlus U N, ?_, ?_, ?_⟩
    · exact matrixTotalNat_colPathMoveNatPlus U N hN01 hN12
    · unfold matrixFNat
      rw [matrixOfNat_colPathMoveNatPlus U N hN01 hN12]
      exact hplus
    · exact supportCardNat_colPathMoveNatPlus_lt U N hpath hNpos hN01 hN12 rfl
  · refine ⟨colPathMoveNatMinus U P, ?_, ?_, ?_⟩
    · exact matrixTotalNat_colPathMoveNatMinus U P hP00 hP11
    · unfold matrixFNat
      rw [matrixOfNat_colPathMoveNatMinus U P hP00 hP11]
      exact hminus
    · exact supportCardNat_colPathMoveNatMinus_lt U P hpath hPpos hP00 hP11 rfl

theorem entry_eq_zero_of_support_subset
    (U : NatMatrix) {S : Finset MatrixEdge}
    (hsub : supportOfNat U ⊆ S) {i : Fin 3} {j : Fin 4}
    (h : (i, j) ∉ S) :
    U i j = 0 := by
  exact entry_eq_zero_of_not_mem_support U (fun hmem => h (hsub hmem))

/-- Delete the canonical double-star central edge and move its mass to the
row-side leaf. -/
def doubleStarMoveXNat (U : NatMatrix) : NatMatrix :=
  fun i j =>
    if i = 0 ∧ j = 1 then U i j + U 0 0 else
    if i = 0 ∧ j = 0 then 0 else
    U i j

/-- Delete the canonical double-star central edge and move its mass to the
column-side leaf. -/
def doubleStarMoveZNat (U : NatMatrix) : NatMatrix :=
  fun i j =>
    if i = 1 ∧ j = 0 then U i j + U 0 0 else
    if i = 0 ∧ j = 0 then 0 else
    U i j

theorem matrixTotalNat_doubleStarMoveXNat (U : NatMatrix) :
    matrixTotalNat (doubleStarMoveXNat U) = matrixTotalNat U := by
  simp [matrixTotalNat, doubleStarMoveXNat, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem matrixTotalNat_doubleStarMoveZNat (U : NatMatrix) :
    matrixTotalNat (doubleStarMoveZNat U) = matrixTotalNat U := by
  simp [matrixTotalNat, doubleStarMoveZNat, Fin.sum_univ_three, Fin.sum_univ_four]
  omega

theorem supportOfNat_doubleStarMoveXNat_subset
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportOfNat (doubleStarMoveXNat U) ⊆ supportOfNat U := by
  have h01pos : 0 < U 0 1 := by
    rw [← mem_supportOfNat_iff U ((0 : Fin 3), (1 : Fin 4))]
    exact hcore (by simp [descentDoubleStarCore])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [doubleStarMoveXNat] at he ⊢ <;> omega

theorem supportOfNat_doubleStarMoveZNat_subset
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportOfNat (doubleStarMoveZNat U) ⊆ supportOfNat U := by
  have h10pos : 0 < U 1 0 := by
    rw [← mem_supportOfNat_iff U ((1 : Fin 3), (0 : Fin 4))]
    exact hcore (by simp [descentDoubleStarCore])
  intro e he
  rw [mem_supportOfNat_iff] at he ⊢
  rcases e with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [doubleStarMoveZNat] at he ⊢ <;> omega

theorem supportCardNat_doubleStarMoveXNat_lt
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportCardNat (doubleStarMoveXNat U) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_doubleStarMoveXNat_subset U hcore, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcore (by simp [descentDoubleStarCore])
  have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
      supportOfNat (doubleStarMoveXNat U) := by
    rw [mem_supportOfNat_iff]
    simp [doubleStarMoveXNat]
  exact hkilled (hsubset h00mem)

theorem supportCardNat_doubleStarMoveZNat_lt
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U) :
    supportCardNat (doubleStarMoveZNat U) < supportCardNat U := by
  apply supportCardNat_lt_of_support_ssubset
  refine ⟨supportOfNat_doubleStarMoveZNat_subset U hcore, ?_⟩
  intro hsubset
  have h00mem : ((0 : Fin 3), (0 : Fin 4)) ∈ supportOfNat U :=
    hcore (by simp [descentDoubleStarCore])
  have hkilled : ((0 : Fin 3), (0 : Fin 4)) ∉
      supportOfNat (doubleStarMoveZNat U) := by
    rw [mem_supportOfNat_iff]
    simp [doubleStarMoveZNat]
  exact hkilled (hsubset h00mem)

theorem matrixFNat_doubleStarMoveX_sub
    (U : NatMatrix)
    (h11 : U 1 1 = 0) (h12 : U 1 2 = 0)
    (h13 : U 1 3 = 0) (h21 : U 2 1 = 0) :
    matrixFNat U - matrixFNat (doubleStarMoveXNat U) =
      (U 0 0 : Rat) * (2 * (U 2 0 : Rat) + 2 * (U 1 0 : Rat) - (U 0 1 : Rat)) := by
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, doubleStarMoveXNat,
    Fin.sum_univ_three, Fin.sum_univ_four, h11, h12, h13, h21]
  ring

theorem matrixFNat_doubleStarMoveZ_sub
    (U : NatMatrix)
    (h11 : U 1 1 = 0) (h12 : U 1 2 = 0)
    (h13 : U 1 3 = 0) (h21 : U 2 1 = 0) :
    matrixFNat U - matrixFNat (doubleStarMoveZNat U) =
      (U 0 0 : Rat) *
        (2 * ((U 0 2 : Rat) + (U 0 3 : Rat)) + 2 * (U 0 1 : Rat) - (U 1 0 : Rat)) := by
  simp [matrixFNat, matrixOfNat, matrixF, rowSum, colSum, doubleStarMoveZNat,
    Fin.sum_univ_three, Fin.sum_univ_four, h11, h12, h13, h21]
  ring

/-- A support in the canonical double-star envelope has a one-step descent. -/
theorem canonical_doubleStar_descent
    (U : NatMatrix)
    (hcore : descentDoubleStarCore ⊆ supportOfNat U)
    (henv : supportOfNat U ⊆ descentDoubleStarSupport) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  have h11 : U 1 1 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have h12 : U 1 2 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have h13 : U 1 3 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have h21 : U 2 1 = 0 := entry_eq_zero_of_support_subset U henv
    (by simp [descentDoubleStarSupport])
  have hx0 : 0 <= (U 0 1 : Rat) := by positivity
  have hy0 : 0 <= (U 0 0 : Rat) := by positivity
  have hz0 : 0 <= (U 1 0 : Rat) := by positivity
  have hA : 0 <= (U 0 2 : Rat) + (U 0 3 : Rat) := by positivity
  have hB : 0 <= (U 2 0 : Rat) := by positivity
  rcases doubleStar_coeff_nonneg
      (A := (U 0 2 : Rat) + (U 0 3 : Rat))
      (B := (U 2 0 : Rat))
      (x := (U 0 1 : Rat))
      (z := (U 1 0 : Rat)) hA hB hx0 hz0 with hcoef | hcoef
  · refine ⟨doubleStarMoveXNat U, matrixTotalNat_doubleStarMoveXNat U, ?_, ?_⟩
    · rw [← sub_nonneg, matrixFNat_doubleStarMoveX_sub U h11 h12 h13 h21]
      exact mul_nonneg hy0 hcoef
    · exact supportCardNat_doubleStarMoveXNat_lt U hcore
  · refine ⟨doubleStarMoveZNat U, matrixTotalNat_doubleStarMoveZNat U, ?_, ?_⟩
    · rw [← sub_nonneg, matrixFNat_doubleStarMoveZ_sub U h11 h12 h13 h21]
      exact mul_nonneg hy0 hcoef
    · exact supportCardNat_doubleStarMoveZNat_lt U hcore

theorem descent_of_relabel_symm
    (er : Fin 3 ≃ Fin 3) (ec : Fin 4 ≃ Fin 4)
    (U : NatMatrix)
    (h :
      ∃ W : NatMatrix,
        matrixTotalNat W = matrixTotalNat (relabelNatMatrix er.symm ec.symm U) ∧
        matrixFNat W <= matrixFNat (relabelNatMatrix er.symm ec.symm U) ∧
        supportCardNat W < supportCardNat (relabelNatMatrix er.symm ec.symm U)) :
    ∃ V : NatMatrix,
      matrixTotalNat V = matrixTotalNat U ∧
      matrixFNat V <= matrixFNat U ∧
      supportCardNat V < supportCardNat U := by
  rcases h with ⟨W, htotal, hF, hcard⟩
  refine ⟨relabelNatMatrix er ec W, ?_, ?_, ?_⟩
  · rw [matrixTotalNat_relabelNatMatrix, htotal, matrixTotalNat_relabelNatMatrix]
  · rw [matrixFNat_relabelNatMatrix]
    rw [matrixFNat_relabelNatMatrix] at hF
    exact hF
  · rw [supportCardNat_relabelNatMatrix]
    rw [supportCardNat_relabelNatMatrix] at hcard
    exact hcard

/-- The one-step support descent lemma from Section 5. -/
theorem support_descent_step_proven : SupportDescentStepStatement := by
  intro U hnotstar
  rcases nonstar_support_has_descent_shape (supportOfNat U) hnotstar with
    hcycle | hrow | hcol | hdouble
  · rcases hcycle with ⟨er, ec, hcycle⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_cycle_descent
    rw [supportOfNat_relabelNatMatrix]
    simpa using hcycle
  · rcases hrow with ⟨er, ec, hrow⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_row_path_descent
    rw [supportOfNat_relabelNatMatrix]
    simpa using hrow
  · rcases hcol with ⟨er, ec, hcol⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_col_path_descent
    rw [supportOfNat_relabelNatMatrix]
    simpa using hcol
  · rcases hdouble with ⟨er, ec, hcore, henv⟩
    apply descent_of_relabel_symm er ec U
    apply canonical_doubleStar_descent
    · rw [supportOfNat_relabelNatMatrix]
      simpa using hcore
    · rw [supportOfNat_relabelNatMatrix]
      simpa using henv

end Lollipop

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Lemma 7.2 (`lem:compression`): support compression preserves total
mass, does not increase `F`, and terminates at a star forest.
-/

namespace Lollipop.Manuscript.Lemma_7_2

abbrev CoreStatement : Prop := SupportCompressionStatement

end Lollipop.Manuscript.Lemma_7_2

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Lemma_7_2

theorem proof : CoreStatement := by
  exact support_compression_of_descent_step support_descent_step_proven

end Lollipop.Manuscript.Lemma_7_2
