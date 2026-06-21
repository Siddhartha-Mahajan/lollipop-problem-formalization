import Lollipop.Internal.Algebra
import Mathlib.Tactic

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

/-- The first small value of `M`. -/
theorem concreteM_zero : concreteM 0 = (0 : ℚ) := by
  native_decide

/-- The second small value of `M`. -/
theorem concreteM_one : concreteM 1 = (3 / 2 : ℚ) := by
  native_decide

/-- The third small value of `M`. -/
theorem concreteM_two : concreteM 2 = (3 : ℚ) := by
  native_decide

/-- The fourth small value of `M`. -/
theorem concreteM_three : concreteM 3 = (9 / 2 : ℚ) := by
  native_decide

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
