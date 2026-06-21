import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

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
