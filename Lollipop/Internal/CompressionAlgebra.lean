import Lollipop.Internal.Algebra
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

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
