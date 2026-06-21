import Lollipop.Internal.ColoredTuran.CloseDirection
import Lollipop.Internal.Manuscript.PrimitiveGeometry.Qoppa

/-!
Direction-to-dot-product bridge.

The close-direction input in the manuscript is recorded as a normalized
cyclic-angle relation.  The geometric route certificates, however, consume
coordinate inequalities involving dot products of bearing vectors.  This file
formalizes the elementary trigonometric bridge between those two languages.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- Dot product of two unit bearing vectors is the cosine of the angle
difference. -/
theorem dot2_angleDirection_angleDirection (a b : ℝ) :
    dot2 (angleDirection a) (angleDirection b) = Real.cos (a - b) := by
  unfold dot2 angleDirection point2
  rw [Real.cos_sub]

/-- A trigonometric nonnegativity hypothesis transfers directly to the dot
product of the corresponding bearing vectors. -/
theorem dot2_angleDirection_nonneg_of_cos_sub_nonneg
    {a b : ℝ} (h : 0 ≤ Real.cos (a - b)) :
    0 ≤ dot2 (angleDirection a) (angleDirection b) := by
  simpa [dot2_angleDirection_angleDirection] using h

/-- Specialization of the dot-product formula to normalized directions, where
`a` and `b` represent turns on `R/Z`. -/
theorem dot2_angleDirection_two_pi (a b : ℝ) :
    dot2 (angleDirection (2 * Real.pi * a))
      (angleDirection (2 * Real.pi * b)) =
        Real.cos (2 * Real.pi * (a - b)) := by
  rw [dot2_angleDirection_angleDirection]
  congr 1
  ring

/-- Cosine is nonnegative when a real number is either within one quarter turn
of zero or within one quarter turn of a full turn. -/
theorem cos_two_pi_mul_nonneg_of_abs_le_quarter_or_three_quarters_le_abs
    {d : ℝ} (hdlt : |d| < 1)
    (hclose : |d| ≤ (1 / 4 : ℝ) ∨ (3 / 4 : ℝ) ≤ |d|) :
    0 ≤ Real.cos (2 * Real.pi * d) := by
  rcases hclose with hquarter | hwrap
  · have hd_bounds : -(1 / 4 : ℝ) ≤ d ∧ d ≤ (1 / 4 : ℝ) :=
      abs_le.mp hquarter
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos],
      by nlinarith [Real.pi_pos]⟩
  · have hcos_abs :
        Real.cos (2 * Real.pi * d) =
          Real.cos (2 * Real.pi * |d|) := by
      by_cases hd_nonneg : 0 ≤ d
      · rw [abs_of_nonneg hd_nonneg]
      · have hd_nonpos : d ≤ 0 := le_of_not_ge hd_nonneg
        rw [abs_of_nonpos hd_nonpos]
        rw [show 2 * Real.pi * -d = -(2 * Real.pi * d) by ring]
        rw [Real.cos_neg]
    have hcos_wrap :
        Real.cos (2 * Real.pi * |d|) =
          Real.cos (2 * Real.pi * (1 - |d|)) := by
      rw [← Real.cos_two_pi_sub (2 * Real.pi * |d|)]
      congr 1
      ring
    have hwrap_bounds :
        0 ≤ 1 - |d| ∧ 1 - |d| ≤ (1 / 4 : ℝ) := by
      exact ⟨by linarith [le_of_lt hdlt], by linarith⟩
    rw [hcos_abs, hcos_wrap]
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos],
      by nlinarith [Real.pi_pos]⟩

/-- The cyclic-close predicate on normalized directions implies nonnegative
cosine of the corresponding angular difference, provided both directions lie
in one fundamental interval. -/
theorem cos_two_pi_mul_sub_nonneg_of_cyclicClosePair
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hclose : CloseDirection.cyclicClosePair a b) :
    0 ≤ Real.cos (2 * Real.pi * (a - b)) := by
  have hdlt : |a - b| < 1 := by
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact
    cos_two_pi_mul_nonneg_of_abs_le_quarter_or_three_quarters_le_abs
      (d := a - b) hdlt (by
        simpa [CloseDirection.cyclicClosePair] using hclose)

/-- A cyclic-close pair of normalized directions has nonnegative dot product
between the associated bearing vectors. -/
theorem dot2_angleDirection_two_pi_nonneg_of_cyclicClosePair
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hclose : CloseDirection.cyclicClosePair a b) :
    0 ≤ dot2 (angleDirection (2 * Real.pi * a))
      (angleDirection (2 * Real.pi * b)) := by
  rw [dot2_angleDirection_two_pi]
  exact cos_two_pi_mul_sub_nonneg_of_cyclicClosePair
    ha0 ha1 hb0 hb1 hclose

/-- Same statement using the arrangement-level close relation. -/
theorem dot2_angleDirection_two_pi_nonneg_of_cyclicClose
    {V : Type*} (theta : V → ℝ) {i j : V}
    (hi0 : 0 ≤ theta i) (hi1 : theta i < 1)
    (hj0 : 0 ≤ theta j) (hj1 : theta j < 1)
    (hclose : CloseDirection.cyclicClose theta i j) :
    0 ≤ dot2 (angleDirection (2 * Real.pi * theta i))
      (angleDirection (2 * Real.pi * theta j)) := by
  exact dot2_angleDirection_two_pi_nonneg_of_cyclicClosePair
    hi0 hi1 hj0 hj1 hclose

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
