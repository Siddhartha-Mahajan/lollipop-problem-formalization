import Lollipop.Internal.Manuscript.PrimitiveGeometry.Qoppa

/-!
# The corrected local blow-up family

This file formalizes the algebraic core of the replacement for the false
`Phi_t` orbit in the manuscript.  For `0 ≤ t ≤ 1/4`, the family is

* center `c_t = (3t,3t)`,
* radial vector `v_t = (1-t^2,-2t)`,
* radius `r_t = 1+t^2`,
* stem points `c_t + q v_t` with `q ≥ 1`.

The theorems below check the radial identity, the two strict circle-circle
inequalities, the anchor signs and derivative bounds for the two mixed
components, and the explicit accepted parameters for the unique stem-stem
intersection.  These are the scalar inequalities used in the corrected
manuscript proof of the local `2+1+0+1=4` crossing count.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry
namespace PolynomialBlowUp

noncomputable section

/-- Center of the corrected polynomial family. -/
def center (t : ℝ) : R2 := point2 (3 * t) (3 * t)

/-- Radial vector and stem direction of the corrected polynomial family. -/
def vector (t : ℝ) : R2 := point2 (1 - t ^ 2) (-2 * t)

/-- Radius of the corrected polynomial family. -/
def radius (t : ℝ) : ℝ := 1 + t ^ 2

/-- Anchor of the corrected polynomial family. -/
def anchor (t : ℝ) : R2 := center t + vector t

/-- A point on the supporting stem line, using the center-based parameter. -/
def stemPoint (t q : ℝ) : R2 := center t + q • vector t

/-- The radial vector has exactly the required length. -/
theorem radial_identity (t : ℝ) :
    (1 - t ^ 2) ^ 2 + (-2 * t) ^ 2 = (1 + t ^ 2) ^ 2 := by
  ring

/-- Coordinate form of the radial identity in the primitive geometry model. -/
theorem normSq2_vector (t : ℝ) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 (vector t) = radius t ^ 2 := by
  unfold vector radius point2
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  ring

/-- The family radius is positive for every real parameter. -/
theorem radius_pos (t : ℝ) : 0 < radius t := by
  unfold radius
  positivity


/-- The polynomial anchor lies on its polynomial circle. -/
theorem anchor_mem_circleSet (t : ℝ) :
    anchor t ∈ circleSet (center t) (radius t) := by
  unfold anchor center vector radius circleSet
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 point2
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- The polynomial stem direction never vanishes. -/
theorem vector_ne_zero (t : ℝ) : vector t ≠ 0 := by
  intro hzero
  have hnorm := normSq2_vector t
  rw [hzero] at hnorm
  have hsq : radius t ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (radius_pos t))
  apply hsq
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2,
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2] using hnorm.symm

/-- The corrected family as an actual primitive Euclidean lollipop. -/
def lollipop (t : ℝ) : EuclideanLollipop where
  center := PolynomialBlowUp.center t
  radius := PolynomialBlowUp.radius t
  radius_pos := radius_pos t
  anchor := PolynomialBlowUp.anchor t
  rayDirection := vector t
  rayDirection_ne_zero := vector_ne_zero t
  anchor_on_circle := anchor_mem_circleSet t
  normalizedDirection := 0
  normalizedDirection_nonneg := by norm_num
  normalizedDirection_lt_one := by norm_num

/-- Every member of the corrected family is radial outward. -/
theorem lollipop_isRadialOutward (t : ℝ) :
    (lollipop t).IsRadialOutward := by
  refine ⟨1, by norm_num, ?_⟩
  simp [lollipop, anchor]

/-- Center-based parameters `q ≥ 1` describe points on the actual half-line. -/
theorem stemPoint_mem_raySet {t q : ℝ} (hq : 1 ≤ q) :
    stemPoint t q ∈ raySet (anchor t) (vector t) := by
  refine ⟨q - 1, sub_nonneg.mpr hq, ?_⟩
  ext i
  simp [stemPoint, anchor, Pi.add_apply, Pi.smul_apply]
  ring

/-- Squared distance of a supporting-stem point from its own center. -/
theorem distSq2_stemPoint_center (t q : ℝ) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (stemPoint t q) (center t) = q ^ 2 * radius t ^ 2 := by
  unfold stemPoint center vector radius point2
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- A point strictly beyond the anchor is strictly outside its own circle. -/
theorem stemPoint_strictly_outside_own_circle
    {t q : ℝ} (hq : 1 < q) :
    radius t ^ 2 <
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (stemPoint t q) (center t) := by
  rw [distSq2_stemPoint_center]
  have hr : 0 < radius t ^ 2 := sq_pos_of_pos (radius_pos t)
  have hq2 : 1 < q ^ 2 := by nlinarith
  nlinarith [mul_pos (sub_pos.mpr hq2) hr]

/-- The polynomial used for the stem of `Γ_s` against the circle of `Γ_t`. -/
def F (s t q : ℝ) : ℝ :=
  (3 * s + q * (1 - s ^ 2) - 3 * t) ^ 2 +
    (3 * s - 2 * s * q - 3 * t) ^ 2 - (1 + t ^ 2) ^ 2

/-- The polynomial used for the stem of `Γ_t` against the circle of `Γ_s`. -/
def G (s t q : ℝ) : ℝ :=
  (3 * t + q * (1 - t ^ 2) - 3 * s) ^ 2 +
    (3 * t - 2 * t * q - 3 * s) ^ 2 - (1 + s ^ 2) ^ 2

/-- `F` is exactly the squared-distance circle equation along the `s` stem. -/
theorem F_eq_geometry (s t q : ℝ) :
    F s t q =
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (stemPoint s q) (center t) - radius t ^ 2 := by
  unfold F stemPoint center vector radius point2
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- `G` is exactly the squared-distance circle equation along the `t` stem. -/
theorem G_eq_geometry (s t q : ℝ) :
    G s t q =
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (stemPoint t q) (center s) - radius s ^ 2 := by
  unfold G stemPoint center vector radius point2
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- The positive factor in the value `F(s,t,1)`. -/
def B (s t : ℝ) : ℝ :=
  6 + 8 * s - 16 * t - 6 * s ^ 2 +
    s ^ 3 + s ^ 2 * t + s * t ^ 2 + t ^ 3

/-- The positive factor in the value `G(s,t,1)`. -/
def C (s t : ℝ) : ℝ :=
  6 - 16 * s + 8 * t - 6 * t ^ 2 +
    s ^ 3 + s ^ 2 * t + s * t ^ 2 + t ^ 3

/-- Exact anchor-value factorization for the first mixed component. -/
theorem F_one (s t : ℝ) : F s t 1 = -(t - s) * B s t := by
  unfold F B
  ring

/-- Exact anchor-value factorization for the reverse mixed component. -/
theorem G_one (s t : ℝ) : G s t 1 = (t - s) * C s t := by
  unfold G C
  ring

/-- Half of the derivative of `F` at the anchor. -/
def FhalfDerivativeAtOne (s t : ℝ) : ℝ :=
  (1 + s ^ 2) ^ 2 - 3 * (t - s) * (1 - 2 * s - s ^ 2)

/-- Half of the derivative of `G` at the anchor. -/
def GhalfDerivativeAtOne (s t : ℝ) : ℝ :=
  (1 + t ^ 2) ^ 2 + 3 * (t - s) * (1 - 2 * t - t ^ 2)

/-- Direct differentiation identity for `F` at `q=1`. -/
theorem FhalfDerivativeAtOne_eq (s t : ℝ) :
    (1 - s ^ 2) * (3 * s + (1 - s ^ 2) - 3 * t) +
        (-2 * s) * (3 * s - 2 * s - 3 * t) =
      FhalfDerivativeAtOne s t := by
  unfold FhalfDerivativeAtOne
  ring

/-- Direct differentiation identity for `G` at `q=1`. -/
theorem GhalfDerivativeAtOne_eq (s t : ℝ) :
    (1 - t ^ 2) * (3 * t + (1 - t ^ 2) - 3 * s) +
        (-2 * t) * (3 * t - 2 * t - 3 * s) =
      GhalfDerivativeAtOne s t := by
  unfold GhalfDerivativeAtOne
  ring

private theorem parameter_square_bounds
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    s ^ 2 ≤ (1 : ℝ) / 16 ∧ t ^ 2 ≤ (1 : ℝ) / 16 ∧
      s * t ≤ (1 : ℝ) / 16 := by
  have hsle : s ≤ (1 : ℝ) / 4 := le_trans (le_of_lt hst) ht
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hsprod :
      0 ≤ ((1 : ℝ) / 4 - s) * ((1 : ℝ) / 4 + s) :=
    mul_nonneg (sub_nonneg.mpr hsle) (by positivity)
  have htprod :
      0 ≤ ((1 : ℝ) / 4 - t) * ((1 : ℝ) / 4 + t) :=
    mul_nonneg (sub_nonneg.mpr ht) (by positivity)
  have hstprod : 0 ≤ (s - t) ^ 2 := sq_nonneg (s - t)
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The strict two-circle inequalities for `0 ≤ s < t ≤ 1/4`. -/
theorem circle_strict_inequalities
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    (t - s) ^ 2 * (s + t) ^ 2 < 18 * (t - s) ^ 2 ∧
      18 * (t - s) ^ 2 < (2 + s ^ 2 + t ^ 2) ^ 2 := by
  have hdelta : 0 < t - s := sub_pos.mpr hst
  have hsle : s ≤ (1 : ℝ) / 4 := le_trans (le_of_lt hst) ht
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hsum_nonneg : 0 ≤ s + t := by positivity
  have hsum_le : s + t ≤ (1 : ℝ) / 2 := by nlinarith
  have hsumprod :
      0 ≤ ((1 : ℝ) / 2 - (s + t)) * ((1 : ℝ) / 2 + (s + t)) :=
    mul_nonneg (sub_nonneg.mpr hsum_le) (by positivity)
  have hdelta_le : t - s ≤ (1 : ℝ) / 4 := by nlinarith
  have hdeltaprod :
      0 ≤ ((1 : ℝ) / 4 - (t - s)) * ((1 : ℝ) / 4 + (t - s)) :=
    mul_nonneg (sub_nonneg.mpr hdelta_le) (by positivity)
  have hdelta_sq_pos : 0 < (t - s) ^ 2 := sq_pos_of_pos hdelta
  constructor
  · have hcoef : (s + t) ^ 2 < (18 : ℝ) := by nlinarith
    have hmul := mul_lt_mul_of_pos_left hcoef hdelta_sq_pos
    nlinarith
  · have hnonneg : 0 ≤ s ^ 2 + t ^ 2 := by positivity
    have hrad_sq : 4 ≤ (2 + s ^ 2 + t ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (s ^ 2 + t ^ 2)]
    nlinarith

/-- Uniform lower bound for the factor in `F(s,t,1)`. -/
theorem B_lower
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    (13 : ℝ) / 8 ≤ B s t := by
  rcases parameter_square_bounds hs hst ht with ⟨hs2, _ht2, _hstp⟩
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have hs2t : 0 ≤ s ^ 2 * t := by positivity
  have hst2 : 0 ≤ s * t ^ 2 := by positivity
  have ht3 : 0 ≤ t ^ 3 := by positivity
  unfold B
  nlinarith

/-- Uniform strict lower bound for the factor in `G(s,t,1)`. -/
theorem C_lower
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    (29 : ℝ) / 8 < C s t := by
  rcases parameter_square_bounds hs hst ht with ⟨_hs2, ht2, _hstp⟩
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hs3 : 0 ≤ s ^ 3 := by positivity
  have hs2t : 0 ≤ s ^ 2 * t := by positivity
  have hst2 : 0 ≤ s * t ^ 2 := by positivity
  have ht3 : 0 ≤ t ^ 3 := by positivity
  unfold C
  nlinarith

/-- The first stem anchor lies strictly inside the later circle. -/
theorem F_one_neg
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    F s t 1 < 0 := by
  rw [F_one]
  have hdelta : 0 < t - s := sub_pos.mpr hst
  have hB : 0 < B s t := lt_of_lt_of_le (by norm_num) (B_lower hs hst ht)
  nlinarith [mul_pos hdelta hB]

/-- The reverse stem anchor lies strictly outside the earlier circle. -/
theorem G_one_pos
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    0 < G s t 1 := by
  rw [G_one]
  have hdelta : 0 < t - s := sub_pos.mpr hst
  have hC : 0 < C s t := lt_trans (by norm_num) (C_lower hs hst ht)
  exact mul_pos hdelta hC

/-- Uniform positive derivative bound for the accepted mixed component. -/
theorem FhalfDerivativeAtOne_lower
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    (1 : ℝ) / 4 ≤ FhalfDerivativeAtOne s t := by
  have hdelta0 : 0 ≤ t - s := le_of_lt (sub_pos.mpr hst)
  have hdelta_le : t - s ≤ (1 : ℝ) / 4 := by nlinarith
  have hnonneg : 0 ≤ 2 * s + s ^ 2 := by positivity
  have hprod : 0 ≤ (t - s) * (2 * s + s ^ 2) :=
    mul_nonneg hdelta0 hnonneg
  have hsquare : 1 ≤ (1 + s ^ 2) ^ 2 := by
    nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]
  unfold FhalfDerivativeAtOne
  nlinarith

/-- The reverse mixed component is already increasing at its anchor. -/
theorem GhalfDerivativeAtOne_pos
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    0 < GhalfDerivativeAtOne s t := by
  rcases parameter_square_bounds hs hst ht with ⟨_hs2, ht2, _hstp⟩
  have hdelta : 0 < t - s := sub_pos.mpr hst
  have hfactor : (7 : ℝ) / 16 ≤ 1 - 2 * t - t ^ 2 := by
    nlinarith
  have hfactor0 : 0 ≤ 1 - 2 * t - t ^ 2 := le_trans (by norm_num) hfactor
  have hprod : 0 ≤ 3 * (t - s) * (1 - 2 * t - t ^ 2) := by positivity
  have hsq : 0 < (1 + t ^ 2) ^ 2 := by positivity
  unfold GhalfDerivativeAtOne
  nlinarith

/-- Determinant of the two polynomial stem directions. -/
theorem direction_determinant (s t : ℝ) :
    (1 - s ^ 2) * (-2 * t) - (-2 * s) * (1 - t ^ 2) =
      2 * (s - t) * (1 + s * t) := by
  ring

/-- The stem directions are nonparallel for distinct ordered parameters. -/
theorem direction_determinant_ne_zero
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    2 * (s - t) * (1 + s * t) ≠ 0 := by
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hleft : s - t < 0 := sub_neg.mpr hst
  have hright : 0 < 1 + s * t := by positivity
  have hneg_left : 2 * (s - t) < 0 :=
    mul_neg_of_pos_of_neg (by norm_num) hleft
  have hneg : 2 * (s - t) * (1 + s * t) < 0 :=
    mul_neg_of_neg_of_pos hneg_left hright
  exact ne_of_lt hneg

/-- Center-based parameter of the intersection on the `s` stem. -/
def lambda (s t : ℝ) : ℝ :=
  3 * (1 + 2 * t - t ^ 2) / (2 * (1 + s * t))

/-- Center-based parameter of the intersection on the `t` stem. -/
def mu (s t : ℝ) : ℝ :=
  3 * (1 + 2 * s - s ^ 2) / (2 * (1 + s * t))

/-- The explicit parameters solve the two supporting-line equations. -/
theorem rayRay_solution_coordinates
    (s t : ℝ) (hden : 1 + s * t ≠ 0) :
    3 * s + lambda s t * (1 - s ^ 2) =
        3 * t + mu s t * (1 - t ^ 2) ∧
      3 * s - 2 * s * lambda s t =
        3 * t - 2 * t * mu s t := by
  constructor <;> unfold lambda mu <;> field_simp [hden] <;> ring

/-- The intersection lies strictly beyond the anchor on the `s` stem. -/
theorem one_lt_lambda
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    1 < lambda s t := by
  rcases parameter_square_bounds hs hst ht with ⟨_hs2, ht2, hstp⟩
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hden : 0 < 2 * (1 + s * t) := by positivity
  unfold lambda
  rw [lt_div_iff₀ hden]
  nlinarith

/-- The intersection lies strictly beyond the anchor on the `t` stem. -/
theorem one_lt_mu
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    1 < mu s t := by
  rcases parameter_square_bounds hs hst ht with ⟨hs2, _ht2, hstp⟩
  have ht0 : 0 ≤ t := le_trans hs (le_of_lt hst)
  have hden : 0 < 2 * (1 + s * t) := by positivity
  unfold mu
  rw [lt_div_iff₀ hden]
  nlinarith

/-- The complete scalar package used by the corrected local crossing proof. -/
theorem corrected_local_pair_data
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    ((t - s) ^ 2 * (s + t) ^ 2 < 18 * (t - s) ^ 2 ∧
      18 * (t - s) ^ 2 < (2 + s ^ 2 + t ^ 2) ^ 2) ∧
    F s t 1 < 0 ∧
    (1 : ℝ) / 4 ≤ FhalfDerivativeAtOne s t ∧
    0 < G s t 1 ∧
    0 < GhalfDerivativeAtOne s t ∧
    2 * (s - t) * (1 + s * t) ≠ 0 ∧
    1 < lambda s t ∧
    1 < mu s t := by
  refine ⟨circle_strict_inequalities hs hst ht, ?_⟩
  refine ⟨F_one_neg hs hst ht, ?_⟩
  refine ⟨FhalfDerivativeAtOne_lower hs hst ht, ?_⟩
  refine ⟨G_one_pos hs hst ht, ?_⟩
  refine ⟨GhalfDerivativeAtOne_pos hs hst ht, ?_⟩
  refine ⟨direction_determinant_ne_zero hs hst, ?_⟩
  exact ⟨one_lt_lambda hs hst ht, one_lt_mu hs hst ht⟩

end

end PolynomialBlowUp
end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
