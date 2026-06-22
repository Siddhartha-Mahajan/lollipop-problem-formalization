import Lollipop.Concrete.EndToEnd.Lower.RationalBase
import Lollipop.Internal.Manuscript.PrimitiveGeometry.PolynomialBlowUp
import Mathlib.Tactic

/-!
# Corrected polynomial four-crossing family

For `0 ≤ t ≤ 1/4`, put

`c(t) = (3t,3t)`, `v(t) = (1-t²,-2t)`.

The identity `‖v(t)‖ = 1+t²` makes this a concrete radial lollipop without any
square roots.  Distinct ordered parameters satisfy the strict chamber
`2+1+0+1=4`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower
namespace PolynomialFamily

open Set

namespace PB

abbrev Old :=
  TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp

end PB

/-- Concrete version of the corrected polynomial family. -/
def local (t : ℝ) : Lollipop where
  center := R2.toPoint (PB.Old.center t)
  radial := R2.toPoint (PB.Old.vector t)
  radial_ne_zero := by
    intro h
    apply PB.Old.vector_ne_zero t
    have := congrArg R2.ofPoint h
    simpa using this

@[simp] theorem local_center (t : ℝ) :
    (local t).center = R2.toPoint (PB.Old.center t) := rfl

@[simp] theorem local_radial (t : ℝ) :
    (local t).radial = R2.toPoint (PB.Old.vector t) := rfl

/-- The radius is the polynomial `1+t²`. -/
@[simp] theorem local_radius (t : ℝ) :
    (local t).radius = PB.Old.radius t := by
  have hsq := PB.Old.normSq2_vector t
  have hnonneg : 0 ≤ (local t).radius := norm_nonneg _
  have hpos := PB.Old.radius_pos t
  have hsquare : (local t).radius ^ 2 = PB.Old.radius t ^ 2 := by
    rw [Lollipop.radius, local_radial, R2.norm_sq_toPoint]
    exact hsq
  nlinarith

/-- Unit direction is the polynomial vector divided by `1+t²`. -/
@[simp] theorem local_unitRadial (t : ℝ) :
    (local t).unitRadial =
      (PB.Old.radius t)⁻¹ • R2.toPoint (PB.Old.vector t) := by
  simp [Lollipop.unitRadial, local_radius, local_radial]

@[simp] theorem local_anchor (t : ℝ) :
    (local t).anchor = R2.toPoint (PB.Old.anchor t) := by
  simp [Lollipop.anchor, local, PB.Old.anchor, R2.toPoint_add]

/-- The family starts at the standard unit lollipop. -/
@[simp] theorem local_zero : local 0 = standardLollipop := by
  ext <;>
    simp [local, standardLollipop, PB.Old.center, PB.Old.vector,
      TheoremOneManuscript.PrimitiveGeometry.point2]

/-- Polynomial continuity of the family in center/radial coordinates. -/
theorem continuous_local : Continuous local := by
  apply continuous_lollipop_mk
  · unfold local PB.Old.center
    fun_prop
  · unfold local PB.Old.vector
    fun_prop

namespace DiagnosticBridge

/-- Exact center-distance polynomial. -/
theorem centerDistanceSq_local (s t : ℝ) :
    centerDistanceSq (local s) (local t) = 18 * (t - s) ^ 2 := by
  unfold centerDistanceSq displacement normSqPoint dotPoint local
    PB.Old.center TheoremOneManuscript.PrimitiveGeometry.point2
  simp [Pi.sub_apply]
  ring

/-- Exact circle outer margin. -/
theorem outerMargin_local (s t : ℝ) :
    circleOuterMargin (local s) (local t) =
      (2 + s ^ 2 + t ^ 2) ^ 2 - 18 * (t - s) ^ 2 := by
  rw [circleOuterMargin, local_radius, local_radius,
    centerDistanceSq_local]
  unfold PB.Old.radius
  ring

/-- Exact circle inner margin. -/
theorem innerMargin_local (s t : ℝ) :
    circleInnerMargin (local s) (local t) =
      18 * (t - s) ^ 2 - (t - s) ^ 2 * (s + t) ^ 2 := by
  rw [circleInnerMargin, local_radius, local_radius,
    centerDistanceSq_local]
  unfold PB.Old.radius
  ring

/-- Forward anchor power is `F(s,t,1)`. -/
theorem forwardAnchorPower_local (s t : ℝ) :
    anchorPower (local s) (local t) = PB.Old.F s t 1 := by
  rw [anchorPower, local_anchor, local_center, local_radius,
    ← PB.Old.F_eq_geometry]
  unfold normSqPoint dotPoint
  rw [← TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq]
  rfl

/-- Reverse anchor power is `G(s,t,1)`. -/
theorem reverseAnchorPower_local (s t : ℝ) :
    anchorPower (local t) (local s) = PB.Old.G s t 1 := by
  rw [anchorPower, local_anchor, local_center, local_radius,
    ← PB.Old.G_eq_geometry]
  unfold normSqPoint dotPoint
  rw [← TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq]
  rfl

/-- Existing derivative diagnostic equals minus radius times `vertexAhead` for
the reverse mixed component. -/
theorem reverseDerivative_eq_neg_radius_mul_vertexAhead (s t : ℝ) :
    PB.Old.GhalfDerivativeAtOne s t =
      -(PB.Old.radius t) * vertexAhead (local t) (local s) := by
  unfold PB.Old.GhalfDerivativeAtOne PB.Old.radius vertexAhead
    projectedCenterParameter displacement dotPoint Lollipop.unitRadial
    local PB.Old.center PB.Old.vector
    TheoremOneManuscript.PrimitiveGeometry.point2
  simp [Pi.sub_apply, Pi.smul_apply]
  field_simp [ne_of_gt (PB.Old.radius_pos t)]
  ring

/-- Forward negative anchor power forces positive discriminant. -/
theorem forward_discriminant_pos_of_anchor_neg
    {s t : ℝ} (h : anchorPower (local s) (local t) < 0) :
    0 < lineDiscriminant (local s) (local t) := by
  have hid := PairChamberPort.anchorPower_eq_mixed_at_anchor
    (local s) (local t)
  nlinarith [sq_nonneg
    ((local s).radius - projectedCenterParameter (local s) (local t))]

/-- Determinant of actual unit directions. -/
theorem directionDet_local (s t : ℝ) :
    directionDet (local s) (local t) =
      (2 * (s - t) * (1 + s * t)) /
        (PB.Old.radius s * PB.Old.radius t) := by
  unfold directionDet detPoint
  rw [local_unitRadial, local_unitRadial]
  simp [Pi.smul_apply, PB.Old.vector,
    TheoremOneManuscript.PrimitiveGeometry.point2]
  rw [PB.Old.direction_determinant]
  ring

/-- The line parameters are the old center-based parameters times radius. -/
theorem leftLineParameter_local (s t : ℝ) :
    leftLineParameter (local s) (local t) =
      PB.Old.radius s * PB.Old.lambda s t := by
  unfold leftLineParameter displacement directionDet detPoint
  rw [local_center, local_center, local_unitRadial, local_unitRadial]
  simp [PB.Old.center, PB.Old.vector,
    TheoremOneManuscript.PrimitiveGeometry.point2,
    Pi.sub_apply, Pi.smul_apply]
  field_simp [ne_of_gt (PB.Old.radius_pos s),
    ne_of_gt (PB.Old.radius_pos t)]
  unfold PB.Old.lambda PB.Old.radius
  ring

/-- Symmetric line parameter formula. -/
theorem rightLineParameter_local (s t : ℝ) :
    rightLineParameter (local s) (local t) =
      PB.Old.radius t * PB.Old.mu s t := by
  unfold rightLineParameter displacement directionDet detPoint
  rw [local_center, local_center, local_unitRadial, local_unitRadial]
  simp [PB.Old.center, PB.Old.vector,
    TheoremOneManuscript.PrimitiveGeometry.point2,
    Pi.sub_apply, Pi.smul_apply]
  field_simp [ne_of_gt (PB.Old.radius_pos s),
    ne_of_gt (PB.Old.radius_pos t)]
  unfold PB.Old.mu PB.Old.radius
  ring

end DiagnosticBridge

/-- Distinct ordered local members realize the strict four-crossing code. -/
theorem local_realizes_four
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    RealizesStrictPairCode StrictPairCode.four (local s) (local t) := by
  rcases PB.Old.corrected_local_pair_data hs hst ht with
    ⟨hcircle, hFneg, _hFderiv, hGpos, hGderiv,
      hdet, hlambda, hmu⟩
  have hout : 0 < circleOuterMargin (local s) (local t) := by
    rw [DiagnosticBridge.outerMargin_local]
    exact sub_pos.mpr hcircle.2
  have hin : 0 < circleInnerMargin (local s) (local t) := by
    rw [DiagnosticBridge.innerMargin_local]
    exact sub_pos.mpr hcircle.1
  have hforwardPower : anchorPower (local s) (local t) < 0 := by
    rw [DiagnosticBridge.forwardAnchorPower_local]
    exact hFneg
  have hforwardDisc : 0 < lineDiscriminant (local s) (local t) :=
    DiagnosticBridge.forward_discriminant_pos_of_anchor_neg hforwardPower
  have hreversePower : 0 < anchorPower (local t) (local s) := by
    rw [DiagnosticBridge.reverseAnchorPower_local]
    exact hGpos
  have hreverseVertex : vertexAhead (local t) (local s) < 0 := by
    have hrpos := PB.Old.radius_pos t
    rw [DiagnosticBridge.reverseDerivative_eq_neg_radius_mul_vertexAhead] at hGderiv
    nlinarith
  have hdet' : directionDet (local s) (local t) ≠ 0 := by
    rw [DiagnosticBridge.directionDet_local]
    exact div_ne_zero hdet
      (mul_ne_zero (PB.Old.radius_pos s).ne' (PB.Old.radius_pos t).ne')
  have hleft : (local s).radius <
      leftLineParameter (local s) (local t) := by
    rw [DiagnosticBridge.leftLineParameter_local, local_radius]
    nlinarith [PB.Old.radius_pos s]
  have hright : (local t).radius <
      rightLineParameter (local s) (local t) := by
    rw [DiagnosticBridge.rightLineParameter_local, local_radius]
    nlinarith [PB.Old.radius_pos t]
  exact ⟨hout, hin,
    ⟨hforwardDisc, hforwardPower⟩,
    Or.inr ⟨hreversePower, hreverseVertex⟩,
    by simpa [RayRayCodeRealized, StrictPairCode.four] using
      And.intro hdet' (And.intro hleft hright)⟩

/-- The corrected local family has exactly four finite crossings. -/
theorem local_pairCrossingCount_eq_four
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    pairCrossingCount (local s) (local t) = 4 := by
  simpa using pairCrossingCount_eq_of_realizes
    (local_realizes_four hs hst ht)

/-- The corrected local family is pairwise primitive-transverse. -/
theorem local_pair_transverse
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    PrimitivePairwiseTransverse (local s) (local t) :=
  primitivePairwiseTransverse_of_realizes (local_realizes_four hs hst ht)

/-- Same-cluster family based at an arbitrary base lollipop. -/
def around (Q : Lollipop) (t : ℝ) : Lollipop :=
  (similarityTo Q).mapLollipop (local t)

@[simp] theorem around_zero (Q : Lollipop) : around Q 0 = Q := by
  simp [around, similarityTo_standard]

/-- Continuity of the transported local family. -/
theorem continuous_around (Q : Lollipop) : Continuous (around Q) := by
  exact continuous_mapLollipop (similarityTo Q) |>.comp continuous_local

/-- A positive similarity preserves the exact four-crossing local pattern. -/
theorem around_pairCrossingCount_eq_four
    (Q : Lollipop) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    pairCrossingCount (around Q s) (around Q t) = 4 := by
  rw [around, around, PlaneSimilarity.pairCrossingCount_map]
  exact local_pairCrossingCount_eq_four hs hst ht

/-- Similarity transport preserves primitive transversality. -/
theorem around_pair_transverse
    (Q : Lollipop) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    PrimitivePairwiseTransverse (around Q s) (around Q t) := by
  exact primitivePairwiseTransverse_map
    (similarityTo Q) (local_pair_transverse hs hst ht)

end PolynomialFamily
end Lower
end EndToEnd
end Concrete
end Lollipop
