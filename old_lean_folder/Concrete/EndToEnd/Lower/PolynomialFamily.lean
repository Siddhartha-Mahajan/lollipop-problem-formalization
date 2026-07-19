import old_lean_folder.Concrete.EndToEnd.Lower.RationalBase
import old_lean_folder.Internal.Manuscript.PrimitiveGeometry.PolynomialBlowUp
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

export TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp
  (anchor center corrected_local_pair_data direction_determinant F
    F_eq_geometry G G_eq_geometry GhalfDerivativeAtOne lambda mu
    normSq2_vector radius radius_pos vector vector_ne_zero)

end PB

/-- Concrete version of the corrected polynomial family. -/
def member (t : ℝ) : Lollipop where
  center := R2.toPoint (PB.center t)
  radial := R2.toPoint (PB.vector t)
  radial_ne_zero := by
    intro h
    apply PB.vector_ne_zero t
    have := congrArg R2.ofPoint h
    have hzero : R2.ofPoint (0 : Point) = (0 : R2) := by
      ext i
      rfl
    rwa [hzero] at this

@[simp] theorem local_center (t : ℝ) :
    (member t).center = R2.toPoint (PB.center t) := rfl

@[simp] theorem local_radial (t : ℝ) :
    (member t).radial = R2.toPoint (PB.vector t) := rfl

/-- The radius is the polynomial `1+t²`. -/
@[simp] theorem local_radius (t : ℝ) :
    (member t).radius = PB.radius t := by
  have hsq := PB.normSq2_vector t
  have hnonneg : 0 ≤ (member t).radius := norm_nonneg _
  have hpos := PB.radius_pos t
  have hsquare : (member t).radius ^ 2 = PB.radius t ^ 2 := by
    rw [Lollipop.radius, local_radial, R2.norm_sq_toPoint]
    exact hsq
  nlinarith

/-- Unit direction is the polynomial vector divided by `1+t²`. -/
@[simp] theorem local_unitRadial (t : ℝ) :
    (member t).unitRadial =
      (PB.radius t)⁻¹ • R2.toPoint (PB.vector t) := by
  simp [Lollipop.unitRadial, local_radius, local_radial]

@[simp] theorem local_anchor (t : ℝ) :
    (member t).anchor = R2.toPoint (PB.anchor t) := by
  simp [Lollipop.anchor, member, PB.anchor, R2.toPoint_add]

/-- The family starts at the standard unit lollipop. -/
@[simp] theorem local_zero : member 0 = standardLollipop := by
  ext <;>
    simp [member, standardLollipop, PB.center, PB.vector,
      TheoremOneManuscript.PrimitiveGeometry.point2]

/-- Polynomial continuity of the family in center/radial coordinates. -/
theorem continuous_local : Continuous member := by
  rw [continuous_induced_rng]
  change Continuous (fun t : ℝ =>
    (R2.toPoint (PB.center t), R2.toPoint (PB.vector t)))
  have hc : Continuous (fun t : ℝ => R2.toPoint (PB.center t)) := by
    unfold R2.toPoint TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
      TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp.center
      TheoremOneManuscript.PrimitiveGeometry.point2
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp
      (continuous_pi (by
        intro i
        fin_cases i <;> simp <;> fun_prop))
  have hv : Continuous (fun t : ℝ => R2.toPoint (PB.vector t)) := by
    unfold R2.toPoint TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
      TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp.vector
      TheoremOneManuscript.PrimitiveGeometry.point2
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℝ)).comp
      (continuous_pi (by
        intro i
        fin_cases i <;> simp <;> fun_prop))
  exact hc.prodMk hv

/-- Similarity transport is continuous in lollipop coordinates. -/
theorem continuous_mapLollipop (S : PlaneSimilarity) :
    Continuous (fun L : Lollipop => S.mapLollipop L) := by
  rw [continuous_induced_rng]
  change Continuous (fun L : Lollipop =>
    ((S.mapLollipop L).center, (S.mapLollipop L).radial))
  have hc : Continuous (fun L : Lollipop => (S.mapLollipop L).center) := by
    change Continuous (fun L : Lollipop => S.toFun L.center)
    unfold PlaneSimilarity.toFun
    fun_prop
  have hr : Continuous (fun L : Lollipop => (S.mapLollipop L).radial) := by
    change Continuous (fun L : Lollipop => S.scale • S.orthogonal L.radial)
    fun_prop
  exact hc.prodMk hr

namespace DiagnosticBridge

/-- The displayed squared norm agrees with the primitive squared-distance
formula after lifting `R2` coordinates to `Point`. -/
theorem normSqPoint_toPoint_sub (x y : R2) :
    normSqPoint (R2.toPoint x - R2.toPoint y) =
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2 x y := by
  unfold normSqPoint dotPoint
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  simp

/-- Exact center-distance polynomial. -/
theorem centerDistanceSq_local (s t : ℝ) :
    centerDistanceSq (member s) (member t) = 18 * (t - s) ^ 2 := by
  unfold centerDistanceSq displacement normSqPoint dotPoint member
    PB.center TheoremOneManuscript.PrimitiveGeometry.point2
  simp
  ring

/-- Exact circle outer margin. -/
theorem outerMargin_local (s t : ℝ) :
    circleOuterMargin (member s) (member t) =
      (2 + s ^ 2 + t ^ 2) ^ 2 - 18 * (t - s) ^ 2 := by
  rw [circleOuterMargin, local_radius, local_radius,
    centerDistanceSq_local]
  unfold PB.radius
  ring

/-- Exact circle inner margin. -/
theorem innerMargin_local (s t : ℝ) :
    circleInnerMargin (member s) (member t) =
      18 * (t - s) ^ 2 - (t - s) ^ 2 * (s + t) ^ 2 := by
  rw [circleInnerMargin, local_radius, local_radius,
    centerDistanceSq_local]
  unfold PB.radius
  ring

/-- Forward anchor power is `F(s,t,1)`. -/
theorem forwardAnchorPower_local (s t : ℝ) :
    anchorPower (member s) (member t) = PB.F s t 1 := by
  rw [anchorPower, local_anchor, local_center, local_radius,
    normSqPoint_toPoint_sub]
  rw [show PB.anchor s =
      TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp.stemPoint s 1 by
    simp [PB.anchor,
      TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp.stemPoint]]
  exact (PB.F_eq_geometry s t 1).symm

/-- Reverse anchor power is `G(s,t,1)`. -/
theorem reverseAnchorPower_local (s t : ℝ) :
    anchorPower (member t) (member s) = PB.G s t 1 := by
  rw [anchorPower, local_anchor, local_center, local_radius,
    normSqPoint_toPoint_sub]
  rw [show PB.anchor t =
      TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp.stemPoint t 1 by
    simp [PB.anchor,
      TheoremOneManuscript.PrimitiveGeometry.PolynomialBlowUp.stemPoint]]
  exact (PB.G_eq_geometry s t 1).symm

/-- Existing derivative diagnostic equals minus radius times `vertexAhead` for
the reverse mixed component. -/
theorem reverseDerivative_eq_neg_radius_mul_vertexAhead (s t : ℝ) :
    PB.GhalfDerivativeAtOne s t =
      -(PB.radius t) * vertexAhead (member t) (member s) := by
  unfold vertexAhead projectedCenterParameter displacement dotPoint
  rw [local_center, local_center, local_unitRadial, local_radius]
  unfold PB.GhalfDerivativeAtOne PB.radius PB.center PB.vector
    TheoremOneManuscript.PrimitiveGeometry.point2
  simp
  field_simp [ne_of_gt (PB.radius_pos t)]
  ring_nf

/-- Forward negative anchor power forces positive discriminant. -/
theorem forward_discriminant_pos_of_anchor_neg
    {s t : ℝ} (h : anchorPower (member s) (member t) < 0) :
    0 < lineDiscriminant (member s) (member t) := by
  have hid := PairChamberPort.anchorPower_eq_mixed_at_anchor
    (member s) (member t)
  nlinarith [sq_nonneg
    ((member s).radius - projectedCenterParameter (member s) (member t))]

/-- Determinant of actual unit directions. -/
theorem directionDet_local (s t : ℝ) :
    directionDet (member s) (member t) =
      (2 * (s - t) * (1 + s * t)) /
        (PB.radius s * PB.radius t) := by
  unfold directionDet detPoint
  rw [local_unitRadial, local_unitRadial]
  simp [PB.vector,
    TheoremOneManuscript.PrimitiveGeometry.point2]
  unfold PB.radius
  field_simp [ne_of_gt (PB.radius_pos s), ne_of_gt (PB.radius_pos t)]
  ring

/-- The line parameters are the old center-based parameters times radius. -/
theorem leftLineParameter_local {s t : ℝ}
    (hdet : 2 * (s - t) * (1 + s * t) ≠ 0) :
    leftLineParameter (member s) (member t) =
      PB.radius s * PB.lambda s t := by
  have hden : -(t * (1 - s ^ 2)) + s * (1 - t ^ 2) ≠ 0 := by
    intro h
    apply hdet
    have hfac :
        -(t * (1 - s ^ 2)) + s * (1 - t ^ 2) =
          (s - t) * (1 + s * t) := by ring
    have hprod : (s - t) * (1 + s * t) = 0 := by
      rw [← hfac]
      exact h
    calc
      2 * (s - t) * (1 + s * t) =
          2 * ((s - t) * (1 + s * t)) := by ring
      _ = 0 := by rw [hprod]; ring
  have hone : 1 + s * t ≠ 0 := by
    intro h
    apply hdet
    rw [h]
    ring
  have hone' : 1 + t * s ≠ 0 := by
    convert hone using 1 <;> ring
  unfold leftLineParameter displacement directionDet detPoint
  rw [local_center, local_center, local_unitRadial, local_unitRadial]
  simp [PB.center, PB.vector,
    TheoremOneManuscript.PrimitiveGeometry.point2]
  field_simp [ne_of_gt (PB.radius_pos s),
    ne_of_gt (PB.radius_pos t), hden, hone]
  simp [PB.lambda]
  field_simp [hone']
  ring_nf

/-- Symmetric line parameter formula. -/
theorem rightLineParameter_local {s t : ℝ}
    (hdet : 2 * (s - t) * (1 + s * t) ≠ 0) :
    rightLineParameter (member s) (member t) =
      PB.radius t * PB.mu s t := by
  have hden : -(t * (1 - s ^ 2)) + s * (1 - t ^ 2) ≠ 0 := by
    intro h
    apply hdet
    have hfac :
        -(t * (1 - s ^ 2)) + s * (1 - t ^ 2) =
          (s - t) * (1 + s * t) := by ring
    have hprod : (s - t) * (1 + s * t) = 0 := by
      rw [← hfac]
      exact h
    calc
      2 * (s - t) * (1 + s * t) =
          2 * ((s - t) * (1 + s * t)) := by ring
      _ = 0 := by rw [hprod]; ring
  have hone : 1 + s * t ≠ 0 := by
    intro h
    apply hdet
    rw [h]
    ring
  have hone' : 1 + t * s ≠ 0 := by
    convert hone using 1 <;> ring
  unfold rightLineParameter displacement directionDet detPoint
  rw [local_center, local_center, local_unitRadial, local_unitRadial]
  simp [PB.center, PB.vector,
    TheoremOneManuscript.PrimitiveGeometry.point2]
  field_simp [ne_of_gt (PB.radius_pos s),
    ne_of_gt (PB.radius_pos t), hden, hone]
  simp [PB.mu]
  field_simp [hone']
  ring_nf

end DiagnosticBridge

/-- Distinct ordered local members realize the strict four-crossing code. -/
theorem local_realizes_four
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    RealizesStrictPairCode StrictPairCode.four (member s) (member t) := by
  rcases PB.corrected_local_pair_data hs hst ht with
    ⟨hcircle, hFneg, _hFderiv, hGpos, hGderiv,
      hdet, hlambda, hmu⟩
  have hout : 0 < circleOuterMargin (member s) (member t) := by
    rw [DiagnosticBridge.outerMargin_local]
    exact sub_pos.mpr hcircle.2
  have hin : 0 < circleInnerMargin (member s) (member t) := by
    rw [DiagnosticBridge.innerMargin_local]
    exact sub_pos.mpr hcircle.1
  have hforwardPower : anchorPower (member s) (member t) < 0 := by
    rw [DiagnosticBridge.forwardAnchorPower_local]
    exact hFneg
  have hforwardDisc : 0 < lineDiscriminant (member s) (member t) :=
    DiagnosticBridge.forward_discriminant_pos_of_anchor_neg hforwardPower
  have hreversePower : 0 < anchorPower (member t) (member s) := by
    rw [DiagnosticBridge.reverseAnchorPower_local]
    exact hGpos
  have hreverseVertex : vertexAhead (member t) (member s) < 0 := by
    have hrpos := PB.radius_pos t
    rw [DiagnosticBridge.reverseDerivative_eq_neg_radius_mul_vertexAhead] at hGderiv
    nlinarith
  have hdet' : directionDet (member s) (member t) ≠ 0 := by
    rw [DiagnosticBridge.directionDet_local]
    exact div_ne_zero hdet
      (mul_ne_zero (PB.radius_pos s).ne' (PB.radius_pos t).ne')
  have hleft : (member s).radius <
      leftLineParameter (member s) (member t) := by
    rw [DiagnosticBridge.leftLineParameter_local hdet, local_radius]
    nlinarith [PB.radius_pos s]
  have hright : (member t).radius <
      rightLineParameter (member s) (member t) := by
    rw [DiagnosticBridge.rightLineParameter_local hdet, local_radius]
    nlinarith [PB.radius_pos t]
  exact ⟨hout, hin,
    ⟨hforwardDisc, hforwardPower⟩,
    Or.inr ⟨hreversePower, hreverseVertex⟩,
    by simpa [RayRayCodeRealized, StrictPairCode.four] using
      And.intro hdet' (And.intro hleft hright)⟩

/-- The corrected local family has exactly four finite crossings. -/
theorem local_pairCrossingCount_eq_four
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    pairCrossingCount (member s) (member t) = 4 := by
  simpa using pairCrossingCount_eq_of_realizes
    (local_realizes_four hs hst ht)

/-- The corrected local family is pairwise primitive-transverse. -/
theorem local_pair_transverse
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ (1 : ℝ) / 4) :
    PrimitivePairwiseTransverse (member s) (member t) :=
  primitivePairwiseTransverse_of_realizes (local_realizes_four hs hst ht)

/-- Same-cluster family based at an arbitrary base lollipop. -/
def around (Q : Lollipop) (t : ℝ) : Lollipop :=
  (similarityTo Q).mapLollipop (member t)

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

end PolynomialFamily
end Lower
end EndToEnd
end Concrete
end Lollipop
