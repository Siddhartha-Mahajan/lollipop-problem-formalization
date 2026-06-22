import Lollipop.Concrete.EndToEnd.Lower.PairChamber
import Mathlib.Tactic

/-!
# Exact rational four-lollipop base

This is the corrected all-rational Karlsson base used by the manuscript.  The
six unordered pairs have crossing codes

* `(0,1)`: five;
* `(0,2)`, `(0,3)`, `(1,2)`, `(1,3)`, `(2,3)`: seven.

Every decisive sign is proved from an exact rational identity.  The smallest
positive ray--ray margin is `151 / 23400` for pair `(1,2)`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower
namespace RationalBase

open Set

/-- Displayed coordinate pair. -/
def point2 (x y : ℝ) : Point := fun i => if i = 0 then x else y

@[simp] theorem point2_zero (x y : ℝ) : point2 x y 0 = x := by
  simp [point2]

@[simp] theorem point2_one (x y : ℝ) : point2 x y 1 = y := by
  simp [point2]

@[ext] theorem point2_ext {p q : Point}
    (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q := by
  ext i
  fin_cases i <;> assumption

/-- A lollipop specified by center, radius and a unit rational direction. -/
def fromCenter (c : Point) (r : ℝ) (u : Point)
    (hr : 0 < r) (hu : normSqPoint u = 1) : Lollipop where
  center := c
  radial := r • u
  radial_ne_zero := by
    intro h
    have hcoord := congrArg (fun v : Point => normSqPoint v) h
    simp [normSqPoint, dotPoint, Pi.smul_apply] at hcoord
    have : r ^ 2 * normSqPoint u = 0 := by
      simpa [normSqPoint, dotPoint, Pi.smul_apply] using hcoord
    rw [hu] at this
    nlinarith

/-- A lollipop specified by anchor, radius and a unit rational direction. -/
def fromAnchor (a : Point) (r : ℝ) (u : Point)
    (hr : 0 < r) (hu : normSqPoint u = 1) : Lollipop :=
  fromCenter (a - r • u) r u hr hu

@[simp] theorem fromCenter_center
    (c : Point) (r : ℝ) (u : Point) (hr hu) :
    (fromCenter c r u hr hu).center = c := rfl

/-- Norm bridge used to simplify exact rational radii. -/
theorem norm_eq_one_of_normSqPoint_eq_one
    {u : Point} (hu : normSqPoint u = 1) : ‖u‖ = 1 := by
  have hnonneg : 0 ≤ ‖u‖ := norm_nonneg _
  have hsquare : ‖u‖ ^ 2 = 1 := by
    simpa [normSqPoint, dotPoint, EuclideanSpace.norm_sq_eq] using hu
  nlinarith

@[simp] theorem fromCenter_radius
    (c : Point) (r : ℝ) (u : Point) (hr : 0 < r)
    (hu : normSqPoint u = 1) :
    (fromCenter c r u hr hu).radius = r := by
  simp [fromCenter, Lollipop.radius, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, norm_eq_one_of_normSqPoint_eq_one hu]

@[simp] theorem fromCenter_unitRadial
    (c : Point) (r : ℝ) (u : Point) (hr : 0 < r)
    (hu : normSqPoint u = 1) :
    (fromCenter c r u hr hu).unitRadial = u := by
  simp [Lollipop.unitRadial, fromCenter_radius, fromCenter,
    smul_smul, hr.ne']

@[simp] theorem fromCenter_anchor
    (c : Point) (r : ℝ) (u : Point) (hr : 0 < r)
    (hu : normSqPoint u = 1) :
    (fromCenter c r u hr hu).anchor = c + r • u := by
  simp [Lollipop.anchor, fromCenter]

@[simp] theorem fromAnchor_center
    (a : Point) (r : ℝ) (u : Point) (hr hu) :
    (fromAnchor a r u hr hu).center = a - r • u := rfl

@[simp] theorem fromAnchor_radius
    (a : Point) (r : ℝ) (u : Point) (hr : 0 < r)
    (hu : normSqPoint u = 1) :
    (fromAnchor a r u hr hu).radius = r := by
  simp [fromAnchor]

@[simp] theorem fromAnchor_unitRadial
    (a : Point) (r : ℝ) (u : Point) (hr : 0 < r)
    (hu : normSqPoint u = 1) :
    (fromAnchor a r u hr hu).unitRadial = u := by
  simp [fromAnchor]

@[simp] theorem fromAnchor_anchor
    (a : Point) (r : ℝ) (u : Point) (hr : 0 < r)
    (hu : normSqPoint u = 1) :
    (fromAnchor a r u hr hu).anchor = a := by
  simp [fromAnchor, Lollipop.anchor, fromCenter]

/-- The four exact unit directions. -/
def u0 : Point := point2 1 0
def u1 : Point := point2 (144 / 145) (-17 / 145)
def u2 : Point := point2 (-36 / 85) (-77 / 85)
def u3 : Point := point2 (-17 / 145) (144 / 145)

@[simp] theorem u0_unit : normSqPoint u0 = 1 := by
  norm_num [u0, point2, normSqPoint, dotPoint]

@[simp] theorem u1_unit : normSqPoint u1 = 1 := by
  norm_num [u1, point2, normSqPoint, dotPoint]

@[simp] theorem u2_unit : normSqPoint u2 = 1 := by
  norm_num [u2, point2, normSqPoint, dotPoint]

@[simp] theorem u3_unit : normSqPoint u3 = 1 := by
  norm_num [u3, point2, normSqPoint, dotPoint]

/-- The corrected rational base. -/
def Q0 : Lollipop :=
  fromAnchor (point2 0 0) 200 u0 (by norm_num) u0_unit

def Q1 : Lollipop :=
  fromCenter (point2 (9/20) (2/5)) (11/20) u1 (by norm_num) u1_unit

def Q2 : Lollipop :=
  fromAnchor (point2 (23/20) (13/20)) 100 u2 (by norm_num) u2_unit

def Q3 : Lollipop :=
  fromAnchor (point2 (21/20) (-1/20)) 100 u3 (by norm_num) u3_unit

/-- Base indexed by `Fin 4`. -/
def base : Fin 4 → Lollipop
  | 0 => Q0
  | 1 => Q1
  | 2 => Q2
  | 3 => Q3

/-- All scalar diagnostics used by one unordered pair. -/
structure Diagnostics where
  outerMargin : ℝ
  innerMargin : ℝ
  forwardDiscriminant : ℝ
  forwardAnchorPower : ℝ
  forwardVertexAhead : ℝ
  reverseDiscriminant : ℝ
  reverseAnchorPower : ℝ
  reverseVertexAhead : ℝ
  determinant : ℝ
  leftParameterMargin : ℝ
  rightParameterMargin : ℝ
  deriving Repr

/-- Compute the exact diagnostic record of an ordered pair. -/
def diagnostics (L M : Lollipop) : Diagnostics where
  outerMargin := circleOuterMargin L M
  innerMargin := circleInnerMargin L M
  forwardDiscriminant := lineDiscriminant L M
  forwardAnchorPower := anchorPower L M
  forwardVertexAhead := vertexAhead L M
  reverseDiscriminant := lineDiscriminant M L
  reverseAnchorPower := anchorPower M L
  reverseVertexAhead := vertexAhead M L
  determinant := directionDet L M
  leftParameterMargin := leftLineParameter L M - L.radius
  rightParameterMargin := rightLineParameter L M - M.radius

/-- Exact pair `(0,1)` values. -/
theorem diagnostics_Q0_Q1 : diagnostics Q0 Q1 =
    { outerMargin := 1997/50
      innerMargin := 20003/50
      forwardDiscriminant := 57/400
      forwardAnchorPower := 3/50
      forwardVertexAhead := 9/20
      reverseDiscriminant := 13263872679/336400
      reverseAnchorPower := 2317609/5800
      reverseVertexAhead := -115751/580
      determinant := -17/145
      leftParameterMargin := 261/68
      rightParameterMargin := 973/340 } := by
  ext <;> norm_num [diagnostics, Q0, Q1, fromAnchor, fromCenter,
    circleOuterMargin, circleInnerMargin, centerDistanceSq, displacement,
    normSqPoint, projectedCenterParameter, lineDiscriminant, anchorPower,
    vertexAhead, directionDet, leftLineParameter, rightLineParameter,
    detPoint, dotPoint, Lollipop.anchor, Lollipop.unitRadial,
    Lollipop.radius, point2, u0, u1, EuclideanSpace.norm_sq_eq]

/-- Exact pair `(0,2)` values. -/
theorem diagnostics_Q0_Q2 : diagnostics Q0 Q2 =
    { outerMargin := 76098467/3400
      innerMargin := 195901533/3400
      forwardDiscriminant := 193697559/115600
      forwardAnchorPower := 737533/3400
      forwardVertexAhead := 14791/340
      reverseDiscriminant := 19931654191/2890000
      reverseAnchorPower := 92349/200
      reverseVertexAhead := 145829/1700
      determinant := -77/85
      leftParameterMargin := 1303/1540
      rightParameterMargin := 221/308 } := by
  ext <;> norm_num [diagnostics, Q0, Q2, fromAnchor, fromCenter,
    circleOuterMargin, circleInnerMargin, centerDistanceSq, displacement,
    normSqPoint, projectedCenterParameter, lineDiscriminant, anchorPower,
    vertexAhead, directionDet, leftLineParameter, rightLineParameter,
    detPoint, dotPoint, Lollipop.anchor, Lollipop.unitRadial,
    Lollipop.radius, point2, u0, u2, EuclideanSpace.norm_sq_eq]

/-- Exact pair `(0,3)` values. -/
theorem diagnostics_Q0_Q3 : diagnostics Q0 Q3 =
    { outerMargin := 202157191/5800
      innerMargin := 261842809/5800
      forwardDiscriminant := 42898359/336400
      forwardAnchorPower := 206809/5800
      forwardVertexAhead := 7409/580
      reverseDiscriminant := 1150893951/8410000
      reverseAnchorPower := 84221/200
      reverseVertexAhead := 68501/2900
      determinant := 144/145
      leftParameterMargin := 3007/2880
      rightParameterMargin := 29/576 } := by
  ext <;> norm_num [diagnostics, Q0, Q3, fromAnchor, fromCenter,
    circleOuterMargin, circleInnerMargin, centerDistanceSq, displacement,
    normSqPoint, projectedCenterParameter, lineDiscriminant, anchorPower,
    vertexAhead, directionDet, leftLineParameter, rightLineParameter,
    detPoint, dotPoint, Lollipop.anchor, Lollipop.unitRadial,
    Lollipop.radius, point2, u0, u3, EuclideanSpace.norm_sq_eq]

/-- Exact pair `(1,2)` values. -/
theorem diagnostics_Q1_Q2 : diagnostics Q1 Q2 =
    { outerMargin := 351/68
      innerMargin := 14609/68
      forwardDiscriminant := 562449451551/607622500
      forwardAnchorPower := 17286209/246500
      forwardVertexAhead := 388928/12325
      reverseDiscriminant := 67821/2890000
      reverseAnchorPower := 1/4
      reverseVertexAhead := 889/1700
      determinant := -468/493
      leftParameterMargin := 151/23400
      rightParameterMargin := 8143/23400 } := by
  ext <;> norm_num [diagnostics, Q1, Q2, fromAnchor, fromCenter,
    circleOuterMargin, circleInnerMargin, centerDistanceSq, displacement,
    normSqPoint, projectedCenterParameter, lineDiscriminant, anchorPower,
    vertexAhead, directionDet, leftLineParameter, rightLineParameter,
    detPoint, dotPoint, Lollipop.anchor, Lollipop.unitRadial,
    Lollipop.radius, point2, u1, u2, EuclideanSpace.norm_sq_eq]

/-- Exact pair `(1,3)` values. -/
theorem diagnostics_Q1_Q3 : diagnostics Q1 Q3 =
    { outerMargin := 9123/1450
      innerMargin := 309877/1450
      forwardDiscriminant := 207269701311/442050625
      forwardAnchorPower := 32792513/420500
      forwardVertexAhead := 983347/42050
      reverseDiscriminant := 317/42050
      reverseAnchorPower := 13/50
      reverseVertexAhead := 15/29
      determinant := 20447/21025
      leftParameterMargin := 247/29210
      rightParameterMargin := 1131/2921 } := by
  ext <;> norm_num [diagnostics, Q1, Q3, fromAnchor, fromCenter,
    circleOuterMargin, circleInnerMargin, centerDistanceSq, displacement,
    normSqPoint, projectedCenterParameter, lineDiscriminant, anchorPower,
    vertexAhead, directionDet, leftLineParameter, rightLineParameter,
    detPoint, dotPoint, Lollipop.anchor, Lollipop.unitRadial,
    Lollipop.radius, point2, u1, u3, EuclideanSpace.norm_sq_eq]

/-- Exact pair `(2,3)` values. -/
theorem diagnostics_Q2_Q3 : diagnostics Q2 Q3 =
    { outerMargin := 2689731/986
      innerMargin := 36750269/986
      forwardDiscriminant := 7002650391/972196
      forwardAnchorPower := 7957/58
      forwardVertexAhead := 84475/986
      reverseDiscriminant := 4378230968959/607622500
      reverseAnchorPower := 4617/34
      reverseVertexAhead := 2112047/24650
      determinant := -6493/12325
      leftParameterMargin := 4471/12986
      rightParameterMargin := 5075/12986 } := by
  ext <;> norm_num [diagnostics, Q2, Q3, fromAnchor, fromCenter,
    circleOuterMargin, circleInnerMargin, centerDistanceSq, displacement,
    normSqPoint, projectedCenterParameter, lineDiscriminant, anchorPower,
    vertexAhead, directionDet, leftLineParameter, rightLineParameter,
    detPoint, dotPoint, Lollipop.anchor, Lollipop.unitRadial,
    Lollipop.radius, point2, u2, u3, EuclideanSpace.norm_sq_eq]

/-- A positive diagnostics record realizes the seven chamber. -/
theorem realizes_seven_of_diagnostics_positive
    {L M : Lollipop} {D : Diagnostics}
    (hD : diagnostics L M = D)
    (hout : 0 < D.outerMargin) (hin : 0 < D.innerMargin)
    (hfdisc : 0 < D.forwardDiscriminant)
    (hfpower : 0 < D.forwardAnchorPower)
    (hfvertex : 0 < D.forwardVertexAhead)
    (hrdisc : 0 < D.reverseDiscriminant)
    (hrpower : 0 < D.reverseAnchorPower)
    (hrvertex : 0 < D.reverseVertexAhead)
    (hdet : D.determinant ≠ 0)
    (hl : 0 < D.leftParameterMargin)
    (hr : 0 < D.rightParameterMargin) :
    RealizesStrictPairCode StrictPairCode.seven L M := by
  have := congrArg Diagnostics.outerMargin hD
  have := congrArg Diagnostics.innerMargin hD
  have := congrArg Diagnostics.forwardDiscriminant hD
  have := congrArg Diagnostics.forwardAnchorPower hD
  have := congrArg Diagnostics.forwardVertexAhead hD
  have := congrArg Diagnostics.reverseDiscriminant hD
  have := congrArg Diagnostics.reverseAnchorPower hD
  have := congrArg Diagnostics.reverseVertexAhead hD
  have := congrArg Diagnostics.determinant hD
  have := congrArg Diagnostics.leftParameterMargin hD
  have := congrArg Diagnostics.rightParameterMargin hD
  simp only [diagnostics] at *
  refine ⟨by linarith, by linarith, ?_, ?_, ?_⟩
  · exact ⟨by linarith, by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith, by linarith⟩
  · simp [RayRayCodeRealized, StrictPairCode.seven]
    exact ⟨by simpa using hdet, by linarith, by linarith⟩

/-- Pair `(0,1)` realizes the exceptional five-crossing chamber. -/
theorem Q0_Q1_realizes_five :
    RealizesStrictPairCode StrictPairCode.five Q0 Q1 := by
  rw [show diagnostics Q0 Q1 = _ from diagnostics_Q0_Q1]
  norm_num [RealizesStrictPairCode, StrictPairCode.five,
    MixedCode.Realized, RayRayCodeRealized, diagnostics]

/-- Pair `(0,2)` realizes seven. -/
theorem Q0_Q2_realizes_seven :
    RealizesStrictPairCode StrictPairCode.seven Q0 Q2 := by
  rw [show diagnostics Q0 Q2 = _ from diagnostics_Q0_Q2]
  norm_num [RealizesStrictPairCode, StrictPairCode.seven,
    MixedCode.Realized, RayRayCodeRealized, diagnostics]

/-- Pair `(0,3)` realizes seven. -/
theorem Q0_Q3_realizes_seven :
    RealizesStrictPairCode StrictPairCode.seven Q0 Q3 := by
  rw [show diagnostics Q0 Q3 = _ from diagnostics_Q0_Q3]
  norm_num [RealizesStrictPairCode, StrictPairCode.seven,
    MixedCode.Realized, RayRayCodeRealized, diagnostics]

/-- Pair `(1,2)` realizes seven. -/
theorem Q1_Q2_realizes_seven :
    RealizesStrictPairCode StrictPairCode.seven Q1 Q2 := by
  rw [show diagnostics Q1 Q2 = _ from diagnostics_Q1_Q2]
  norm_num [RealizesStrictPairCode, StrictPairCode.seven,
    MixedCode.Realized, RayRayCodeRealized, diagnostics]

/-- Pair `(1,3)` realizes seven. -/
theorem Q1_Q3_realizes_seven :
    RealizesStrictPairCode StrictPairCode.seven Q1 Q3 := by
  rw [show diagnostics Q1 Q3 = _ from diagnostics_Q1_Q3]
  norm_num [RealizesStrictPairCode, StrictPairCode.seven,
    MixedCode.Realized, RayRayCodeRealized, diagnostics]

/-- Pair `(2,3)` realizes seven. -/
theorem Q2_Q3_realizes_seven :
    RealizesStrictPairCode StrictPairCode.seven Q2 Q3 := by
  rw [show diagnostics Q2 Q3 = _ from diagnostics_Q2_Q3]
  norm_num [RealizesStrictPairCode, StrictPairCode.seven,
    MixedCode.Realized, RayRayCodeRealized, diagnostics]

/-- Karlsson pair code on the four base clusters. -/
def baseCode (i j : Fin 4) : StrictPairCode :=
  if i = 0 ∧ j = 1 then StrictPairCode.five
  else if i = 1 ∧ j = 0 then StrictPairCode.five.swap
  else StrictPairCode.seven

@[simp] theorem baseCode_swap (i j : Fin 4) :
    baseCode j i = (baseCode i j).swap := by
  fin_cases i <;> fin_cases j <;>
    simp [baseCode, StrictPairCode.swap, StrictPairCode.seven,
      StrictPairCode.five]

/-- Exact six-pair base theorem. -/
theorem base_realizes_code
    {i j : Fin 4} (hij : i ≠ j) :
    RealizesStrictPairCode (baseCode i j) (base i) (base j) := by
  fin_cases i <;> fin_cases j <;>
    simp_all [base, baseCode, Q0_Q1_realizes_five,
      Q0_Q2_realizes_seven, Q0_Q3_realizes_seven,
      Q1_Q2_realizes_seven, Q1_Q3_realizes_seven,
      Q2_Q3_realizes_seven, realizes_swap_iff]

/-- Exact finite crossing numbers of all six base pairs. -/
theorem base_pairCrossingCount
    {i j : Fin 4} (hij : i ≠ j) :
    pairCrossingCount (base i) (base j) = (baseCode i j).crossings :=
  pairCrossingCount_eq_of_realizes (base_realizes_code hij)

/-- The exact minimum positive margin highlighted in the audit. -/
theorem smallest_displayed_margin_pos : (0 : ℝ) < 151 / 23400 := by
  norm_num

end RationalBase
end Lower
end EndToEnd
end Concrete
end Lollipop
