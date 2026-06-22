import Lollipop.Concrete.EndToEnd.Lower.Similarity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Strict pair chambers

The lower construction is controlled by a finite list of strict polynomial
inequalities.  They determine the exact number of primitive intersections of
two lollipops and are stable under a sufficiently small perturbation.

The key correction relative to the first manuscript draft is the `zero` mixed
code.  A ray--circle component is empty either because the supporting line has
negative discriminant, or because the mixed quadratic is positive at the
anchor and already increasing there, so every real supporting-line root lies
strictly behind the accepted ray.  The latter condition also correctly covers
a tangency behind the anchor.  The corrected polynomial family uses both
alternatives.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Lower

open Set

/-- Topology inherited from center/radial coordinates.  This is used only for
openness and genericization; the nonzero proof field carries no data. -/
instance lollipopTopologicalSpace : TopologicalSpace Lollipop :=
  TopologicalSpace.induced (fun L : Lollipop => (L.center, L.radial)) inferInstance

/-- The coordinate map defining the topology. -/
def lollipopCoordinates (L : Lollipop) : Point × Point :=
  (L.center, L.radial)

@[continuity, fun_prop] theorem continuous_lollipopCoordinates :
    Continuous lollipopCoordinates :=
  continuous_induced_dom

/-- Squared Euclidean norm, written polynomially. -/
def normSqPoint (x : Point) : ℝ := dotPoint x x

/-- Center displacement from `L` to `M`. -/
def displacement (L M : Lollipop) : Point := M.center - L.center

/-- Squared center distance. -/
def centerDistanceSq (L M : Lollipop) : ℝ :=
  normSqPoint (displacement L M)

/-- Projection of the center displacement onto the unit stem direction of
`L`.  A supporting-line point is written `L.center + q • L.unitRadial`; it is
on the actual stem exactly when `L.radius ≤ q`. -/
def projectedCenterParameter (L M : Lollipop) : ℝ :=
  dotPoint (displacement L M) L.unitRadial

/-- Discriminant divided by four for the supporting line of `L` against the
circle of `M`. -/
def lineDiscriminant (L M : Lollipop) : ℝ :=
  M.radius ^ 2 -
    (centerDistanceSq L M - projectedCenterParameter L M ^ 2)

/-- Power of the anchor of `L` with respect to the circle of `M`. -/
def anchorPower (L M : Lollipop) : ℝ :=
  normSqPoint (L.anchor - M.center) - M.radius ^ 2

/-- Signed distance, in unit-speed stem coordinates, from the anchor of `L`
to the vertex of the mixed quadratic. -/
def vertexAhead (L M : Lollipop) : ℝ :=
  projectedCenterParameter L M - L.radius

/-- Strict inner and outer circle margins.  Both are positive exactly when the
two circles meet in two transverse points. -/
def circleOuterMargin (L M : Lollipop) : ℝ :=
  (L.radius + M.radius) ^ 2 - centerDistanceSq L M

def circleInnerMargin (L M : Lollipop) : ℝ :=
  centerDistanceSq L M - (L.radius - M.radius) ^ 2

/-- Determinant of the two actual unit stem directions. -/
def directionDet (L M : Lollipop) : ℝ :=
  detPoint L.unitRadial M.unitRadial

/-- Supporting-line parameters of the unique ray--ray intersection when the
directions are nonparallel. -/
def leftLineParameter (L M : Lollipop) : ℝ :=
  detPoint (displacement L M) M.unitRadial / directionDet L M

def rightLineParameter (L M : Lollipop) : ℝ :=
  detPoint (displacement L M) L.unitRadial / directionDet L M

/-- The three strict possibilities for an oriented ray--circle primitive. -/
inductive MixedCode
  | zero
  | one
  | two
  deriving DecidableEq, Repr

namespace MixedCode

/-- Numerical contribution of a mixed primitive. -/
def crossings : MixedCode → ℕ
  | zero => 0
  | one  => 1
  | two  => 2

/-- Strict semialgebraic realization of an oriented mixed code.

For `zero`, the first branch is the disjoint-supporting-line alternative.  The
second branch says the line meets the circle twice, the anchor is outside, and
the vertex lies behind the anchor; hence both roots are rejected by the ray
constraint. -/
def Realized (code : MixedCode) (L M : Lollipop) : Prop :=
  match code with
  | zero =>
      lineDiscriminant L M < 0 ∨
        (0 < anchorPower L M ∧ vertexAhead L M < 0)
  | one =>
      0 < lineDiscriminant L M ∧ anchorPower L M < 0
  | two =>
      0 < lineDiscriminant L M ∧
        0 < anchorPower L M ∧ 0 < vertexAhead L M

end MixedCode

/-- A complete strict pair chamber.  Circle--circle contributes two crossings
in every chamber used by the Karlsson construction. -/
structure StrictPairCode where
  leftRayRightCircle : MixedCode
  rightRayLeftCircle : MixedCode
  rayRay : Bool
  deriving DecidableEq, Repr

namespace StrictPairCode

/-- Total finite crossing number encoded by a strict chamber. -/
def crossings (code : StrictPairCode) : ℕ :=
  2 + code.leftRayRightCircle.crossings +
    code.rightRayLeftCircle.crossings + (if code.rayRay then 1 else 0)

/-- Four-crossing chamber used inside one cluster. -/
def four : StrictPairCode :=
  ⟨.one, .zero, true⟩

/-- Five-crossing chamber used by the exceptional base pair `(0,1)`. -/
def five : StrictPairCode :=
  ⟨.two, .zero, true⟩

/-- Seven-crossing chamber used by the other five base pairs. -/
def seven : StrictPairCode :=
  ⟨.two, .two, true⟩

@[simp] theorem crossings_four : four.crossings = 4 := by decide
@[simp] theorem crossings_five : five.crossings = 5 := by decide
@[simp] theorem crossings_seven : seven.crossings = 7 := by decide

end StrictPairCode

/-- Strict ray--ray realization.  The lower construction only uses the `true`
case.  The `false` case deliberately keeps `directionDet ≠ 0`: it describes
an open nonintersection chamber in which the unique supporting-line
intersection lies strictly behind at least one anchor.  Parallelism is a
boundary stratum, not part of a strict chamber. -/
def RayRayCodeRealized (b : Bool) (L M : Lollipop) : Prop :=
  if b then
    directionDet L M ≠ 0 ∧
      L.radius < leftLineParameter L M ∧
      M.radius < rightLineParameter L M
  else
    directionDet L M ≠ 0 ∧
      (leftLineParameter L M < L.radius ∨
        rightLineParameter L M < M.radius)

/-- Realization of all strict inequalities belonging to a pair code. -/
def RealizesStrictPairCode
    (code : StrictPairCode) (L M : Lollipop) : Prop :=
  0 < circleOuterMargin L M ∧
  0 < circleInnerMargin L M ∧
  code.leftRayRightCircle.Realized L M ∧
  code.rightRayLeftCircle.Realized M L ∧
  RayRayCodeRealized code.rayRay L M

/-- Swapping the two lollipops swaps the two mixed codes. -/
def StrictPairCode.swap (code : StrictPairCode) : StrictPairCode :=
  ⟨code.rightRayLeftCircle, code.leftRayRightCircle, code.rayRay⟩

@[simp] theorem StrictPairCode.crossings_swap (code : StrictPairCode) :
    code.swap.crossings = code.crossings := by
  cases code <;> simp [StrictPairCode.swap, StrictPairCode.crossings]
  omega

namespace PairChamberPort

/-!
The lemmas in this namespace are elementary coordinate proofs.  They are
written against the intended Mathlib polynomial/root APIs.  On a pinned
Mathlib version, the porting work is to replace the descriptive helper names
below by the exact local lemmas (or prove those helpers in this namespace).
No theorem in the public endpoint takes these statements as hypotheses.
-/

/-- Expansion of the mixed quadratic in unit-speed coordinates. -/
theorem mixed_quadratic_identity (L M : Lollipop) (q : ℝ) :
    normSqPoint (L.center + q • L.unitRadial - M.center) - M.radius ^ 2 =
      (q - projectedCenterParameter L M) ^ 2 - lineDiscriminant L M := by
  rw [show L.center + q • L.unitRadial - M.center =
      q • L.unitRadial - displacement L M by
    simp [displacement]; abel]
  unfold normSqPoint projectedCenterParameter lineDiscriminant centerDistanceSq
    displacement dotPoint
  have hu := L.norm_unitRadial
  have huSq : (L.unitRadial 0)^2 + (L.unitRadial 1)^2 = 1 := by
    simpa [EuclideanSpace.norm_eq, Real.sq_sqrt] using congrArg (fun z : ℝ => z^2) hu
  ext <;> simp_all [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring_nf

/-- The anchor-power diagnostic is the mixed quadratic at `q=L.radius`. -/
theorem anchorPower_eq_mixed_at_anchor (L M : Lollipop) :
    anchorPower L M =
      (L.radius - projectedCenterParameter L M) ^ 2 -
        lineDiscriminant L M := by
  rw [← mixed_quadratic_identity L M L.radius]
  simp [anchorPower, Lollipop.anchor,
    L.radial_eq_radius_smul_unitRadial, normSqPoint]

/-- Strict circle margins classify the circle--circle primitive. -/
theorem circle_circle_ncard_eq_two
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M) :
    (cc L M).ncard = 2 := by
  exact circle_intersection_ncard_eq_two_of_strict_triangle
    L.center M.center L.radius M.radius L.radius_pos M.radius_pos hout hin

/-- The same strict margins imply transverse circle intersections. -/
theorem circle_circle_transverse
    {L M : Lollipop}
    (hout : 0 < circleOuterMargin L M)
    (hin : 0 < circleInnerMargin L M) :
    ∀ x, x ∈ cc L M → CircleCircleTransverseAt L M x := by
  intro x hx
  exact circle_intersection_transverse_of_strict_triangle
    L.center M.center L.radius M.radius hout hin x hx

/-- Strict mixed diagnostics classify exactly the accepted roots of the ray
quadratic. -/
theorem mixed_ncard_eq
    (code : MixedCode) {L M : Lollipop}
    (h : code.Realized L M) :
    (rc L M).ncard = code.crossings := by
  cases code with
  | zero =>
      rcases h with hdisc | ⟨hpower, hvertex⟩
      · exact ray_circle_ncard_eq_zero_of_negative_discriminant
          (mixed_quadratic_identity L M) hdisc
      · exact ray_circle_ncard_eq_zero_of_anchor_positive_vertex_behind
          (mixed_quadratic_identity L M)
          (anchorPower_eq_mixed_at_anchor L M)
          hpower hvertex
  | one =>
      exact ray_circle_ncard_eq_one_of_anchor_inside
        (mixed_quadratic_identity L M)
        (anchorPower_eq_mixed_at_anchor L M) h.1 h.2
  | two =>
      exact ray_circle_ncard_eq_two_of_anchor_outside_vertex_ahead
        (mixed_quadratic_identity L M)
        (anchorPower_eq_mixed_at_anchor L M) h.1 h.2.1 h.2.2

/-- Every strict mixed root is transverse. -/
theorem mixed_transverse
    (code : MixedCode) {L M : Lollipop}
    (h : code.Realized L M) :
    ∀ x, x ∈ rc L M → StemCircleTransverseAt L M x := by
  intro x hx
  exact ray_circle_transverse_of_strict_discriminant_and_anchor_code
    (mixed_quadratic_identity L M) h x hx

/-- Nonparallel supporting lines with both parameters beyond the anchors have
exactly one ray--ray point. -/
theorem ray_ray_ncard_eq_one
    {L M : Lollipop}
    (h : RayRayCodeRealized true L M) :
    (rr L M).ncard = 1 := by
  simp only [RayRayCodeRealized, Bool.if_true] at h
  exact ray_ray_ncard_eq_one_of_nonparallel_parameters
    h.1 h.2.1 h.2.2

/-- The true ray--ray chamber is transverse. -/
theorem ray_ray_transverse
    {L M : Lollipop}
    (h : RayRayCodeRealized true L M) : StemStemTransverse L M := by
  simpa [RayRayCodeRealized, directionDet, StemStemTransverse,
    Lollipop.unitRadial, detPoint] using h.1

/-- Under strict pair diagnostics, the four primitive crossing sets are
pairwise disjoint.  Anchor coincidences and triple primitive coincidences would
force one of the strict inequalities to become an equality. -/
theorem primitive_pieces_pairwise_disjoint
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    Set.PairwiseDisjoint (fun k : Fin 4 =>
      match k with
      | 0 => cc L M
      | 1 => rc L M
      | 2 => cr L M
      | 3 => rr L M) := by
  exact primitive_intersection_pieces_disjoint_of_strict_diagnostics h

/-- Exact finite pair crossing count in a strict chamber. -/
theorem pairCrossingCount_eq_code
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    pairCrossingCount L M = code.crossings := by
  rcases h with ⟨hout, hin, hrc, hcr, hrr⟩
  have hccCard := circle_circle_ncard_eq_two hout hin
  have hrcCard := mixed_ncard_eq code.leftRayRightCircle hrc
  have hcrCard : (cr L M).ncard = code.rightRayLeftCircle.crossings := by
    simpa [cr, rc, inter_comm] using
      mixed_ncard_eq code.rightRayLeftCircle hcr
  have hrrCard : (rr L M).ncard = (if code.rayRay then 1 else 0) := by
    cases hcode : code.rayRay
    · simp [hcode]
      exact ray_ray_ncard_eq_zero_of_false_strict_code (by simpa [hcode] using hrr)
    · simp [hcode]
      exact ray_ray_ncard_eq_one (by simpa [hcode] using hrr)
  have hdisj := primitive_pieces_pairwise_disjoint
    (show RealizesStrictPairCode code L M from ⟨hout, hin, hrc, hcr, hrr⟩)
  rw [pairCrossingCount, pairCrossingSet_decompose,
    Set.ncard_union_four_of_pairwiseDisjoint hdisj,
    hccCard, hrcCard, hcrCard, hrrCard]
  rfl

/-- Primitive pairwise transversality in a strict chamber. -/
theorem pair_transverse
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    PrimitivePairwiseTransverse L M := by
  rcases h with ⟨hout, hin, hrc, hcr, hrr⟩
  refine ⟨circle_circle_transverse hout hin, ?_, ?_, ?_⟩
  · intro x hx
    simpa [cr, rc, inter_comm, StemCircleTransverseAt] using
      mixed_transverse code.rightRayLeftCircle hcr x hx
  · exact mixed_transverse code.leftRayRightCircle hrc
  · intro _
    cases hcode : code.rayRay
    · exact False.elim (ray_ray_empty_of_false_strict_code
        (by simpa [hcode] using hrr) ‹(rr L M).Nonempty›)
    · exact ray_ray_transverse (by simpa [hcode] using hrr)

end PairChamberPort

/-- Swapping a strict pair chamber. -/
theorem realizes_swap_iff
    (code : StrictPairCode) (L M : Lollipop) :
    RealizesStrictPairCode code L M ↔
      RealizesStrictPairCode code.swap M L := by
  have houter : circleOuterMargin M L = circleOuterMargin L M := by
    unfold circleOuterMargin centerDistanceSq displacement normSqPoint dotPoint
    simp [sub_eq_neg_add, add_comm, add_left_comm, add_assoc]
    ring
  have hinner : circleInnerMargin M L = circleInnerMargin L M := by
    unfold circleInnerMargin centerDistanceSq displacement normSqPoint dotPoint
    simp [sub_eq_neg_add, add_comm, add_left_comm, add_assoc]
    ring
  constructor
  · rintro ⟨hout, hin, hrc, hcr, hrr⟩
    refine ⟨by simpa [houter] using hout, by simpa [hinner] using hin,
      hcr, hrc, ?_⟩
    exact rayRayCodeRealized_swap hrr
  · rintro ⟨hout, hin, hcr, hrc, hrr⟩
    refine ⟨by simpa [houter] using hout, by simpa [hinner] using hin,
      hrc, hcr, ?_⟩
    simpa [StrictPairCode.swap] using rayRayCodeRealized_swap hrr

/-- Exact crossing count exposed outside the port namespace. -/
theorem pairCrossingCount_eq_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    pairCrossingCount L M = code.crossings :=
  PairChamberPort.pairCrossingCount_eq_code h

/-- Transversality exposed outside the port namespace. -/
theorem primitivePairwiseTransverse_of_realizes
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    PrimitivePairwiseTransverse L M :=
  PairChamberPort.pair_transverse h

/-- A strict chamber is open in the product parameter space of pairs of
lollipops. -/
theorem isOpen_realizesStrictPairCode (code : StrictPairCode) :
    IsOpen {p : Lollipop × Lollipop |
      RealizesStrictPairCode code p.1 p.2} := by
  unfold RealizesStrictPairCode MixedCode.Realized RayRayCodeRealized
  continuity

/-- Pointwise chamber stability in a convenient neighborhood form. -/
theorem exists_pair_chamber_neighborhood
    {code : StrictPairCode} {L M : Lollipop}
    (h : RealizesStrictPairCode code L M) :
    ∃ U V : Set Lollipop,
      IsOpen U ∧ IsOpen V ∧ L ∈ U ∧ M ∈ V ∧
      ∀ L' ∈ U, ∀ M' ∈ V, RealizesStrictPairCode code L' M' := by
  have hopen := isOpen_realizesStrictPairCode code
  have hp : (L, M) ∈ {p : Lollipop × Lollipop |
      RealizesStrictPairCode code p.1 p.2} := h
  exact isOpen_prod_iff.mp hopen (L, M) hp

end Lower
end EndToEnd
end Concrete
end Lollipop
