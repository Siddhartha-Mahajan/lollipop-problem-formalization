import Lollipop.Internal.Manuscript.PrimitiveGeometry.ComponentBounds
import Lollipop.Internal.Manuscript.PrimitiveGeometry.NormalizedBearing
import Lollipop.Internal.Manuscript.PrimitiveGeometry.OverlapSavings

/-!
Audit examples for the close-pair route boundary.

The close-pair route theorem cannot be discharged merely by proving that one
of the two mixed circle-ray components is always empty.  This file gives a
small exact radial, normalized-bearing, cyclic-close pair where both mixed
components are nonempty.  The example is not a counterexample to the
`<= 5` close-pair bound; it only rules out an overly strong intermediate
claim.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd

/-- Unit lollipop anchored at `(1,0)` and pointing right. -/
noncomputable def closeRouteAuditRight : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 1 0) 1 0 0
    (by norm_num) (by norm_num) (by norm_num)

/-- Unit lollipop with the same anchor and pointing down. -/
noncomputable def closeRouteAuditDown : EuclideanLollipop :=
  EuclideanLollipop.fromAnchor
    (point2 1 0) 1 (-(Real.pi / 2)) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num)

theorem closeRouteAuditRight_isRadialOutward :
    closeRouteAuditRight.IsRadialOutward := by
  simpa [closeRouteAuditRight] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 1 0) 1 0 0
      (by norm_num) (by norm_num) (by norm_num)

theorem closeRouteAuditDown_isRadialOutward :
    closeRouteAuditDown.IsRadialOutward := by
  simpa [closeRouteAuditDown] using
    EuclideanLollipop.fromAnchor_isRadialOutward
      (point2 1 0) 1 (-(Real.pi / 2)) (3 / 4)
      (by norm_num) (by norm_num) (by norm_num)

theorem closeRouteAuditRight_hasNormalizedBearing :
    closeRouteAuditRight.HasNormalizedBearing := by
  unfold closeRouteAuditRight
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing (by ring)

theorem closeRouteAuditDown_hasNormalizedBearing :
    closeRouteAuditDown.HasNormalizedBearing := by
  unfold closeRouteAuditDown
  exact EuclideanLollipop.fromAnchor_hasNormalizedBearing_of_eq_sub_two_pi
    (by ring)

theorem closeRouteAudit_cyclicClosePair :
    CloseDirection.cyclicClosePair
      closeRouteAuditRight.normalizedDirection
      closeRouteAuditDown.normalizedDirection := by
  unfold closeRouteAuditRight closeRouteAuditDown
  simp [EuclideanLollipop.fromAnchor, CloseDirection.cyclicClosePair]
  right
  norm_num

/-- The shared anchor belongs to both mixed components. -/
theorem closeRouteAudit_mixed_components_nonempty :
    ∃ p : EuclideanR2,
      p ∈ euclideanCircleRaySet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanRayCircleSet closeRouteAuditRight closeRouteAuditDown := by
  refine ⟨toEuclideanR2 (point2 1 0), ?_, ?_⟩
  · exact
      mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            closeRouteAuditRight.anchor_on_circle)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditDown.rayDirection)
  · exact
      mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditRight.rayDirection)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            closeRouteAuditDown.anchor_on_circle)

theorem closeRouteAudit_circleRay_not_empty :
    ¬ (∀ p : EuclideanR2,
      p ∉ euclideanCircleRaySet closeRouteAuditRight closeRouteAuditDown) := by
  intro hempty
  rcases closeRouteAudit_mixed_components_nonempty with ⟨p, hp, _⟩
  exact hempty p hp

theorem closeRouteAudit_rayCircle_not_empty :
    ¬ (∀ p : EuclideanR2,
      p ∉ euclideanRayCircleSet closeRouteAuditRight closeRouteAuditDown) := by
  intro hempty
  rcases closeRouteAudit_mixed_components_nonempty with ⟨p, _, hp⟩
  exact hempty p hp

theorem closeRouteAudit_spheres_distinct :
    euclideanSphere closeRouteAuditRight.center closeRouteAuditRight.radius ≠
      euclideanSphere closeRouteAuditDown.center closeRouteAuditDown.radius := by
  apply euclideanSphere_ne_of_center_ne
  intro hcenter
  have hx := congr_fun hcenter 0
  simp [closeRouteAuditRight, closeRouteAuditDown,
    EuclideanLollipop.fromAnchor, angleDirection, point2,
    Real.cos_neg, Real.cos_pi_div_two] at hx

theorem closeRouteAudit_rayLines_distinct :
    euclideanRayLine closeRouteAuditRight ≠
      euclideanRayLine closeRouteAuditDown := by
  apply euclideanRayLine_ne_of_det2_rayDirection_ne_zero
  have hdet :
      det2 closeRouteAuditRight.rayDirection
        closeRouteAuditDown.rayDirection = -1 := by
    simp [closeRouteAuditRight, closeRouteAuditDown,
      EuclideanLollipop.fromAnchor, angleDirection, det2, point2,
      Real.cos_neg, Real.sin_neg, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
  rw [hdet]
  norm_num

theorem closeRouteAudit_common_all_components :
    ∃ p : EuclideanR2,
      p ∈ euclideanCircleCircleSet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanCircleRaySet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanRayCircleSet closeRouteAuditRight closeRouteAuditDown ∧
      p ∈ euclideanRayRaySet closeRouteAuditRight closeRouteAuditDown := by
  refine ⟨toEuclideanR2 (point2 1 0), ?_, ?_, ?_, ?_⟩
  · exact
      mem_euclideanCircleCircleSet_of_mem_circleSets
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            closeRouteAuditRight.anchor_on_circle)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            closeRouteAuditDown.anchor_on_circle)
  · exact
      mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            closeRouteAuditRight.anchor_on_circle)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditDown.rayDirection)
  · exact
      mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditRight.rayDirection)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            closeRouteAuditDown.anchor_on_circle)
  · exact
      mem_euclideanRayRaySet_of_mem_raySets
        (L := closeRouteAuditRight) (M := closeRouteAuditDown)
        (p := point2 1 0)
        (by
          simpa [closeRouteAuditRight, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditRight.rayDirection)
        (by
          simpa [closeRouteAuditDown, EuclideanLollipop.fromAnchor] using
            anchor_mem_raySet (point2 1 0)
              closeRouteAuditDown.rayDirection)

theorem closeRouteAudit_direct_savings_four :
    PairCarrierSavings closeRouteAuditRight closeRouteAuditDown 4 := by
  rcases closeRouteAudit_common_all_components with
    ⟨p, hcc, hcr, hrc, hrr⟩
  exact
    pairCarrierSavingsFourOfCommonAllComponents
      closeRouteAudit_spheres_distinct
      closeRouteAudit_rayLines_distinct
      (q := p) hcc hcr hrc hrr

theorem closeRouteAudit_carrier_card_le_four
    (S : Finset EuclideanR2)
    (hS : ∀ p ∈ S,
      p ∈ euclideanPairIntersectionSet
        closeRouteAuditRight closeRouteAuditDown) :
    S.card ≤ 4 :=
  closeRouteAudit_direct_savings_four.carrier_card_le S hS

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop
