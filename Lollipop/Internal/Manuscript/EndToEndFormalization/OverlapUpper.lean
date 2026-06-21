import Lollipop.Internal.Manuscript.CompleteFormalization.AutomaticUpper
import Lollipop.Internal.Manuscript.PrimitiveGeometry.OverlapSavings

/-!
Automatic upper certificates from concrete component-overlap witnesses.

The direct-savings upper endpoint asks for `PairCarrierSavings` inputs.  This
module records a more geometric sufficient boundary: the construction may
instead supply the overlap witnesses already proved in
`PrimitiveGeometry.OverlapSavings`, and Lean converts them into direct
whole-carrier savings certificates.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace EndToEndFormalization
namespace OverlapUpper

open PrimitiveGeometry

universe u

noncomputable section

/-! ## Orientation helpers for lifted component overlap witnesses -/

/-- Lifted circle-circle component membership is symmetric in the two
lollipops. -/
theorem mem_euclideanCircleCircleSet_swap
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanCircleCircleSet L M) :
    p ∈ euclideanCircleCircleSet M L := by
  rcases hp with ⟨hpL, hpM⟩
  exact ⟨hpM, hpL⟩

/-- A lifted ray-circle membership becomes circle-ray membership after
swapping the two lollipops. -/
theorem mem_euclideanCircleRaySet_swap_of_mem_rayCircle
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayCircleSet L M) :
    p ∈ euclideanCircleRaySet M L := by
  rcases hp with ⟨hpL, hpM⟩
  exact ⟨hpM, hpL⟩

/-- A lifted circle-ray membership becomes ray-circle membership after
swapping the two lollipops. -/
theorem mem_euclideanRayCircleSet_swap_of_mem_circleRay
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanCircleRaySet L M) :
    p ∈ euclideanRayCircleSet M L := by
  rcases hp with ⟨hpL, hpM⟩
  exact ⟨hpM, hpL⟩

/-- Lifted ray-ray component membership is symmetric in the two lollipops. -/
theorem mem_euclideanRayRaySet_swap
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ euclideanRayRaySet M L := by
  rcases hp with ⟨hpL, hpM⟩
  exact ⟨hpM, hpL⟩

/-- Lifted triple-overlap witnesses are symmetric in the two lollipops. -/
def pairComponentTripleOverlap_symm
    {L M : EuclideanLollipop} {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q) :
    PairComponentTripleOverlap M L q := by
  cases H with
  | withoutCircleCircle hqcr hqrc hqrr =>
      exact
        PairComponentTripleOverlap.withoutCircleCircle
          (mem_euclideanCircleRaySet_swap_of_mem_rayCircle hqrc)
          (mem_euclideanRayCircleSet_swap_of_mem_circleRay hqcr)
          (mem_euclideanRayRaySet_swap hqrr)
  | withoutCircleRay hqcc hqrc hqrr =>
      exact
        PairComponentTripleOverlap.withoutRayCircle
          (mem_euclideanCircleCircleSet_swap hqcc)
          (mem_euclideanCircleRaySet_swap_of_mem_rayCircle hqrc)
          (mem_euclideanRayRaySet_swap hqrr)
  | withoutRayCircle hqcc hqcr hqrr =>
      exact
        PairComponentTripleOverlap.withoutCircleRay
          (mem_euclideanCircleCircleSet_swap hqcc)
          (mem_euclideanRayCircleSet_swap_of_mem_circleRay hqcr)
          (mem_euclideanRayRaySet_swap hqrr)
  | withoutRayRay hqcc hqcr hqrc =>
      exact
        PairComponentTripleOverlap.withoutRayRay
          (mem_euclideanCircleCircleSet_swap hqcc)
          (mem_euclideanCircleRaySet_swap_of_mem_rayCircle hqrc)
          (mem_euclideanRayCircleSet_swap_of_mem_circleRay hqcr)

/-- Lifted two-double-overlap witnesses are symmetric in the two lollipops. -/
def pairComponentTwoDoubleOverlap_symm
    {L M : EuclideanLollipop} {q r : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q r) :
    PairComponentTwoDoubleOverlap M L q r := by
  cases H with
  | circleCircle_circleRay__rayCircle_rayRay hqcc hqcr hrrc hrrr =>
      exact
        PairComponentTwoDoubleOverlap.circleCircle_rayCircle__circleRay_rayRay
          (mem_euclideanCircleCircleSet_swap hqcc)
          (mem_euclideanRayCircleSet_swap_of_mem_circleRay hqcr)
          (mem_euclideanCircleRaySet_swap_of_mem_rayCircle hrrc)
          (mem_euclideanRayRaySet_swap hrrr)
  | circleCircle_rayCircle__circleRay_rayRay hqcc hqrc hrcr hrrr =>
      exact
        PairComponentTwoDoubleOverlap.circleCircle_circleRay__rayCircle_rayRay
          (mem_euclideanCircleCircleSet_swap hqcc)
          (mem_euclideanCircleRaySet_swap_of_mem_rayCircle hqrc)
          (mem_euclideanRayCircleSet_swap_of_mem_circleRay hrcr)
          (mem_euclideanRayRaySet_swap hrrr)
  | circleCircle_rayRay__circleRay_rayCircle hqcc hqrr hrcr hrrc =>
      exact
        PairComponentTwoDoubleOverlap.circleCircle_rayRay__circleRay_rayCircle
          (mem_euclideanCircleCircleSet_swap hqcc)
          (mem_euclideanRayRaySet_swap hqrr)
          (mem_euclideanCircleRaySet_swap_of_mem_rayCircle hrrc)
          (mem_euclideanRayCircleSet_swap_of_mem_circleRay hrcr)

/-- A concrete overlap witness sufficient for direct `<= 5` whole-carrier
savings: either one point lies in any three carrier components, or two
witnesses together improve all four component estimates. -/
inductive PairComponentFiveOverlap
    (L M : EuclideanLollipop) : Type where
  | triple {q : EuclideanR2}
      (H : PairComponentTripleOverlap L M q)
  | twoDouble {q r : EuclideanR2}
      (H : PairComponentTwoDoubleOverlap L M q r)

namespace PairComponentFiveOverlap

/-- Lifted five-overlap witnesses are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop}
    (H : PairComponentFiveOverlap L M) :
    PairComponentFiveOverlap M L := by
  cases H with
  | triple H =>
      exact PairComponentFiveOverlap.triple (pairComponentTripleOverlap_symm H)
  | twoDouble H =>
      exact PairComponentFiveOverlap.twoDouble
        (pairComponentTwoDoubleOverlap_symm H)

/-- Canonicalize lifted five-overlap data supplied in either lollipop order. -/
def ofEither
    {L M : EuclideanLollipop}
    (H :
      PairComponentFiveOverlap L M ⊕
        PairComponentFiveOverlap M L) :
    PairComponentFiveOverlap L M := by
  cases H with
  | inl H => exact H
  | inr H => exact H.symm

/-- A five-overlap witness gives direct whole-carrier `<= 5` savings. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop}
    (H : PairComponentFiveOverlap L M)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 := by
  cases H with
  | triple H =>
      exact pairCarrierSavingsFiveOfTripleComponentOverlap hLM hline H
  | twoDouble H =>
      exact pairCarrierSavingsFiveOfTwoDoubleComponentOverlap hLM hline H

end PairComponentFiveOverlap

/-- A triple-overlap witness is stronger than the advertised `<= 5` route:
because the circle/ray components are product components, any one point in
three of them lies in all four and gives direct whole-carrier `<= 4` savings. -/
def pairCarrierSavingsFourOfTripleOverlap
    {L M : EuclideanLollipop}
    {q : EuclideanR2}
    (H : PairComponentTripleOverlap L M q)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  PrimitiveGeometry.pairCarrierSavingsFourOfTripleComponentOverlap
    hLM hline H

/-- If the two witnesses in a two-double-overlap certificate are the same
point, the certificate gives direct whole-carrier `<= 4` savings. -/
def pairCarrierSavingsFourOfTwoDoubleOverlapSamePoint
    {L M : EuclideanLollipop}
    {q : EuclideanR2}
    (H : PairComponentTwoDoubleOverlap L M q q)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  PrimitiveGeometry.pairCarrierSavingsFourOfTwoDoubleComponentOverlapSamePoint
    hLM hline H

/-- A concrete overlap witness sufficient for direct `<= 4` whole-carrier
savings: one point lies in all four carrier components. -/
structure PairComponentAllFourOverlap
    (L M : EuclideanLollipop) : Type where
  point : EuclideanR2
  circleCircle : point ∈ euclideanCircleCircleSet L M
  circleRay : point ∈ euclideanCircleRaySet L M
  rayCircle : point ∈ euclideanRayCircleSet L M
  rayRay : point ∈ euclideanRayRaySet L M

namespace PairComponentAllFourOverlap

/-- Lifted all-four-overlap witnesses are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop}
    (H : PairComponentAllFourOverlap L M) :
    PairComponentAllFourOverlap M L where
  point := H.point
  circleCircle := mem_euclideanCircleCircleSet_swap H.circleCircle
  circleRay := mem_euclideanCircleRaySet_swap_of_mem_rayCircle H.rayCircle
  rayCircle := mem_euclideanRayCircleSet_swap_of_mem_circleRay H.circleRay
  rayRay := mem_euclideanRayRaySet_swap H.rayRay

/-- Canonicalize lifted all-four-overlap data supplied in either lollipop
order. -/
def ofEither
    {L M : EuclideanLollipop}
    (H :
      PairComponentAllFourOverlap L M ⊕
        PairComponentAllFourOverlap M L) :
    PairComponentAllFourOverlap L M := by
  cases H with
  | inl H => exact H
  | inr H => exact H.symm

/-- A primitive coordinate point lying on both circles and both rays gives the
all-four lifted component-overlap witness. -/
def of_primitive_point
    {L M : EuclideanLollipop} {p : R2}
    (hLcircle : p ∈ circleSet L.center L.radius)
    (hMcircle : p ∈ circleSet M.center M.radius)
    (hLray : p ∈ raySet L.anchor L.rayDirection)
    (hMray : p ∈ raySet M.anchor M.rayDirection) :
    PairComponentAllFourOverlap L M where
  point := toEuclideanR2 p
  circleCircle :=
    mem_euclideanCircleCircleSet_of_mem_circleSets
      (L := L) (M := M) (p := p) hLcircle hMcircle
  circleRay :=
    mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
      (L := L) (M := M) (p := p) hLcircle hMray
  rayCircle :=
    mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
      (L := L) (M := M) (p := p) hLray hMcircle
  rayRay :=
    mem_euclideanRayRaySet_of_mem_raySets
      (L := L) (M := M) (p := p) hLray hMray

/-- If two primitive lollipops share their anchor, that common anchor lies in
all four lifted circle/ray components. -/
def of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    PairComponentAllFourOverlap L M where
  point := toEuclideanR2 L.anchor
  circleCircle := by
    have hM : L.anchor ∈ circleSet M.center M.radius := by
      simpa [hanchor] using M.anchor_on_circle
    exact
      mem_euclideanCircleCircleSet_of_mem_circleSets
        (L := L) (M := M) (p := L.anchor)
        L.anchor_on_circle hM
  circleRay := by
    have hM : L.anchor ∈ raySet M.anchor M.rayDirection := by
      simpa [hanchor] using anchor_mem_raySet M.anchor M.rayDirection
    exact
      mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
        (L := L) (M := M) (p := L.anchor)
        L.anchor_on_circle hM
  rayCircle := by
    have hM : L.anchor ∈ circleSet M.center M.radius := by
      simpa [hanchor] using M.anchor_on_circle
    exact
      mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
        (L := L) (M := M) (p := L.anchor)
        (anchor_mem_raySet L.anchor L.rayDirection) hM
  rayRay := by
    have hM : L.anchor ∈ raySet M.anchor M.rayDirection := by
      simpa [hanchor] using anchor_mem_raySet M.anchor M.rayDirection
    exact
      mem_euclideanRayRaySet_of_mem_raySets
        (L := L) (M := M) (p := L.anchor)
        (anchor_mem_raySet L.anchor L.rayDirection) hM

/-- An all-four-overlap witness gives direct whole-carrier `<= 4` savings. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop}
    (H : PairComponentAllFourOverlap L M)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  pairCarrierSavingsFourOfCommonAllComponents hLM hline
    H.circleCircle H.circleRay H.rayCircle H.rayRay

end PairComponentAllFourOverlap

namespace PairComponentFiveOverlap

/-- An all-four-overlap witness is stronger than the five-overlap witness
needed for the close-only and intriguing-only upper branches. -/
def of_all_four
    {L M : EuclideanLollipop}
    (H : PairComponentAllFourOverlap L M) :
    PairComponentFiveOverlap L M :=
  PairComponentFiveOverlap.triple
    (PairComponentTripleOverlap.withoutCircleCircle
      H.circleRay H.rayCircle H.rayRay)

/-- A shared anchor gives the five-overlap witness needed for the close-only
and intriguing-only upper branches. -/
def of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    PairComponentFiveOverlap L M :=
  of_all_four (PairComponentAllFourOverlap.of_common_anchor hanchor)

/-- A primitive coordinate point lying on both circles and both rays gives
the five-overlap witness needed for the close-only and intriguing-only upper
branches. -/
def of_primitive_point
    {L M : EuclideanLollipop} {p : R2}
    (hLcircle : p ∈ circleSet L.center L.radius)
    (hMcircle : p ∈ circleSet M.center M.radius)
    (hLray : p ∈ raySet L.anchor L.rayDirection)
    (hMray : p ∈ raySet M.anchor M.rayDirection) :
    PairComponentFiveOverlap L M :=
  of_all_four
    (PairComponentAllFourOverlap.of_primitive_point
      hLcircle hMcircle hLray hMray)

end PairComponentFiveOverlap

/-! ## Primitive coordinate constructors for two-double overlap witnesses -/

/-- Primitive coordinate constructor for the two-double pattern
`circle-circle/circle-ray` at `q` and `ray-circle/ray-ray` at `r`. -/
def pairComponentTwoDoubleOverlapOfPrimitiveCcCrRcRr
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqMray : q ∈ raySet M.anchor M.rayDirection)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMcircle : r ∈ circleSet M.center M.radius)
    (hrMray : r ∈ raySet M.anchor M.rayDirection) :
    PairComponentTwoDoubleOverlap L M (toEuclideanR2 q) (toEuclideanR2 r) :=
  PairComponentTwoDoubleOverlap.circleCircle_circleRay__rayCircle_rayRay
    (mem_euclideanCircleCircleSet_of_mem_circleSets
      (L := L) (M := M) (p := q) hqLcircle hqMcircle)
    (mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
      (L := L) (M := M) (p := q) hqLcircle hqMray)
    (mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
      (L := L) (M := M) (p := r) hrLray hrMcircle)
    (mem_euclideanRayRaySet_of_mem_raySets
      (L := L) (M := M) (p := r) hrLray hrMray)

/-- Primitive coordinate constructor for the two-double pattern
`circle-circle/ray-circle` at `q` and `circle-ray/ray-ray` at `r`. -/
def pairComponentTwoDoubleOverlapOfPrimitiveCcRcCrRr
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqLray : q ∈ raySet L.anchor L.rayDirection)
    (hrLcircle : r ∈ circleSet L.center L.radius)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMray : r ∈ raySet M.anchor M.rayDirection) :
    PairComponentTwoDoubleOverlap L M (toEuclideanR2 q) (toEuclideanR2 r) :=
  PairComponentTwoDoubleOverlap.circleCircle_rayCircle__circleRay_rayRay
    (mem_euclideanCircleCircleSet_of_mem_circleSets
      (L := L) (M := M) (p := q) hqLcircle hqMcircle)
    (mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
      (L := L) (M := M) (p := q) hqLray hqMcircle)
    (mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
      (L := L) (M := M) (p := r) hrLcircle hrMray)
    (mem_euclideanRayRaySet_of_mem_raySets
      (L := L) (M := M) (p := r) hrLray hrMray)

/-- Primitive coordinate constructor for the two-double pattern
`circle-circle/ray-ray` at `q` and `circle-ray/ray-circle` at `r`. -/
def pairComponentTwoDoubleOverlapOfPrimitiveCcRrCrRc
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqLray : q ∈ raySet L.anchor L.rayDirection)
    (hqMray : q ∈ raySet M.anchor M.rayDirection)
    (hrLcircle : r ∈ circleSet L.center L.radius)
    (hrMcircle : r ∈ circleSet M.center M.radius)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMray : r ∈ raySet M.anchor M.rayDirection) :
    PairComponentTwoDoubleOverlap L M (toEuclideanR2 q) (toEuclideanR2 r) :=
  PairComponentTwoDoubleOverlap.circleCircle_rayRay__circleRay_rayCircle
    (mem_euclideanCircleCircleSet_of_mem_circleSets
      (L := L) (M := M) (p := q) hqLcircle hqMcircle)
    (mem_euclideanRayRaySet_of_mem_raySets
      (L := L) (M := M) (p := q) hqLray hqMray)
    (mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
      (L := L) (M := M) (p := r) hrLcircle hrMray)
    (mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
      (L := L) (M := M) (p := r) hrLray hrMcircle)

namespace PairComponentFiveOverlap

/-- Primitive coordinate data for the `cc/cr` and `rc/rr` two-double pattern
give a five-overlap witness. -/
def of_primitive_two_double_cc_cr_and_rc_rr
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqMray : q ∈ raySet M.anchor M.rayDirection)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMcircle : r ∈ circleSet M.center M.radius)
    (hrMray : r ∈ raySet M.anchor M.rayDirection) :
    PairComponentFiveOverlap L M :=
  PairComponentFiveOverlap.twoDouble
    (pairComponentTwoDoubleOverlapOfPrimitiveCcCrRcRr
      hqLcircle hqMcircle hqMray hrLray hrMcircle hrMray)

/-- Primitive coordinate data for the `cc/rc` and `cr/rr` two-double pattern
give a five-overlap witness. -/
def of_primitive_two_double_cc_rc_and_cr_rr
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqLray : q ∈ raySet L.anchor L.rayDirection)
    (hrLcircle : r ∈ circleSet L.center L.radius)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMray : r ∈ raySet M.anchor M.rayDirection) :
    PairComponentFiveOverlap L M :=
  PairComponentFiveOverlap.twoDouble
    (pairComponentTwoDoubleOverlapOfPrimitiveCcRcCrRr
      hqLcircle hqMcircle hqLray hrLcircle hrLray hrMray)

/-- Primitive coordinate data for the `cc/rr` and `cr/rc` two-double pattern
give a five-overlap witness. -/
def of_primitive_two_double_cc_rr_and_cr_rc
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqLray : q ∈ raySet L.anchor L.rayDirection)
    (hqMray : q ∈ raySet M.anchor M.rayDirection)
    (hrLcircle : r ∈ circleSet L.center L.radius)
    (hrMcircle : r ∈ circleSet M.center M.radius)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMray : r ∈ raySet M.anchor M.rayDirection) :
    PairComponentFiveOverlap L M :=
  PairComponentFiveOverlap.twoDouble
    (pairComponentTwoDoubleOverlapOfPrimitiveCcRrCrRc
      hqLcircle hqMcircle hqLray hqMray
      hrLcircle hrMcircle hrLray hrMray)

end PairComponentFiveOverlap

/-- A shared anchor and the standard genericity hypotheses give a direct
whole-carrier `<= 4` savings certificate. -/
def pairCarrierSavingsFourOfCommonAnchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  (PairComponentAllFourOverlap.of_common_anchor hanchor).toPairCarrierSavings
    hLM hline

/-- A shared anchor and the standard genericity hypotheses also give the
weaker direct whole-carrier `<= 5` savings certificate used by the close-only
and intriguing-only branches. -/
def pairCarrierSavingsFiveOfCommonAnchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 :=
  (PairComponentFiveOverlap.of_common_anchor hanchor).toPairCarrierSavings
    hLM hline

/-- A primitive coordinate point lying on both circles and both rays, together
with the standard genericity hypotheses, gives direct whole-carrier `<= 4`
savings. -/
def pairCarrierSavingsFourOfPrimitivePoint
    {L M : EuclideanLollipop} {p : R2}
    (hLcircle : p ∈ circleSet L.center L.radius)
    (hMcircle : p ∈ circleSet M.center M.radius)
    (hLray : p ∈ raySet L.anchor L.rayDirection)
    (hMray : p ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  (PairComponentAllFourOverlap.of_primitive_point
    hLcircle hMcircle hLray hMray).toPairCarrierSavings hLM hline

/-- The same primitive all-four point gives the weaker direct whole-carrier
`<= 5` savings used by the close-only and intriguing-only branches. -/
def pairCarrierSavingsFiveOfPrimitivePoint
    {L M : EuclideanLollipop} {p : R2}
    (hLcircle : p ∈ circleSet L.center L.radius)
    (hMcircle : p ∈ circleSet M.center M.radius)
    (hLray : p ∈ raySet L.anchor L.rayDirection)
    (hMray : p ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 :=
  (PairComponentFiveOverlap.of_primitive_point
    hLcircle hMcircle hLray hMray).toPairCarrierSavings hLM hline

/-- Primitive coordinate data for the `cc/cr` and `rc/rr` two-double pattern,
together with the standard genericity hypotheses, give direct whole-carrier
`<= 5` savings. -/
def pairCarrierSavingsFiveOfPrimitiveTwoDoubleCcCrRcRr
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqMray : q ∈ raySet M.anchor M.rayDirection)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMcircle : r ∈ circleSet M.center M.radius)
    (hrMray : r ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 :=
  (PairComponentFiveOverlap.of_primitive_two_double_cc_cr_and_rc_rr
    hqLcircle hqMcircle hqMray hrLray hrMcircle hrMray).toPairCarrierSavings
      hLM hline

/-- Primitive coordinate data for the `cc/rc` and `cr/rr` two-double pattern,
together with the standard genericity hypotheses, give direct whole-carrier
`<= 5` savings. -/
def pairCarrierSavingsFiveOfPrimitiveTwoDoubleCcRcCrRr
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqLray : q ∈ raySet L.anchor L.rayDirection)
    (hrLcircle : r ∈ circleSet L.center L.radius)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMray : r ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 :=
  (PairComponentFiveOverlap.of_primitive_two_double_cc_rc_and_cr_rr
    hqLcircle hqMcircle hqLray hrLcircle hrLray hrMray).toPairCarrierSavings
      hLM hline

/-- Primitive coordinate data for the `cc/rr` and `cr/rc` two-double pattern,
together with the standard genericity hypotheses, give direct whole-carrier
`<= 5` savings. -/
def pairCarrierSavingsFiveOfPrimitiveTwoDoubleCcRrCrRc
    {L M : EuclideanLollipop} {q r : R2}
    (hqLcircle : q ∈ circleSet L.center L.radius)
    (hqMcircle : q ∈ circleSet M.center M.radius)
    (hqLray : q ∈ raySet L.anchor L.rayDirection)
    (hqMray : q ∈ raySet M.anchor M.rayDirection)
    (hrLcircle : r ∈ circleSet L.center L.radius)
    (hrMcircle : r ∈ circleSet M.center M.radius)
    (hrLray : r ∈ raySet L.anchor L.rayDirection)
    (hrMray : r ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 :=
  (PairComponentFiveOverlap.of_primitive_two_double_cc_rr_and_cr_rc
    hqLcircle hqMcircle hqLray hqMray
    hrLcircle hrMcircle hrLray hrMray).toPairCarrierSavings hLM hline

/-- Primitive coordinate data for the same-point `cc/cr` and `rc/rr`
two-double pattern give the all-four-overlap witness. -/
def pairComponentAllFourOverlapOfPrimitiveSamePointTwoDoubleCcCrRcRr
    {L M : EuclideanLollipop} {p : R2}
    (hpLcircle : p ∈ circleSet L.center L.radius)
    (hpMcircle : p ∈ circleSet M.center M.radius)
    (hpMray : p ∈ raySet M.anchor M.rayDirection)
    (hpLray : p ∈ raySet L.anchor L.rayDirection) :
    PairComponentAllFourOverlap L M :=
  PairComponentAllFourOverlap.of_primitive_point
    (p := p) hpLcircle hpMcircle hpLray hpMray

/-- Primitive coordinate data for the same-point `cc/rc` and `cr/rr`
two-double pattern give the all-four-overlap witness. -/
def pairComponentAllFourOverlapOfPrimitiveSamePointTwoDoubleCcRcCrRr
    {L M : EuclideanLollipop} {p : R2}
    (hpLcircle : p ∈ circleSet L.center L.radius)
    (hpMcircle : p ∈ circleSet M.center M.radius)
    (hpLray : p ∈ raySet L.anchor L.rayDirection)
    (hpMray : p ∈ raySet M.anchor M.rayDirection) :
    PairComponentAllFourOverlap L M :=
  PairComponentAllFourOverlap.of_primitive_point
    (p := p) hpLcircle hpMcircle hpLray hpMray

/-- Primitive coordinate data for the same-point `cc/rr` and `cr/rc`
two-double pattern give the all-four-overlap witness. -/
def pairComponentAllFourOverlapOfPrimitiveSamePointTwoDoubleCcRrCrRc
    {L M : EuclideanLollipop} {p : R2}
    (hpLcircle : p ∈ circleSet L.center L.radius)
    (hpMcircle : p ∈ circleSet M.center M.radius)
    (hpLray : p ∈ raySet L.anchor L.rayDirection)
    (hpMray : p ∈ raySet M.anchor M.rayDirection) :
    PairComponentAllFourOverlap L M :=
  PairComponentAllFourOverlap.of_primitive_point
    (p := p) hpLcircle hpMcircle hpLray hpMray

/-- Primitive coordinate data for the same-point `cc/cr` and `rc/rr`
two-double pattern give direct whole-carrier `<= 4` savings. -/
def pairCarrierSavingsFourOfPrimitiveSamePointTwoDoubleCcCrRcRr
    {L M : EuclideanLollipop} {p : R2}
    (hpLcircle : p ∈ circleSet L.center L.radius)
    (hpMcircle : p ∈ circleSet M.center M.radius)
    (hpMray : p ∈ raySet M.anchor M.rayDirection)
    (hpLray : p ∈ raySet L.anchor L.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  (pairComponentAllFourOverlapOfPrimitiveSamePointTwoDoubleCcCrRcRr
    hpLcircle hpMcircle hpMray hpLray).toPairCarrierSavings hLM hline

/-- Primitive coordinate data for the same-point `cc/rc` and `cr/rr`
two-double pattern give direct whole-carrier `<= 4` savings. -/
def pairCarrierSavingsFourOfPrimitiveSamePointTwoDoubleCcRcCrRr
    {L M : EuclideanLollipop} {p : R2}
    (hpLcircle : p ∈ circleSet L.center L.radius)
    (hpMcircle : p ∈ circleSet M.center M.radius)
    (hpLray : p ∈ raySet L.anchor L.rayDirection)
    (hpMray : p ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  (pairComponentAllFourOverlapOfPrimitiveSamePointTwoDoubleCcRcCrRr
    hpLcircle hpMcircle hpLray hpMray).toPairCarrierSavings hLM hline

/-- Primitive coordinate data for the same-point `cc/rr` and `cr/rc`
two-double pattern give direct whole-carrier `<= 4` savings. -/
def pairCarrierSavingsFourOfPrimitiveSamePointTwoDoubleCcRrCrRc
    {L M : EuclideanLollipop} {p : R2}
    (hpLcircle : p ∈ circleSet L.center L.radius)
    (hpMcircle : p ∈ circleSet M.center M.radius)
    (hpLray : p ∈ raySet L.anchor L.rayDirection)
    (hpMray : p ∈ raySet M.anchor M.rayDirection)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  (pairComponentAllFourOverlapOfPrimitiveSamePointTwoDoubleCcRrCrRc
    hpLcircle hpMcircle hpLray hpMray).toPairCarrierSavings hLM hline

/-! ## Primitive coordinate overlap certificates -/

/-- Raw coordinate data for one point lying on both circles and both rays. -/
structure PrimitivePairAllFourOverlap
    (L M : EuclideanLollipop) : Type where
  point : R2
  leftCircle : point ∈ circleSet L.center L.radius
  rightCircle : point ∈ circleSet M.center M.radius
  leftRay : point ∈ raySet L.anchor L.rayDirection
  rightRay : point ∈ raySet M.anchor M.rayDirection

namespace PrimitivePairAllFourOverlap

/-- If two primitive lollipops share their anchor, that common primitive
point lies on both circles and both rays. -/
def of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    PrimitivePairAllFourOverlap L M where
  point := L.anchor
  leftCircle := L.anchor_on_circle
  rightCircle := by
    simpa [hanchor] using M.anchor_on_circle
  leftRay := anchor_mem_raySet L.anchor L.rayDirection
  rightRay := by
    simpa [hanchor] using anchor_mem_raySet M.anchor M.rayDirection

/-- Raw all-four overlap data are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop}
    (H : PrimitivePairAllFourOverlap L M) :
    PrimitivePairAllFourOverlap M L where
  point := H.point
  leftCircle := H.rightCircle
  rightCircle := H.leftCircle
  leftRay := H.rightRay
  rightRay := H.leftRay

/-- Canonicalize raw all-four overlap data supplied in either lollipop order. -/
def ofEither
    {L M : EuclideanLollipop}
    (H :
      PrimitivePairAllFourOverlap L M ⊕
        PrimitivePairAllFourOverlap M L) :
    PrimitivePairAllFourOverlap L M := by
  cases H with
  | inl H => exact H
  | inr H => exact H.symm

/-- Raw coordinate all-four data give the existing lifted all-four component
overlap witness. -/
def toPairComponentAllFourOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairAllFourOverlap L M) :
    PairComponentAllFourOverlap L M :=
  PairComponentAllFourOverlap.of_primitive_point
    (p := H.point) H.leftCircle H.rightCircle H.leftRay H.rightRay

/-- Raw coordinate all-four data give direct whole-carrier `<= 4` savings. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop}
    (H : PrimitivePairAllFourOverlap L M)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  H.toPairComponentAllFourOverlap.toPairCarrierSavings hLM hline

end PrimitivePairAllFourOverlap

/-- Raw coordinate data for one point realizing any three of the four
circle/ray component patterns.  Lean derives the missing fourth component
because these are product components. -/
inductive PrimitivePairTripleOverlap
    (L M : EuclideanLollipop) : Type where
  | withoutCircleCircle
      (p : R2)
      (hCircleRayLeftCircle : p ∈ circleSet L.center L.radius)
      (hCircleRayRightRay : p ∈ raySet M.anchor M.rayDirection)
      (hRayCircleLeftRay : p ∈ raySet L.anchor L.rayDirection)
      (hRayCircleRightCircle : p ∈ circleSet M.center M.radius)
  | withoutCircleRay
      (p : R2)
      (hCircleCircleLeftCircle : p ∈ circleSet L.center L.radius)
      (hCircleCircleRightCircle : p ∈ circleSet M.center M.radius)
      (hRayCircleLeftRay : p ∈ raySet L.anchor L.rayDirection)
      (hRayRayRightRay : p ∈ raySet M.anchor M.rayDirection)
  | withoutRayCircle
      (p : R2)
      (hCircleCircleLeftCircle : p ∈ circleSet L.center L.radius)
      (hCircleCircleRightCircle : p ∈ circleSet M.center M.radius)
      (hCircleRayRightRay : p ∈ raySet M.anchor M.rayDirection)
      (hRayRayLeftRay : p ∈ raySet L.anchor L.rayDirection)
  | withoutRayRay
      (p : R2)
      (hCircleCircleLeftCircle : p ∈ circleSet L.center L.radius)
      (hCircleCircleRightCircle : p ∈ circleSet M.center M.radius)
      (hCircleRayRightRay : p ∈ raySet M.anchor M.rayDirection)
      (hRayCircleLeftRay : p ∈ raySet L.anchor L.rayDirection)

namespace PrimitivePairTripleOverlap

/-- Raw primitive triple-overlap data are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop}
    (H : PrimitivePairTripleOverlap L M) :
    PrimitivePairTripleOverlap M L := by
  cases H with
  | withoutCircleCircle p hLcircle hMray hLray hMcircle =>
      exact
        PrimitivePairTripleOverlap.withoutCircleCircle
          p hMcircle hLray hMray hLcircle
  | withoutCircleRay p hLcircle hMcircle hLray hMray =>
      exact
        PrimitivePairTripleOverlap.withoutCircleRay
          p hMcircle hLcircle hMray hLray
  | withoutRayCircle p hLcircle hMcircle hMray hLray =>
      exact
        PrimitivePairTripleOverlap.withoutRayCircle
          p hMcircle hLcircle hLray hMray
  | withoutRayRay p hLcircle hMcircle hMray hLray =>
      exact
        PrimitivePairTripleOverlap.withoutRayRay
          p hMcircle hLcircle hLray hMray

/-- Canonicalize raw triple-overlap data supplied in either lollipop order. -/
def ofEither
    {L M : EuclideanLollipop}
    (H :
      PrimitivePairTripleOverlap L M ⊕
        PrimitivePairTripleOverlap M L) :
    PrimitivePairTripleOverlap L M := by
  cases H with
  | inl H => exact H
  | inr H => exact H.symm

/-- Raw primitive triple-overlap data imply raw all-four overlap data. -/
def toPrimitivePairAllFourOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairTripleOverlap L M) :
    PrimitivePairAllFourOverlap L M := by
  cases H with
  | withoutCircleCircle p hLcircle hMray hLray hMcircle =>
      exact
        { point := p
          leftCircle := hLcircle
          rightCircle := hMcircle
          leftRay := hLray
          rightRay := hMray }
  | withoutCircleRay p hLcircle hMcircle hLray hMray =>
      exact
        { point := p
          leftCircle := hLcircle
          rightCircle := hMcircle
          leftRay := hLray
          rightRay := hMray }
  | withoutRayCircle p hLcircle hMcircle hMray hLray =>
      exact
        { point := p
          leftCircle := hLcircle
          rightCircle := hMcircle
          leftRay := hLray
          rightRay := hMray }
  | withoutRayRay p hLcircle hMcircle hMray hLray =>
      exact
        { point := p
          leftCircle := hLcircle
          rightCircle := hMcircle
          leftRay := hLray
          rightRay := hMray }

/-- Raw primitive triple-overlap data give the lifted all-four component
overlap witness. -/
def toPairComponentAllFourOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairTripleOverlap L M) :
    PairComponentAllFourOverlap L M :=
  H.toPrimitivePairAllFourOverlap.toPairComponentAllFourOverlap

/-- Raw primitive triple-overlap data give direct whole-carrier `<= 4`
savings. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop}
    (H : PrimitivePairTripleOverlap L M)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  H.toPairComponentAllFourOverlap.toPairCarrierSavings hLM hline

end PrimitivePairTripleOverlap

/-- Raw primitive data sufficient for direct `<= 4` whole-carrier savings.  The
constructors include explicit all-four data, triple-overlap data, and the three
same-point two-double patterns. -/
inductive PrimitivePairFourOverlap
    (L M : EuclideanLollipop) : Type where
  | allFour
      (H : PrimitivePairAllFourOverlap L M)
  | triple
      (H : PrimitivePairTripleOverlap L M)
  | samePointTwoDoubleCcCrRcRr
      (p : R2)
      (hpLcircle : p ∈ circleSet L.center L.radius)
      (hpMcircle : p ∈ circleSet M.center M.radius)
      (hpMray : p ∈ raySet M.anchor M.rayDirection)
      (hpLray : p ∈ raySet L.anchor L.rayDirection)
  | samePointTwoDoubleCcRcCrRr
      (p : R2)
      (hpLcircle : p ∈ circleSet L.center L.radius)
      (hpMcircle : p ∈ circleSet M.center M.radius)
      (hpLray : p ∈ raySet L.anchor L.rayDirection)
      (hpMray : p ∈ raySet M.anchor M.rayDirection)
  | samePointTwoDoubleCcRrCrRc
      (p : R2)
      (hpLcircle : p ∈ circleSet L.center L.radius)
      (hpMcircle : p ∈ circleSet M.center M.radius)
      (hpLray : p ∈ raySet L.anchor L.rayDirection)
      (hpMray : p ∈ raySet M.anchor M.rayDirection)

namespace PrimitivePairFourOverlap

/-- A shared primitive anchor gives raw primitive four-overlap data. -/
def of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    PrimitivePairFourOverlap L M :=
  PrimitivePairFourOverlap.allFour
    (PrimitivePairAllFourOverlap.of_common_anchor hanchor)

/-- Raw primitive four-overlap data are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop}
    (H : PrimitivePairFourOverlap L M) :
    PrimitivePairFourOverlap M L := by
  cases H with
  | allFour H =>
      exact PrimitivePairFourOverlap.allFour H.symm
  | triple H =>
      exact PrimitivePairFourOverlap.triple H.symm
  | samePointTwoDoubleCcCrRcRr p hpLcircle hpMcircle hpMray hpLray =>
      exact
        PrimitivePairFourOverlap.allFour
          { point := p
            leftCircle := hpMcircle
            rightCircle := hpLcircle
            leftRay := hpMray
            rightRay := hpLray }
  | samePointTwoDoubleCcRcCrRr p hpLcircle hpMcircle hpLray hpMray =>
      exact
        PrimitivePairFourOverlap.allFour
          { point := p
            leftCircle := hpMcircle
            rightCircle := hpLcircle
            leftRay := hpMray
            rightRay := hpLray }
  | samePointTwoDoubleCcRrCrRc p hpLcircle hpMcircle hpLray hpMray =>
      exact
        PrimitivePairFourOverlap.allFour
          { point := p
            leftCircle := hpMcircle
            rightCircle := hpLcircle
            leftRay := hpMray
            rightRay := hpLray }

/-- Canonicalize raw primitive four-overlap data supplied in either lollipop
order. -/
def ofEither
    {L M : EuclideanLollipop}
    (H :
      PrimitivePairFourOverlap L M ⊕
        PrimitivePairFourOverlap M L) :
    PrimitivePairFourOverlap L M := by
  cases H with
  | inl H => exact H
  | inr H => exact H.symm

/-- Raw primitive four-overlap data imply raw all-four overlap data. -/
def toPrimitivePairAllFourOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairFourOverlap L M) :
    PrimitivePairAllFourOverlap L M := by
  cases H with
  | allFour H =>
      exact H
  | triple H =>
      exact H.toPrimitivePairAllFourOverlap
  | samePointTwoDoubleCcCrRcRr p hpLcircle hpMcircle hpMray hpLray =>
      exact
        { point := p
          leftCircle := hpLcircle
          rightCircle := hpMcircle
          leftRay := hpLray
          rightRay := hpMray }
  | samePointTwoDoubleCcRcCrRr p hpLcircle hpMcircle hpLray hpMray =>
      exact
        { point := p
          leftCircle := hpLcircle
          rightCircle := hpMcircle
          leftRay := hpLray
          rightRay := hpMray }
  | samePointTwoDoubleCcRrCrRc p hpLcircle hpMcircle hpLray hpMray =>
      exact
        { point := p
          leftCircle := hpLcircle
          rightCircle := hpMcircle
          leftRay := hpLray
          rightRay := hpMray }

/-- Raw primitive four-overlap data give the lifted all-four component-overlap
witness. -/
def toPairComponentAllFourOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairFourOverlap L M) :
    PairComponentAllFourOverlap L M :=
  H.toPrimitivePairAllFourOverlap.toPairComponentAllFourOverlap

/-- Raw primitive four-overlap data give direct whole-carrier `<= 4` savings. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop}
    (H : PrimitivePairFourOverlap L M)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 4 :=
  H.toPairComponentAllFourOverlap.toPairCarrierSavings hLM hline

end PrimitivePairFourOverlap

/-- Raw coordinate data sufficient for direct `<= 5` whole-carrier savings:
either one primitive point lies in all four components, or two primitive
witnesses realize one of the three two-double overlap patterns. -/
inductive PrimitivePairFiveOverlap
    (L M : EuclideanLollipop) : Type where
  | triple
      (H : PrimitivePairTripleOverlap L M)
  | allFour
      (p : R2)
      (hLcircle : p ∈ circleSet L.center L.radius)
      (hMcircle : p ∈ circleSet M.center M.radius)
      (hLray : p ∈ raySet L.anchor L.rayDirection)
      (hMray : p ∈ raySet M.anchor M.rayDirection)
  | twoDoubleCcCrRcRr
      (q r : R2)
      (hqLcircle : q ∈ circleSet L.center L.radius)
      (hqMcircle : q ∈ circleSet M.center M.radius)
      (hqMray : q ∈ raySet M.anchor M.rayDirection)
      (hrLray : r ∈ raySet L.anchor L.rayDirection)
      (hrMcircle : r ∈ circleSet M.center M.radius)
      (hrMray : r ∈ raySet M.anchor M.rayDirection)
  | twoDoubleCcRcCrRr
      (q r : R2)
      (hqLcircle : q ∈ circleSet L.center L.radius)
      (hqMcircle : q ∈ circleSet M.center M.radius)
      (hqLray : q ∈ raySet L.anchor L.rayDirection)
      (hrLcircle : r ∈ circleSet L.center L.radius)
      (hrLray : r ∈ raySet L.anchor L.rayDirection)
      (hrMray : r ∈ raySet M.anchor M.rayDirection)
  | twoDoubleCcRrCrRc
      (q r : R2)
      (hqLcircle : q ∈ circleSet L.center L.radius)
      (hqMcircle : q ∈ circleSet M.center M.radius)
      (hqLray : q ∈ raySet L.anchor L.rayDirection)
      (hqMray : q ∈ raySet M.anchor M.rayDirection)
      (hrLcircle : r ∈ circleSet L.center L.radius)
      (hrMcircle : r ∈ circleSet M.center M.radius)
      (hrLray : r ∈ raySet L.anchor L.rayDirection)
      (hrMray : r ∈ raySet M.anchor M.rayDirection)

namespace PrimitivePairFiveOverlap

/-- Raw primitive five-overlap data are symmetric in the two lollipops. -/
def symm
    {L M : EuclideanLollipop}
    (H : PrimitivePairFiveOverlap L M) :
    PrimitivePairFiveOverlap M L := by
  cases H with
  | triple H =>
      exact PrimitivePairFiveOverlap.triple H.symm
  | allFour p hLcircle hMcircle hLray hMray =>
      exact PrimitivePairFiveOverlap.allFour
        p hMcircle hLcircle hMray hLray
  | twoDoubleCcCrRcRr q r hqLcircle hqMcircle hqMray
      hrLray hrMcircle hrMray =>
      exact
        PrimitivePairFiveOverlap.twoDoubleCcRcCrRr
          q r hqMcircle hqLcircle hqMray
          hrMcircle hrMray hrLray
  | twoDoubleCcRcCrRr q r hqLcircle hqMcircle hqLray
      hrLcircle hrLray hrMray =>
      exact
        PrimitivePairFiveOverlap.twoDoubleCcCrRcRr
          q r hqMcircle hqLcircle hqLray
          hrMray hrLcircle hrLray
  | twoDoubleCcRrCrRc q r hqLcircle hqMcircle hqLray hqMray
      hrLcircle hrMcircle hrLray hrMray =>
      exact
        PrimitivePairFiveOverlap.twoDoubleCcRrCrRc
          q r hqMcircle hqLcircle hqMray hqLray
          hrMcircle hrLcircle hrMray hrLray

/-- Canonicalize raw primitive five-overlap data supplied in either lollipop
order. -/
def ofEither
    {L M : EuclideanLollipop}
    (H :
      PrimitivePairFiveOverlap L M ⊕
        PrimitivePairFiveOverlap M L) :
    PrimitivePairFiveOverlap L M := by
  cases H with
  | inl H => exact H
  | inr H => exact H.symm

/-- Raw coordinate five-overlap data give the existing lifted component
five-overlap witness. -/
def toPairComponentFiveOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairFiveOverlap L M) :
    PairComponentFiveOverlap L M := by
  cases H with
  | triple H =>
      exact PairComponentFiveOverlap.of_all_four
        H.toPairComponentAllFourOverlap
  | allFour p hLcircle hMcircle hLray hMray =>
      exact
        PairComponentFiveOverlap.of_primitive_point
          (p := p) hLcircle hMcircle hLray hMray
  | twoDoubleCcCrRcRr q r hqLcircle hqMcircle hqMray
      hrLray hrMcircle hrMray =>
      exact
        PairComponentFiveOverlap.of_primitive_two_double_cc_cr_and_rc_rr
          (q := q) (r := r)
          hqLcircle hqMcircle hqMray hrLray hrMcircle hrMray
  | twoDoubleCcRcCrRr q r hqLcircle hqMcircle hqLray
      hrLcircle hrLray hrMray =>
      exact
        PairComponentFiveOverlap.of_primitive_two_double_cc_rc_and_cr_rr
          (q := q) (r := r)
          hqLcircle hqMcircle hqLray hrLcircle hrLray hrMray
  | twoDoubleCcRrCrRc q r hqLcircle hqMcircle hqLray hqMray
      hrLcircle hrMcircle hrLray hrMray =>
      exact
        PairComponentFiveOverlap.of_primitive_two_double_cc_rr_and_cr_rc
          (q := q) (r := r)
          hqLcircle hqMcircle hqLray hqMray
          hrLcircle hrMcircle hrLray hrMray

/-- Raw coordinate five-overlap data give direct whole-carrier `<= 5`
savings. -/
def toPairCarrierSavings
    {L M : EuclideanLollipop}
    (H : PrimitivePairFiveOverlap L M)
    (hLM :
      euclideanSphere L.center L.radius ≠
        euclideanSphere M.center M.radius)
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    PairCarrierSavings L M 5 :=
  H.toPairComponentFiveOverlap.toPairCarrierSavings hLM hline

/-- Raw all-four coordinate data are stronger than the primitive five-overlap
boundary. -/
def of_all_four
    {L M : EuclideanLollipop}
    (H : PrimitivePairAllFourOverlap L M) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.allFour
    H.point H.leftCircle H.rightCircle H.leftRay H.rightRay

/-- Raw primitive triple-overlap data are stronger than the primitive
five-overlap boundary. -/
def of_triple
    {L M : EuclideanLollipop}
    (H : PrimitivePairTripleOverlap L M) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.triple H

/-- Raw primitive four-overlap data are stronger than the primitive
five-overlap boundary. -/
def of_four
    {L M : EuclideanLollipop}
    (H : PrimitivePairFourOverlap L M) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.of_all_four H.toPrimitivePairAllFourOverlap

/-- A shared primitive anchor gives raw primitive five-overlap data. -/
def of_common_anchor
    {L M : EuclideanLollipop}
    (hanchor : L.anchor = M.anchor) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.of_all_four
    (PrimitivePairAllFourOverlap.of_common_anchor hanchor)

end PrimitivePairFiveOverlap

namespace PrimitivePairAllFourOverlap

/-- Raw all-four coordinate data also give the primitive four-overlap witness
needed by the close-and-intriguing branch. -/
def toPrimitivePairFourOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairAllFourOverlap L M) :
    PrimitivePairFourOverlap L M :=
  PrimitivePairFourOverlap.allFour H

/-- Raw all-four coordinate data also give the primitive five-overlap witness
needed by the close-only and intriguing-only branches. -/
def toPrimitivePairFiveOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairAllFourOverlap L M) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.of_all_four H

end PrimitivePairAllFourOverlap

namespace PrimitivePairTripleOverlap

/-- Raw primitive triple-overlap data also give the primitive five-overlap
witness needed by close-only and intriguing-only branches. -/
def toPrimitivePairFiveOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairTripleOverlap L M) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.of_triple H

end PrimitivePairTripleOverlap

namespace PrimitivePairFourOverlap

/-- Raw primitive four-overlap data also give the primitive five-overlap witness
needed by close-only and intriguing-only branches. -/
def toPrimitivePairFiveOverlap
    {L M : EuclideanLollipop}
    (H : PrimitivePairFourOverlap L M) :
    PrimitivePairFiveOverlap L M :=
  PrimitivePairFiveOverlap.of_four H

end PrimitivePairFourOverlap

/-- Automatic upper certificate whose close/intriguing branches are supplied
by concrete overlap witnesses rather than by prebuilt direct-savings
certificates. -/
structure OverlapSavingsStepwiseCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  close_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PairComponentFiveOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  intriguing_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentFiveOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  close_intriguing_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentAllFourOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A)
        (CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (arrangement n A)
          (spheres_distinct n A)
          (rayLines_distinct n A))
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace OverlapSavingsStepwiseCertificate

/-- Overlap-witness upper certificates are a special case of direct-savings
automatic upper certificates. -/
noncomputable def toDirectSavingsStepwiseCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : OverlapSavingsStepwiseCertificate P) :
    CompleteFormalization.AutomaticUpper.DirectSavingsStepwiseCertificate P where
  arrangement := h.arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := by
    intro n A i j hij hclose
    exact
      (h.close_overlap n A i j hij hclose).toPairCarrierSavings
        (h.spheres_distinct n A i j hij)
        (h.rayLines_distinct n A i j hij)
  intriguing_savings := by
    intro n A i j hij hintriguing
    exact
      (h.intriguing_overlap n A i j hij hintriguing).toPairCarrierSavings
        (h.spheres_distinct n A i j hij)
        (h.rayLines_distinct n A i j hij)
  close_intriguing_savings := by
    intro n A i j hij hclose hintriguing
    exact
      (h.close_intriguing_overlap n A i j hij hclose hintriguing)
        |>.toPairCarrierSavings
          (h.spheres_distinct n A i j hij)
          (h.rayLines_distinct n A i j hij)
  region_increment := h.region_increment
  radial_outward := h.radial_outward

end OverlapSavingsStepwiseCertificate

/-- Automatic upper certificate whose close/intriguing branches are supplied
as raw primitive coordinate overlap data.  This is the construction-facing
version of `OverlapSavingsStepwiseCertificate`; no lifted component-overlap
witnesses need to be built by hand. -/
structure PrimitiveOverlapSavingsStepwiseCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  close_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PrimitivePairFiveOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  intriguing_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitivePairFiveOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  close_intriguing_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitivePairAllFourOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A)
        (CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (arrangement n A)
          (spheres_distinct n A)
          (rayLines_distinct n A))
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PrimitiveOverlapSavingsStepwiseCertificate

/-- Primitive coordinate overlap certificates are a special case of the
existing lifted overlap-witness automatic upper certificates. -/
noncomputable def toOverlapSavingsStepwiseCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveOverlapSavingsStepwiseCertificate P) :
    OverlapSavingsStepwiseCertificate P where
  arrangement := h.arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_overlap := by
    intro n A i j hij hclose
    exact
      (h.close_overlap n A i j hij hclose).toPairComponentFiveOverlap
  intriguing_overlap := by
    intro n A i j hij hintriguing
    exact
      (h.intriguing_overlap n A i j hij hintriguing).toPairComponentFiveOverlap
  close_intriguing_overlap := by
    intro n A i j hij hclose hintriguing
    exact
      (h.close_intriguing_overlap n A i j hij hclose hintriguing)
        |>.toPairComponentAllFourOverlap
  region_increment := h.region_increment
  radial_outward := h.radial_outward

end PrimitiveOverlapSavingsStepwiseCertificate

/-- Primitive upper certificate whose close-and-intriguing branch may be any
raw primitive `<= 4` overlap witness: all-four, triple, or same-point
two-double.  It converts to the older primitive upper certificate by deriving
the corresponding all-four witness. -/
structure PrimitiveFlexibleOverlapSavingsStepwiseCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      EuclideanLollipopArrangement n
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      euclideanRayLine ((arrangement n A).lollipop i) ≠
        euclideanRayLine ((arrangement n A).lollipop j)
  close_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PrimitivePairFiveOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  intriguing_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitivePairFiveOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  close_intriguing_overlap :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitivePairFourOverlap ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A)
        (CompleteFormalization.FiniteCarrier.automaticCarrierCrossingTable
          (arrangement n A)
          (spheres_distinct n A)
          (rayLines_distinct n A))
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PrimitiveFlexibleOverlapSavingsStepwiseCertificate

/-- Flexible primitive upper certificates are a special case of the existing
primitive upper certificate. -/
noncomputable def toPrimitiveOverlapSavingsStepwiseCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveFlexibleOverlapSavingsStepwiseCertificate P) :
    PrimitiveOverlapSavingsStepwiseCertificate P where
  arrangement := h.arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_overlap := h.close_overlap
  intriguing_overlap := h.intriguing_overlap
  close_intriguing_overlap := by
    intro n A i j hij hclose hintriguing
    exact
      (h.close_intriguing_overlap n A i j hij hclose hintriguing)
        |>.toPrimitivePairAllFourOverlap
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Flexible primitive upper certificates also convert directly to the lifted
overlap-witness upper certificate. -/
noncomputable def toOverlapSavingsStepwiseCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveFlexibleOverlapSavingsStepwiseCertificate P) :
    OverlapSavingsStepwiseCertificate P :=
  h.toPrimitiveOverlapSavingsStepwiseCertificate.toOverlapSavingsStepwiseCertificate

end PrimitiveFlexibleOverlapSavingsStepwiseCertificate

end

end OverlapUpper
end EndToEndFormalization
end TheoremOneManuscript
end Lollipop
