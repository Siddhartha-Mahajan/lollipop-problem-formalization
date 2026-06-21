import Lollipop.Internal.Manuscript.CompleteFormalization.FiniteCarrier
import Lollipop.Internal.Manuscript.FirstPrinciples.LocalBoundary
import Lollipop.Internal.Manuscript.PrimitiveGeometry.CarrierSavings

/-!
Automatic upper carrier witnesses.

`FirstPrinciples.LocalBoundary` still allowed each upper pair to provide its
finite carrier-intersection witness as data.  The finite-carrier construction
in this folder removes that field: after the usual generic noncoincidence
hypotheses, Lean constructs the finite witness and the crossing table by
counting it.  The remaining upper obligations are the genuinely geometric
route-savings certificates and the ordered insertion-region recurrence.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace CompleteFormalization

universe u

open PrimitiveGeometry

namespace AutomaticUpper

noncomputable section

/-- Upper certificate with automatic finite carrier-intersection witnesses.

For each arrangement, the crossing table is definitionally the cardinality of
the finite carrier-intersection `Finset` constructed from the two generic
noncoincidence facts.  The certificate still requires the route constructors
for close/intriguing savings and the stepwise region recurrence for that
automatic table. -/
structure RoutedStepwiseCertificate
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
  close_savings_route :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PairComponentSavingsFiveRoute ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  intriguing_savings_route :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentSavingsFiveRoute ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  close_intriguing_savings_route :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairComponentSavingsFourRoute ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j)
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A)
        (FiniteCarrier.automaticCarrierCrossingTable
          (arrangement n A)
          (spheres_distinct n A)
          (rayLines_distinct n A))
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace RoutedStepwiseCertificate

/-- The automatic crossing table associated to one arrangement. -/
noncomputable def cross
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedStepwiseCertificate P)
    (n : Nat) (A : P.Arrangement n) : Fin n → Fin n → Rat :=
  FiniteCarrier.automaticCarrierCrossingTable
    (h.arrangement n A)
    (h.spheres_distinct n A)
    (h.rayLines_distinct n A)

/-- Automatic upper certificates produce the routed local upper boundary used
by the first-principles theorem stack. -/
noncomputable def toRoutedPairStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedStepwiseCertificate P) :
    FirstPrinciples.RoutedPairStepwiseLocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  routed_local_pair_data := by
    intro n A i j hij
    let E := h.arrangement n A
    let hLM := h.spheres_distinct n A i j hij
    let hline := h.rayLines_distinct n A i j hij
    exact
      { carrier_crossing :=
          FiniteCarrier.localPairCarrierCrossingDataOfFiniteCarrierEq
            (A := E) hij hLM hline
            (by
              simpa [RoutedStepwiseCertificate.cross, E, hLM, hline] using
                FiniteCarrier.automaticCarrierCrossingTable_eq_card
                  (h.spheres_distinct n A) (h.rayLines_distinct n A) hij)
        spheres_distinct := hLM
        rayLines_distinct := hline
        close_savings_route := h.close_savings_route n A i j hij
        intriguing_savings_route := h.intriguing_savings_route n A i j hij
        close_intriguing_savings_route :=
          h.close_intriguing_savings_route n A i j hij }
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Automatic upper certificates also assemble to the non-routed local upper
boundary. -/
noncomputable def toPairStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedStepwiseCertificate P) :
    FirstPrinciples.PairStepwiseLocalEuclideanUpperCertificate P :=
  h.toRoutedPairStepwiseLocalEuclideanUpperCertificate
    |>.toPairStepwiseLocalEuclideanUpperCertificate

/-- The automatically generated table satisfies the generic `<= 7` pair
bound for every increasing pair. -/
theorem cross_le_seven
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedStepwiseCertificate P)
    {n : Nat} {A : P.Arrangement n} {i j : Fin n} (hij : i < j) :
    h.cross n A i j ≤ 7 :=
  FiniteCarrier.automaticCarrierCrossingTable_le_seven
    (h.spheres_distinct n A) (h.rayLines_distinct n A) hij

end RoutedStepwiseCertificate

/-- Upper certificate with automatic finite carrier-intersection witnesses and
direct whole-carrier savings bounds.  Compared with
`RoutedStepwiseCertificate`, the close/intriguing geometric input is already a
`PairCarrierSavings` certificate, so coupled overlap arguments can feed this
boundary without first decomposing into independent component caps. -/
structure DirectSavingsStepwiseCertificate
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
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PairCarrierSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairCarrierSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PairCarrierSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A)
        (FiniteCarrier.automaticCarrierCrossingTable
          (arrangement n A)
          (spheres_distinct n A)
          (rayLines_distinct n A))
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace DirectSavingsStepwiseCertificate

/-- The automatic crossing table associated to one arrangement. -/
noncomputable def cross
    {P : TheoremOne.ProblemFamily.{u}}
    (h : DirectSavingsStepwiseCertificate P)
    (n : Nat) (A : P.Arrangement n) : Fin n → Fin n → Rat :=
  FiniteCarrier.automaticCarrierCrossingTable
    (h.arrangement n A)
    (h.spheres_distinct n A)
    (h.rayLines_distinct n A)

/-- Automatic direct-savings upper data assemble to the primitive direct
whole-carrier upper package used by the theorem-facing proof stack. -/
noncomputable def toDirectSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : DirectSavingsStepwiseCertificate P) :
    PrimitiveCarrierDirectSavingsUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := by
    intro n A
    exact FiniteCarrier.pairwiseCarrierCrossingDataOfFiniteCarrier
      (h.arrangement n A) (h.spheres_distinct n A) (h.rayLines_distinct n A)
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := h.close_savings
  intriguing_savings := h.intriguing_savings
  close_intriguing_savings := h.close_intriguing_savings
  region_increment := by
    intro n A
    exact (h.region_increment n A).toOrderedIncrementalPairRegionData

/-- Routed automatic upper data are a special case of automatic direct
whole-carrier savings data. -/
noncomputable def ofRoutedStepwiseCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedStepwiseCertificate P) :
    DirectSavingsStepwiseCertificate P where
  arrangement := h.arrangement
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := by
    intro n A i j hij hclose
    exact (h.close_savings_route n A i j hij hclose).toPairCarrierSavings
  intriguing_savings := by
    intro n A i j hij hintriguing
    exact
      (h.intriguing_savings_route n A i j hij
        hintriguing).toPairCarrierSavings
  close_intriguing_savings := by
    intro n A i j hij hclose hintriguing
    exact
      (h.close_intriguing_savings_route n A i j hij hclose
        hintriguing).toPairCarrierSavings
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- The automatically generated table satisfies the generic `<= 7` pair
bound for every increasing pair. -/
theorem cross_le_seven
    {P : TheoremOne.ProblemFamily.{u}}
    (h : DirectSavingsStepwiseCertificate P)
    {n : Nat} {A : P.Arrangement n} {i j : Fin n} (hij : i < j) :
    h.cross n A i j ≤ 7 :=
  FiniteCarrier.automaticCarrierCrossingTable_le_seven
    (h.spheres_distinct n A) (h.rayLines_distinct n A) hij

end DirectSavingsStepwiseCertificate

/-- Theorem 1 certificate boundary with automatic upper carrier witnesses and
the strongest current local/stepwise lower boundary. -/
structure RoutedStepwiseTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : RoutedStepwiseCertificate P.toProblemFamily
  lower :
    FirstPrinciples.StepwisePairLocalKarlssonLowerCertificate
      P.toProblemFamily

namespace RoutedStepwiseTheoremOneCertificates

/-- Convert automatic-upper theorem certificates to the current strongest
first-principles boundary. -/
noncomputable def toRoutedAllPairStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedStepwiseTheoremOneCertificates P) :
    FirstPrinciples.RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper.toRoutedPairStepwiseLocalEuclideanUpperCertificate
  lower := h.lower

/-- Convert automatic-upper theorem certificates all the way to the
theorem-facing first-principles certificate package. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedStepwiseTheoremOneCertificates P) :
    FirstPrinciples.TheoremOneCertificates P :=
  h.toRoutedAllPairStepwiseFullyLocalTheoremOneCertificates
    |>.toTheoremOneCertificates

end RoutedStepwiseTheoremOneCertificates

/-- Automatic-upper theorem boundary with monotone local lower pair
inequalities.  This removes the exact lower copy-pair classification
requirement while keeping Lean-generated finite carrier witnesses on the upper
side. -/
structure RoutedStepwiseMonotoneLowerTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : RoutedStepwiseCertificate P.toProblemFamily
  lower :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate
      P.toProblemFamily

namespace RoutedStepwiseMonotoneLowerTheoremOneCertificates

/-- Convert automatic-upper monotone-lower certificates to the routed local
first-principles monotone boundary. -/
noncomputable def toRoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedStepwiseMonotoneLowerTheoremOneCertificates P) :
    FirstPrinciples.RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates
      P where
  upper := h.upper.toRoutedPairStepwiseLocalEuclideanUpperCertificate
  lower := h.lower

end RoutedStepwiseMonotoneLowerTheoremOneCertificates

/-- Direct-savings automatic-upper theorem boundary with the exact local
Karlsson lower package. -/
structure DirectSavingsStepwiseTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : DirectSavingsStepwiseCertificate P.toProblemFamily
  lower :
    FirstPrinciples.StepwisePairLocalKarlssonLowerCertificate
      P.toProblemFamily

namespace DirectSavingsStepwiseTheoremOneCertificates

/-- Convert automatic direct-savings theorem certificates to the
theorem-facing direct-savings/Karlsson-base subtheorem package. -/
noncomputable def toDirectSavingsKarlssonBaseLowerTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsStepwiseTheoremOneCertificates P) :
    FormalizedProof.DirectSavingsKarlssonBaseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper.toDirectSavingsUpperGeometryData
  lower_karlsson_base :=
    h.lower.toLocalKarlssonLowerCertificate
      |>.toKarlssonBaseBlowUpIncrementalLowerData

/-- Routed automatic upper theorem certificates are a special case of the
direct-savings automatic theorem boundary. -/
noncomputable def ofRoutedStepwiseTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedStepwiseTheoremOneCertificates P) :
    DirectSavingsStepwiseTheoremOneCertificates P where
  upper := DirectSavingsStepwiseCertificate.ofRoutedStepwiseCertificate h.upper
  lower := h.lower

end DirectSavingsStepwiseTheoremOneCertificates

/-- Direct-savings automatic-upper theorem boundary with monotone local lower
pair inequalities. -/
structure DirectSavingsStepwiseMonotoneLowerTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : DirectSavingsStepwiseCertificate P.toProblemFamily
  lower :
    FirstPrinciples.StepwisePairLocalKarlssonLowerBoundCertificate
      P.toProblemFamily

namespace DirectSavingsStepwiseMonotoneLowerTheoremOneCertificates

/-- Convert automatic direct-savings monotone-lower certificates to the
theorem-facing direct-savings/monotone-pairwise-lower package. -/
noncomputable def toDirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : DirectSavingsStepwiseMonotoneLowerTheoremOneCertificates P) :
    FormalizedProof.DirectSavingsMonotonePairwiseLowerTheoremOneSubtheorems
      P where
  upper_geometry := h.upper.toDirectSavingsUpperGeometryData
  lower_pairwise_bound :=
    h.lower
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

/-- Routed automatic upper monotone-lower theorem certificates are a special
case of the direct-savings automatic monotone theorem boundary. -/
noncomputable def ofRoutedStepwiseMonotoneLowerTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedStepwiseMonotoneLowerTheoremOneCertificates P) :
    DirectSavingsStepwiseMonotoneLowerTheoremOneCertificates P where
  upper := DirectSavingsStepwiseCertificate.ofRoutedStepwiseCertificate h.upper
  lower := h.lower

end DirectSavingsStepwiseMonotoneLowerTheoremOneCertificates

/-- Manuscript Theorem 1 follows from automatic upper carrier witnesses,
route-savings certificates, stepwise upper/lower region data, and local
Karlsson copy-pair lower certificates. -/
theorem theorem_one
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedStepwiseTheoremOneCertificates P) :
    FormalizedProof.FinalTheoremOneStatement P :=
  FirstPrinciples.theorem_one_from_routed_all_pair_stepwise_fully_local_first_principles_boundary
    P h.toRoutedAllPairStepwiseFullyLocalTheoremOneCertificates

/-- Single-size displayed formula from the automatic-upper boundary. -/
theorem theorem_one_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedStepwiseTheoremOneCertificates P)
    (n : Nat) :
    FormalizedProof.FinalTheoremOneAtStatement P n :=
  FirstPrinciples.theorem_one_at_from_routed_all_pair_stepwise_fully_local_first_principles_boundary
    P h.toRoutedAllPairStepwiseFullyLocalTheoremOneCertificates n

end

end AutomaticUpper
end CompleteFormalization
end TheoremOneManuscript
end Lollipop
