import Lollipop.Internal.Manuscript.FirstPrinciples.Boundary

/-!
Local first-principles boundary for manuscript Theorem 1.

`Boundary.lean` records the theorem-facing certificate boundary after all
generic Lean proof work has been discharged.  This file refines its upper
Euclidean input by replacing the global pairwise carrier-intersection
certificate with one local certificate for each unordered pair `i < j`.
Lean assembles those local certificates before invoking the existing
first-principles theorem.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace FirstPrinciples

universe u

/-- Lower certificate with Karlsson's four-base table supplied as the six
visible unordered values plus symmetry, rather than as a universal ordered
table theorem. -/
abbrev LocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  ExplicitInputs.KarlssonBaseSixPairBlowUpIncrementalLowerData P

/-- Expand the six-pair lower certificate into the theorem-facing lower
certificate used by `Boundary.lean`. -/
noncomputable def localKarlssonLowerCertificate_toKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalKarlssonLowerCertificate P) :
    KarlssonLowerCertificate P :=
  h.toKarlssonBaseBlowUpIncrementalLowerData

/-- Lower certificate where the local blow-up pair-value facts are supplied
one copy-pair at a time. -/
abbrev PairLocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u :=
  ExplicitInputs.KarlssonBaseSixPairLocalBlowUpIncrementalLowerData P

/-- Assemble local blow-up copy-pair values into the six-pair lower
certificate used by the theorem stack. -/
noncomputable def pairLocalKarlssonLowerCertificate_toLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairLocalKarlssonLowerCertificate P) :
    LocalKarlssonLowerCertificate P :=
  h.toKarlssonBaseSixPairBlowUpIncrementalLowerData

/-- Lower certificate with both local six-entry Karlsson base table data and
stepwise ordered insertion-region data. -/
structure StepwiseLocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    ExplicitInputs.KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    StepwiseOrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, i < j →
        pair_cross n (arrangement n q hq) i j =
          ExplicitInputs.karlssonBaseCopyPairCrossing base_pair_cross
            ((cluster_witness n q hq).cluster) i j
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwiseLocalKarlssonLowerCertificate

/-- Assemble stepwise lower-region data into the fully local lower certificate
used by the theorem stack. -/
noncomputable def toLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseLocalKarlssonLowerCertificate P) :
    LocalKarlssonLowerCertificate P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_table := h.base_pair_table
  base_region_increment :=
    h.base_region_increment.toOrderedIncrementalPairRegionData
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := h.pair_cross_eq_base_copy
  region_increment := by
    intro n q hq
    exact (h.region_increment n q hq).toOrderedIncrementalPairRegionData

end StepwiseLocalKarlssonLowerCertificate

/-- Lower certificate with local six-entry base table data, local copy-pair
value certificates, and stepwise ordered insertion-region data. -/
structure StepwisePairLocalKarlssonLowerCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  base_arrangement : P.Arrangement 4
  base_pair_cross : Fin 4 → Fin 4 → Rat
  base_pair_table :
    ExplicitInputs.KarlssonBaseSixPairTableCertificate base_pair_cross
  base_region_increment :
    StepwiseOrderedIncrementalPairRegionData 4
      (P.region 4 base_arrangement) base_pair_cross
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_cross_eq_base_copy :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.LocalKarlssonBaseCopyPairCrossingData
          base_pair_cross ((cluster_witness n q hq).cluster)
          (pair_cross n (arrangement n q hq)) i j hij
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwisePairLocalKarlssonLowerCertificate

/-- Assemble local copy-pair and local region-step data into the stepwise
lower certificate with a universal copy-pair theorem. -/
noncomputable def toStepwiseLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwisePairLocalKarlssonLowerCertificate P) :
    StepwiseLocalKarlssonLowerCertificate P where
  base_arrangement := h.base_arrangement
  base_pair_cross := h.base_pair_cross
  base_pair_table := h.base_pair_table
  base_region_increment := h.base_region_increment
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_eq_base_copy := by
    intro n q hq i j hij
    exact ExplicitInputs.pair_cross_eq_base_copy_from_local
      (h.local_pair_cross_eq_base_copy n q hq) i j hij
  region_increment := h.region_increment

/-- Assemble all local lower data into the six-pair lower certificate used by
the theorem stack. -/
noncomputable def toLocalKarlssonLowerCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwisePairLocalKarlssonLowerCertificate P) :
    LocalKarlssonLowerCertificate P :=
  h.toStepwiseLocalKarlssonLowerCertificate.toLocalKarlssonLowerCertificate

end StepwisePairLocalKarlssonLowerCertificate

/-- Lower certificate with local monotone copy-pair lower-bound certificates
and stepwise ordered insertion-region data.  Unlike
`StepwisePairLocalKarlssonLowerCertificate`, this does not require exact
classification of the copy-pair crossing value; proving the Karlsson cluster
value is a lower bound is enough for the lower half of Theorem 1. -/
structure StepwisePairLocalKarlssonLowerBoundCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, (q : QuadVec n) → q ∈ sortedQuadVecs n →
      P.Arrangement n
  cluster_witness :
    ∀ (n : Nat) (q : QuadVec n), q ∈ sortedQuadVecs n →
      ExplicitInputs.CardinalityClusteredKarlssonTableWitness q
  pair_cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_cross_ge_cluster :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      ∀ i j : Fin n, ∀ hij : i < j,
        ExplicitInputs.LocalClusterPairLowerBoundData
          ((cluster_witness n q hq).cluster)
          (pair_cross n (arrangement n q hq)) i j hij
  region_increment :
    ∀ (n : Nat) (q : QuadVec n) (hq : q ∈ sortedQuadVecs n),
      StepwiseOrderedIncrementalPairRegionData n
        (P.region n (arrangement n q hq))
        (pair_cross n (arrangement n q hq))

namespace StepwisePairLocalKarlssonLowerBoundCertificate

/-- Assemble local monotone copy-pair certificates into the theorem-facing
monotone pairwise lower package. -/
noncomputable def toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwisePairLocalKarlssonLowerBoundCertificate P) :
    ExplicitInputs.PairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData
      P where
  arrangement := h.arrangement
  cluster_witness := h.cluster_witness
  pair_cross := h.pair_cross
  pair_cross_ge_cluster := by
    intro n q hq i j hij
    exact ExplicitInputs.pair_cross_ge_cluster_from_local
      (h.local_pair_cross_ge_cluster n q hq) i j hij
  region_increment := by
    intro n q hq
    exact (h.region_increment n q hq).toOrderedIncrementalPairRegionData

end StepwisePairLocalKarlssonLowerBoundCertificate

/-- One local upper pair certificate: it bundles the finite carrier
intersection witness, generic noncoincidence facts, and all close/intriguing
component-savings branches for a single unordered pair `i < j`. -/
structure LocalEuclideanUpperPairData
    {n : Nat} (A : PrimitiveGeometry.EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  carrier_crossing :
    PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij
  spheres_distinct :
    PrimitiveGeometry.euclideanSphere (A.lollipop i).center
        (A.lollipop i).radius ≠
      PrimitiveGeometry.euclideanSphere (A.lollipop j).center
        (A.lollipop j).radius
  rayLines_distinct :
    PrimitiveGeometry.euclideanRayLine (A.lollipop i) ≠
      PrimitiveGeometry.euclideanRayLine (A.lollipop j)
  close_savings :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
      PrimitiveGeometry.PairComponentSavings (A.lollipop i) (A.lollipop j) 5
  intriguing_savings :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavings (A.lollipop i) (A.lollipop j) 5
  close_intriguing_savings :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavings (A.lollipop i) (A.lollipop j) 4

namespace LocalEuclideanUpperPairData

/-- The local upper pair certificate proves the generic `<= 7` crossing bound
for its pair. -/
theorem generic_cross_le_seven
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij) :
    cross i j ≤ 7 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_seven
    D.carrier_crossing D.spheres_distinct D.rayLines_distinct

/-- On a close pair, the local upper pair certificate proves the `<= 5`
crossing bound consumed by the colored-Turan argument. -/
theorem close_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    cross i j ≤ 5 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.close_savings hclose)

/-- On an intriguing pair, the local upper pair certificate proves the `<= 5`
crossing bound consumed by the colored-Turan argument. -/
theorem intriguing_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 5 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.intriguing_savings hintriguing)

/-- On a pair that is both close and intriguing, the local upper pair
certificate proves the stronger `<= 4` crossing bound. -/
theorem close_intriguing_cross_le_four
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : LocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 4 :=
  PrimitiveGeometry.localPairCarrierCrossingData_cross_le_of_pairComponentSavings
    D.carrier_crossing (D.close_intriguing_savings hclose hintriguing)

end LocalEuclideanUpperPairData

/-- One local upper pair certificate whose close/intriguing savings are given
by named geometric route certificates rather than raw component-savings
objects. -/
structure RoutedLocalEuclideanUpperPairData
    {n : Nat} (A : PrimitiveGeometry.EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  carrier_crossing :
    PrimitiveGeometry.LocalPairCarrierCrossingData A cross i j hij
  spheres_distinct :
    PrimitiveGeometry.euclideanSphere (A.lollipop i).center
        (A.lollipop i).radius ≠
      PrimitiveGeometry.euclideanSphere (A.lollipop j).center
        (A.lollipop j).radius
  rayLines_distinct :
    PrimitiveGeometry.euclideanRayLine (A.lollipop i) ≠
      PrimitiveGeometry.euclideanRayLine (A.lollipop j)
  close_savings_route :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
      PrimitiveGeometry.PairComponentSavingsFiveRoute
        (A.lollipop i) (A.lollipop j)
  intriguing_savings_route :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavingsFiveRoute
        (A.lollipop i) (A.lollipop j)
  close_intriguing_savings_route :
    TheoremOneEndToEnd.CloseDirection.cyclicClose
      (fun k => A.normalizedDirection k) i j →
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k => A.center k) (fun k => A.radius k) i j →
      PrimitiveGeometry.PairComponentSavingsFourRoute
        (A.lollipop i) (A.lollipop j)

namespace RoutedLocalEuclideanUpperPairData

/-- Promote a primitive routed local pair-data object to the first-principles
local upper pair record. -/
noncomputable def ofPrimitiveRoutedLocalPairData
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : PrimitiveGeometry.PrimitiveRoutedLocalPairData A cross i j hij) :
    RoutedLocalEuclideanUpperPairData A cross i j hij where
  carrier_crossing := D.carrier_crossing
  spheres_distinct := D.spheres_distinct
  rayLines_distinct := D.rayLines_distinct
  close_savings_route := D.close_savings_route
  intriguing_savings_route := D.intriguing_savings_route
  close_intriguing_savings_route := D.close_intriguing_savings_route

/-- Convert routed upper pair data into the component-savings pair data used
by the current theorem stack. -/
noncomputable def toLocalEuclideanUpperPairData
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij) :
    LocalEuclideanUpperPairData A cross i j hij where
  carrier_crossing := D.carrier_crossing
  spheres_distinct := D.spheres_distinct
  rayLines_distinct := D.rayLines_distinct
  close_savings := by
    intro hclose
    exact (D.close_savings_route hclose).toPairComponentSavings
  intriguing_savings := by
    intro hintriguing
    exact (D.intriguing_savings_route hintriguing).toPairComponentSavings
  close_intriguing_savings := by
    intro hclose hintriguing
    exact (D.close_intriguing_savings_route hclose hintriguing).toPairComponentSavings

/-- The routed local upper pair certificate proves the generic `<= 7`
crossing bound for its pair. -/
theorem generic_cross_le_seven
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij) :
    cross i j ≤ 7 :=
  D.toLocalEuclideanUpperPairData.generic_cross_le_seven

/-- On a close pair, routed local upper data prove the `<= 5` crossing bound. -/
theorem close_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    cross i j ≤ 5 :=
  D.toLocalEuclideanUpperPairData.close_cross_le_five hclose

/-- On an intriguing pair, routed local upper data prove the `<= 5` crossing
bound. -/
theorem intriguing_cross_le_five
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 5 :=
  D.toLocalEuclideanUpperPairData.intriguing_cross_le_five hintriguing

/-- On a pair that is both close and intriguing, routed local upper data prove
the stronger `<= 4` crossing bound. -/
theorem close_intriguing_cross_le_four
    {n : Nat} {A : PrimitiveGeometry.EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat} {i j : Fin n} {hij : i < j}
    (D : RoutedLocalEuclideanUpperPairData A cross i j hij)
    (hclose :
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j)
    (hintriguing :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => A.center k) (fun k => A.radius k) i j) :
    cross i j ≤ 4 :=
  D.toLocalEuclideanUpperPairData.close_intriguing_cross_le_four
    hclose hintriguing

end RoutedLocalEuclideanUpperPairData

/-- Local upper Euclidean certificate.

This is the version closest to a first-principles coordinate calculation:
for each concrete arrangement and each local pair `i < j`, one supplies the
finite carrier-intersection set for that pair only.  Lean assembles these
local certificates into the global pairwise crossing table expected by the
theorem stack. -/
structure LocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      PrimitiveGeometry.LocalPairCarrierCrossingData
        (arrangement n A) (cross n A) i j hij
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop j)
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace LocalEuclideanUpperCertificate

/-- Assemble local one-pair carrier certificates into the global upper
certificate used by `Boundary.lean`. -/
noncomputable def toEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalEuclideanUpperCertificate P) :
    EuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  pairwise_crossings := by
    intro n A
    exact PrimitiveGeometry.PairwiseCarrierCrossingData.ofLocal
      (h.local_pairwise_crossings n A)
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := h.close_savings
  intriguing_savings := h.intriguing_savings
  close_intriguing_savings := h.close_intriguing_savings
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Local upper certificates supply the local finite carrier-intersection
obligations directly. -/
def provided_local_finite_carrier_intersections
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalEuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      PrimitiveGeometry.LocalPairCarrierCrossingData
        (h.arrangement n A) (h.cross n A) i j hij :=
  h.local_pairwise_crossings

/-- Local upper certificates also provide the assembled global crossing data. -/
noncomputable def provided_assembled_finite_carrier_intersections
    {P : TheoremOne.ProblemFamily.{u}}
    (h : LocalEuclideanUpperCertificate P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PrimitiveGeometry.PairwiseCarrierCrossingData
        (h.arrangement n A) (h.cross n A) :=
  h.toEuclideanUpperCertificate.pairwise_crossings

end LocalEuclideanUpperCertificate

/-- Local upper Euclidean certificate whose ordered region recurrence is also
split into local insertion-step certificates. -/
structure StepwiseLocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      PrimitiveGeometry.LocalPairCarrierCrossingData
        (arrangement n A) (cross n A) i j hij
  spheres_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop i).center
          ((arrangement n A).lollipop i).radius ≠
        PrimitiveGeometry.euclideanSphere ((arrangement n A).lollipop j).center
          ((arrangement n A).lollipop j).radius
  rayLines_distinct :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop i) ≠
        PrimitiveGeometry.euclideanRayLine ((arrangement n A).lollipop j)
  close_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 5
  close_intriguing_savings :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      TheoremOneEndToEnd.CloseDirection.cyclicClose
        (fun k => (arrangement n A).normalizedDirection k) i j →
      TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
        (fun k => (arrangement n A).center k)
        (fun k => (arrangement n A).radius k) i j →
        PrimitiveGeometry.PairComponentSavings ((arrangement n A).lollipop i)
          ((arrangement n A).lollipop j) 4
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace StepwiseLocalEuclideanUpperCertificate

/-- Assemble stepwise upper-region data into the local upper certificate used
by the theorem stack. -/
noncomputable def toLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseLocalEuclideanUpperCertificate P) :
    LocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  local_pairwise_crossings := h.local_pairwise_crossings
  spheres_distinct := h.spheres_distinct
  rayLines_distinct := h.rayLines_distinct
  close_savings := h.close_savings
  intriguing_savings := h.intriguing_savings
  close_intriguing_savings := h.close_intriguing_savings
  region_increment := by
    intro n A
    exact (h.region_increment n A).toOrderedIncrementalPairRegionData
  radial_outward := h.radial_outward

/-- Assemble stepwise local upper data into the non-radial component-savings
upper package used by monotone lower theorem endpoints. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : StepwiseLocalEuclideanUpperCertificate P) :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toLocalEuclideanUpperCertificate
    |>.toEuclideanUpperCertificate
    |>.toComponentSavingsUpperGeometryData

end StepwiseLocalEuclideanUpperCertificate

/-- Upper certificate where every unordered pair carries one local bundle of
carrier-crossing, genericity, and close/intriguing component-savings data, and
the ordered region recurrence is supplied step by step. -/
structure PairStepwiseLocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  local_pair_data :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      LocalEuclideanUpperPairData (arrangement n A) (cross n A) i j hij
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace PairStepwiseLocalEuclideanUpperCertificate

/-- Assemble pair-local upper data into the stepwise local upper certificate
used by the theorem stack. -/
noncomputable def toStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairStepwiseLocalEuclideanUpperCertificate P) :
    StepwiseLocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  local_pairwise_crossings := by
    intro n A i j hij
    exact (h.local_pair_data n A i j hij).carrier_crossing
  spheres_distinct := by
    intro n A i j hij
    exact (h.local_pair_data n A i j hij).spheres_distinct
  rayLines_distinct := by
    intro n A i j hij
    exact (h.local_pair_data n A i j hij).rayLines_distinct
  close_savings := by
    intro n A i j hij hclose
    exact (h.local_pair_data n A i j hij).close_savings hclose
  intriguing_savings := by
    intro n A i j hij hintriguing
    exact (h.local_pair_data n A i j hij).intriguing_savings hintriguing
  close_intriguing_savings := by
    intro n A i j hij hclose hintriguing
    exact (h.local_pair_data n A i j hij).close_intriguing_savings
      hclose hintriguing
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Assemble pair-local upper data directly into the local upper certificate
with bundled ordered region recurrences. -/
noncomputable def toLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairStepwiseLocalEuclideanUpperCertificate P) :
    LocalEuclideanUpperCertificate P :=
  h.toStepwiseLocalEuclideanUpperCertificate.toLocalEuclideanUpperCertificate

/-- Assemble pair-local upper data into the component-savings upper package
used by monotone lower theorem endpoints. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PairStepwiseLocalEuclideanUpperCertificate P) :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toStepwiseLocalEuclideanUpperCertificate.toComponentSavingsUpperGeometryData

end PairStepwiseLocalEuclideanUpperCertificate

/-- Route-based upper certificate: every unordered upper pair supplies one
local carrier/genericity bundle, and close/intriguing savings are supplied via
named geometric route constructors. -/
structure RoutedPairStepwiseLocalEuclideanUpperCertificate
    (P : TheoremOne.ProblemFamily.{u}) : Type u where
  arrangement :
    ∀ n : Nat, P.Arrangement n →
      PrimitiveGeometry.EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  routed_local_pair_data :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, ∀ hij : i < j,
      RoutedLocalEuclideanUpperPairData (arrangement n A) (cross n A) i j hij
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      StepwiseOrderedIncrementalPairRegionData n (P.region n A) (cross n A)
  radial_outward :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      ((arrangement n A).lollipop i).IsRadialOutward

namespace RoutedPairStepwiseLocalEuclideanUpperCertificate

/-- Assemble routed upper savings data into the all-pair local upper
certificate used by the theorem stack. -/
noncomputable def toPairStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedPairStepwiseLocalEuclideanUpperCertificate P) :
    PairStepwiseLocalEuclideanUpperCertificate P where
  arrangement := h.arrangement
  cross := h.cross
  local_pair_data := by
    intro n A i j hij
    exact (h.routed_local_pair_data n A i j hij).toLocalEuclideanUpperPairData
  region_increment := h.region_increment
  radial_outward := h.radial_outward

/-- Assemble routed upper savings data directly into the stepwise local upper
certificate. -/
noncomputable def toStepwiseLocalEuclideanUpperCertificate
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedPairStepwiseLocalEuclideanUpperCertificate P) :
    StepwiseLocalEuclideanUpperCertificate P :=
  h.toPairStepwiseLocalEuclideanUpperCertificate
    |>.toStepwiseLocalEuclideanUpperCertificate

/-- Assemble routed upper data into the component-savings upper package used
by monotone lower theorem endpoints. -/
noncomputable def toComponentSavingsUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : RoutedPairStepwiseLocalEuclideanUpperCertificate P) :
    PrimitiveGeometry.PrimitiveCarrierComponentSavingsUpperGeometryData P :=
  h.toStepwiseLocalEuclideanUpperCertificate.toComponentSavingsUpperGeometryData

end RoutedPairStepwiseLocalEuclideanUpperCertificate

/-- The complete local first-principles boundary for manuscript Theorem 1.

Compared with `TheoremOneCertificates`, this asks for local one-pair upper
carrier-intersection certificates, then lets Lean assemble the global upper
certificate. -/
structure LocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : LocalEuclideanUpperCertificate P.toProblemFamily
  lower : KarlssonLowerCertificate P.toProblemFamily

namespace LocalTheoremOneCertificates

/-- Convert the local first-principles boundary to the theorem-facing boundary
by assembling the upper pairwise carrier-crossing data. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : LocalTheoremOneCertificates P) :
    TheoremOneCertificates P where
  upper := h.upper.toEuclideanUpperCertificate
  lower := h.lower

end LocalTheoremOneCertificates

/-- Fully local first-principles boundary: local one-pair upper carrier
certificates and a six-entry symmetric Karlsson base lower certificate. -/
structure FullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : LocalEuclideanUpperCertificate P.toProblemFamily
  lower : LocalKarlssonLowerCertificate P.toProblemFamily

namespace FullyLocalTheoremOneCertificates

/-- Convert the fully local boundary into the local-upper/theorem-facing-lower
boundary. -/
noncomputable def toLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : FullyLocalTheoremOneCertificates P) :
    LocalTheoremOneCertificates P where
  upper := h.upper
  lower :=
    localKarlssonLowerCertificate_toKarlssonLowerCertificate h.lower

/-- Convert the fully local boundary directly to the theorem-facing boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : FullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toLocalTheoremOneCertificates.toTheoremOneCertificates

end FullyLocalTheoremOneCertificates

/-- Fully stepwise local first-principles boundary: local one-pair carrier
certificates, local region-step certificates, and a six-entry symmetric
Karlsson lower base table. -/
structure StepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : StepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwiseLocalKarlssonLowerCertificate P.toProblemFamily

namespace StepwiseFullyLocalTheoremOneCertificates

/-- Assemble all stepwise local data into the fully local theorem boundary. -/
noncomputable def toFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : StepwiseFullyLocalTheoremOneCertificates P) :
    FullyLocalTheoremOneCertificates P where
  upper := h.upper.toLocalEuclideanUpperCertificate
  lower := h.lower.toLocalKarlssonLowerCertificate

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : StepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end StepwiseFullyLocalTheoremOneCertificates

/-- Strongest current local first-principles boundary: upper carrier
intersections are local per pair, lower blow-up values are local per copy pair,
and both upper/lower region recurrences are local per insertion step. -/
structure PairStepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : StepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwisePairLocalKarlssonLowerCertificate P.toProblemFamily

namespace PairStepwiseFullyLocalTheoremOneCertificates

/-- Assemble the strongest local boundary into the stepwise fully local
boundary with universal lower copy-pair values. -/
noncomputable def toStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PairStepwiseFullyLocalTheoremOneCertificates P) :
    StepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper
  lower := h.lower.toStepwiseLocalKarlssonLowerCertificate

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PairStepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toStepwiseFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end PairStepwiseFullyLocalTheoremOneCertificates

/-- Strongest current all-pair local first-principles boundary: each upper
unordered pair supplies one local carrier/genericity/savings bundle, each lower
copy pair supplies one local inherited-value certificate, and both region
recurrences are supplied step by step. -/
structure AllPairStepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : PairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwisePairLocalKarlssonLowerCertificate P.toProblemFamily

namespace AllPairStepwiseFullyLocalTheoremOneCertificates

/-- Assemble the all-pair local boundary into the previous stepwise local
boundary. -/
noncomputable def toPairStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : AllPairStepwiseFullyLocalTheoremOneCertificates P) :
    PairStepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper.toStepwiseLocalEuclideanUpperCertificate
  lower := h.lower

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : AllPairStepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toPairStepwiseFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end AllPairStepwiseFullyLocalTheoremOneCertificates

/-- Strongest current route-based local first-principles boundary: upper
close/intriguing savings are supplied by named geometric route constructors,
lower copy-pair values are local, and both region recurrences are stepwise. -/
structure RoutedAllPairStepwiseFullyLocalTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : RoutedPairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower : StepwisePairLocalKarlssonLowerCertificate P.toProblemFamily

namespace RoutedAllPairStepwiseFullyLocalTheoremOneCertificates

/-- Assemble the route-based boundary into the all-pair local boundary. -/
noncomputable def toAllPairStepwiseFullyLocalTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P) :
    AllPairStepwiseFullyLocalTheoremOneCertificates P where
  upper := h.upper.toPairStepwiseLocalEuclideanUpperCertificate
  lower := h.lower

/-- Convert directly to the theorem-facing first-principles boundary. -/
noncomputable def toTheoremOneCertificates
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P) :
    TheoremOneCertificates P :=
  h.toAllPairStepwiseFullyLocalTheoremOneCertificates.toTheoremOneCertificates

end RoutedAllPairStepwiseFullyLocalTheoremOneCertificates

/-- Pair-local upper boundary with monotone local lower pair inequalities.
This is the strongest lower-bound-facing local boundary: it avoids exact
copy-pair crossing classification while retaining stepwise region data. -/
structure PairStepwiseMonotoneLowerTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : PairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower :
    StepwisePairLocalKarlssonLowerBoundCertificate P.toProblemFamily

namespace PairStepwiseMonotoneLowerTheoremOneCertificates

/-- Convert the pair-local monotone first-principles boundary into the
formalized monotone pairwise lower subtheorem package. -/
noncomputable def toMonotonePairwiseLowerTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : PairStepwiseMonotoneLowerTheoremOneCertificates P) :
    FormalizedProof.MonotonePairwiseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper.toComponentSavingsUpperGeometryData
  lower_pairwise_bound :=
    h.lower
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end PairStepwiseMonotoneLowerTheoremOneCertificates

/-- Route-based upper boundary with monotone local lower pair inequalities. -/
structure RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u where
  upper : RoutedPairStepwiseLocalEuclideanUpperCertificate P.toProblemFamily
  lower :
    StepwisePairLocalKarlssonLowerBoundCertificate P.toProblemFamily

namespace RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates

/-- Convert routed upper data and monotone local lower data into the
formalized monotone pairwise lower subtheorem package. -/
noncomputable def toMonotonePairwiseLowerTheoremOneSubtheorems
    {P : TheoremOne.MaxProblemFamily.{u}}
    (h : RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates P) :
    FormalizedProof.MonotonePairwiseLowerTheoremOneSubtheorems P where
  upper_geometry := h.upper.toComponentSavingsUpperGeometryData
  lower_pairwise_bound :=
    h.lower
      |>.toPairwiseCardinalityClusteredKarlssonBlowUpIncrementalLowerBoundData

end RoutedAllPairStepwiseMonotoneLowerTheoremOneCertificates

/-- Manuscript Theorem 1 follows from route-based all-pair local
first-principles certificates. -/
theorem theorem_one_from_routed_all_pair_stepwise_fully_local_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P) :
    FormalizedProof.FinalTheoremOneStatement P :=
  theorem_one_from_first_principles_boundary P h.toTheoremOneCertificates

/-- Single-size form of Theorem 1 from route-based all-pair local
first-principles certificates. -/
theorem theorem_one_at_from_routed_all_pair_stepwise_fully_local_first_principles_boundary
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : RoutedAllPairStepwiseFullyLocalTheoremOneCertificates P)
    (n : Nat) :
    FormalizedProof.FinalTheoremOneAtStatement P n :=
  theorem_one_at_from_first_principles_boundary
    P h.toTheoremOneCertificates n

end FirstPrinciples
end TheoremOneManuscript
end Lollipop
