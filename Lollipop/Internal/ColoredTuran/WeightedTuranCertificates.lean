import Lollipop.Internal.ColoredTuran.PartitionCertificates
import Lollipop.Internal.ColoredTuran.WeightedTuranTheorem

/-!
End-to-end quotient certificates using the proved weighted Turan theorem.

This layer removes the numeric weighted-Turan complement-bound fields from the
partition-matrix quotient certificate.  Instead, the quotient carries two actual
blocker graphs.  If their off-diagonal complements are `K_4`-free and
`K_5`-free, Lean chooses the `3`- and `4`-partitions supplied by the weighted
Turan theorem and then reuses the existing partition-intersection/matrix
pipeline.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

/-- A quotient certificate in which the weighted Turan partitions are generated
from actual blocker graphs and clique-free complement hypotheses. -/
structure WeightedTuranCertifiedQuotient
    (Vertex : Type u) [Fintype Vertex] [DecidableEq Vertex]
    extends QuotientData where
  nNat : Nat
  n_eq : n = (nNat : Rat)
  x : Vertex → Nat
  total_weight : totalWeightNat x = nNat
  Q_eq : Q = weightSquareSumRat x
  Agraph : SimpleGraph Vertex
  Bgraph : SimpleGraph Vertex
  [decidable_A : DecidableRel Agraph.Adj]
  [decidable_B : DecidableRel Bgraph.Adj]
  aOnlyE_eq : aOnlyE = weightedEdgeMass x Agraph.Adj
  bOnlyD_eq : bOnlyD = weightedEdgeMass x Bgraph.Adj
  A_compl_cliqueFree : Agraphᶜ.CliqueFree 4
  B_compl_cliqueFree : Bgraphᶜ.CliqueFree 5
  sigma_eq :
    sigma =
      3 * weightedEdgeMass x (fun v w : Vertex => v ≠ w) -
        2 * weightedEdgeMass x Agraph.Adj - 2 * weightedEdgeMass x Bgraph.Adj

/-- Convert a weighted-Turan graph quotient into the existing
partition-generated quotient by choosing the two weighted Turan partitions. -/
noncomputable def WeightedTuranCertifiedQuotient.toPartitionMatrixCertifiedQuotient
    {Vertex : Type u} [Fintype Vertex] [DecidableEq Vertex]
    (q : WeightedTuranCertifiedQuotient Vertex) :
    PartitionMatrixCertifiedQuotient Vertex := by
  letI : DecidableRel q.Agraph.Adj := q.decidable_A
  letI : DecidableRel q.Bgraph.Adj := q.decidable_B
  have hAex :
      ∃ p3 : Vertex → Fin 3,
        orderedRelWeight q.x q.Agraphᶜ.Adj ≤
          (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p3 :=
    exists_partition_bound_of_cliqueFree q.x q.Agraphᶜ
      (r := 3) (by decide) q.A_compl_cliqueFree
  let p3 : Vertex → Fin 3 := Classical.choose hAex
  have hp3 :
      orderedRelWeight q.x q.Agraphᶜ.Adj ≤
        (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p3 :=
    Classical.choose_spec hAex
  have hBex :
      ∃ p4 : Vertex → Fin 4,
        orderedRelWeight q.x q.Bgraphᶜ.Adj ≤
          (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p4 :=
    exists_partition_bound_of_cliqueFree q.x q.Bgraphᶜ
      (r := 4) (by decide) q.B_compl_cliqueFree
  let p4 : Vertex → Fin 4 := Classical.choose hBex
  have hp4 :
      orderedRelWeight q.x q.Bgraphᶜ.Adj ≤
        (totalWeightNat q.x : Rat)^2 - partitionSquareWeight q.x p4 :=
    Classical.choose_spec hBex
  exact
    { n := q.n
      Q := q.Q
      aOnlyE := q.aOnlyE
      bOnlyD := q.bOnlyD
      sigma := q.sigma
      nNat := q.nNat
      n_eq := q.n_eq
      x := q.x
      p3 := p3
      p4 := p4
      total_weight := q.total_weight
      Q_eq := q.Q_eq
      A := q.Agraph.Adj
      B := q.Bgraph.Adj
      decidable_A := q.decidable_A
      decidable_B := q.decidable_B
      A_loopless := by
        intro v
        exact q.Agraph.loopless.irrefl v
      B_loopless := by
        intro v
        exact q.Bgraph.loopless.irrefl v
      aOnlyE_eq := q.aOnlyE_eq
      bOnlyD_eq := q.bOnlyD_eq
      A_complement_le_p3 := by
        have hle :=
          orderedRelWeight_le_of_imp q.x
            (fun v w : Vertex => v ≠ w ∧ ¬ q.Agraph.Adj v w)
            q.Agraphᶜ.Adj
            (by
              intro v w h
              exact (SimpleGraph.compl_adj q.Agraph v w).2 h)
        exact le_trans hle hp3
      B_complement_le_p4 := by
        have hle :=
          orderedRelWeight_le_of_imp q.x
            (fun v w : Vertex => v ≠ w ∧ ¬ q.Bgraph.Adj v w)
            q.Bgraphᶜ.Adj
            (by
              intro v w h
              exact (SimpleGraph.compl_adj q.Bgraph v w).2 h)
        exact le_trans hle hp4
      sigma_eq := q.sigma_eq }

/-- Colored-pair certificate whose quotient partitions are supplied by the
proved weighted Turan theorem. -/
structure WeightedTuranCertifiedColoredPair where
  nNat : Nat
  sigma : Rat
  Vertex : Type u
  [vertex_fintype : Fintype Vertex]
  [vertex_decidableEq : DecidableEq Vertex]
  quotient : WeightedTuranCertifiedQuotient Vertex
  quotient_nNat : quotient.nNat = nNat
  quotient_preserves_sigma : quotient.sigma ≥ sigma

/-- Forget the weighted-Turan graph hypotheses after Lean has chosen the
partitions and built the partition-matrix certificate. -/
noncomputable def WeightedTuranCertifiedColoredPair.toPartitionMatrixCertifiedColoredPair
    (p : WeightedTuranCertifiedColoredPair.{u}) :
    PartitionMatrixCertifiedColoredPair.{u} := by
  classical
  letI : Fintype p.Vertex := p.vertex_fintype
  letI : DecidableEq p.Vertex := p.vertex_decidableEq
  exact
    { nNat := p.nNat
      sigma := p.sigma
      Vertex := p.Vertex
      quotient := p.quotient.toPartitionMatrixCertifiedQuotient
      quotient_nNat := by
        simpa [WeightedTuranCertifiedQuotient.toPartitionMatrixCertifiedQuotient]
          using p.quotient_nNat
      quotient_preserves_sigma := by
        simpa [WeightedTuranCertifiedQuotient.toPartitionMatrixCertifiedQuotient]
          using p.quotient_preserves_sigma }

/-- Colored Turan bound from actual blocker graphs plus the proved weighted
Turan theorem, partition-intersection bookkeeping, and matrix theorem. -/
theorem weighted_turan_certified_colored_turan_bound
    (p : WeightedTuranCertifiedColoredPair.{u}) :
    p.sigma ≤ concreteS p.nNat := by
  exact partition_matrix_certified_colored_turan_bound
    p.toPartitionMatrixCertifiedColoredPair

/-- Pairwise lollipop upper certificate using weighted-Turan-generated blocker
partitions. -/
structure PairwiseWeightedTuranCertifiedLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  cross : Fin nNat → Fin nNat → Rat
  score : Fin nNat → Fin nNat → Rat
  pair : WeightedTuranCertifiedColoredPair.{u}
  pair_nNat : pair.nNat = nNat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  pointwise_crossing_bound :
    ∀ i j : Fin nNat, i < j → cross i j ≤ 4 + score i j
  score_sum_le_sigma : pairSum nNat score ≤ pair.sigma
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Convert the weighted-Turan-generated upper certificate into the existing
partition-matrix certificate. -/
noncomputable def PairwiseWeightedTuranCertifiedLollipopUpper.toPairwisePartitionMatrixCertifiedLollipopUpper
    (L : PairwiseWeightedTuranCertifiedLollipopUpper.{u}) :
    PairwisePartitionMatrixCertifiedLollipopUpper.{u} where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair := L.pair.toPartitionMatrixCertifiedColoredPair
  pair_nNat := L.pair_nNat
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := L.score_sum_le_sigma
  regions_eq := L.regions_eq

/-- End-to-end upper bound for one arrangement from actual blocker graphs and
the proved weighted Turan theorem. -/
theorem pairwise_weighted_turan_certified_lollipop_upper_bound_choose
    (L : PairwiseWeightedTuranCertifiedLollipopUpper.{u}) :
    L.regions ≤ candidateRegionsChoose L.nNat := by
  exact pairwise_partition_matrix_certified_lollipop_upper_bound_choose
    L.toPairwisePartitionMatrixCertifiedLollipopUpper

/-- Upper certificates for every arrangement where the weighted Turan
partitions are generated internally from clique-free blocker complements. -/
def PairwiseWeightedTuranUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseWeightedTuranCertifiedLollipopUpper.{u},
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert weighted-Turan-generated upper certificates into the existing
partition-matrix certificate family. -/
theorem pairwise_weighted_turan_upper_certificates_to_partition_matrix
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseWeightedTuranUpperCertificates P) :
    PairwisePartitionMatrixUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwisePartitionMatrixCertifiedLollipopUpper, hLn, hLreg⟩

/-- Upper-bound half of Theorem 1 from blocker graphs whose complements satisfy
the clique-free hypotheses required by weighted Turan. -/
theorem upper_bound_of_pairwise_weighted_turan_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseWeightedTuranUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_partition_matrix_certificates P
    (pairwise_weighted_turan_upper_certificates_to_partition_matrix hupper)

end TheoremOneEndToEnd
end Lollipop
