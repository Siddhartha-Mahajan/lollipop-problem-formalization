import Lollipop.Concrete.EndToEnd.PairGeometry
import Lollipop.Internal.ColoredTuran.GeometricReduction
import Mathlib.Tactic

/-!
# Concrete upper-bound assembly

The concrete upper theorem turns the arbitrary-arrangement region inequality,
pair-excess savings, close-pair forcing, intriguing-pair forcing, and the
colored Turan backend into

`regionCountRat A ≤ candidate n`.

The colored Turan backend and the close-pair forcing are proved in Lean.  The
remaining upper inputs are explicit concrete theorem packages: planar topology,
close/intriguing pair savings, and the narrow five-circle intriguing forcing
for the manuscript's concrete `Intriguing` relation.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

/-- Bridge between the concrete endpoint's displayed candidate and the
repository's internal candidate. -/
private theorem candidate_eq_candidateRegionsChoose_upper (n : ℕ) :
    candidate n = candidateRegionsChoose n := by
  unfold candidate candidateRegionsChoose
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]

/-- Among any four concrete stem directions, some pair is close. -/
theorem close_pair_in_every_four {n : ℕ} (A : Arrangement n) :
    ∀ t : Finset (Fin n), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ PairGeometry.Close (A i) (A j) := by
  intro t ht
  rcases TheoremOneEndToEnd.CloseDirection.exists_cyclicClose_pair_of_card_four
      (direction01 A) ht
      (fun i hi => direction01_nonneg A i)
      (fun i hi => direction01_lt_one A i) with
    ⟨i, hi, j, hj, hij, hclose⟩
  refine ⟨i, hi, j, hj, hij, ?_⟩
  exact radial_dot_nonneg_of_cyclicClose hclose

/-- Remaining concrete upper-bound theorem package.

The universal `q ≤ 7` pair bound and four-direction close forcing are no
longer fields: they are proved as `PairGeometry.pairExcess_le_seven` and
`close_pair_in_every_four`. -/
structure UpperPorts : Prop where
  topology : PlanarTopologyPorts
  pairGeometry : PairGeometry.PairGeometryPorts
  intriguing_pair_in_every_five :
    ∀ {n : ℕ} (A : Arrangement n), ∀ t : Finset (Fin n), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ PairGeometry.Intriguing (A i) (A j)

/-- Concrete arrangement packaged in the geometric upper structure consumed by
the internal colored-Turan backend. -/
noncomputable def pairwiseGeometricLollipopUpper
    (ports : UpperPorts) {n : ℕ} (A : Arrangement n) :
    TheoremOneEndToEnd.PairwiseGeometricLollipopUpper where
  nNat := n
  crossings := regionCountRat A - (n : ℚ) - 1
  regions := regionCountRat A
  close := fun i j => PairGeometry.Close (A i) (A j)
  intriguing := fun i j => PairGeometry.Intriguing (A i) (A j)
  close_decidable := Classical.decRel _
  intriguing_decidable := Classical.decRel _
  close_symm := fun i j => PairGeometry.close_symm (A i) (A j)
  intriguing_symm := fun i j => PairGeometry.intriguing_symm (A i) (A j)
  cross := pairExcessTable A
  crossings_le_pairSum := by
    exact ports.topology.crossing_excess_le_pairSum A
  cross_le_general := by
    intro i j hij
    exact PairGeometry.pairExcess_le_seven (A i) (A j)
  cross_le_close := by
    intro i j hij hclose
    exact PairGeometry.pairExcess_le_five_of_close
      ports.pairGeometry hclose
  cross_le_intriguing := by
    intro i j hij hintr
    exact PairGeometry.pairExcess_le_five_of_intriguing
      ports.pairGeometry hintr
  cross_le_close_intriguing := by
    intro i j hij hclose hintr
    exact PairGeometry.pairExcess_le_four_of_close_intriguing
      ports.pairGeometry hclose hintr
  close_pair_in_every_four := close_pair_in_every_four A
  intriguing_pair_in_every_five := ports.intriguing_pair_in_every_five A
  regions_eq := by ring

/-- Upper bound for one concrete arrangement. -/
theorem regionCountRat_le_candidate (ports : UpperPorts)
    {n : ℕ} (A : Arrangement n) :
    regionCountRat A ≤ candidate n := by
  have hupper :=
    TheoremOneEndToEnd.pairwise_colored_graph_certified_lollipop_upper_bound_choose
      (pairwiseGeometricLollipopUpper ports A).toPairwiseColoredGraphCertifiedLollipopUpper
  dsimp [
    TheoremOneEndToEnd.PairwiseGeometricLollipopUpper.toPairwiseColoredGraphCertifiedLollipopUpper,
    pairwiseGeometricLollipopUpper] at hupper
  simpa [candidate_eq_candidateRegionsChoose_upper n] using hupper

/-- All-size concrete upper theorem. -/
theorem regionUpper (ports : UpperPorts) (n : ℕ) : RegionUpperStatement n :=
  fun A => regionCountRat_le_candidate ports A

theorem regionUpper_all (ports : UpperPorts) :
    ∀ n : ℕ, RegionUpperStatement n :=
  regionUpper ports

end EndToEnd
end Concrete
end Lollipop
