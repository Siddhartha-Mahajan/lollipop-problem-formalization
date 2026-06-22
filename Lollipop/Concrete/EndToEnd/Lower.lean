import Lollipop.Concrete.EndToEnd.Upper
import Lollipop.Concrete.EndToEnd.Lower.BlowUp
import Lollipop.Internal.Lower

/-!
# Concrete lower theorem from explicit remaining ports

The geometric blow-up is converted to the repository's already proved lower
algebra, which selects an admissible quadruple attaining `concreteS n`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

/-- Bridge between the concrete endpoint's displayed candidate and the
repository's internal lower-construction candidate. -/
theorem candidate_eq_candidateRegionsChoose (n : ℕ) :
    candidate n = candidateRegionsChoose n := by
  unfold candidate candidateRegionsChoose
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]

/-- The remaining concrete theorem package needed by the lower construction.

These are not caller-facing certificates for an abstract problem family.  They
are the concrete geometry/topology theorems still to prove: genericity
avoidance, similarity invariance, and planar topology. -/
structure LowerPorts : Prop where
  blowUp : Lower.BlowUp.BlowUpPorts
  topology : PlanarTopologyPorts
  genericity : ∀ n : ℕ, Lower.GenericityPort.GenericityAvoidance n

/-- Every admissible quadruple has a concrete lollipop realization with its
exact lower region count. -/
theorem lowerRealization_all (ports : LowerPorts) (n : ℕ) :
    LowerRealization (Arrangement n) regionCountRat n :=
  Lower.BlowUp.lowerRealization ports.blowUp ports.topology.generic_region_eq
    ports.genericity n

/-- The displayed candidate is attained for every size. -/
theorem regionLower (ports : LowerPorts) (n : ℕ) : RegionLowerStatement n := by
  rcases exists_region_eq_candidate_of_lowerRealization
    (lowerRealization_all ports n) with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rw [hA, candidate_eq_candidateRegionsChoose,
    candidateRegionsChoose_eq_candidateRegions]

/-- All-size lower theorem. -/
theorem regionLower_all (ports : LowerPorts) :
    ∀ n : ℕ, RegionLowerStatement n :=
  regionLower ports

end EndToEnd
end Concrete
end Lollipop
