import Lollipop.Topology.PlanarPorts

/-!
# Concrete maximum theorem

Final assembly of the lollipop maximum theorem for concrete Euclidean lollipops
with no caller-supplied packages: the upper bound uses the proved topology
ports, the lower bound the proved chamber-genericity theorem and the blow-up
construction.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Final

/-- Upper endpoint ports, all proved. -/
def upperPorts : UpperPorts where
  topology := Topology.fanTopologyPorts

/-- Upper bound for every size. -/
theorem regionUpper_proved (n : ℕ) : RegionUpperStatement n :=
  regionUpper upperPorts n

/-- The displayed candidate equals the internal lower-construction candidate. -/
theorem candidate_eq_choose (n : ℕ) : candidate n = candidateRegionsChoose n := by
  unfold candidate candidateRegionsChoose
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]

/-- Lower bound for every size. -/
theorem regionLower_proved (n : ℕ) : RegionLowerStatement n := by
  rcases exists_region_eq_candidate_of_lowerRealization
    (Lower.BlowUp.lowerRealization
      Topology.planarTopologyPorts.generic_region_eq
      Genericity.chamberGenericityAvoidance_all n) with ⟨A, hA⟩
  refine ⟨A, ?_⟩
  rw [hA, candidate_eq_choose, candidateRegionsChoose_eq_candidateRegions]

/-- **Theorem 1.1 (concrete form).**  For every `n`, the maximum number of
complementary regions of `n` Euclidean lollipops is attained, and equals the
displayed candidate. -/
theorem lollipopMaximum (n : ℕ) : LollipopMaximumStatement n :=
  lollipopMaximum_of_upper_lower (regionUpper_proved n) (regionLower_proved n)

/-- Expanded form in terms of the manuscript formula `4 C(n,2) + S(n) + n + 1`. -/
theorem lollipopMaximum_expanded (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) +
        TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1) := by
  simpa [LollipopMaximumStatement, regionCountRat, candidate] using lollipopMaximum n

end Final
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
