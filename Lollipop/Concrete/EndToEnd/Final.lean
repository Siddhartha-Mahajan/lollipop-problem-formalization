import Lollipop.Concrete.EndToEnd.Lower

/-!
# Concrete endpoint from explicit remaining ports

This is the intended concrete theorem shape.  It has no
`GeometryCertificates` argument and is stated directly for Euclidean lollipops
and connected components of their complement.  At this stage it still takes an
explicit package of concrete geometry/topology theorems that remain to be
proved.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

/-- The remaining concrete theorem package needed by the current endpoint. -/
structure EndToEndPorts : Prop where
  upper : UpperPorts
  lower : LowerPorts

/-- Build the endpoint ports from the sharper fan-topology package and the
separate lower genericity-avoidance theorem. -/
def EndToEndPorts.ofFanTopology
    (topology : InsertionFan.FanTopologyPorts)
    (genericity : ∀ n : ℕ,
      Lower.GenericityPort.ChamberGenericityAvoidance n) :
    EndToEndPorts where
  upper := UpperPorts.ofFanTopology topology
  lower := LowerPorts.ofFanTopology topology genericity

/-- Maximum number of complementary regions for `n` concrete Euclidean
lollipops. -/
theorem lollipopMaximum (ports : EndToEndPorts) (n : ℕ) :
    LollipopMaximumStatement n :=
  lollipopMaximum_of_upper_lower
    (regionUpper ports.upper n)
    (regionLower ports.lower n)

/-- All-size version. -/
theorem lollipopMaximum_all (ports : EndToEndPorts) :
    ∀ n : ℕ, LollipopMaximumStatement n :=
  lollipopMaximum_all_of_upper_lower
    (regionUpper_all ports.upper)
    (regionLower_all ports.lower)

/-- Expanded theorem statement, convenient for downstream use. -/
theorem lollipopMaximum_expanded (ports : EndToEndPorts) (n : ℕ) :
    IsGreatest
      (Set.range (fun A : Arrangement n => (regionCount A : ℚ)))
      (4 * ((n.choose 2 : ℕ) : ℚ) +
        TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1) := by
  simpa [LollipopMaximumStatement, regionCountRat, candidate] using
    lollipopMaximum ports n

end EndToEnd
end Concrete
end Lollipop
