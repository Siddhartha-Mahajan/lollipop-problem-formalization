import Lollipop.Concrete.EndToEnd.PairGeometry
import Mathlib.Tactic

/-!
# Concrete upper-bound boundary

The concrete upper theorem is the part of the manuscript that turns the
arbitrary-arrangement region inequality, pair-excess savings, close-pair
forcing, intriguing-pair forcing, and the colored Turan backend into

`regionCountRat A ≤ candidate n`.

Earlier versions of this file contained an unfinished proof script with
references to unavailable bridge lemmas.  This file records the consumed upper
theorem as a concrete target.  It is not an abstract `GeometryCertificates`
argument: the statement quantifies directly over concrete Euclidean
arrangements and their connected-component region count.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

/-- Remaining concrete upper-bound theorem package. -/
structure UpperPorts : Prop where
  regionCountRat_le_candidate :
    ∀ {n : ℕ} (A : Arrangement n), regionCountRat A ≤ candidate n

/-- Upper bound for one concrete arrangement. -/
theorem regionCountRat_le_candidate (ports : UpperPorts)
    {n : ℕ} (A : Arrangement n) :
    regionCountRat A ≤ candidate n :=
  ports.regionCountRat_le_candidate A

/-- All-size concrete upper theorem. -/
theorem regionUpper (ports : UpperPorts) (n : ℕ) : RegionUpperStatement n :=
  fun A => regionCountRat_le_candidate ports A

theorem regionUpper_all (ports : UpperPorts) :
    ∀ n : ℕ, RegionUpperStatement n :=
  regionUpper ports

end EndToEnd
end Concrete
end Lollipop
