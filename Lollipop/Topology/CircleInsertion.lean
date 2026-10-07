import Lollipop.Lemma_8_5.Proof
import Lollipop.Topology.CircleJordan
import Lollipop.Topology.JordanClassifier
import Mathlib.Tactic

/-!
# Circle insertion topology

This file proves the base active-side lifting lemma for inserting a Jordan
circle into the empty carrier.  It is the simplest instance of the local
crosscut obligation: when the enlarged carrier is the Jordan curve itself,
equal Jordan side is exactly equality of complement components, so the
checked simple-arc characterization of closed-set components supplies the
avoiding arc.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace CircleInsertion

open Set

/-- Empty set inclusion into any carrier. -/
theorem empty_subset (K : Set Point) : (∅ : Set Point) ⊆ K := by
  intro x hx
  exact False.elim hx

/-- A simple closed curve is closed, proved directly from its compact
parametrization. -/
theorem isClosed_of_isSimpleClosedCurve
    {J : Set Point} (hJ : IsSimpleClosedCurve J) : IsClosed J := by
  obtain ⟨f, rfl, hfcont, _hfinj, _hperiod⟩ := hJ
  exact (isCompact_Icc.image_of_continuousOn hfcont.continuousOn).isClosed

/-- For a simple closed curve inserted over the empty old carrier, equal
Jordan side gives an avoiding simple arc in the curve complement. -/
theorem activeSideArcLifting_empty_self
    {J : Set Point} (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (((∅ : Set Point)ᶜ) : Set Point)) :
    JordanClassifier.ActiveSideArcLifting
      (empty_subset J) (Subset.rfl : J ⊆ J) hJ active := by
  intro x y _hxold _hyold hside hxy
  have hcomp :
      ConnectedComponents.mk x = ConnectedComponents.mk y := by
    apply (JordanClassifier.jordanComplementComponentsEquivBool hJ).injective
    apply JordanClassifier.boolToFin2_injective
    simpa [JordanClassifier.sideOfComponent, ComponentFibers.inclusionMap,
      ComponentFibers.inclusion, ComponentSurjectivity.complementSubset]
      using hside
  exact JordanBridge.exists_simpleArcEnd_disjoint_of_connectedComponents_mk_eq
    (isClosed_of_isSimpleClosedCurve hJ) x y hcomp hxy

/-- Concrete lollipop-circle version of the empty-carrier active-side lifting
lemma. -/
theorem activeSideArcLifting_empty_circle
    (L : Lollipop)
    (active : ConnectedComponents (((∅ : Set Point)ᶜ) : Set Point)) :
    JordanClassifier.ActiveSideArcLifting
      (empty_subset L.circle) (Subset.rfl : L.circle ⊆ L.circle)
      (CircleJordan.isSimpleClosedCurve_circle L) active :=
  activeSideArcLifting_empty_self
    (CircleJordan.isSimpleClosedCurve_circle L) active

end CircleInsertion
end EndToEnd
end Concrete
end Lollipop
