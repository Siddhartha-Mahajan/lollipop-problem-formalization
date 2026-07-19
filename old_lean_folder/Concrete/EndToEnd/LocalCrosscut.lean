import old_lean_folder.Concrete.EndToEnd.ArcClosedCurve
import old_lean_folder.Concrete.EndToEnd.JordanClassifier
import old_lean_folder.Concrete.EndToEnd.LocalFiltration

/-!
# Local crosscut insertion steps

This file packages the checked Jordan-side classifier as localized filtration
step data.  It does not yet construct the geometric crosscut for a lollipop
edge.  Instead, it fixes the exact target for that construction:

* produce a simple closed curve `J` inside the one-edge extension;
* prove equal Jordan side gives an avoiding simple arc in the enlarged
  complement;
* in the exact/generic case, prove that both Jordan sides occur.

Those three geometric facts are precisely what is now needed to obtain the
one-step localized filtration objects consumed by the insertion topology
pipeline.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace LocalCrosscut

open Set Function

/-- Bounded localized edge-step data from a Jordan crosscut classifier. -/
def localizedEdgeStepOfJordanCrosscut
    {C E J : Set Point}
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    LocalFiltration.LocalizedEdgeStep C E where
  active := active
  localized := hloc
  activeClassifier := fun a =>
    JordanClassifier.sideOfComponent hJK hJ a.1
  active_injective :=
    JordanClassifier.activeSide_injective_of_arcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active hlift

/-- Exact localized edge-step data from a Jordan crosscut classifier. -/
def localizedExactEdgeStepOfJordanCrosscut
    {C E J : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active)
    (hside : JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    LocalFiltration.LocalizedExactEdgeStep L C E where
  old_closed := hCclosed
  edge_subset_carrier := hE
  active := active
  localized := hloc
  activeClassifier := fun a =>
    JordanClassifier.sideOfComponent hJK hJ a.1
  active_injective :=
    JordanClassifier.activeSide_injective_of_arcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active hlift
  active_surjective := hside

/-- Bounded localized edge-step data when the Jordan curve is supplied as the
union of two simple arcs in the one-edge extension. -/
def localizedEdgeStepOfTwoArcCrosscut
    {C E A B : Set Point} {x z : Point}
    (hAext : A ⊆ LocalInsertion.carrierExtension C E)
    (hBext : B ⊆ LocalInsertion.carrierExtension C E)
    (hA : IsSimpleArcEnd A x z) (hB : IsSimpleArcEnd B x z)
    (hxz : x ≠ z) (hinter : A ∩ B ⊆ {x, z})
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E)
      (union_subset hAext hBext)
      (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs
        hA hB hxz hinter)
      active) :
    LocalFiltration.LocalizedEdgeStep C E :=
  localizedEdgeStepOfJordanCrosscut
    (union_subset hAext hBext)
    (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs hA hB hxz hinter)
    active hloc hlift

/-- Exact localized edge-step data when the Jordan curve is supplied as the
union of two simple arcs in the one-edge extension. -/
def localizedExactEdgeStepOfTwoArcCrosscut
    {C E A B : Set Point} {x z : Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (hAext : A ⊆ LocalInsertion.carrierExtension C E)
    (hBext : B ⊆ LocalInsertion.carrierExtension C E)
    (hA : IsSimpleArcEnd A x z) (hB : IsSimpleArcEnd B x z)
    (hxz : x ≠ z) (hinter : A ∩ B ⊆ {x, z})
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E)
      (union_subset hAext hBext)
      (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs
        hA hB hxz hinter)
      active)
    (hside : JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E)
      (union_subset hAext hBext)
      (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs
        hA hB hxz hinter)
      active) :
    LocalFiltration.LocalizedExactEdgeStep L C E :=
  localizedExactEdgeStepOfJordanCrosscut hCclosed L hE
    (union_subset hAext hBext)
    (ArcClosedCurve.isSimpleClosedCurve_union_of_two_arcs hA hB hxz hinter)
    active hloc hlift hside

/-- One-step bounded localized filtration from Jordan crosscut data. -/
def localizedEdgeFiltrationOfJordanCrosscut
    {C E J : Set Point}
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    LocalFiltration.LocalizedEdgeFiltration 1 C
      (LocalInsertion.carrierExtension C E) := by
  simpa using
    LocalFiltration.LocalizedEdgeFiltration.snoc
      (LocalFiltration.LocalizedEdgeFiltration.nil C)
      E
      (localizedEdgeStepOfJordanCrosscut hJK hJ active hloc hlift)

/-- One-step exact localized filtration from Jordan crosscut data. -/
def localizedExactEdgeFiltrationOfJordanCrosscut
    {C E J : Set Point} (hCclosed : IsClosed C)
    (L : Lollipop) (hE : E ⊆ L.carrier)
    (hJK : J ⊆ LocalInsertion.carrierExtension C E)
    (hJ : IsSimpleClosedCurve J)
    (active : ConnectedComponents (Cᶜ : Set Point))
    (hloc : LocalInsertion.EdgeLocalized C E active)
    (hlift : JordanClassifier.ActiveSideArcLifting
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active)
    (hside : JordanClassifier.ActiveSideSurjective
      (LocalInsertion.old_subset_carrierExtension C E) hJK hJ active) :
    LocalFiltration.LocalizedExactEdgeFiltration L 1 C
      (LocalInsertion.carrierExtension C E) := by
  simpa using
    LocalFiltration.LocalizedExactEdgeFiltration.snoc
      (LocalFiltration.LocalizedExactEdgeFiltration.nil (L := L) C)
      E
      (localizedExactEdgeStepOfJordanCrosscut hCclosed L hE hJK hJ active
        hloc hlift hside)

end LocalCrosscut
end EndToEnd
end Concrete
end Lollipop
