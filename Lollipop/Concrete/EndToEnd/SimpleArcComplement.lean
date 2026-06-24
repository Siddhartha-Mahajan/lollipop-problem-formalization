import Lollipop.Concrete.EndToEnd.JordanBridge
import JordanCurveTheorem.SectionAA_RectagApprox
import Mathlib.Tactic

/-!
# Complements of simple arcs

The localized insertion route repeatedly needs the elementary planar fact
that inserting a compact simple arc by itself does not disconnect the plane.
The vendored Jordan development proves the stronger arc-avoidance theorem
`simple_arc_conn_complement`; this file exposes the connected-component
consequences in the concrete endpoint namespace.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace SimpleArcComplement

open Set
open JordanCurveTheorem

/-- The complement of a simple arc in the plane is connected. -/
theorem isConnected_compl_simpleArc {C : Set Point}
    (hC : IsSimpleArc C) : IsConnected Cᶜ := by
  have hcompact : IsCompact C := isSimpleArc_compact hC
  have hnonempty : Cᶜ.Nonempty := by
    have hne : C ≠ Set.univ := hcompact.ne_univ
    by_contra hempty
    apply hne
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      by_contra hxC
      have hxCompl : x ∈ Cᶜ := hxC
      exact hempty ⟨x, hxCompl⟩
  refine ⟨hnonempty, ?_⟩
  rw [isPreconnected_iff_subset_of_disjoint]
  intro U V hUo hVo hsub hUV
  by_contra hneither
  have hnotU : ¬ Cᶜ ⊆ U := fun hCU => hneither (Or.inl hCU)
  have hnotV : ¬ Cᶜ ⊆ V := fun hCV => hneither (Or.inr hCV)
  rw [Set.not_subset] at hnotU hnotV
  obtain ⟨p, hpC, hpU⟩ := hnotU
  obtain ⟨q, hqC, hqV⟩ := hnotV
  have hpq : p ≠ q := by
    intro hpq
    subst q
    rcases hsub hpC with hpU' | hpV'
    · exact hpU hpU'
    · exact hqV hpV'
  obtain ⟨A, hA, hCA⟩ := simple_arc_conn_complement hC hpC hqC hpq
  have hAsub : A ⊆ Cᶜ := by
    intro x hxA hxC
    exact Set.disjoint_left.mp hCA hxC hxA
  have hAconn : IsPreconnected A :=
    (isSimpleArc_isConnected (isSimpleArcEnd_isSimpleArc hA)).isPreconnected
  have hpA : p ∈ A := isSimpleArcEnd_mem_left hA
  have hqA : q ∈ A := isSimpleArcEnd_mem_right hA
  have hcoverA : A ⊆ U ∪ V := hAsub.trans hsub
  have hdisjA : A ∩ (U ∩ V) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx' : x ∈ Cᶜ ∩ (U ∩ V) := ⟨hAsub hx.1, hx.2⟩
    rw [hUV] at hx'
    exact hx'
  rcases (isPreconnected_iff_subset_of_disjoint.mp hAconn)
      U V hUo hVo hcoverA hdisjA with hAU | hAV
  · exact hpU (hAU hpA)
  · exact hqV (hAV hqA)

/-- A simple-arc complement has exactly one connected component. -/
theorem componentCount_compl_simpleArc_eq_one {C : Set Point}
    (hC : IsSimpleArc C) :
    componentCount (Cᶜ) = 1 := by
  have hconn : IsConnected Cᶜ := isConnected_compl_simpleArc hC
  letI : ConnectedSpace (Cᶜ : Set Point) := Subtype.connectedSpace hconn
  simp [componentCount]

/-- The connected-component quotient of a simple-arc complement is finite. -/
theorem finite_connectedComponents_compl_simpleArc {C : Set Point}
    (hC : IsSimpleArc C) :
    Finite (ConnectedComponents (Cᶜ : Set Point)) := by
  have hconn : IsConnected Cᶜ := isConnected_compl_simpleArc hC
  letI : ConnectedSpace (Cᶜ : Set Point) := Subtype.connectedSpace hconn
  infer_instance

end SimpleArcComplement
end EndToEnd
end Concrete
end Lollipop
