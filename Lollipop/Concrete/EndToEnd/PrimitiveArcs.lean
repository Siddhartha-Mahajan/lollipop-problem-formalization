import Lollipop.Concrete.EndToEnd.SimpleArcComplement
import Lollipop.Concrete.Topology
import JordanCurveTheorem.SectionN_K33
import Mathlib.Tactic

/-!
# Primitive lollipop arcs

The finite-subdivision topology proof needs concrete carrier pieces packaged
as simple arcs.  This file starts with the algebraic part: finite subsegments
of a lollipop stem.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace PrimitiveArcs

open Set

/-- The finite stem subsegment between two stem parameters. -/
def stemSegment (L : Lollipop) (a b : ℝ) : Set Point :=
  segment ℝ (L.stemMap a) (L.stemMap b)

theorem stemMap_ne_of_ne (L : Lollipop) {a b : ℝ} (hab : a ≠ b) :
    L.stemMap a ≠ L.stemMap b := by
  intro h
  have hvec : a • L.radial = b • L.radial := by
    simpa [Lollipop.stemMap] using add_left_cancel h
  have hzero : (a - b) • L.radial = (0 : Point) := by
    simpa [sub_smul] using sub_eq_zero.mpr hvec
  rcases smul_eq_zero.mp hzero with hscalar | hradial
  · exact hab (sub_eq_zero.mp hscalar)
  · exact L.radial_ne_zero hradial

/-- A finite nondegenerate stem subsegment is a simple arc. -/
theorem isSimpleArcEnd_stemSegment
    (L : Lollipop) {a b : ℝ} (hab : a ≠ b) :
    IsSimpleArcEnd (stemSegment L a b) (L.stemMap a) (L.stemMap b) :=
  segment_isSimpleArcEnd (stemMap_ne_of_ne L hab)

/-- Stem subsegments whose endpoints are on the outward ray remain in the
stem. -/
theorem stemSegment_subset_stem
    (L : Lollipop) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    stemSegment L a b ⊆ L.stem := by
  intro z hz
  rw [stemSegment, mem_segment_iff_param] at hz
  rcases hz with ⟨t, ht0, ht1, rfl⟩
  refine ⟨t * a + (1 - t) * b, ?_, ?_⟩
  · have hta : t * 1 ≤ t * a :=
      mul_le_mul_of_nonneg_left ha ht0
    have htb : (1 - t) * 1 ≤ (1 - t) * b :=
      mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr ht1)
    nlinarith
  · simp [Lollipop.stemMap]
    module

/-- Stem subsegments whose endpoints are on the outward ray remain in the
full lollipop carrier. -/
theorem stemSegment_subset_carrier
    (L : Lollipop) {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    stemSegment L a b ⊆ L.carrier :=
  (stemSegment_subset_stem L ha hb).trans (Lollipop.stem_subset_carrier L)

/-- A nondegenerate finite stem subsegment has connected complement. -/
theorem componentCount_compl_stemSegment_eq_one
    (L : Lollipop) {a b : ℝ} (hab : a ≠ b) :
    componentCount ((stemSegment L a b)ᶜ) = 1 :=
  SimpleArcComplement.componentCount_compl_simpleArc_eq_one
    (isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_stemSegment L hab))

/-- Finiteness form for complements of finite stem subsegments. -/
theorem finite_connectedComponents_compl_stemSegment
    (L : Lollipop) {a b : ℝ} (hab : a ≠ b) :
    Finite (ConnectedComponents ((stemSegment L a b)ᶜ : Set Point)) :=
  SimpleArcComplement.finite_connectedComponents_compl_simpleArc
    (isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_stemSegment L hab))

end PrimitiveArcs
end EndToEnd
end Concrete
end Lollipop
