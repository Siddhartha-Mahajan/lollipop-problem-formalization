import Lollipop.Concrete.EndToEnd.CircleJordan
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

/-- A finite nondegenerate stem subsegment is connected. -/
theorem stemSegment_isConnected
    (L : Lollipop) {a b : ℝ} (hab : a ≠ b) :
    IsConnected (stemSegment L a b) :=
  isSimpleArc_isConnected
    (isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_stemSegment L hab))

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

/-- The circular subarc with normalized parameters in `[0,1]`. -/
def circleArc (L : Lollipop) (a b : ℝ) : Set Point :=
  CircleJordan.circleParam L '' Icc a b

/-- Reparametrize the circular subarc `[a,b]` by `[0,1]`. -/
def circleArcParam (L : Lollipop) (a b t : ℝ) : Point :=
  CircleJordan.circleParam L (a + t * (b - a))

theorem circleArc_eq_range_circleArcParam
    (L : Lollipop) {a b : ℝ} (hab : a < b) :
    circleArc L a b = circleArcParam L a b '' Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(s - a) / (b - a), ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hs.1)
        (sub_nonneg.mpr (le_of_lt hab))
    · exact div_le_one_of_le₀ (sub_le_sub_right hs.2 a)
        (sub_nonneg.mpr (le_of_lt hab))
    · unfold circleArcParam
      congr 1
      field_simp [sub_ne_zero.mpr hab.ne']
      ring
  · rintro ⟨t, ht, rfl⟩
    refine ⟨a + t * (b - a), ⟨?_, ?_⟩, rfl⟩
    · have hnonneg : 0 ≤ t * (b - a) :=
        mul_nonneg ht.1 (sub_nonneg.mpr (le_of_lt hab))
      nlinarith
    · have hmul : t * (b - a) ≤ 1 * (b - a) :=
        mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr (le_of_lt hab))
      nlinarith

theorem continuous_circleArcParam (L : Lollipop) (a b : ℝ) :
    Continuous (circleArcParam L a b) := by
  unfold circleArcParam
  exact (CircleJordan.continuous_circleParam L).comp
    (by fun_prop : Continuous fun t : ℝ => a + t * (b - a))

theorem circleArcParam_injOn
    (L : Lollipop) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    InjOn (circleArcParam L a b) (Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hsParam : a + s * (b - a) ∈ Ico (0 : ℝ) 1 := by
    constructor
    · have hnonneg : 0 ≤ s * (b - a) :=
        mul_nonneg hs.1 (sub_nonneg.mpr (le_of_lt hab))
      nlinarith
    · have hmul : s * (b - a) ≤ 1 * (b - a) :=
        mul_le_mul_of_nonneg_right hs.2 (sub_nonneg.mpr (le_of_lt hab))
      nlinarith
  have htParam : a + t * (b - a) ∈ Ico (0 : ℝ) 1 := by
    constructor
    · have hnonneg : 0 ≤ t * (b - a) :=
        mul_nonneg ht.1 (sub_nonneg.mpr (le_of_lt hab))
      nlinarith
    · have hmul : t * (b - a) ≤ 1 * (b - a) :=
        mul_le_mul_of_nonneg_right ht.2 (sub_nonneg.mpr (le_of_lt hab))
      nlinarith
  have hparam :
      a + s * (b - a) = a + t * (b - a) :=
    CircleJordan.circleParam_injOn_Ico L hsParam htParam hst
  nlinarith [sub_pos.mpr hab]

/-- A proper circular subarc inside one turn is a simple arc. -/
theorem isSimpleArcEnd_circleArc
    (L : Lollipop) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    IsSimpleArcEnd (circleArc L a b)
      (CircleJordan.circleParam L a) (CircleJordan.circleParam L b) := by
  refine ⟨circleArcParam L a b, ?_, continuous_circleArcParam L a b,
    circleArcParam_injOn L ha hab hb, ?_, ?_⟩
  · exact circleArc_eq_range_circleArcParam L hab
  · simp [circleArcParam]
  · simp [circleArcParam]

/-- A proper circular subarc inside one turn is connected. -/
theorem circleArc_isConnected
    (L : Lollipop) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    IsConnected (circleArc L a b) :=
  isSimpleArc_isConnected
    (isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_circleArc L ha hab hb))

theorem circleArc_subset_circle
    (L : Lollipop) (a b : ℝ) :
    circleArc L a b ⊆ L.circle := by
  rintro x ⟨t, _ht, rfl⟩
  exact CircleJordan.circleParam_mem_circle L t

theorem circleArc_subset_carrier
    (L : Lollipop) (a b : ℝ) :
    circleArc L a b ⊆ L.carrier :=
  (circleArc_subset_circle L a b).trans (Lollipop.circle_subset_carrier L)

/-- A proper circular subarc has connected complement. -/
theorem componentCount_compl_circleArc_eq_one
    (L : Lollipop) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    componentCount ((circleArc L a b)ᶜ) = 1 :=
  SimpleArcComplement.componentCount_compl_simpleArc_eq_one
    (isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_circleArc L ha hab hb))

/-- Finiteness form for complements of proper circular subarcs. -/
theorem finite_connectedComponents_compl_circleArc
    (L : Lollipop) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) :
    Finite (ConnectedComponents ((circleArc L a b)ᶜ : Set Point)) :=
  SimpleArcComplement.finite_connectedComponents_compl_simpleArc
    (isSimpleArcEnd_isSimpleArc (isSimpleArcEnd_circleArc L ha hab hb))

end PrimitiveArcs
end EndToEnd
end Concrete
end Lollipop
