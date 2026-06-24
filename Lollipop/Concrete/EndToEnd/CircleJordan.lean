import Lollipop.Concrete.EndToEnd.JordanBridge
import Lollipop.Concrete.Topology
import JordanCurveTheorem.SectionN_K33
import Mathlib.Tactic

/-!
# Lollipop circles as Jordan curves

The base insertion step in the topology-first route uses the lollipop circle
as the separating Jordan curve.  This file proves the reusable bridge from
the concrete lollipop circle definition to the local Jordan-curve API.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace CircleJordan

open Set
open Real

/-- Standard parametrization of the concrete lollipop circle. -/
def circleParam (L : Lollipop) (t : ℝ) : Point :=
  L.center + L.radius • cis (2 * π * t)

theorem continuous_circleParam (L : Lollipop) :
    Continuous (circleParam L) := by
  unfold circleParam
  exact continuous_polar continuous_const
    (by fun_prop : Continuous fun t : ℝ => 2 * π * t)

theorem circleParam_zero_eq_one (L : Lollipop) :
    circleParam L 0 = circleParam L 1 := by
  unfold circleParam
  simp [cis, point, Real.cos_two_pi, Real.sin_two_pi]

theorem circleParam_mem_circle (L : Lollipop) (t : ℝ) :
    circleParam L t ∈ L.circle := by
  unfold circleParam Lollipop.circle
  have hnorm :
      ‖L.radius • cis (2 * π * t)‖ = L.radius := by
    have hcis := norm2_scale_cis L.radius (2 * π * t)
    simpa [norm2, abs_of_pos L.radius_pos] using hcis
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    Lollipop.radius] using hnorm

theorem circle_subset_range_circleParam (L : Lollipop) :
    L.circle ⊆ circleParam L '' Icc (0 : ℝ) 1 := by
  intro x hx
  let y : Point := x - L.center
  rcases polar_exist y with ⟨r, θ, hθ, hr, hy⟩
  have hnorm_y : ‖y‖ = L.radius := by
    simpa [y, Lollipop.circle] using hx
  have hradius_abs : |r| = L.radius := by
    have h := congrArg norm hy
    rw [norm_smul] at h
    have hcisnorm : ‖cis θ‖ = 1 := by
      simpa [norm2] using norm2_cis θ
    rw [hcisnorm, mul_one] at h
    rw [hnorm_y] at h
    simpa [Real.norm_eq_abs] using h.symm
  have hradius : r = L.radius := by
    rw [abs_of_nonneg hr] at hradius_abs
    exact hradius_abs
  refine ⟨θ / (2 * π), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg hθ.1 (le_of_lt (by positivity : (0 : ℝ) < 2 * π))
  · have h2pi_pos : 0 < 2 * π := by positivity
    exact div_le_one_of_le₀ (le_of_lt hθ.2) (le_of_lt h2pi_pos)
  · unfold circleParam
    rw [show 2 * π * (θ / (2 * π)) = θ by
      field_simp [show (2 : ℝ) * π ≠ 0 by positivity]]
    rw [← hradius, ← hy]
    simp [y, sub_eq_add_neg, add_left_comm]

theorem range_circleParam_subset_circle (L : Lollipop) :
    circleParam L '' Icc (0 : ℝ) 1 ⊆ L.circle := by
  rintro x ⟨t, _ht, rfl⟩
  exact circleParam_mem_circle L t

theorem circle_eq_range_circleParam (L : Lollipop) :
    L.circle = circleParam L '' Icc (0 : ℝ) 1 :=
  subset_antisymm (circle_subset_range_circleParam L)
    (range_circleParam_subset_circle L)

theorem circleParam_injOn_Ico (L : Lollipop) :
    InjOn (circleParam L) (Ico (0 : ℝ) 1) := by
  intro a ha b hb hab
  unfold circleParam at hab
  have hvec :
      L.radius • cis (2 * π * a) =
        L.radius • cis (2 * π * b) := by
    exact add_left_cancel hab
  have haθ : 2 * π * a ∈ Ico (0 : ℝ) (2 * π) := by
    constructor <;> nlinarith [ha.1, ha.2, Real.pi_pos]
  have hbθ : 2 * π * b ∈ Ico (0 : ℝ) (2 * π) := by
    constructor <;> nlinarith [hb.1, hb.2, Real.pi_pos]
  rcases polar_inj (le_of_lt L.radius_pos) (le_of_lt L.radius_pos)
      haθ hbθ hvec with hzero | hangle
  · exact False.elim (L.radius_ne_zero hzero.1)
  · have hθ : 2 * π * a = 2 * π * b := hangle.2
    nlinarith [Real.pi_pos]

/-- A concrete lollipop circle is a simple closed curve in the local Jordan
API. -/
theorem isSimpleClosedCurve_circle (L : Lollipop) :
    IsSimpleClosedCurve L.circle := by
  refine ⟨circleParam L, circle_eq_range_circleParam L,
    continuous_circleParam L, circleParam_injOn_Ico L,
    circleParam_zero_eq_one L⟩

/-- The complement of a concrete lollipop circle has exactly two connected
components. -/
theorem componentCount_circle_compl_eq_two (L : Lollipop) :
    componentCount (L.circleᶜ) = 2 :=
  JordanBridge.jordan_complement_componentCount_eq_two
    (isSimpleClosedCurve_circle L)

/-- The complement of a concrete lollipop circle has finitely many connected
components. -/
theorem finite_connectedComponents_circle_compl (L : Lollipop) :
    Finite (ConnectedComponents (L.circleᶜ : Set Point)) :=
  JordanBridge.finite_components_jordan_complement
    (isSimpleClosedCurve_circle L)

end CircleJordan
end EndToEnd
end Concrete
end Lollipop
