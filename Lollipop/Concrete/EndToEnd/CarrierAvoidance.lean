import Lollipop.Concrete.EndToEnd.Support
import Mathlib.Topology.Separation.Connected
import Mathlib.Tactic

/-!
# Carrier avoidance

A concrete lollipop carrier has empty interior.  This is the local geometric
fact needed by finite triple-contact avoidance: a finite list of translated
carriers cannot fill a nonempty open set of translation parameters.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

namespace Lollipop

/-- The point opposite the stem anchor on the circle. -/
def opposite (L : Lollipop) : Point :=
  L.center - L.radial

theorem opposite_mem_circle (L : Lollipop) : opposite L ∈ L.circle := by
  unfold opposite
  change ‖(L.center - L.radial) - L.center‖ = ‖L.radial‖
  rw [show (L.center - L.radial) - L.center = -L.radial by module]
  simp

theorem anchor_ne_opposite (L : Lollipop) : L.anchor ≠ opposite L := by
  intro h
  apply L.radial_ne_zero
  have h' : L.center + L.radial = L.center - L.radial := by
    simpa [Lollipop.anchor, opposite] using h
  have htwo : (2 : ℝ) • L.radial = 0 := by
    calc
      (2 : ℝ) • L.radial = L.radial + L.radial := by module
      _ = (L.center + L.radial) - (L.center - L.radial) := by module
      _ = 0 := by
        rw [h']
        module
  rcases smul_eq_zero.mp htwo with htwoZero | hradial
  · norm_num at htwoZero
  · exact hradial

theorem circle_infinite (L : Lollipop) : L.circle.Infinite := by
  have hnontrivial : L.circle.Nontrivial :=
    ⟨L.anchor, L.anchor_mem_circle,
      opposite L, opposite_mem_circle L, anchor_ne_opposite L⟩
  exact L.isConnected_circle.isPreconnected.infinite_of_nontrivial hnontrivial

/-- A circle whose radius differs from `L.radius` meets `L.carrier` in a
finite set. -/
theorem circle_inter_carrier_finite_of_radius_ne
    (M L : Lollipop) (hradius : M.radius ≠ L.radius) :
    (M.circle ∩ L.carrier).Finite := by
  have hsphere : concreteSphere M ≠ concreteSphere L := by
    intro h
    exact hradius (congrArg EuclideanGeometry.Sphere.radius h)
  have hcc : (M.circle ∩ L.circle).Finite := by
    change (cc M L).Finite
    apply finite_of_forall_mem_eq_left_or_right
    intro a b x ha hb hx hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx
  have hcr : (M.circle ∩ L.stem).Finite := by
    change (cr M L).Finite
    exact finite_circle_ray_intersection M L
  apply (hcc.union hcr).subset
  intro z hz
  change z ∈ M.circle ∧ (z ∈ L.circle ∨ z ∈ L.stem) at hz
  rcases hz with ⟨hzM, hzLcircle | hzLstem⟩
  · exact Or.inl ⟨hzM, hzLcircle⟩
  · exact Or.inr ⟨hzM, hzLstem⟩

/-- Every nonempty open set contains a point outside a fixed concrete
lollipop carrier. -/
theorem exists_mem_open_not_mem_carrier
    (L : Lollipop) {U : Set Point}
    (hUopen : IsOpen U) {x : Point} (hxU : x ∈ U) :
    ∃ z : Point, z ∈ U ∧ z ∉ L.carrier := by
  obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hUopen x hxU
  let ρ : ℝ := min ε L.radius / 4
  have hminpos : 0 < min ε L.radius := lt_min hεpos L.radius_pos
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hρltε : ρ < ε := by
    have hle := min_le_left ε L.radius
    dsimp [ρ]
    nlinarith
  have hρltRadius : ρ < L.radius := by
    have hle := min_le_right ε L.radius
    dsimp [ρ]
    nlinarith
  let M : Lollipop :=
    { center := x
      radial := ρ • L.unitRadial
      radial_ne_zero := smul_ne_zero (ne_of_gt hρpos) L.unitRadial_ne_zero }
  have hMradius : M.radius = ρ := by
    simp [M, Lollipop.radius, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρpos]
  have hcircleU : M.circle ⊆ U := by
    intro z hz
    apply hball
    rw [Metric.mem_ball]
    have hz' : ‖z - x‖ = ρ := by
      simpa [M, Lollipop.circle, hMradius] using hz
    simpa [dist_eq_norm, hz'] using hρltε
  have hMRadiusNe : M.radius ≠ L.radius := by
    rw [hMradius]
    exact ne_of_lt hρltRadius
  have hinterFinite : (M.circle ∩ L.carrier).Finite :=
    circle_inter_carrier_finite_of_radius_ne M L hMRadiusNe
  by_contra hno
  push Not at hno
  have hcircleSubset : M.circle ⊆ M.circle ∩ L.carrier := by
    intro z hz
    exact ⟨hz, hno z (hcircleU hz)⟩
  exact circle_infinite M (hinterFinite.subset hcircleSubset)

end Lollipop

end EndToEnd
end Concrete
end Lollipop
