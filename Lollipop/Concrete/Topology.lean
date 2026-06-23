import Lollipop.Concrete.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-!
# Elementary topology of concrete lollipops

This file proves the first concrete topological facts needed by the
certificate-free endpoint: the primitive circle and stem are closed and
connected, and therefore the full lollipop carrier is closed and connected.
-/

noncomputable section

namespace Lollipop
namespace Concrete

open Set

namespace Lollipop

/-- The concrete point space is genuinely two-dimensional. -/
theorem one_lt_rank_point : 1 < Module.rank ℝ Point := by
  have hrank :
      Module.rank ℝ Point = Module.rank ℝ (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin 2)).toLinearEquiv.rank_eq
  rw [hrank, rank_fin_fun]
  norm_num

/-- The affine parametrization of the outward stem. -/
def stemMap (L : Lollipop) (t : ℝ) : Point :=
  L.center + t • L.radial

theorem continuous_stemMap (L : Lollipop) : Continuous (stemMap L) := by
  unfold stemMap
  fun_prop

/-- The concrete circle is the usual metric sphere. -/
theorem circle_eq_sphere (L : Lollipop) :
    L.circle = Metric.sphere L.center L.radius := by
  ext x
  simp [circle]

theorem isClosed_circle (L : Lollipop) : IsClosed L.circle := by
  rw [circle_eq_sphere]
  exact Metric.isClosed_sphere

theorem isConnected_circle (L : Lollipop) : IsConnected L.circle := by
  rw [circle_eq_sphere]
  exact isConnected_sphere one_lt_rank_point L.center
    (le_of_lt (radius_pos L))

/-- The stem is the image of the closed ray `[1, ∞)` under its affine map. -/
theorem stem_eq_image_Ici (L : Lollipop) :
    L.stem = stemMap L '' Ici (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

theorem isClosed_stem (L : Lollipop) : IsClosed L.stem := by
  rw [stem_eq_image_Ici]
  have hsmul : IsClosed ((fun t : ℝ => t • L.radial) '' Ici (1 : ℝ)) :=
    (isClosedEmbedding_smul_left (𝕜 := ℝ) L.radial_ne_zero).isClosedMap
      (Ici (1 : ℝ)) isClosed_Ici
  have htranslate :
      IsClosed ((fun y : Point => L.center + y) ''
        ((fun t : ℝ => t • L.radial) '' Ici (1 : ℝ))) :=
    (Homeomorph.addLeft L.center).isClosedMap
      ((fun t : ℝ => t • L.radial) '' Ici (1 : ℝ)) hsmul
  convert htranslate using 1
  ext x
  constructor
  · rintro ⟨t, ht, htx⟩
    exact ⟨t • L.radial, ⟨t, ht, rfl⟩, by simpa [stemMap] using htx⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, htx⟩
    exact ⟨t, ht, by simpa [stemMap] using htx⟩

theorem isConnected_stem (L : Lollipop) : IsConnected L.stem := by
  rw [stem_eq_image_Ici]
  exact isConnected_Ici.image (stemMap L) (continuous_stemMap L).continuousOn

theorem isClosed_carrier (L : Lollipop) : IsClosed L.carrier := by
  simpa [carrier] using (isClosed_circle L).union (isClosed_stem L)

theorem isConnected_carrier (L : Lollipop) : IsConnected L.carrier := by
  have hmeet : (L.circle ∩ L.stem).Nonempty :=
    ⟨L.anchor, anchor_mem_circle L, anchor_mem_stem L⟩
  simpa [carrier] using
    (isConnected_circle L).union hmeet (isConnected_stem L)

/-- Actual unit stem direction. -/
def unitRadial (L : Lollipop) : Point := L.radius⁻¹ • L.radial

@[simp] theorem norm_unitRadial (L : Lollipop) : ‖L.unitRadial‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs]
  rw [abs_inv]
  rw [abs_of_pos L.radius_pos]
  exact inv_mul_cancel₀ L.radius_ne_zero

theorem unitRadial_ne_zero (L : Lollipop) : L.unitRadial ≠ 0 := by
  intro h
  have hnorm := L.norm_unitRadial
  rw [h, norm_zero] at hnorm
  norm_num at hnorm

theorem radial_eq_radius_smul_unitRadial (L : Lollipop) :
    L.radial = L.radius • L.unitRadial := by
  simp [unitRadial, smul_smul, L.radius_ne_zero]

/-- Unit-speed form of the stem. -/
def stemByDistance (L : Lollipop) : Set Point :=
  {x | ∃ q : ℝ, L.radius ≤ q ∧ x = L.center + q • L.unitRadial}

@[simp] theorem stem_eq_stemByDistance (L : Lollipop) :
    L.stem = L.stemByDistance := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t * L.radius, by nlinarith [L.radius_pos], ?_⟩
    rw [L.radial_eq_radius_smul_unitRadial, smul_smul]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q / L.radius, (le_div_iff₀ L.radius_pos).2 (by simpa using hq), ?_⟩
    rw [L.radial_eq_radius_smul_unitRadial, smul_smul]
    field_simp [L.radius_ne_zero]

end Lollipop

end Concrete
end Lollipop
