import Lollipop.Lemma_5_1.Proof
import Lollipop.Theorem_4_1.Proof
import Lollipop.Theorem_7_1.Proof
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Geometry.Euclidean.Sphere.Power
import Mathlib.Geometry.Euclidean.Sphere.SecondInter
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Order.IntermediateValue

/-!
This is the substantive proof compilation unit for `Proposition_2_1`.
All project proof components used below are integrated here or imported
directly from another manuscript-numbered `Proof.lean` file.
-/

/-!
Proof component 1: `Basic`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Concrete Euclidean lollipops

This file starts the certificate-free endpoint requested in
`audit/UNCONDITIONAL_FORMALIZATION_VERDICT.md`.

The older public theorem proves the manuscript formula from abstract geometry
certificates.  Here the geometric object is concrete: a lollipop in the
Euclidean plane is a circle together with the outward radial stem determined by
a single nonzero vector.  Regions are actual connected components of the
complement.

The hard upper and lower geometric theorems are not assumed here.  They are
named as concrete propositions, and `lollipopMaximum_of_upper_lower` records
the final assembly step those proofs must feed.
-/

noncomputable section

namespace Lollipop
namespace Concrete

open Set

/-- The Euclidean plane used for the certificate-free lollipop model. -/
abbrev Point : Type :=
  EuclideanSpace ℝ (Fin 2)

/--
A concrete lollipop is determined by a center and one nonzero radial vector.
The circle has radius `‖radial‖`, and the stem starts at `center + radial` and
continues in the same outward radial direction.
-/
structure Lollipop where
  center : Point
  radial : Point
  radial_ne_zero : radial ≠ 0

namespace Lollipop

@[ext] theorem ext {L M : Lollipop}
    (hcenter : L.center = M.center) (hradial : L.radial = M.radial) :
    L = M := by
  cases L
  cases M
  simp_all

/-- The circle radius determined by the radial vector. -/
def radius (L : Lollipop) : ℝ :=
  ‖L.radial‖

/-- The point where the stem attaches to the circle. -/
def anchor (L : Lollipop) : Point :=
  L.center + L.radial

/-- The circular primitive of a lollipop. -/
def circle (L : Lollipop) : Set Point :=
  {x | ‖x - L.center‖ = L.radius}

/-- The outward radial stem of a lollipop. -/
def stem (L : Lollipop) : Set Point :=
  {x | ∃ t : ℝ, 1 ≤ t ∧ x = L.center + t • L.radial}

/-- The full carrier: circle plus outward radial stem. -/
def carrier (L : Lollipop) : Set Point :=
  L.circle ∪ L.stem

theorem radius_pos (L : Lollipop) : 0 < L.radius := by
  simpa [radius, norm_pos_iff] using L.radial_ne_zero

theorem radius_ne_zero (L : Lollipop) : L.radius ≠ 0 :=
  ne_of_gt (radius_pos L)

theorem anchor_mem_circle (L : Lollipop) : L.anchor ∈ L.circle := by
  simp [circle, anchor, radius]

theorem anchor_mem_stem (L : Lollipop) : L.anchor ∈ L.stem := by
  refine ⟨1, le_rfl, ?_⟩
  simp [anchor]

theorem circle_subset_carrier (L : Lollipop) : L.circle ⊆ L.carrier :=
  fun _ hx => Or.inl hx

theorem stem_subset_carrier (L : Lollipop) : L.stem ⊆ L.carrier :=
  fun _ hx => Or.inr hx

theorem anchor_mem_carrier (L : Lollipop) : L.anchor ∈ L.carrier :=
  stem_subset_carrier L (anchor_mem_stem L)

end Lollipop

/-- An arrangement of `n` concrete lollipops. -/
abbrev Arrangement (n : ℕ) : Type :=
  Fin n → Lollipop

/-- The occupied carrier set of an arrangement. -/
def occupied {n : ℕ} (A : Arrangement n) : Set Point :=
  ⋃ i, (A i).carrier

theorem mem_occupied_iff {n : ℕ} {A : Arrangement n} {x : Point} :
    x ∈ occupied A ↔ ∃ i : Fin n, x ∈ (A i).carrier := by
  simp [occupied]

/-- The complement of the occupied set, as a topological subtype. -/
abbrev FreeSpace {n : ℕ} (A : Arrangement n) : Type :=
  {x : Point // x ∉ occupied A}

/--
The number of connected components of the complement.

This uses `Nat.card`, so it is zero if the connected-component type has not
yet been proved finite.  A complete formalization must separately prove
finiteness for finite lollipop arrangements and then connect this definition
to the planar graph/topology engine.
-/
def regionCount {n : ℕ} (A : Arrangement n) : ℕ :=
  Nat.card (ConnectedComponents (FreeSpace A))

/-- Finiteness obligation for concrete lollipop complement components. -/
def RegionFinitenessStatement (n : ℕ) : Prop :=
  ∀ A : Arrangement n, Finite (ConnectedComponents (FreeSpace A))

/-- Region count coerced to `ℚ`, matching the manuscript formula stack. -/
def regionCountRat {n : ℕ} (A : Arrangement n) : ℚ :=
  regionCount A

/-- The displayed manuscript candidate value. -/
def candidate (n : ℕ) : ℚ :=
  4 * ((n.choose 2 : ℕ) : ℚ) +
    TheoremOneManuscript.manuscriptS n + (n : ℚ) + 1

/-- Concrete upper-bound statement for the certificate-free endpoint. -/
def RegionUpperStatement (n : ℕ) : Prop :=
  ∀ A : Arrangement n, regionCountRat A ≤ candidate n

/-- Concrete lower-bound statement for the certificate-free endpoint. -/
def RegionLowerStatement (n : ℕ) : Prop :=
  ∃ A : Arrangement n, regionCountRat A = candidate n

/-- The intended certificate-free maximum theorem statement. -/
def LollipopMaximumStatement (n : ℕ) : Prop :=
  IsGreatest (Set.range (fun A : Arrangement n => regionCountRat A)) (candidate n)

/--
The final assembly step for the concrete endpoint.

The remaining work is to prove `RegionUpperStatement n` and
`RegionLowerStatement n` from the actual Euclidean geometry/topology.  Once
those are available, this theorem produces the desired `IsGreatest` statement
without any `GeometryCertificates` argument.
-/
theorem lollipopMaximum_of_upper_lower {n : ℕ}
    (hupper : RegionUpperStatement n)
    (hlower : RegionLowerStatement n) :
    LollipopMaximumStatement n := by
  constructor
  · rcases hlower with ⟨A, hA⟩
    exact ⟨A, hA⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper A

/-- All-`n` assembly form of the certificate-free endpoint. -/
theorem lollipopMaximum_all_of_upper_lower
    (hupper : ∀ n : ℕ, RegionUpperStatement n)
    (hlower : ∀ n : ℕ, RegionLowerStatement n) :
    ∀ n : ℕ, LollipopMaximumStatement n :=
  fun n => lollipopMaximum_of_upper_lower (hupper n) (hlower n)

end Concrete
end Lollipop

/-!
Proof component 2: `Topology`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

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

/-!
Proof component 3: `Empty`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Empty concrete arrangement

The obstruction note points out that the abstract certificate interface can
misrepresent the `n = 0` case.  In the concrete Euclidean model, the empty
arrangement has the whole plane as free space, hence exactly one connected
component.
-/

noncomputable section

namespace Lollipop
namespace Concrete

open Set

/-- The manuscript extremum has value `0` at size `0`. -/
theorem manuscriptS_zero :
    TheoremOneManuscript.manuscriptS 0 = 0 := by
  rw [TheoremOneManuscript.manuscriptS_eq_concreteS]
  rw [Lollipop.concreteS_eq_concreteM, Lollipop.concreteM_zero]
  norm_num

/-- The concrete target formula has value `1` at size `0`. -/
theorem candidate_zero : candidate 0 = 1 := by
  simp [candidate, manuscriptS_zero]

/-- The unique empty arrangement, named for use as the `n = 0` lower witness. -/
def emptyArrangement : Arrangement 0 :=
  fun i => nomatch i

theorem occupied_zero (A : Arrangement 0) : occupied A = ∅ := by
  ext x
  simp [occupied]

theorem freeSpace_zero_nonempty (A : Arrangement 0) : Nonempty (FreeSpace A) :=
  ⟨⟨0, by simp [occupied_zero A]⟩⟩

/-- The empty arrangement has exactly one complementary region. -/
theorem regionCount_zero (A : Arrangement 0) : regionCount A = 1 := by
  have hset : {x : Point | x ∉ occupied A} = univ := by
    ext x
    simp [occupied_zero A]
  have hpre : IsPreconnected ({x : Point | x ∉ occupied A}) := by
    rw [hset]
    exact isPreconnected_univ
  haveI : PreconnectedSpace (FreeSpace A) := Subtype.preconnectedSpace hpre
  have hsub : Subsingleton (ConnectedComponents (FreeSpace A)) := inferInstance
  have hnon : Nonempty (ConnectedComponents (FreeSpace A)) :=
    ConnectedComponents.nonempty_iff_nonempty.mpr (freeSpace_zero_nonempty A)
  unfold regionCount
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, hnon⟩

theorem regionCountRat_zero (A : Arrangement 0) : regionCountRat A = 1 := by
  simp [regionCountRat, regionCount_zero A]

theorem regionUpperStatement_zero : RegionUpperStatement 0 := by
  intro A
  rw [regionCountRat_zero A, candidate_zero]

theorem regionLowerStatement_zero : RegionLowerStatement 0 :=
  ⟨emptyArrangement, by rw [regionCountRat_zero, candidate_zero]⟩

/-- Concrete certificate-free maximum theorem for the empty arrangement. -/
theorem lollipopMaximum_zero : LollipopMaximumStatement 0 :=
  lollipopMaximum_of_upper_lower regionUpperStatement_zero regionLowerStatement_zero

end Concrete
end Lollipop

/-!
Proof component 4: `ColoredTuran.GeometricReduction`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Geometric-input reduction.

This module moves the remaining upper-bound boundary one step closer to the
manuscript.  Instead of asking for a prebuilt colored graph certificate, it
starts from the geometric predicates used in the paper: `close` and
`intriguing`, a pairwise crossing table, the pointwise geometric crossing
bounds, and the two finite forbidden-pair facts.  Lean then constructs the
four-colored graph and produces the colored-graph upper certificate used by
the fully internalized colored Turan stack.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ColoredGraph

variable {V : Type u} [DecidableEq V]

/-- The four-coloring determined by the manuscript's two geometric predicates.
Color `B` means `D`-only, i.e. not close but intriguing; color `A` means
`E`-only, i.e. close but not intriguing; color `X` means neither close nor
intriguing. -/
def colorOfCloseIntriguing
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (v w : V) : PairColor :=
  if v = w then
    PairColor.zero
  else if close v w then
    if intriguing v w then PairColor.zero else PairColor.A
  else if intriguing v w then
    PairColor.B
  else
    PairColor.X

/-- The colored graph built from the close/intriguing predicates. -/
def ofCloseIntriguing
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v) :
    ColoredGraph V where
  color := colorOfCloseIntriguing close intriguing
  color_symm := by
    intro v w
    by_cases hvw : v = w
    · subst w
      simp [colorOfCloseIntriguing]
    · have hwv : w ≠ v := Ne.symm hvw
      simp [colorOfCloseIntriguing, hvw, hwv,
        hclose_symm v w, hintr_symm v w]
  color_self := by
    intro v
    simp [colorOfCloseIntriguing]

@[simp]
theorem ofCloseIntriguing_color
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    (v w : V) :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).color v w =
      colorOfCloseIntriguing close intriguing v w := by
  rfl

/-- In the close/intriguing coloring, the derived `D` graph is exactly the
off-diagonal relation "not close". -/
theorem ofCloseIntriguing_DGraph_adj_iff
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    {v w : V} :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).DGraph.Adj v w ↔
      v ≠ w ∧ ¬ close v w := by
  by_cases hvw : v = w
  · subst w
    simp [DGraph, colorOfCloseIntriguing, isDColor]
  · by_cases hc : close v w <;>
      by_cases hi : intriguing v w <;>
        simp [DGraph, colorOfCloseIntriguing, isDColor, hvw, hc, hi]

/-- In the close/intriguing coloring, the derived `E` graph is exactly the
off-diagonal relation "not intriguing". -/
theorem ofCloseIntriguing_EGraph_adj_iff
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    {v w : V} :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).EGraph.Adj v w ↔
      v ≠ w ∧ ¬ intriguing v w := by
  by_cases hvw : v = w
  · subst w
    simp [EGraph, colorOfCloseIntriguing, isEColor]
  · by_cases hc : close v w <;>
      by_cases hi : intriguing v w <;>
        simp [EGraph, colorOfCloseIntriguing, isEColor, hvw, hc, hi]

/-- If every four vertices contain a close pair, the `D = not close` graph is
`K_4`-free. -/
theorem ofCloseIntriguing_DGraph_cliqueFree_four
    [Fintype V]
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    (hclose_four :
      ∀ t : Finset V, t.card = 4 →
        ∃ v ∈ t, ∃ w ∈ t, v ≠ w ∧ close v w) :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).DGraph.CliqueFree 4 := by
  intro t ht
  rcases hclose_four t ht.card_eq with ⟨v, hv, w, hw, hvw, hclose⟩
  have hadj := ht.isClique hv hw hvw
  have hnot_close :
      ¬ close v w := by
    exact ((ofCloseIntriguing_DGraph_adj_iff
      close intriguing hclose_symm hintr_symm).mp hadj).2
  exact hnot_close hclose

/-- If every five vertices contain an intriguing pair, the `E = not
intriguing` graph is `K_5`-free. -/
theorem ofCloseIntriguing_EGraph_cliqueFree_five
    [Fintype V]
    (close intriguing : V → V → Prop)
    [DecidableRel close] [DecidableRel intriguing]
    (hclose_symm : ∀ v w : V, close v w ↔ close w v)
    (hintr_symm : ∀ v w : V, intriguing v w ↔ intriguing w v)
    (hintr_five :
      ∀ t : Finset V, t.card = 5 →
        ∃ v ∈ t, ∃ w ∈ t, v ≠ w ∧ intriguing v w) :
    (ofCloseIntriguing close intriguing hclose_symm hintr_symm).EGraph.CliqueFree 5 := by
  intro t ht
  rcases hintr_five t ht.card_eq with ⟨v, hv, w, hw, hvw, hintr⟩
  have hadj := ht.isClique hv hw hvw
  have hnot_intr :
      ¬ intriguing v w := by
    exact ((ofCloseIntriguing_EGraph_adj_iff
      close intriguing hclose_symm hintr_symm).mp hadj).2
  exact hnot_intr hintr

end ColoredGraph

section PairSums

/-- For a symmetric zero-diagonal table on `Fin n`, the ordered double sum is
twice the increasing-pair sum. -/
theorem two_pairSum_eq_double_sum_of_symm_zero_diag
    (n : Nat) (f : Fin n → Fin n → Rat)
    (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0) :
    2 * pairSum n f = ∑ i : Fin n, ∑ j : Fin n, f i j := by
  classical
  let all : Finset (Fin n × Fin n) := Finset.univ
  let ltSet : Finset (Fin n × Fin n) := all.filter (fun p => p.1 < p.2)
  let gtSet : Finset (Fin n × Fin n) := all.filter (fun p => p.2 < p.1)
  let eqSet : Finset (Fin n × Fin n) := all.filter (fun p => p.1 = p.2)
  have hpair : pairFinset n = ltSet := by
    ext p
    simp [pairFinset, ltSet, all]
  have hgt_eq :
      (∑ p ∈ gtSet, f p.1 p.2) =
        ∑ p ∈ ltSet, f p.1 p.2 := by
    refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
    · intro p hp
      simp [gtSet, ltSet, all] at hp ⊢
      exact hp
    · intro a ha b hb h
      cases a
      cases b
      simp at h
      aesop
    · intro b hb
      refine ⟨(b.2, b.1), ?_, ?_⟩
      · simp [gtSet, ltSet, all] at hb ⊢
        exact hb
      · simp
    · intro p hp
      exact hsymm p.1 p.2
  have heq_zero : (∑ p ∈ eqSet, f p.1 p.2) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [eqSet, all] at hp
    simpa [hp] using hdiag p.1
  have hpartition : all = ltSet ∪ eqSet ∪ gtSet := by
    ext p
    simp [all, ltSet, eqSet, gtSet]
    omega
  have hdisj_lt_eq : Disjoint ltSet eqSet := by
    rw [Finset.disjoint_left]
    intro p hlt heq
    simp [ltSet, eqSet, all] at hlt heq
    omega
  have hdisj_lteq_gt : Disjoint (ltSet ∪ eqSet) gtSet := by
    rw [Finset.disjoint_left]
    intro p hp hgt
    rw [Finset.mem_union] at hp
    simp [ltSet, eqSet, gtSet, all] at hp hgt
    rcases hp with hp | hp <;> omega
  have hfull_parts :
      (∑ p : Fin n × Fin n, f p.1 p.2) =
        (∑ p ∈ ltSet, f p.1 p.2) +
        (∑ p ∈ eqSet, f p.1 p.2) +
        (∑ p ∈ gtSet, f p.1 p.2) := by
    calc
      (∑ p : Fin n × Fin n, f p.1 p.2) =
          ∑ p ∈ all, f p.1 p.2 := by
            simp [all]
      _ = ∑ p ∈ ltSet ∪ eqSet ∪ gtSet, f p.1 p.2 := by
            rw [← hpartition]
      _ = (∑ p ∈ ltSet ∪ eqSet, f p.1 p.2) +
            (∑ p ∈ gtSet, f p.1 p.2) := by
            rw [Finset.sum_union hdisj_lteq_gt]
      _ = ((∑ p ∈ ltSet, f p.1 p.2) +
            (∑ p ∈ eqSet, f p.1 p.2)) +
            (∑ p ∈ gtSet, f p.1 p.2) := by
            rw [Finset.sum_union hdisj_lt_eq]
      _ = (∑ p ∈ ltSet, f p.1 p.2) +
            (∑ p ∈ eqSet, f p.1 p.2) +
            (∑ p ∈ gtSet, f p.1 p.2) := by
            ring
  have hprod :
      (∑ i : Fin n, ∑ j : Fin n, f i j) =
        ∑ p : Fin n × Fin n, f p.1 p.2 := by
    symm
    rw [← Finset.sum_product
      (Finset.univ : Finset (Fin n)) (Finset.univ : Finset (Fin n))
      (fun p : Fin n × Fin n => f p.1 p.2)]
    simp only [Finset.univ_product_univ]
  rw [hprod, hfull_parts, heq_zero, hgt_eq]
  unfold pairSum
  rw [hpair]
  ring

/-- A colored graph on `Fin n` has ordered objective equal to twice the
increasing-pair color-weight sum. -/
theorem two_pairSum_colorWeight_eq_orderedColorWeight
    (n : Nat) (C : ColoredGraph (Fin n)) :
    2 * pairSum n (fun i j => (C.color i j).weight) =
      C.orderedColorWeight := by
  rw [two_pairSum_eq_double_sum_of_symm_zero_diag]
  · rfl
  · intro i j
    rw [C.color_symm i j]
  · intro i
    simp [C.color_self i, PairColor.weight]

end PairSums

/-- The exact geometric data from which Lean can build the current strongest
upper certificate: close/intriguing relations, pairwise crossings, the
pointwise geometric crossing bounds, and the two forbidden-pair facts. -/
structure PairwiseGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  intriguing_pair_in_every_five :
    ∀ t : Finset (Fin nNat), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ intriguing i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

namespace PairwiseGeometricLollipopUpper

/-- The colored graph canonically associated to the geometric predicates. -/
noncomputable def coloredGraph (L : PairwiseGeometricLollipopUpper) :
    ColoredGraph (Fin L.nNat) := by
  letI : DecidableRel L.close := L.close_decidable
  letI : DecidableRel L.intriguing := L.intriguing_decidable
  exact ColoredGraph.ofCloseIntriguing
    L.close L.intriguing L.close_symm L.intriguing_symm

/-- Its pair score is exactly the color weight of the associated pair. -/
noncomputable def score (L : PairwiseGeometricLollipopUpper) :
    Fin L.nNat → Fin L.nNat → Rat :=
  fun i j => ((L.coloredGraph).color i j).weight

/-- The pointwise geometric cases imply the manuscript's
`cross <= 4 + score` estimate. -/
theorem pointwise_crossing_bound
    (L : PairwiseGeometricLollipopUpper) :
    ∀ i j : Fin L.nNat, i < j → L.cross i j ≤ 4 + L.score i j := by
  intro i j hij
  letI : DecidableRel L.close := L.close_decidable
  letI : DecidableRel L.intriguing := L.intriguing_decidable
  have hne : i ≠ j := ne_of_lt hij
  by_cases hc : L.close i j
  · by_cases hi : L.intriguing i j
    · have hcross := L.cross_le_close_intriguing i j hij hc hi
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith
    · have hcross := L.cross_le_close i j hij hc
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith
  · by_cases hi : L.intriguing i j
    · have hcross := L.cross_le_intriguing i j hij hi
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith
    · have hcross := L.cross_le_general i j hij
      simp [score, coloredGraph, ColoredGraph.colorOfCloseIntriguing,
        hne, hc, hi, PairColor.weight] at hcross ⊢
      linarith

/-- Convert geometric close/intriguing data into the colored-graph certificate
used by the internalized colored Turan proof. -/
noncomputable def toPairwiseColoredGraphCertifiedLollipopUpper
    (L : PairwiseGeometricLollipopUpper) :
    PairwiseColoredGraphCertifiedLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  cross := L.cross
  score := L.score
  pair :=
    { nNat := L.nNat
      sigma := pairSum L.nNat L.score
      Vertex := Fin L.nNat
      C := L.coloredGraph
      D_cliqueFree := by
        letI : DecidableRel L.close := L.close_decidable
        letI : DecidableRel L.intriguing := L.intriguing_decidable
        simpa [coloredGraph] using
          ColoredGraph.ofCloseIntriguing_DGraph_cliqueFree_four
            L.close L.intriguing L.close_symm L.intriguing_symm
            L.close_pair_in_every_four
      E_cliqueFree := by
        letI : DecidableRel L.close := L.close_decidable
        letI : DecidableRel L.intriguing := L.intriguing_decidable
        simpa [coloredGraph] using
          ColoredGraph.ofCloseIntriguing_EGraph_cliqueFree_five
            L.close L.intriguing L.close_symm L.intriguing_symm
            L.intriguing_pair_in_every_five
      card_eq := Fintype.card_fin L.nNat
      sigma_le_color := by
        have hordered :=
          two_pairSum_colorWeight_eq_orderedColorWeight L.nNat L.coloredGraph
        change
          pairSum L.nNat (fun i j => (L.coloredGraph.color i j).weight) ≤
            L.coloredGraph.orderedColorWeight / 2
        linarith }
  pair_nNat := rfl
  crossings_le_pairSum := L.crossings_le_pairSum
  pointwise_crossing_bound := L.pointwise_crossing_bound
  score_sum_le_sigma := by rfl
  regions_eq := L.regions_eq

end PairwiseGeometricLollipopUpper

/-- Upper certificates for every arrangement from exactly the geometric
close/intriguing data used in the manuscript. -/
def PairwiseGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper-bound half of Theorem 1 from the manuscript's close/intriguing
geometric upper data. -/
theorem upper_bound_of_pairwise_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  rw [← hLreg, ← hLn]
  exact pairwise_colored_graph_certified_lollipop_upper_bound_choose
    L.toPairwiseColoredGraphCertifiedLollipopUpper

end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 5: `ColoredTuran.CloseDirection`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Finite direction pigeonhole for the close-pair input.

The manuscript uses the elementary fact that among four stem directions in the
plane, two differ by at most a right angle.  This file formalizes the
one-dimensional normalized-angle core of that fact: for four numbers in
cyclic order in `[0, 1)`, one adjacent cyclic gap is at most `1 / 4`.
-/

namespace Lollipop
namespace TheoremOneEndToEnd
namespace CloseDirection

/-- Two normalized directions are close when their circular distance on
`R/Z` is at most `1 / 4`. -/
def cyclicClosePair (a b : ℝ) : Prop :=
  |a - b| ≤ (1 / 4 : ℝ) ∨ (3 / 4 : ℝ) ≤ |a - b|

/-- The canonical close relation from a normalized direction map. -/
def cyclicClose {V : Type*} (theta : V → ℝ) (i j : V) : Prop :=
  cyclicClosePair (theta i) (theta j)

theorem cyclicClosePair_symm (a b : ℝ) :
    cyclicClosePair a b ↔ cyclicClosePair b a := by
  unfold cyclicClosePair
  rw [abs_sub_comm a b]

theorem cyclicClose_symm {V : Type*} (theta : V → ℝ) (i j : V) :
    cyclicClose theta i j ↔ cyclicClose theta j i := by
  exact cyclicClosePair_symm (theta i) (theta j)

/-- If the ordinary normalized-angle distance lies strictly between the two
close thresholds, then the cyclic-close predicate is false. -/
theorem not_cyclicClosePair_of_abs_between
    {a b : ℝ}
    (hlo : (1 / 4 : ℝ) < |a - b|)
    (hhi : |a - b| < (3 / 4 : ℝ)) :
    ¬ cyclicClosePair a b := by
  intro hclose
  rcases hclose with hle | hge
  · linarith
  · linarith

/-- Map-valued version of `not_cyclicClosePair_of_abs_between`. -/
theorem not_cyclicClose_of_abs_between
    {V : Type*} {theta : V → ℝ} {i j : V}
    (hlo : (1 / 4 : ℝ) < |theta i - theta j|)
    (hhi : |theta i - theta j| < (3 / 4 : ℝ)) :
    ¬ cyclicClose theta i j :=
  not_cyclicClosePair_of_abs_between hlo hhi

private theorem cyclicClosePair_of_ordered_sub_le
    {a b : ℝ} (hab : a ≤ b) (h : b - a ≤ (1 / 4 : ℝ)) :
    cyclicClosePair a b := by
  left
  have habs : |a - b| = b - a := by
    rw [abs_of_nonpos]
    · ring
    · linarith
  rwa [habs]

private theorem cyclicClosePair_of_wrap_gap_le
    {a b : ℝ} (_hab : a ≤ b) (h : a + 1 - b ≤ (1 / 4 : ℝ)) :
    cyclicClosePair b a := by
  right
  have habs : |b - a| = b - a := by
    rw [abs_of_nonneg]
    linarith
  rw [habs]
  linarith

/-- Four normalized directions in cyclic order contain a close adjacent pair. -/
theorem sorted_four_has_cyclicClose
    (theta : Fin 4 → ℝ)
    (h0 : 0 ≤ theta 0)
    (h01 : theta 0 ≤ theta 1)
    (h12 : theta 1 ≤ theta 2)
    (h23 : theta 2 ≤ theta 3)
    (h3 : theta 3 < 1) :
    ∃ i : Fin 4, ∃ j : Fin 4, i ≠ j ∧ cyclicClose theta i j := by
  by_cases h01gap : theta 1 - theta 0 ≤ (1 / 4 : ℝ)
  · exact ⟨0, 1, by decide,
      cyclicClosePair_of_ordered_sub_le h01 h01gap⟩
  · by_cases h12gap : theta 2 - theta 1 ≤ (1 / 4 : ℝ)
    · exact ⟨1, 2, by decide,
        cyclicClosePair_of_ordered_sub_le h12 h12gap⟩
    · by_cases h23gap : theta 3 - theta 2 ≤ (1 / 4 : ℝ)
      · exact ⟨2, 3, by decide,
          cyclicClosePair_of_ordered_sub_le h23 h23gap⟩
      · by_cases hwrap : theta 0 + 1 - theta 3 ≤ (1 / 4 : ℝ)
        · have h03 : theta 0 ≤ theta 3 := by linarith
          exact ⟨3, 0, by decide,
            cyclicClosePair_of_wrap_gap_le h03 hwrap⟩
        · have h01gt : (1 / 4 : ℝ) < theta 1 - theta 0 :=
            lt_of_not_ge h01gap
          have h12gt : (1 / 4 : ℝ) < theta 2 - theta 1 :=
            lt_of_not_ge h12gap
          have h23gt : (1 / 4 : ℝ) < theta 3 - theta 2 :=
            lt_of_not_ge h23gap
          have hwrapgt : (1 / 4 : ℝ) < theta 0 + 1 - theta 3 :=
            lt_of_not_ge hwrap
          nlinarith

/-- Cyclic ordering data for a four-element subset.  The enumeration lists the
four directions in nondecreasing normalized-angle order. -/
structure FourSetCyclicOrderData {V : Type*} (theta : V → ℝ)
    (t : Finset V) where
  enumerate : Fin 4 ≃ {x : V // x ∈ t}
  sorted01 : theta (enumerate 0) ≤ theta (enumerate 1)
  sorted12 : theta (enumerate 1) ≤ theta (enumerate 2)
  sorted23 : theta (enumerate 2) ≤ theta (enumerate 3)

namespace FourSetCyclicOrderData

/-- Ordered direction data on a four-set yields a close pair in that four-set. -/
theorem exists_cyclicClose_pair
    {V : Type*} {theta : V → ℝ} {t : Finset V}
    (D : FourSetCyclicOrderData theta t)
    (htheta_nonneg : ∀ x ∈ t, 0 ≤ theta x)
    (htheta_lt_one : ∀ x ∈ t, theta x < 1) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ cyclicClose theta x y := by
  let localTheta : Fin 4 → ℝ := fun i => theta (D.enumerate i)
  have h0 : 0 ≤ localTheta 0 :=
    htheta_nonneg (D.enumerate 0) (D.enumerate 0).property
  have h3 : localTheta 3 < 1 :=
    htheta_lt_one (D.enumerate 3) (D.enumerate 3).property
  rcases sorted_four_has_cyclicClose localTheta h0
      D.sorted01 D.sorted12 D.sorted23 h3 with
    ⟨i, j, hij, hclose⟩
  refine ⟨D.enumerate i, (D.enumerate i).property,
    D.enumerate j, (D.enumerate j).property, ?_, hclose⟩
  intro hval
  exact hij (D.enumerate.injective (Subtype.ext hval))

end FourSetCyclicOrderData

/-- Any four normalized directions contain a close pair.  This packages the
sorting step with mathlib's `List.mergeSort`, so later geometric certificates
only need a normalized direction map rather than sorted order data for every
four-subset. -/
theorem exists_cyclicClose_pair_of_card_four
    {V : Type*} [DecidableEq V]
    (theta : V → ℝ) {t : Finset V} (ht : t.card = 4)
    (htheta_nonneg : ∀ x ∈ t, 0 ≤ theta x)
    (htheta_lt_one : ∀ x ∈ t, theta x < 1) :
    ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ cyclicClose theta x y := by
  classical
  let r : V → V → Prop := fun x y => theta x ≤ theta y
  letI : IsTrans V r :=
    ⟨fun _x _y _z hxy hyz => le_trans hxy hyz⟩
  letI : Std.Total r :=
    ⟨fun x y => le_total (theta x) (theta y)⟩
  let l : List V := t.toList.mergeSort (fun x y => theta x ≤ theta y)
  have hperm : List.Perm l t.toList := by
    simpa [l] using List.mergeSort_perm t.toList (fun x y => theta x ≤ theta y)
  have hlen : l.length = 4 := by
    simp [l, Finset.length_toList, ht]
  have hsorted : l.Pairwise r := by
    simpa [l, r] using List.pairwise_mergeSort' r t.toList
  have hnodup : l.Nodup := by
    simpa [l] using
      (Finset.nodup_toList t).mergeSort
        (le := fun x y => theta x ≤ theta y)
  let idx : Fin 4 → Fin l.length := fun i => Fin.cast hlen.symm i
  let localTheta : Fin 4 → ℝ := fun i => theta (l.get (idx i))
  have hmem : ∀ i : Fin 4, l.get (idx i) ∈ t := by
    intro i
    have hmem_l : l.get (idx i) ∈ l := List.get_mem l (idx i)
    have hmem_toList : l.get (idx i) ∈ t.toList :=
      hperm.mem_iff.mp hmem_l
    simpa using hmem_toList
  have h0 : 0 ≤ localTheta 0 :=
    htheta_nonneg (l.get (idx 0)) (hmem 0)
  have h3 : localTheta 3 < 1 :=
    htheta_lt_one (l.get (idx 3)) (hmem 3)
  have h01 : localTheta 0 ≤ localTheta 1 := by
    exact hsorted.rel_get_of_lt (show idx 0 < idx 1 by
      rw [Fin.lt_def]
      norm_num [idx])
  have h12 : localTheta 1 ≤ localTheta 2 := by
    exact hsorted.rel_get_of_lt (show idx 1 < idx 2 by
      rw [Fin.lt_def]
      norm_num [idx])
  have h23 : localTheta 2 ≤ localTheta 3 := by
    exact hsorted.rel_get_of_lt (show idx 2 < idx 3 by
      rw [Fin.lt_def]
      norm_num [idx])
  rcases sorted_four_has_cyclicClose localTheta h0 h01 h12 h23 h3 with
    ⟨i, j, hij, hclose⟩
  refine ⟨l.get (idx i), hmem i, l.get (idx j), hmem j, ?_, hclose⟩
  intro hxy
  have hidx : idx i = idx j := hnodup.get_inj_iff.mp hxy
  exact hij (Fin.cast_injective hlen.symm hidx)

end CloseDirection
end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 6: `ColoredTuran.PaulsenLinearAlgebra`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Paulsen's five-circle linear algebra obstruction.

The manuscript appendix proves that five pairwise non-intriguing circles
cannot exist by translating them to five vectors in `R^4` with Gram values
`1` on the diagonal and in `(-1, 0)` off the diagonal for a symmetric
indefinite bilinear form.  This module formalizes the circle-vector
calculation from centers/radii and distance inequalities, plus the
linear-algebraic contradiction.  The remaining Euclidean boundary is proving
that the manuscript's non-intriguing circle relation supplies those distance
inequalities.
-/

namespace Lollipop
namespace TheoremOneEndToEnd
namespace PaulsenLinearAlgebra

open BigOperators

abbrev R4 := Fin 4 → ℝ

abbrev R2 := Fin 2 → ℝ

/-- The Euclidean dot product on the coordinate model `Fin 2 -> R`. -/
def dot2 (x y : R2) : ℝ :=
  x 0 * y 0 + x 1 * y 1

/-- Squared norm in the coordinate model `Fin 2 -> R`. -/
def normSq2 (x : R2) : ℝ :=
  dot2 x x

/-- Squared Euclidean distance in the coordinate model `Fin 2 -> R`. -/
def distSq2 (x y : R2) : ℝ :=
  normSq2 (x - y)

theorem distSq2_symm (x y : R2) :
    distSq2 x y = distSq2 y x := by
  unfold distSq2 normSq2 dot2
  simp [Pi.sub_apply]
  ring

/-- Paulsen's obtuse-intersection distance condition for two circles. -/
def circleObtuseCondition (r s : ℝ) (x y : R2) : Prop :=
  r ^ 2 + s ^ 2 < distSq2 x y ∧ distSq2 x y < (r + s) ^ 2

/-- The circle relation corresponding to the manuscript's "intriguing"
condition at the level needed by Paulsen's appendix: a pair is intriguing
unless it satisfies the strict obtuse-intersection distance condition. -/
def circleIntriguingPair (r s : ℝ) (x y : R2) : Prop :=
  ¬ circleObtuseCondition r s x y

/-- The canonical circle-coordinate intriguing relation on an indexed family. -/
def circleIntriguing {V : Type*}
    (center : V → R2) (radius : V → ℝ) (i j : V) : Prop :=
  circleIntriguingPair (radius i) (radius j) (center i) (center j)

theorem circleObtuseCondition_symm
    (r s : ℝ) (x y : R2) :
    circleObtuseCondition r s x y ↔
      circleObtuseCondition s r y x := by
  unfold circleObtuseCondition
  rw [distSq2_symm y x]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2]
  · intro h
    constructor <;> nlinarith [h.1, h.2]

theorem circleIntriguingPair_symm
    (r s : ℝ) (x y : R2) :
    circleIntriguingPair r s x y ↔ circleIntriguingPair s r y x := by
  unfold circleIntriguingPair
  rw [circleObtuseCondition_symm]

theorem circleIntriguing_symm {V : Type*}
    (center : V → R2) (radius : V → ℝ) (i j : V) :
    circleIntriguing center radius i j ↔ circleIntriguing center radius j i := by
  exact circleIntriguingPair_symm (radius i) (radius j) (center i) (center j)

theorem circleObtuseCondition_of_not_circleIntriguing {V : Type*}
    (center : V → R2) (radius : V → ℝ) {i j : V}
    (h : ¬ circleIntriguing center radius i j) :
    circleObtuseCondition (radius i) (radius j) (center i) (center j) := by
  classical
  exact of_not_not h

/-- Algebraic case split for the formal intriguing-circle relation.

Since `circleIntriguingPair` is the negation of the open obtuse-distance
interval, an intriguing pair lies on one of the two closed sides of that
interval. -/
theorem circleIntriguingPair_iff_distSq2_le_or_radius_add_sq_le
    (r s : ℝ) (x y : R2) :
    circleIntriguingPair r s x y ↔
      distSq2 x y ≤ r ^ 2 + s ^ 2 ∨
        (r + s) ^ 2 ≤ distSq2 x y := by
  unfold circleIntriguingPair circleObtuseCondition
  constructor
  · intro h
    by_cases hleft : distSq2 x y ≤ r ^ 2 + s ^ 2
    · exact Or.inl hleft
    · have hleft_lt : r ^ 2 + s ^ 2 < distSq2 x y :=
        lt_of_not_ge hleft
      right
      by_contra hright
      have hright_lt : distSq2 x y < (r + s) ^ 2 :=
        lt_of_not_ge hright
      exact h ⟨hleft_lt, hright_lt⟩
  · rintro (hleft | hright) ⟨hleft_lt, hright_lt⟩
    · exact (not_lt_of_ge hleft) hleft_lt
    · exact (not_lt_of_ge hright) hright_lt

/-- Indexed form of
`circleIntriguingPair_iff_distSq2_le_or_radius_add_sq_le`. -/
theorem circleIntriguing_iff_distSq2_le_or_radius_add_sq_le {V : Type*}
    (center : V → R2) (radius : V → ℝ) (i j : V) :
    circleIntriguing center radius i j ↔
      distSq2 (center i) (center j) ≤ radius i ^ 2 + radius j ^ 2 ∨
        (radius i + radius j) ^ 2 ≤ distSq2 (center i) (center j) := by
  exact
    circleIntriguingPair_iff_distSq2_le_or_radius_add_sq_le
      (radius i) (radius j) (center i) (center j)

/-- Paulsen's symmetric bilinear form on `R^4`, written as
`(α, β, x₁, x₂)`. -/
noncomputable def lorentzForm (x y : R4) : ℝ :=
  (2 : ℝ)⁻¹ * x 0 * y 1 +
    (2 : ℝ)⁻¹ * x 1 * y 0 +
      x 2 * y 2 + x 3 * y 3

/-- The vector attached to a circle with center `x` and radius `r` in
Paulsen's appendix: `(1/r) * (1, r^2 - |x|^2, x)`. -/
noncomputable def circleVec (r : ℝ) (x : R2) : R4
  | 0 => r⁻¹
  | 1 => r⁻¹ * (r ^ 2 - normSq2 x)
  | 2 => r⁻¹ * x 0
  | 3 => r⁻¹ * x 1

@[simp]
theorem circleVec_zero (r : ℝ) (x : R2) :
    circleVec r x 0 = r⁻¹ := rfl

@[simp]
theorem circleVec_one (r : ℝ) (x : R2) :
    circleVec r x 1 = r⁻¹ * (r ^ 2 - normSq2 x) := rfl

@[simp]
theorem circleVec_two (r : ℝ) (x : R2) :
    circleVec r x 2 = r⁻¹ * x 0 := rfl

@[simp]
theorem circleVec_three (r : ℝ) (x : R2) :
    circleVec r x 3 = r⁻¹ * x 1 := rfl

theorem circleVec_first_pos {r : ℝ} (hr : 0 < r) (x : R2) :
    0 < circleVec r x 0 := by
  simp [inv_pos.mpr hr]

/-- Direct calculation: Paulsen's vector has Gram value `1` with itself. -/
theorem lorentzForm_circleVec_self {r : ℝ} (x : R2) (hr : r ≠ 0) :
    lorentzForm (circleVec r x) (circleVec r x) = 1 := by
  unfold lorentzForm circleVec normSq2 dot2
  field_simp [hr]
  ring

/-- Direct calculation of the off-diagonal Gram value for two circle vectors. -/
theorem lorentzForm_circleVec_pair
    {r s : ℝ} (x y : R2) (hr : r ≠ 0) (hs : s ≠ 0) :
    lorentzForm (circleVec r x) (circleVec s y) =
      (r ^ 2 + s ^ 2 - distSq2 x y) / (2 * r * s) := by
  unfold lorentzForm circleVec distSq2 normSq2 dot2
  field_simp [hr, hs]
  simp [Pi.sub_apply]
  ring_nf

/-- The lower distance inequality in Paulsen's obtuse-intersection condition
forces the off-diagonal Gram value to be negative. -/
theorem lorentzForm_circleVec_pair_neg
    {r s : ℝ} (x y : R2) (hr : 0 < r) (hs : 0 < s)
    (hdist : r ^ 2 + s ^ 2 < distSq2 x y) :
    lorentzForm (circleVec r x) (circleVec s y) < 0 := by
  rw [lorentzForm_circleVec_pair x y (ne_of_gt hr) (ne_of_gt hs)]
  have hden : 0 < 2 * r * s := by positivity
  have hnum : r ^ 2 + s ^ 2 - distSq2 x y < 0 := by linarith
  exact div_neg_of_neg_of_pos hnum hden

/-- The upper distance inequality in Paulsen's obtuse-intersection condition
forces the off-diagonal Gram value to be greater than `-1`. -/
theorem lorentzForm_circleVec_pair_gt_neg_one
    {r s : ℝ} (x y : R2) (hr : 0 < r) (hs : 0 < s)
    (hdist : distSq2 x y < (r + s) ^ 2) :
    -1 < lorentzForm (circleVec r x) (circleVec s y) := by
  rw [lorentzForm_circleVec_pair x y (ne_of_gt hr) (ne_of_gt hs)]
  have hden : 0 < 2 * r * s := by positivity
  have hnum : -(2 * r * s) < r ^ 2 + s ^ 2 - distSq2 x y := by
    nlinarith
  have hdiv := div_lt_div_of_pos_right hnum hden
  have hminus : (-(2 * r * s)) / (2 * r * s) = -1 := by
    field_simp [ne_of_gt hden]
  linarith

theorem lorentzForm_symm (x y : R4) :
    lorentzForm x y = lorentzForm y x := by
  unfold lorentzForm
  ring_nf

theorem lorentzForm_add_left (x y z : R4) :
    lorentzForm (x + y) z = lorentzForm x z + lorentzForm y z := by
  unfold lorentzForm
  simp [Pi.add_apply]
  ring_nf

theorem lorentzForm_add_right (x y z : R4) :
    lorentzForm x (y + z) = lorentzForm x y + lorentzForm x z := by
  rw [lorentzForm_symm x (y + z), lorentzForm_add_left, lorentzForm_symm y x,
    lorentzForm_symm z x]

theorem lorentzForm_smul_left (a : ℝ) (x y : R4) :
    lorentzForm (a • x) y = a * lorentzForm x y := by
  unfold lorentzForm
  simp [Pi.smul_apply]
  ring_nf

theorem lorentzForm_smul_right (a : ℝ) (x y : R4) :
    lorentzForm x (a • y) = a * lorentzForm x y := by
  rw [lorentzForm_symm x (a • y), lorentzForm_smul_left, lorentzForm_symm y x]

theorem lorentzForm_sum_left {ι : Type*}
    (s : Finset ι) (f : ι → R4) (w : R4) :
    lorentzForm (∑ i ∈ s, f i) w = ∑ i ∈ s, lorentzForm (f i) w := by
  classical
  refine Finset.induction_on s ?base ?step
  · simp [lorentzForm]
  · intro a s has hs
    simp [has, hs, lorentzForm_add_left]

theorem lorentzForm_sum_right {ι : Type*}
    (s : Finset ι) (w : R4) (f : ι → R4) :
    lorentzForm w (∑ i ∈ s, f i) = ∑ i ∈ s, lorentzForm w (f i) := by
  calc
    lorentzForm w (∑ i ∈ s, f i) =
        lorentzForm (∑ i ∈ s, f i) w := lorentzForm_symm w _
    _ = ∑ i ∈ s, lorentzForm (f i) w := lorentzForm_sum_left s f w
    _ = ∑ i ∈ s, lorentzForm w (f i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact lorentzForm_symm (f i) w

theorem lorentzForm_weighted_sum_left {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (f : ι → R4) (w : R4) :
    lorentzForm (∑ i ∈ s, a i • f i) w =
      ∑ i ∈ s, a i * lorentzForm (f i) w := by
  rw [lorentzForm_sum_left]
  apply Finset.sum_congr rfl
  intro i _hi
  exact lorentzForm_smul_left (a i) (f i) w

theorem lorentzForm_weighted_sum_right {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (w : R4) (f : ι → R4) :
    lorentzForm w (∑ i ∈ s, a i • f i) =
      ∑ i ∈ s, a i * lorentzForm w (f i) := by
  calc
    lorentzForm w (∑ i ∈ s, a i • f i) =
        lorentzForm (∑ i ∈ s, a i • f i) w := lorentzForm_symm w _
    _ = ∑ i ∈ s, a i * lorentzForm (f i) w :=
        lorentzForm_weighted_sum_left s a f w
    _ = ∑ i ∈ s, a i * lorentzForm w (f i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [lorentzForm_symm (f i) w]

theorem lorentzForm_weighted_sum_sum {ι κ : Type*}
    (s : Finset ι) (t : Finset κ)
    (a : ι → ℝ) (f : ι → R4) (g : κ → R4) :
    lorentzForm (∑ i ∈ s, a i • f i) (∑ j ∈ t, g j) =
      ∑ i ∈ s, ∑ j ∈ t, a i * lorentzForm (f i) (g j) := by
  rw [lorentzForm_weighted_sum_left]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [lorentzForm_sum_right]
  rw [Finset.mul_sum]

/-- A finite sum of strictly negative real terms is strictly negative when the
indexing finset is nonempty. -/
theorem Finset.sum_lt_zero_of_nonempty_of_forall_neg {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ s, f i < 0) :
    (∑ i ∈ s, f i) < 0 := by
  have hpos :
      0 < ∑ i ∈ s, -f i := by
    exact Finset.sum_pos (fun i hi => neg_pos.mpr (hf i hi)) hs
  have hneg : 0 < -(∑ i ∈ s, f i) := by
    simpa [Finset.sum_neg_distrib] using hpos
  exact neg_pos.mp hneg

theorem Finset.sum_lt_zero_of_nonempty_of_forall_neg₂ {ι κ : Type*}
    {s : Finset ι} {t : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → κ → ℝ)
    (hf : ∀ i ∈ s, ∀ j ∈ t, f i j < 0) :
    (∑ i ∈ s, ∑ j ∈ t, f i j) < 0 := by
  refine Finset.sum_lt_zero_of_nonempty_of_forall_neg hs
    (fun i => ∑ j ∈ t, f i j) ?_
  intro i hi
  exact Finset.sum_lt_zero_of_nonempty_of_forall_neg ht
    (fun j => f i j) (hf i hi)

/-- The contradiction in Paulsen's proof once a nontrivial relation has already
been split into positive coefficients on two disjoint nonempty sides, and the
left side has at most two vectors. -/
theorem splitRelation_contradiction
    (v : Fin 5 → R4)
    (hself : ∀ i : Fin 5, lorentzForm (v i) (v i) = 1)
    (hneg : ∀ i j : Fin 5, i ≠ j → lorentzForm (v i) (v j) < 0)
    (hgt_neg_one : ∀ i j : Fin 5, i ≠ j → -1 < lorentzForm (v i) (v j))
    (P N : Finset (Fin 5))
    (hPnonempty : P.Nonempty) (hNnonempty : N.Nonempty)
    (hdisj : Disjoint P N) (hPle : P.card ≤ 2)
    (a b : Fin 5 → ℝ)
    (ha : ∀ i ∈ P, 0 < a i)
    (hb : ∀ j ∈ N, 0 < b j)
    (hrel : ∑ i ∈ P, a i • v i = ∑ j ∈ N, b j • v j) :
    False := by
  classical
  let w : R4 := ∑ i ∈ P, v i
  have hleft_pos :
      0 < lorentzForm (∑ i ∈ P, a i • v i) w := by
    have hPcard_pos : 0 < P.card := Finset.card_pos.mpr hPnonempty
    have hPcard : P.card = 1 ∨ P.card = 2 := by omega
    rcases hPcard with hcard | hcard
    · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
      subst P
      simp only [Finset.sum_singleton] at *
      have hw : w = v p := by simp [w]
      rw [hw, lorentzForm_smul_left, hself p]
      simpa using ha p (by simp)
    · obtain ⟨p, q, hpq, hP⟩ := Finset.card_eq_two.mp hcard
      subst P
      have hpq' : p ≠ q := hpq
      have hqp' : q ≠ p := Ne.symm hpq
      have hpair_symm : lorentzForm (v q) (v p) = lorentzForm (v p) (v q) :=
        lorentzForm_symm (v q) (v p)
      have hfactor_pos :
          0 < 1 + lorentzForm (v p) (v q) := by
        linarith [hgt_neg_one p q hpq']
      have hcoef_pos : 0 < a p + a q := by
        exact add_pos (ha p (by simp [hpq'])) (ha q (by simp [hqp']))
      have hleft_eq :
          lorentzForm (∑ i ∈ ({p, q} : Finset (Fin 5)), a i • v i) w =
            (a p + a q) * (1 + lorentzForm (v p) (v q)) := by
        have hw : w = v p + v q := by
          simp [w, hpq']
        rw [hw]
        simp [hpq', lorentzForm_add_left, lorentzForm_add_right,
          lorentzForm_smul_left, hself p, hself q, hpair_symm]
        ring
      rw [hleft_eq]
      exact mul_pos hcoef_pos hfactor_pos
  have hright_neg :
      lorentzForm (∑ j ∈ N, b j • v j) w < 0 := by
    unfold w
    rw [lorentzForm_weighted_sum_sum]
    exact Finset.sum_lt_zero_of_nonempty_of_forall_neg₂ hNnonempty hPnonempty
      (fun j i => b j * lorentzForm (v j) (v i)) (by
        intro j hj i hi
        have hji : j ≠ i := by
          intro hji
          subst i
          exact (Finset.disjoint_left.mp hdisj) hi hj
        exact mul_neg_of_pos_of_neg (hb j hj) (hneg j i hji))
  have heq :
      lorentzForm (∑ i ∈ P, a i • v i) w =
        lorentzForm (∑ j ∈ N, b j • v j) w := by
    rw [hrel]
  linarith

/-- Any five vectors in Paulsen's `R^4` are linearly dependent. -/
theorem not_linearIndependent_fin_five_R4 (v : Fin 5 → R4) :
    ¬ LinearIndependent ℝ v := by
  intro hlin
  have hle := hlin.fintype_card_le_finrank
  norm_num [R4, Module.finrank_fin_fun] at hle

/-- A nonzero linear relation among vectors whose first coordinates are all
positive has at least one positive and one negative coefficient.  This is the
formal version of the appendix sentence justifying that both sides of the
split relation are nonempty. -/
theorem relation_has_pos_and_neg_coefficients
    (v : Fin 5 → R4) (hfirst : ∀ i : Fin 5, 0 < v i 0)
    (c : Fin 5 → ℝ)
    (hrel : ∑ i : Fin 5, c i • v i = 0)
    (hnonzero : ∃ i : Fin 5, c i ≠ 0) :
    (∃ i : Fin 5, 0 < c i) ∧ (∃ i : Fin 5, c i < 0) := by
  classical
  have hcoord : ∑ i : Fin 5, c i * v i 0 = 0 := by
    have h := congr_fun hrel 0
    simpa [Finset.sum_apply, Pi.smul_apply] using h
  have hweighted_nonzero : ∃ i : Fin 5, c i * v i 0 ≠ 0 := by
    rcases hnonzero with ⟨i, hi⟩
    refine ⟨i, mul_ne_zero hi ?_⟩
    exact ne_of_gt (hfirst i)
  have hweighted_nonzero_univ :
      ∃ i ∈ (Finset.univ : Finset (Fin 5)), c i * v i 0 ≠ 0 := by
    rcases hweighted_nonzero with ⟨i, hi⟩
    exact ⟨i, by simp, hi⟩
  constructor
  · rcases Finset.exists_pos_of_sum_zero_of_exists_nonzero
      (s := (Finset.univ : Finset (Fin 5)))
      (fun i : Fin 5 => c i * v i 0) hcoord hweighted_nonzero_univ with
      ⟨i, _hi_mem, hi⟩
    refine ⟨i, ?_⟩
    nlinarith [hfirst i]
  · have hcoord_neg : ∑ i : Fin 5, -(c i * v i 0) = 0 := by
      simp [Finset.sum_neg_distrib, hcoord]
    have hweighted_neg_nonzero :
        ∃ i ∈ (Finset.univ : Finset (Fin 5)), -(c i * v i 0) ≠ 0 := by
      rcases hweighted_nonzero with ⟨i, hi⟩
      exact ⟨i, by simp, neg_ne_zero.mpr hi⟩
    rcases Finset.exists_pos_of_sum_zero_of_exists_nonzero
      (s := (Finset.univ : Finset (Fin 5)))
      (fun i : Fin 5 => -(c i * v i 0))
      hcoord_neg hweighted_neg_nonzero with ⟨i, _hi_mem, hi⟩
    refine ⟨i, ?_⟩
    nlinarith [hfirst i]

/-- Split a nonzero relation into positive coefficients on the positive and
negative coefficient supports. -/
theorem relation_split
    (v : Fin 5 → R4) (c : Fin 5 → ℝ)
    (hrel : ∑ i : Fin 5, c i • v i = 0) :
    let P : Finset (Fin 5) := Finset.univ.filter (fun i => 0 < c i)
    let N : Finset (Fin 5) := Finset.univ.filter (fun i => c i < 0)
    Disjoint P N ∧
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j := by
  classical
  intro P N
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    simp [P] at hiP
    simp [N] at hiN
    linarith
  have hterm_zero :
      ∀ i : Fin 5, i ∉ P → i ∉ N → c i = 0 := by
    intro i hiP hiN
    simp [P] at hiP
    simp [N] at hiN
    linarith
  have hsum_union :
      (∑ i : Fin 5, c i • v i) =
        ∑ i ∈ P ∪ N, c i • v i := by
    symm
    refine Finset.sum_subset (Finset.subset_univ (P ∪ N)) ?_
    intro i _hiuniv hi_union
    have hiP : i ∉ P := by
      intro hi
      exact hi_union (Finset.mem_union.mpr (Or.inl hi))
    have hiN : i ∉ N := by
      intro hi
      exact hi_union (Finset.mem_union.mpr (Or.inr hi))
    simp [hterm_zero i hiP hiN]
  have hsumPN :
      (∑ i ∈ P, c i • v i) + (∑ i ∈ N, c i • v i) = 0 := by
    rw [hsum_union, Finset.sum_union hdisj] at hrel
    simpa using hrel
  have hP_eq_negN :
      (∑ i ∈ P, c i • v i) = -(∑ i ∈ N, c i • v i) := by
    simpa [eq_neg_iff_add_eq_zero] using hsumPN
  refine ⟨hdisj, ?_⟩
  rw [hP_eq_negN]
  simp [Finset.sum_neg_distrib]

/-- The abstract five-vector obstruction behind Paulsen's forced-intriguing
pair theorem.  The Euclidean circle computation supplies the hypotheses:
positive first coordinate, diagonal Gram value `1`, and off-diagonal Gram
values in `(-1, 0)`. -/
theorem no_paulsen_gram_five
    (v : Fin 5 → R4)
    (hfirst : ∀ i : Fin 5, 0 < v i 0)
    (hself : ∀ i : Fin 5, lorentzForm (v i) (v i) = 1)
    (hneg : ∀ i j : Fin 5, i ≠ j → lorentzForm (v i) (v j) < 0)
    (hgt_neg_one : ∀ i j : Fin 5, i ≠ j → -1 < lorentzForm (v i) (v j)) :
    False := by
  classical
  obtain ⟨c, hrel, hnonzero⟩ :=
    Fintype.not_linearIndependent_iff.mp (not_linearIndependent_fin_five_R4 v)
  let P : Finset (Fin 5) := Finset.univ.filter (fun i => 0 < c i)
  let N : Finset (Fin 5) := Finset.univ.filter (fun i => c i < 0)
  have hposneg := relation_has_pos_and_neg_coefficients v hfirst c hrel hnonzero
  have hPnonempty : P.Nonempty := by
    rcases hposneg.1 with ⟨i, hi⟩
    exact ⟨i, by simp [P, hi]⟩
  have hNnonempty : N.Nonempty := by
    rcases hposneg.2 with ⟨i, hi⟩
    exact ⟨i, by simp [N, hi]⟩
  have hsplit := relation_split v c hrel
  dsimp only at hsplit
  change
    Disjoint P N ∧
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j at hsplit
  have hdisj : Disjoint P N := hsplit.1
  have hrel_split :
      (∑ i ∈ P, c i • v i) = ∑ j ∈ N, (-c j) • v j :=
    hsplit.2
  have haP : ∀ i ∈ P, 0 < c i := by
    intro i hi
    simpa [P] using hi
  have hbN : ∀ j ∈ N, 0 < -c j := by
    intro j hj
    have : c j < 0 := by simpa [N] using hj
    linarith
  have hcard_union_le : (P ∪ N).card ≤ 5 := by
    simpa using Finset.card_le_univ (P ∪ N)
  have hcard_sum_le : P.card + N.card ≤ 5 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact hcard_union_le
  have hsmall : P.card ≤ 2 ∨ N.card ≤ 2 := by
    by_contra h
    push Not at h
    omega
  rcases hsmall with hPle | hNle
  · exact splitRelation_contradiction v hself hneg hgt_neg_one
      P N hPnonempty hNnonempty hdisj hPle c (fun j => -c j)
      haP hbN hrel_split
  · have hrel_split_symm :
        (∑ j ∈ N, (-c j) • v j) = ∑ i ∈ P, c i • v i :=
      hrel_split.symm
    exact splitRelation_contradiction v hself hneg hgt_neg_one
      N P hNnonempty hPnonempty hdisj.symm hNle
      (fun j => -c j) c hbN haP hrel_split_symm

universe u

/-- Data supplied by the Euclidean circle calculation for one five-element
subset.  If all five indexed objects were non-intriguing, these vectors would
satisfy Paulsen's impossible Gram conditions. -/
structure FiveSetPaulsenData {V : Type u} (intriguing : V → V → Prop)
    (t : Finset V) where
  enumerate : Fin 5 ≃ {x : V // x ∈ t}
  vec : Fin 5 → R4
  first_pos : ∀ i : Fin 5, 0 < vec i 0
  self_gram : ∀ i : Fin 5, lorentzForm (vec i) (vec i) = 1
  nonintriguing_gram_neg :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        lorentzForm (vec i) (vec j) < 0
  nonintriguing_gram_gt_neg_one :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        -1 < lorentzForm (vec i) (vec j)

/-- Circle-coordinate data for one five-element subset, in exactly the
distance-inequality form used by Paulsen's appendix. -/
structure FiveSetPaulsenCircleData {V : Type u} (intriguing : V → V → Prop)
    (t : Finset V) where
  enumerate : Fin 5 ≃ {x : V // x ∈ t}
  center : Fin 5 → R2
  radius : Fin 5 → ℝ
  radius_pos : ∀ i : Fin 5, 0 < radius i
  nonintriguing_dist_low :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        radius i ^ 2 + radius j ^ 2 < distSq2 (center i) (center j)
  nonintriguing_dist_high :
    ∀ i j : Fin 5, i ≠ j →
      ¬ intriguing (enumerate i) (enumerate j) →
        distSq2 (center i) (center j) < (radius i + radius j) ^ 2

namespace FiveSetPaulsenData

/-- Build Paulsen five-set data from the circle-coordinate calculation in the
appendix.  The two distance inequalities are exactly
`r_i^2 + r_j^2 < |x_i - x_j|^2 < (r_i + r_j)^2` for non-intriguing pairs. -/
noncomputable def ofCircleCoordinates
    {V : Type u} {intriguing : V → V → Prop} {t : Finset V}
    (enumerate : Fin 5 ≃ {x : V // x ∈ t})
    (center : Fin 5 → R2) (radius : Fin 5 → ℝ)
    (radius_pos : ∀ i : Fin 5, 0 < radius i)
    (nonintriguing_dist_low :
      ∀ i j : Fin 5, i ≠ j →
        ¬ intriguing (enumerate i) (enumerate j) →
          radius i ^ 2 + radius j ^ 2 < distSq2 (center i) (center j))
    (nonintriguing_dist_high :
      ∀ i j : Fin 5, i ≠ j →
        ¬ intriguing (enumerate i) (enumerate j) →
          distSq2 (center i) (center j) < (radius i + radius j) ^ 2) :
    FiveSetPaulsenData intriguing t where
  enumerate := enumerate
  vec := fun i => circleVec (radius i) (center i)
  first_pos := by
    intro i
    exact circleVec_first_pos (radius_pos i) (center i)
  self_gram := by
    intro i
    exact lorentzForm_circleVec_self (center i) (ne_of_gt (radius_pos i))
  nonintriguing_gram_neg := by
    intro i j hij hnon
    exact lorentzForm_circleVec_pair_neg (center i) (center j)
      (radius_pos i) (radius_pos j)
      (nonintriguing_dist_low i j hij hnon)
  nonintriguing_gram_gt_neg_one := by
    intro i j hij hnon
    exact lorentzForm_circleVec_pair_gt_neg_one (center i) (center j)
      (radius_pos i) (radius_pos j)
      (nonintriguing_dist_high i j hij hnon)

end FiveSetPaulsenData

namespace FiveSetPaulsenCircleData

/-- Convert circle-coordinate five-set data to Paulsen vector data. -/
noncomputable def toFiveSetPaulsenData
    {V : Type u} {intriguing : V → V → Prop} {t : Finset V}
    (D : FiveSetPaulsenCircleData intriguing t) :
    FiveSetPaulsenData intriguing t :=
  FiveSetPaulsenData.ofCircleCoordinates
    D.enumerate D.center D.radius D.radius_pos
    D.nonintriguing_dist_low D.nonintriguing_dist_high

end FiveSetPaulsenCircleData

/-- Paulsen vector data on every five-element subset proves the manuscript's
forbidden-pair fact: every five contain an intriguing pair. -/
theorem intriguing_pair_in_every_five_of_paulsen_data
    {V : Type u} [DecidableEq V]
    (intriguing : V → V → Prop)
    (hdata : ∀ t : Finset V, t.card = 5 →
      FiveSetPaulsenData intriguing t) :
    ∀ t : Finset V, t.card = 5 →
      ∃ x ∈ t, ∃ y ∈ t, x ≠ y ∧ intriguing x y := by
  classical
  intro t ht
  by_contra hnone
  have hnot_intr :
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ intriguing x y := by
    intro x hx y hy hxy hxy_intr
    exact hnone ⟨x, hx, y, hy, hxy, hxy_intr⟩
  let D := hdata t ht
  have hneg :
      ∀ i j : Fin 5, i ≠ j → lorentzForm (D.vec i) (D.vec j) < 0 := by
    intro i j hij
    refine D.nonintriguing_gram_neg i j hij ?_
    have hne_val : (D.enumerate i : V) ≠ D.enumerate j := by
      intro hval
      exact hij (D.enumerate.injective (Subtype.ext hval))
    exact hnot_intr (D.enumerate i) (D.enumerate i).property
      (D.enumerate j) (D.enumerate j).property hne_val
  have hgt :
      ∀ i j : Fin 5, i ≠ j → -1 < lorentzForm (D.vec i) (D.vec j) := by
    intro i j hij
    refine D.nonintriguing_gram_gt_neg_one i j hij ?_
    have hne_val : (D.enumerate i : V) ≠ D.enumerate j := by
      intro hval
      exact hij (D.enumerate.injective (Subtype.ext hval))
    exact hnot_intr (D.enumerate i) (D.enumerate i).property
      (D.enumerate j) (D.enumerate j).property hne_val
  exact no_paulsen_gram_five D.vec D.first_pos D.self_gram hneg hgt

end PaulsenLinearAlgebra
end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 7: `ColoredTuran.GeometricPaulsenReduction`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Geometric-input reduction with Paulsen's five-circle obstruction internalized.

`GeometricReduction.lean` asks directly for the manuscript fact that every
five lollipops contain an intriguing pair.  This module replaces that one
field by Paulsen vector data, by circle-coordinate distance data on each
five-element subset, or by one global circle-coordinate model per arrangement,
and derives the forbidden-pair field using
`PaulsenLinearAlgebra.no_paulsen_gram_five`.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

open BigOperators

universe u

/-- Geometric upper-bound data where the `K_5`-free input is supplied through
Paulsen's linear-algebra witnesses rather than as a bare hypothesis. -/
structure PairwisePaulsenGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  paulsen_data_in_every_five :
    ∀ t : Finset (Fin nNat), t.card = 5 →
      PaulsenLinearAlgebra.FiveSetPaulsenData intriguing t
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Geometric upper-bound data where Paulsen's five-set input is supplied in
the circle-coordinate form used in the appendix: centers, positive radii, and
the two obtuse-intersection distance inequalities for non-intriguing pairs. -/
structure PairwisePaulsenCircleGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  paulsen_circle_data_in_every_five :
    ∀ t : Finset (Fin nNat), t.card = 5 →
      PaulsenLinearAlgebra.FiveSetPaulsenCircleData intriguing t
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Geometric upper-bound data with one global circle-coordinate model.  From
global centers/radii and the two distance inequalities for every
non-intriguing pair, Lean builds the five-set Paulsen circle data for every
five-subset. -/
structure PairwiseGlobalCircleGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  intriguing : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  [intriguing_decidable : DecidableRel intriguing]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  intriguing_symm : ∀ i j : Fin nNat, intriguing i j ↔ intriguing j i
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  nonintriguing_dist_low :
    ∀ i j : Fin nNat, i ≠ j → ¬ intriguing i j →
      radius i ^ 2 + radius j ^ 2 <
        PaulsenLinearAlgebra.distSq2 (center i) (center j)
  nonintriguing_dist_high :
    ∀ i j : Fin nNat, i ≠ j → ¬ intriguing i j →
      PaulsenLinearAlgebra.distSq2 (center i) (center j) <
        (radius i + radius j) ^ 2
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j → intriguing i j → cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j → intriguing i j → cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Geometric upper-bound data with one global circle-coordinate model and the
intriguing relation fixed to the canonical Paulsen circle relation
`circleIntriguing center radius`.  This removes the separate
non-intriguing-distance implication field: it is true by definition of the
relation. -/
structure PairwiseCanonicalCircleGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  close : Fin nNat → Fin nNat → Prop
  [close_decidable : DecidableRel close]
  close_symm : ∀ i j : Fin nNat, close i j ↔ close j i
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close : ∀ i j : Fin nNat, i < j → close i j → cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j → close i j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 4
  close_pair_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ close i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Strongest current upper-bound data: one global circle-coordinate model for
the circle part and one global normalized direction model for stems.  The
`close` and `intriguing` relations are fixed to the canonical relations from
those coordinates; Lean derives both finite forbidden-pair facts. -/
structure PairwiseCanonicalGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  direction_order_data_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      CloseDirection.FourSetCyclicOrderData direction t
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_general : ∀ i j : Fin nNat, i < j → cross i j ≤ 7
  cross_le_close :
    ∀ i j : Fin nNat, i < j →
      CloseDirection.cyclicClose direction i j →
        cross i j ≤ 5
  cross_le_intriguing :
    ∀ i j : Fin nNat, i < j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 5
  cross_le_close_intriguing :
    ∀ i j : Fin nNat, i < j →
      CloseDirection.cyclicClose direction i j →
      PaulsenLinearAlgebra.circleIntriguing center radius i j →
        cross i j ≤ 4
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- The manuscript's four pairwise crossing-count cases as one canonical
table, after `close` and `intriguing` have both been fixed to their coordinate
definitions. -/
noncomputable def canonicalCrossingCaseBound
    {n : Nat}
    (direction : Fin n → ℝ)
    (center : Fin n → PaulsenLinearAlgebra.R2)
    (radius : Fin n → ℝ)
    (i j : Fin n) : Rat := by
  classical
  exact
    if CloseDirection.cyclicClose direction i j then
      if PaulsenLinearAlgebra.circleIntriguing center radius i j then 4 else 5
    else if PaulsenLinearAlgebra.circleIntriguing center radius i j then
      5
    else
      7

/-- Stronger canonical geometric upper-bound data where the pointwise
crossing estimate is supplied as the single four-case table
`canonicalCrossingCaseBound`.  Lean derives the four separate crossing
inequality fields used by the older geometric reduction. -/
structure PairwiseCanonicalCaseBoundGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  direction_order_data_in_every_four :
    ∀ t : Finset (Fin nNat), t.card = 4 →
      CloseDirection.FourSetCyclicOrderData direction t
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_case :
    ∀ i j : Fin nNat, i < j →
      cross i j ≤ canonicalCrossingCaseBound direction center radius i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Strongest current coordinate upper-bound data.  It supplies one global
circle-coordinate model, one global normalized direction map, and one
canonical four-case crossing table.  Lean now derives close-pair-in-four by
sorting each four-subset, so no per-four direction-order certificate is
needed. -/
structure PairwiseCanonicalCoordinateGeometricLollipopUpper where
  nNat : Nat
  crossings : Rat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  cross : Fin nNat → Fin nNat → Rat
  crossings_le_pairSum : crossings ≤ pairSum nNat cross
  cross_le_case :
    ∀ i j : Fin nNat, i < j →
      cross i j ≤ canonicalCrossingCaseBound direction center radius i j
  regions_eq : regions = crossings + (nNat : Rat) + 1

/-- Strongest current exact pairwise-count upper data.  It supplies pairwise
crossing counts directly and the generic region equation in the exact
pair-sum form, so Lean fills the older total-crossing field and
`crossings <= pairSum cross` automatically. -/
structure PairwiseCanonicalExactCoordinateGeometricLollipopUpper where
  nNat : Nat
  regions : Rat
  center : Fin nNat → PaulsenLinearAlgebra.R2
  radius : Fin nNat → ℝ
  radius_pos : ∀ i : Fin nNat, 0 < radius i
  direction : Fin nNat → ℝ
  direction_nonneg : ∀ i : Fin nNat, 0 ≤ direction i
  direction_lt_one : ∀ i : Fin nNat, direction i < 1
  cross : Fin nNat → Fin nNat → Rat
  cross_le_case :
    ∀ i j : Fin nNat, i < j →
      cross i j ≤ canonicalCrossingCaseBound direction center radius i j
  regions_eq_pairSum : regions = pairSum nNat cross + (nNat : Rat) + 1

namespace PairwisePaulsenGeometricLollipopUpper

/-- Paulsen's formalized obstruction supplies the intriguing-pair-in-five
field needed by the existing geometric reduction. -/
theorem intriguing_pair_in_every_five
    (L : PairwisePaulsenGeometricLollipopUpper) :
    ∀ t : Finset (Fin L.nNat), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ L.intriguing i j := by
  exact PaulsenLinearAlgebra.intriguing_pair_in_every_five_of_paulsen_data
    L.intriguing L.paulsen_data_in_every_five

/-- Forget the Paulsen witnesses after Lean has used them to derive the
five-set intriguing-pair theorem. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwisePaulsenGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := L.close
  intriguing := L.intriguing
  close_decidable := L.close_decidable
  intriguing_decidable := L.intriguing_decidable
  close_symm := L.close_symm
  intriguing_symm := L.intriguing_symm
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  intriguing_pair_in_every_five := L.intriguing_pair_in_every_five
  regions_eq := L.regions_eq

/-- Convert Paulsen-geometric data directly into the colored-graph certificate
used by the internalized colored Turan proof. -/
noncomputable def toPairwiseColoredGraphCertifiedLollipopUpper
    (L : PairwisePaulsenGeometricLollipopUpper) :
    PairwiseColoredGraphCertifiedLollipopUpper :=
  L.toPairwiseGeometricLollipopUpper.toPairwiseColoredGraphCertifiedLollipopUpper

end PairwisePaulsenGeometricLollipopUpper

namespace PairwisePaulsenCircleGeometricLollipopUpper

/-- Convert circle-coordinate Paulsen data to the vector-witness package. -/
noncomputable def toPairwisePaulsenGeometricLollipopUpper
    (L : PairwisePaulsenCircleGeometricLollipopUpper) :
    PairwisePaulsenGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := L.close
  intriguing := L.intriguing
  close_decidable := L.close_decidable
  intriguing_decidable := L.intriguing_decidable
  close_symm := L.close_symm
  intriguing_symm := L.intriguing_symm
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  paulsen_data_in_every_five := by
    intro t ht
    exact (L.paulsen_circle_data_in_every_five t ht).toFiveSetPaulsenData
  regions_eq := L.regions_eq

/-- Convert circle-coordinate Paulsen data into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwisePaulsenCircleGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwisePaulsenGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwisePaulsenCircleGeometricLollipopUpper

namespace PairwiseGlobalCircleGeometricLollipopUpper

/-- The five-set Paulsen circle data obtained by restricting the global
centers/radii to a five-element subset. -/
noncomputable def fiveSetPaulsenCircleData
    (L : PairwiseGlobalCircleGeometricLollipopUpper)
    (t : Finset (Fin L.nNat)) (ht : t.card = 5) :
    PaulsenLinearAlgebra.FiveSetPaulsenCircleData L.intriguing t where
  enumerate := (t.equivFinOfCardEq ht).symm
  center := fun i => L.center ((t.equivFinOfCardEq ht).symm i)
  radius := fun i => L.radius ((t.equivFinOfCardEq ht).symm i)
  radius_pos := by
    intro i
    exact L.radius_pos ((t.equivFinOfCardEq ht).symm i)
  nonintriguing_dist_low := by
    intro i j hij hnon
    have hne :
        (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat) ≠
          (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat) := by
      intro hval
      have hsub :
          ((t.equivFinOfCardEq ht).symm i : t) =
            ((t.equivFinOfCardEq ht).symm j : t) := Subtype.ext hval
      exact hij ((t.equivFinOfCardEq ht).symm.injective hsub)
    exact L.nonintriguing_dist_low
      (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat)
      (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat)
      hne hnon
  nonintriguing_dist_high := by
    intro i j hij hnon
    have hne :
        (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat) ≠
          (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat) := by
      intro hval
      have hsub :
          ((t.equivFinOfCardEq ht).symm i : t) =
            ((t.equivFinOfCardEq ht).symm j : t) := Subtype.ext hval
      exact hij ((t.equivFinOfCardEq ht).symm.injective hsub)
    exact L.nonintriguing_dist_high
      (((t.equivFinOfCardEq ht).symm i : t) : Fin L.nNat)
      (((t.equivFinOfCardEq ht).symm j : t) : Fin L.nNat)
      hne hnon

/-- Convert a global circle-coordinate model to the per-five-set
Paulsen-circle certificate package. -/
noncomputable def toPairwisePaulsenCircleGeometricLollipopUpper
    (L : PairwiseGlobalCircleGeometricLollipopUpper) :
    PairwisePaulsenCircleGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := L.close
  intriguing := L.intriguing
  close_decidable := L.close_decidable
  intriguing_decidable := L.intriguing_decidable
  close_symm := L.close_symm
  intriguing_symm := L.intriguing_symm
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  paulsen_circle_data_in_every_five := L.fiveSetPaulsenCircleData
  regions_eq := L.regions_eq

/-- Convert a global circle-coordinate model into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseGlobalCircleGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwisePaulsenCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseGlobalCircleGeometricLollipopUpper

namespace PairwiseCanonicalCircleGeometricLollipopUpper

/-- Convert the canonical circle-coordinate model to the global-circle model
with an explicit intriguing relation and explicit distance-inequality fields. -/
noncomputable def toPairwiseGlobalCircleGeometricLollipopUpper
    (L : PairwiseCanonicalCircleGeometricLollipopUpper) :
    PairwiseGlobalCircleGeometricLollipopUpper := by
  classical
  exact
    { nNat := L.nNat
      crossings := L.crossings
      regions := L.regions
      close := L.close
      intriguing := PaulsenLinearAlgebra.circleIntriguing L.center L.radius
      close_decidable := L.close_decidable
      intriguing_decidable := inferInstance
      close_symm := L.close_symm
      intriguing_symm :=
        PaulsenLinearAlgebra.circleIntriguing_symm L.center L.radius
      center := L.center
      radius := L.radius
      radius_pos := L.radius_pos
      nonintriguing_dist_low := by
        intro i j _hij hnot
        exact (PaulsenLinearAlgebra.circleObtuseCondition_of_not_circleIntriguing
          L.center L.radius hnot).1
      nonintriguing_dist_high := by
        intro i j _hij hnot
        exact (PaulsenLinearAlgebra.circleObtuseCondition_of_not_circleIntriguing
          L.center L.radius hnot).2
      cross := L.cross
      crossings_le_pairSum := L.crossings_le_pairSum
      cross_le_general := L.cross_le_general
      cross_le_close := L.cross_le_close
      cross_le_intriguing := L.cross_le_intriguing
      cross_le_close_intriguing := L.cross_le_close_intriguing
      close_pair_in_every_four := L.close_pair_in_every_four
      regions_eq := L.regions_eq }

/-- Convert the canonical circle-coordinate model into the existing geometric
upper certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalCircleGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseGlobalCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalCircleGeometricLollipopUpper

namespace PairwiseCanonicalGeometricLollipopUpper

/-- The close-pair-in-four fact follows from the checked cyclic-direction
pigeonhole theorem. -/
theorem close_pair_in_every_four
    (L : PairwiseCanonicalGeometricLollipopUpper) :
    ∀ t : Finset (Fin L.nNat), t.card = 4 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧
        CloseDirection.cyclicClose L.direction i j := by
  intro t ht
  exact (L.direction_order_data_in_every_four t ht).exists_cyclicClose_pair
    (fun i _hi => L.direction_nonneg i)
    (fun i _hi => L.direction_lt_one i)

/-- Convert canonical circle/direction data to the canonical-circle package,
forgetting that the close-pair-in-four fact was derived by Lean. -/
noncomputable def toPairwiseCanonicalCircleGeometricLollipopUpper
    (L : PairwiseCanonicalGeometricLollipopUpper) :
    PairwiseCanonicalCircleGeometricLollipopUpper where
  nNat := L.nNat
  crossings := L.crossings
  regions := L.regions
  close := CloseDirection.cyclicClose L.direction
  close_decidable := by
    classical
    exact inferInstance
  close_symm := CloseDirection.cyclicClose_symm L.direction
  center := L.center
  radius := L.radius
  radius_pos := L.radius_pos
  cross := L.cross
  crossings_le_pairSum := L.crossings_le_pairSum
  cross_le_general := L.cross_le_general
  cross_le_close := L.cross_le_close
  cross_le_intriguing := L.cross_le_intriguing
  cross_le_close_intriguing := L.cross_le_close_intriguing
  close_pair_in_every_four := L.close_pair_in_every_four
  regions_eq := L.regions_eq

/-- Convert canonical circle/direction data into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalGeometricLollipopUpper

namespace PairwiseCanonicalCaseBoundGeometricLollipopUpper

/-- Expand the single canonical pairwise crossing table into the four
pointwise crossing inequalities expected by the canonical geometric package. -/
noncomputable def toPairwiseCanonicalGeometricLollipopUpper
    (L : PairwiseCanonicalCaseBoundGeometricLollipopUpper) :
    PairwiseCanonicalGeometricLollipopUpper := by
  classical
  refine
    { nNat := L.nNat
      crossings := L.crossings
      regions := L.regions
      center := L.center
      radius := L.radius
      radius_pos := L.radius_pos
      direction := L.direction
      direction_nonneg := L.direction_nonneg
      direction_lt_one := L.direction_lt_one
      direction_order_data_in_every_four :=
        L.direction_order_data_in_every_four
      cross := L.cross
      crossings_le_pairSum := L.crossings_le_pairSum
      cross_le_general := ?_
      cross_le_close := ?_
      cross_le_intriguing := ?_
      cross_le_close_intriguing := ?_
      regions_eq := L.regions_eq }
  · intro i j hij
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (4 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc
    have h := L.cross_le_case i j hij
    by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hi
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc hi
    have h := L.cross_le_case i j hij
    simpa [canonicalCrossingCaseBound, hc, hi] using h

/-- Convert the one-table canonical package into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalCaseBoundGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalCaseBoundGeometricLollipopUpper

namespace PairwiseCanonicalCoordinateGeometricLollipopUpper

/-- Expand the single canonical crossing table into the canonical-circle
package.  The close-pair-in-four input is derived from the unordered
normalized-direction pigeonhole theorem. -/
noncomputable def toPairwiseCanonicalCircleGeometricLollipopUpper
    (L : PairwiseCanonicalCoordinateGeometricLollipopUpper) :
    PairwiseCanonicalCircleGeometricLollipopUpper := by
  classical
  refine
    { nNat := L.nNat
      crossings := L.crossings
      regions := L.regions
      close := CloseDirection.cyclicClose L.direction
      close_decidable := inferInstance
      close_symm := CloseDirection.cyclicClose_symm L.direction
      center := L.center
      radius := L.radius
      radius_pos := L.radius_pos
      cross := L.cross
      crossings_le_pairSum := L.crossings_le_pairSum
      cross_le_general := ?_
      cross_le_close := ?_
      cross_le_intriguing := ?_
      cross_le_close_intriguing := ?_
      close_pair_in_every_four := ?_
      regions_eq := L.regions_eq }
  · intro i j hij
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (4 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
    · by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
      · have h' : L.cross i j ≤ (5 : Rat) := by
          simpa [canonicalCrossingCaseBound, hc, hi] using h
        exact le_trans h' (by norm_num)
      · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc
    have h := L.cross_le_case i j hij
    by_cases hi :
        PaulsenLinearAlgebra.circleIntriguing L.center L.radius i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hi
    have h := L.cross_le_case i j hij
    by_cases hc : CloseDirection.cyclicClose L.direction i j
    · have h' : L.cross i j ≤ (4 : Rat) := by
        simpa [canonicalCrossingCaseBound, hc, hi] using h
      exact le_trans h' (by norm_num)
    · simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro i j hij hc hi
    have h := L.cross_le_case i j hij
    simpa [canonicalCrossingCaseBound, hc, hi] using h
  · intro t ht
    exact CloseDirection.exists_cyclicClose_pair_of_card_four
      L.direction ht
      (fun i _hi => L.direction_nonneg i)
      (fun i _hi => L.direction_lt_one i)

/-- Convert the coordinate package into the existing geometric upper
certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalCoordinateGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalCircleGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalCoordinateGeometricLollipopUpper

namespace PairwiseCanonicalExactCoordinateGeometricLollipopUpper

/-- Convert exact pairwise-count coordinate data to the previous coordinate
package by setting the total crossing count to the pair sum. -/
noncomputable def toPairwiseCanonicalCoordinateGeometricLollipopUpper
    (L : PairwiseCanonicalExactCoordinateGeometricLollipopUpper) :
    PairwiseCanonicalCoordinateGeometricLollipopUpper where
  nNat := L.nNat
  crossings := pairSum L.nNat L.cross
  regions := L.regions
  center := L.center
  radius := L.radius
  radius_pos := L.radius_pos
  direction := L.direction
  direction_nonneg := L.direction_nonneg
  direction_lt_one := L.direction_lt_one
  cross := L.cross
  crossings_le_pairSum := le_rfl
  cross_le_case := L.cross_le_case
  regions_eq := L.regions_eq_pairSum

/-- Convert exact pairwise-count coordinate data into the existing geometric
upper certificate. -/
noncomputable def toPairwiseGeometricLollipopUpper
    (L : PairwiseCanonicalExactCoordinateGeometricLollipopUpper) :
    PairwiseGeometricLollipopUpper :=
  L.toPairwiseCanonicalCoordinateGeometricLollipopUpper.toPairwiseGeometricLollipopUpper

end PairwiseCanonicalExactCoordinateGeometricLollipopUpper

/-- Upper certificates for every arrangement from geometric data where the
five-intriguing-pair fact is certified by Paulsen vector witnesses. -/
def PairwisePaulsenGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwisePaulsenGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from geometric data where
Paulsen's five-intriguing-pair input is supplied by circle-coordinate
distance-inequality witnesses. -/
def PairwisePaulsenCircleGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwisePaulsenCircleGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from one global circle-coordinate
model per arrangement. -/
def PairwiseGlobalCircleGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseGlobalCircleGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from one global circle-coordinate
model whose intriguing relation is the canonical Paulsen circle relation. -/
def PairwiseCanonicalCircleGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalCircleGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from canonical circle and
canonical direction coordinate data. -/
def PairwiseCanonicalGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from canonical circle/direction
coordinate data plus one canonical four-case crossing-count table. -/
def PairwiseCanonicalCaseBoundGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalCaseBoundGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from global circle coordinates,
global normalized directions, and one canonical crossing-count table. -/
def PairwiseCanonicalCoordinateGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalCoordinateGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Upper certificates for every arrangement from exact pairwise crossing
counts, global circle coordinates, global normalized directions, and one
canonical crossing-count table. -/
def PairwiseCanonicalExactCoordinateGeometricUpperCertificates
    (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  ∀ n : Nat, ∀ A : P.Arrangement n,
    ∃ L : PairwiseCanonicalExactCoordinateGeometricLollipopUpper,
      L.nNat = n ∧ L.regions = P.region n A

/-- Convert Paulsen-geometric certificate families to the existing geometric
certificate families. -/
noncomputable def pairwise_paulsen_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePaulsenGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert circle-coordinate Paulsen-geometric certificate families to the
vector-witness Paulsen-geometric certificate families. -/
noncomputable def pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePaulsenCircleGeometricUpperCertificates P) :
    PairwisePaulsenGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwisePaulsenGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert circle-coordinate Paulsen-geometric certificate families to the
existing geometric certificate families. -/
noncomputable def pairwise_paulsen_circle_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwisePaulsenCircleGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_paulsen_geometric_upper_certificates_to_geometric
    (pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen hupper)

/-- Convert global circle-coordinate certificate families to the per-five-set
Paulsen-circle certificate families. -/
noncomputable def pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseGlobalCircleGeometricUpperCertificates P) :
    PairwisePaulsenCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwisePaulsenCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert global circle-coordinate certificate families to the existing
geometric certificate families. -/
noncomputable def pairwise_global_circle_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseGlobalCircleGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_paulsen_circle_geometric_upper_certificates_to_geometric
    (pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle hupper)

/-- Convert canonical circle-coordinate certificate families to global
circle-coordinate certificate families. -/
noncomputable def pairwise_canonical_circle_geometric_upper_certificates_to_global
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCircleGeometricUpperCertificates P) :
    PairwiseGlobalCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseGlobalCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert canonical circle-coordinate certificate families to the existing
geometric certificate families. -/
noncomputable def pairwise_canonical_circle_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCircleGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_global_circle_geometric_upper_certificates_to_geometric
    (pairwise_canonical_circle_geometric_upper_certificates_to_global hupper)

/-- Convert canonical circle/direction certificate families to canonical
circle certificate families. -/
noncomputable def pairwise_canonical_geometric_upper_certificates_to_canonical_circle
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalGeometricUpperCertificates P) :
    PairwiseCanonicalCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert canonical circle/direction certificate families to the existing
geometric certificate families. -/
noncomputable def pairwise_canonical_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_circle_geometric_upper_certificates_to_geometric
    (pairwise_canonical_geometric_upper_certificates_to_canonical_circle hupper)

/-- Convert one-table canonical certificate families to canonical
circle/direction certificate families. -/
noncomputable def pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCaseBoundGeometricUpperCertificates P) :
    PairwiseCanonicalGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert one-table canonical certificate families to the existing geometric
certificate families. -/
noncomputable def pairwise_canonical_case_bound_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCaseBoundGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_geometric_upper_certificates_to_geometric
    (pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
      hupper)

/-- Convert coordinate certificate families to canonical-circle certificate
families. -/
noncomputable def pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCoordinateGeometricUpperCertificates P) :
    PairwiseCanonicalCircleGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalCircleGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert coordinate certificate families to the existing geometric
certificate families. -/
noncomputable def pairwise_canonical_coordinate_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalCoordinateGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_circle_geometric_upper_certificates_to_geometric
    (pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
      hupper)

/-- Convert exact pairwise-count coordinate certificate families to coordinate
certificate families. -/
noncomputable def pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalExactCoordinateGeometricUpperCertificates P) :
    PairwiseCanonicalCoordinateGeometricUpperCertificates P := by
  intro n A
  rcases hupper n A with ⟨L, hLn, hLreg⟩
  exact ⟨L.toPairwiseCanonicalCoordinateGeometricLollipopUpper, hLn, hLreg⟩

/-- Convert exact pairwise-count coordinate certificate families to the
existing geometric certificate families. -/
noncomputable def pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_geometric
    {P : TheoremOne.ProblemFamily.{u}}
    (hupper : PairwiseCanonicalExactCoordinateGeometricUpperCertificates P) :
    PairwiseGeometricUpperCertificates P :=
  pairwise_canonical_coordinate_geometric_upper_certificates_to_geometric
    (pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
      hupper)

/-- Upper-bound half of Theorem 1 from geometric data whose five-set
intriguing-pair input is discharged by Paulsen's checked linear algebra. -/
theorem upper_bound_of_pairwise_paulsen_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwisePaulsenGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_geometric_certificates P
    (pairwise_paulsen_geometric_upper_certificates_to_geometric hupper)

/-- Upper-bound half of Theorem 1 from geometric data whose five-set
intriguing-pair input is discharged from circle-coordinate Paulsen witnesses. -/
theorem upper_bound_of_pairwise_paulsen_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwisePaulsenCircleGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_paulsen_geometric_certificates P
    (pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen hupper)

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement. -/
theorem upper_bound_of_pairwise_global_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseGlobalCircleGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_paulsen_circle_geometric_certificates P
    (pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle hupper)

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement, with intriguing fixed to the canonical Paulsen circle relation. -/
theorem upper_bound_of_pairwise_canonical_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalCircleGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_global_circle_geometric_certificates P
    (pairwise_canonical_circle_geometric_upper_certificates_to_global hupper)

/-- Upper-bound half of Theorem 1 from canonical circle and direction
coordinate data. -/
theorem upper_bound_of_pairwise_canonical_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_circle_geometric_certificates P
    (pairwise_canonical_geometric_upper_certificates_to_canonical_circle hupper)

/-- Upper-bound half of Theorem 1 from canonical circle/direction coordinate
data and one canonical four-case crossing-count table. -/
theorem upper_bound_of_pairwise_canonical_case_bound_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalCaseBoundGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_geometric_certificates P
    (pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
      hupper)

/-- Upper-bound half of Theorem 1 from global circle coordinates, global
normalized directions, and one canonical crossing-count table. -/
theorem upper_bound_of_pairwise_canonical_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalCoordinateGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_circle_geometric_certificates P
    (pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
      hupper)

/-- Upper-bound half of Theorem 1 from exact pairwise crossing counts, global
circle coordinates, global normalized directions, and one canonical
crossing-count table. -/
theorem upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (hupper : PairwiseCanonicalExactCoordinateGeometricUpperCertificates P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact upper_bound_of_pairwise_canonical_coordinate_geometric_certificates P
    (pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
      hupper)

end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 8: `Manuscript.RegionEquation`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Incremental region-count algebra for the manuscript-facing Theorem 1 layer.

This file isolates the purely finite algebra behind the usual planar-region
recurrence: start with one region, insert the lollipops one at a time, and add
`added k + 1` regions at step `k`.  The theorem below proves that this implies
the final equation `regions = total crossings + n + 1` once the incremental
crossing contributions sum to the stated total.
-/

namespace Lollipop
namespace TheoremOneManuscript

open BigOperators

/-- Telescoping algebra for an incremental region count.  If `partialRegions 0 = 1`
and each step `k < n` adds `added k + 1`, then after `n` steps the count is
the sum of all incremental additions plus `n + 1`. -/
theorem region_eq_sum_added_of_increment
    (partialRegions added : Nat → Rat) :
    ∀ n : Nat,
      partialRegions 0 = 1 →
      (∀ k : Nat, k < n →
        partialRegions (k + 1) = partialRegions k + added k + 1) →
      partialRegions n = (∑ k ∈ Finset.range n, added k) + (n : Rat) + 1
  | 0, hzero, _ => by
      simp [hzero]
  | Nat.succ n, hzero, hstep => by
      have hprev :
          ∀ k : Nat, k < n →
            partialRegions (k + 1) = partialRegions k + added k + 1 := by
        intro k hk
        exact hstep k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have ih :=
        region_eq_sum_added_of_increment partialRegions added n hzero hprev
      have hlast :
          partialRegions (n + 1) = partialRegions n + added n + 1 :=
        hstep n (Nat.lt_succ_self n)
      calc
        partialRegions (Nat.succ n)
            = partialRegions n + added n + 1 := by
                simpa [Nat.succ_eq_add_one] using hlast
        _ = ((∑ k ∈ Finset.range n, added k) + (n : Rat) + 1) +
              added n + 1 := by
                rw [ih]
        _ = (∑ k ∈ Finset.range (Nat.succ n), added k) +
              (Nat.succ n : Rat) + 1 := by
                rw [Finset.sum_range_succ]
                simp [Nat.cast_succ]
                ring

/-- Concrete incremental data for deriving a final region equation.  The
`added_sum_eq_total` field can later be supplied either by a direct finite
crossing-count calculation or by a more structured pair-indexing lemma. -/
structure IncrementalRegionData
    (n : Nat) (target totalCrossings : Rat) where
  partialRegions : Nat → Rat
  added : Nat → Rat
  partialRegions_zero : partialRegions 0 = 1
  partialRegions_step :
    ∀ k : Nat, k < n →
      partialRegions (k + 1) = partialRegions k + added k + 1
  partialRegions_final : partialRegions n = target
  added_sum_eq_total : (∑ k ∈ Finset.range n, added k) = totalCrossings

namespace IncrementalRegionData

/-- The incremental data imply the final `target = totalCrossings + n + 1`
region equation. -/
theorem target_eq_totalCrossings_add
    {n : Nat} {target totalCrossings : Rat}
    (D : IncrementalRegionData n target totalCrossings) :
    target = totalCrossings + (n : Rat) + 1 := by
  rw [← D.partialRegions_final]
  rw [region_eq_sum_added_of_increment D.partialRegions D.added n
    D.partialRegions_zero D.partialRegions_step]
  rw [D.added_sum_eq_total]

end IncrementalRegionData

/-- Incremental data specialized to the pair-sum crossing total used in the
upper-bound certificates. -/
abbrev IncrementalPairRegionData
    (n : Nat) (target : Rat) (cross : Fin n → Fin n → Rat) : Type :=
  IncrementalRegionData n target (pairSum n cross)

/-- The pair-sum-specialized incremental package gives exactly the region
equation required by the final upper-certificate stack. -/
theorem region_eq_pairSum_of_incremental_pair_region_data
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : IncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  D.target_eq_totalCrossings_add

/-- The crossing contribution against all earlier indices for a fixed inserted
index `j`. -/
def previousPairSum
    {n : Nat} (cross : Fin n → Fin n → Rat) (j : Fin n) : Rat :=
  ∑ i : Fin n, if i < j then cross i j else 0

/-- The previous-pair contribution written as a natural-indexed sequence,
with value `0` outside `0, ..., n - 1`. -/
def previousPairAdded
    {n : Nat} (cross : Fin n → Fin n → Rat) (k : Nat) : Rat :=
  if h : k < n then previousPairSum cross ⟨k, h⟩ else 0

/-- Previous-pair sums respect pointwise equality of crossing tables. -/
theorem previousPairSum_congr
    {n : Nat} {cross cross' : Fin n → Fin n → Rat}
    (hcross : ∀ i j : Fin n, cross i j = cross' i j)
    (j : Fin n) :
    previousPairSum cross j = previousPairSum cross' j := by
  classical
  unfold previousPairSum
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hij : i < j
  · simp [hij, hcross i j]
  · simp [hij]

/-- Natural-indexed previous-pair additions respect pointwise equality of
crossing tables. -/
theorem previousPairAdded_congr
    {n : Nat} {cross cross' : Fin n → Fin n → Rat}
    (hcross : ∀ i j : Fin n, cross i j = cross' i j)
    (k : Nat) :
    previousPairAdded cross k = previousPairAdded cross' k := by
  unfold previousPairAdded
  by_cases hk : k < n
  · simp [hk, previousPairSum_congr hcross ⟨k, hk⟩]
  · simp [hk]

/-- Summing previous-pair contributions over insertion indices is the same as
summing over unordered increasing pairs. -/
theorem pairSum_eq_sum_previousPairSum
    (n : Nat) (cross : Fin n → Fin n → Rat) :
    pairSum n cross = ∑ j : Fin n, previousPairSum cross j := by
  classical
  unfold pairSum previousPairSum
  let fibers : Fin n → Finset (Fin n) :=
    fun j => (Finset.univ.filter fun i : Fin n => i < j)
  have hprod :
      (∑ p ∈ pairFinset n, cross p.1 p.2) =
        ∑ j ∈ (Finset.univ : Finset (Fin n)),
          ∑ i ∈ fibers j, cross i j := by
    refine Finset.sum_finset_product_right
      (r := pairFinset n) (s := (Finset.univ : Finset (Fin n)))
      (t := fibers) ?_
    intro p
    simp [pairFinset, fibers]
  calc
    (∑ p ∈ pairFinset n, cross p.1 p.2)
        = ∑ j ∈ (Finset.univ : Finset (Fin n)),
            ∑ i ∈ fibers j, cross i j := hprod
    _ = ∑ j : Fin n, ∑ i : Fin n,
            if i < j then cross i j else 0 := by
          simp [fibers, Finset.sum_filter]

/-- The natural-indexed previous-pair sequence sums to `pairSum`. -/
theorem sum_range_previousPairAdded_eq_pairSum
    {n : Nat} (cross : Fin n → Fin n → Rat) :
    (∑ k ∈ Finset.range n, previousPairAdded cross k) = pairSum n cross := by
  rw [pairSum_eq_sum_previousPairSum n cross]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [previousPairAdded]

/-- Region-increment data where the crossing contribution at step `k` is the
canonical sum over previous pairs `i < k`. -/
structure OrderedIncrementalPairRegionData
    (n : Nat) (target : Rat) (cross : Fin n → Fin n → Rat) where
  partialRegions : Nat → Rat
  partialRegions_zero : partialRegions 0 = 1
  partialRegions_step :
    ∀ k : Nat, k < n →
      partialRegions (k + 1) =
        partialRegions k + previousPairAdded cross k + 1
  partialRegions_final : partialRegions n = target

namespace OrderedIncrementalPairRegionData

/-- Ordered previous-pair increment data imply the general incremental
pair-region package. -/
def toIncrementalPairRegionData
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross) :
    IncrementalPairRegionData n target cross where
  partialRegions := D.partialRegions
  added := previousPairAdded cross
  partialRegions_zero := D.partialRegions_zero
  partialRegions_step := D.partialRegions_step
  partialRegions_final := D.partialRegions_final
  added_sum_eq_total := sum_range_previousPairAdded_eq_pairSum cross

/-- Ordered previous-pair increment data prove the pair-sum region equation. -/
theorem target_eq_pairSum_add
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  region_eq_pairSum_of_incremental_pair_region_data
    D.toIncrementalPairRegionData

/-- Ordered incremental region data can be transported across pointwise
equality of crossing tables. -/
def congr_cross
    {n : Nat} {target : Rat} {cross cross' : Fin n → Fin n → Rat}
    (D : OrderedIncrementalPairRegionData n target cross)
    (hcross : ∀ i j : Fin n, cross i j = cross' i j) :
    OrderedIncrementalPairRegionData n target cross' where
  partialRegions := D.partialRegions
  partialRegions_zero := D.partialRegions_zero
  partialRegions_step := by
    intro k hk
    calc
      D.partialRegions (k + 1) =
          D.partialRegions k + previousPairAdded cross k + 1 :=
        D.partialRegions_step k hk
      _ = D.partialRegions k + previousPairAdded cross' k + 1 := by
        rw [previousPairAdded_congr hcross k]
  partialRegions_final := D.partialRegions_final

end OrderedIncrementalPairRegionData

/-- One local insertion step in the ordered previous-pair region recurrence.
This is the per-step certificate that a first-principles construction can
prove independently before Lean assembles the full recurrence. -/
structure OrderedIncrementStepData
    (n : Nat) (partialRegions : Nat → Rat)
    (cross : Fin n → Fin n → Rat) (k : Nat) (hk : k < n) where
  step_eq :
    partialRegions (k + 1) =
      partialRegions k + previousPairAdded cross k + 1

namespace OrderedIncrementStepData

/-- A local insertion-step certificate can be transported across pointwise
equality of crossing tables. -/
def congr_cross
    {n : Nat} {partialRegions : Nat → Rat}
    {cross cross' : Fin n → Fin n → Rat} {k : Nat} {hk : k < n}
    (D : OrderedIncrementStepData n partialRegions cross k hk)
    (hcross : ∀ i j : Fin n, cross i j = cross' i j) :
    OrderedIncrementStepData n partialRegions cross' k hk where
  step_eq := by
    calc
      partialRegions (k + 1) =
          partialRegions k + previousPairAdded cross k + 1 := D.step_eq
      _ = partialRegions k + previousPairAdded cross' k + 1 := by
        rw [previousPairAdded_congr hcross k]

end OrderedIncrementStepData

/-- Ordered region-increment data supplied as one local certificate for each
insertion step. -/
structure StepwiseOrderedIncrementalPairRegionData
    (n : Nat) (target : Rat) (cross : Fin n → Fin n → Rat) where
  partialRegions : Nat → Rat
  partialRegions_zero : partialRegions 0 = 1
  step :
    ∀ k : Nat, ∀ hk : k < n,
      OrderedIncrementStepData n partialRegions cross k hk
  partialRegions_final : partialRegions n = target

namespace StepwiseOrderedIncrementalPairRegionData

/-- Assemble local insertion-step certificates into the bundled ordered
incremental region data used by the theorem stack. -/
def toOrderedIncrementalPairRegionData
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross) :
    OrderedIncrementalPairRegionData n target cross where
  partialRegions := D.partialRegions
  partialRegions_zero := D.partialRegions_zero
  partialRegions_step := by
    intro k hk
    exact (D.step k hk).step_eq
  partialRegions_final := D.partialRegions_final

/-- Stepwise ordered region data prove the pair-sum region equation. -/
theorem target_eq_pairSum_add
    {n : Nat} {target : Rat} {cross : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross) :
    target = pairSum n cross + (n : Rat) + 1 :=
  D.toOrderedIncrementalPairRegionData.target_eq_pairSum_add

/-- Stepwise ordered region data can be transported across pointwise equality
of crossing tables. -/
def congr_cross
    {n : Nat} {target : Rat} {cross cross' : Fin n → Fin n → Rat}
    (D : StepwiseOrderedIncrementalPairRegionData n target cross)
    (hcross : ∀ i j : Fin n, cross i j = cross' i j) :
    StepwiseOrderedIncrementalPairRegionData n target cross' where
  partialRegions := D.partialRegions
  partialRegions_zero := D.partialRegions_zero
  step := by
    intro k hk
    exact (D.step k hk).congr_cross hcross
  partialRegions_final := D.partialRegions_final

end StepwiseOrderedIncrementalPairRegionData

end TheoremOneManuscript
end Lollipop

/-!
Proof component 9: `SectionFive.Proof`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Theorem 1 assembly with Section 5 discharged.

This file is the manuscript-facing final dependency package.  Unlike
`TheoremOneFormal.Proof`, it no longer asks for the matrix theorem, support
descent, or star-forest minimum as inputs: those are proved in
`TheoremOneComplete.SupportDescent` and imported here.  The remaining inputs
are the problem-family upper certificates and lower realizations, which encode
the external geometric/construction data for the chosen lollipop model.
-/

namespace Lollipop
namespace TheoremOneComplete

universe u

/-- The remaining non-Section-5 inputs needed for Theorem 1 over an abstract
problem family.  Section 5's matrix theorem is now supplied by
`matrix_theorem_proven`. -/
structure TheoremOneInputs (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : TheoremOneFormal.PairwiseNatMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Convert the complete-input package to the older formal subtheorem package
by filling the matrix field with the checked Section 5 theorem. -/
def TheoremOneInputs.toFormalSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : TheoremOneInputs P) :
    TheoremOneFormal.TheoremOneSubtheorems P where
  matrix_theorem := matrix_theorem_proven
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Theorem 1 in maximum form with the matrix theorem fully discharged. -/
theorem theorem_one_maximum
    (P : TheoremOne.ProblemFamily.{u})
    (h : TheoremOneInputs P) :
    TheoremOne.MaximumStatement P := by
  exact TheoremOneFormal.theorem_one_maximum_from_subtheorems P
    h.toFormalSubtheorems

/-- Complete inputs for a family with a named maximum-count function. -/
def MaxTheoremOneInputs (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneInputs P.toProblemFamily

/-- Theorem 1 in formula form with the matrix theorem fully discharged. -/
theorem theorem_one_formula
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneInputs P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum P.toProblemFamily h)

/-- Single-size displayed formula for Theorem 1. -/
theorem theorem_one_formula_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneInputs P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula P h n

end TheoremOneComplete
end Lollipop

/-!
Proof component 10: `ColoredTuran.Proof`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Theorem 1 as a final Lean statement from proved subtheorems.

This is the most expanded theorem assembly in the repository.  The matrix
theorem, all Section 5 compression cases, finite-sum crossing reduction,
lower-construction algebra, and partition-intersection matrix algebra are
proved in imported files.  The input package below contains only the
certificate-producing statements for the actual lollipop model.
-/

namespace Lollipop
namespace TheoremOneEndToEnd

universe u

/-- The remaining model-specific inputs after the generic proof has been
formalized.  These are certificate-production statements: for every lollipop
arrangement, produce the pairwise/colored/weighted quotient certificate, and
for every admissible four-cluster lower pattern, produce a realizing
arrangement. -/
structure TheoremOneSubtheorems (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : PairwisePartitionMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Convert the refined end-to-end package to the complete package where the
matrix theorem has already been discharged. -/
def TheoremOneSubtheorems.toCompleteInputs
    {P : TheoremOne.ProblemFamily.{u}}
    (h : TheoremOneSubtheorems P) :
    TheoremOneComplete.TheoremOneInputs P where
  upper_certificates :=
    pairwise_partition_matrix_upper_certificates_to_nat_matrix h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Theorem 1 in maximum form, with all generic algebraic and matrix
subtheorems proved and only model-specific certificate production supplied. -/
theorem theorem_one_maximum
    (P : TheoremOne.ProblemFamily.{u})
    (h : TheoremOneSubtheorems P) :
    TheoremOne.MaximumStatement P := by
  exact TheoremOneComplete.theorem_one_maximum P h.toCompleteInputs

/-- End-to-end inputs for a problem family with a named maximum-count
function. -/
def MaxTheoremOneSubtheorems (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOneSubtheorems P.toProblemFamily

/-- Theorem 1 in the manuscript formula form for a named maximum-count
function. -/
theorem theorem_one_formula
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P) :
    TheoremOne.FormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_maximum P.toProblemFamily h)

/-- Single-size version of Theorem 1 in the displayed manuscript form. -/
theorem theorem_one_formula_at
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxTheoremOneSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula P h n

end TheoremOneEndToEnd
end Lollipop

/-!
Proof component 11: `CertifiedEndpoint.Statement`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Final Theorem 1 endpoint.

This folder is intentionally small and non-disruptive.  It packages the
existing formalization in the mathlib style used for maximum theorems:
`IsGreatest (Set.range ...) value`.  That statement simultaneously records
attainment and the universal upper bound.

The generic combinatorial and algebraic subtheorems imported here are proved
in the `Lollipop` tree.  The only remaining inputs are the model-specific
certificate producers for the concrete lollipop family: refined upper
certificates for every arrangement and lower realizations.
-/

namespace Lollipop
namespace TheoremOneFinal

universe u

/-- Theorem 1 as a mathlib-style maximum statement for an abstract lollipop
problem family. -/
def TheoremOneStatement (P : TheoremOne.ProblemFamily.{u}) : Prop :=
  TheoremOne.MaximumStatement P

/-- Theorem 1 as the displayed formula for a family with a named maximum
function. -/
def TheoremOneFormulaStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  TheoremOne.FormulaStatement P

/-- The remaining model-specific subtheorems after the generic proof has been
formalized.  These are certificate-production statements rather than algebraic
or matrix inequalities: every arrangement supplies the refined pairwise upper
certificate, and every size has a lower realization attaining the candidate
value. -/
structure ModelSubtheorems (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : TheoremOneEndToEnd.PairwisePartitionMatrixUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Stronger model-specific subtheorems after the weighted Turan theorem has
been internalized.  Upper certificates now supply actual blocker graphs whose
off-diagonal complements are clique-free; Lean generates the Turan partitions
and then runs the partition-intersection/matrix pipeline. -/
structure WeightedTuranModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates : TheoremOneEndToEnd.PairwiseWeightedTuranUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest currently internalized upper-certificate package.  Upper
certificates supply no-zero colored quotient certificates.  Lean then derives
the blocker complement clique-free hypotheses, chooses the weighted-Turan
partitions, runs the partition-intersection/matrix pipeline, and applies the
pairwise lollipop reduction. -/
structure ColoredQuotientModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseColoredQuotientUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest internalized upper-certificate package.  Upper certificates
provide only the original colored graph for the two-graph reduction, with the
`D`/`E` forbidden-clique hypotheses and the geometric pairwise score bounds.
Lean then performs colored Zykov, quotienting, weighted Turan,
partition-intersection, Section 5, and pairwise summation internally. -/
structure ColoredGraphModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseColoredGraphUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest upper-bound interface before choosing an explicit Euclidean
coordinate model.  Upper certificates provide the manuscript's close and
intriguing predicates, pairwise crossing table, geometric crossing cases, and
the two finite forbidden-pair facts.  Lean constructs the colored graph and
then performs colored Zykov, quotienting, weighted Turan,
partition-intersection, Section 5, and pairwise summation internally. -/
structure GeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with Paulsen's five-circle linear algebra
internalized.  The upper certificates still supply the pairwise crossing
geometry and the close-pair-in-four fact, but the five-intriguing-pair fact is
derived in Lean from Paulsen vector witnesses on every five-element subset. -/
structure PaulsenGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwisePaulsenGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with Paulsen's appendix reduced to circle
coordinates and distance inequalities.  Lean constructs Paulsen vectors,
proves their Gram inequalities, derives the five-intriguing-pair fact, and
then runs the rest of the upper-bound stack internally. -/
structure PaulsenCircleGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwisePaulsenCircleGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with one global circle-coordinate model per
arrangement.  Lean restricts the global centers/radii to every five-subset,
builds the Paulsen circle data, derives the five-intriguing-pair fact, and
then runs the rest of the upper-bound stack internally. -/
structure GlobalCircleGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseGlobalCircleGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Geometric model package with one global circle-coordinate model per
arrangement and with `intriguing` fixed to the canonical Paulsen circle
relation. -/
structure CanonicalCircleGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCircleGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current geometric upper model.  The close relation is fixed to
the canonical cyclic direction relation and the intriguing relation is fixed to
the canonical Paulsen circle relation; Lean derives both finite
forbidden-pair facts. -/
structure CanonicalGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current concise geometric upper model.  The close and
intriguing relations are canonical, and the pairwise crossing estimate is
supplied as one four-case table; Lean expands that table and derives both
finite forbidden-pair facts. -/
structure CanonicalCaseBoundGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCaseBoundGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current geometric upper model.  Upper certificates provide
global circle coordinates, global normalized directions, and one canonical
crossing table; Lean derives the unordered four-direction close-pair theorem
by sorting each four-set. -/
structure CanonicalCoordinateGeometricModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCoordinateGeometricUpperCertificates P
  lower_realizations : TheoremOne.LowerRealizations P

/-- Strongest current upper/lower model.  The upper side uses global circle
coordinates, normalized directions, and one canonical crossing table.  The
lower side supplies Karlsson blow-up crossing counts plus the generic
`regions = crossings + n + 1` equation; Lean derives the older lower
realization interface. -/
structure CanonicalCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalCoordinateGeometricUpperCertificates P
  lower_crossing_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      TheoremOne.LowerCrossingRealizations P lower_crossings

/-- Strongest current exact-pairwise upper/lower model.  The upper side
supplies exact pairwise crossing counts and the exact region equation in
pair-sum form; Lean fills the older total-crossing fields.  The lower side
uses Karlsson blow-up crossing-count realizations plus the generic region
equation. -/
structure CanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P
  lower_crossing_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      TheoremOne.LowerCrossingRealizations P lower_crossings

/-- Convert the final model-specific package to the expanded end-to-end
subtheorem package. -/
def ModelSubtheorems.toEndToEndSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ModelSubtheorems P) :
    TheoremOneEndToEnd.TheoremOneSubtheorems P where
  upper_certificates := h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the weighted-Turan model package to the previous final package by
choosing the weighted Turan partitions internally. -/
def WeightedTuranModelSubtheorems.toModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : WeightedTuranModelSubtheorems P) :
    ModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_weighted_turan_upper_certificates_to_partition_matrix
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the colored-quotient model package to the weighted-Turan package by
deriving blocker graphs and clique-free complement hypotheses internally. -/
def ColoredQuotientModelSubtheorems.toWeightedTuranModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ColoredQuotientModelSubtheorems P) :
    WeightedTuranModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_colored_quotient_upper_certificates_to_weighted_turan
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the colored-quotient model package to the final model package. -/
def ColoredQuotientModelSubtheorems.toModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ColoredQuotientModelSubtheorems P) :
    ModelSubtheorems P :=
  h.toWeightedTuranModelSubtheorems.toModelSubtheorems

/-- Convert the Paulsen-geometric package to the geometric package after Lean
derives the five-intriguing-pair fact from Paulsen's checked linear algebra. -/
noncomputable def PaulsenGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PaulsenGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_paulsen_geometric_upper_certificates_to_geometric
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the Paulsen circle-coordinate package to the Paulsen vector package
after Lean performs the circle-vector Gram calculation. -/
noncomputable def PaulsenCircleGeometricModelSubtheorems.toPaulsenGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    PaulsenGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_paulsen_circle_geometric_upper_certificates_to_paulsen
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the Paulsen circle-coordinate package to the geometric package. -/
noncomputable def PaulsenCircleGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toPaulsenGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the global circle-coordinate package to the Paulsen circle package
after Lean restricts the global data to every five-subset. -/
noncomputable def GlobalCircleGeometricModelSubtheorems.toPaulsenCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : GlobalCircleGeometricModelSubtheorems P) :
    PaulsenCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_global_circle_geometric_upper_certificates_to_paulsen_circle
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the global circle-coordinate package to the geometric package. -/
noncomputable def GlobalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : GlobalCircleGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toPaulsenCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the canonical circle-coordinate package to the global circle
package after Lean unfolds the canonical intriguing relation into distance
inequalities. -/
noncomputable def CanonicalCircleGeometricModelSubtheorems.toGlobalCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    GlobalCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_circle_geometric_upper_certificates_to_global
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the canonical circle-coordinate package to the geometric package. -/
noncomputable def CanonicalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toGlobalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the canonical geometric package to the canonical circle package
after Lean derives close-pair-in-four from the cyclic direction theorem. -/
noncomputable def CanonicalGeometricModelSubtheorems.toCanonicalCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalGeometricModelSubtheorems P) :
    CanonicalCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_geometric_upper_certificates_to_canonical_circle
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the canonical geometric package to the geometric package. -/
noncomputable def CanonicalGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toCanonicalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the one-table canonical geometric package to the expanded
canonical geometric package by deriving the four pointwise crossing
inequality fields from the single case table. -/
noncomputable def CanonicalCaseBoundGeometricModelSubtheorems.toCanonicalGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    CanonicalGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_case_bound_geometric_upper_certificates_to_canonical
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the one-table canonical geometric package to the geometric
package. -/
noncomputable def CanonicalCaseBoundGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toCanonicalGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the coordinate package to the canonical-circle package by deriving
the close-pair-in-four theorem from unordered normalized directions and
expanding the crossing case table. -/
noncomputable def CanonicalCoordinateGeometricModelSubtheorems.toCanonicalCircleGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    CanonicalCircleGeometricModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_coordinate_geometric_upper_certificates_to_canonical_circle
      h.upper_certificates
  lower_realizations := h.lower_realizations

/-- Convert the coordinate package to the geometric package. -/
noncomputable def CanonicalCoordinateGeometricModelSubtheorems.toGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    GeometricModelSubtheorems P :=
  h.toCanonicalCircleGeometricModelSubtheorems.toGeometricModelSubtheorems

/-- Convert the crossing-count lower package to the previous coordinate
package after deriving lower realizations from crossing counts and the generic
region equation. -/
noncomputable def CanonicalCoordinateGeometricCrossingModelSubtheorems.toCanonicalCoordinateGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    CanonicalCoordinateGeometricModelSubtheorems P where
  upper_certificates := h.upper_certificates
  lower_realizations :=
    by
      rcases h.lower_crossing_realizations with ⟨lower_crossings, hlower⟩
      exact TheoremOne.lowerRealizations_of_lowerCrossingRealizations P
        (crossings := lower_crossings) hlower

/-- Convert exact-pairwise upper/lower data to the previous coordinate
crossing package by deriving the older coordinate upper certificates. -/
noncomputable def CanonicalExactCoordinateGeometricCrossingModelSubtheorems.toCanonicalCoordinateGeometricCrossingModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    CanonicalCoordinateGeometricCrossingModelSubtheorems P where
  upper_certificates :=
    TheoremOneEndToEnd.pairwise_canonical_exact_coordinate_geometric_upper_certificates_to_coordinate
      h.upper_certificates
  lower_crossing_realizations := h.lower_crossing_realizations

/-- Convert exact-pairwise upper/lower data to the previous coordinate package. -/
noncomputable def CanonicalExactCoordinateGeometricCrossingModelSubtheorems.toCanonicalCoordinateGeometricModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    CanonicalCoordinateGeometricModelSubtheorems P :=
  h.toCanonicalCoordinateGeometricCrossingModelSubtheorems
    |>.toCanonicalCoordinateGeometricModelSubtheorems

/-- Section 5's `3 x 4` matrix theorem is proved internally. -/
theorem section_five_matrix_theorem_proven : MatrixTheoremStatement :=
  matrix_theorem_proven

/-- The upper-bound half of Theorem 1 from the refined upper certificates.
All blocker, quotient, partition-intersection, pair-summation, and matrix
steps used here are proved in imported files. -/
theorem upper_bound_proven
    (P : TheoremOne.ProblemFamily.{u})
    (h : ModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_partition_matrix_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from actual blocker graphs plus the proved
weighted Turan theorem. -/
theorem upper_bound_proven_from_weighted_turan
    (P : TheoremOne.ProblemFamily.{u})
    (h : WeightedTuranModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_weighted_turan_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from no-zero colored quotient certificates.
All colored quotient, blocker, weighted Turan, partition-intersection,
pair-summation, and matrix steps used here are proved in imported files. -/
theorem upper_bound_proven_from_colored_quotients
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredQuotientModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_colored_quotient_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from original colored graph certificates.
This is the current strongest internalized upper path: colored Zykov and the
quotient construction are proved in Lean. -/
theorem upper_bound_proven_from_colored_graphs
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredGraphModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_colored_graph_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from the manuscript's close/intriguing
geometric upper data. -/
theorem upper_bound_proven_from_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from geometric upper data where Paulsen
vector witnesses discharge the five-intriguing-pair input. -/
theorem upper_bound_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_paulsen_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from geometric upper data where Paulsen
circle-coordinate witnesses discharge the five-intriguing-pair input. -/
theorem upper_bound_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_paulsen_circle_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement. -/
theorem upper_bound_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GlobalCircleGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_global_circle_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from one global circle-coordinate model per
arrangement, with `intriguing` fixed to the canonical Paulsen circle relation. -/
theorem upper_bound_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_circle_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from canonical circle and direction
coordinate data. -/
theorem upper_bound_proven_from_canonical_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from canonical circle/direction coordinate
data and one canonical four-case crossing-count table. -/
theorem upper_bound_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_case_bound_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from global circle coordinates, global
normalized directions, and one canonical crossing table. -/
theorem upper_bound_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_coordinate_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from the strongest current upper/lower
package.  The lower crossing data is unused for the upper half. -/
theorem upper_bound_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_coordinate_geometric_certificates
    P h.upper_certificates

/-- Upper-bound half of Theorem 1 from exact pairwise crossing counts, global
circle coordinates, global normalized directions, and one canonical crossing
table.  The lower crossing data is unused for the upper half. -/
theorem upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
    P h.upper_certificates

/-- The lower-attainment half of Theorem 1 from the lower-realization
certificates and the checked lower-construction algebra. -/
theorem lower_attainment_proven
    (P : TheoremOne.ProblemFamily.{u})
    (h : ModelSubtheorems P) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact TheoremOneFormal.lower_attainment_of_realizations_choose
    P h.lower_realizations

/-- Theorem 1 in maximum form: the candidate value is attained and is an
upper bound for every arrangement. -/
theorem theorem_one_statement_proven
    (P : TheoremOne.ProblemFamily.{u})
    (h : ModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneEndToEnd.theorem_one_maximum
    P h.toEndToEndSubtheorems

/-- Theorem 1 in maximum form from the stronger weighted-Turan certificate
package. -/
theorem theorem_one_statement_proven_from_weighted_turan
    (P : TheoremOne.ProblemFamily.{u})
    (h : WeightedTuranModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in maximum form from no-zero colored quotient upper certificates
and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_colored_quotients
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredQuotientModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in maximum form from original colored graph upper certificates
and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_colored_graphs
    (P : TheoremOne.ProblemFamily.{u})
    (h : ColoredGraphModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_colored_graphs P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from the manuscript's close/intriguing geometric
upper data and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from Paulsen-geometric upper data and
lower-realization certificates. -/
theorem theorem_one_statement_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_paulsen_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from Paulsen circle-coordinate geometric upper
data and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : PaulsenCircleGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_paulsen_circle_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from one global circle-coordinate upper model per
arrangement and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : GlobalCircleGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_global_circle_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from canonical circle-coordinate upper data and
lower-realization certificates. -/
theorem theorem_one_statement_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCircleGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_circle_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from canonical circle and direction upper data
and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_canonical_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from canonical circle/direction data, one
four-case crossing-count table, and lower-realization certificates. -/
theorem theorem_one_statement_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCaseBoundGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_case_bound_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from global circle coordinates, global
normalized directions, one canonical crossing table, and lower-realization
certificates. -/
theorem theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricModelSubtheorems P) :
    TheoremOneStatement P := by
  exact TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
    P
    (upper_bound_proven_from_canonical_coordinate_geometric_certificates P h)
    (TheoremOneFormal.lower_attainment_of_realizations_choose
      P h.lower_realizations)

/-- Theorem 1 in maximum form from global circle coordinates, global
normalized directions, one canonical crossing table, lower Karlsson
crossing-count realizations, and the generic region equation. -/
theorem theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates
    P h.toCanonicalCoordinateGeometricModelSubtheorems

/-- Theorem 1 in maximum form from exact pairwise upper data, global circle
coordinates, global normalized directions, one canonical crossing table,
lower Karlsson crossing-count realizations, and the generic region equation. -/
theorem theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
    P h.toCanonicalCoordinateGeometricCrossingModelSubtheorems

/-- Final inputs for a family with a named maximum-count function. -/
def MaxModelSubtheorems (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ModelSubtheorems P.toProblemFamily

/-- Final weighted-Turan inputs for a family with a named maximum-count
function. -/
def MaxWeightedTuranModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  WeightedTuranModelSubtheorems P.toProblemFamily

/-- Final colored-quotient inputs for a family with a named maximum-count
function. -/
def MaxColoredQuotientModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ColoredQuotientModelSubtheorems P.toProblemFamily

/-- Final colored-graph inputs for a family with a named maximum-count
function. -/
def MaxColoredGraphModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ColoredGraphModelSubtheorems P.toProblemFamily

/-- Final geometric inputs for a family with a named maximum-count function. -/
def MaxGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  GeometricModelSubtheorems P.toProblemFamily

/-- Final Paulsen-geometric inputs for a family with a named maximum-count
function. -/
def MaxPaulsenGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  PaulsenGeometricModelSubtheorems P.toProblemFamily

/-- Final Paulsen circle-coordinate geometric inputs for a family with a named
maximum-count function. -/
def MaxPaulsenCircleGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  PaulsenCircleGeometricModelSubtheorems P.toProblemFamily

/-- Final global circle-coordinate geometric inputs for a family with a named
maximum-count function. -/
def MaxGlobalCircleGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  GlobalCircleGeometricModelSubtheorems P.toProblemFamily

/-- Final canonical circle-coordinate geometric inputs for a family with a
named maximum-count function. -/
def MaxCanonicalCircleGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCircleGeometricModelSubtheorems P.toProblemFamily

/-- Final canonical circle and direction geometric inputs for a family with a
named maximum-count function. -/
def MaxCanonicalGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalGeometricModelSubtheorems P.toProblemFamily

/-- Final one-table canonical geometric inputs for a family with a named
maximum-count function. -/
def MaxCanonicalCaseBoundGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCaseBoundGeometricModelSubtheorems P.toProblemFamily

/-- Final coordinate geometric inputs for a family with a named maximum-count
function. -/
def MaxCanonicalCoordinateGeometricModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCoordinateGeometricModelSubtheorems P.toProblemFamily

/-- Final coordinate upper and lower-crossing inputs for a family with a named
maximum-count function. -/
def MaxCanonicalCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalCoordinateGeometricCrossingModelSubtheorems P.toProblemFamily

/-- Final exact-pairwise coordinate upper and lower-crossing inputs for a
family with a named maximum-count function. -/
def MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalExactCoordinateGeometricCrossingModelSubtheorems P.toProblemFamily

/-- Theorem 1 in formula form for a named maximum-count function. -/
theorem theorem_one_formula_statement_proven
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOneEndToEnd.theorem_one_formula P
    h.toEndToEndSubtheorems

/-- Theorem 1 in formula form from the stronger weighted-Turan certificate
package. -/
theorem theorem_one_formula_statement_proven_from_weighted_turan
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxWeightedTuranModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in formula form from no-zero colored quotient upper certificates
and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_colored_quotients
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredQuotientModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven P h.toModelSubtheorems

/-- Theorem 1 in formula form from original colored graph upper certificates
and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_colored_graphs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredGraphModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_colored_graphs P.toProblemFamily h)

/-- Theorem 1 in formula form from the manuscript's close/intriguing geometric
upper data and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from Paulsen-geometric upper data and
lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_paulsen_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from Paulsen circle-coordinate geometric upper
data and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenCircleGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_paulsen_circle_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from one global circle-coordinate upper model
per arrangement and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGlobalCircleGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_global_circle_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from canonical circle-coordinate upper data and
lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCircleGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_circle_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from canonical circle and direction upper data
and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from canonical circle/direction data, one
four-case crossing-count table, and lower-realization certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCaseBoundGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_case_bound_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from global circle coordinates, global
normalized directions, one canonical crossing table, and lower-realization
certificates. -/
theorem theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_coordinate_geometric_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from the strongest current upper/lower package,
using lower crossing counts plus `regions = crossings + n + 1`. -/
theorem theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_coordinate_geometric_crossing_certificates
      P.toProblemFamily h)

/-- Theorem 1 in formula form from the strongest exact-pairwise upper/lower
package. -/
theorem theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact TheoremOne.formulaStatement_of_maximumStatement P
    (theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P.toProblemFamily h)

/-- Single-size displayed formula. -/
theorem theorem_one_formula_at_proven
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven P h n

/-- Single-size displayed formula from the stronger weighted-Turan certificate
package. -/
theorem theorem_one_formula_at_proven_from_weighted_turan
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxWeightedTuranModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_weighted_turan P h n

/-- Single-size displayed formula from no-zero colored quotient upper
certificates and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_colored_quotients
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredQuotientModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_colored_quotients P h n

/-- Single-size displayed formula from original colored graph upper
certificates and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_colored_graphs
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxColoredGraphModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_colored_graphs P h n

/-- Single-size displayed formula from the manuscript's close/intriguing
geometric upper data and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_geometric_certificates P h n

/-- Single-size displayed formula from Paulsen-geometric upper data and
lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_paulsen_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_paulsen_geometric_certificates P h n

/-- Single-size displayed formula from Paulsen circle-coordinate geometric
upper data and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_paulsen_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxPaulsenCircleGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_paulsen_circle_geometric_certificates P h n

/-- Single-size displayed formula from one global circle-coordinate upper model
per arrangement and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_global_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxGlobalCircleGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_global_circle_geometric_certificates P h n

/-- Single-size displayed formula from canonical circle-coordinate upper data
and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_circle_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCircleGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_circle_geometric_certificates P h n

/-- Single-size displayed formula from canonical circle and direction upper
data and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_geometric_certificates P h n

/-- Single-size displayed formula from canonical circle/direction data, one
four-case crossing-count table, and lower-realization certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_case_bound_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCaseBoundGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_case_bound_geometric_certificates P h n

/-- Single-size displayed formula from global circle coordinates, global
normalized directions, one canonical crossing table, and lower-realization
certificates. -/
theorem theorem_one_formula_at_proven_from_canonical_coordinate_geometric_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_certificates P h n

/-- Single-size displayed formula from the strongest current upper/lower
package, using lower crossing counts plus `regions = crossings + n + 1`. -/
theorem theorem_one_formula_at_proven_from_canonical_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalCoordinateGeometricCrossingModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_coordinate_geometric_crossing_certificates P h n

/-- Single-size displayed formula from the strongest exact-pairwise upper/lower
package. -/
theorem theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + concreteS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates P h n

end TheoremOneFinal
end Lollipop

/-!
Proof component 12: `Manuscript.Statement`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Manuscript-facing statement of Theorem 1.

The final proof stack in `TheoremOneFinal` uses the internal labeled extremum
`concreteS`.  `FormulaBridge` proves that this is the same as the manuscript's
sorted extremum `manuscriptS`, so this file exposes the displayed formula in
the paper's notation.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Theorem 1 in the manuscript's displayed formula form, using the sorted
definition of `S(n)`. -/
def TheoremOneFormulaStatement (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  ∀ n : Nat,
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1

/-- Lower crossing-count realizations for the manuscript's sorted quadruples.
This is weaker than the older all-labeled-quadruple lower interface and
matches the displayed sorted maximum in the paper. -/
def SortedLowerCrossingRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      crossings A = lowerCrossingsOfQuad q ∧
      region A = crossings A + (n : Rat) + 1

/-- Sorted lower crossing-count realizations for every size in a problem
family. -/
def SortedLowerCrossingRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerCrossingRealization (P.Arrangement n) (P.region n)
      (crossings n) n

/-- Sorted lower crossing-count realizations where the lower region equation
is supplied by incremental insertion data. -/
def SortedLowerIncrementalCrossingRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      ∃ _ : IncrementalRegionData n (region A) (crossings A),
        crossings A = lowerCrossingsOfQuad q

/-- Incremental sorted lower crossing-count realizations for every size in a
problem family. -/
def SortedLowerIncrementalCrossingRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerIncrementalCrossingRealization (P.Arrangement n) (P.region n)
      (crossings n) n

/-- Monotone sorted lower crossing-count realizations.  For lower bounds the
construction does not need to prove the pair-sum is exactly Karlsson's table;
it is enough to produce at least that many crossings and satisfy the region
equation.  This interface is useful for concrete geometric blow-up proofs,
where proving lower witnesses can be easier than classifying every possible
carrier intersection. -/
def SortedLowerCrossingBoundRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      lowerCrossingsOfQuad q ≤ crossings A ∧
      region A = crossings A + (n : Rat) + 1

/-- Monotone sorted lower crossing-count realizations for every size in a
problem family. -/
def SortedLowerCrossingBoundRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerCrossingBoundRealization (P.Arrangement n) (P.region n)
      (crossings n) n

/-- Incremental version of the monotone sorted lower interface. -/
def SortedLowerIncrementalCrossingBoundRealization
    (Arrangement : Type*) (region crossings : Arrangement → Rat) (n : Nat) : Prop :=
  ∀ q : QuadVec n, q ∈ sortedQuadVecs n →
    ∃ A : Arrangement,
      ∃ _ : IncrementalRegionData n (region A) (crossings A),
        lowerCrossingsOfQuad q ≤ crossings A

/-- Incremental monotone sorted lower realizations for every size in a problem
family. -/
def SortedLowerIncrementalCrossingBoundRealizations
    (P : TheoremOne.ProblemFamily.{u})
    (crossings : (n : Nat) → P.Arrangement n → Rat) : Prop :=
  ∀ n : Nat,
    SortedLowerIncrementalCrossingBoundRealization
      (P.Arrangement n) (P.region n) (crossings n) n

/-- Exact sorted lower realizations are a special case of the monotone lower
interface. -/
theorem sortedLowerCrossingBoundRealization_of_exact
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerCrossingRealization Arrangement region crossings n) :
    SortedLowerCrossingBoundRealization Arrangement region crossings n := by
  intro q hq
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  exact ⟨A, by rw [hcross], hregion⟩

/-- Incremental monotone lower data imply the direct monotone lower
interface. -/
theorem sortedLowerCrossingBoundRealization_of_incremental_bound
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerIncrementalCrossingBoundRealization
        Arrangement region crossings n) :
    SortedLowerCrossingBoundRealization Arrangement region crossings n := by
  intro q hq
  rcases hreal q hq with ⟨A, D, hcross⟩
  exact ⟨A, hcross, D.target_eq_totalCrossings_add⟩

/-- Incremental monotone lower realizations for every size imply direct
monotone lower realizations for every size. -/
theorem sortedLowerCrossingBoundRealizations_of_incremental_bound
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hreal : SortedLowerIncrementalCrossingBoundRealizations P crossings) :
    SortedLowerCrossingBoundRealizations P crossings := by
  intro n
  exact sortedLowerCrossingBoundRealization_of_incremental_bound (hreal n)

/-- Incremental lower region data imply the ordinary sorted lower
crossing-count realization interface. -/
theorem sortedLowerCrossingRealization_of_incremental
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerIncrementalCrossingRealization Arrangement region crossings n) :
    SortedLowerCrossingRealization Arrangement region crossings n := by
  intro q hq
  rcases hreal q hq with ⟨A, hregion, hcross⟩
  exact ⟨A, hcross, hregion.target_eq_totalCrossings_add⟩

/-- Incremental lower realizations for every size imply the ordinary sorted
lower interface. -/
theorem sortedLowerCrossingRealizations_of_incremental
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hreal : SortedLowerIncrementalCrossingRealizations P crossings) :
    SortedLowerCrossingRealizations P crossings := by
  intro n
  exact sortedLowerCrossingRealization_of_incremental (hreal n)

/-- The manuscript's sorted finite maximum is attained. -/
theorem exists_quadVecExcess_eq_manuscriptS (n : Nat) :
    ∃ q : QuadVec n, q ∈ sortedQuadVecs n ∧ quadVecExcess q = manuscriptS n := by
  unfold manuscriptS
  rcases Finset.exists_mem_eq_sup' (sortedQuadVecs_nonempty n) quadVecExcess with
    ⟨q, hq, hqmax⟩
  exact ⟨q, hq, hqmax.symm⟩

/-- A sorted quadruple attaining the manuscript extremum gives the candidate
lower region count. -/
theorem lowerRegionsOfQuad_eq_candidate_of_manuscript_excess
    {n : Nat} {q : QuadVec n}
    (hq : q ∈ sortedQuadVecs n)
    (hmax : quadVecExcess q = manuscriptS n) :
    lowerRegionsOfQuad q = candidateRegions n := by
  have hquad : q ∈ quadVecs n := by
    rw [sortedQuadVecs, Finset.mem_filter] at hq
    exact hq.1
  apply lowerRegionsOfQuad_eq_candidate_of_excess hquad
  rwa [manuscriptS_eq_concreteS] at hmax

/-- Sorted lower crossing-count realizations are enough to attain the
candidate region count. -/
theorem exists_region_eq_candidate_of_sortedLowerCrossingRealization
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal : SortedLowerCrossingRealization Arrangement region crossings n) :
    ∃ A : Arrangement, region A = candidateRegions n := by
  rcases exists_quadVecExcess_eq_manuscriptS n with ⟨q, hq, hmax⟩
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  refine ⟨A, ?_⟩
  have hregionLower : region A = lowerRegionsOfQuad q := by
    rw [hregion, hcross]
    rfl
  rw [hregionLower, lowerRegionsOfQuad_eq_candidate_of_manuscript_excess hq hmax]

/-- Monotone sorted lower realizations produce an arrangement whose region
count is at least the candidate.  Combined with the already-proved upper
bound, this is enough for exactness, and it avoids requiring the lower
construction to classify all extra intersections away. -/
theorem exists_candidate_le_region_of_sortedLowerCrossingBoundRealization
    {Arrangement : Type*} {region crossings : Arrangement → Rat} {n : Nat}
    (hreal :
      SortedLowerCrossingBoundRealization Arrangement region crossings n) :
    ∃ A : Arrangement, candidateRegions n ≤ region A := by
  rcases exists_quadVecExcess_eq_manuscriptS n with ⟨q, hq, hmax⟩
  rcases hreal q hq with ⟨A, hcross, hregion⟩
  refine ⟨A, ?_⟩
  have hcandidate :
      candidateRegions n = lowerRegionsOfQuad q :=
    (lowerRegionsOfQuad_eq_candidate_of_manuscript_excess hq hmax).symm
  rw [hcandidate, lowerRegionsOfQuad, hregion]
  linarith

/-- Sorted lower crossing-count realizations give lower attainment in the
`Nat.choose` candidate form. -/
theorem lower_attainment_of_sortedLowerCrossingRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerCrossingRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  intro n
  rcases exists_region_eq_candidate_of_sortedLowerCrossingRealization
      (hlower n) with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Monotone sorted lower crossing-count realizations give lower attainment as
an inequality in the `Nat.choose` candidate form. -/
theorem lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerCrossingBoundRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A := by
  intro n
  rcases exists_candidate_le_region_of_sortedLowerCrossingBoundRealization
      (hlower n) with ⟨A, hA⟩
  exact ⟨A, by simpa [candidateRegionsChoose_eq_candidateRegions] using hA⟩

/-- Incremental sorted lower realizations give lower attainment in the
`Nat.choose` candidate form. -/
theorem lower_attainment_of_sortedLowerIncrementalCrossingRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerIncrementalCrossingRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      P.region n A = candidateRegionsChoose n := by
  exact
    lower_attainment_of_sortedLowerCrossingRealizations_choose
      P (sortedLowerCrossingRealizations_of_incremental P hlower)

/-- Incremental monotone sorted lower realizations give lower attainment as an
inequality in the `Nat.choose` candidate form. -/
theorem lower_bound_attainment_of_sortedLowerIncrementalCrossingBoundRealizations_choose
    (P : TheoremOne.ProblemFamily.{u})
    {crossings : (n : Nat) → P.Arrangement n → Rat}
    (hlower : SortedLowerIncrementalCrossingBoundRealizations P crossings) :
    ∀ n : Nat, ∃ A : P.Arrangement n,
      candidateRegionsChoose n ≤ P.region n A := by
  exact
    lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
      P (sortedLowerCrossingBoundRealizations_of_incremental_bound P hlower)

/-- Upper bound plus monotone lower attainment imply the maximum statement.
The lower construction need only reach at least the candidate value; the upper
bound then forces equality for the chosen arrangement. -/
theorem maximumStatement_of_choose_upper_bound_and_lower_bound_attainment
    (P : TheoremOne.ProblemFamily.{u})
    (hupper :
      ∀ n : Nat, ∀ A : P.Arrangement n,
        P.region n A ≤ candidateRegionsChoose n)
    (hlower :
      ∀ n : Nat, ∃ A : P.Arrangement n,
        candidateRegionsChoose n ≤ P.region n A) :
    TheoremOne.MaximumStatement P := by
  intro n
  constructor
  · rcases hlower n with ⟨A, hA_lower⟩
    exact ⟨A, le_antisymm (hupper n A) hA_lower⟩
  · intro y hy
    rcases hy with ⟨A, rfl⟩
    exact hupper n A

/-- Strongest current manuscript-facing upper/lower package.  Compared with
`TheoremOneFinal.CanonicalExactCoordinateGeometricCrossingModelSubtheorems`,
the lower side only asks for sorted Karlsson crossing-count realizations. -/
structure CanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P
  lower_sorted_crossing_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      SortedLowerCrossingRealizations P lower_crossings

/-- The corresponding package for a family with a named maximum-count
function. -/
def MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalExactCoordinateGeometricCrossingModelSubtheorems P.toProblemFamily

/-- Monotone manuscript-facing upper/lower package.  The upper side is the
same exact-coordinate certificate package; the lower side only has to realize
arrangements whose crossing count is at least the sorted Karlsson value. -/
structure CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) : Prop where
  upper_certificates :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P
  lower_sorted_crossing_bound_realizations :
    ∃ lower_crossings : (n : Nat) → P.Arrangement n → Rat,
      SortedLowerCrossingBoundRealizations P lower_crossings

/-- Monotone package for a family with a named maximum-count function. -/
def MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Prop :=
  CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems
    P.toProblemFamily

/-- Upper bound from the manuscript-facing exact coordinate package. -/
theorem upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact
    TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
      P h.upper_certificates

/-- Upper bound from the monotone manuscript-facing package. -/
theorem upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P) :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A ≤ candidateRegionsChoose n := by
  exact
    TheoremOneEndToEnd.upper_bound_of_pairwise_canonical_exact_coordinate_geometric_certificates
      P h.upper_certificates

/-- Maximum-form Theorem 1 from exact upper data and sorted-only lower
crossing-count realizations. -/
theorem theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  rcases h.lower_sorted_crossing_realizations with ⟨lower_crossings, hlower⟩
  exact
    TheoremOneFormal.maximumStatement_of_choose_upper_bound_and_lower_attainment
      P
      (upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
        P h)
      (lower_attainment_of_sortedLowerCrossingRealizations_choose
        P (crossings := lower_crossings) hlower)

/-- Maximum-form Theorem 1 from exact upper data and monotone sorted lower
crossing-count realizations. -/
theorem theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
    (P : TheoremOne.ProblemFamily.{u})
    (h : CanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  rcases h.lower_sorted_crossing_bound_realizations with
    ⟨lower_crossings, hlower⟩
  exact
    maximumStatement_of_choose_upper_bound_and_lower_bound_attainment
      P
      (upper_bound_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
        P h)
      (lower_bound_attainment_of_sortedLowerCrossingBoundRealizations_choose
        P (crossings := lower_crossings) hlower)

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from exact
upper data and sorted-only lower crossing-count realizations. -/
theorem theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hmax :
      TheoremOne.MaximumStatement P.toProblemFamily :=
    theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P.toProblemFamily h
  have hformula := TheoremOne.formulaStatement_of_maximumStatement P hmax n
  rw [hformula]
  unfold candidateRegionsChoose
  rw [← manuscriptS_eq_concreteS n]

/-- Formula-form Theorem 1 with the manuscript's sorted `S(n)`, from exact
upper data and monotone sorted lower crossing-count realizations. -/
theorem theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_bound_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxCanonicalExactCoordinateGeometricCrossingModelBoundSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hmax :
      TheoremOne.MaximumStatement P.toProblemFamily :=
    theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_bound_certificates
      P.toProblemFamily h
  have hformula := TheoremOne.formulaStatement_of_maximumStatement P hmax n
  rw [hformula]
  unfold candidateRegionsChoose
  rw [← manuscriptS_eq_concreteS n]

/-- The final theorem using the manuscript's sorted `S(n)`, proved from the
ordinary final theorem plus the sorted/labeled extremum bridge. -/
theorem theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneFinal.MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  intro n
  have hfinal :=
    TheoremOneFinal.theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P h n
  rw [hfinal, manuscriptS_eq_concreteS]

/-- Single-size version of the manuscript-facing displayed formula. -/
theorem theorem_one_formula_at_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : TheoremOneFinal.MaxCanonicalExactCoordinateGeometricCrossingModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact
    theorem_one_formula_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P h n

end TheoremOneManuscript
end Lollipop

/-!
Proof component 13: `Manuscript.ConcreteModel`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Concrete manuscript-facing model interface.

This module is intentionally a packaging layer.  It spells out the remaining
Euclidean/model data in the terms used by the manuscript: for every
arrangement, global circle centers/radii, normalized stem directions, exact
pairwise crossing counts satisfying the canonical four-case crossing table,
and either the generic region equation in pair-sum form or a step-by-step
incremental region recurrence that implies it.  On the lower side it asks only
for sorted Karlsson blow-up crossing-count realizations.

All combinatorial, algebraic, Turan, matrix, and finite-extremum consequences
are then supplied by imported proved theorems.
-/

namespace Lollipop
namespace TheoremOneManuscript

universe u

/-- Upper Euclidean/model data for every arrangement in a problem family,
written as global extractor functions rather than existential certificates. -/
structure CanonicalExactUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  center :
    ∀ n : Nat, P.Arrangement n →
      Fin n → TheoremOneEndToEnd.PaulsenLinearAlgebra.R2
  radius :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  radius_pos :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 < radius n A i
  direction :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  direction_nonneg :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 ≤ direction n A i
  direction_lt_one :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      direction n A i < 1
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (direction n A) (center n A) (radius n A) i j
  regions_eq_pairSum :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      P.region n A = pairSum n (cross n A) + (n : Rat) + 1

namespace CanonicalExactUpperGeometryData

/-- Turn global upper geometry extractors into the strongest exact-coordinate
upper certificates used by the proved theorem stack. -/
noncomputable def toUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactUpperGeometryData P) :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P := by
  intro n A
  exact
    ⟨{ nNat := n
       regions := P.region n A
       center := h.center n A
       radius := h.radius n A
       radius_pos := h.radius_pos n A
       direction := h.direction n A
       direction_nonneg := h.direction_nonneg n A
       direction_lt_one := h.direction_lt_one n A
       cross := h.cross n A
       cross_le_case := h.cross_le_case n A
       regions_eq_pairSum := h.regions_eq_pairSum n A },
      rfl, rfl⟩

end CanonicalExactUpperGeometryData

/-- Upper Euclidean/model data where the region equation is derived from the
canonical previous-pair insertion recurrence rather than assumed directly. -/
structure CanonicalExactUpperGeometryIncrementalData
    (P : TheoremOne.ProblemFamily.{u}) where
  center :
    ∀ n : Nat, P.Arrangement n →
      Fin n → TheoremOneEndToEnd.PaulsenLinearAlgebra.R2
  radius :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  radius_pos :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 < radius n A i
  direction :
    ∀ n : Nat, P.Arrangement n → Fin n → ℝ
  direction_nonneg :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      0 ≤ direction n A i
  direction_lt_one :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i : Fin n,
      direction n A i < 1
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (direction n A) (center n A) (radius n A) i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace CanonicalExactUpperGeometryIncrementalData

/-- The incremental upper geometry data imply the direct pair-sum region
equation expected by the existing upper-certificate stack. -/
def toCanonicalExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactUpperGeometryIncrementalData P) :
    CanonicalExactUpperGeometryData P where
  center := h.center
  radius := h.radius
  radius_pos := h.radius_pos
  direction := h.direction
  direction_nonneg := h.direction_nonneg
  direction_lt_one := h.direction_lt_one
  cross := h.cross
  cross_le_case := h.cross_le_case
  regions_eq_pairSum := by
    intro n A
    exact OrderedIncrementalPairRegionData.target_eq_pairSum_add
      (h.region_increment n A)

/-- Turn incremental upper geometry data into the exact-coordinate upper
certificates used by the theorem stack. -/
noncomputable def toUpperCertificates
    {P : TheoremOne.ProblemFamily.{u}}
    (h : CanonicalExactUpperGeometryIncrementalData P) :
    TheoremOneEndToEnd.PairwiseCanonicalExactCoordinateGeometricUpperCertificates P :=
  h.toCanonicalExactUpperGeometryData.toUpperCertificates

end CanonicalExactUpperGeometryIncrementalData

/-- Sorted Karlsson lower data for a problem family. -/
structure SortedKarlssonLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  realizations : SortedLowerCrossingRealizations P crossings

/-- Sorted Karlsson lower data where the lower region equation is also
supplied by incremental insertion data. -/
structure SortedKarlssonIncrementalLowerData
    (P : TheoremOne.ProblemFamily.{u}) where
  crossings : (n : Nat) → P.Arrangement n → Rat
  realizations : SortedLowerIncrementalCrossingRealizations P crossings

namespace SortedKarlssonIncrementalLowerData

/-- Forget the incremental lower proof details after deriving
`regions = crossings + n + 1`. -/
def toSortedKarlssonLowerData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : SortedKarlssonIncrementalLowerData P) :
    SortedKarlssonLowerData P where
  crossings := h.crossings
  realizations :=
    sortedLowerCrossingRealizations_of_incremental
      P (crossings := h.crossings) h.realizations

end SortedKarlssonIncrementalLowerData

/-- The remaining manuscript-model obligations after all internal proof
layers have been discharged. -/
structure ConcreteModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryData P
  lower_karlsson : SortedKarlssonLowerData P

namespace ConcreteModelSubtheorems

/-- Convert the explicit manuscript-model obligations into the concise
subtheorem package used by the manuscript-facing final theorem. -/
noncomputable def toCanonicalExactCoordinateGeometricCrossingModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteModelSubtheorems P) :
    CanonicalExactCoordinateGeometricCrossingModelSubtheorems P where
  upper_certificates := h.upper_geometry.toUpperCertificates
  lower_sorted_crossing_realizations :=
    ⟨h.lower_karlsson.crossings, h.lower_karlsson.realizations⟩

end ConcreteModelSubtheorems

/-- Concrete manuscript-model obligations with the upper region equation
proved from canonical previous-pair insertion data. -/
structure ConcreteIncrementalModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : SortedKarlssonLowerData P

/-- Concrete manuscript-model obligations where both upper and lower region
equations are supplied by incremental insertion data. -/
structure ConcreteFullyIncrementalModelSubtheorems
    (P : TheoremOne.ProblemFamily.{u}) where
  upper_geometry : CanonicalExactUpperGeometryIncrementalData P
  lower_karlsson : SortedKarlssonIncrementalLowerData P

namespace ConcreteIncrementalModelSubtheorems

/-- Forget the incremental proof details after deriving the pair-sum region
equation. -/
def toConcreteModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteIncrementalModelSubtheorems P) :
    ConcreteModelSubtheorems P where
  upper_geometry := h.upper_geometry.toCanonicalExactUpperGeometryData
  lower_karlsson := h.lower_karlsson

end ConcreteIncrementalModelSubtheorems

namespace ConcreteFullyIncrementalModelSubtheorems

/-- Forget lower incremental proof details after deriving the ordinary sorted
Karlsson lower interface. -/
def toConcreteIncrementalModelSubtheorems
    {P : TheoremOne.ProblemFamily.{u}}
    (h : ConcreteFullyIncrementalModelSubtheorems P) :
    ConcreteIncrementalModelSubtheorems P where
  upper_geometry := h.upper_geometry
  lower_karlsson := h.lower_karlsson.toSortedKarlssonLowerData

end ConcreteFullyIncrementalModelSubtheorems

/-- Maximum-form Theorem 1 from the explicit concrete manuscript model
obligations. -/
theorem theorem_one_statement_proven_from_concrete_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact
    theorem_one_statement_proven_from_canonical_exact_coordinate_geometric_crossing_certificates
      P h.toCanonicalExactCoordinateGeometricCrossingModelSubtheorems

/-- Maximum-form Theorem 1 from concrete manuscript obligations whose region
equation is supplied by incremental insertion data. -/
theorem theorem_one_statement_proven_from_incremental_concrete_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_concrete_model
    P h.toConcreteModelSubtheorems

/-- Maximum-form Theorem 1 from fully incremental concrete manuscript
obligations. -/
theorem theorem_one_statement_proven_from_fully_incremental_concrete_model
    (P : TheoremOne.ProblemFamily.{u})
    (h : ConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFinal.TheoremOneStatement P := by
  exact theorem_one_statement_proven_from_incremental_concrete_model
    P h.toConcreteIncrementalModelSubtheorems

/-- Concrete manuscript-model obligations for a family with a named maximum
count function. -/
def MaxConcreteModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteModelSubtheorems P.toProblemFamily

/-- Incremental concrete manuscript-model obligations for a family with a
named maximum count function. -/
def MaxConcreteIncrementalModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteIncrementalModelSubtheorems P.toProblemFamily

/-- Fully incremental concrete manuscript-model obligations for a family with
a named maximum count function. -/
def MaxConcreteFullyIncrementalModelSubtheorems
    (P : TheoremOne.MaxProblemFamily.{u}) : Type u :=
  ConcreteFullyIncrementalModelSubtheorems P.toProblemFamily

/-- Formula-form Theorem 1 from the explicit concrete manuscript model
obligations. -/
theorem theorem_one_formula_statement_proven_from_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact
    theorem_one_formula_statement_proven_from_manuscript_canonical_exact_coordinate_geometric_crossing_certificates
      P h.toCanonicalExactCoordinateGeometricCrossingModelSubtheorems

/-- Formula-form Theorem 1 from incremental concrete manuscript obligations. -/
theorem theorem_one_formula_statement_proven_from_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_concrete_model
    P h.toConcreteModelSubtheorems

/-- Formula-form Theorem 1 from fully incremental concrete manuscript
obligations. -/
theorem theorem_one_formula_statement_proven_from_fully_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P) :
    TheoremOneFormulaStatement P := by
  exact theorem_one_formula_statement_proven_from_incremental_concrete_model
    P h.toConcreteIncrementalModelSubtheorems

/-- Single-size displayed formula from the explicit concrete manuscript model
obligations. -/
theorem theorem_one_formula_at_proven_from_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_concrete_model P h n

/-- Single-size displayed formula from incremental concrete manuscript
obligations. -/
theorem theorem_one_formula_at_proven_from_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_incremental_concrete_model P h n

/-- Single-size displayed formula from fully incremental concrete manuscript
obligations. -/
theorem theorem_one_formula_at_proven_from_fully_incremental_concrete_model
    (P : TheoremOne.MaxProblemFamily.{u})
    (h : MaxConcreteFullyIncrementalModelSubtheorems P)
    (n : Nat) :
    P.aLop n =
      4 * ((n.choose 2 : Nat) : Rat) + manuscriptS n + (n : Rat) + 1 := by
  exact theorem_one_formula_statement_proven_from_fully_incremental_concrete_model P h n

end TheoremOneManuscript
end Lollipop

/-!
Proof component 14: `Manuscript.PrimitiveGeometry.Basic`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Primitive coordinate records for lollipop geometry.

This file names the geometric objects that the remaining Euclidean part of
the manuscript must construct.  It deliberately does not assert a crossing
count theorem for these sets from first principles.  Instead, it gives a
mathlib-style coordinate model for a lollipop as a circle plus a ray, then
packages the exact pairwise crossing table and incremental region data as the
remaining primitive geometric certificate.  Lean proves that such primitive
records imply the canonical upper-data interface used by Theorem 1.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

universe u

abbrev R2 := TheoremOneEndToEnd.PaulsenLinearAlgebra.R2

/-- The coordinate circle with center `center` and radius `radius`, written
using the squared-distance model already used in Paulsen's formalized
appendix. -/
def circleSet (center : R2) (radius : ℝ) : Set R2 :=
  {p | TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2 p center = radius ^ 2}

/-- The half-line starting at `anchor` in direction `direction`. -/
def raySet (anchor direction : R2) : Set R2 :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ p = anchor + t • direction}

/-- The base point of a ray lies on that ray. -/
theorem anchor_mem_raySet (anchor direction : R2) :
    anchor ∈ raySet anchor direction := by
  refine ⟨0, by norm_num, ?_⟩
  simp

/-- A coordinate lollipop: a circle together with a ray attached at an anchor
point on the circle, plus the normalized stem direction used by the close-pair
theorem.  The separate predicate `EuclideanLollipop.IsRadialOutward` records
the stronger manuscript condition that the ray points radially outward. -/
structure EuclideanLollipop where
  center : R2
  radius : ℝ
  radius_pos : 0 < radius
  anchor : R2
  rayDirection : R2
  rayDirection_ne_zero : rayDirection ≠ 0
  anchor_on_circle : anchor ∈ circleSet center radius
  normalizedDirection : ℝ
  normalizedDirection_nonneg : 0 ≤ normalizedDirection
  normalizedDirection_lt_one : normalizedDirection < 1

namespace EuclideanLollipop

/-- The manuscript's radial-outward stem condition: the vector from the center
to the anchor is a positive multiple of the ray direction.  The ray direction
itself may be rescaled without changing the half-line. -/
def IsRadialOutward (L : EuclideanLollipop) : Prop :=
  ∃ scale : ℝ, 0 < scale ∧ L.anchor - L.center = scale • L.rayDirection

/-- The point set of a coordinate lollipop. -/
def carrier (L : EuclideanLollipop) : Set R2 :=
  circleSet L.center L.radius ∪ raySet L.anchor L.rayDirection

/-- The circle part is contained in the lollipop carrier. -/
theorem circle_subset_carrier (L : EuclideanLollipop) :
    circleSet L.center L.radius ⊆ L.carrier := by
  intro p hp
  exact Or.inl hp

/-- The ray part is contained in the lollipop carrier. -/
theorem ray_subset_carrier (L : EuclideanLollipop) :
    raySet L.anchor L.rayDirection ⊆ L.carrier := by
  intro p hp
  exact Or.inr hp

/-- The anchor lies on the ray part of the lollipop. -/
theorem anchor_mem_ray (L : EuclideanLollipop) :
    L.anchor ∈ raySet L.anchor L.rayDirection :=
  anchor_mem_raySet L.anchor L.rayDirection

/-- The anchor lies in the lollipop carrier. -/
theorem anchor_mem_carrier (L : EuclideanLollipop) :
    L.anchor ∈ L.carrier := by
  exact Or.inl L.anchor_on_circle

end EuclideanLollipop

/-- The set of intersection points between two coordinate lollipop carriers. -/
def pairIntersectionSet (L M : EuclideanLollipop) : Set R2 :=
  L.carrier ∩ M.carrier

/-- Membership in a primitive carrier intersection is exactly one of the four
circle/ray component membership patterns. -/
theorem mem_pairIntersectionSet_iff
    {L M : EuclideanLollipop} {p : R2} :
    p ∈ pairIntersectionSet L M ↔
      (p ∈ circleSet L.center L.radius ∧
        p ∈ circleSet M.center M.radius) ∨
      (p ∈ circleSet L.center L.radius ∧
        p ∈ raySet M.anchor M.rayDirection) ∨
      (p ∈ raySet L.anchor L.rayDirection ∧
        p ∈ circleSet M.center M.radius) ∨
      (p ∈ raySet L.anchor L.rayDirection ∧
        p ∈ raySet M.anchor M.rayDirection) := by
  unfold pairIntersectionSet EuclideanLollipop.carrier
  constructor
  · intro hp
    rcases hp with ⟨hL, hM⟩
    rcases hL with hLcircle | hLray
    · rcases hM with hMcircle | hMray
      · exact Or.inl ⟨hLcircle, hMcircle⟩
      · exact Or.inr (Or.inl ⟨hLcircle, hMray⟩)
    · rcases hM with hMcircle | hMray
      · exact Or.inr (Or.inr (Or.inl ⟨hLray, hMcircle⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hLray, hMray⟩))
  · intro hp
    rcases hp with hcc | hcr | hrc | hrr
    · exact ⟨Or.inl hcc.1, Or.inl hcc.2⟩
    · exact ⟨Or.inl hcr.1, Or.inr hcr.2⟩
    · exact ⟨Or.inr hrc.1, Or.inl hrc.2⟩
    · exact ⟨Or.inr hrr.1, Or.inr hrr.2⟩

/-- Two primitive circle memberships give a point of the primitive pair
carrier intersection. -/
theorem mem_pairIntersectionSet_of_mem_circleSets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ circleSet M.center M.radius) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2 (Or.inl ⟨hL, hM⟩)

/-- A primitive left-circle/right-ray membership pair gives a point of the
primitive pair carrier intersection. -/
theorem mem_pairIntersectionSet_of_mem_circleSet_of_mem_raySet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2 (Or.inr (Or.inl ⟨hL, hM⟩))

/-- A primitive left-ray/right-circle membership pair gives a point of the
primitive pair carrier intersection. -/
theorem mem_pairIntersectionSet_of_mem_raySet_of_mem_circleSet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ circleSet M.center M.radius) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2
    (Or.inr (Or.inr (Or.inl ⟨hL, hM⟩)))

/-- Two primitive ray memberships give a point of the primitive pair carrier
intersection. -/
theorem mem_pairIntersectionSet_of_mem_raySets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    p ∈ pairIntersectionSet L M :=
  mem_pairIntersectionSet_iff.2
    (Or.inr (Or.inr (Or.inr ⟨hL, hM⟩)))

/-- Pairwise carrier intersection is symmetric. -/
theorem pairIntersectionSet_symm (L M : EuclideanLollipop) :
    pairIntersectionSet L M = pairIntersectionSet M L := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.2, hp.1⟩
  · intro hp
    exact ⟨hp.2, hp.1⟩

/-- A finite coordinate lollipop arrangement. -/
structure EuclideanLollipopArrangement (n : Nat) where
  lollipop : Fin n → EuclideanLollipop

namespace EuclideanLollipopArrangement

/-- The point set of the `i`-th lollipop in an arrangement. -/
def carrier {n : Nat} (A : EuclideanLollipopArrangement n) (i : Fin n) :
    Set R2 :=
  (A.lollipop i).carrier

/-- The carrier-intersection set for a pair of lollipops in an arrangement. -/
def pairIntersectionSet {n : Nat}
    (A : EuclideanLollipopArrangement n) (i j : Fin n) : Set R2 :=
  PrimitiveGeometry.pairIntersectionSet (A.lollipop i) (A.lollipop j)

/-- Arrangement-indexed carrier-intersection membership is exactly one of
the four primitive component membership patterns. -/
theorem mem_pairIntersectionSet_iff {n : Nat}
    (A : EuclideanLollipopArrangement n) {i j : Fin n} {p : R2} :
    p ∈ A.pairIntersectionSet i j ↔
      (p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius) ∨
      (p ∈ circleSet (A.lollipop i).center (A.lollipop i).radius ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection) ∨
      (p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ circleSet (A.lollipop j).center (A.lollipop j).radius) ∨
      (p ∈ raySet (A.lollipop i).anchor (A.lollipop i).rayDirection ∧
        p ∈ raySet (A.lollipop j).anchor (A.lollipop j).rayDirection) :=
  PrimitiveGeometry.mem_pairIntersectionSet_iff

/-- Pairwise carrier intersection in an arrangement is symmetric. -/
theorem pairIntersectionSet_symm {n : Nat}
    (A : EuclideanLollipopArrangement n) (i j : Fin n) :
    A.pairIntersectionSet i j = A.pairIntersectionSet j i :=
  PrimitiveGeometry.pairIntersectionSet_symm (A.lollipop i) (A.lollipop j)

/-- Extract circle centers from a coordinate lollipop arrangement. -/
def center {n : Nat} (A : EuclideanLollipopArrangement n) (i : Fin n) : R2 :=
  (A.lollipop i).center

/-- Extract radii from a coordinate lollipop arrangement. -/
def radius {n : Nat} (A : EuclideanLollipopArrangement n) (i : Fin n) : ℝ :=
  (A.lollipop i).radius

/-- Extract normalized stem directions from a coordinate lollipop arrangement. -/
def normalizedDirection {n : Nat}
    (A : EuclideanLollipopArrangement n) (i : Fin n) : ℝ :=
  (A.lollipop i).normalizedDirection

theorem radius_pos {n : Nat} (A : EuclideanLollipopArrangement n)
    (i : Fin n) :
    0 < A.radius i :=
  (A.lollipop i).radius_pos

theorem normalizedDirection_nonneg {n : Nat}
    (A : EuclideanLollipopArrangement n) (i : Fin n) :
    0 ≤ A.normalizedDirection i :=
  (A.lollipop i).normalizedDirection_nonneg

theorem normalizedDirection_lt_one {n : Nat}
    (A : EuclideanLollipopArrangement n) (i : Fin n) :
    A.normalizedDirection i < 1 :=
  (A.lollipop i).normalizedDirection_lt_one

end EuclideanLollipopArrangement

/-- A local carrier-intersection certificate for one ordered pair `i < j` in a
primitive coordinate lollipop arrangement.  This is the one-pair version of
`PairwiseCarrierCrossingData`, intended for first-principles Euclidean
calculations that identify one finite crossing set at a time. -/
structure LocalPairCarrierCrossingData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) (i j : Fin n) (hij : i < j) where
  crossingPoints : Finset R2
  crossingPoints_spec :
    (crossingPoints : Set R2) = A.pairIntersectionSet i j
  cross_eq_card :
    cross i j = (crossingPoints.card : Rat)

/-- A finite carrier-intersection certificate for the pairwise crossing table
of one primitive coordinate lollipop arrangement.  In a fully first-principles
Euclidean proof, `crossingPoints_spec` is where the circle/ray intersection
calculation would identify the actual finite set of crossings. -/
structure PairwiseCarrierCrossingData
    {n : Nat} (A : EuclideanLollipopArrangement n)
    (cross : Fin n → Fin n → Rat) where
  crossingPoints : ∀ i j : Fin n, i < j → Finset R2
  crossingPoints_spec :
    ∀ i j : Fin n, ∀ hij : i < j,
      (crossingPoints i j hij : Set R2) = A.pairIntersectionSet i j
  cross_eq_card :
    ∀ i j : Fin n, ∀ hij : i < j,
      cross i j = ((crossingPoints i j hij).card : Rat)

namespace PairwiseCarrierCrossingData

/-- Assemble local one-pair carrier-intersection certificates into the global
pairwise crossing-data structure expected by the theorem stack. -/
noncomputable def ofLocal
    {n : Nat} {A : EuclideanLollipopArrangement n}
    {cross : Fin n → Fin n → Rat}
    (loc :
      ∀ i j : Fin n, ∀ hij : i < j,
        LocalPairCarrierCrossingData A cross i j hij) :
    PairwiseCarrierCrossingData A cross where
  crossingPoints := fun i j hij => (loc i j hij).crossingPoints
  crossingPoints_spec := by
    intro i j hij
    exact (loc i j hij).crossingPoints_spec
  cross_eq_card := by
    intro i j hij
    exact (loc i j hij).cross_eq_card

end PairwiseCarrierCrossingData

/-- Primitive upper geometric data for a problem family.  Compared with
`CanonicalExactUpperGeometryIncrementalData`, this names the actual coordinate
lollipops whose centers, radii, and stem directions feed the canonical
case-bound table.  The difficult remaining Euclidean certificate is exactly
the pairwise crossing-count table `cross_le_case`, together with the
incremental region data for those crossings. -/
structure PrimitiveExactUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (fun k => (arrangement n A).normalizedDirection k)
          (fun k => (arrangement n A).center k)
          (fun k => (arrangement n A).radius k) i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveExactUpperGeometryData

/-- Primitive coordinate lollipop data imply the canonical exact upper
geometry interface used by the manuscript theorem stack. -/
def toCanonicalExactUpperGeometryIncrementalData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveExactUpperGeometryData P) :
    CanonicalExactUpperGeometryIncrementalData P where
  center := fun n A i => (h.arrangement n A).center i
  radius := fun n A i => (h.arrangement n A).radius i
  radius_pos := by
    intro n A i
    exact (h.arrangement n A).radius_pos i
  direction := fun n A i => (h.arrangement n A).normalizedDirection i
  direction_nonneg := by
    intro n A i
    exact (h.arrangement n A).normalizedDirection_nonneg i
  direction_lt_one := by
    intro n A i
    exact (h.arrangement n A).normalizedDirection_lt_one i
  cross := h.cross
  cross_le_case := h.cross_le_case
  region_increment := h.region_increment

end PrimitiveExactUpperGeometryData

/-- Stronger primitive upper data where the pairwise crossing table is also
certified by finite intersection sets of the lollipop carriers. -/
structure PrimitiveCarrierCertifiedExactUpperGeometryData
    (P : TheoremOne.ProblemFamily.{u}) where
  arrangement :
    ∀ n : Nat, P.Arrangement n → EuclideanLollipopArrangement n
  cross :
    ∀ n : Nat, P.Arrangement n → Fin n → Fin n → Rat
  pairwise_crossings :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      PairwiseCarrierCrossingData (arrangement n A) (cross n A)
  cross_le_case :
    ∀ n : Nat, ∀ A : P.Arrangement n, ∀ i j : Fin n, i < j →
      cross n A i j ≤
        TheoremOneEndToEnd.canonicalCrossingCaseBound
          (fun k => (arrangement n A).normalizedDirection k)
          (fun k => (arrangement n A).center k)
          (fun k => (arrangement n A).radius k) i j
  region_increment :
    ∀ n : Nat, ∀ A : P.Arrangement n,
      OrderedIncrementalPairRegionData n (P.region n A) (cross n A)

namespace PrimitiveCarrierCertifiedExactUpperGeometryData

/-- Forget the explicit finite carrier-intersection witnesses after retaining
the exact pairwise crossing table they certify. -/
def toPrimitiveExactUpperGeometryData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierCertifiedExactUpperGeometryData P) :
    PrimitiveExactUpperGeometryData P where
  arrangement := h.arrangement
  cross := h.cross
  cross_le_case := h.cross_le_case
  region_increment := h.region_increment

/-- Carrier-certified primitive data imply the canonical exact upper geometry
interface used by the theorem stack. -/
def toCanonicalExactUpperGeometryIncrementalData
    {P : TheoremOne.ProblemFamily.{u}}
    (h : PrimitiveCarrierCertifiedExactUpperGeometryData P) :
    CanonicalExactUpperGeometryIncrementalData P :=
  h.toPrimitiveExactUpperGeometryData.toCanonicalExactUpperGeometryIncrementalData

end PrimitiveCarrierCertifiedExactUpperGeometryData

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 15: `Manuscript.PrimitiveGeometry.Qoppa`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Coordinate constructors for lollipops/qoppas.

The OEIS/Karlsson data list lollipops either by center or by anchor together
with a radius and a bearing angle.  This file formalizes those two
constructors for the primitive lollipop model.  The only trigonometry needed
is the mathlib identity `cos^2 + sin^2 = 1`, which proves that the anchor
lies on the specified circle.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- A point/vector in the primitive coordinate plane. -/
def point2 (x y : ℝ) : R2
  | 0 => x
  | 1 => y

@[simp] theorem point2_zero (x y : ℝ) :
    point2 x y 0 = x := rfl

@[simp] theorem point2_one (x y : ℝ) :
    point2 x y 1 = y := rfl

/-- Unit direction vector with bearing angle `theta`. -/
noncomputable def angleDirection (theta : ℝ) : R2 :=
  point2 (Real.cos theta) (Real.sin theta)

@[simp] theorem angleDirection_zero (theta : ℝ) :
    angleDirection theta 0 = Real.cos theta := rfl

@[simp] theorem angleDirection_one (theta : ℝ) :
    angleDirection theta 1 = Real.sin theta := rfl

/-- A bearing direction has squared norm `1`. -/
theorem normSq2_angleDirection (theta : ℝ) :
    normSq2 (angleDirection theta) = 1 := by
  unfold normSq2 dot2 angleDirection point2
  nlinarith [Real.cos_sq_add_sin_sq theta]

/-- A bearing direction is nonzero. -/
theorem angleDirection_ne_zero (theta : ℝ) :
    angleDirection theta ≠ 0 := by
  intro hzero
  have hnorm := normSq2_angleDirection theta
  rw [hzero] at hnorm
  norm_num [normSq2, dot2] at hnorm

/-- If the anchor is `center + radius * direction(theta)`, then it lies on
the circle of radius `radius` around `center`. -/
theorem center_plus_radius_direction_mem_circleSet
    (center : R2) (radius theta : ℝ) :
    center + radius • angleDirection theta ∈ circleSet center radius := by
  unfold circleSet distSq2 normSq2 dot2 angleDirection point2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  nlinarith [Real.cos_sq_add_sin_sq theta]

/-- If the center is `anchor - radius * direction(theta)`, then the anchor
lies on that circle. -/
theorem anchor_mem_circleSet_anchor_minus_radius_direction
    (anchor : R2) (radius theta : ℝ) :
    anchor ∈ circleSet (anchor - radius • angleDirection theta) radius := by
  unfold circleSet distSq2 normSq2 dot2 angleDirection point2
  simp [Pi.sub_apply, Pi.smul_apply]
  nlinarith [Real.cos_sq_add_sin_sq theta]

namespace EuclideanLollipop

/-- Constructor matching `Qoppa.from_center(center, radius, theta)`: the
anchor is `center + radius * (cos theta, sin theta)`, and the ray points in
that bearing direction. -/
noncomputable def fromCenter
    (center : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    EuclideanLollipop where
  center := center
  radius := radius
  radius_pos := hradius
  anchor := center + radius • angleDirection theta
  rayDirection := angleDirection theta
  rayDirection_ne_zero := angleDirection_ne_zero theta
  anchor_on_circle :=
    center_plus_radius_direction_mem_circleSet center radius theta
  normalizedDirection := normalizedDirection
  normalizedDirection_nonneg := hdir_nonneg
  normalizedDirection_lt_one := hdir_lt_one

/-- The `fromCenter` constructor satisfies the manuscript's radial-outward
stem condition. -/
theorem fromCenter_isRadialOutward
    (center : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).IsRadialOutward := by
  refine ⟨radius, hradius, ?_⟩
  ext i
  simp [fromCenter, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]

/-- Constructor matching `Qoppa.from_anchor(anchor, radius, theta)`: the
center is `anchor - radius * (cos theta, sin theta)`, and the ray points in
that bearing direction. -/
noncomputable def fromAnchor
    (anchor : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    EuclideanLollipop where
  center := anchor - radius • angleDirection theta
  radius := radius
  radius_pos := hradius
  anchor := anchor
  rayDirection := angleDirection theta
  rayDirection_ne_zero := angleDirection_ne_zero theta
  anchor_on_circle :=
    anchor_mem_circleSet_anchor_minus_radius_direction anchor radius theta
  normalizedDirection := normalizedDirection
  normalizedDirection_nonneg := hdir_nonneg
  normalizedDirection_lt_one := hdir_lt_one

/-- The `fromAnchor` constructor satisfies the manuscript's radial-outward
stem condition. -/
theorem fromAnchor_isRadialOutward
    (anchor : R2) (radius theta normalizedDirection : ℝ)
    (hradius : 0 < radius)
    (hdir_nonneg : 0 ≤ normalizedDirection)
    (hdir_lt_one : normalizedDirection < 1) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).IsRadialOutward := by
  refine ⟨radius, hradius, ?_⟩
  ext i
  simp [fromAnchor, Pi.sub_apply, Pi.smul_apply]

end EuclideanLollipop

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 16: `Manuscript.PrimitiveGeometry.DirectionBridge`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Direction-to-dot-product bridge.

The close-direction input in the manuscript is recorded as a normalized
cyclic-angle relation.  The geometric route certificates, however, consume
coordinate inequalities involving dot products of bearing vectors.  This file
formalizes the elementary trigonometric bridge between those two languages.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- Dot product of two unit bearing vectors is the cosine of the angle
difference. -/
theorem dot2_angleDirection_angleDirection (a b : ℝ) :
    dot2 (angleDirection a) (angleDirection b) = Real.cos (a - b) := by
  unfold dot2 angleDirection point2
  rw [Real.cos_sub]

/-- A trigonometric nonnegativity hypothesis transfers directly to the dot
product of the corresponding bearing vectors. -/
theorem dot2_angleDirection_nonneg_of_cos_sub_nonneg
    {a b : ℝ} (h : 0 ≤ Real.cos (a - b)) :
    0 ≤ dot2 (angleDirection a) (angleDirection b) := by
  simpa [dot2_angleDirection_angleDirection] using h

/-- Specialization of the dot-product formula to normalized directions, where
`a` and `b` represent turns on `R/Z`. -/
theorem dot2_angleDirection_two_pi (a b : ℝ) :
    dot2 (angleDirection (2 * Real.pi * a))
      (angleDirection (2 * Real.pi * b)) =
        Real.cos (2 * Real.pi * (a - b)) := by
  rw [dot2_angleDirection_angleDirection]
  congr 1
  ring

/-- Cosine is nonnegative when a real number is either within one quarter turn
of zero or within one quarter turn of a full turn. -/
theorem cos_two_pi_mul_nonneg_of_abs_le_quarter_or_three_quarters_le_abs
    {d : ℝ} (hdlt : |d| < 1)
    (hclose : |d| ≤ (1 / 4 : ℝ) ∨ (3 / 4 : ℝ) ≤ |d|) :
    0 ≤ Real.cos (2 * Real.pi * d) := by
  rcases hclose with hquarter | hwrap
  · have hd_bounds : -(1 / 4 : ℝ) ≤ d ∧ d ≤ (1 / 4 : ℝ) :=
      abs_le.mp hquarter
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos],
      by nlinarith [Real.pi_pos]⟩
  · have hcos_abs :
        Real.cos (2 * Real.pi * d) =
          Real.cos (2 * Real.pi * |d|) := by
      by_cases hd_nonneg : 0 ≤ d
      · rw [abs_of_nonneg hd_nonneg]
      · have hd_nonpos : d ≤ 0 := le_of_not_ge hd_nonneg
        rw [abs_of_nonpos hd_nonpos]
        rw [show 2 * Real.pi * -d = -(2 * Real.pi * d) by ring]
        rw [Real.cos_neg]
    have hcos_wrap :
        Real.cos (2 * Real.pi * |d|) =
          Real.cos (2 * Real.pi * (1 - |d|)) := by
      rw [← Real.cos_two_pi_sub (2 * Real.pi * |d|)]
      congr 1
      ring
    have hwrap_bounds :
        0 ≤ 1 - |d| ∧ 1 - |d| ≤ (1 / 4 : ℝ) := by
      exact ⟨by linarith [le_of_lt hdlt], by linarith⟩
    rw [hcos_abs, hcos_wrap]
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos],
      by nlinarith [Real.pi_pos]⟩

/-- The cyclic-close predicate on normalized directions implies nonnegative
cosine of the corresponding angular difference, provided both directions lie
in one fundamental interval. -/
theorem cos_two_pi_mul_sub_nonneg_of_cyclicClosePair
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hclose : CloseDirection.cyclicClosePair a b) :
    0 ≤ Real.cos (2 * Real.pi * (a - b)) := by
  have hdlt : |a - b| < 1 := by
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  exact
    cos_two_pi_mul_nonneg_of_abs_le_quarter_or_three_quarters_le_abs
      (d := a - b) hdlt (by
        simpa [CloseDirection.cyclicClosePair] using hclose)

/-- A cyclic-close pair of normalized directions has nonnegative dot product
between the associated bearing vectors. -/
theorem dot2_angleDirection_two_pi_nonneg_of_cyclicClosePair
    {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hclose : CloseDirection.cyclicClosePair a b) :
    0 ≤ dot2 (angleDirection (2 * Real.pi * a))
      (angleDirection (2 * Real.pi * b)) := by
  rw [dot2_angleDirection_two_pi]
  exact cos_two_pi_mul_sub_nonneg_of_cyclicClosePair
    ha0 ha1 hb0 hb1 hclose

/-- Same statement using the arrangement-level close relation. -/
theorem dot2_angleDirection_two_pi_nonneg_of_cyclicClose
    {V : Type*} (theta : V → ℝ) {i j : V}
    (hi0 : 0 ≤ theta i) (hi1 : theta i < 1)
    (hj0 : 0 ≤ theta j) (hj1 : theta j < 1)
    (hclose : CloseDirection.cyclicClose theta i j) :
    0 ≤ dot2 (angleDirection (2 * Real.pi * theta i))
      (angleDirection (2 * Real.pi * theta j)) := by
  exact dot2_angleDirection_two_pi_nonneg_of_cyclicClosePair
    hi0 hi1 hj0 hj1 hclose

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 17: `Manuscript.PrimitiveGeometry.NormalizedBearing`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Compatibility between stored ray directions and normalized directions.

`EuclideanLollipop` deliberately keeps the actual ray vector and the
normalized angle used by the close-pair pigeonhole as separate fields.  This
file names the compatibility condition needed to use close-pair angle data in
coordinate route certificates.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd
open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- A lollipop's stored ray vector is the bearing vector determined by its
normalized direction. -/
def EuclideanLollipop.HasNormalizedBearing
    (L : EuclideanLollipop) : Prop :=
  L.rayDirection = angleDirection (2 * Real.pi * L.normalizedDirection)

namespace EuclideanLollipop

/-- Bearing vectors are unchanged after adding one full turn. -/
theorem angleDirection_add_two_pi (theta : ℝ) :
    angleDirection (theta + 2 * Real.pi) = angleDirection theta := by
  ext i; fin_cases i <;> simp [angleDirection, point2,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Bearing vectors are unchanged after subtracting one full turn. -/
theorem angleDirection_sub_two_pi (theta : ℝ) :
    angleDirection (theta - 2 * Real.pi) = angleDirection theta := by
  ext i; fin_cases i <;> simp [angleDirection, point2,
    Real.cos_sub_two_pi, Real.sin_sub_two_pi]

/-- The `fromCenter` constructor has normalized-bearing compatibility when
its angle is exactly the normalized angle in radians. -/
theorem fromCenter_hasNormalizedBearing
    {center : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromCenter, htheta]

/-- The `fromCenter` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one negative full turn. -/
theorem fromCenter_hasNormalizedBearing_of_eq_sub_two_pi
    {center : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection - 2 * Real.pi) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromCenter, htheta, angleDirection_sub_two_pi]

/-- The `fromCenter` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one positive full turn. -/
theorem fromCenter_hasNormalizedBearing_of_eq_add_two_pi
    {center : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection + 2 * Real.pi) :
    (fromCenter center radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromCenter, htheta, angleDirection_add_two_pi]

/-- The `fromAnchor` constructor has normalized-bearing compatibility when
its angle is exactly the normalized angle in radians. -/
theorem fromAnchor_hasNormalizedBearing
    {anchor : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromAnchor, htheta]

/-- The `fromAnchor` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one negative full turn. -/
theorem fromAnchor_hasNormalizedBearing_of_eq_sub_two_pi
    {anchor : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection - 2 * Real.pi) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromAnchor, htheta, angleDirection_sub_two_pi]

/-- The `fromAnchor` constructor has normalized-bearing compatibility when
its angle differs from the normalized angle by one positive full turn. -/
theorem fromAnchor_hasNormalizedBearing_of_eq_add_two_pi
    {anchor : R2} {radius theta normalizedDirection : ℝ}
    {hradius : 0 < radius}
    {hdir_nonneg : 0 ≤ normalizedDirection}
    {hdir_lt_one : normalizedDirection < 1}
    (htheta : theta = 2 * Real.pi * normalizedDirection + 2 * Real.pi) :
    (fromAnchor anchor radius theta normalizedDirection
      hradius hdir_nonneg hdir_lt_one).HasNormalizedBearing := by
  simp [HasNormalizedBearing, fromAnchor, htheta, angleDirection_add_two_pi]

/-- Under normalized-bearing compatibility, a cyclic-close pair has
nonnegative dot product between the actual stored ray directions. -/
theorem dot2_rayDirection_nonneg_of_cyclicClosePair
    {L M : EuclideanLollipop}
    (hL : L.HasNormalizedBearing)
    (hM : M.HasNormalizedBearing)
    (hclose :
      CloseDirection.cyclicClosePair L.normalizedDirection
        M.normalizedDirection) :
    0 ≤ dot2 L.rayDirection M.rayDirection := by
  rw [hL, hM]
  exact dot2_angleDirection_two_pi_nonneg_of_cyclicClosePair
    L.normalizedDirection_nonneg L.normalizedDirection_lt_one
    M.normalizedDirection_nonneg M.normalizedDirection_lt_one hclose

end EuclideanLollipop

namespace EuclideanLollipopArrangement

/-- Every lollipop in the arrangement has normalized-bearing compatibility. -/
def HasNormalizedBearings
    {n : Nat} (A : EuclideanLollipopArrangement n) : Prop :=
  ∀ i : Fin n, (A.lollipop i).HasNormalizedBearing

/-- Arrangement-level form of the close-direction-to-ray-dot bridge. -/
theorem dot2_rayDirection_nonneg_of_cyclicClose
    {n : Nat} {A : EuclideanLollipopArrangement n} {i j : Fin n}
    (hA : A.HasNormalizedBearings)
    (hclose :
      CloseDirection.cyclicClose
        (fun k => A.normalizedDirection k) i j) :
    0 ≤ dot2 (A.lollipop i).rayDirection (A.lollipop j).rayDirection := by
  exact
    EuclideanLollipop.dot2_rayDirection_nonneg_of_cyclicClosePair
      (hA i) (hA j)
      (by
        simpa [CloseDirection.cyclicClose,
          EuclideanLollipopArrangement.normalizedDirection] using hclose)

end EuclideanLollipopArrangement

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 18: `Manuscript.PrimitiveGeometry.SphereBridge`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
Bridge from primitive coordinate circles to mathlib Euclidean spheres.

The primitive lollipop layer records points as `Fin 2 -> ℝ` because Paulsen's
linear-algebra appendix uses explicit coordinates.  Mathlib's Euclidean
line/sphere theorems use the `L^2` product space `EuclideanSpace ℝ (Fin 2)`.
This file connects the two views by the canonical `WithLp.toLp 2` wrapper and
proves that the primitive squared-distance circle is exactly the preimage of a
mathlib Euclidean sphere.
-/

namespace Lollipop
namespace TheoremOneManuscript
namespace PrimitiveGeometry

open TheoremOneEndToEnd.PaulsenLinearAlgebra

/-- The same coordinate plane as `R2`, equipped with mathlib's `L^2`
inner-product norm. -/
abbrev EuclideanR2 : Type :=
  EuclideanSpace ℝ (Fin 2)

/-- View the primitive coordinate plane as mathlib's Euclidean plane. -/
def toEuclideanR2 (x : R2) : EuclideanR2 :=
  WithLp.toLp 2 x

/-- The lift from primitive coordinates to `EuclideanSpace` is injective. -/
theorem toEuclideanR2_injective : Function.Injective toEuclideanR2 := by
  intro x y hxy
  exact WithLp.toLp_injective 2 hxy

@[simp]
theorem toEuclideanR2_apply (x : R2) (i : Fin 2) :
    toEuclideanR2 x i = x i :=
  rfl

@[simp]
theorem toEuclideanR2_add (x y : R2) :
    toEuclideanR2 (x + y) = toEuclideanR2 x + toEuclideanR2 y := by
  ext i
  rfl

@[simp]
theorem toEuclideanR2_smul (t : ℝ) (x : R2) :
    toEuclideanR2 (t • x) = t • toEuclideanR2 x := by
  ext i
  rfl

@[simp]
theorem toEuclideanR2_sub (x y : R2) :
    toEuclideanR2 (x - y) = toEuclideanR2 x - toEuclideanR2 y := by
  ext i
  rfl

/-- The explicit squared distance used in Paulsen's coordinate calculations is
the squared `L^2` distance after lifting to `EuclideanSpace`. -/
theorem distSq2_eq_euclidean_dist_sq (x y : R2) :
    distSq2 x y = dist (toEuclideanR2 x) (toEuclideanR2 y) ^ 2 := by
  calc
    distSq2 x y =
        (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
          unfold distSq2 normSq2 dot2
          simp [Pi.sub_apply]
          ring
    _ = ∑ i : Fin 2, dist (toEuclideanR2 x i) (toEuclideanR2 y i) ^ 2 := by
          simp [Fin.sum_univ_two, Real.dist_eq, sq_abs]
    _ = dist (toEuclideanR2 x) (toEuclideanR2 y) ^ 2 := by
          exact (EuclideanSpace.dist_sq_eq (toEuclideanR2 x) (toEuclideanR2 y)).symm

/-- The oriented two-dimensional determinant in the primitive coordinate
model. -/
def det2 (x y : R2) : ℝ :=
  x 0 * y 1 - x 1 * y 0

/-- The two-dimensional Lagrange identity:
`|x|^2 |y|^2 = <x,y>^2 + det(x,y)^2`. -/
theorem normSq2_mul_normSq2_eq_dot2_sq_add_det2_sq
    (x y : R2) :
    normSq2 x * normSq2 y = dot2 x y ^ 2 + det2 x y ^ 2 := by
  unfold normSq2 dot2 det2
  ring

/-- The squared determinant is bounded by the product of squared norms. -/
theorem det2_sq_le_normSq2_mul_normSq2 (x y : R2) :
    det2 x y ^ 2 ≤ normSq2 x * normSq2 y := by
  have h := normSq2_mul_normSq2_eq_dot2_sq_add_det2_sq x y
  nlinarith [sq_nonneg (dot2 x y)]

/-- Moving along a line in direction `v` does not change the determinant
against `v`. -/
theorem det2_line_vadd_sub_right
    (anchor center direction : R2) (t : ℝ) :
    det2 ((anchor + t • direction) - center) direction =
      det2 (anchor - center) direction := by
  unfold det2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Squared distance from a center after moving by `t` along a primitive
direction. -/
theorem distSq2_vadd_smul_sub
    (anchor center direction : R2) (t : ℝ) :
    distSq2 (anchor + t • direction) center =
      distSq2 anchor center +
        2 * t * dot2 (anchor - center) direction +
        t ^ 2 * normSq2 direction := by
  unfold distSq2 normSq2 dot2
  simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- In the primitive coordinate plane, zero determinant with a nonzero first
vector means the second vector is a scalar multiple of the first. -/
theorem exists_smul_eq_of_det2_eq_zero_of_ne_zero
    {v w : R2} (hv : v ≠ 0) (hdet : det2 v w = 0) :
    ∃ c : ℝ, w = c • v := by
  by_cases hv0 : v 0 = 0
  · have hv1 : v 1 ≠ 0 := by
      intro hv1
      apply hv
      ext i
      fin_cases i <;> simp [hv0, hv1]
    have hw0 : w 0 = 0 := by
      have hmul : v 1 * w 0 = 0 := by
        have hneg : -(v 1 * w 0) = 0 := by
          simpa [det2, hv0] using hdet
        exact neg_eq_zero.mp hneg
      exact (mul_eq_zero.mp hmul).resolve_left hv1
    refine ⟨w 1 / v 1, ?_⟩
    ext i
    fin_cases i
    · simp [hw0, hv0]
    · simp [Pi.smul_apply]
      field_simp [hv1]
  · have hcoord : v 0 * w 1 = v 1 * w 0 := by
      unfold det2 at hdet
      nlinarith
    refine ⟨w 0 / v 0, ?_⟩
    ext i
    fin_cases i
    · simp [Pi.smul_apply]
      field_simp [hv0]
    · simp [Pi.smul_apply]
      field_simp [hv0]
      nlinarith

/-- The mathlib Euclidean sphere corresponding to a primitive coordinate
circle. -/
def euclideanSphere (center : R2) (radius : ℝ) :
    EuclideanGeometry.Sphere EuclideanR2 where
  center := toEuclideanR2 center
  radius := radius

/-- Two lifted primitive coordinate spheres are different exactly when their
primitive centers or radii are different. -/
theorem euclideanSphere_ne_iff
    {center₁ center₂ : R2} {radius₁ radius₂ : ℝ} :
    euclideanSphere center₁ radius₁ ≠ euclideanSphere center₂ radius₂ ↔
      center₁ ≠ center₂ ∨ radius₁ ≠ radius₂ := by
  rw [EuclideanGeometry.Sphere.ne_iff]
  constructor
  · rintro (hcenter | hradius)
    · exact Or.inl fun h => hcenter (by simp [euclideanSphere, h])
    · exact Or.inr hradius
  · rintro (hcenter | hradius)
    · exact Or.inl fun h => hcenter (toEuclideanR2_injective h)
    · exact Or.inr hradius

/-- Unequal primitive centers give unequal lifted spheres. -/
theorem euclideanSphere_ne_of_center_ne
    {center₁ center₂ : R2} {radius₁ radius₂ : ℝ}
    (hcenter : center₁ ≠ center₂) :
    euclideanSphere center₁ radius₁ ≠ euclideanSphere center₂ radius₂ :=
  euclideanSphere_ne_iff.2 (Or.inl hcenter)

/-- Unequal radii give unequal lifted spheres. -/
theorem euclideanSphere_ne_of_radius_ne
    {center₁ center₂ : R2} {radius₁ radius₂ : ℝ}
    (hradius : radius₁ ≠ radius₂) :
    euclideanSphere center₁ radius₁ ≠ euclideanSphere center₂ radius₂ :=
  euclideanSphere_ne_iff.2 (Or.inr hradius)

/-- Membership in the primitive squared-coordinate circle is exactly
membership in the corresponding mathlib Euclidean sphere, for nonnegative
radii. -/
theorem mem_circleSet_iff_mem_euclideanSphere
    {p center : R2} {radius : ℝ} (hradius : 0 ≤ radius) :
    p ∈ circleSet center radius ↔
      toEuclideanR2 p ∈ euclideanSphere center radius := by
  unfold circleSet euclideanSphere
  rw [EuclideanGeometry.mem_sphere]
  constructor
  · intro hp
    have hsq :
        dist (toEuclideanR2 p) (toEuclideanR2 center) ^ 2 = radius ^ 2 := by
      rw [← distSq2_eq_euclidean_dist_sq]
      exact hp
    exact (sq_eq_sq₀ dist_nonneg hradius).1 hsq
  · intro hp
    have hp' : dist (toEuclideanR2 p) (toEuclideanR2 center) = radius := by
      simpa using hp
    show distSq2 p center = radius ^ 2
    rw [distSq2_eq_euclidean_dist_sq, hp']

/-- Set-level version of `mem_circleSet_iff_mem_euclideanSphere`. -/
theorem circleSet_eq_preimage_euclideanSphere
    (center : R2) {radius : ℝ} (hradius : 0 ≤ radius) :
    circleSet center radius =
      {p : R2 | toEuclideanR2 p ∈ euclideanSphere center radius} := by
  ext p
  exact mem_circleSet_iff_mem_euclideanSphere (p := p) hradius

/-- The primitive ray, lifted to mathlib's Euclidean plane. -/
def euclideanRaySet (anchor direction : R2) : Set EuclideanR2 :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ p = toEuclideanR2 anchor + t • toEuclideanR2 direction}

/-- Membership in a primitive ray is exactly membership in the corresponding
lifted Euclidean ray. -/
theorem mem_raySet_iff_mem_euclideanRaySet {p anchor direction : R2} :
    p ∈ raySet anchor direction ↔
      toEuclideanR2 p ∈ euclideanRaySet anchor direction := by
  unfold raySet euclideanRaySet
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, by simp⟩
  · rintro ⟨t, ht, hp⟩
    refine ⟨t, ht, ?_⟩
    apply WithLp.toLp_injective 2
    simpa [toEuclideanR2] using hp

/-- Set-level version of `mem_raySet_iff_mem_euclideanRaySet`. -/
theorem raySet_eq_preimage_euclideanRaySet (anchor direction : R2) :
    raySet anchor direction =
      {p : R2 | toEuclideanR2 p ∈ euclideanRaySet anchor direction} := by
  ext p
  exact mem_raySet_iff_mem_euclideanRaySet

/-- The supporting affine line of a lifted lollipop ray. -/
noncomputable def euclideanRayLine (L : EuclideanLollipop) :
    AffineSubspace ℝ EuclideanR2 :=
  line[ℝ, toEuclideanR2 L.anchor,
    toEuclideanR2 L.rayDirection +ᵥ toEuclideanR2 L.anchor]

/-- The lifted anchor lies on its ray's supporting affine line. -/
theorem anchor_mem_euclideanRayLine (L : EuclideanLollipop) :
    toEuclideanR2 L.anchor ∈ euclideanRayLine L := by
  unfold euclideanRayLine
  exact left_mem_affineSpan_pair ℝ _ _

/-- The endpoint obtained by adding one direction vector lies on the ray's
supporting affine line. -/
theorem direction_vadd_anchor_mem_euclideanRayLine (L : EuclideanLollipop) :
    toEuclideanR2 L.rayDirection +ᵥ toEuclideanR2 L.anchor ∈
      euclideanRayLine L := by
  unfold euclideanRayLine
  exact right_mem_affineSpan_pair ℝ _ _

/-- The direction of the supporting affine line of a lifted ray. -/
theorem euclideanRayLine_direction (L : EuclideanLollipop) :
    (euclideanRayLine L).direction =
      ℝ ∙ toEuclideanR2 L.rayDirection := by
  unfold euclideanRayLine
  rw [direction_affineSpan, vectorSpan_pair_rev]
  simp [vsub_eq_sub, vadd_eq_add]

/-- The supporting-line definition agrees with the `mk'` line used by
mathlib's line/sphere intersection theorem. -/
theorem euclideanRayLine_eq_mk' (L : EuclideanLollipop) :
    euclideanRayLine L =
      AffineSubspace.mk' (toEuclideanR2 L.anchor)
        (ℝ ∙ toEuclideanR2 L.rayDirection) := by
  have hmk :
      AffineSubspace.mk' (toEuclideanR2 L.anchor)
          (euclideanRayLine L).direction =
        euclideanRayLine L :=
    AffineSubspace.mk'_eq (anchor_mem_euclideanRayLine L)
  rw [← hmk, euclideanRayLine_direction]

/-- If one ray anchor does not lie on another ray's supporting line, the two
supporting lines are different. -/
theorem euclideanRayLine_ne_of_anchor_notMem
    {L M : EuclideanLollipop}
    (hanchor : toEuclideanR2 L.anchor ∉ euclideanRayLine M) :
    euclideanRayLine L ≠ euclideanRayLine M := by
  intro hline
  exact hanchor (by simpa [hline] using anchor_mem_euclideanRayLine L)

/-- Nonparallel primitive ray directions give distinct lifted supporting
lines.  This is a convenient coordinate route for discharging the generic
ray-line noncoincidence field in carrier-counting certificates. -/
theorem euclideanRayLine_ne_of_det2_rayDirection_ne_zero
    {L M : EuclideanLollipop}
    (hdet : det2 L.rayDirection M.rayDirection ≠ 0) :
    euclideanRayLine L ≠ euclideanRayLine M := by
  intro hline
  have hdir :
      ℝ ∙ toEuclideanR2 L.rayDirection =
        ℝ ∙ toEuclideanR2 M.rayDirection := by
    have hcongr := congrArg AffineSubspace.direction hline
    simpa [euclideanRayLine_direction] using hcongr
  have hmem :
      toEuclideanR2 M.rayDirection ∈
        ℝ ∙ toEuclideanR2 L.rayDirection := by
    rw [hdir]
    exact Submodule.mem_span_singleton_self (toEuclideanR2 M.rayDirection)
  rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
  have hMdir : M.rayDirection = c • L.rayDirection := by
    apply toEuclideanR2_injective
    calc
      toEuclideanR2 M.rayDirection = c • toEuclideanR2 L.rayDirection :=
        hc.symm
      _ = toEuclideanR2 (c • L.rayDirection) := by simp
  have hzero : det2 L.rayDirection M.rayDirection = 0 := by
    rw [hMdir]
    unfold det2
    simp [Pi.smul_apply]
    ring
  exact hdet hzero

/-- The lifted carrier of a primitive lollipop. -/
def euclideanCarrier (L : EuclideanLollipop) : Set EuclideanR2 :=
  (euclideanSphere L.center L.radius : Set EuclideanR2) ∪
    euclideanRaySet L.anchor L.rayDirection

/-- Lifted intersection set of two primitive lollipop carriers. -/
def euclideanPairIntersectionSet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  euclideanCarrier L ∩ euclideanCarrier M

/-- Lifted pairwise carrier intersection is symmetric. -/
theorem euclideanPairIntersectionSet_symm (L M : EuclideanLollipop) :
    euclideanPairIntersectionSet L M = euclideanPairIntersectionSet M L := by
  ext p
  constructor
  · intro hp
    exact ⟨hp.2, hp.1⟩
  · intro hp
    exact ⟨hp.2, hp.1⟩

/-- Lifted circle-circle component of a carrier intersection. -/
def euclideanCircleCircleSet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  (euclideanSphere L.center L.radius : Set EuclideanR2) ∩
    (euclideanSphere M.center M.radius : Set EuclideanR2)

/-- Lifted circle-ray component of a carrier intersection. -/
def euclideanCircleRaySet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  (euclideanSphere L.center L.radius : Set EuclideanR2) ∩
    euclideanRaySet M.anchor M.rayDirection

/-- Lifted ray-circle component of a carrier intersection. -/
def euclideanRayCircleSet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  euclideanRaySet L.anchor L.rayDirection ∩
    (euclideanSphere M.center M.radius : Set EuclideanR2)

/-- Lifted ray-ray component of a carrier intersection. -/
def euclideanRayRaySet (L M : EuclideanLollipop) : Set EuclideanR2 :=
  euclideanRaySet L.anchor L.rayDirection ∩
    euclideanRaySet M.anchor M.rayDirection

/-- Primitive circle memberships lift to the Euclidean circle-circle
component. -/
theorem mem_euclideanCircleCircleSet_of_mem_circleSets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ circleSet M.center M.radius) :
    toEuclideanR2 p ∈ euclideanCircleCircleSet L M := by
  constructor
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := L.center) (radius := L.radius)
      L.radius_pos.le).1 hL
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := M.center) (radius := M.radius)
      M.radius_pos.le).1 hM

/-- Primitive circle/ray memberships lift to the Euclidean circle-ray
component. -/
theorem mem_euclideanCircleRaySet_of_mem_circleSet_of_mem_raySet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ circleSet L.center L.radius)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    toEuclideanR2 p ∈ euclideanCircleRaySet L M := by
  constructor
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := L.center) (radius := L.radius)
      L.radius_pos.le).1 hL
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := M.anchor) (direction := M.rayDirection)).1 hM

/-- Primitive ray/circle memberships lift to the Euclidean ray-circle
component. -/
theorem mem_euclideanRayCircleSet_of_mem_raySet_of_mem_circleSet
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ circleSet M.center M.radius) :
    toEuclideanR2 p ∈ euclideanRayCircleSet L M := by
  constructor
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := L.anchor) (direction := L.rayDirection)).1 hL
  · exact (mem_circleSet_iff_mem_euclideanSphere
      (p := p) (center := M.center) (radius := M.radius)
      M.radius_pos.le).1 hM

/-- Primitive ray memberships lift to the Euclidean ray-ray component. -/
theorem mem_euclideanRayRaySet_of_mem_raySets
    {L M : EuclideanLollipop} {p : R2}
    (hL : p ∈ raySet L.anchor L.rayDirection)
    (hM : p ∈ raySet M.anchor M.rayDirection) :
    toEuclideanR2 p ∈ euclideanRayRaySet L M := by
  constructor
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := L.anchor) (direction := L.rayDirection)).1 hL
  · exact (mem_raySet_iff_mem_euclideanRaySet
      (p := p) (anchor := M.anchor) (direction := M.rayDirection)).1 hM

/-- If the distance between two circle centers is greater than the sum of the
radii, their lifted circle-circle component is empty. -/
theorem euclideanCircleCircleSet_empty_of_radius_add_lt_dist
    {L M : EuclideanLollipop}
    (hfar :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center)) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  intro p hp
  have hpL :
      dist p (toEuclideanR2 L.center) = L.radius :=
    EuclideanGeometry.mem_sphere.1 hp.1
  have hpM :
      dist p (toEuclideanR2 M.center) = M.radius :=
    EuclideanGeometry.mem_sphere.1 hp.2
  have htri :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ≤
        dist (toEuclideanR2 L.center) p +
          dist p (toEuclideanR2 M.center) :=
    dist_triangle _ _ _
  rw [dist_comm (toEuclideanR2 L.center) p, hpL, hpM] at htri
  linarith

/-- Squared-coordinate version of the far-apart circle emptiness criterion. -/
theorem euclideanCircleCircleSet_empty_of_radius_add_sq_lt_distSq2
    {L M : EuclideanLollipop}
    (hfar :
      (L.radius + M.radius) ^ 2 < distSq2 L.center M.center) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  have hsum_nonneg : 0 ≤ L.radius + M.radius :=
    add_nonneg L.radius_pos.le M.radius_pos.le
  have hfar_euclidean :
      (L.radius + M.radius) ^ 2 <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 := by
    rwa [distSq2_eq_euclidean_dist_sq] at hfar
  have hdist :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) := by
    exact (sq_lt_sq₀ hsum_nonneg dist_nonneg).1 hfar_euclidean
  exact euclideanCircleCircleSet_empty_of_radius_add_lt_dist hdist

/-- If one circle lies strictly inside the other, with center distance plus
the smaller radius less than the larger radius, then the lifted circle-circle
component is empty. -/
theorem euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
    {L M : EuclideanLollipop}
    (hcontained :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + L.radius <
        M.radius) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  intro p hp
  have hpL :
      dist p (toEuclideanR2 L.center) = L.radius :=
    EuclideanGeometry.mem_sphere.1 hp.1
  have hpM :
      dist p (toEuclideanR2 M.center) = M.radius :=
    EuclideanGeometry.mem_sphere.1 hp.2
  have htri :
      dist p (toEuclideanR2 M.center) ≤
        dist p (toEuclideanR2 L.center) +
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
    dist_triangle _ _ _
  rw [hpL, hpM] at htri
  linarith

/-- Symmetric strictly-contained circle emptiness criterion. -/
theorem euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
    {L M : EuclideanLollipop}
    (hcontained :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + M.radius <
        L.radius) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  intro p hp
  have hempty :
      ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet M L :=
    euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
      (L := M) (M := L) (by
        rw [dist_comm]
        exact hcontained)
  exact hempty p ⟨hp.2, hp.1⟩

/-- Squared-coordinate strictly-contained criterion with `L` inside `M`. -/
theorem euclideanCircleCircleSet_empty_of_distSq2_lt_right_sub_left_radius_sq
    {L M : EuclideanLollipop}
    (hradius : L.radius < M.radius)
    (hcontained :
      distSq2 L.center M.center < (M.radius - L.radius) ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  have hdiff_nonneg : 0 ≤ M.radius - L.radius := by
    linarith
  have hdist_sq :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
        (M.radius - L.radius) ^ 2 := by
    simpa [distSq2_eq_euclidean_dist_sq] using hcontained
  have hdist :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
        M.radius - L.radius := by
    exact (sq_lt_sq₀ dist_nonneg hdiff_nonneg).1 hdist_sq
  exact
    euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
      (by linarith)

/-- Squared-coordinate strictly-contained criterion with `M` inside `L`. -/
theorem euclideanCircleCircleSet_empty_of_distSq2_lt_left_sub_right_radius_sq
    {L M : EuclideanLollipop}
    (hradius : M.radius < L.radius)
    (hcontained :
      distSq2 L.center M.center < (L.radius - M.radius) ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  have hdiff_nonneg : 0 ≤ L.radius - M.radius := by
    linarith
  have hdist_sq :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
        (L.radius - M.radius) ^ 2 := by
    simpa [distSq2_eq_euclidean_dist_sq] using hcontained
  have hdist :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
        L.radius - M.radius := by
    exact (sq_lt_sq₀ dist_nonneg hdiff_nonneg).1 hdist_sq
  exact
    euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
      (by linarith)

/-- A concrete certificate that the two primitive circles do not meet.  The
squared constructors match the coordinate inequalities used elsewhere in the
formalization. -/
inductive CircleCircleNoMeetData (L M : EuclideanLollipop) : Type where
  | farApart :
      L.radius + M.radius <
        dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) →
      CircleCircleNoMeetData L M
  | farApartSq :
      (L.radius + M.radius) ^ 2 < distSq2 L.center M.center →
      CircleCircleNoMeetData L M
  | leftInside :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + L.radius <
        M.radius →
      CircleCircleNoMeetData L M
  | rightInside :
      dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) + M.radius <
        L.radius →
      CircleCircleNoMeetData L M
  | leftInsideSq :
      L.radius < M.radius →
      distSq2 L.center M.center < (M.radius - L.radius) ^ 2 →
      CircleCircleNoMeetData L M
  | rightInsideSq :
      M.radius < L.radius →
      distSq2 L.center M.center < (L.radius - M.radius) ^ 2 →
      CircleCircleNoMeetData L M

namespace CircleCircleNoMeetData

/-- A no-meet circle certificate proves that the lifted circle-circle component
is empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : CircleCircleNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleCircleSet L M := by
  cases D with
  | farApart hfar =>
      exact euclideanCircleCircleSet_empty_of_radius_add_lt_dist hfar
  | farApartSq hfar =>
      exact euclideanCircleCircleSet_empty_of_radius_add_sq_lt_distSq2 hfar
  | leftInside hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_dist_add_left_radius_lt_right_radius
          hcontained
  | rightInside hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_dist_add_right_radius_lt_left_radius
          hcontained
  | leftInsideSq hradius hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_distSq2_lt_right_sub_left_radius_sq
          hradius hcontained
  | rightInsideSq hradius hcontained =>
      exact
        euclideanCircleCircleSet_empty_of_distSq2_lt_left_sub_right_radius_sq
          hradius hcontained

/-- A no-meet certificate is one formal branch of Paulsen's intriguing-circle
relation. -/
theorem circleIntriguingPair
    {L M : EuclideanLollipop}
    (D : CircleCircleNoMeetData L M) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
      L.radius M.radius L.center M.center := by
  unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguingPair
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleObtuseCondition
  intro hobtuse
  cases D with
  | farApart hfar =>
      have hsum_nonneg : 0 ≤ L.radius + M.radius :=
        add_nonneg L.radius_pos.le M.radius_pos.le
      have hdist_nonneg :
          0 ≤ dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
        dist_nonneg
      have hfar_sq :
          (L.radius + M.radius) ^ 2 <
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        (sq_lt_sq₀ hsum_nonneg hdist_nonneg).2 hfar
      have hdistSq :
          distSq2 L.center M.center =
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        distSq2_eq_euclidean_dist_sq L.center M.center
      linarith
  | farApartSq hfar =>
      linarith
  | leftInside hcontained =>
      have hdiff_pos : 0 < M.radius - L.radius := by
        have hnonneg :
            0 ≤ dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
          dist_nonneg
        linarith
      have hdist :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
            M.radius - L.radius := by
        linarith
      have hdist_sq :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
            (M.radius - L.radius) ^ 2 :=
        (sq_lt_sq₀ dist_nonneg hdiff_pos.le).2 hdist
      have hdistSq :
          distSq2 L.center M.center =
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        distSq2_eq_euclidean_dist_sq L.center M.center
      have hdiff_sq_lt :
          (M.radius - L.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith
  | rightInside hcontained =>
      have hdiff_pos : 0 < L.radius - M.radius := by
        have hnonneg :
            0 ≤ dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) :=
          dist_nonneg
        linarith
      have hdist :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) <
            L.radius - M.radius := by
        linarith
      have hdist_sq :
          dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 <
            (L.radius - M.radius) ^ 2 :=
        (sq_lt_sq₀ dist_nonneg hdiff_pos.le).2 hdist
      have hdistSq :
          distSq2 L.center M.center =
            dist (toEuclideanR2 L.center) (toEuclideanR2 M.center) ^ 2 :=
        distSq2_eq_euclidean_dist_sq L.center M.center
      have hdiff_sq_lt :
          (L.radius - M.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith
  | leftInsideSq _hradius hcontained =>
      have hdiff_sq_lt :
          (M.radius - L.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith
  | rightInsideSq _hradius hcontained =>
      have hdiff_sq_lt :
          (L.radius - M.radius) ^ 2 < L.radius ^ 2 + M.radius ^ 2 := by
        nlinarith [L.radius_pos, M.radius_pos]
      linarith

end CircleCircleNoMeetData

/-- Arrangement-indexed form: a no-meet certificate for the two primitive
circles is one formal way to prove the pair is circle-intriguing. -/
theorem circleIntriguing_of_circleCircleNoMeetData
    {n : Nat} {A : EuclideanLollipopArrangement n} {i j : Fin n}
    (D : CircleCircleNoMeetData (A.lollipop i) (A.lollipop j)) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing
      (fun k : Fin n => A.center k) (fun k : Fin n => A.radius k) i j := by
  simpa [TheoremOneEndToEnd.PaulsenLinearAlgebra.circleIntriguing,
    EuclideanLollipopArrangement.center, EuclideanLollipopArrangement.radius]
    using D.circleIntriguingPair

/-- The primitive carrier is exactly the preimage of the lifted Euclidean
carrier. -/
theorem carrier_eq_preimage_euclideanCarrier (L : EuclideanLollipop) :
    L.carrier = {p : R2 | toEuclideanR2 p ∈ euclideanCarrier L} := by
  ext p
  unfold EuclideanLollipop.carrier euclideanCarrier
  constructor
  · intro hp
    rcases hp with hcircle | hray
    · exact Or.inl
        ((mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hcircle)
    · exact Or.inr
        ((mem_raySet_iff_mem_euclideanRaySet
          (p := p) (anchor := L.anchor) (direction := L.rayDirection)).1 hray)
  · intro hp
    rcases hp with hcircle | hray
    · exact Or.inl
        ((mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).2 hcircle)
    · exact Or.inr
        ((mem_raySet_iff_mem_euclideanRaySet
          (p := p) (anchor := L.anchor) (direction := L.rayDirection)).2 hray)

/-- Primitive carrier intersection is the preimage of the lifted carrier
intersection. -/
theorem pairIntersectionSet_eq_preimage_euclideanPairIntersectionSet
    (L M : EuclideanLollipop) :
    pairIntersectionSet L M =
      {p : R2 | toEuclideanR2 p ∈ euclideanPairIntersectionSet L M} := by
  ext p
  simp [pairIntersectionSet, euclideanPairIntersectionSet,
    carrier_eq_preimage_euclideanCarrier]

/-- A lifted carrier intersection splits into the four circle/ray component
types. -/
theorem mem_euclideanPairIntersectionSet_iff
    {L M : EuclideanLollipop} {p : EuclideanR2} :
    p ∈ euclideanPairIntersectionSet L M ↔
      p ∈ euclideanCircleCircleSet L M ∨
        p ∈ euclideanCircleRaySet L M ∨
          p ∈ euclideanRayCircleSet L M ∨
            p ∈ euclideanRayRaySet L M := by
  unfold euclideanPairIntersectionSet euclideanCarrier
    euclideanCircleCircleSet euclideanCircleRaySet
    euclideanRayCircleSet euclideanRayRaySet
  constructor
  · rintro ⟨hL, hM⟩
    rcases hL with hLcircle | hLray
    · rcases hM with hMcircle | hMray
      · exact Or.inl ⟨hLcircle, hMcircle⟩
      · exact Or.inr (Or.inl ⟨hLcircle, hMray⟩)
    · rcases hM with hMcircle | hMray
      · exact Or.inr (Or.inr (Or.inl ⟨hLray, hMcircle⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hLray, hMray⟩))
  · intro h
    rcases h with hcc | hcr | hrc | hrr
    · exact ⟨Or.inl hcc.1, Or.inl hcc.2⟩
    · exact ⟨Or.inl hcr.1, Or.inr hcr.2⟩
    · exact ⟨Or.inr hrc.1, Or.inl hrc.2⟩
    · exact ⟨Or.inr hrr.1, Or.inr hrr.2⟩

/-- Specialization of mathlib's two-sphere theorem: if two lifted primitive
circles are distinct and already have two distinct common points, then every
other common point is one of those two. -/
theorem eq_or_eq_of_mem_euclideanCircleCircleSet_of_two_witnesses
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanCircleCircleSet L M)
    (hp₂ : p₂ ∈ euclideanCircleCircleSet L M)
    (hp : p ∈ euclideanCircleCircleSet L M) :
    p = p₁ ∨ p = p₂ := by
  have hd : Module.finrank ℝ EuclideanR2 = 2 := by
    simp [EuclideanR2]
  exact
    EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := EuclideanR2) (P := EuclideanR2)
      (s₁ := euclideanSphere L.center L.radius)
      (s₂ := euclideanSphere M.center M.radius)
      hd hLM hp₁₂ hp₁.1 hp₂.1 hp.1 hp₁.2 hp₂.2 hp.2

/-- Unlifted primitive-circle version of the two-circle bound. -/
theorem eq_or_eq_of_mem_circleSet_inter_of_two_witnesses
    {L M : EuclideanLollipop}
    (hLM :
      euclideanSphere L.center L.radius ≠ euclideanSphere M.center M.radius)
    {p₁ p₂ p : R2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ circleSet L.center L.radius ∧
      p₁ ∈ circleSet M.center M.radius)
    (hp₂ : p₂ ∈ circleSet L.center L.radius ∧
      p₂ ∈ circleSet M.center M.radius)
    (hp : p ∈ circleSet L.center L.radius ∧
      p ∈ circleSet M.center M.radius) :
    p = p₁ ∨ p = p₂ := by
  have hp₁_lift : toEuclideanR2 p₁ ∈ euclideanCircleCircleSet L M := by
    exact ⟨
      (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hp₁.1,
      (mem_circleSet_iff_mem_euclideanSphere M.radius_pos.le).1 hp₁.2⟩
  have hp₂_lift : toEuclideanR2 p₂ ∈ euclideanCircleCircleSet L M := by
    exact ⟨
      (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hp₂.1,
      (mem_circleSet_iff_mem_euclideanSphere M.radius_pos.le).1 hp₂.2⟩
  have hp_lift : toEuclideanR2 p ∈ euclideanCircleCircleSet L M := by
    exact ⟨
      (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1 hp.1,
      (mem_circleSet_iff_mem_euclideanSphere M.radius_pos.le).1 hp.2⟩
  have hp₁₂_lift : toEuclideanR2 p₁ ≠ toEuclideanR2 p₂ := by
    intro h
    apply hp₁₂
    exact WithLp.toLp_injective 2 h
  rcases eq_or_eq_of_mem_euclideanCircleCircleSet_of_two_witnesses
      hLM hp₁₂_lift hp₁_lift hp₂_lift hp_lift with h | h
  · exact Or.inl (WithLp.toLp_injective 2 h)
  · exact Or.inr (WithLp.toLp_injective 2 h)

/-- The lifted anchor lies on the lifted mathlib sphere. -/
theorem anchor_mem_euclideanSphere (L : EuclideanLollipop) :
    toEuclideanR2 L.anchor ∈ euclideanSphere L.center L.radius := by
  exact (mem_circleSet_iff_mem_euclideanSphere L.radius_pos.le).1
    L.anchor_on_circle

/-- A lifted ray point lies on the affine line through the anchor in the ray
direction. -/
theorem mem_anchor_line_of_mem_euclideanRaySet
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp : p ∈ euclideanRaySet L.anchor L.rayDirection) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
      (ℝ ∙ toEuclideanR2 L.rayDirection) := by
  rcases hp with ⟨t, _ht, rfl⟩
  rw [AffineSubspace.mem_mk']
  simpa using
    Submodule.smul_mem (ℝ ∙ toEuclideanR2 L.rayDirection) t
      (Submodule.mem_span_singleton_self (toEuclideanR2 L.rayDirection))

/-- A lifted ray point lies on the named supporting affine line of the ray. -/
theorem mem_euclideanRayLine_of_mem_euclideanRaySet
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp : p ∈ euclideanRaySet L.anchor L.rayDirection) :
    p ∈ euclideanRayLine L := by
  rw [euclideanRayLine_eq_mk']
  exact mem_anchor_line_of_mem_euclideanRaySet L hp

/-- A point in a ray-circle component lies on the affine line of the ray. -/
theorem mem_anchor_line_of_mem_euclideanRayCircleSet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayCircleSet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
      (ℝ ∙ toEuclideanR2 L.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet L hp.1

/-- A point in a circle-ray component lies on the affine line of the ray. -/
theorem mem_anchor_line_of_mem_euclideanCircleRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanCircleRaySet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 M.anchor)
      (ℝ ∙ toEuclideanR2 M.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet M hp.2

/-- A point in a ray-circle component lies on the named supporting line of
the ray. -/
theorem mem_euclideanRayLine_of_mem_euclideanRayCircleSet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayCircleSet L M) :
    p ∈ euclideanRayLine L :=
  mem_euclideanRayLine_of_mem_euclideanRaySet L hp.1

/-- A point in a circle-ray component lies on the named supporting line of
the ray. -/
theorem mem_euclideanRayLine_of_mem_euclideanCircleRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanCircleRaySet L M) :
    p ∈ euclideanRayLine M :=
  mem_euclideanRayLine_of_mem_euclideanRaySet M hp.2

/-- Orthogonal projection of a point to a lollipop ray's supporting line.  The
supporting line is nonempty because it contains the ray anchor. -/
noncomputable def euclideanRayLineProjection
    (L : EuclideanLollipop) (p : EuclideanR2) : EuclideanR2 :=
  letI : Nonempty (euclideanRayLine L) :=
    ⟨⟨toEuclideanR2 L.anchor, anchor_mem_euclideanRayLine L⟩⟩
  EuclideanGeometry.orthogonalProjection (euclideanRayLine L) p

/-- The projection helper realizes the metric distance to the supporting line
as `Metric.infDist`. -/
theorem dist_euclideanRayLineProjection_eq_infDist
    (L : EuclideanLollipop) (p : EuclideanR2) :
    dist p (euclideanRayLineProjection L p) =
      Metric.infDist p (euclideanRayLine L : Set EuclideanR2) := by
  unfold euclideanRayLineProjection
  letI : Nonempty (euclideanRayLine L) :=
    ⟨⟨toEuclideanR2 L.anchor, anchor_mem_euclideanRayLine L⟩⟩
  exact EuclideanGeometry.dist_orthogonalProjection_eq_infDist
    (euclideanRayLine L) p

/-- If the center of a circle is farther from a ray's supporting line than the
circle radius, then the circle-ray component is empty.  This is a convenient
mathlib projection/`infDist` certificate for one common close/intriguing
savings branch. -/
theorem euclideanCircleRaySet_empty_of_radius_lt_infDist_rayLine
    {L M : EuclideanLollipop}
    (hsep :
      L.radius <
        Metric.infDist (toEuclideanR2 L.center)
          (euclideanRayLine M : Set EuclideanR2)) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M := by
  intro p hp
  have hp_line : p ∈ (euclideanRayLine M : Set EuclideanR2) :=
    mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp
  have hp_sphere :
      dist p (toEuclideanR2 L.center) = L.radius :=
    EuclideanGeometry.mem_sphere.1 hp.1
  have hle :
      Metric.infDist (toEuclideanR2 L.center)
          (euclideanRayLine M : Set EuclideanR2) ≤
        dist (toEuclideanR2 L.center) p :=
    Metric.infDist_le_dist_of_mem hp_line
  rw [dist_comm (toEuclideanR2 L.center) p, hp_sphere] at hle
  linarith

/-- Symmetric line-distance certificate for an empty ray-circle component. -/
theorem euclideanRayCircleSet_empty_of_radius_lt_infDist_rayLine
    {L M : EuclideanLollipop}
    (hsep :
      M.radius <
        Metric.infDist (toEuclideanR2 M.center)
          (euclideanRayLine L : Set EuclideanR2)) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M := by
  intro p hp
  have hp_line : p ∈ (euclideanRayLine L : Set EuclideanR2) :=
    mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp
  have hp_sphere :
      dist p (toEuclideanR2 M.center) = M.radius :=
    EuclideanGeometry.mem_sphere.1 hp.2
  have hle :
      Metric.infDist (toEuclideanR2 M.center)
          (euclideanRayLine L : Set EuclideanR2) ≤
        dist (toEuclideanR2 M.center) p :=
    Metric.infDist_le_dist_of_mem hp_line
  rw [dist_comm (toEuclideanR2 M.center) p, hp_sphere] at hle
  linarith

/-- Coordinate determinant criterion for an empty circle-ray component.  If
the squared perpendicular determinant from the circle center to the ray's
supporting line is larger than `radius^2 * |direction|^2`, then the line, and
hence the ray, misses the circle. -/
theorem euclideanCircleRaySet_empty_of_radius_sq_mul_normSq2_lt_det2_sq
    {L M : EuclideanLollipop}
    (hsep :
      L.radius ^ 2 * normSq2 M.rayDirection <
        det2 (M.anchor - L.center) M.rayDirection ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M := by
  intro p hp
  rcases hp.2 with ⟨t, _ht, hp_eq⟩
  let x : R2 := M.anchor + t • M.rayDirection
  have hx_det :
      det2 (x - L.center) M.rayDirection =
        det2 (M.anchor - L.center) M.rayDirection := by
    simpa [x] using
      det2_line_vadd_sub_right M.anchor L.center M.rayDirection t
  have hx_dist :
      distSq2 x L.center = L.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 L.center) = L.radius :=
      EuclideanGeometry.mem_sphere.1 hp.1
    have hsq :
        dist p (toEuclideanR2 L.center) ^ 2 = L.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 L.center) ^ 2 =
          L.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hdet_le :
      det2 (x - L.center) M.rayDirection ^ 2 ≤
        normSq2 (x - L.center) * normSq2 M.rayDirection :=
    det2_sq_le_normSq2_mul_normSq2 (x - L.center) M.rayDirection
  have hnorm :
      normSq2 (x - L.center) = L.radius ^ 2 := by
    simpa [distSq2] using hx_dist
  rw [hx_det, hnorm] at hdet_le
  exact (not_lt_of_ge hdet_le) hsep

/-- If a ray starts outside a circle and initially points weakly away from the
circle center, then the half-line ray misses the circle.  Unlike the
supporting-line separation certificate, this can apply when the full line
meets the circle behind the ray anchor. -/
theorem euclideanCircleRaySet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
    {L M : EuclideanLollipop}
    (hanchor : L.radius ^ 2 < distSq2 M.anchor L.center)
    (hdot : 0 ≤ dot2 (M.anchor - L.center) M.rayDirection) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M := by
  intro p hp
  rcases hp.2 with ⟨t, ht, hp_eq⟩
  let x : R2 := M.anchor + t • M.rayDirection
  have hx_dist :
      distSq2 x L.center = L.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 L.center) = L.radius :=
      EuclideanGeometry.mem_sphere.1 hp.1
    have hsq :
        dist p (toEuclideanR2 L.center) ^ 2 = L.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 L.center) ^ 2 =
          L.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hnorm_nonneg : 0 ≤ normSq2 M.rayDirection := by
    unfold normSq2 dot2
    nlinarith [sq_nonneg (M.rayDirection 0),
      sq_nonneg (M.rayDirection 1)]
  have hmove_nonneg :
      0 ≤
        2 * t * dot2 (M.anchor - L.center) M.rayDirection +
          t ^ 2 * normSq2 M.rayDirection := by
    have hfirst :
        0 ≤ 2 * t * dot2 (M.anchor - L.center) M.rayDirection := by
      nlinarith
    have hsecond : 0 ≤ t ^ 2 * normSq2 M.rayDirection := by
      nlinarith [sq_nonneg t, hnorm_nonneg]
    nlinarith
  have hx_expand :=
    distSq2_vadd_smul_sub M.anchor L.center M.rayDirection t
  have hx_gt : L.radius ^ 2 < distSq2 x L.center := by
    rw [show x = M.anchor + t • M.rayDirection by rfl]
    rw [hx_expand]
    nlinarith
  rw [hx_dist] at hx_gt
  exact (lt_irrefl (L.radius ^ 2)) hx_gt

/-- Symmetric coordinate determinant criterion for an empty ray-circle
component. -/
theorem euclideanRayCircleSet_empty_of_radius_sq_mul_normSq2_lt_det2_sq
    {L M : EuclideanLollipop}
    (hsep :
      M.radius ^ 2 * normSq2 L.rayDirection <
        det2 (L.anchor - M.center) L.rayDirection ^ 2) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M := by
  intro p hp
  rcases hp.1 with ⟨t, _ht, hp_eq⟩
  let x : R2 := L.anchor + t • L.rayDirection
  have hx_det :
      det2 (x - M.center) L.rayDirection =
        det2 (L.anchor - M.center) L.rayDirection := by
    simpa [x] using
      det2_line_vadd_sub_right L.anchor M.center L.rayDirection t
  have hx_dist :
      distSq2 x M.center = M.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 M.center) = M.radius :=
      EuclideanGeometry.mem_sphere.1 hp.2
    have hsq :
        dist p (toEuclideanR2 M.center) ^ 2 = M.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 M.center) ^ 2 =
          M.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hdet_le :
      det2 (x - M.center) L.rayDirection ^ 2 ≤
        normSq2 (x - M.center) * normSq2 L.rayDirection :=
    det2_sq_le_normSq2_mul_normSq2 (x - M.center) L.rayDirection
  have hnorm :
      normSq2 (x - M.center) = M.radius ^ 2 := by
    simpa [distSq2] using hx_dist
  rw [hx_det, hnorm] at hdet_le
  exact (not_lt_of_ge hdet_le) hsep

/-- Symmetric half-line criterion for an empty ray-circle component. -/
theorem euclideanRayCircleSet_empty_of_radius_sq_lt_anchor_distSq2_of_dot_nonneg
    {L M : EuclideanLollipop}
    (hanchor : M.radius ^ 2 < distSq2 L.anchor M.center)
    (hdot : 0 ≤ dot2 (L.anchor - M.center) L.rayDirection) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M := by
  intro p hp
  rcases hp.1 with ⟨t, ht, hp_eq⟩
  let x : R2 := L.anchor + t • L.rayDirection
  have hx_dist :
      distSq2 x M.center = M.radius ^ 2 := by
    have hp_sphere :
        dist p (toEuclideanR2 M.center) = M.radius :=
      EuclideanGeometry.mem_sphere.1 hp.2
    have hsq :
        dist p (toEuclideanR2 M.center) ^ 2 = M.radius ^ 2 := by
      rw [hp_sphere]
    have hp_to : p = toEuclideanR2 x := by
      simpa [x] using hp_eq
    have hsq' :
        dist (toEuclideanR2 x) (toEuclideanR2 M.center) ^ 2 =
          M.radius ^ 2 := by
      simpa [hp_to] using hsq
    simpa [distSq2_eq_euclidean_dist_sq] using hsq'.symm.symm
  have hnorm_nonneg : 0 ≤ normSq2 L.rayDirection := by
    unfold normSq2 dot2
    nlinarith [sq_nonneg (L.rayDirection 0),
      sq_nonneg (L.rayDirection 1)]
  have hmove_nonneg :
      0 ≤
        2 * t * dot2 (L.anchor - M.center) L.rayDirection +
          t ^ 2 * normSq2 L.rayDirection := by
    have hfirst :
        0 ≤ 2 * t * dot2 (L.anchor - M.center) L.rayDirection := by
      nlinarith
    have hsecond : 0 ≤ t ^ 2 * normSq2 L.rayDirection := by
      nlinarith [sq_nonneg t, hnorm_nonneg]
    nlinarith
  have hx_expand :=
    distSq2_vadd_smul_sub L.anchor M.center L.rayDirection t
  have hx_gt : M.radius ^ 2 < distSq2 x M.center := by
    rw [show x = L.anchor + t • L.rayDirection by rfl]
    rw [hx_expand]
    nlinarith
  rw [hx_dist] at hx_gt
  exact (lt_irrefl (M.radius ^ 2)) hx_gt

/-- Coordinate criterion for an empty ray-ray component.  Parallel ray
directions whose supporting lines have nonzero offset determinant cannot
share a point. -/
theorem euclideanRayRaySet_empty_of_det2_directions_eq_zero_of_det2_anchor_sub_ne_zero
    {L M : EuclideanLollipop}
    (hparallel : det2 L.rayDirection M.rayDirection = 0)
    (hoffset : det2 (M.anchor - L.anchor) L.rayDirection ≠ 0) :
    ∀ p : EuclideanR2, p ∉ euclideanRayRaySet L M := by
  intro p hp
  rcases hp.1 with ⟨s, _hs, hpL⟩
  rcases hp.2 with ⟨t, _ht, hpM⟩
  rcases exists_smul_eq_of_det2_eq_zero_of_ne_zero
      L.rayDirection_ne_zero hparallel with ⟨c, hMdir⟩
  have hpoints :
      L.anchor + s • L.rayDirection =
        M.anchor + t • M.rayDirection := by
    apply toEuclideanR2_injective
    calc
      toEuclideanR2 (L.anchor + s • L.rayDirection)
          = toEuclideanR2 L.anchor + s • toEuclideanR2 L.rayDirection := by
            simp
      _ = p := hpL.symm
      _ = toEuclideanR2 M.anchor + t • toEuclideanR2 M.rayDirection := hpM
      _ = toEuclideanR2 (M.anchor + t • M.rayDirection) := by
            simp
  have hoffset_eq :
      M.anchor - L.anchor = (s - t * c) • L.rayDirection := by
    ext i
    have hi := congr_fun hpoints i
    simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hMdir] at hi ⊢
    linarith
  have hdet_zero :
      det2 (M.anchor - L.anchor) L.rayDirection = 0 := by
    rw [hoffset_eq]
    unfold det2
    simp [Pi.smul_apply]
    ring
  exact hoffset hdet_zero

/-- A concrete certificate that the circle of `L` does not meet the ray of
`M`, witnessed by separation from the ray's supporting line. -/
structure CircleRayNoMeetData (L M : EuclideanLollipop) : Type where
  radius_lt_infDist_rayLine :
    L.radius <
      Metric.infDist (toEuclideanR2 L.center)
        (euclideanRayLine M : Set EuclideanR2)

namespace CircleRayNoMeetData

/-- Projection-distance constructor for `CircleRayNoMeetData`, using
mathlib's theorem that the distance to the orthogonal projection is the
`Metric.infDist` to the affine subspace. -/
noncomputable def of_rayLineProjection
    {L M : EuclideanLollipop}
    (hsep :
      L.radius <
        dist (toEuclideanR2 L.center)
          (euclideanRayLineProjection M (toEuclideanR2 L.center))) :
    CircleRayNoMeetData L M where
  radius_lt_infDist_rayLine := by
    have hdist :
        dist (toEuclideanR2 L.center)
            (euclideanRayLineProjection M (toEuclideanR2 L.center)) =
          Metric.infDist (toEuclideanR2 L.center)
            (euclideanRayLine M : Set EuclideanR2) :=
      dist_euclideanRayLineProjection_eq_infDist M
        (toEuclideanR2 L.center)
    simpa [hdist] using hsep

/-- A circle-ray no-meet certificate proves that the lifted circle-ray
component is empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : CircleRayNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanCircleRaySet L M :=
  euclideanCircleRaySet_empty_of_radius_lt_infDist_rayLine
    D.radius_lt_infDist_rayLine

end CircleRayNoMeetData

/-- A concrete certificate that the ray of `L` does not meet the circle of
`M`, witnessed by separation from the ray's supporting line. -/
structure RayCircleNoMeetData (L M : EuclideanLollipop) : Type where
  radius_lt_infDist_rayLine :
    M.radius <
      Metric.infDist (toEuclideanR2 M.center)
        (euclideanRayLine L : Set EuclideanR2)

namespace RayCircleNoMeetData

/-- Projection-distance constructor for `RayCircleNoMeetData`, using
mathlib's theorem that the distance to the orthogonal projection is the
`Metric.infDist` to the affine subspace. -/
noncomputable def of_rayLineProjection
    {L M : EuclideanLollipop}
    (hsep :
      M.radius <
        dist (toEuclideanR2 M.center)
          (euclideanRayLineProjection L (toEuclideanR2 M.center))) :
    RayCircleNoMeetData L M where
  radius_lt_infDist_rayLine := by
    have hdist :
        dist (toEuclideanR2 M.center)
            (euclideanRayLineProjection L (toEuclideanR2 M.center)) =
          Metric.infDist (toEuclideanR2 M.center)
            (euclideanRayLine L : Set EuclideanR2) :=
      dist_euclideanRayLineProjection_eq_infDist L
        (toEuclideanR2 M.center)
    simpa [hdist] using hsep

/-- A ray-circle no-meet certificate proves that the lifted ray-circle
component is empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : RayCircleNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanRayCircleSet L M :=
  euclideanRayCircleSet_empty_of_radius_lt_infDist_rayLine
    D.radius_lt_infDist_rayLine

end RayCircleNoMeetData

/-- A point in a ray-ray component lies on the affine line of the first ray. -/
theorem mem_left_anchor_line_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
      (ℝ ∙ toEuclideanR2 L.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet L hp.1

/-- A point in a ray-ray component lies on the affine line of the second ray. -/
theorem mem_right_anchor_line_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ AffineSubspace.mk' (toEuclideanR2 M.anchor)
      (ℝ ∙ toEuclideanR2 M.rayDirection) :=
  mem_anchor_line_of_mem_euclideanRaySet M hp.2

/-- A point in a ray-ray component lies on the named supporting line of the
first ray. -/
theorem mem_left_euclideanRayLine_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ euclideanRayLine L :=
  mem_euclideanRayLine_of_mem_euclideanRaySet L hp.1

/-- A point in a ray-ray component lies on the named supporting line of the
second ray. -/
theorem mem_right_euclideanRayLine_of_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p : EuclideanR2}
    (hp : p ∈ euclideanRayRaySet L M) :
    p ∈ euclideanRayLine M :=
  mem_euclideanRayLine_of_mem_euclideanRaySet M hp.2

/-- If the two supporting ray lines are disjoint as sets, then the actual
ray-ray component is empty. -/
theorem euclideanRayRaySet_empty_of_rayLine_disjoint
    {L M : EuclideanLollipop}
    (hdisj :
      Disjoint (euclideanRayLine L : Set EuclideanR2)
        (euclideanRayLine M : Set EuclideanR2)) :
    ∀ p : EuclideanR2, p ∉ euclideanRayRaySet L M := by
  intro p hp
  have hpL : p ∈ (euclideanRayLine L : Set EuclideanR2) :=
    mem_left_euclideanRayLine_of_mem_euclideanRayRaySet hp
  have hpM : p ∈ (euclideanRayLine M : Set EuclideanR2) :=
    mem_right_euclideanRayLine_of_mem_euclideanRayRaySet hp
  exact (Set.disjoint_left.1 hdisj hpL) hpM

/-- A concrete certificate that the two ray components do not meet, witnessed
by disjoint supporting lines. -/
structure RayRayNoMeetData (L M : EuclideanLollipop) : Type where
  rayLine_disjoint :
    Disjoint (euclideanRayLine L : Set EuclideanR2)
      (euclideanRayLine M : Set EuclideanR2)

namespace RayRayNoMeetData

/-- A ray-ray no-meet certificate proves that the lifted ray-ray component is
empty. -/
theorem empty {L M : EuclideanLollipop}
    (D : RayRayNoMeetData L M) :
    ∀ p : EuclideanR2, p ∉ euclideanRayRaySet L M :=
  euclideanRayRaySet_empty_of_rayLine_disjoint D.rayLine_disjoint

end RayRayNoMeetData

/-- Two distinct common points of two ray supporting lines force the two
supporting lines to be equal. -/
theorem euclideanRayLine_eq_of_two_common_points
    {L M : EuclideanLollipop} {p₁ p₂ : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁L : p₁ ∈ euclideanRayLine L)
    (hp₂L : p₂ ∈ euclideanRayLine L)
    (hp₁M : p₁ ∈ euclideanRayLine M)
    (hp₂M : p₂ ∈ euclideanRayLine M) :
    euclideanRayLine L = euclideanRayLine M := by
  have hL : line[ℝ, p₁, p₂] = euclideanRayLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁L hp₂L hp₁₂
  have hM : line[ℝ, p₁, p₂] = euclideanRayLine M :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁M hp₂M hp₁₂
  exact hL.symm.trans hM

/-- Two distinct points in a ray-ray component force equality of the two
supporting ray lines. -/
theorem euclideanRayLine_eq_of_two_mem_euclideanRayRaySet
    {L M : EuclideanLollipop} {p₁ p₂ : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanRayRaySet L M)
    (hp₂ : p₂ ∈ euclideanRayRaySet L M) :
    euclideanRayLine L = euclideanRayLine M := by
  exact euclideanRayLine_eq_of_two_common_points hp₁₂
    (mem_left_euclideanRayLine_of_mem_euclideanRayRaySet hp₁)
    (mem_left_euclideanRayLine_of_mem_euclideanRayRaySet hp₂)
    (mem_right_euclideanRayLine_of_mem_euclideanRayRaySet hp₁)
    (mem_right_euclideanRayLine_of_mem_euclideanRayRaySet hp₂)

/-- If two ray supporting lines are different, their lifted ray-ray component
contains at most one point. -/
theorem eq_of_mem_euclideanRayRaySet_of_rayLine_ne
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M)
    {p₁ p₂ : EuclideanR2}
    (hp₁ : p₁ ∈ euclideanRayRaySet L M)
    (hp₂ : p₂ ∈ euclideanRayRaySet L M) :
    p₁ = p₂ := by
  by_contra hp₁₂
  exact hline
    (euclideanRayLine_eq_of_two_mem_euclideanRayRaySet hp₁₂ hp₁ hp₂)

/-- Set-level version: noncoincident ray supporting lines have a subsingleton
ray-ray component. -/
theorem euclideanRayRaySet_subsingleton_of_rayLine_ne
    {L M : EuclideanLollipop}
    (hline : euclideanRayLine L ≠ euclideanRayLine M) :
    (euclideanRayRaySet L M).Subsingleton := by
  intro p₁ hp₁ p₂ hp₂
  exact eq_of_mem_euclideanRayRaySet_of_rayLine_ne hline hp₁ hp₂

/-- A ray supporting line and a Euclidean sphere have at most two common
points once two distinct common points have been named. -/
theorem eq_or_eq_of_mem_euclideanSphere_of_mem_euclideanRayLine_of_two_witnesses
    {s : EuclideanGeometry.Sphere EuclideanR2}
    {L : EuclideanLollipop}
    {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁_sphere : p₁ ∈ s)
    (hp₂_sphere : p₂ ∈ s)
    (hp_sphere : p ∈ s)
    (hp₁_line : p₁ ∈ euclideanRayLine L)
    (hp₂_line : p₂ ∈ euclideanRayLine L)
    (hp_line : p ∈ euclideanRayLine L) :
    p = p₁ ∨ p = p₂ := by
  have hline : line[ℝ, p₁, p₂] = euclideanRayLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁_line hp₂_line hp₁₂
  have hp_line_pair : p ∈ line[ℝ, p₁, p₂] := by
    rwa [hline]
  have hp₂_cases :
      p₂ = p₁ ∨ p₂ = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere (right_mem_affineSpan_pair ℝ p₁ p₂)).2 hp₂_sphere)
  have hsecond : s.secondInter p₁ (p₂ -ᵥ p₁) = p₂ := by
    rcases hp₂_cases with hp₂_eq | hp₂_eq
    · exact False.elim (hp₁₂ hp₂_eq.symm)
    · exact hp₂_eq.symm
  have hp_cases : p = p₁ ∨ p = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere hp_line_pair).2 hp_sphere)
  rcases hp_cases with hp_eq | hp_eq
  · exact Or.inl hp_eq
  · exact Or.inr (hp_eq.trans hsecond)

/-- A circle-ray component has at most two points once two distinct component
points have been named. -/
theorem eq_or_eq_of_mem_euclideanCircleRaySet_of_two_witnesses
    {L M : EuclideanLollipop} {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanCircleRaySet L M)
    (hp₂ : p₂ ∈ euclideanCircleRaySet L M)
    (hp : p ∈ euclideanCircleRaySet L M) :
    p = p₁ ∨ p = p₂ := by
  exact eq_or_eq_of_mem_euclideanSphere_of_mem_euclideanRayLine_of_two_witnesses
    (s := euclideanSphere L.center L.radius)
    (L := M) hp₁₂
    hp₁.1 hp₂.1 hp.1
    (mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp₁)
    (mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp₂)
    (mem_euclideanRayLine_of_mem_euclideanCircleRaySet hp)

/-- A ray-circle component has at most two points once two distinct component
points have been named. -/
theorem eq_or_eq_of_mem_euclideanRayCircleSet_of_two_witnesses
    {L M : EuclideanLollipop} {p₁ p₂ p : EuclideanR2}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ euclideanRayCircleSet L M)
    (hp₂ : p₂ ∈ euclideanRayCircleSet L M)
    (hp : p ∈ euclideanRayCircleSet L M) :
    p = p₁ ∨ p = p₂ := by
  exact eq_or_eq_of_mem_euclideanSphere_of_mem_euclideanRayLine_of_two_witnesses
    (s := euclideanSphere M.center M.radius)
    (L := L) hp₁₂
    hp₁.2 hp₂.2 hp.2
    (mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp₁)
    (mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp₂)
    (mem_euclideanRayLine_of_mem_euclideanRayCircleSet hp)

/-- A point on a line through the lifted anchor lies on the lifted circle
exactly when it is the anchor or mathlib's second line/sphere intersection.
This is the standard mathlib theorem needed for future circle-ray intersection
counts. -/
theorem eq_or_eq_secondInter_of_mem_anchor_line_iff_mem_euclideanSphere
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp_line :
      p ∈ AffineSubspace.mk' (toEuclideanR2 L.anchor)
        (ℝ ∙ toEuclideanR2 L.rayDirection)) :
    p = toEuclideanR2 L.anchor ∨
        p = (euclideanSphere L.center L.radius).secondInter
          (toEuclideanR2 L.anchor) (toEuclideanR2 L.rayDirection) ↔
      p ∈ euclideanSphere L.center L.radius := by
  exact
    (euclideanSphere L.center L.radius).eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
      (anchor_mem_euclideanSphere L) hp_line

/-- Any lifted point lying both on a lollipop ray and on its circle is either
the anchor or mathlib's second intersection of that line with the circle. -/
theorem eq_or_eq_secondInter_of_mem_euclideanRaySet_of_mem_euclideanSphere
    (L : EuclideanLollipop) {p : EuclideanR2}
    (hp_ray : p ∈ euclideanRaySet L.anchor L.rayDirection)
    (hp_sphere : p ∈ euclideanSphere L.center L.radius) :
    p = toEuclideanR2 L.anchor ∨
      p = (euclideanSphere L.center L.radius).secondInter
        (toEuclideanR2 L.anchor) (toEuclideanR2 L.rayDirection) := by
  exact
    ((eq_or_eq_secondInter_of_mem_anchor_line_iff_mem_euclideanSphere
      L (mem_anchor_line_of_mem_euclideanRaySet L hp_ray)).2 hp_sphere)

end PrimitiveGeometry
end TheoremOneManuscript
end Lollipop

/-!
Proof component 19: `EndToEnd.Coordinate`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Coordinates and normalized bearings for concrete lollipops

The old combinatorial backend expects centers in `Fin 2 → ℝ`, radii, and one
normalized angle in `[0,1)`.  This file derives all of them from the concrete
`center/radial` model.  In particular, the angle is not an independent field.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

abbrev R2 := TheoremOneEndToEnd.PaulsenLinearAlgebra.R2

namespace R2

def ofPoint (p : Point) : R2 := fun i => p i

def toPoint (p : R2) : Point :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2 p

@[simp] theorem ofPoint_apply (p : Point) (i : Fin 2) : ofPoint p i = p i := rfl
@[simp] theorem toPoint_apply (p : R2) (i : Fin 2) : toPoint p i = p i :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_apply p i

@[simp] theorem ofPoint_toPoint (p : R2) : ofPoint (toPoint p) = p := by
  ext i
  exact toPoint_apply p i

@[simp] theorem toPoint_ofPoint (p : Point) : toPoint (ofPoint p) = p := by
  ext i
  exact toPoint_apply (ofPoint p) i

@[simp] theorem ofPoint_add (x y : Point) :
    ofPoint (x + y) = ofPoint x + ofPoint y := by ext i; rfl

@[simp] theorem ofPoint_sub (x y : Point) :
    ofPoint (x - y) = ofPoint x - ofPoint y := by ext i; rfl

@[simp] theorem ofPoint_smul (a : ℝ) (x : Point) :
    ofPoint (a • x) = a • ofPoint x := by ext i; rfl

@[simp] theorem toPoint_add (x y : R2) :
    toPoint (x + y) = toPoint x + toPoint y :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_add x y

@[simp] theorem toPoint_sub (x y : R2) :
    toPoint (x - y) = toPoint x - toPoint y :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_sub x y

@[simp] theorem toPoint_smul (a : ℝ) (x : R2) :
    toPoint (a • x) = a • toPoint x :=
  TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_smul a x

/-- Squared norm in the two coordinate models. -/
theorem norm_sq_toPoint (x : R2) :
    ‖toPoint x‖ ^ 2 =
      TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 x := by
  calc
    ‖toPoint x‖ ^ 2 = dist (toPoint x) (toPoint 0) ^ 2 := by
      rw [show toPoint 0 = (0 : Point) by ext i; simp [toPoint]]
      rw [dist_zero_right]
    _ = TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2 x 0 := by
      simpa [toPoint] using
        (TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq x 0).symm
    _ = TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 x := by
      simp [TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2]

end R2

/-- Polar-coordinate existence in normalized-turn form.

This is the only trigonometric API port in the coordinate layer.  The proof uses
the complex argument, adds one full turn when negative, and divides by `2π`. -/
theorem exists_normalized_angle
    (u : R2)
    (hu : TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 u = 1) :
    ∃ θ : ℝ,
      0 ≤ θ ∧ θ < 1 ∧
      u = TheoremOneManuscript.PrimitiveGeometry.angleDirection
        (2 * Real.pi * θ) := by
  have hxy : (u 0) ^ 2 + (u 1) ^ 2 = 1 := by
    unfold TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
      TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 at hu
    nlinarith
  have hne : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
    by_contra h
    push Not at h
    nlinarith
  let z : ℂ := (u 0 : ℂ) + (u 1 : ℂ) * Complex.I
  have hnormSq : Complex.normSq z = 1 := by
    simpa [z, Complex.normSq_add_mul_I] using hxy
  have hnormSq' : ‖z‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, hnormSq]
  have hnorm : ‖z‖ = 1 := by
    nlinarith [norm_nonneg z, hnormSq']
  have hz : z ≠ 0 := by
    intro hz0
    have : ‖z‖ = 0 := by simp [hz0]
    linarith
  let φ : ℝ := Complex.arg z
  have hcos : Real.cos φ = u 0 := by
    have := Complex.norm_mul_cos_arg z
    simpa [φ, z, hnorm] using this
  have hsin : Real.sin φ = u 1 := by
    have := Complex.norm_mul_sin_arg z
    simpa [φ, z, hnorm] using this
  have hlo : -Real.pi < φ := by
    simpa [φ] using Complex.neg_pi_lt_arg z
  have hhi : φ ≤ Real.pi := by
    simpa [φ] using Complex.arg_le_pi z
  by_cases hφ : φ < 0
  · refine ⟨(φ + 2 * Real.pi) / (2 * Real.pi), ?_, ?_, ?_⟩
    · exact div_nonneg (by nlinarith [Real.pi_pos, hlo]) Real.two_pi_pos.le
    · apply (div_lt_one (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [Real.pi_pos]
    · ext i
      have hangle :
          2 * Real.pi * ((φ + 2 * Real.pi) / (2 * Real.pi)) =
            φ + 2 * Real.pi := by
        field_simp [mul_ne_zero two_ne_zero Real.pi_ne_zero]
      fin_cases i
      · simp [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2,
          Real.cos_add_two_pi, hcos]
      · simp [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2,
          Real.sin_add_two_pi, hsin]
  · have hφ0 : 0 ≤ φ := le_of_not_gt hφ
    refine ⟨φ / (2 * Real.pi), div_nonneg hφ0 (by positivity), ?_, ?_⟩
    · apply (div_lt_one (by positivity : 0 < 2 * Real.pi)).2
      nlinarith [Real.pi_pos]
    · ext i
      have hangle :
          2 * Real.pi * (φ / (2 * Real.pi)) = φ := by
        field_simp [mul_ne_zero two_ne_zero Real.pi_ne_zero]
      fin_cases i
      · simpa [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2] using hcos.symm
      · simpa [hangle, TheoremOneManuscript.PrimitiveGeometry.angleDirection,
          TheoremOneManuscript.PrimitiveGeometry.point2] using hsin.symm

/-- A normalized angle chosen from the actual unit radial direction. -/
def normalizedDirection (L : Lollipop) : ℝ :=
  Classical.choose (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
    rw [← R2.norm_sq_toPoint]
    simp))

@[simp] theorem normalizedDirection_nonneg (L : Lollipop) :
    0 ≤ normalizedDirection L :=
  (Classical.choose_spec
    (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
      rw [← R2.norm_sq_toPoint]; simp))).1

@[simp] theorem normalizedDirection_lt_one (L : Lollipop) :
    normalizedDirection L < 1 :=
  (Classical.choose_spec
    (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
      rw [← R2.norm_sq_toPoint]; simp))).2.1

@[simp] theorem unitRadial_bearing (L : Lollipop) :
    R2.ofPoint L.unitRadial =
      TheoremOneManuscript.PrimitiveGeometry.angleDirection
        (2 * Real.pi * normalizedDirection L) :=
  (Classical.choose_spec
    (exists_normalized_angle (R2.ofPoint L.unitRadial) (by
      rw [← R2.norm_sq_toPoint]; simp))).2.2

/-- Concrete lollipop viewed by the existing primitive-coordinate library. -/
def toPrimitive (L : Lollipop) :
    TheoremOneManuscript.PrimitiveGeometry.EuclideanLollipop where
  center := R2.ofPoint L.center
  radius := L.radius
  radius_pos := L.radius_pos
  anchor := R2.ofPoint L.anchor
  rayDirection := R2.ofPoint L.unitRadial
  rayDirection_ne_zero := by
    intro h
    have hpoint : L.unitRadial = 0 := by
      have hzero : R2.toPoint (0 : R2) = (0 : Point) := by
        ext i
        simp [R2.toPoint]
      exact (R2.toPoint_ofPoint L.unitRadial).symm.trans
        ((congrArg R2.toPoint h).trans hzero)
    have hnorm0 : ‖L.unitRadial‖ = 0 := by simp [hpoint]
    linarith [L.norm_unitRadial]
  anchor_on_circle := by
    unfold TheoremOneManuscript.PrimitiveGeometry.circleSet
    change TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.anchor) (R2.ofPoint L.center) = L.radius ^ 2
    rw [TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq]
    rw [show TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
          (R2.ofPoint L.anchor) = L.anchor by
        simpa [R2.toPoint] using R2.toPoint_ofPoint L.anchor]
    rw [show TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
          (R2.ofPoint L.center) = L.center by
        simpa [R2.toPoint] using R2.toPoint_ofPoint L.center]
    simp [Lollipop.anchor, Lollipop.radius, dist_eq_norm]
  normalizedDirection := normalizedDirection L
  normalizedDirection_nonneg := normalizedDirection_nonneg L
  normalizedDirection_lt_one := normalizedDirection_lt_one L

@[simp] theorem toPrimitive_hasNormalizedBearing (L : Lollipop) :
    (toPrimitive L).HasNormalizedBearing := by
  exact unitRadial_bearing L

/-- Coordinate maps consumed by the existing upper backend. -/
def centerR2 {n : ℕ} (A : Arrangement n) : Fin n → R2 :=
  fun i => R2.ofPoint (A i).center

def radiusR {n : ℕ} (A : Arrangement n) : Fin n → ℝ :=
  fun i => (A i).radius

def direction01 {n : ℕ} (A : Arrangement n) : Fin n → ℝ :=
  fun i => normalizedDirection (A i)

@[simp] theorem radiusR_pos {n : ℕ} (A : Arrangement n) :
    ∀ i, 0 < radiusR A i := fun i => (A i).radius_pos

@[simp] theorem direction01_nonneg {n : ℕ} (A : Arrangement n) :
    ∀ i, 0 ≤ direction01 A i := fun i => normalizedDirection_nonneg (A i)

@[simp] theorem direction01_lt_one {n : ℕ} (A : Arrangement n) :
    ∀ i, direction01 A i < 1 := fun i => normalizedDirection_lt_one (A i)

/-- Close normalized bearings imply a nonnegative dot product of actual stem
directions. -/
theorem radial_dot_nonneg_of_cyclicClose
    {L M : Lollipop}
    (hclose : TheoremOneEndToEnd.CloseDirection.cyclicClosePair
      (normalizedDirection L) (normalizedDirection M)) :
    0 ≤ TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
      (R2.ofPoint L.unitRadial) (R2.ofPoint M.unitRadial) := by
  exact TheoremOneManuscript.PrimitiveGeometry.EuclideanLollipop.dot2_rayDirection_nonneg_of_cyclicClosePair
      (toPrimitive_hasNormalizedBearing L)
      (toPrimitive_hasNormalizedBearing M) hclose

/-- Paulsen's squared-distance coordinates agree with the concrete Euclidean
metric on points. -/
theorem distSq2_ofPoint_eq_dist_sq (x y : Point) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
      (R2.ofPoint x) (R2.ofPoint y) = dist x y ^ 2 := by
  have hx :
      TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
        (R2.ofPoint x) = x := by
    ext i
    exact TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_apply
      (R2.ofPoint x) i
  have hy :
      TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2
        (R2.ofPoint y) = y := by
    ext i
    exact TheoremOneManuscript.PrimitiveGeometry.toEuclideanR2_apply
      (R2.ofPoint y) i
  simpa [hx, hy] using
    TheoremOneManuscript.PrimitiveGeometry.distSq2_eq_euclidean_dist_sq
      (R2.ofPoint x) (R2.ofPoint y)

end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 20: `EndToEnd.Compactification`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# One-point compactification and the robust pair excess

For arbitrary, possibly degenerate arrangements, a finite crossing-point count
is not the correct pair invariant.  We use

`q(L,M) = #π₀(Ĺ ∩ M̂) - 1`,

where every compactified carrier contains the common point at infinity.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

abbrev Sphere2 := OnePoint Point

def finitePoint (x : Point) : Sphere2 := OnePoint.some x

def infinity : Sphere2 := OnePoint.infty

@[simp] theorem finitePoint_injective : Function.Injective finitePoint := by
  intro x y h
  simpa [finitePoint] using h

@[simp] theorem finitePoint_ne_infinity (x : Point) :
    finitePoint x ≠ infinity := by simp [finitePoint, infinity]

def finiteLift (S : Set Point) : Set Sphere2 := finitePoint '' S

@[simp] theorem mem_finiteLift_iff {S : Set Point} {x : Point} :
    finitePoint x ∈ finiteLift S ↔ x ∈ S := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact finitePoint_injective hxy ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

@[simp] theorem infinity_not_mem_finiteLift (S : Set Point) :
    infinity ∉ finiteLift S := by
  rintro ⟨x, _, hx⟩
  exact finitePoint_ne_infinity x hx

/-- Compactified carrier. -/
def hatCarrier (L : Lollipop) : Set Sphere2 :=
  finiteLift L.carrier ∪ {infinity}

@[simp] theorem infinity_mem_hatCarrier (L : Lollipop) :
    infinity ∈ hatCarrier L := by simp [hatCarrier]

@[simp] theorem finitePoint_mem_hatCarrier_iff (L : Lollipop) (x : Point) :
    finitePoint x ∈ hatCarrier L ↔ x ∈ L.carrier := by
  simp [hatCarrier]

/-- Compactified arrangement union.  The explicit infinity term also makes the
empty arrangement correct. -/
def hatOccupied {n : ℕ} (A : Arrangement n) : Set Sphere2 :=
  (⋃ i, hatCarrier (A i)) ∪ {infinity}

@[simp] theorem infinity_mem_hatOccupied {n : ℕ} (A : Arrangement n) :
    infinity ∈ hatOccupied A := by simp [hatOccupied]

@[simp] theorem finitePoint_mem_hatOccupied_iff {n : ℕ}
    (A : Arrangement n) (x : Point) :
    finitePoint x ∈ hatOccupied A ↔ x ∈ occupied A := by
  simp [hatOccupied, occupied]

/-- Number of connected components of a subspace. -/
def componentCount {X : Type*} [TopologicalSpace X] (S : Set X) : ℕ :=
  Nat.card (ConnectedComponents S)

/-- Region count is component count of the ordinary occupied complement. -/
theorem regionCount_eq_componentCount_compl {n : ℕ} (A : Arrangement n) :
    regionCount A = componentCount ((occupied A)ᶜ) := by
  rfl

/-- Rational region count as component count of the ordinary occupied
complement. -/
theorem regionCountRat_eq_componentCount_compl {n : ℕ} (A : Arrangement n) :
    regionCountRat A = (componentCount ((occupied A)ᶜ) : ℚ) := by
  rw [regionCountRat, regionCount_eq_componentCount_compl]

def hatPairIntersection (L M : Lollipop) : Set Sphere2 :=
  hatCarrier L ∩ hatCarrier M

@[simp] theorem infinity_mem_hatPairIntersection (L M : Lollipop) :
    infinity ∈ hatPairIntersection L M :=
  ⟨infinity_mem_hatCarrier L, infinity_mem_hatCarrier M⟩

/-- Robust pair excess, valid for tangent, coincident, and overlapping pairs. -/
def pairExcessNat (L M : Lollipop) : ℕ :=
  componentCount (hatPairIntersection L M) - 1

def pairExcess (L M : Lollipop) : ℚ := pairExcessNat L M

@[simp] theorem hatPairIntersection_symm (L M : Lollipop) :
    hatPairIntersection L M = hatPairIntersection M L := by
  simp [hatPairIntersection, inter_comm]

@[simp] theorem pairExcessNat_symm (L M : Lollipop) :
    pairExcessNat L M = pairExcessNat M L := by
  simp [pairExcessNat, hatPairIntersection_symm]

@[simp] theorem pairExcess_symm (L M : Lollipop) :
    pairExcess L M = pairExcess M L := by
  simp [pairExcess, pairExcessNat_symm]

def pairExcessTable {n : ℕ} (A : Arrangement n) : Fin n → Fin n → ℚ :=
  fun i j => pairExcess (A i) (A j)

@[simp] theorem pairExcessTable_symm {n : ℕ} (A : Arrangement n)
    (i j : Fin n) : pairExcessTable A i j = pairExcessTable A j i :=
  pairExcess_symm (A i) (A j)

/-- Set-level finite-chart complement identity. -/
theorem finitePoint_preimage_compl_hatOccupied {n : ℕ} (A : Arrangement n) :
    finitePoint ⁻¹' (hatOccupied A)ᶜ = (occupied A)ᶜ := by
  ext x
  simp

/-- Equivalence between the original free space and the compactified
complement.  `PlanarTopology` upgrades it to a homeomorphism. -/
def freeSpaceEquivHatComplement {n : ℕ} (A : Arrangement n) :
    FreeSpace A ≃ {x : Sphere2 // x ∉ hatOccupied A} where
  toFun x := ⟨finitePoint x, by simpa using x.property⟩
  invFun y := by
    rcases y with ⟨y, hy⟩
    cases y using OnePoint.rec with
    | infty => exact False.elim (hy (infinity_mem_hatOccupied A))
    | coe x =>
        exact ⟨x, by
          intro hx
          exact hy (by
            simpa [finitePoint] using (finitePoint_mem_hatOccupied_iff A x).2 hx)⟩
  left_inv x := by ext; rfl
  right_inv y := by
    rcases y with ⟨y, hy⟩
    cases y using OnePoint.rec with
    | infty => exact False.elim (hy (infinity_mem_hatOccupied A))
    | coe x => rfl

end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 21: `EndToEnd.ComponentFibers`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Connected-component fibre bookkeeping

This module contains generic quotient-level cardinality lemmas for inclusions
of subspaces.  It is intended for the eventual planar insertion proof: if a
new carrier splits at most one old complementary component into two pieces,
then the total number of connected components rises by at most one, and exact
two-sided splitting gives equality.

No planar geometry is assumed here.  All maps are induced by actual continuous
subtype inclusions and Mathlib's `ConnectedComponents` quotient.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ComponentFibers

open Set Function BigOperators

universe u v

/-- The fibre of a function over a point, packaged as a subtype. -/
abbrev Fiber {A : Type u} {B : Type v} (f : A → B) (b : B) :=
  {a : A // f a = b}

/-- Every type is equivalent to the sigma type of the fibres of a function. -/
noncomputable def fiberSigmaEquiv {A : Type u} {B : Type v} (f : A → B) :
    A ≃ Σ b : B, Fiber f b where
  toFun a := ⟨f a, ⟨a, rfl⟩⟩
  invFun x := x.2.1
  left_inv := by intro a; rfl
  right_inv := by rintro ⟨b, a, ha⟩; subst b; rfl

section ComponentMaps

variable {X : Type u} [TopologicalSpace X]

/-- Inclusion of one set into another, as a continuous subtype map. -/
def inclusion {S T : Set X} (hST : S ⊆ T) : S → T :=
  fun x => ⟨x.1, hST x.2⟩

theorem continuous_inclusion {S T : Set X} (hST : S ⊆ T) :
    Continuous (inclusion hST) :=
  Continuous.subtype_mk continuous_subtype_val (fun x => hST x.2)

/-- Component map induced by a set inclusion. -/
def inclusionMap {S T : Set X} (hST : S ⊆ T) :
    ConnectedComponents S → ConnectedComponents T :=
  (continuous_inclusion hST).connectedComponentsMap

@[simp] theorem inclusionMap_mk {S T : Set X}
    (hST : S ⊆ T) (x : S) :
    inclusionMap hST (ConnectedComponents.mk x) =
      ConnectedComponents.mk (inclusion hST x) := by
  simp [inclusionMap]

/-- A component map is surjective once every target point is component-related
to a point in the source. -/
theorem inclusionMap_surjective_of_component_meets
    {S T : Set X} (hST : S ⊆ T)
    (hmeet : ∀ y : T, ∃ x : S,
      ConnectedComponents.mk (inclusion hST x) = ConnectedComponents.mk y) :
    Surjective (inclusionMap hST) := by
  intro c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨x, hx⟩ := hmeet y
  exact ⟨ConnectedComponents.mk x, by simpa [inclusionMap] using hx⟩

end ComponentMaps

section FibreCardinality

variable {A : Type u} {B : Type v}
variable (f : A → B)

/-- A subsingleton fibre is finite. -/
theorem finite_fiber_of_subsingleton
    (b : B) [Subsingleton (Fiber f b)] :
    Finite (Fiber f b) :=
  Finite.of_injective (fun _ : Fiber f b => PUnit.unit)
    (fun a c _ => Subsingleton.elim a c)

/-- Fibrewise finiteness implies finiteness of the source. -/
theorem finite_source_of_finite_fibers
    [Finite B]
    (hfinite : ∀ b : B, Finite (Fiber f b)) :
    Finite A := by
  letI : ∀ b : B, Finite (Fiber f b) := hfinite
  exact Finite.of_injective (fiberSigmaEquiv f).toFun
    (fiberSigmaEquiv f).injective

/-- Cardinality of a source as a sum of cardinalities of its fibres. -/
theorem natCard_eq_sum_fibers
    [Fintype B]
    (hfinite : ∀ b : B, Finite (Fiber f b)) :
    Nat.card A = ∑ b : B, Nat.card (Fiber f b) := by
  letI : ∀ b : B, Finite (Fiber f b) := hfinite
  rw [Nat.card_congr (fiberSigmaEquiv f), Nat.card_sigma]

end FibreCardinality

private theorem sum_if_eq_two_else_one
    {β : Type*} [Fintype β] [DecidableEq β] (a : β) :
    (∑ b : β, if b = a then (2 : ℕ) else 1) = Fintype.card β + 1 := by
  rw [Finset.sum_eq_add_sum_diff_singleton
    (s := Finset.univ) (i := a)
    (f := fun b => if b = a then (2 : ℕ) else 1) (by simp)]
  have hsum :
      (∑ x ∈ Finset.univ \ {a}, if x = a then (2 : ℕ) else 1) =
        ∑ x ∈ Finset.univ \ {a}, (1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp at hx
    simp [hx]
  rw [hsum]
  have hsumConst :
      (∑ x ∈ Finset.univ \ {a}, (1 : ℕ)) =
        (Finset.univ \ {a}).card := by
    simp
  rw [hsumConst]
  have hcard :
      (Finset.univ \ {a}).card = Fintype.card β - 1 := by
    rw [Finset.card_sdiff]
    simp
  have hpos : 0 < Fintype.card β := Fintype.card_pos_iff.mpr ⟨a⟩
  rw [hcard]
  simp only [if_true]
  omega

section SplitBound

variable {X : Type u} [TopologicalSpace X]
variable {S T : Set X} (hST : S ⊆ T)

/-- Quotient-level data saying that only one target component may split, and
it has at most two source components above it. -/
structure OneComponentSplitData where
  active : ConnectedComponents T
  activeClassifier : Fiber (inclusionMap hST) active → Fin 2
  active_injective : Injective activeClassifier
  inactive_subsingleton :
    ∀ b : ConnectedComponents T, b ≠ active →
      Subsingleton (Fiber (inclusionMap hST) b)

/-- Exact splitting data: every target component survives and the active fibre
contains both values of its two-valued classifier. -/
structure ExactOneComponentSplitData extends OneComponentSplitData hST where
  componentMap_surjective : Surjective (inclusionMap hST)
  activeSide_surjective : Surjective activeClassifier

/-- The split data make every source fibre finite. -/
theorem finite_fiber_of_oneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    ∀ b : ConnectedComponents T,
      Finite (Fiber (inclusionMap hST) b) := by
  intro b
  by_cases hb : b = d.active
  · subst b
    exact Finite.of_injective d.activeClassifier d.active_injective
  · letI : Subsingleton (Fiber (inclusionMap hST) b) :=
      d.inactive_subsingleton b hb
    exact finite_fiber_of_subsingleton (inclusionMap hST) b

/-- In particular, finite target component count implies finite source
component count under one-component split data. -/
theorem finite_source_of_oneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    Finite (ConnectedComponents S) :=
  finite_source_of_finite_fibers (inclusionMap hST)
    (finite_fiber_of_oneComponentSplit hST d)

/-- The active fibre has cardinality at most two. -/
theorem active_fiber_natCard_le_two
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    Nat.card (Fiber (inclusionMap hST) d.active) ≤ 2 := by
  simpa using
    (Nat.card_le_card_of_injective d.activeClassifier d.active_injective)

/-- Every inactive fibre has cardinality at most one. -/
theorem inactive_fiber_natCard_le_one
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST)
    (b : ConnectedComponents T) (hb : b ≠ d.active) :
    Nat.card (Fiber (inclusionMap hST) b) ≤ 1 := by
  letI : Subsingleton (Fiber (inclusionMap hST) b) :=
    d.inactive_subsingleton b hb
  calc
    Nat.card (Fiber (inclusionMap hST) b) ≤ Nat.card Unit :=
      Nat.card_le_card_of_injective
        (fun _ : Fiber (inclusionMap hST) b => ())
        (fun a c _ => Subsingleton.elim a c)
    _ = 1 := by simp

/-- One target component with at most two descendants and all other target
components with at most one descendant give the sharp `+1` upper bound. -/
theorem componentCount_le_add_one_of_oneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : OneComponentSplitData hST) :
    componentCount S ≤ componentCount T + 1 := by
  classical
  letI : Fintype (ConnectedComponents T) :=
    Fintype.ofFinite (ConnectedComponents T)
  let hfinite := finite_fiber_of_oneComponentSplit hST d
  letI : ∀ b : ConnectedComponents T,
      Finite (Fiber (inclusionMap hST) b) := hfinite
  letI : Finite (ConnectedComponents S) :=
    finite_source_of_oneComponentSplit hST d
  unfold componentCount
  rw [natCard_eq_sum_fibers (inclusionMap hST) hfinite]
  calc
    (∑ b : ConnectedComponents T,
        Nat.card (Fiber (inclusionMap hST) b)) ≤
        ∑ b : ConnectedComponents T,
          (if b = d.active then 2 else 1) := by
      exact Finset.sum_le_sum fun b _ => by
        by_cases hb : b = d.active
        · subst b
          simpa using active_fiber_natCard_le_two hST d
        · simpa [hb] using inactive_fiber_natCard_le_one hST d b hb
    _ = Nat.card (ConnectedComponents T) + 1 := by
      simpa [Nat.card_eq_fintype_card] using
        sum_if_eq_two_else_one d.active

/-- Exact data force the active fibre to have exactly two elements. -/
theorem active_fiber_natCard_eq_two
    [Finite (ConnectedComponents T)]
    (d : ExactOneComponentSplitData hST) :
    Nat.card (Fiber (inclusionMap hST) d.active) = 2 := by
  let e : Fiber (inclusionMap hST) d.active ≃ Fin 2 :=
    Equiv.ofBijective d.activeClassifier
      ⟨d.active_injective, d.activeSide_surjective⟩
  calc
    Nat.card (Fiber (inclusionMap hST) d.active) = Nat.card (Fin 2) :=
      Nat.card_congr e
    _ = 2 := by simp

/-- Surjectivity of the component map makes every inactive subsingleton fibre
have exactly one element. -/
theorem inactive_fiber_natCard_eq_one
    [Finite (ConnectedComponents T)]
    (d : ExactOneComponentSplitData hST)
    (b : ConnectedComponents T) (hb : b ≠ d.active) :
    Nat.card (Fiber (inclusionMap hST) b) = 1 := by
  letI : Subsingleton (Fiber (inclusionMap hST) b) :=
    d.inactive_subsingleton b hb
  have hnon : Nonempty (Fiber (inclusionMap hST) b) := by
    obtain ⟨a, ha⟩ := d.componentMap_surjective b
    exact ⟨⟨a, ha⟩⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, hnon⟩

/-- Exact one-component splitting raises component count by exactly one. -/
theorem componentCount_eq_add_one_of_exactOneComponentSplit
    [Finite (ConnectedComponents T)]
    (d : ExactOneComponentSplitData hST) :
    componentCount S = componentCount T + 1 := by
  classical
  letI : Fintype (ConnectedComponents T) :=
    Fintype.ofFinite (ConnectedComponents T)
  let hfinite := finite_fiber_of_oneComponentSplit hST d.toOneComponentSplitData
  letI : ∀ b : ConnectedComponents T,
      Finite (Fiber (inclusionMap hST) b) := hfinite
  letI : Finite (ConnectedComponents S) :=
    finite_source_of_oneComponentSplit hST d.toOneComponentSplitData
  unfold componentCount
  rw [natCard_eq_sum_fibers (inclusionMap hST) hfinite]
  calc
    (∑ b : ConnectedComponents T,
        Nat.card (Fiber (inclusionMap hST) b)) =
        ∑ b : ConnectedComponents T,
          (if b = d.active then 2 else 1) := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hb : b = d.active
      · subst b
        simpa using active_fiber_natCard_eq_two hST d
      · simpa [hb] using inactive_fiber_natCard_eq_one hST d b hb
    _ = Nat.card (ConnectedComponents T) + 1 := by
      simpa [Nat.card_eq_fintype_card] using
        sum_if_eq_two_else_one d.active

end SplitBound

end ComponentFibers
end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 22: `EndToEnd.ComponentSplitChain`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Finite chains of one-component splits

This file iterates the quotient-level fibre-count theorem from
`ComponentFibers`.  A chain runs from the smaller free set to the larger free
set.  Each step is an inclusion whose component map has at most one
two-element fibre, so an `m`-step chain raises component count by at most `m`;
exact split data give equality.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace ComponentSplitChain

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A finite sequence of inclusions, each carrying a one-component split
certificate.  `snoc` appends the last inclusion. -/
inductive Chain : (m : ℕ) → Set X → Set X → Type u
  | nil (S : Set X) : Chain 0 S S
  | snoc {m : ℕ} {S T U : Set X}
      (head : Chain m S T)
      (hTU : T ⊆ U)
      (split : ComponentFibers.OneComponentSplitData hTU) :
      Chain (m + 1) S U

/-- A one-step chain. -/
noncomputable def Chain.singleton {S T : Set X}
    (hST : S ⊆ T) (split : ComponentFibers.OneComponentSplitData hST) :
    Chain 1 S T := by
  simpa using Chain.snoc (Chain.nil S) hST split

/-- Concatenation of split chains. -/
noncomputable def Chain.trans {m : ℕ} {S T : Set X}
    (left : Chain m S T) :
    ∀ {k : ℕ} {U : Set X}, Chain k T U → Chain (m + k) S U
  | 0, _, .nil _ => by simpa using left
  | _, _, .snoc head hVU split => by
      simpa [Nat.add_assoc] using
        Chain.snoc (Chain.trans left head) hVU split

/-- Explicit finiteness propagation along a chain. -/
@[reducible] noncomputable def Chain.finiteSourceExplicit :
    ∀ {m : ℕ} {S T : Set X}, Chain m S T →
      Finite (ConnectedComponents T) → Finite (ConnectedComponents S)
  | 0, _, _, .nil _, hfinite => hfinite
  | _, _, _, .snoc head hTU split, hfinite => by
      letI : Finite (ConnectedComponents _) := hfinite
      let hmiddle : Finite (ConnectedComponents _) :=
        ComponentFibers.finite_source_of_oneComponentSplit hTU split
      exact Chain.finiteSourceExplicit head hmiddle

/-- Typeclass form of finiteness propagation. -/
theorem Chain.finite_source {m : ℕ} {S T : Set X}
    (_chain : Chain m S T) [Finite (ConnectedComponents T)] :
    Finite (ConnectedComponents S) :=
  Chain.finiteSourceExplicit _chain inferInstance

/-- Explicit component-count bound along a chain. -/
theorem Chain.componentCount_le_explicit :
    ∀ {m : ℕ} {S T : Set X} (_chain : Chain m S T),
      Finite (ConnectedComponents T) →
      componentCount S ≤ componentCount T + m
  | 0, _, _, .nil _, _ => by simp
  | _, _, _, .snoc head hTU split, hfinite => by
      letI : Finite (ConnectedComponents _) := hfinite
      let hmiddle : Finite (ConnectedComponents _) :=
        ComponentFibers.finite_source_of_oneComponentSplit hTU split
      letI : Finite (ConnectedComponents _) := hmiddle
      have hhead := Chain.componentCount_le_explicit head hmiddle
      have hlast :=
        ComponentFibers.componentCount_le_add_one_of_oneComponentSplit hTU split
      omega

/-- An `m`-step split chain raises component count by at most `m`. -/
theorem Chain.componentCount_le {m : ℕ} {S T : Set X}
    (chain : Chain m S T) [Finite (ConnectedComponents T)] :
    componentCount S ≤ componentCount T + m :=
  Chain.componentCount_le_explicit chain inferInstance

/-- Exact analogue of `Chain`. -/
inductive ExactChain : (m : ℕ) → Set X → Set X → Type u
  | nil (S : Set X) : ExactChain 0 S S
  | snoc {m : ℕ} {S T U : Set X}
      (head : ExactChain m S T)
      (hTU : T ⊆ U)
      (split : ComponentFibers.ExactOneComponentSplitData hTU) :
      ExactChain (m + 1) S U

/-- Forget exactness. -/
noncomputable def ExactChain.toChain :
    ∀ {m : ℕ} {S T : Set X}, ExactChain m S T → Chain m S T
  | 0, _, _, .nil S => .nil S
  | _, _, _, .snoc head hTU split =>
      .snoc (ExactChain.toChain head) hTU split.toOneComponentSplitData

/-- A one-step exact chain. -/
noncomputable def ExactChain.singleton {S T : Set X}
    (hST : S ⊆ T) (split : ComponentFibers.ExactOneComponentSplitData hST) :
    ExactChain 1 S T := by
  simpa using ExactChain.snoc (ExactChain.nil S) hST split

/-- Concatenation of exact chains. -/
noncomputable def ExactChain.trans {m : ℕ} {S T : Set X}
    (left : ExactChain m S T) :
    ∀ {k : ℕ} {U : Set X}, ExactChain k T U → ExactChain (m + k) S U
  | 0, _, .nil _ => by simpa using left
  | _, _, .snoc head hVU split => by
      simpa [Nat.add_assoc] using
        ExactChain.snoc (ExactChain.trans left head) hVU split

/-- Exact chains inherit finiteness propagation. -/
theorem ExactChain.finite_source {m : ℕ} {S T : Set X}
    (_chain : ExactChain m S T) [Finite (ConnectedComponents T)] :
    Finite (ConnectedComponents S) :=
  _chain.toChain.finite_source

/-- Explicit exact component-count recurrence. -/
theorem ExactChain.componentCount_eq_explicit :
    ∀ {m : ℕ} {S T : Set X} (_chain : ExactChain m S T),
      Finite (ConnectedComponents T) →
      componentCount S = componentCount T + m
  | 0, _, _, .nil _, _ => by simp
  | _, _, _, .snoc head hTU split, hfinite => by
      letI : Finite (ConnectedComponents _) := hfinite
      let hmiddle : Finite (ConnectedComponents _) :=
        ComponentFibers.finite_source_of_oneComponentSplit hTU
          split.toOneComponentSplitData
      letI : Finite (ConnectedComponents _) := hmiddle
      have hhead := ExactChain.componentCount_eq_explicit head hmiddle
      have hlast :=
        ComponentFibers.componentCount_eq_add_one_of_exactOneComponentSplit hTU split
      omega

/-- An exact `m`-step chain raises component count by exactly `m`. -/
theorem ExactChain.componentCount_eq {m : ℕ} {S T : Set X}
    (chain : ExactChain m S T) [Finite (ConnectedComponents T)] :
    componentCount S = componentCount T + m :=
  ExactChain.componentCount_eq_explicit chain inferInstance

end ComponentSplitChain
end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 23: `EndToEnd.Support`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Shared geometric and finite-component support

This module isolates low-level Euclidean facts used by both the arbitrary
upper bound and the generic lower construction.  The declarations in
`EuclideanPort` are narrow API ports: their proofs are elementary coordinate
arguments (linear equations for rays and quadratic equations for circles).
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set BigOperators
open scoped Topology

/-- Determinant and dot product in displayed coordinates. -/
def detPoint (u v : Point) : ℝ := u 0 * v 1 - u 1 * v 0

def dotPoint (u v : Point) : ℝ := u 0 * v 0 + u 1 * v 1

theorem continuous_detPoint_comp
    {X : Type*} [TopologicalSpace X] {u v : X → Point}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => detPoint (u x) (v x)) := by
  unfold detPoint
  fun_prop

theorem continuous_dotPoint_comp
    {X : Type*} [TopologicalSpace X] {u v : X → Point}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous (fun x => dotPoint (u x) (v x)) := by
  unfold dotPoint
  fun_prop

@[simp] theorem detPoint_skew (u v : Point) :
    detPoint v u = -detPoint u v := by
  unfold detPoint
  ring

@[simp] theorem dotPoint_comm (u v : Point) :
    dotPoint v u = dotPoint u v := by
  unfold dotPoint
  ring

/-- Primitive crossing sets. -/
def cc (L M : Lollipop) : Set Point := L.circle ∩ M.circle
def cr (L M : Lollipop) : Set Point := L.circle ∩ M.stem
def rc (L M : Lollipop) : Set Point := L.stem ∩ M.circle
def rr (L M : Lollipop) : Set Point := L.stem ∩ M.stem

def pairCrossingSet (L M : Lollipop) : Set Point := L.carrier ∩ M.carrier

def pairCrossingCount (L M : Lollipop) : ℕ :=
  (pairCrossingSet L M).ncard

/-- Finite crossing sum for an arrangement.  For generic arrangements this is
the ordinary crossing count used in the Euler face formula. -/
def totalCrossingsNat {n : ℕ} (A : Arrangement n) : ℕ :=
  ∑ p ∈ Lollipop.pairFinset n, pairCrossingCount (A p.1) (A p.2)

/-- The bundled Euclidean sphere underlying a concrete lollipop circle. -/
def concreteSphere (L : Lollipop) : EuclideanGeometry.Sphere Point where
  center := L.center
  radius := L.radius

/-- The supporting affine line of a concrete lollipop stem. -/
def stemLine (L : Lollipop) : AffineSubspace ℝ Point :=
  line[ℝ, L.center, L.center + L.radial]

/-- The concrete point space has finrank two. -/
theorem point_finrank : Module.finrank ℝ Point = 2 := by
  simp [Point]

/-- A stem point lies on the stem's supporting affine line. -/
theorem mem_stemLine_of_mem_stem
    {L : Lollipop} {x : Point} (hx : x ∈ L.stem) :
    x ∈ stemLine L := by
  rcases hx with ⟨t, _ht, rfl⟩
  have hmk :
      stemLine L =
        AffineSubspace.mk' L.center (ℝ ∙ L.radial) := by
    rw [stemLine]
    rw [← AffineSubspace.mk'_eq (left_mem_affineSpan_pair ℝ L.center (L.center + L.radial))]
    rw [direction_affineSpan, vectorSpan_pair_rev]
    simp [vsub_eq_sub]
  rw [hmk, AffineSubspace.mem_mk']
  simpa [vsub_eq_sub] using
    Submodule.smul_mem (ℝ ∙ L.radial) t
      (Submodule.mem_span_singleton_self L.radial)

theorem stemLine_direction (L : Lollipop) :
    (stemLine L).direction = ℝ ∙ L.radial := by
  rw [stemLine]
  rw [direction_affineSpan, vectorSpan_pair_rev]
  simp [vsub_eq_sub]

theorem stemLine_ne_of_detPoint_ne_zero
    {L M : Lollipop} (hdet : detPoint L.radial M.radial ≠ 0) :
    stemLine L ≠ stemLine M := by
  intro hline
  have hdir :
      ℝ ∙ L.radial = ℝ ∙ M.radial := by
    have hcongr := congrArg AffineSubspace.direction hline
    simpa [stemLine_direction] using hcongr
  have hmem : M.radial ∈ ℝ ∙ L.radial := by
    rw [hdir]
    exact Submodule.mem_span_singleton_self M.radial
  rcases Submodule.mem_span_singleton.mp hmem with ⟨c, hc⟩
  have hzero : detPoint L.radial M.radial = 0 := by
    rw [← hc]
    unfold detPoint
    simp
    ring
  exact hdet hzero

/-- A point that is topologically isolated inside a set. -/
def IsolatedPoint {X : Type*} [TopologicalSpace X] (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ ∃ U ∈ 𝓝 x, U ∩ S ⊆ {x}

theorem finite_of_subsingleton_of_mem
    {α : Type*} {S : Set α} {x : α}
    (hsub : S.Subsingleton) (hx : x ∈ S) :
    S.Finite :=
  (finite_singleton x).subset (by
    intro y hy
    exact hsub hy hx)

theorem isolatedPoint_of_mem_finite
    {X : Type*} [TopologicalSpace X] [T1Space X]
    {S : Set X} (hS : S.Finite) {x : X} (hx : x ∈ S) :
    IsolatedPoint S x := by
  refine ⟨hx, ?_⟩
  let U : Set X := (S \ {x})ᶜ
  have hclosed : IsClosed (S \ {x}) := hS.diff.isClosed
  have hopen : IsOpen U := isOpen_compl_iff.2 hclosed
  have hxU : x ∈ U := by
    simp [U]
  refine ⟨U, hopen.mem_nhds hxU, ?_⟩
  intro y hy
  have hyS : y ∈ S := hy.2
  have hy_not : y ∉ S \ {x} := by simpa [U] using hy.1
  have hyx : y = x := by
    by_contra hne
    exact hy_not ⟨hyS, by simp [hne]⟩
  simp [hyx]

theorem finite_connectedComponents_of_finite_set
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : S.Finite) :
    Finite (ConnectedComponents S) := by
  haveI : Finite S := hS.to_subtype
  exact Finite.of_surjective ConnectedComponents.mk
    ConnectedComponents.surjective_coe

/-- A singleton has exactly one connected component. -/
theorem componentCount_singleton
    {X : Type*} [TopologicalSpace X] (p : X) :
    componentCount ({p} : Set X) = 1 := by
  haveI : Finite (ConnectedComponents ({p} : Set X)) :=
    finite_connectedComponents_of_finite_set (finite_singleton p)
  haveI : Subsingleton (ConnectedComponents ({p} : Set X)) := by
    refine ⟨?_⟩
    intro q r
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe r
    have hxy : x = y := by
      apply Subtype.ext
      have hx : x.1 = p := Set.mem_singleton_iff.mp x.property
      have hy : y.1 = p := Set.mem_singleton_iff.mp y.property
      exact hx.trans hy.symm
    exact congrArg ConnectedComponents.mk hxy
  unfold componentCount
  have hcard : Nat.card (ConnectedComponents ({p} : Set X)) ≤ 1 :=
    (Finite.card_le_one_iff_subsingleton).2 inferInstance
  haveI : Nonempty (ConnectedComponents ({p} : Set X)) :=
    ConnectedComponents.nonempty_iff_nonempty.mpr ⟨⟨p, by simp⟩⟩
  have hpos : 0 < Nat.card (ConnectedComponents ({p} : Set X)) :=
    Nat.card_pos
  omega

theorem finite_of_forall_mem_eq_left_or_right
    {α : Type*} {s : Set α}
    (h :
      ∀ ⦃a b x : α⦄, a ∈ s → b ∈ s → x ∈ s → a ≠ b →
        x = a ∨ x = b) :
    s.Finite := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact finite_empty
  · by_cases hsingle : ∀ x ∈ s, x = a
    · exact (finite_singleton a).subset (by
        intro x hx
        simp [hsingle x hx])
    · push Not at hsingle
      rcases hsingle with ⟨b, hb, hba⟩
      exact ((finite_singleton b).insert a).subset (by
        intro x hx
        rcases h ha hb hx hba.symm with hx_eq | hx_eq
        · simp [hx_eq]
        · simp [hx_eq])

theorem ncard_le_two_of_forall_mem_eq_left_or_right
    {α : Type*} {s : Set α}
    (h :
      ∀ ⦃a b x : α⦄, a ∈ s → b ∈ s → x ∈ s → a ≠ b →
        x = a ∨ x = b) :
    s.ncard ≤ 2 := by
  classical
  have hs : s.Finite := finite_of_forall_mem_eq_left_or_right h
  by_contra hle
  have hlt : 2 < s.ncard := Nat.lt_of_not_ge hle
  rcases (Set.two_lt_ncard_iff hs).1 hlt with
    ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  rcases h ha hb hc hab with hc_eq | hc_eq
  · exact hac hc_eq.symm
  · exact hbc hc_eq.symm

theorem componentCount_union_singleton_sub_one_le_one
    {X : Type*} [TopologicalSpace X] {S : Set X} {a : X}
    (hS : IsConnected S) :
    componentCount (S ∪ {a}) - 1 ≤ 1 := by
  let U : Set X := S ∪ {a}
  let base : U := ⟨hS.nonempty.some, Or.inl hS.nonempty.some_mem⟩
  let apex : U := ⟨a, Or.inr rfl⟩
  let f : Option Unit → ConnectedComponents U := fun o =>
    match o with
    | none => ConnectedComponents.mk apex
    | some _ => ConnectedComponents.mk base
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨u, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases u.property with huS | hua
    · refine ⟨some (), ?_⟩
      dsimp [f]
      rw [ConnectedComponents.coe_eq_coe]
      apply connectedComponent_eq_iff_mem.2
      let SU : Set U := {z | (z : X) ∈ S}
      have hSU_conn : IsConnected SU := by
        let incl : S → U := fun z => ⟨z, Or.inl z.property⟩
        haveI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
        have hrange : Set.range incl = SU := by
          ext z
          constructor
          · rintro ⟨w, rfl⟩
            exact w.property
          · intro hz
            exact ⟨⟨z, hz⟩, rfl⟩
        rw [← hrange]
        exact isConnected_range (by continuity : Continuous incl)
      have hbase : base ∈ SU := hS.nonempty.some_mem
      have hu : u ∈ SU := huS
      exact hSU_conn.subset_connectedComponent hu hbase
    · refine ⟨none, ?_⟩
      dsimp [f]
      congr
      ext
      have hu_eq : (u : X) = a := by simpa using hua
      exact hu_eq.symm
  haveI : Finite (ConnectedComponents U) := Finite.of_surjective f hsurj
  have hcard : Nat.card (ConnectedComponents U) ≤ Nat.card (Option Unit) :=
    Nat.card_le_card_of_surjective f hsurj
  unfold componentCount
  dsimp [U] at hcard
  have hopt : Nat.card (Option Unit) = 2 := by
    simp
  omega

theorem finite_connectedComponents_union_singleton_of_connected
    {X : Type*} [TopologicalSpace X] {S : Set X} {a : X}
    (hS : IsConnected S) :
    Finite (ConnectedComponents ((S ∪ {a}) : Set X)) := by
  let U : Set X := S ∪ {a}
  let base : U := ⟨hS.nonempty.some, Or.inl hS.nonempty.some_mem⟩
  let apex : U := ⟨a, Or.inr rfl⟩
  let f : Option Unit → ConnectedComponents U := fun o =>
    match o with
    | none => ConnectedComponents.mk apex
    | some _ => ConnectedComponents.mk base
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨u, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases u.property with huS | hua
    · refine ⟨some (), ?_⟩
      dsimp [f]
      rw [ConnectedComponents.coe_eq_coe]
      apply connectedComponent_eq_iff_mem.2
      let SU : Set U := {z | (z : X) ∈ S}
      have hSU_conn : IsConnected SU := by
        let incl : S → U := fun z => ⟨z, Or.inl z.property⟩
        haveI : ConnectedSpace S := isConnected_iff_connectedSpace.mp hS
        have hrange : Set.range incl = SU := by
          ext z
          constructor
          · rintro ⟨w, rfl⟩
            exact w.property
          · intro hz
            exact ⟨⟨z, hz⟩, rfl⟩
        rw [← hrange]
        exact isConnected_range (by continuity : Continuous incl)
      have hbase : base ∈ SU := hS.nonempty.some_mem
      have hu : u ∈ SU := huS
      exact hSU_conn.subset_connectedComponent hu hbase
    · refine ⟨none, ?_⟩
      dsimp [f]
      congr
      ext
      have hu_eq : (u : X) = a := by simpa using hua
      exact hu_eq.symm
  exact Finite.of_surjective f hsurj

theorem finite_connectedComponents_finiteLift_union_infinity
    {S : Set Point} (hS : S.Finite) :
    Finite (ConnectedComponents ((finiteLift S ∪ {infinity}) : Set Sphere2)) := by
  exact finite_connectedComponents_of_finite_set
    ((hS.image finitePoint).union (finite_singleton infinity))

theorem component_excess_union_infinity_le_one
    {S : Set Sphere2} (hS : IsConnected S) :
    componentCount (S ∪ {infinity}) - 1 ≤ 1 :=
  componentCount_union_singleton_sub_one_le_one hS

theorem concreteSphere_ne_of_circle_ne
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle) :
    concreteSphere L ≠ concreteSphere M := by
  intro hsphere
  apply hcircle
  rw [L.circle_eq_sphere, M.circle_eq_sphere]
  simpa [concreteSphere] using
    congrArg (fun s : EuclideanGeometry.Sphere Point => (s : Set Point)) hsphere

theorem eq_or_eq_of_mem_cc_of_two_witnesses
    {L M : Lollipop}
    (hsphere : concreteSphere L ≠ concreteSphere M)
    {p₁ p₂ p : Point}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁ : p₁ ∈ cc L M)
    (hp₂ : p₂ ∈ cc L M)
    (hp : p ∈ cc L M) :
    p = p₁ ∨ p = p₂ := by
  exact
    EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two
      (V := Point) (P := Point)
      (s₁ := concreteSphere L)
      (s₂ := concreteSphere M)
      point_finrank hsphere hp₁₂ hp₁.1 hp₂.1 hp.1 hp₁.2 hp₂.2 hp.2

theorem finite_circle_intersection_of_ne
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle) :
    (cc L M).Finite := by
  have hsphere : concreteSphere L ≠ concreteSphere M :=
    concreteSphere_ne_of_circle_ne hcircle
  apply finite_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx

theorem circle_intersection_ncard_le_two
    (L M : Lollipop) (hcircle : L.circle ≠ M.circle) :
    (cc L M).ncard ≤ 2 := by
  have hsphere : concreteSphere L ≠ concreteSphere M :=
    concreteSphere_ne_of_circle_ne hcircle
  apply ncard_le_two_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx

theorem eq_or_eq_of_mem_sphere_of_mem_stemLine_of_two_witnesses
    {s : EuclideanGeometry.Sphere Point} {L : Lollipop}
    {p₁ p₂ p : Point}
    (hp₁₂ : p₁ ≠ p₂)
    (hp₁_sphere : p₁ ∈ s)
    (hp₂_sphere : p₂ ∈ s)
    (hp_sphere : p ∈ s)
    (hp₁_line : p₁ ∈ stemLine L)
    (hp₂_line : p₂ ∈ stemLine L)
    (hp_line : p ∈ stemLine L) :
    p = p₁ ∨ p = p₂ := by
  have hline : line[ℝ, p₁, p₂] = stemLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne hp₁_line hp₂_line hp₁₂
  have hp_line_pair : p ∈ line[ℝ, p₁, p₂] := by
    rwa [hline]
  have hp₂_cases :
      p₂ = p₁ ∨ p₂ = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere (right_mem_affineSpan_pair ℝ p₁ p₂)).2 hp₂_sphere)
  have hsecond : s.secondInter p₁ (p₂ -ᵥ p₁) = p₂ := by
    rcases hp₂_cases with hp₂_eq | hp₂_eq
    · exact False.elim (hp₁₂ hp₂_eq.symm)
    · exact hp₂_eq.symm
  have hp_cases : p = p₁ ∨ p = s.secondInter p₁ (p₂ -ᵥ p₁) := by
    exact
      ((s.eq_or_eq_secondInter_iff_mem_of_mem_affineSpan_pair
        hp₁_sphere hp_line_pair).2 hp_sphere)
  rcases hp_cases with hp_eq | hp_eq
  · exact Or.inl hp_eq
  · exact Or.inr (hp_eq.trans hsecond)

theorem finite_circle_ray_intersection (L M : Lollipop) :
    (cr L M).Finite := by
  apply finite_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_sphere_of_mem_stemLine_of_two_witnesses
    (s := concreteSphere L) (L := M) hab
    ha.1 hb.1 hx.1
    (mem_stemLine_of_mem_stem ha.2)
    (mem_stemLine_of_mem_stem hb.2)
    (mem_stemLine_of_mem_stem hx.2)

theorem circle_ray_intersection_ncard_le_two (L M : Lollipop) :
    (cr L M).ncard ≤ 2 := by
  apply ncard_le_two_of_forall_mem_eq_left_or_right
  intro a b x ha hb hx hab
  exact eq_or_eq_of_mem_sphere_of_mem_stemLine_of_two_witnesses
    (s := concreteSphere L) (L := M) hab
    ha.1 hb.1 hx.1
    (mem_stemLine_of_mem_stem ha.2)
    (mem_stemLine_of_mem_stem hb.2)
    (mem_stemLine_of_mem_stem hx.2)

theorem finite_ray_circle_intersection (L M : Lollipop) :
    (rc L M).Finite := by
  simpa [rc, cr, inter_comm] using finite_circle_ray_intersection M L

theorem totallyDisconnectedSpace_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] :
    TotallyDisconnectedSpace X := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro x
  apply subset_antisymm
  · intro y hy
    exact (isClopen_discrete ({x} : Set X)).connectedComponent_subset (by simp) hy
  · intro y hy
    simpa using hy

noncomputable def connectedComponentsEquivSelfOfTotallyDisconnected
    (X : Type*) [TopologicalSpace X] [TotallyDisconnectedSpace X] :
    ConnectedComponents X ≃ X where
  toFun q := Quotient.out q
  invFun x := ConnectedComponents.mk x
  left_inv q := Quotient.out_eq q
  right_inv x := by
    have hq : ConnectedComponents.mk (Quotient.out (ConnectedComponents.mk x)) =
        ConnectedComponents.mk x :=
      Quotient.out_eq (ConnectedComponents.mk x)
    rw [ConnectedComponents.coe_eq_coe] at hq
    rw [connectedComponent_eq_singleton, connectedComponent_eq_singleton] at hq
    simpa using hq

/-- A homeomorphism induces an equivalence on connected-component quotients. -/
noncomputable def connectedComponentsEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := e.continuous.connectedComponentsMap
  invFun := e.symm.continuous.connectedComponentsMap
  left_inv q := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
    simp
  right_inv q := by
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe q
    simp

@[simp] theorem pairCrossingSet_decompose (L M : Lollipop) :
    pairCrossingSet L M = cc L M ∪ rc L M ∪ cr L M ∪ rr L M := by
  ext x
  simp only [pairCrossingSet, cc, cr, rc, rr, Lollipop.carrier,
    mem_inter_iff, mem_union]
  tauto

/-- Transversality predicates in coordinates. -/
def CircleCircleTransverseAt (L M : Lollipop) (x : Point) : Prop :=
  detPoint (x - L.center) (x - M.center) ≠ 0

def StemCircleTransverseAt (L M : Lollipop) (x : Point) : Prop :=
  dotPoint L.radial (x - M.center) ≠ 0

def StemStemTransverse (L M : Lollipop) : Prop :=
  detPoint L.radial M.radial ≠ 0

theorem rr_subsingleton_of_transverse
    {L M : Lollipop} (hdet : StemStemTransverse L M) :
    (rr L M).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  have hlineL : line[ℝ, p, q] = stemLine L :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (mem_stemLine_of_mem_stem hp.1)
      (mem_stemLine_of_mem_stem hq.1) hpq
  have hlineM : line[ℝ, p, q] = stemLine M :=
    affineSpan_pair_eq_of_mem_of_mem_of_ne
      (mem_stemLine_of_mem_stem hp.2)
      (mem_stemLine_of_mem_stem hq.2) hpq
  exact stemLine_ne_of_detPoint_ne_zero hdet (hlineL.symm.trans hlineM)

structure PrimitivePairwiseTransverse (L M : Lollipop) : Prop where
  cc : ∀ x, x ∈ cc L M → CircleCircleTransverseAt L M x
  cr : ∀ x, x ∈ cr L M → StemCircleTransverseAt M L x
  rc : ∀ x, x ∈ rc L M → StemCircleTransverseAt L M x
  rr : (rr L M).Nonempty → StemStemTransverse L M

/-- Genericity sufficient for the exact embedded-graph Euler face formula. -/
structure IsGeneric {n : ℕ} (A : Arrangement n) : Prop where
  pair_finite : ∀ i j : Fin n, i ≠ j →
    (pairCrossingSet (A i) (A j)).Finite
  pair_transverse : ∀ i j : Fin n, i ≠ j →
    PrimitivePairwiseTransverse (A i) (A j)
  away_left_anchor : ∀ i j : Fin n, i ≠ j →
    (A i).anchor ∉ pairCrossingSet (A i) (A j)
  away_right_anchor : ∀ i j : Fin n, i ≠ j →
    (A j).anchor ∉ pairCrossingSet (A i) (A j)
  no_triple : ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
    pairCrossingSet (A i) (A j) ∩ (A k).carrier = ∅
  nonparallel_stems : ∀ i j : Fin n, i ≠ j →
    detPoint (A i).radial (A j).radial ≠ 0

/-- The stem is convex. -/
theorem stem_convex (L : Lollipop) : Convex ℝ L.stem := by
  rw [L.stem_eq_image_Ici]
  have hlin : Convex ℝ ((fun t : ℝ => t • L.radial) '' Ici (1 : ℝ)) :=
    (convex_Ici (1 : ℝ)).linear_image (LinearMap.id.smulRight L.radial)
  simpa [Lollipop.stemMap, image_image, Function.comp_def] using
    hlin.translate L.center

/-- Every compactified carrier is compact. -/
theorem isCompact_hatCarrier (L : Lollipop) : IsCompact (hatCarrier L) := by
  have hclosed : IsClosed (hatCarrier L) := by
    rw [OnePoint.isClosed_iff_of_mem (infinity_mem_hatCarrier L)]
    convert L.isClosed_carrier using 1
    ext x
    simp [hatCarrier, finiteLift, finitePoint, infinity]
  exact hclosed.isCompact

/-- Every finite compactified arrangement union is compact. -/
theorem isCompact_hatOccupied {n : ℕ} (A : Arrangement n) :
    IsCompact (hatOccupied A) := by
  classical
  exact (isCompact_iUnion fun i : Fin n => isCompact_hatCarrier (A i)).union
    isCompact_singleton

noncomputable def finiteLiftUnionInfinityEquivOption (S : Set Point) :
    ((finiteLift S ∪ ({infinity} : Set Sphere2)) : Set Sphere2) ≃ Option S := by
  classical
  let e : S ≃ finiteLift S :=
    { toFun := fun x => ⟨finitePoint x, ⟨x, x.property, rfl⟩⟩
      invFun := fun y => by
        exact ⟨Classical.choose y.property,
          (Classical.choose_spec y.property).1⟩
      left_inv := by
        intro x
        apply Subtype.ext
        let hx : finitePoint ↑x ∈ finiteLift S := ⟨↑x, x.property, rfl⟩
        exact finitePoint_injective (Classical.choose_spec hx).2
      right_inv := by
        intro y
        rcases y with ⟨y, hy⟩
        dsimp
        rcases Classical.choose_spec hy with ⟨hx, hxy⟩
        ext
        exact hxy }
  have hdisj : Disjoint (finiteLift S) ({infinity} : Set Sphere2) := by
    rw [Set.disjoint_iff]
    intro x hx
    have hxinf : x = infinity := by simpa using hx.2
    exact False.elim (infinity_not_mem_finiteLift S (hxinf ▸ hx.1))
  let singletonToOption : S ⊕ ({infinity} : Set Sphere2) ≃ Option S :=
    { toFun := fun x =>
        match x with
        | Sum.inl s => some s
        | Sum.inr _ => none
      invFun := fun x =>
        match x with
        | none => Sum.inr ⟨infinity, rfl⟩
        | some s => Sum.inl s
      left_inv := by
        intro x
        cases x with
        | inl s => rfl
        | inr y =>
            apply congrArg Sum.inr
            ext
            simpa using y.property.symm
      right_inv := by
        intro x
        cases x <;> rfl }
  exact (Equiv.Set.union hdisj).trans
    ((Equiv.sumCongr e.symm (Equiv.refl ({infinity} : Set Sphere2))).trans
      singletonToOption)

/-- A finite set plus infinity has one component per finite point and one at
infinity. -/
theorem componentCount_finiteLift_union_infinity_sub_one
    {S : Set Point} (hS : S.Finite) :
    componentCount (finiteLift S ∪ {infinity}) - 1 = S.ncard := by
  let U : Set Sphere2 := finiteLift S ∪ {infinity}
  let eU : U ≃ Option S := finiteLiftUnionInfinityEquivOption S
  haveI : Finite S := hS.to_subtype
  haveI : Finite U := Finite.of_equiv (Option S) eU.symm
  haveI : DiscreteTopology U := inferInstance
  haveI : TotallyDisconnectedSpace U := totallyDisconnectedSpace_of_discrete
  have hcomponents : ConnectedComponents U ≃ Option S :=
    (connectedComponentsEquivSelfOfTotallyDisconnected U).trans eU
  unfold componentCount
  rw [Nat.card_congr hcomponents]
  simp [Nat.card_coe_set_eq]

theorem component_excess_of_convex_finite_chart_le_one
    {S : Set Point} (hconv : Convex ℝ S) :
    componentCount (finiteLift S ∪ {infinity}) - 1 ≤ 1 := by
  by_cases hne : S.Nonempty
  · have hconn : IsConnected (finiteLift S) :=
      (hconv.isConnected hne).image finitePoint OnePoint.continuous_coe.continuousOn
    exact component_excess_union_infinity_le_one hconn
  · have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hfinite : S.Finite := by simp [hempty]
    rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
    simp [hempty]

/-- Compactified pair intersection is the finite-chart pair crossing set
together with infinity. -/
theorem hatPairIntersection_eq_finiteLift_pairCrossingSet_union_infinity
    (L M : Lollipop) :
    hatPairIntersection L M = finiteLift (pairCrossingSet L M) ∪ {infinity} := by
  ext z
  cases z using OnePoint.rec with
  | infty =>
      change infinity ∈ hatPairIntersection L M ↔
        infinity ∈ finiteLift (pairCrossingSet L M) ∪ {infinity}
      simp
  | coe x =>
      change finitePoint x ∈ hatPairIntersection L M ↔
        finitePoint x ∈ finiteLift (pairCrossingSet L M) ∪ {infinity}
      simp [hatPairIntersection, hatCarrier, pairCrossingSet]

/-- When an ordinary pair crossing set is finite, the robust component-excess
definition reduces to the ordinary finite crossing count. -/
theorem pairExcessNat_eq_pairCrossingCount_of_finite
    {L M : Lollipop} (hfinite : (pairCrossingSet L M).Finite) :
    pairExcessNat L M = pairCrossingCount L M := by
  rw [pairExcessNat,
    hatPairIntersection_eq_finiteLift_pairCrossingSet_union_infinity,
    componentCount_finiteLift_union_infinity_sub_one hfinite]
  rfl


namespace EuclideanPort

/-- Two distinct planar circles meet in at most two points; equal circles form
one connected primitive component. -/
theorem circle_circle_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (cc L M) ∪ {infinity}) - 1 ≤ 2 := by
  by_cases hsame : L.circle = M.circle
  · have hconn : IsConnected (finiteLift (cc L M)) := by
      simpa [cc, hsame, finiteLift] using
        L.isConnected_circle.image finitePoint OnePoint.continuous_coe.continuousOn
    exact (component_excess_union_infinity_le_one hconn).trans (by norm_num)
  · have hfinite : (cc L M).Finite := by
      exact finite_circle_intersection_of_ne hsame
    have hcard : (cc L M).ncard ≤ 2 :=
      circle_intersection_ncard_le_two L M hsame
    rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
    exact hcard

/-- A circle and a radial ray meet in at most two connected components. -/
theorem circle_ray_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (cr L M) ∪ {infinity}) - 1 ≤ 2 := by
  have hfinite : (cr L M).Finite :=
    finite_circle_ray_intersection L M
  have hcard : (cr L M).ncard ≤ 2 :=
    circle_ray_intersection_ncard_le_two L M
  rw [componentCount_finiteLift_union_infinity_sub_one hfinite]
  exact hcard

/-- Symmetric mixed bound. -/
theorem ray_circle_components_le_two (L M : Lollipop) :
    componentCount (finiteLift (rc L M) ∪ {infinity}) - 1 ≤ 2 := by
  simpa [rc, cr, inter_comm] using circle_ray_components_le_two M L

/-- Two rays have at most one finite connected component after removing the
common infinity component, including overlapping collinear rays. -/
theorem ray_ray_components_le_one (L M : Lollipop) :
    componentCount (finiteLift (rr L M) ∪ {infinity}) - 1 ≤ 1 := by
  have hconv : Convex ℝ (rr L M) := (stem_convex L).inter (stem_convex M)
  exact component_excess_of_convex_finite_chart_le_one hconv

/-- A finite transverse primitive pair has one connected component for every
finite crossing, plus infinity. -/
theorem pairExcess_eq_ncard_of_transverse
    {L M : Lollipop}
    (hfinite : (pairCrossingSet L M).Finite)
    (_htrans : PrimitivePairwiseTransverse L M)
    (_hnoTriple :
      (Set.univ : Set (Fin 4)).PairwiseDisjoint (fun k : Fin 4 =>
        match k with
        | 0 => cc L M
        | 1 => rc L M
        | 2 => cr L M
        | 3 => rr L M)) :
    pairExcessNat L M = pairCrossingCount L M := by
  have hhat : hatPairIntersection L M =
      finiteLift (pairCrossingSet L M) ∪ {infinity} := by
    ext x
    cases x using OnePoint.rec with
    | infty =>
        simp [hatPairIntersection, hatCarrier, finiteLift, finitePoint, infinity]
    | coe p =>
        simp [hatPairIntersection, hatCarrier, pairCrossingSet, finiteLift,
          finitePoint, infinity]
  rw [pairExcessNat, hhat,
    componentCount_finiteLift_union_infinity_sub_one hfinite]
  rfl

/-- A transverse circle--circle intersection is isolated. -/
theorem isolated_cc_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ cc L M) (h : CircleCircleTransverseAt L M x) :
    IsolatedPoint (cc L M) x := by
  have hsphere : concreteSphere L ≠ concreteSphere M := by
    intro hsphere
    have hcenter : L.center = M.center :=
      congrArg EuclideanGeometry.Sphere.center hsphere
    have hzero : detPoint (x - L.center) (x - M.center) = 0 := by
      rw [hcenter]
      unfold detPoint
      ring
    exact h hzero
  have hfinite : (cc L M).Finite := by
    apply finite_of_forall_mem_eq_left_or_right
    intro a b y ha hb hy hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hy
  exact isolatedPoint_of_mem_finite hfinite hx

/-- A transverse mixed intersection is isolated. -/
theorem isolated_rc_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ rc L M) (_h : StemCircleTransverseAt L M x) :
    IsolatedPoint (rc L M) x := by
  exact isolatedPoint_of_mem_finite (finite_ray_circle_intersection L M) hx

/-- A transverse ray--ray point is isolated. -/
theorem isolated_rr_of_transverse
    {L M : Lollipop} {x : Point}
    (hx : x ∈ rr L M) (h : StemStemTransverse L M) :
    IsolatedPoint (rr L M) x := by
  exact isolatedPoint_of_mem_finite
    (finite_of_subsingleton_of_mem (rr_subsingleton_of_transverse h) hx) hx

end EuclideanPort

/-- Finite unions of connected sets sharing a common point are connected. -/
theorem isConnected_iUnion_of_common
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    {S : ι → Set X}
    (hS : ∀ i, IsConnected (S i))
    (p : X) (hp : ∀ i, p ∈ S i) (i0 : ι) :
    IsConnected (⋃ i, S i) := by
  have hInter : (⋂ i : ι, S i).Nonempty := by
    refine ⟨p, ?_⟩
    simpa using hp
  refine ⟨⟨p, Set.mem_iUnion_of_mem i0 (hp i0)⟩, ?_⟩
  exact isPreconnected_iUnion (s := S) hInter (fun i => (hS i).isPreconnected)

/-- Components of a finite union of sets with a common point are bounded by
the sum of the non-base components of the pieces. -/
theorem componentCount_iUnion_sub_one_le_sum_sub_one
    {ι X : Type*} [Fintype ι] [Nonempty ι] [TopologicalSpace X]
    {S : ι → Set X} (p : X) (hp : ∀ i, p ∈ S i)
    [∀ i, Finite (ConnectedComponents (S i))] :
    componentCount (⋃ i, S i) - 1 ≤
      ∑ i : ι, (componentCount (S i) - 1) := by
  classical
  let U : Set X := ⋃ i, S i
  let i0 : ι := Classical.choice inferInstance
  let incl (i : ι) : S i → U :=
    fun x => ⟨x.1, Set.mem_iUnion_of_mem i x.2⟩
  have hincl (i : ι) : Continuous (incl i) := by
    dsimp [incl]
    continuity
  let componentMap (i : ι) :
      ConnectedComponents (S i) → ConnectedComponents U :=
    (hincl i).connectedComponentsMap
  let base (i : ι) : ConnectedComponents (S i) :=
    ConnectedComponents.mk (⟨p, hp i⟩ : S i)
  let baseU : ConnectedComponents U :=
    ConnectedComponents.mk
      (⟨p, Set.mem_iUnion_of_mem i0 (hp i0)⟩ : U)
  let Labels : Type _ :=
    Option (Σ i : ι, {q : ConnectedComponents (S i) // q ≠ base i})
  let labelComponent : Labels → ConnectedComponents U
    | none => baseU
    | some x => componentMap x.1 x.2.1
  have hmap_mk (i : ι) (x : S i) :
      componentMap i (ConnectedComponents.mk x) =
        ConnectedComponents.mk (incl i x) := by
    simp [componentMap]
  have hbase_map (i : ι) :
      componentMap i (base i) = baseU := by
    change componentMap i (ConnectedComponents.mk (⟨p, hp i⟩ : S i)) = baseU
    rw [hmap_mk i (⟨p, hp i⟩ : S i)]
  have hsurj : Function.Surjective labelComponent := by
    intro q
    obtain ⟨u, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases Set.mem_iUnion.mp u.property with ⟨i, hui⟩
    let ui : S i := ⟨u.1, hui⟩
    let qi : ConnectedComponents (S i) := ConnectedComponents.mk ui
    by_cases hbase : qi = base i
    · refine ⟨none, ?_⟩
      dsimp [labelComponent]
      have hq : componentMap i qi = ConnectedComponents.mk u := by
        simpa [ui, incl] using hmap_mk i ui
      rw [← hq, hbase, hbase_map i]
    · refine ⟨some ⟨i, ⟨qi, hbase⟩⟩, ?_⟩
      dsimp [labelComponent]
      simpa [ui, incl] using hmap_mk i ui
  haveI : Finite Labels := by
    dsimp [Labels]
    infer_instance
  have hcard :
      componentCount U ≤ Nat.card Labels := by
    haveI : Finite (ConnectedComponents U) :=
      Finite.of_surjective labelComponent hsurj
    exact Nat.card_le_card_of_surjective labelComponent hsurj
  have hnonbase (i : ι) :
      Nat.card {q : ConnectedComponents (S i) // q ≠ base i} ≤
        componentCount (S i) - 1 := by
    have hlt :
        Nat.card {q : ConnectedComponents (S i) // q ≠ base i} <
          Nat.card (ConnectedComponents (S i)) :=
      Finite.card_subtype_lt (p := fun q : ConnectedComponents (S i) =>
        q ≠ base i) (x := base i) (by simp)
    unfold componentCount
    omega
  have hlabels :
      Nat.card Labels ≤
        (∑ i : ι, (componentCount (S i) - 1)) + 1 := by
    dsimp [Labels]
    rw [Finite.card_option, Nat.card_sigma]
    gcongr with i
    exact hnonbase i
  unfold componentCount at hcard
  dsimp [U] at hcard
  exact Nat.sub_le_iff_le_add.2 (le_trans hcard hlabels)

/-- A finite union of sets with component-finite members has component-finite
union. -/
theorem finite_connectedComponents_iUnion
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    {S : ι → Set X}
    [∀ i, Finite (ConnectedComponents (S i))] :
    Finite (ConnectedComponents (⋃ i, S i)) := by
  classical
  let U : Set X := ⋃ i, S i
  let incl (i : ι) : S i → U :=
    fun x => ⟨x.1, Set.mem_iUnion_of_mem i x.2⟩
  have hincl (i : ι) : Continuous (incl i) := by
    dsimp [incl]
    continuity
  let componentMap (i : ι) :
      ConnectedComponents (S i) → ConnectedComponents U :=
    (hincl i).connectedComponentsMap
  let labelComponent :
      (Σ i : ι, ConnectedComponents (S i)) → ConnectedComponents U :=
    fun x => componentMap x.1 x.2
  have hmap_mk (i : ι) (x : S i) :
      componentMap i (ConnectedComponents.mk x) =
        ConnectedComponents.mk (incl i x) := by
    simp [componentMap]
  have hsurj : Function.Surjective labelComponent := by
    intro q
    obtain ⟨u, rfl⟩ := ConnectedComponents.surjective_coe q
    rcases Set.mem_iUnion.mp u.property with ⟨i, hui⟩
    let ui : S i := ⟨u.1, hui⟩
    refine ⟨⟨i, ConnectedComponents.mk ui⟩, ?_⟩
    dsimp [labelComponent]
    simpa [ui, incl] using hmap_mk i ui
  exact Finite.of_surjective labelComponent hsurj

/-- A finite pointed union.  The singleton makes the empty-index case uniform. -/
def pointedFinsetUnion {ι X : Type*} (p : X) (s : Finset ι)
    (S : ι → Set X) : Set X :=
  {p} ∪ ⋃ i : {i // i ∈ s}, S i.1

@[simp] theorem mem_pointedFinsetUnion_base
    {ι X : Type*} (p : X) (s : Finset ι) (S : ι → Set X) :
    p ∈ pointedFinsetUnion p s S := by
  simp [pointedFinsetUnion]

theorem mem_pointedFinsetUnion_iff
    {ι X : Type*} (p z : X) (s : Finset ι) (S : ι → Set X) :
    z ∈ pointedFinsetUnion p s S ↔
      z = p ∨ ∃ i ∈ s, z ∈ S i := by
  constructor
  · intro hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
      exact Or.inr ⟨i.1, i.2, hi⟩
  · rintro (rfl | ⟨i, hi, hz⟩)
    · simp [pointedFinsetUnion]
    · exact Or.inr (Set.mem_iUnion_of_mem ⟨i, hi⟩ hz)

/-- Component excess is subadditive for a finite pointed union whose members
all contain the chosen point. -/
theorem componentCount_pointedFinsetUnion_sub_one_le_sum_sub_one
    {ι X : Type*} [TopologicalSpace X] (p : X) (s : Finset ι)
    (S : ι → Set X)
    (hp : ∀ i ∈ s, p ∈ S i)
    (hfinite : ∀ i ∈ s, Finite (ConnectedComponents (S i))) :
    componentCount (pointedFinsetUnion p s S) - 1 ≤
      ∑ i ∈ s, (componentCount (S i) - 1) := by
  classical
  let Idx := {i // i ∈ s}
  let T : Option Idx → Set X
    | none => {p}
    | some i => S i.1
  have hsingleton :
      componentCount ({p} : Set X) - 1 = 0 := by
    haveI : Finite (ConnectedComponents ({p} : Set X)) :=
      finite_connectedComponents_of_finite_set (finite_singleton p)
    haveI : Subsingleton (ConnectedComponents ({p} : Set X)) := by
      refine ⟨?_⟩
      intro q r
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe q
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe r
      have hxy : x = y := by
        apply Subtype.ext
        have hx : x.1 = p := Set.mem_singleton_iff.mp x.property
        have hy : y.1 = p := Set.mem_singleton_iff.mp y.property
        exact hx.trans hy.symm
      exact congrArg ConnectedComponents.mk hxy
    unfold componentCount
    have hcard : Nat.card (ConnectedComponents ({p} : Set X)) ≤ 1 := by
      exact (Finite.card_le_one_iff_subsingleton).2 inferInstance
    haveI : Nonempty (ConnectedComponents ({p} : Set X)) :=
      ConnectedComponents.nonempty_iff_nonempty.mpr ⟨⟨p, by simp⟩⟩
    have hpos : 0 < Nat.card (ConnectedComponents ({p} : Set X)) :=
      Nat.card_pos
    omega
  have hTfinite : ∀ o : Option Idx,
      Finite (ConnectedComponents (T o)) := by
    intro o
    cases o with
    | none =>
        dsimp [T]
        exact finite_connectedComponents_of_finite_set (finite_singleton p)
    | some i =>
        dsimp [T]
        exact hfinite i.1 i.2
  haveI (o : Option Idx) : Finite (ConnectedComponents (T o)) :=
    hTfinite o
  have hpoint : ∀ o : Option Idx, p ∈ T o := by
    intro o
    cases o with
    | none => simp [T]
    | some i =>
        dsimp [T]
        exact hp i.1 i.2
  have hunion_eq :
      pointedFinsetUnion p s S = ⋃ o : Option Idx, T o := by
    ext z
    constructor
    · intro hz
      rcases (mem_pointedFinsetUnion_iff p z s S).1 hz with hz | hz
      · exact Set.mem_iUnion_of_mem (none : Option Idx) (by simpa [T] using hz)
      · rcases hz with ⟨i, hi, hzS⟩
        exact Set.mem_iUnion_of_mem (some (⟨i, hi⟩ : Idx)) hzS
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨o, ho⟩
      cases o with
      | none =>
          apply (mem_pointedFinsetUnion_iff p z s S).2
          exact Or.inl (by simpa [T] using ho)
      | some i =>
          apply (mem_pointedFinsetUnion_iff p z s S).2
          exact Or.inr ⟨i.1, i.2, by simpa [T] using ho⟩
  have hbound :
      componentCount (⋃ o : Option Idx, T o) - 1 ≤
        ∑ o : Option Idx, (componentCount (T o) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one p hpoint
  rw [hunion_eq]
  refine hbound.trans ?_
  rw [Fintype.sum_option, hsingleton, zero_add]
  exact le_of_eq (by
    simpa [Idx, T] using
      (Finset.sum_attach (s := s)
        (f := fun i => componentCount (S i) - 1)))

end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 24: `EndToEnd.Insertion`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Insertion bookkeeping for the concrete endpoint

This module records the set-level append operation and connects split-chain
component estimates to the actual `regionCount` of lollipop arrangements.
It is deliberately independent of the untrusted Jordan-curve draft code.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace Insertion

open Set

/-- Append one lollipop to a finite arrangement. -/
def snocArrangement {n : ℕ} (A : Arrangement n) (L : Lollipop) :
    Arrangement (n + 1) :=
  fun i => if h : i.1 < n then A ⟨i.1, h⟩ else L

@[simp] theorem snocArrangement_castSucc {n : ℕ}
    (A : Arrangement n) (L : Lollipop) (i : Fin n) :
    snocArrangement A L i.castSucc = A i := by
  simp [snocArrangement, i.2]

@[simp] theorem snocArrangement_last {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    snocArrangement A L (Fin.last n) = L := by
  simp [snocArrangement]

/-- An index of `Fin (n+1)` which is not below `n` is the last index. -/
theorem fin_eq_last_of_not_lt {n : ℕ} {i : Fin (n + 1)}
    (hi : ¬ i.1 < n) : i = Fin.last n := by
  apply Fin.ext
  simp only [Fin.val_last]
  omega

/-- Appending a lollipop adds exactly its carrier to the occupied set. -/
theorem occupied_snocArrangement {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    occupied (snocArrangement A L) = occupied A ∪ L.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_occupied_iff.mp hx
    by_cases hlt : i.1 < n
    · apply Or.inl
      apply mem_occupied_iff.mpr
      refine ⟨⟨i.1, hlt⟩, ?_⟩
      simpa [snocArrangement, hlt] using hi
    · apply Or.inr
      have hieq : i = Fin.last n := fin_eq_last_of_not_lt hlt
      subst i
      simpa using hi
  · rintro (hx | hx)
    · obtain ⟨i, hi⟩ := mem_occupied_iff.mp hx
      apply mem_occupied_iff.mpr
      exact ⟨i.castSucc, by simpa using hi⟩
    · apply mem_occupied_iff.mpr
      exact ⟨Fin.last n, by simpa using hx⟩

/-- Region count after an append is component count of the complement of the
old occupied carrier union the inserted carrier. -/
theorem regionCount_snoc_eq_componentCount_union_compl
    {n : ℕ} (A : Arrangement n) (L : Lollipop) :
    regionCount (snocArrangement A L) =
      componentCount ((occupied A ∪ L.carrier)ᶜ) := by
  rw [regionCount_eq_componentCount_compl, occupied_snocArrangement]

/-- `FreeSpace A` is the ordinary occupied complement, with the equivalent
predicate made explicit. -/
def freeSpaceHomeomorphOccupiedCompl {n : ℕ} (A : Arrangement n) :
    FreeSpace A ≃ₜ (((occupied A : Set Point)ᶜ) : Set Point) :=
  Homeomorph.setCongr (by
    ext x
    rfl)

/-- Component quotients are invariant under the complement-predicate
homeomorphism. -/
noncomputable def freeSpaceComponentsEquivOccupiedCompl {n : ℕ}
    (A : Arrangement n) :
    ConnectedComponents (FreeSpace A) ≃
      ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point) :=
  connectedComponentsEquivOfHomeomorph
    (freeSpaceHomeomorphOccupiedCompl A)

/-- Finiteness transfer from `FreeSpace A` to the ordinary occupied
complement subtype. -/
theorem finite_occupiedCompl_of_freeSpace {n : ℕ} (A : Arrangement n)
    [Finite (ConnectedComponents (FreeSpace A))] :
    Finite (ConnectedComponents
      (((occupied A : Set Point)ᶜ) : Set Point)) :=
  Finite.of_equiv _ (freeSpaceComponentsEquivOccupiedCompl A)

/-- The appended free space is homeomorphic to the complement of the union of
the old occupied set with the inserted carrier. -/
def freeSpaceSnocHomeomorphUnionCompl {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    FreeSpace (snocArrangement A L) ≃ₜ
      ((((occupied A : Set Point) ∪ L.carrier)ᶜ) : Set Point) :=
  (freeSpaceHomeomorphOccupiedCompl (snocArrangement A L)).trans
    (Homeomorph.setCongr (by
      rw [occupied_snocArrangement]))

/-- Component quotient equivalence for the appended free space. -/
noncomputable def freeSpaceSnocComponentsEquivUnionCompl {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    ConnectedComponents (FreeSpace (snocArrangement A L)) ≃
      ConnectedComponents
        ((((occupied A : Set Point) ∪ L.carrier)ᶜ) : Set Point) :=
  connectedComponentsEquivOfHomeomorph
    (freeSpaceSnocHomeomorphUnionCompl A L)

/-- The new complement is a subset of the old complement after inserting a
carrier. -/
theorem union_compl_subset_occupied_compl {n : ℕ}
    (A : Arrangement n) (L : Lollipop) :
    (occupied A ∪ L.carrier)ᶜ ⊆ (occupied A)ᶜ := by
  intro x hx hxOld
  exact hx (Or.inl hxOld)

/-- A finite chain of one-component splits for one insertion.  It runs from
the new complement to the old complement. -/
structure InsertionSplitChain {n : ℕ}
    (A : Arrangement n) (L : Lollipop) where
  edgeCount : ℕ
  chain : ComponentSplitChain.Chain edgeCount
    ((occupied A ∪ L.carrier)ᶜ) ((occupied A)ᶜ)

/-- Exact version of `InsertionSplitChain`. -/
structure ExactInsertionSplitChain {n : ℕ}
    (A : Arrangement n) (L : Lollipop) where
  edgeCount : ℕ
  chain : ComponentSplitChain.ExactChain edgeCount
    ((occupied A ∪ L.carrier)ᶜ) ((occupied A)ᶜ)

/-- Exact insertion chains can be used as bounded insertion chains. -/
def ExactInsertionSplitChain.toInsertionSplitChain
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    (h : ExactInsertionSplitChain A L) : InsertionSplitChain A L where
  edgeCount := h.edgeCount
  chain := h.chain.toChain

/-- Finiteness of old complement components propagates through a split-chain
insertion. -/
theorem finite_newComponents_of_insertionSplitChain
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    [Finite (ConnectedComponents (FreeSpace A))]
    (h : InsertionSplitChain A L) :
    Finite (ConnectedComponents
      (FreeSpace (snocArrangement A L))) := by
  haveI : Finite
      (ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point)) :=
    finite_occupiedCompl_of_freeSpace A
  have hnew : Finite
      (ConnectedComponents
        ((((occupied A : Set Point) ∪ L.carrier)ᶜ) : Set Point)) :=
    h.chain.finite_source
  exact Finite.of_equiv _
    (freeSpaceSnocComponentsEquivUnionCompl A L).symm

/-- A bounded split-chain insertion raises region count by at most the chain
length. -/
theorem regionCount_snoc_le_add_edgeCount
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    [Finite (ConnectedComponents (FreeSpace A))]
    (h : InsertionSplitChain A L) :
    regionCount (snocArrangement A L) ≤ regionCount A + h.edgeCount := by
  haveI : Finite
      (ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point)) :=
    finite_occupiedCompl_of_freeSpace A
  rw [regionCount_snoc_eq_componentCount_union_compl,
    regionCount_eq_componentCount_compl A]
  exact h.chain.componentCount_le

/-- An exact split-chain insertion gives the exact region-count increment. -/
theorem regionCount_snoc_eq_add_edgeCount
    {n : ℕ} {A : Arrangement n} {L : Lollipop}
    [Finite (ConnectedComponents (FreeSpace A))]
    (h : ExactInsertionSplitChain A L) :
    regionCount (snocArrangement A L) = regionCount A + h.edgeCount := by
  haveI : Finite
      (ConnectedComponents (((occupied A : Set Point)ᶜ) : Set Point)) :=
    finite_occupiedCompl_of_freeSpace A
  rw [regionCount_snoc_eq_componentCount_union_compl,
    regionCount_eq_componentCount_compl A]
  exact h.chain.componentCount_eq

end Insertion
end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 25: `EndToEnd.PlanarInsertion`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Ordered insertion reduction for the planar complement inequality

This file isolates a finite prefixArrangement reduction for the remaining planar
topology.  It does not prove the Jordan/embedded-graph step.  Instead, it
shows that local insertion bounds, or stronger split-chain data for each
insertion, imply the global arbitrary-arrangement pair-excess inequality used
by `PlanarTopologyPorts`.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace PlanarInsertion

open BigOperators

/-- Restrict a final arrangement to its first `k` natural indices. -/
def prefixArrangement {n : ℕ} (A : Arrangement n) (k : ℕ) (hk : k ≤ n) :
    Arrangement k :=
  fun i => A ⟨i.1, i.2.trans_le hk⟩

@[simp] theorem prefix_apply {n : ℕ} (A : Arrangement n)
    (k : ℕ) (hk : k ≤ n) (i : Fin k) :
    prefixArrangement A k hk i = A ⟨i.1, i.2.trans_le hk⟩ := rfl

/-- Restricting to all `n` indices recovers the original arrangement. -/
theorem prefix_full {n : ℕ} (A : Arrangement n) :
    prefixArrangement A n le_rfl = A := by
  funext i
  apply congrArg A
  exact Fin.ext rfl

/-- The next occupied prefixArrangement is the old occupied prefixArrangement union the new carrier.
-/
theorem occupied_prefix_succ {n : ℕ} (A : Arrangement n)
    {k : ℕ} (hk : k < n) :
    occupied (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) =
      occupied (prefixArrangement A k (Nat.le_of_lt hk)) ∪
        (A ⟨k, hk⟩).carrier := by
  ext x
  constructor
  · intro hx
    rcases mem_occupied_iff.mp hx with ⟨i, hi⟩
    by_cases hik : i.1 < k
    · left
      apply mem_occupied_iff.mpr
      let j : Fin k := ⟨i.1, hik⟩
      refine ⟨j, ?_⟩
      change x ∈ (A ⟨i.1,
        i.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier at hi
      change x ∈ (A ⟨j.1,
        j.2.trans_le (Nat.le_of_lt hk)⟩).carrier
      simpa [j] using hi
    · right
      have hieq : i.1 = k := by omega
      change x ∈ (A ⟨i.1,
        i.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier at hi
      simpa [hieq] using hi
  · intro hx
    rcases hx with hx | hx
    · rcases mem_occupied_iff.mp hx with ⟨i, hi⟩
      apply mem_occupied_iff.mpr
      let j : Fin (k + 1) := ⟨i.1, by omega⟩
      refine ⟨j, ?_⟩
      change x ∈ (A ⟨i.1,
        i.2.trans_le (Nat.le_of_lt hk)⟩).carrier at hi
      change x ∈ (A ⟨j.1,
        j.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier
      simpa [j] using hi
    · apply mem_occupied_iff.mpr
      let j : Fin (k + 1) := ⟨k, by omega⟩
      refine ⟨j, ?_⟩
      change x ∈ (A ⟨j.1,
        j.2.trans_le (Nat.succ_le_of_lt hk)⟩).carrier
      simpa [j] using hx

/-- The next prefixArrangement is the append of the old prefixArrangement by the new lollipop. -/
theorem prefix_succ_eq_snocArrangement {n : ℕ} (A : Arrangement n)
    {k : ℕ} (hk : k < n) :
    prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk) =
      Insertion.snocArrangement
        (prefixArrangement A k (Nat.le_of_lt hk)) (A ⟨k, hk⟩) := by
  funext i
  by_cases hik : i.1 < k
  · simp [prefixArrangement, Insertion.snocArrangement, hik]
  · have hi : i = Fin.last k := Insertion.fin_eq_last_of_not_lt hik
    subst i
    simp [prefixArrangement, Insertion.snocArrangement]

/-- Finite component count for the empty prefixArrangement. -/
theorem finite_prefixComponents_zero {n : ℕ} (A : Arrangement n)
    (hk : 0 ≤ n) :
    Finite (ConnectedComponents (FreeSpace (prefixArrangement A 0 hk))) := by
  have hset : {x : Point | x ∉ occupied (prefixArrangement A 0 hk)} = Set.univ := by
    ext x
    simp [occupied_zero (prefixArrangement A 0 hk)]
  have hpre : IsPreconnected
      ({x : Point | x ∉ occupied (prefixArrangement A 0 hk)}) := by
    rw [hset]
    exact isPreconnected_univ
  haveI : PreconnectedSpace (FreeSpace (prefixArrangement A 0 hk)) :=
    Subtype.preconnectedSpace hpre
  exact .of_subsingleton

/-- Local upper-topology proposition for one fixed final arrangement. -/
def OrderedInsertionRegionBound {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    regionCountRat
        (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) ≤
      regionCountRat (prefixArrangement A k (Nat.le_of_lt hk)) +
        TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1

/-- Universal form of the remaining ordered insertion theorem. -/
def PlanarInsertionRegionBoundStatement : Prop :=
  ∀ {n : ℕ} (A : Arrangement n), OrderedInsertionRegionBound A

/-- Stronger split-chain input for one fixed final arrangement. -/
def OrderedInsertionSplitChainBound {n : ℕ} (A : Arrangement n) : Prop :=
  ∀ (k : ℕ) (hk : k < n),
    ∃ h : Insertion.InsertionSplitChain
        (prefixArrangement A k (Nat.le_of_lt hk)) (A ⟨k, hk⟩),
      (h.edgeCount : ℚ) ≤
        TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1

/-- Split-chain data propagate finiteness through all ordered prefixes. -/
theorem finite_prefixComponents_of_orderedSplitChain
    {n : ℕ} (A : Arrangement n)
    (hsplit : OrderedInsertionSplitChainBound A) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Finite (ConnectedComponents (FreeSpace (prefixArrangement A k hk))) := by
  intro k
  induction k with
  | zero =>
      intro hk
      exact finite_prefixComponents_zero A hk
  | succ k ih =>
      intro hkSucc
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      rcases hsplit k hk with ⟨hchain, _hbudget⟩
      haveI : Finite
          (ConnectedComponents
            (FreeSpace (prefixArrangement A k (Nat.le_of_lt hk)))) :=
        ih (Nat.le_of_lt hk)
      rw [prefix_succ_eq_snocArrangement A hk]
      exact Insertion.finite_newComponents_of_insertionSplitChain hchain

/-- Split-chain data with a rational edge budget imply the ordered insertion
region bound. -/
theorem orderedInsertionRegionBound_of_splitChain
    {n : ℕ} (A : Arrangement n)
    (hsplit : OrderedInsertionSplitChainBound A) :
    OrderedInsertionRegionBound A := by
  intro k hk
  rcases hsplit k hk with ⟨hchain, hbudget⟩
  haveI : Finite
      (ConnectedComponents
        (FreeSpace (prefixArrangement A k (Nat.le_of_lt hk)))) :=
    finite_prefixComponents_of_orderedSplitChain A hsplit k
      (Nat.le_of_lt hk)
  have hnat :
      regionCount (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) ≤
        regionCount (prefixArrangement A k (Nat.le_of_lt hk)) +
          hchain.edgeCount := by
    rw [prefix_succ_eq_snocArrangement A hk]
    exact Insertion.regionCount_snoc_le_add_edgeCount hchain
  have hq :
      regionCountRat (prefixArrangement A (k + 1) (Nat.succ_le_of_lt hk)) ≤
        regionCountRat (prefixArrangement A k (Nat.le_of_lt hk)) +
          (hchain.edgeCount : ℚ) := by
    unfold regionCountRat
    exact_mod_cast hnat
  linarith

/-- Finite induction over prefixes: local insertion inequalities bound every
prefixArrangement by the sum of all earlier-pair contributions seen so far. -/
theorem prefix_regionCountRat_le_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionBound A) :
    ∀ (k : ℕ) (hk : k ≤ n),
      regionCountRat (prefixArrangement A k hk) ≤
        (∑ r ∈ Finset.range k,
          TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
          (k : ℚ) + 1 := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [regionCountRat_zero]
      simp
  | succ k ih =>
      intro hkSucc
      have hk : k < n := Nat.lt_of_succ_le hkSucc
      have hstep := hinsert k hk
      have hprev := ih (Nat.le_of_lt hk)
      calc
        regionCountRat (prefixArrangement A (Nat.succ k) hkSucc) ≤
            regionCountRat (prefixArrangement A k (Nat.le_of_lt hk)) +
              TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
          simpa [Nat.succ_eq_add_one] using hstep
        _ ≤ ((∑ r ∈ Finset.range k,
                TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
              (k : ℚ) + 1) +
            TheoremOneManuscript.previousPairAdded (pairExcessTable A) k + 1 := by
          gcongr
        _ = (∑ r ∈ Finset.range (Nat.succ k),
                TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
              (Nat.succ k : ℚ) + 1 := by
          rw [Finset.sum_range_succ]
          simp [Nat.cast_succ]
          ring

/-- The local ordered insertion theorem implies the full planar complement
pair-sum upper inequality for the fixed arrangement. -/
theorem regionCountRat_le_pairSum_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionBound A) :
    regionCountRat A ≤
      (n : ℚ) + 1 + pairSum n (pairExcessTable A) := by
  have hprefix :=
    prefix_regionCountRat_le_of_orderedInsertion A hinsert n le_rfl
  calc
    regionCountRat A = regionCountRat (prefixArrangement A n le_rfl) := by
      rw [prefix_full]
    _ ≤ (∑ r ∈ Finset.range n,
          TheoremOneManuscript.previousPairAdded (pairExcessTable A) r) +
          (n : ℚ) + 1 := hprefix
    _ = pairSum n (pairExcessTable A) + (n : ℚ) + 1 := by
      rw [TheoremOneManuscript.sum_range_previousPairAdded_eq_pairSum]
    _ = (n : ℚ) + 1 + pairSum n (pairExcessTable A) := by
      ring

/-- Ordered insertion control implies the exact planar-topology inequality
field required by `PlanarTopologyPorts`. -/
theorem crossing_excess_le_pairSum_of_orderedInsertion
    {n : ℕ} (A : Arrangement n)
    (hinsert : OrderedInsertionRegionBound A) :
    regionCountRat A - (n : ℚ) - 1 ≤ pairSum n (pairExcessTable A) := by
  have h := regionCountRat_le_pairSum_of_orderedInsertion A hinsert
  linarith

/-- Universal ordered insertion control is sufficient for the
arbitrary-arrangement planar complement inequality. -/
theorem crossing_excess_le_pairSum_of_insertion
    (hinsert : PlanarInsertionRegionBoundStatement) :
    ∀ {n : ℕ} (A : Arrangement n),
      regionCountRat A - (n : ℚ) - 1 ≤ pairSum n (pairExcessTable A) := by
  intro n A
  exact crossing_excess_le_pairSum_of_orderedInsertion A (hinsert A)

/-- Split-chain control is a stronger route to the same ordered insertion
statement. -/
theorem planarInsertionRegionBoundStatement_of_splitChain
    (hsplit : ∀ {n : ℕ} (A : Arrangement n),
      OrderedInsertionSplitChainBound A) :
    PlanarInsertionRegionBoundStatement := by
  intro n A
  exact orderedInsertionRegionBound_of_splitChain A (hsplit A)

end PlanarInsertion
end EndToEnd
end Concrete
end Lollipop

/-!
Proof component 26: `EndToEnd.PlanarTopology`.
The complete checked source follows; it is part of this numbered proof
module rather than an import from a generic project support directory.
-/

/-!
# Planar topology boundary

The concrete upper and lower endpoints need two hard planar-topology facts:

1. the arbitrary-arrangement pair-excess bound
   `regions(A) - n - 1 ≤ Σ q(Aᵢ,Aⱼ)`;
2. the generic Euler equation
   `regions(A) = crossings(A) + n + 1`.

The previous version of this file sketched these proofs using unavailable
Mathlib APIs for Alexander duality, Mayer--Vietoris, semialgebraic
triangulation, and connected-component homeomorphisms.  This file records the
same obligations as explicit concrete theorem targets.  They are not abstract
`GeometryCertificates`: every field is stated for the concrete Euclidean
lollipop model and the concrete connected-component region count.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd

open Set

/-- Remaining planar-topology theorem package for the concrete model. -/
structure PlanarTopologyPorts : Prop where
  region_components_finite :
    ∀ {n : ℕ} (A : Arrangement n),
      Finite (ConnectedComponents (FreeSpace A))
  crossing_excess_le_pairSum :
    ∀ {n : ℕ} (A : Arrangement n),
      regionCountRat A - (n : ℚ) - 1 ≤
        Lollipop.pairSum n (pairExcessTable A)
  generic_region_eq :
    ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
      regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1

/-- Build the planar topology port from local ordered insertion control plus
the generic Euler equation. -/
def PlanarTopologyPorts.ofOrderedInsertion
    (hfinite : ∀ {n : ℕ} (A : Arrangement n),
      Finite (ConnectedComponents (FreeSpace A)))
    (hinsert : PlanarInsertion.PlanarInsertionRegionBoundStatement)
    (hgeneric :
      ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
        regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1) :
    PlanarTopologyPorts where
  region_components_finite := hfinite
  crossing_excess_le_pairSum := by
    intro n A
    exact PlanarInsertion.crossing_excess_le_pairSum_of_insertion hinsert A
  generic_region_eq := hgeneric

/-- Build the planar topology port from universal split-chain insertion data.
The split chains also prove finiteness of every prefix complement. -/
def PlanarTopologyPorts.ofSplitChain
    (hsplit : ∀ {n : ℕ} (A : Arrangement n),
      PlanarInsertion.OrderedInsertionSplitChainBound A)
    (hgeneric :
      ∀ {n : ℕ} {A : Arrangement n}, IsGeneric A →
        regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1) :
    PlanarTopologyPorts where
  region_components_finite := by
    intro n A
    have hprefix :=
      PlanarInsertion.finite_prefixComponents_of_orderedSplitChain
        A (hsplit A) n le_rfl
    rw [PlanarInsertion.prefix_full A] at hprefix
    exact hprefix
  crossing_excess_le_pairSum := by
    intro n A
    exact PlanarInsertion.crossing_excess_le_pairSum_of_orderedInsertion A
      (PlanarInsertion.orderedInsertionRegionBound_of_splitChain A (hsplit A))
  generic_region_eq := hgeneric

theorem region_components_finite_zero (A : Arrangement 0) :
    Finite (ConnectedComponents (FreeSpace A)) := by
  have hset : {x : Point | x ∉ occupied A} = univ := by
    ext x
    simp [occupied_zero A]
  have hpre : IsPreconnected ({x : Point | x ∉ occupied A}) := by
    rw [hset]
    exact isPreconnected_univ
  haveI : PreconnectedSpace (FreeSpace A) := Subtype.preconnectedSpace hpre
  exact .of_subsingleton

theorem crossing_excess_le_pairSum_zero (A : Arrangement 0) :
    regionCountRat A - (0 : ℚ) - 1 ≤
      Lollipop.pairSum 0 (pairExcessTable A) := by
  simp [regionCountRat_zero A, Lollipop.pairSum, Lollipop.pairFinset]

theorem regionCountRat_eq_crossings_add_zero
    {A : Arrangement 0} (_hA : IsGeneric A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (0 : ℚ) + 1 := by
  simp [regionCountRat_zero A, totalCrossingsNat, Lollipop.pairFinset]

/-- Finiteness of concrete complement components, from the planar topology
package. -/
theorem region_components_finite (ports : PlanarTopologyPorts)
    {n : ℕ} (A : Arrangement n) :
    Finite (ConnectedComponents (FreeSpace A)) :=
  ports.region_components_finite A

/-- Rational arbitrary-arrangement bound consumed by the colored Turan backend. -/
theorem crossing_excess_le_pairSum (ports : PlanarTopologyPorts)
    {n : ℕ} (A : Arrangement n) :
    regionCountRat A - (n : ℚ) - 1 ≤
      Lollipop.pairSum n (pairExcessTable A) :=
  ports.crossing_excess_le_pairSum A

/-- Generic exact region equation in rational form. -/
theorem regionCountRat_eq_crossings_add (ports : PlanarTopologyPorts)
    {n : ℕ} {A : Arrangement n} (hA : IsGeneric A) :
    regionCountRat A = ((totalCrossingsNat A : ℕ) : ℚ) + (n : ℚ) + 1 :=
  ports.generic_region_eq hA

end EndToEnd
end Concrete
end Lollipop

/-!
The manuscript-facing proposition is repeated here as `CoreStatement` so
this proof module does not cyclically import its public statement module.
`Statement.lean` imports this file and exposes the same expression under the
public name `Statement`.
-/

/-!
Manuscript Proposition 2.1 (`prop:top-region`): the arbitrary-arrangement
topological region inequality, together with its generic equality clause.
-/

namespace Lollipop.Manuscript.Proposition_2_1

open Concrete Concrete.EndToEnd

def CoreStatement : Prop :=
  (forall {n : Nat} (A : Arrangement n),
      regionCountRat A - (n : Rat) - 1 <= pairSum n (pairExcessTable A)) /\
  (forall {n : Nat} {A : Arrangement n}, IsGeneric A ->
      regionCountRat A = ((totalCrossingsNat A : Nat) : Rat) + (n : Rat) + 1)

end Lollipop.Manuscript.Proposition_2_1

/-! The actual numbered proof. -/

namespace Lollipop.Manuscript.Proposition_2_1

open Concrete Concrete.EndToEnd

theorem proof (ports : PlanarTopologyPorts) : CoreStatement := by
  constructor
  · intro n A
    exact ports.crossing_excess_le_pairSum A
  · intro n A hA
    exact ports.generic_region_eq hA

end Lollipop.Manuscript.Proposition_2_1
