import old_lean_folder.Concrete.EndToEnd.PlanarTopology
import old_lean_folder.Internal.ColoredTuran.PaulsenLinearAlgebra
import Mathlib.Tactic

/-!
# Concrete pair geometry

This file proves the four robust pair-excess bounds used by the colored Turán
backend.  The proofs count connected components, not intersection
multiplicity, so every statement remains valid for tangencies, coincident
circles, and overlapping stems.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace PairGeometry

open Set

/-- Compactify one primitive intersection together with infinity. -/
def hatPiece (S : Set Point) : Set Sphere2 := finiteLift S ∪ {infinity}

def pieceExcess (S : Set Point) : ℕ := componentCount (hatPiece S) - 1

/-- The four primitive pieces of a pair intersection. -/
def pairPiece (L M : Lollipop) (k : Fin 4) : Set Sphere2 :=
  match k.1 with
  | 0 => hatPiece (cc L M)
  | 1 => hatPiece (rc L M)
  | 2 => hatPiece (cr L M)
  | _ => hatPiece (rr L M)

/-- Three-piece decomposition used for close pairs, where the two mixed
primitive intersections are counted together. -/
def closePairPiece (L M : Lollipop) (k : Fin 3) : Set Sphere2 :=
  match k.1 with
  | 0 => hatPiece (cc L M)
  | 1 => hatPiece (cr L M ∪ rc L M)
  | _ => hatPiece (rr L M)

/-- Four-piece decomposition for intriguing pairs: mixed intersections already
lying on both circles are counted in the circle-circle piece. -/
def intriguingPairPiece (L M : Lollipop) (k : Fin 4) : Set Sphere2 :=
  match k.1 with
  | 0 => hatPiece (cc L M)
  | 1 => hatPiece (cr L M \ cc L M)
  | 2 => hatPiece (rc L M \ cc L M)
  | _ => hatPiece (rr L M)

@[simp] theorem infinity_mem_hatPiece (S : Set Point) :
    infinity ∈ hatPiece S := by
  simp [hatPiece]

/-- The compactified pair intersection is the union of the four compactified
primitive intersections. -/
theorem hatPairIntersection_decompose (L M : Lollipop) :
    hatPairIntersection L M =
      hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
        hatPiece (cr L M) ∪ hatPiece (rr L M) := by
  ext x
  cases x using OnePoint.rec with
  | infty =>
      change infinity ∈ hatPairIntersection L M ↔
        infinity ∈
          hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
            hatPiece (cr L M) ∪ hatPiece (rr L M)
      constructor
      · intro _h
        simp [hatPiece]
      · intro _h
        exact infinity_mem_hatPairIntersection L M
  | coe p =>
      change finitePoint p ∈ hatPairIntersection L M ↔
        finitePoint p ∈
          hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
            hatPiece (cr L M) ∪ hatPiece (rr L M)
      simp [hatPairIntersection, hatPiece, cc, rc, cr, rr, Lollipop.carrier]
      tauto

theorem hatPairIntersection_eq_iUnion_pairPiece (L M : Lollipop) :
    hatPairIntersection L M = ⋃ k : Fin 4, pairPiece L M k := by
  rw [hatPairIntersection_decompose]
  ext x
  constructor
  · intro hx
    rcases hx with ((hcc | hrc) | hcr) | hrr
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [pairPiece] using hcc⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [pairPiece] using hrc⟩
    · exact Set.mem_iUnion.mpr ⟨2, by simpa [pairPiece] using hcr⟩
    · exact Set.mem_iUnion.mpr ⟨3, by simpa [pairPiece] using hrr⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    fin_cases k <;> simp [pairPiece] at hk ⊢ <;> tauto

/-- Close-pair decomposition with the two mixed pieces merged. -/
theorem hatPairIntersection_decompose_close (L M : Lollipop) :
    hatPairIntersection L M =
      hatPiece (cc L M) ∪ hatPiece (cr L M ∪ rc L M) ∪
        hatPiece (rr L M) := by
  ext x
  cases x using OnePoint.rec with
  | infty =>
      change infinity ∈ hatPairIntersection L M ↔
        infinity ∈
          hatPiece (cc L M) ∪ hatPiece (cr L M ∪ rc L M) ∪
            hatPiece (rr L M)
      constructor
      · intro _h
        simp [hatPiece]
      · intro _h
        exact infinity_mem_hatPairIntersection L M
  | coe p =>
      change finitePoint p ∈ hatPairIntersection L M ↔
        finitePoint p ∈
          hatPiece (cc L M) ∪ hatPiece (cr L M ∪ rc L M) ∪
            hatPiece (rr L M)
      simp [hatPairIntersection, hatPiece, cc, rc, cr, rr, Lollipop.carrier]
      tauto

theorem hatPairIntersection_eq_iUnion_closePairPiece (L M : Lollipop) :
    hatPairIntersection L M = ⋃ k : Fin 3, closePairPiece L M k := by
  rw [hatPairIntersection_decompose_close]
  ext x
  constructor
  · intro hx
    rcases hx with (hcc | hmix) | hrr
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [closePairPiece] using hcc⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [closePairPiece] using hmix⟩
    · exact Set.mem_iUnion.mpr ⟨2, by simpa [closePairPiece] using hrr⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    fin_cases k <;> simp [closePairPiece] at hk ⊢ <;> tauto

/-- Intriguing-pair decomposition that removes the circle-circle overlap from
the two mixed primitives. -/
theorem hatPairIntersection_decompose_intriguing (L M : Lollipop) :
    hatPairIntersection L M =
      hatPiece (cc L M) ∪ hatPiece (cr L M \ cc L M) ∪
        hatPiece (rc L M \ cc L M) ∪ hatPiece (rr L M) := by
  rw [hatPairIntersection_decompose]
  ext x
  cases x using OnePoint.rec with
  | infty =>
      change infinity ∈
          hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
            hatPiece (cr L M) ∪ hatPiece (rr L M) ↔
        infinity ∈
          hatPiece (cc L M) ∪ hatPiece (cr L M \ cc L M) ∪
            hatPiece (rc L M \ cc L M) ∪ hatPiece (rr L M)
      simp [hatPiece]
  | coe p =>
      change finitePoint p ∈
          hatPiece (cc L M) ∪ hatPiece (rc L M) ∪
            hatPiece (cr L M) ∪ hatPiece (rr L M) ↔
        finitePoint p ∈
          hatPiece (cc L M) ∪ hatPiece (cr L M \ cc L M) ∪
            hatPiece (rc L M \ cc L M) ∪ hatPiece (rr L M)
      simp [hatPiece]
      tauto

theorem hatPairIntersection_eq_iUnion_intriguingPairPiece (L M : Lollipop) :
    hatPairIntersection L M = ⋃ k : Fin 4, intriguingPairPiece L M k := by
  rw [hatPairIntersection_decompose_intriguing]
  ext x
  constructor
  · intro hx
    rcases hx with ((hcc | hcr) | hrc) | hrr
    · exact Set.mem_iUnion.mpr ⟨0, by simpa [intriguingPairPiece] using hcc⟩
    · exact Set.mem_iUnion.mpr ⟨1, by simpa [intriguingPairPiece] using hcr⟩
    · exact Set.mem_iUnion.mpr ⟨2, by simpa [intriguingPairPiece] using hrc⟩
    · exact Set.mem_iUnion.mpr ⟨3, by simpa [intriguingPairPiece] using hrr⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨k, hk⟩
    fin_cases k <;> simp [intriguingPairPiece] at hk ⊢ <;> tauto

/-- Close means the smaller angle between actual stem directions is at most a
right angle. -/
def Close (L M : Lollipop) : Prop :=
  0 ≤ TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
    (R2.ofPoint L.unitRadial) (R2.ofPoint M.unitRadial)

/-- The manuscript's intriguing-circle relation.  A pair is intriguing when
the two circle curves are disjoint, or when their squared center distance is at
most the sum of the squared radii.  In particular, an **external tangency is
not** intriguing: the circles meet, while the second inequality is false.

This boundary convention is essential.  The canonical Paulsen relation in the
older backend is the complement of an *open* obtuse interval and therefore
classifies an external tangency as intriguing.  That broader relation does not
satisfy the required five-component pair bound.  `Upper.lean` instead applies
the Paulsen obstruction after one uniform infinitesimal enlargement of all
radii, exactly as in the manuscript. -/
def Intriguing (L M : Lollipop) : Prop :=
  ¬ (cc L M).Nonempty ∨
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
      (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
        L.radius ^ 2 + M.radius ^ 2

@[simp] theorem close_symm (L M : Lollipop) : Close L M ↔ Close M L := by
  unfold Close TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2
  constructor <;> intro h <;> nlinarith

@[simp] theorem intriguing_symm (L M : Lollipop) :
    Intriguing L M ↔ Intriguing M L := by
  unfold Intriguing
  rw [TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2_symm]
  have hcc : (cc M L).Nonempty ↔ (cc L M).Nonempty := by
    simp [cc, inter_comm]
  rw [hcc]
  constructor <;> rintro (hdisj | hnear)
  · exact Or.inl hdisj
  · exact Or.inr (by nlinarith)
  · exact Or.inl hdisj
  · exact Or.inr (by nlinarith)

def normSqPoint (x : Point) : ℝ :=
  TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 (R2.ofPoint x)

@[simp] theorem dotPoint_add_left (x y z : Point) :
    dotPoint (x + y) z = dotPoint x z + dotPoint y z := by
  unfold dotPoint
  simp
  ring

@[simp] theorem dotPoint_add_right (x y z : Point) :
    dotPoint x (y + z) = dotPoint x y + dotPoint x z := by
  rw [dotPoint_comm, dotPoint_add_left, dotPoint_comm y x, dotPoint_comm z x]

@[simp] theorem dotPoint_sub_left (x y z : Point) :
    dotPoint (x - y) z = dotPoint x z - dotPoint y z := by
  unfold dotPoint
  simp
  ring

@[simp] theorem dotPoint_sub_right (x y z : Point) :
    dotPoint x (y - z) = dotPoint x y - dotPoint x z := by
  rw [dotPoint_comm, dotPoint_sub_left, dotPoint_comm y x, dotPoint_comm z x]

@[simp] theorem dotPoint_smul_left (a : ℝ) (x y : Point) :
    dotPoint (a • x) y = a * dotPoint x y := by
  unfold dotPoint
  simp
  ring

@[simp] theorem dotPoint_smul_right (a : ℝ) (x y : Point) :
    dotPoint x (a • y) = a * dotPoint x y := by
  rw [dotPoint_comm, dotPoint_smul_left, dotPoint_comm y x]

theorem normSqPoint_eq_norm_sq (x : Point) :
    normSqPoint x = ‖x‖ ^ 2 := by
  calc
    normSqPoint x =
        TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2 (R2.ofPoint x) := rfl
    _ = ‖R2.toPoint (R2.ofPoint x)‖ ^ 2 := by
          rw [← R2.norm_sq_toPoint]
    _ = ‖x‖ ^ 2 := by simp

@[simp] theorem normSqPoint_unitRadial (L : Lollipop) :
    normSqPoint L.unitRadial = 1 := by
  rw [normSqPoint_eq_norm_sq, L.norm_unitRadial]
  norm_num

theorem dotPoint_sq_le_normSqPoint_mul_normSqPoint (x y : Point) :
    dotPoint x y ^ 2 ≤ normSqPoint x * normSqPoint y := by
  unfold dotPoint normSqPoint
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 R2.ofPoint
  nlinarith [sq_nonneg (x 0 * y 1 - x 1 * y 0)]

theorem dotPoint_le_of_normSqPoint_eq_of_unit
    {x u : Point} {r : ℝ}
    (hr : 0 ≤ r)
    (hx : normSqPoint x = r ^ 2)
    (hu : normSqPoint u = 1) :
    dotPoint x u ≤ r := by
  have hcs := dotPoint_sq_le_normSqPoint_mul_normSqPoint x u
  rw [hx, hu, mul_one] at hcs
  by_cases hdot : dotPoint x u ≤ 0
  · exact hdot.trans hr
  · have hdot0 : 0 < dotPoint x u := lt_of_not_ge hdot
    nlinarith [sq_nonneg (dotPoint x u - r)]

def radialStemPoint (L : Lollipop) (q : ℝ) : Point :=
  L.center + q • L.unitRadial

theorem mem_stem_iff_exists_radius_le (L : Lollipop) (x : Point) :
    x ∈ L.stem ↔
      ∃ q : ℝ, L.radius ≤ q ∧ x = radialStemPoint L q := by
  rw [L.stem_eq_stemByDistance]
  rfl

@[simp] theorem radialStemPoint_sub_center (L : Lollipop) (q : ℝ) :
    radialStemPoint L q - L.center = q • L.unitRadial := by
  simp [radialStemPoint]

theorem normSq_radialStemPoint_sub_center
    (L M : Lollipop) (q : ℝ) :
    normSqPoint (radialStemPoint L q - M.center) =
      q ^ 2 -
        2 * q * dotPoint (M.center - L.center) L.unitRadial +
        normSqPoint (M.center - L.center) := by
  unfold radialStemPoint normSqPoint dotPoint
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 R2.ofPoint
  simp
  have hu := normSqPoint_unitRadial L
  unfold normSqPoint TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 R2.ofPoint at hu
  simp at hu
  nlinarith

theorem radialStemPoint_injective (L : Lollipop) :
    Function.Injective (radialStemPoint L) := by
  intro q p hqp
  have hsmul : q • L.unitRadial = p • L.unitRadial := by
    simpa [radialStemPoint] using hqp
  have hsub : (q - p) • L.unitRadial = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hsmul
  by_contra hne
  have hscalar : q - p ≠ 0 := sub_ne_zero.mpr hne
  rcases smul_eq_zero.mp hsub with hzero | hzero
  · exact hscalar hzero
  · exact L.unitRadial_ne_zero hzero

theorem center_projection_gt_radius_of_two_stem_circle_points
    {L M : Lollipop} {x y : Point}
    (hxstem : x ∈ L.stem) (hxcircle : x ∈ M.circle)
    (hystem : y ∈ L.stem) (hycircle : y ∈ M.circle)
    (hxy : x ≠ y) :
    L.radius < dotPoint (M.center - L.center) L.unitRadial := by
  rcases (mem_stem_iff_exists_radius_le L x).1 hxstem with
    ⟨q, hq, rfl⟩
  rcases (mem_stem_iff_exists_radius_le L y).1 hystem with
    ⟨p, hp, rfl⟩
  have hqp : q ≠ p := by
    intro h
    apply hxy
    simpa [h]
  have hxnorm :
      normSqPoint (radialStemPoint L q - M.center) = M.radius ^ 2 := by
    rw [normSqPoint_eq_norm_sq]
    have hx := hxcircle
    change ‖radialStemPoint L q - M.center‖ = M.radius at hx
    rw [hx]
  have hynorm :
      normSqPoint (radialStemPoint L p - M.center) = M.radius ^ 2 := by
    rw [normSqPoint_eq_norm_sq]
    have hy := hycircle
    change ‖radialStemPoint L p - M.center‖ = M.radius at hy
    rw [hy]
  rw [normSq_radialStemPoint_sub_center L M q] at hxnorm
  rw [normSq_radialStemPoint_sub_center L M p] at hynorm
  let a := dotPoint (M.center - L.center) L.unitRadial
  have hfactor : (q - p) * (q + p - 2 * a) = 0 := by
    dsimp [a]
    nlinarith
  have hsum : q + p = 2 * a := by
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact (hqp (sub_eq_zero.mp hzero)).elim
    · nlinarith
  by_contra hnot
  have ha : a ≤ L.radius := le_of_not_gt hnot
  have hqr : q = L.radius := by nlinarith
  have hpr : p = L.radius := by nlinarith
  exact hqp (hqr.trans hpr.symm)

theorem cr_symm_rc (L M : Lollipop) : cr L M = rc M L := by
  simp [cr, rc, inter_comm]

theorem cc_symm (L M : Lollipop) : cc L M = cc M L := by
  simp [cc, inter_comm]

theorem cr_eq_empty_of_close_of_two_rc_points
    {L M : Lollipop}
    (hclose : Close L M)
    {x y : Point}
    (hx : x ∈ rc L M) (hy : y ∈ rc L M) (hxy : x ≠ y) :
    cr L M = ∅ := by
  have hproj :
      L.radius < dotPoint (M.center - L.center) L.unitRadial :=
    center_projection_gt_radius_of_two_stem_circle_points
      hx.1 hx.2 hy.1 hy.2 hxy
  ext z
  constructor
  · intro hz
    have hzLcircle : z ∈ L.circle := hz.1
    have hzMstem : z ∈ M.stem := hz.2
    rcases (mem_stem_iff_exists_radius_le M z).1 hzMstem with
      ⟨t, ht, rfl⟩
    have htpos : 0 < t := lt_of_lt_of_le M.radius_pos ht
    have hdotuv : 0 ≤ dotPoint M.unitRadial L.unitRadial := by
      have hclose' : Close M L := (close_symm L M).1 hclose
      simpa [Close, dotPoint, TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2,
        R2.ofPoint] using hclose'
    have hexpand :
        dotPoint (radialStemPoint M t - L.center) L.unitRadial =
          dotPoint (M.center - L.center) L.unitRadial +
            t * dotPoint M.unitRadial L.unitRadial := by
      simp [radialStemPoint]
      ring
    have hgt :
        L.radius < dotPoint (radialStemPoint M t - L.center) L.unitRadial := by
      rw [hexpand]
      nlinarith
    have hnorm :
        normSqPoint (radialStemPoint M t - L.center) = L.radius ^ 2 := by
      rw [normSqPoint_eq_norm_sq]
      have hz' := hzLcircle
      change ‖radialStemPoint M t - L.center‖ = L.radius at hz'
      rw [hz']
    have hle :
        dotPoint (radialStemPoint M t - L.center) L.unitRadial ≤ L.radius :=
      dotPoint_le_of_normSqPoint_eq_of_unit L.radius_pos.le hnorm
        (normSqPoint_unitRadial L)
    exact False.elim ((not_lt_of_ge hle) hgt)
  · intro hz
    simp at hz

theorem rc_eq_empty_of_close_of_two_cr_points
    {L M : Lollipop}
    (hclose : Close L M)
    {x y : Point}
    (hx : x ∈ cr L M) (hy : y ∈ cr L M) (hxy : x ≠ y) :
    rc L M = ∅ := by
  have hclose' : Close M L := (close_symm L M).1 hclose
  have hx' : x ∈ rc M L := by simpa [cr_symm_rc] using hx
  have hy' : y ∈ rc M L := by simpa [cr_symm_rc] using hy
  have h := cr_eq_empty_of_close_of_two_rc_points hclose' hx' hy' hxy
  simpa [cr_symm_rc] using h

theorem exists_two_distinct_of_finite_ncard_eq_two
    {S : Set Point} (hfin : S.Finite) (hcard : S.ncard = 2) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
  classical
  have hcard' : hfin.toFinset.card = 2 := by
    simpa [Set.ncard_eq_toFinset_card S hfin] using hcard
  obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp hcard'
  refine ⟨x, ?_, y, ?_, hxy⟩
  · exact hfin.mem_toFinset.mp (by simpa [hset])
  · exact hfin.mem_toFinset.mp (by simpa [hset])

theorem mixed_union_ncard_le_two
    {L M : Lollipop} (hclose : Close L M) :
    (cr L M ∪ rc L M).ncard ≤ 2 := by
  have hcrfin := finite_circle_ray_intersection L M
  have hrcfin := finite_ray_circle_intersection L M
  have hcrle := circle_ray_intersection_ncard_le_two L M
  have hrcle : (rc L M).ncard ≤ 2 := by
    simpa [rc, cr, inter_comm] using circle_ray_intersection_ncard_le_two M L
  have hunion :
      (cr L M ∪ rc L M).ncard ≤ (cr L M).ncard + (rc L M).ncard :=
    Set.ncard_union_le (cr L M) (rc L M)
  by_cases hrc1 : (rc L M).ncard ≤ 1
  · by_cases hcr1 : (cr L M).ncard ≤ 1
    · omega
    · have hcr2 : (cr L M).ncard = 2 := by omega
      rcases exists_two_distinct_of_finite_ncard_eq_two hcrfin hcr2 with
        ⟨x, hx, y, hy, hxy⟩
      have hempty := rc_eq_empty_of_close_of_two_cr_points hclose hx hy hxy
      have hrc0 : (rc L M).ncard = 0 := by simp [hempty]
      omega
  · have hrc2 : (rc L M).ncard = 2 := by omega
    rcases exists_two_distinct_of_finite_ncard_eq_two hrcfin hrc2 with
      ⟨x, hx, y, hy, hxy⟩
    have hempty := cr_eq_empty_of_close_of_two_rc_points hclose hx hy hxy
    have hcr0 : (cr L M).ncard = 0 := by
      rw [hempty]
      simp
    omega

theorem componentCount_hatPiece_mixed_sub_one_le_two
    {L M : Lollipop} (hclose : Close L M) :
    componentCount (hatPiece (cr L M ∪ rc L M)) - 1 ≤ 2 := by
  have hfin : (cr L M ∪ rc L M).Finite :=
    (finite_circle_ray_intersection L M).union
      (finite_ray_circle_intersection L M)
  rw [hatPiece, componentCount_finiteLift_union_infinity_sub_one hfin]
  exact mixed_union_ncard_le_two hclose

theorem componentCount_hatPiece_sub_one_eq_ncard_of_finite
    {S : Set Point} (hfin : S.Finite) :
    componentCount (hatPiece S) - 1 = S.ncard := by
  simpa [hatPiece] using
    componentCount_finiteLift_union_infinity_sub_one hfin

theorem centerDistSq_eq_normSqPoint (L M : Lollipop) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) =
      normSqPoint (M.center - L.center) := by
  unfold normSqPoint TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2 R2.ofPoint
  simp [Pi.sub_apply]
  ring

theorem dotPoint_le_one_of_unit
    {u v : Point} (hu : normSqPoint u = 1) (hv : normSqPoint v = 1) :
    dotPoint u v ≤ 1 := by
  have hu' : normSqPoint u = (1 : ℝ) ^ 2 := by simpa using hu
  exact dotPoint_le_of_normSqPoint_eq_of_unit
    (r := 1) (by norm_num) hu' hv

theorem sq_sub_le_normSqPoint_neg_smul_add_smul
    {u v : Point} (hu : normSqPoint u = 1) (hv : normSqPoint v = 1)
    {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p) :
    (p - s) ^ 2 ≤ normSqPoint ((-s) • u + p • v) := by
  have huv : dotPoint u v ≤ 1 := dotPoint_le_one_of_unit hu hv
  have hsp : 0 ≤ s * p := mul_nonneg hs hp
  have hmul : s * p * dotPoint u v ≤ s * p := by
    have h := mul_le_mul_of_nonneg_left huv hsp
    simpa [mul_assoc] using h
  have hu' := hu
  have hv' := hv
  unfold normSqPoint at hu' hv' ⊢
  unfold dotPoint at huv hmul
  simp [TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2,
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2, R2.ofPoint] at hu' hv' huv hmul ⊢
  ring_nf at hu' hv' hmul ⊢
  nlinarith

theorem normSq_radialStemPoint_sub_self (L : Lollipop) (q : ℝ) :
    normSqPoint (radialStemPoint L q - L.center) = q ^ 2 := by
  rw [normSq_radialStemPoint_sub_center L L q]
  simp [dotPoint, normSqPoint,
    TheoremOneEndToEnd.PaulsenLinearAlgebra.dot2,
    TheoremOneEndToEnd.PaulsenLinearAlgebra.normSq2, R2.ofPoint]

theorem not_two_stem_circle_points_of_near
    {L M : Lollipop}
    (hnear : normSqPoint (M.center - L.center) ≤
      L.radius ^ 2 + M.radius ^ 2)
    {x y : Point}
    (hxstem : x ∈ L.stem) (hxcircle : x ∈ M.circle)
    (hystem : y ∈ L.stem) (hycircle : y ∈ M.circle)
    (hxy : x ≠ y) : False := by
  rcases (mem_stem_iff_exists_radius_le L x).1 hxstem with
    ⟨q, hq, rfl⟩
  rcases (mem_stem_iff_exists_radius_le L y).1 hystem with
    ⟨p, hp, rfl⟩
  have hqp : q ≠ p := by
    intro h
    apply hxy
    simpa [h]
  have hqeq :
      q ^ 2 - 2 * q * dotPoint (M.center - L.center) L.unitRadial +
          normSqPoint (M.center - L.center) = M.radius ^ 2 := by
    rw [← normSq_radialStemPoint_sub_center L M q,
      normSqPoint_eq_norm_sq]
    have h := hxcircle
    change ‖radialStemPoint L q - M.center‖ = M.radius at h
    rw [h]
  have hpeq :
      p ^ 2 - 2 * p * dotPoint (M.center - L.center) L.unitRadial +
          normSqPoint (M.center - L.center) = M.radius ^ 2 := by
    rw [← normSq_radialStemPoint_sub_center L M p,
      normSqPoint_eq_norm_sq]
    have h := hycircle
    change ‖radialStemPoint L p - M.center‖ = M.radius at h
    rw [h]
  let a := dotPoint (M.center - L.center) L.unitRadial
  have hfactor : (q - p) * (q + p - 2 * a) = 0 := by
    dsimp [a]
    nlinarith
  have hsum : q + p = 2 * a := by
    rcases mul_eq_zero.mp hfactor with hz | hz
    · exact (hqp (sub_eq_zero.mp hz)).elim
    · nlinarith
  have hprod :
      normSqPoint (M.center - L.center) - M.radius ^ 2 = q * p := by
    have hqeq' :
        q ^ 2 - 2 * q * a +
            normSqPoint (M.center - L.center) = M.radius ^ 2 := by
      simpa [a] using hqeq
    have htwice : 2 * a = q + p := by nlinarith [hsum]
    have hfrom :
        normSqPoint (M.center - L.center) - M.radius ^ 2 =
          -q ^ 2 + 2 * q * a := by
      nlinarith [hqeq']
    have hrewrite : 2 * q * a = q * (q + p) := by
      calc
        2 * q * a = q * (2 * a) := by ring
        _ = q * (q + p) := by rw [htwice]
    calc
      normSqPoint (M.center - L.center) - M.radius ^ 2 =
          -q ^ 2 + 2 * q * a := hfrom
      _ = -q ^ 2 + q * (q + p) := by rw [hrewrite]
      _ = q * p := by ring
  have hprod_gt : L.radius ^ 2 < q * p := by
    have hqpos : 0 < q := lt_of_lt_of_le L.radius_pos hq
    have hppos : 0 < p := lt_of_lt_of_le L.radius_pos hp
    by_cases hqeqr : q = L.radius
    · have hpgt : L.radius < p := by
        have hpne : p ≠ L.radius := by
          intro hpr
          exact hqp (hqeqr.trans hpr.symm)
        exact lt_of_le_of_ne hp (Ne.symm hpne)
      rw [hqeqr]
      nlinarith [L.radius_pos, hpgt]
    · have hqgt : L.radius < q := lt_of_le_of_ne hq (Ne.symm hqeqr)
      nlinarith [L.radius_pos, hqgt, hp]
  nlinarith [hnear, hprod, hprod_gt]

theorem parameter_gt_radius_of_rc_diff_cc
    {L M : Lollipop} {x : Point} {q : ℝ}
    (hx : x ∈ rc L M \ cc L M)
    (hxq : x = radialStemPoint L q) :
    L.radius < q := by
  have hq : L.radius ≤ q := by
    have hxstem : x ∈ L.stem := hx.1.1
    rcases (mem_stem_iff_exists_radius_le L x).1 hxstem with
      ⟨p, hp, hpEq⟩
    have hpq : p = q := radialStemPoint_injective L (hpEq.symm.trans hxq)
    simpa [hpq] using hp
  refine lt_of_le_of_ne hq ?_
  intro hqr
  have hxanchor : x = L.anchor := by
    rw [hxq, ← hqr]
    simp [radialStemPoint, Lollipop.anchor,
      L.radial_eq_radius_smul_unitRadial]
  have hxLcircle : x ∈ L.circle := by
    rw [hxanchor]
    exact L.anchor_mem_circle
  have hxMcircle : x ∈ M.circle := hx.1.2
  exact hx.2 ⟨hxLcircle, hxMcircle⟩

theorem anchor_strictly_inside_of_rc_diff_cc
    {L M : Lollipop}
    (hnear : normSqPoint (M.center - L.center) ≤
      L.radius ^ 2 + M.radius ^ 2)
    {x : Point}
    (hx : x ∈ rc L M \ cc L M) :
    normSqPoint (L.anchor - M.center) < M.radius ^ 2 := by
  have hxstem : x ∈ L.stem := hx.1.1
  have hxcircle : x ∈ M.circle := hx.1.2
  rcases (mem_stem_iff_exists_radius_le L x).1 hxstem with
    ⟨q, hq, hxq⟩
  have hqgt : L.radius < q :=
    parameter_gt_radius_of_rc_diff_cc hx hxq
  have hroot :
      q ^ 2 - 2 * q * dotPoint (M.center - L.center) L.unitRadial +
          normSqPoint (M.center - L.center) = M.radius ^ 2 := by
    rw [← normSq_radialStemPoint_sub_center L M q,
      normSqPoint_eq_norm_sq]
    have h := hxcircle
    rw [hxq] at h
    change ‖radialStemPoint L q - M.center‖ = M.radius at h
    rw [h]
  have hanchor :
      normSqPoint (L.anchor - M.center) =
        L.radius ^ 2 -
          2 * L.radius * dotPoint (M.center - L.center) L.unitRadial +
          normSqPoint (M.center - L.center) := by
    rw [show L.anchor = radialStemPoint L L.radius by
      simp [Lollipop.anchor, radialStemPoint,
        L.radial_eq_radius_smul_unitRadial]]
    exact normSq_radialStemPoint_sub_center L M L.radius
  have hother_lt :
      2 * dotPoint (M.center - L.center) L.unitRadial - q < L.radius := by
    by_contra hnot
    have hge : L.radius ≤
        2 * dotPoint (M.center - L.center) L.unitRadial - q :=
      le_of_not_gt hnot
    have hqpos : 0 < q := lt_trans L.radius_pos hqgt
    have hrpos := L.radius_pos
    nlinarith
  rw [hanchor]
  have hfactor :
      L.radius ^ 2 -
          2 * L.radius * dotPoint (M.center - L.center) L.unitRadial +
          normSqPoint (M.center - L.center) - M.radius ^ 2 =
        (q - L.radius) *
          (2 * dotPoint (M.center - L.center) L.unitRadial - q - L.radius) := by
    nlinarith
  have hneg :
      (q - L.radius) *
          (2 * dotPoint (M.center - L.center) L.unitRadial - q - L.radius) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hqgt) (by linarith)
  nlinarith [hfactor, hneg]

theorem rc_diff_cc_ncard_le_one_of_near
    {L M : Lollipop}
    (hnear : normSqPoint (M.center - L.center) ≤
      L.radius ^ 2 + M.radius ^ 2) :
    (rc L M \ cc L M).ncard ≤ 1 := by
  have hfin : (rc L M \ cc L M).Finite :=
    (finite_ray_circle_intersection L M).diff
  by_contra hnot
  have hge : 2 ≤ (rc L M \ cc L M).ncard := by omega
  have hle : (rc L M \ cc L M).ncard ≤ 2 :=
    le_trans (Set.ncard_le_ncard Set.diff_subset
      (finite_ray_circle_intersection L M))
      (by simpa [rc, cr, inter_comm] using
        circle_ray_intersection_ncard_le_two M L)
  have hcard : (rc L M \ cc L M).ncard = 2 := by omega
  rcases exists_two_distinct_of_finite_ncard_eq_two hfin hcard with
    ⟨x, hx, y, hy, hxy⟩
  exact not_two_stem_circle_points_of_near hnear
    hx.1.1 hx.1.2 hy.1.1 hy.1.2 hxy

theorem cr_diff_cc_ncard_le_one_of_near
    {L M : Lollipop}
    (hnear : normSqPoint (M.center - L.center) ≤
      L.radius ^ 2 + M.radius ^ 2) :
    (cr L M \ cc L M).ncard ≤ 1 := by
  have hnear_norm :
      ‖M.center - L.center‖ ^ 2 ≤ L.radius ^ 2 + M.radius ^ 2 := by
    simpa [normSqPoint_eq_norm_sq] using hnear
  have hnear' : normSqPoint (L.center - M.center) ≤
      M.radius ^ 2 + L.radius ^ 2 := by
    rw [normSqPoint_eq_norm_sq]
    simpa [norm_sub_rev, add_comm] using hnear_norm
  rw [cr_symm_rc L M, cc_symm L M]
  exact rc_diff_cc_ncard_le_one_of_near (L := M) (M := L) hnear'

theorem rr_eq_empty_of_both_outside_mixed_of_near
    {L M : Lollipop}
    (hnear : normSqPoint (M.center - L.center) ≤
      L.radius ^ 2 + M.radius ^ 2)
    (hleft : (rc L M \ cc L M).Nonempty)
    (hright : (cr L M \ cc L M).Nonempty) :
    rr L M = ∅ := by
  rcases hleft with ⟨zL, hzL⟩
  rcases hright with ⟨zM, hzM⟩
  have hinsideL : normSqPoint (L.anchor - M.center) < M.radius ^ 2 :=
    anchor_strictly_inside_of_rc_diff_cc hnear hzL
  have hnear_norm :
      ‖M.center - L.center‖ ^ 2 ≤ L.radius ^ 2 + M.radius ^ 2 := by
    simpa [normSqPoint_eq_norm_sq] using hnear
  have hnear' : normSqPoint (L.center - M.center) ≤
      M.radius ^ 2 + L.radius ^ 2 := by
    rw [normSqPoint_eq_norm_sq]
    simpa [norm_sub_rev, add_comm] using hnear_norm
  have hzM' : zM ∈ rc M L \ cc M L := by
    constructor
    · simpa [cr_symm_rc] using hzM.1
    · intro hcc
      exact hzM.2 (by simpa [cc_symm] using hcc)
  have hinsideM : normSqPoint (M.anchor - L.center) < L.radius ^ 2 :=
    anchor_strictly_inside_of_rc_diff_cc hnear' hzM'
  ext x
  constructor
  · intro hx
    have hxLstem : x ∈ L.stem := hx.1
    have hxMstem : x ∈ M.stem := hx.2
    rcases (mem_stem_iff_exists_radius_le L x).1 hxLstem with
      ⟨q, hq, hxq⟩
    rcases (mem_stem_iff_exists_radius_le M x).1 hxMstem with
      ⟨p, hp, hxp⟩
    have hline : radialStemPoint L q = radialStemPoint M p :=
      hxq.symm.trans hxp
    have hqgt : L.radius < q := by
      by_contra hnot
      have hqeq : q = L.radius := le_antisymm (le_of_not_gt hnot) hq
      have hxanchor : x = L.anchor := by
        rw [hxq, hqeq]
        simp [Lollipop.anchor, radialStemPoint,
          L.radial_eq_radius_smul_unitRadial]
      have hnormM : normSqPoint (x - M.center) = p ^ 2 := by
        rw [hxp, normSq_radialStemPoint_sub_self M p]
      rw [← hxanchor] at hinsideL
      have hp2 : M.radius ^ 2 ≤ p ^ 2 := by nlinarith [M.radius_pos, hp]
      nlinarith
    have hpgt : M.radius < p := by
      by_contra hnot
      have hpeq : p = M.radius := le_antisymm (le_of_not_gt hnot) hp
      have hxanchor : x = M.anchor := by
        rw [hxp, hpeq]
        simp [Lollipop.anchor, radialStemPoint,
          M.radial_eq_radius_smul_unitRadial]
      have hnormL : normSqPoint (x - L.center) = q ^ 2 := by
        rw [hxq, normSq_radialStemPoint_sub_self L q]
      rw [← hxanchor] at hinsideM
      have hq2 : L.radius ^ 2 ≤ q ^ 2 := by nlinarith [L.radius_pos, hq]
      nlinarith
    let s : ℝ := q - L.radius
    let t : ℝ := p - M.radius
    have hs : 0 < s := by dsimp [s]; linarith
    have ht : 0 < t := by dsimp [t]; linarith
    have hp0 : 0 ≤ p := le_trans M.radius_pos.le hp
    have hq0 : 0 ≤ q := le_trans L.radius_pos.le hq
    have hvecL :
        L.anchor - M.center = (-s) • L.unitRadial + p • M.unitRadial := by
      ext i
      have hi := congrArg (fun z : Point => z i) hline
      simp [radialStemPoint, Lollipop.anchor,
        L.radial_eq_radius_smul_unitRadial] at hi ⊢
      dsimp [s]
      nlinarith
    have hvecM :
        M.anchor - L.center = (-t) • M.unitRadial + q • L.unitRadial := by
      ext i
      have hi := congrArg (fun z : Point => z i) hline
      simp [radialStemPoint, Lollipop.anchor,
        M.radial_eq_radius_smul_unitRadial] at hi ⊢
      dsimp [t]
      nlinarith
    have hsqL : (p - s) ^ 2 ≤ normSqPoint (L.anchor - M.center) := by
      rw [hvecL]
      exact sq_sub_le_normSqPoint_neg_smul_add_smul
        (normSqPoint_unitRadial L) (normSqPoint_unitRadial M) hs.le hp0
    have hsqM : (q - t) ^ 2 ≤ normSqPoint (M.anchor - L.center) := by
      rw [hvecM]
      exact sq_sub_le_normSqPoint_neg_smul_add_smul
        (normSqPoint_unitRadial M) (normSqPoint_unitRadial L) ht.le hq0
    have hts : t < s := by
      have hps : p - s < M.radius := by
        by_contra hnot
        have hge : M.radius ≤ p - s := le_of_not_gt hnot
        have hsq : M.radius ^ 2 ≤ (p - s) ^ 2 := by
          nlinarith [M.radius_pos]
        nlinarith [hsqL, hinsideL, hsq]
      dsimp [t]
      linarith
    have hst : s < t := by
      have hqt : q - t < L.radius := by
        by_contra hnot
        have hge : L.radius ≤ q - t := le_of_not_gt hnot
        have hsq : L.radius ^ 2 ≤ (q - t) ^ 2 := by
          nlinarith [L.radius_pos]
        nlinarith [hsqM, hinsideM, hsq]
      dsimp [s]
      linarith
    exact False.elim ((not_lt_of_ge hts.le) hst)
  · intro hx
    simp at hx

/-- If two concrete lollipop circles meet, the distance between their centers
is at most the sum of their radii. -/
theorem dist_center_le_radius_add_of_cc_nonempty
    {L M : Lollipop} (hcc : (cc L M).Nonempty) :
    dist L.center M.center ≤ L.radius + M.radius := by
  rcases hcc with ⟨p, hpL, hpM⟩
  have hpLdist : dist L.center p = L.radius := by
    rw [dist_comm]
    simpa [cc, Lollipop.circle, dist_eq_norm] using hpL
  have hpMdist : dist p M.center = M.radius := by
    simpa [cc, Lollipop.circle, dist_eq_norm] using hpM
  have htri :
      dist L.center M.center ≤ dist L.center p + dist p M.center :=
    dist_triangle L.center p M.center
  nlinarith

/-- Squared-coordinate form of
`dist_center_le_radius_add_of_cc_nonempty`. -/
theorem distSq2_center_le_radius_add_sq_of_cc_nonempty
    {L M : Lollipop} (hcc : (cc L M).Nonempty) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
      (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
        (L.radius + M.radius) ^ 2 := by
  rw [distSq2_ofPoint_eq_dist_sq]
  have hdist := dist_center_le_radius_add_of_cc_nonempty hcc
  exact (sq_le_sq₀ dist_nonneg
    (add_nonneg L.radius_pos.le M.radius_pos.le)).2 hdist

/-- A non-intriguing concrete pair satisfies Paulsen's strict lower
distance inequality for the uninflated circles. -/
theorem radius_sq_add_lt_distSq2_of_not_intriguing
    {L M : Lollipop} (hnot : ¬ Intriguing L M) :
    L.radius ^ 2 + M.radius ^ 2 <
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) := by
  unfold Intriguing at hnot
  push Not at hnot
  exact hnot.2

/-- A non-intriguing concrete pair satisfies Paulsen's strict upper distance
inequality after any positive uniform radius inflation. -/
theorem distSq2_lt_inflated_radius_add_sq_of_not_intriguing
    {L M : Lollipop} {ε : ℝ} (hε : 0 < ε) (hnot : ¬ Intriguing L M) :
    TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
      (R2.ofPoint L.center) (R2.ofPoint M.center) <
        (L.radius + ε + (M.radius + ε)) ^ 2 := by
  have hnot' := hnot
  unfold Intriguing at hnot'
  push Not at hnot'
  have hle := distSq2_center_le_radius_add_sq_of_cc_nonempty hnot'.1
  refine hle.trans_lt ?_
  have hleft_nonneg : 0 ≤ L.radius + M.radius :=
    add_nonneg L.radius_pos.le M.radius_pos.le
  have hright_nonneg : 0 ≤ L.radius + ε + (M.radius + ε) := by
    nlinarith [L.radius_pos, M.radius_pos, hε]
  have hlt :
      L.radius + M.radius < L.radius + ε + (M.radius + ε) := by
    nlinarith
  exact (sq_lt_sq₀ hleft_nonneg hright_nonneg).2 hlt

/-- If `ε` is smaller than the normalized lower-distance gap, then inflating
both radii by `ε` preserves Paulsen's strict lower distance inequality. -/
theorem inflated_radius_sq_add_lt_distSq2_of_epsilon_lt
    {L M : Lollipop} {ε : ℝ}
    (hεpos : 0 < ε) (hεlt1 : ε < 1)
    (hεsmall :
      ε <
        (TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
            (R2.ofPoint L.center) (R2.ofPoint M.center) -
          (L.radius ^ 2 + M.radius ^ 2)) /
          (4 * (L.radius + M.radius + 1)))
    (hnot : ¬ Intriguing L M) :
    (L.radius + ε) ^ 2 + (M.radius + ε) ^ 2 <
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) := by
  set d2 := TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
    (R2.ofPoint L.center) (R2.ofPoint M.center)
  set gap := d2 - (L.radius ^ 2 + M.radius ^ 2)
  have hgap_pos : 0 < gap := by
    have hlow := radius_sq_add_lt_distSq2_of_not_intriguing hnot
    dsimp [gap, d2]
    linarith
  have hden_pos : 0 < 4 * (L.radius + M.radius + 1) := by
    nlinarith [L.radius_pos, M.radius_pos]
  have hmul :
      ε * (4 * (L.radius + M.radius + 1)) < gap := by
    have := (lt_div_iff₀ hden_pos).1 hεsmall
    simpa [gap, d2, mul_comm, mul_left_comm, mul_assoc] using this
  have hεsq_le : ε ^ 2 ≤ ε := by
    nlinarith [sq_nonneg (ε - 1), hεpos, hεlt1]
  have hextra :
      2 * ε * (L.radius + M.radius) + 2 * ε ^ 2 < gap := by
    nlinarith [hmul, hεsq_le, L.radius_pos, M.radius_pos, hεpos]
  dsimp [gap, d2] at hgap_pos hextra ⊢
  nlinarith

private theorem exists_pos_lt_one_lt_all_finset
    {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ i ∈ s, ε < f i := by
  classical
  induction s using Finset.induction with
  | empty =>
      refine ⟨(1 : ℝ) / 2, by norm_num, by norm_num, ?_⟩
      simp
  | insert a s ha ih =>
      have hfs : ∀ i ∈ s, 0 < f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rcases ih hfs with ⟨δ, hδpos, hδlt1, hδall⟩
      let ε : ℝ := min δ (f a) / 2
      have hfa : 0 < f a := hf a (Finset.mem_insert_self a s)
      have hmin_pos : 0 < min δ (f a) := lt_min hδpos hfa
      have hhalf_lt_min : min δ (f a) / 2 < min δ (f a) := by
        nlinarith
      refine ⟨ε, ?_, ?_, ?_⟩
      · dsimp [ε]
        nlinarith
      · dsimp [ε]
        have hmin_le_delta : min δ (f a) ≤ δ := min_le_left δ (f a)
        exact (hhalf_lt_min.trans_le hmin_le_delta).trans hδlt1
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with hi_eq | hi
        · dsimp [ε]
          have hmin_le_fi : min δ (f a) ≤ f i := by
            rw [hi_eq]
            exact min_le_right δ (f a)
          exact hhalf_lt_min.trans_le hmin_le_fi
        · dsimp [ε]
          have hmin_le_delta : min δ (f a) ≤ δ := min_le_left δ (f a)
          exact (hhalf_lt_min.trans_le hmin_le_delta).trans (hδall i hi)

set_option maxHeartbeats 4000000

/-- Every five concrete lollipops contain a pair satisfying the manuscript's
strict concrete `Intriguing` relation. -/
theorem intriguing_pair_in_every_five
    {n : ℕ} (A : Arrangement n) :
    ∀ t : Finset (Fin n), t.card = 5 →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ Intriguing (A i) (A j) := by
  classical
  intro t ht
  by_contra hnone
  let e : Fin 5 ≃ {x : Fin n // x ∈ t} := (t.equivFinOfCardEq ht).symm
  have hnot_intr :
      ∀ i j : Fin 5, i ≠ j → ¬ Intriguing (A (e i)) (A (e j)) := by
    intro i j hij hintr
    refine hnone ?_
    refine ⟨(e i : Fin n), (e i).property, (e j : Fin n), (e j).property, ?_, hintr⟩
    intro hval
    exact hij (e.injective (Subtype.ext hval))
  let distinctPairs : Finset (Fin 5 × Fin 5) :=
    Finset.univ.filter fun p : Fin 5 × Fin 5 => p.1 ≠ p.2
  let center : Fin 5 → TheoremOneEndToEnd.PaulsenLinearAlgebra.R2 :=
    fun i => centerR2 A (e i)
  let baseRadius : Fin 5 → ℝ := fun i => (A (e i)).radius
  let gapBound : Fin 5 × Fin 5 → ℝ := fun p =>
    (TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (center p.1) (center p.2) -
      (baseRadius p.1 ^ 2 + baseRadius p.2 ^ 2)) /
      (4 * (baseRadius p.1 + baseRadius p.2 + 1))
  have hgapBound_pos : ∀ p ∈ distinctPairs, 0 < gapBound p := by
    intro p hp
    have hp_ne : p.1 ≠ p.2 := by
      simpa [distinctPairs] using hp
    have hlow :=
      radius_sq_add_lt_distSq2_of_not_intriguing
        (L := A (e p.1)) (M := A (e p.2)) (hnot_intr p.1 p.2 hp_ne)
    have hnum :
        0 <
          TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
            (center p.1) (center p.2) -
          (baseRadius p.1 ^ 2 + baseRadius p.2 ^ 2) := by
      dsimp [center, baseRadius] at hlow ⊢
      simpa [centerR2] using sub_pos.mpr hlow
    have hden :
        0 < 4 * (baseRadius p.1 + baseRadius p.2 + 1) := by
      dsimp [baseRadius]
      nlinarith [(A (e p.1)).radius_pos, (A (e p.2)).radius_pos]
    exact div_pos hnum hden
  let epsSpec :=
    exists_pos_lt_one_lt_all_finset distinctPairs gapBound hgapBound_pos
  let ε : ℝ := Classical.choose epsSpec
  have hεpos : 0 < ε := (Classical.choose_spec epsSpec).1
  have hεlt1 : ε < 1 := (Classical.choose_spec epsSpec).2.1
  have hεsmall : ∀ p ∈ distinctPairs, ε < gapBound p :=
    (Classical.choose_spec epsSpec).2.2
  let radius : Fin 5 → ℝ := fun i => baseRadius i + ε
  let vec : Fin 5 → TheoremOneEndToEnd.PaulsenLinearAlgebra.R4 :=
    fun i => TheoremOneEndToEnd.PaulsenLinearAlgebra.circleVec
      (radius i) (center i)
  have hradius_pos : ∀ i : Fin 5, 0 < radius i := by
    intro i
    dsimp [radius, baseRadius]
    nlinarith [(A (e i)).radius_pos, hεpos]
  have hfirst : ∀ i : Fin 5, 0 < vec i 0 := by
    intro i
    exact TheoremOneEndToEnd.PaulsenLinearAlgebra.circleVec_first_pos
      (hradius_pos i) (center i)
  have hself :
      ∀ i : Fin 5,
        TheoremOneEndToEnd.PaulsenLinearAlgebra.lorentzForm
          (vec i) (vec i) = 1 := by
    intro i
    exact TheoremOneEndToEnd.PaulsenLinearAlgebra.lorentzForm_circleVec_self
      (center i) (ne_of_gt (hradius_pos i))
  have hdist_low :
      ∀ i j : Fin 5, i ≠ j →
        radius i ^ 2 + radius j ^ 2 <
          TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
            (center i) (center j) := by
    intro i j hij
    have hp_mem : (i, j) ∈ distinctPairs := by
      simp [distinctPairs, hij]
    have hsmall := hεsmall (i, j) hp_mem
    have hlow :=
      inflated_radius_sq_add_lt_distSq2_of_epsilon_lt
        (L := A (e i)) (M := A (e j))
        hεpos hεlt1
        (by simpa [gapBound, center, baseRadius, centerR2] using hsmall)
        (hnot_intr i j hij)
    simpa [radius, baseRadius, center, centerR2] using hlow
  have hdist_high :
      ∀ i j : Fin 5, i ≠ j →
        TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
          (center i) (center j) <
            (radius i + radius j) ^ 2 := by
    intro i j hij
    have hhigh :=
      distSq2_lt_inflated_radius_add_sq_of_not_intriguing
        (L := A (e i)) (M := A (e j)) hεpos (hnot_intr i j hij)
    simpa [radius, baseRadius, center, centerR2] using hhigh
  have hneg :
      ∀ i j : Fin 5, i ≠ j →
        TheoremOneEndToEnd.PaulsenLinearAlgebra.lorentzForm
          (vec i) (vec j) < 0 := by
    intro i j hij
    exact TheoremOneEndToEnd.PaulsenLinearAlgebra.lorentzForm_circleVec_pair_neg
      (center i) (center j) (hradius_pos i) (hradius_pos j)
      (hdist_low i j hij)
  have hgt :
      ∀ i j : Fin 5, i ≠ j →
        -1 <
          TheoremOneEndToEnd.PaulsenLinearAlgebra.lorentzForm
            (vec i) (vec j) := by
    intro i j hij
    exact TheoremOneEndToEnd.PaulsenLinearAlgebra.lorentzForm_circleVec_pair_gt_neg_one
      (center i) (center j) (hradius_pos i) (hradius_pos j)
      (hdist_high i j hij)
  exact TheoremOneEndToEnd.PaulsenLinearAlgebra.no_paulsen_gram_five
    vec hfirst hself hneg hgt

private theorem finite_components_hatPiece_cc (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (cc L M))) := by
  unfold hatPiece
  by_cases hsame : L.circle = M.circle
  · have hconn : IsConnected (finiteLift (cc L M)) := by
      simpa [cc, hsame, finiteLift] using
        L.isConnected_circle.image finitePoint OnePoint.continuous_coe.continuousOn
    exact finite_connectedComponents_union_singleton_of_connected hconn
  · exact finite_connectedComponents_finiteLift_union_infinity
      (finite_circle_intersection_of_ne hsame)

private theorem finite_components_hatPiece_rc (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (rc L M))) := by
  unfold hatPiece
  exact finite_connectedComponents_finiteLift_union_infinity
    (finite_ray_circle_intersection L M)

private theorem finite_components_hatPiece_cr (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (cr L M))) := by
  unfold hatPiece
  exact finite_connectedComponents_finiteLift_union_infinity
    (finite_circle_ray_intersection L M)

private theorem finite_components_hatPiece_rr (L M : Lollipop) :
    Finite (ConnectedComponents (hatPiece (rr L M))) := by
  unfold hatPiece
  have hconv : Convex ℝ (rr L M) := (stem_convex L).inter (stem_convex M)
  by_cases hne : (rr L M).Nonempty
  · have hconn : IsConnected (finiteLift (rr L M)) :=
      (hconv.isConnected hne).image finitePoint
        OnePoint.continuous_coe.continuousOn
    exact finite_connectedComponents_union_singleton_of_connected hconn
  · have hempty : rr L M = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    exact finite_connectedComponents_finiteLift_union_infinity finite_empty

private theorem finite_components_pairPiece (L M : Lollipop) (k : Fin 4) :
    Finite (ConnectedComponents (pairPiece L M k)) := by
  fin_cases k
  · change Finite (ConnectedComponents (hatPiece (cc L M)))
    exact finite_components_hatPiece_cc L M
  · change Finite (ConnectedComponents (hatPiece (rc L M)))
    exact finite_components_hatPiece_rc L M
  · change Finite (ConnectedComponents (hatPiece (cr L M)))
    exact finite_components_hatPiece_cr L M
  · change Finite (ConnectedComponents (hatPiece (rr L M)))
    exact finite_components_hatPiece_rr L M

/-- The compactified intersection of two concrete lollipop carriers has
finitely many connected components, including degenerate coincident and
overlapping cases. -/
theorem finite_connectedComponents_hatPairIntersection (L M : Lollipop) :
    Finite (ConnectedComponents (hatPairIntersection L M)) := by
  rw [hatPairIntersection_eq_iUnion_pairPiece]
  haveI (k : Fin 4) : Finite (ConnectedComponents (pairPiece L M k)) :=
    finite_components_pairPiece L M k
  exact finite_connectedComponents_iUnion

/-- Bound the whole compactified pair intersection from independent bounds on
the four primitive compactified pieces. -/
private theorem pairExcessNat_le_of_hatPiece_bounds
    (L M : Lollipop) {bCC bRC bCR bRR : ℕ}
    (hcc : componentCount (hatPiece (cc L M)) - 1 ≤ bCC)
    (hrc : componentCount (hatPiece (rc L M)) - 1 ≤ bRC)
    (hcr : componentCount (hatPiece (cr L M)) - 1 ≤ bCR)
    (hrr : componentCount (hatPiece (rr L M)) - 1 ≤ bRR) :
    pairExcessNat L M ≤ bCC + bRC + bCR + bRR := by
  let S : Fin 4 → Set Sphere2 := pairPiece L M
  haveI (k : Fin 4) : Finite (ConnectedComponents (S k)) :=
    finite_components_pairPiece L M k
  have hcommon : ∀ k : Fin 4, infinity ∈ S k := by
    intro k
    fin_cases k <;> simp [S, pairPiece]
  have hunion :
      componentCount (⋃ k : Fin 4, S k) - 1 ≤
        ∑ k : Fin 4, (componentCount (S k) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one infinity hcommon
  unfold pairExcessNat
  rw [hatPairIntersection_eq_iUnion_pairPiece]
  refine hunion.trans ?_
  rw [Fin.sum_univ_four]
  change
    (componentCount (hatPiece (cc L M)) - 1) +
      (componentCount (hatPiece (rc L M)) - 1) +
      (componentCount (hatPiece (cr L M)) - 1) +
      (componentCount (hatPiece (rr L M)) - 1) ≤
        bCC + bRC + bCR + bRR
  omega

/-- An empty primitive piece contributes zero after compactification and
subtracting the common infinity component. -/
theorem componentCount_hatPiece_sub_one_eq_zero_of_empty
    {S : Set Point} (h_empty : ¬ S.Nonempty) :
    componentCount (hatPiece S) - 1 = 0 := by
  have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
  rw [hempty]
  unfold hatPiece
  rw [componentCount_finiteLift_union_infinity_sub_one finite_empty]
  simp

/-- If the circle-circle primitive is empty, its compactified contribution is
zero after subtracting the common infinity component. -/
theorem componentCount_hatPiece_cc_sub_one_eq_zero_of_empty
    {L M : Lollipop} (hcc_empty : ¬ (cc L M).Nonempty) :
    componentCount (hatPiece (cc L M)) - 1 = 0 := by
  exact componentCount_hatPiece_sub_one_eq_zero_of_empty hcc_empty

theorem componentCount_hatPiece_rc_sub_one_eq_zero_of_empty
    {L M : Lollipop} (hrc_empty : ¬ (rc L M).Nonempty) :
    componentCount (hatPiece (rc L M)) - 1 = 0 := by
  exact componentCount_hatPiece_sub_one_eq_zero_of_empty hrc_empty

theorem componentCount_hatPiece_cr_sub_one_eq_zero_of_empty
    {L M : Lollipop} (hcr_empty : ¬ (cr L M).Nonempty) :
    componentCount (hatPiece (cr L M)) - 1 = 0 := by
  exact componentCount_hatPiece_sub_one_eq_zero_of_empty hcr_empty

theorem componentCount_hatPiece_rr_sub_one_eq_zero_of_empty
    {L M : Lollipop} (hrr_empty : ¬ (rr L M).Nonempty) :
    componentCount (hatPiece (rr L M)) - 1 = 0 := by
  exact componentCount_hatPiece_sub_one_eq_zero_of_empty hrr_empty

/-- If the two circles do not meet, the pair loses the two possible
circle-circle components, so the universal `2+2+2+1` bound improves to
`0+2+2+1`. -/
theorem pairExcessNat_le_five_of_cc_empty
    {L M : Lollipop} (hcc_empty : ¬ (cc L M).Nonempty) :
    pairExcessNat L M ≤ 5 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cc_sub_one_eq_zero_of_empty hcc_empty]
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.ray_circle_components_le_two L M
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_ray_components_le_two L M
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty left-ray/right-circle primitive gives a `2+0+2+1` saving. -/
theorem pairExcessNat_le_five_of_rc_empty
    {L M : Lollipop} (hrc_empty : ¬ (rc L M).Nonempty) :
    pairExcessNat L M ≤ 5 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rc_sub_one_eq_zero_of_empty hrc_empty]
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_ray_components_le_two L M
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty left-circle/right-ray primitive gives a `2+2+0+1` saving. -/
theorem pairExcessNat_le_five_of_cr_empty
    {L M : Lollipop} (hcr_empty : ¬ (cr L M).Nonempty) :
    pairExcessNat L M ≤ 5 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.ray_circle_components_le_two L M
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cr_sub_one_eq_zero_of_empty hcr_empty]
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty circle-circle and ray-ray primitives give a `0+2+2+0` saving. -/
theorem pairExcessNat_le_four_of_cc_empty_rr_empty
    {L M : Lollipop}
    (hcc_empty : ¬ (cc L M).Nonempty)
    (hrr_empty : ¬ (rr L M).Nonempty) :
    pairExcessNat L M ≤ 4 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cc_sub_one_eq_zero_of_empty hcc_empty]
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.ray_circle_components_le_two L M
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_ray_components_le_two L M
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rr_sub_one_eq_zero_of_empty hrr_empty]
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty circle-circle and left-ray/right-circle primitives give a
`0+0+2+1` saving. -/
theorem pairExcessNat_le_three_of_cc_empty_rc_empty
    {L M : Lollipop}
    (hcc_empty : ¬ (cc L M).Nonempty)
    (hrc_empty : ¬ (rc L M).Nonempty) :
    pairExcessNat L M ≤ 3 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cc_sub_one_eq_zero_of_empty hcc_empty]
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rc_sub_one_eq_zero_of_empty hrc_empty]
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_ray_components_le_two L M
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty circle-circle and left-circle/right-ray primitives give a
`0+2+0+1` saving. -/
theorem pairExcessNat_le_three_of_cc_empty_cr_empty
    {L M : Lollipop}
    (hcc_empty : ¬ (cc L M).Nonempty)
    (hcr_empty : ¬ (cr L M).Nonempty) :
    pairExcessNat L M ≤ 3 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cc_sub_one_eq_zero_of_empty hcc_empty]
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.ray_circle_components_le_two L M
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cr_sub_one_eq_zero_of_empty hcr_empty]
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty mixed primitives give a `2+0+0+1` saving. -/
theorem pairExcessNat_le_three_of_rc_empty_cr_empty
    {L M : Lollipop}
    (hrc_empty : ¬ (rc L M).Nonempty)
    (hcr_empty : ¬ (cr L M).Nonempty) :
    pairExcessNat L M ≤ 3 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rc_sub_one_eq_zero_of_empty hrc_empty]
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cr_sub_one_eq_zero_of_empty hcr_empty]
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty left-ray/right-circle and ray-ray primitives give a `2+0+2+0`
saving. -/
theorem pairExcessNat_le_four_of_rc_empty_rr_empty
    {L M : Lollipop}
    (hrc_empty : ¬ (rc L M).Nonempty)
    (hrr_empty : ¬ (rr L M).Nonempty) :
    pairExcessNat L M ≤ 4 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rc_sub_one_eq_zero_of_empty hrc_empty]
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_ray_components_le_two L M
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rr_sub_one_eq_zero_of_empty hrr_empty]
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Empty left-circle/right-ray and ray-ray primitives give a `2+2+0+0`
saving. -/
theorem pairExcessNat_le_four_of_cr_empty_rr_empty
    {L M : Lollipop}
    (hcr_empty : ¬ (cr L M).Nonempty)
    (hrr_empty : ¬ (rr L M).Nonempty) :
    pairExcessNat L M ≤ 4 := by
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.ray_circle_components_le_two L M
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cr_sub_one_eq_zero_of_empty hcr_empty]
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_rr_sub_one_eq_zero_of_empty hrr_empty]
  have h := pairExcessNat_le_of_hatPiece_bounds L M
    hccHat hrcHat hcrHat hrrHat
  omega

/-- Universal `2+2+2+1` pair bound at the natural-number level. -/
theorem pairExcessNat_le_seven (L M : Lollipop) :
    pairExcessNat L M ≤ 7 := by
  let S : Fin 4 → Set Sphere2 := pairPiece L M
  haveI (k : Fin 4) : Finite (ConnectedComponents (S k)) :=
    finite_components_pairPiece L M k
  have hcommon : ∀ k : Fin 4, infinity ∈ S k := by
    intro k
    fin_cases k <;> simp [S, pairPiece]
  have hunion :
      componentCount (⋃ k : Fin 4, S k) - 1 ≤
        ∑ k : Fin 4, (componentCount (S k) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one infinity hcommon
  have hcc := EuclideanPort.circle_circle_components_le_two L M
  have hrc := EuclideanPort.ray_circle_components_le_two L M
  have hcr := EuclideanPort.circle_ray_components_le_two L M
  have hrr := EuclideanPort.ray_ray_components_le_one L M
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using hcc
  have hrcHat : componentCount (hatPiece (rc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using hrc
  have hcrHat : componentCount (hatPiece (cr L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using hcr
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using hrr
  unfold pairExcessNat
  rw [hatPairIntersection_eq_iUnion_pairPiece]
  refine hunion.trans ?_
  rw [Fin.sum_univ_four]
  change
    (componentCount (hatPiece (cc L M)) - 1) +
      (componentCount (hatPiece (rc L M)) - 1) +
      (componentCount (hatPiece (cr L M)) - 1) +
      (componentCount (hatPiece (rr L M)) - 1) ≤ 7
  omega

/-- Close-pair saving proved from the concrete mixed-intersection geometry. -/
theorem pairExcessNat_le_five_of_close
    {L M : Lollipop} (hclose : Close L M) :
    pairExcessNat L M ≤ 5 := by
  let S : Fin 3 → Set Sphere2 := closePairPiece L M
  haveI (k : Fin 3) : Finite (ConnectedComponents (S k)) := by
    fin_cases k
    · change Finite (ConnectedComponents (hatPiece (cc L M)))
      exact finite_components_hatPiece_cc L M
    · change Finite (ConnectedComponents (hatPiece (cr L M ∪ rc L M)))
      exact finite_connectedComponents_finiteLift_union_infinity
        ((finite_circle_ray_intersection L M).union
          (finite_ray_circle_intersection L M))
    · change Finite (ConnectedComponents (hatPiece (rr L M)))
      exact finite_components_hatPiece_rr L M
  have hcommon : ∀ k : Fin 3, infinity ∈ S k := by
    intro k
    fin_cases k <;> simp [S, closePairPiece]
  have hunion :
      componentCount (⋃ k : Fin 3, S k) - 1 ≤
        ∑ k : Fin 3, (componentCount (S k) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one infinity hcommon
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hmixHat :
      componentCount (hatPiece (cr L M ∪ rc L M)) - 1 ≤ 2 :=
    componentCount_hatPiece_mixed_sub_one_le_two hclose
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  unfold pairExcessNat
  rw [hatPairIntersection_eq_iUnion_closePairPiece]
  refine hunion.trans ?_
  rw [Fin.sum_univ_three]
  change
    (componentCount (hatPiece (cc L M)) - 1) +
      (componentCount (hatPiece (cr L M ∪ rc L M)) - 1) +
      (componentCount (hatPiece (rr L M)) - 1) ≤ 5
  omega

/-- Near-circle intriguing branch proved from the outside-mixed component
collapse. -/
theorem pairExcessNat_le_four_of_intriguing_near
    {L M : Lollipop}
    (hnear :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
          L.radius ^ 2 + M.radius ^ 2) :
    pairExcessNat L M ≤ 4 := by
  have hnearNorm :
      normSqPoint (M.center - L.center) ≤
        L.radius ^ 2 + M.radius ^ 2 := by
    simpa [centerDistSq_eq_normSqPoint] using hnear
  let S : Fin 4 → Set Sphere2 := intriguingPairPiece L M
  have hcrFin : (cr L M \ cc L M).Finite :=
    (finite_circle_ray_intersection L M).diff
  have hrcFin : (rc L M \ cc L M).Finite :=
    (finite_ray_circle_intersection L M).diff
  haveI (k : Fin 4) : Finite (ConnectedComponents (S k)) := by
    fin_cases k
    · change Finite (ConnectedComponents (hatPiece (cc L M)))
      exact finite_components_hatPiece_cc L M
    · change Finite (ConnectedComponents (hatPiece (cr L M \ cc L M)))
      exact finite_connectedComponents_finiteLift_union_infinity hcrFin
    · change Finite (ConnectedComponents (hatPiece (rc L M \ cc L M)))
      exact finite_connectedComponents_finiteLift_union_infinity hrcFin
    · change Finite (ConnectedComponents (hatPiece (rr L M)))
      exact finite_components_hatPiece_rr L M
  have hcommon : ∀ k : Fin 4, infinity ∈ S k := by
    intro k
    fin_cases k <;> simp [S, intriguingPairPiece]
  have hunion :
      componentCount (⋃ k : Fin 4, S k) - 1 ≤
        ∑ k : Fin 4, (componentCount (S k) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one infinity hcommon
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 2 := by
    simpa [hatPiece] using EuclideanPort.circle_circle_components_le_two L M
  have hcrHat :
      componentCount (hatPiece (cr L M \ cc L M)) - 1 ≤ 1 := by
    rw [componentCount_hatPiece_sub_one_eq_ncard_of_finite hcrFin]
    exact cr_diff_cc_ncard_le_one_of_near hnearNorm
  have hrcHat :
      componentCount (hatPiece (rc L M \ cc L M)) - 1 ≤ 1 := by
    rw [componentCount_hatPiece_sub_one_eq_ncard_of_finite hrcFin]
    exact rc_diff_cc_ncard_le_one_of_near hnearNorm
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  have hsum :
      ∑ k : Fin 4, (componentCount (S k) - 1) ≤ 4 := by
    rw [Fin.sum_univ_four]
    change
      (componentCount (hatPiece (cc L M)) - 1) +
        (componentCount (hatPiece (cr L M \ cc L M)) - 1) +
        (componentCount (hatPiece (rc L M \ cc L M)) - 1) +
        (componentCount (hatPiece (rr L M)) - 1) ≤ 4
    by_cases hboth :
        (cr L M \ cc L M).Nonempty ∧
          (rc L M \ cc L M).Nonempty
    · have hrr_empty : ¬ (rr L M).Nonempty := by
        rw [rr_eq_empty_of_both_outside_mixed_of_near
          hnearNorm hboth.2 hboth.1]
        simp
      have hrrZero : componentCount (hatPiece (rr L M)) - 1 ≤ 0 := by
        rw [componentCount_hatPiece_rr_sub_one_eq_zero_of_empty hrr_empty]
      omega
    · have hmixed :
        (componentCount (hatPiece (cr L M \ cc L M)) - 1) +
          (componentCount (hatPiece (rc L M \ cc L M)) - 1) ≤ 1 := by
        by_cases hcr : (cr L M \ cc L M).Nonempty
        · have hrc : ¬ (rc L M \ cc L M).Nonempty := by
            intro hrc
            exact hboth ⟨hcr, hrc⟩
          have hrcZero :
              componentCount (hatPiece (rc L M \ cc L M)) - 1 = 0 :=
            componentCount_hatPiece_sub_one_eq_zero_of_empty hrc
          rw [hrcZero]
          omega
        · have hcrZero :
              componentCount (hatPiece (cr L M \ cc L M)) - 1 = 0 :=
            componentCount_hatPiece_sub_one_eq_zero_of_empty hcr
          rw [hcrZero]
          omega
      omega
  unfold pairExcessNat
  rw [hatPairIntersection_eq_iUnion_intriguingPairPiece]
  exact hunion.trans hsum

/-- Weaker natural-number wrapper for callers that only need the ordinary
intriguing-pair bound. -/
theorem pairExcessNat_le_five_of_intriguing_near
    {L M : Lollipop}
    (hnear :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
          L.radius ^ 2 + M.radius ^ 2) :
    pairExcessNat L M ≤ 5 := by
  exact (pairExcessNat_le_four_of_intriguing_near hnear).trans (by norm_num)

/-- Circle-disjoint close pairs satisfy the combined saving. -/
theorem pairExcessNat_le_four_of_close_cc_empty
    {L M : Lollipop} (hclose : Close L M)
    (hcc_empty : ¬ (cc L M).Nonempty) :
    pairExcessNat L M ≤ 4 := by
  let S : Fin 3 → Set Sphere2 := closePairPiece L M
  haveI (k : Fin 3) : Finite (ConnectedComponents (S k)) := by
    fin_cases k
    · change Finite (ConnectedComponents (hatPiece (cc L M)))
      exact finite_components_hatPiece_cc L M
    · change Finite (ConnectedComponents (hatPiece (cr L M ∪ rc L M)))
      exact finite_connectedComponents_finiteLift_union_infinity
        ((finite_circle_ray_intersection L M).union
          (finite_ray_circle_intersection L M))
    · change Finite (ConnectedComponents (hatPiece (rr L M)))
      exact finite_components_hatPiece_rr L M
  have hcommon : ∀ k : Fin 3, infinity ∈ S k := by
    intro k
    fin_cases k <;> simp [S, closePairPiece]
  have hunion :
      componentCount (⋃ k : Fin 3, S k) - 1 ≤
        ∑ k : Fin 3, (componentCount (S k) - 1) :=
    componentCount_iUnion_sub_one_le_sum_sub_one infinity hcommon
  have hccHat : componentCount (hatPiece (cc L M)) - 1 ≤ 0 := by
    rw [componentCount_hatPiece_cc_sub_one_eq_zero_of_empty hcc_empty]
  have hmixHat :
      componentCount (hatPiece (cr L M ∪ rc L M)) - 1 ≤ 2 :=
    componentCount_hatPiece_mixed_sub_one_le_two hclose
  have hrrHat : componentCount (hatPiece (rr L M)) - 1 ≤ 1 := by
    simpa [hatPiece] using EuclideanPort.ray_ray_components_le_one L M
  unfold pairExcessNat
  rw [hatPairIntersection_eq_iUnion_closePairPiece]
  refine hunion.trans ?_
  rw [Fin.sum_univ_three]
  change
    (componentCount (hatPiece (cc L M)) - 1) +
      (componentCount (hatPiece (cr L M ∪ rc L M)) - 1) +
      (componentCount (hatPiece (rr L M)) - 1) ≤ 4
  omega

/-- Universal `2+2+2+1` pair bound. -/
theorem pairExcess_le_seven (L M : Lollipop) : pairExcess L M ≤ 7 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_seven L M

/-- Circle-disjoint intriguing branch. -/
theorem pairExcess_le_five_of_cc_empty
    {L M : Lollipop} (hcc_empty : ¬ (cc L M).Nonempty) :
    pairExcess L M ≤ 5 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_five_of_cc_empty hcc_empty

/-- Rational wrapper for the empty left-ray/right-circle primitive saving. -/
theorem pairExcess_le_five_of_rc_empty
    {L M : Lollipop} (hrc_empty : ¬ (rc L M).Nonempty) :
    pairExcess L M ≤ 5 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_five_of_rc_empty hrc_empty

/-- Rational wrapper for the empty left-circle/right-ray primitive saving. -/
theorem pairExcess_le_five_of_cr_empty
    {L M : Lollipop} (hcr_empty : ¬ (cr L M).Nonempty) :
    pairExcess L M ≤ 5 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_five_of_cr_empty hcr_empty

/-- Rational wrapper for the empty circle-circle and ray-ray saving. -/
theorem pairExcess_le_four_of_cc_empty_rr_empty
    {L M : Lollipop}
    (hcc_empty : ¬ (cc L M).Nonempty)
    (hrr_empty : ¬ (rr L M).Nonempty) :
    pairExcess L M ≤ 4 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_four_of_cc_empty_rr_empty
    hcc_empty hrr_empty

/-- Rational wrapper for the empty circle-circle and left-ray/right-circle
saving. -/
theorem pairExcess_le_three_of_cc_empty_rc_empty
    {L M : Lollipop}
    (hcc_empty : ¬ (cc L M).Nonempty)
    (hrc_empty : ¬ (rc L M).Nonempty) :
    pairExcess L M ≤ 3 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_three_of_cc_empty_rc_empty
    hcc_empty hrc_empty

/-- Rational wrapper for the empty circle-circle and left-circle/right-ray
saving. -/
theorem pairExcess_le_three_of_cc_empty_cr_empty
    {L M : Lollipop}
    (hcc_empty : ¬ (cc L M).Nonempty)
    (hcr_empty : ¬ (cr L M).Nonempty) :
    pairExcess L M ≤ 3 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_three_of_cc_empty_cr_empty
    hcc_empty hcr_empty

/-- Rational wrapper for the empty mixed-primitives saving. -/
theorem pairExcess_le_three_of_rc_empty_cr_empty
    {L M : Lollipop}
    (hrc_empty : ¬ (rc L M).Nonempty)
    (hcr_empty : ¬ (cr L M).Nonempty) :
    pairExcess L M ≤ 3 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_three_of_rc_empty_cr_empty
    hrc_empty hcr_empty

/-- Rational wrapper for the empty left-ray/right-circle and ray-ray saving. -/
theorem pairExcess_le_four_of_rc_empty_rr_empty
    {L M : Lollipop}
    (hrc_empty : ¬ (rc L M).Nonempty)
    (hrr_empty : ¬ (rr L M).Nonempty) :
    pairExcess L M ≤ 4 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_four_of_rc_empty_rr_empty
    hrc_empty hrr_empty

/-- Rational wrapper for the empty left-circle/right-ray and ray-ray saving. -/
theorem pairExcess_le_four_of_cr_empty_rr_empty
    {L M : Lollipop}
    (hcr_empty : ¬ (cr L M).Nonempty)
    (hrr_empty : ¬ (rr L M).Nonempty) :
    pairExcess L M ≤ 4 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_four_of_cr_empty_rr_empty
    hcr_empty hrr_empty

/-- Close-pair saving. -/
theorem pairExcess_le_five_of_close
    {L M : Lollipop} (hclose : Close L M) : pairExcess L M ≤ 5 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_five_of_close hclose

/-- Rational wrapper for the near-circle intriguing branch. -/
theorem pairExcess_le_five_of_intriguing_near
    {L M : Lollipop}
    (hnear :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
          L.radius ^ 2 + M.radius ^ 2) :
    pairExcess L M ≤ 5 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_five_of_intriguing_near hnear

/-- Rational wrapper for the stronger near-circle intriguing branch. -/
theorem pairExcess_le_four_of_intriguing_near
    {L M : Lollipop}
    (hnear :
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
          L.radius ^ 2 + M.radius ^ 2) :
    pairExcess L M ≤ 4 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_four_of_intriguing_near hnear

/-- Intriguing-pair saving. -/
theorem pairExcess_le_five_of_intriguing
    {L M : Lollipop} (hintr : Intriguing L M) : pairExcess L M ≤ 5 := by
  rcases hintr with hdisj | hnear
  · exact pairExcess_le_five_of_cc_empty hdisj
  · exact pairExcess_le_five_of_intriguing_near hnear

/-- Rational wrapper for the circle-disjoint close branch. -/
theorem pairExcess_le_four_of_close_cc_empty
    {L M : Lollipop} (hclose : Close L M)
    (hcc_empty : ¬ (cc L M).Nonempty) : pairExcess L M ≤ 4 := by
  unfold pairExcess
  exact_mod_cast pairExcessNat_le_four_of_close_cc_empty hclose hcc_empty

/-- Combined close/intriguing saving. -/
theorem pairExcess_le_four_of_close_intriguing
    {L M : Lollipop} (hclose : Close L M) (hintr : Intriguing L M) :
    pairExcess L M ≤ 4 := by
  rcases hintr with hdisj | hnear
  · exact pairExcess_le_four_of_close_cc_empty hclose hdisj
  · exact pairExcess_le_four_of_intriguing_near hnear

end PairGeometry
end EndToEnd
end Concrete
end Lollipop
