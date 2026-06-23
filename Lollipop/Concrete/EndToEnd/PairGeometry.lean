import Lollipop.Concrete.EndToEnd.PlanarTopology
import Lollipop.Internal.ColoredTuran.PaulsenLinearAlgebra
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

/-- Remaining concrete pair-geometry theorem package.

These fields are the remaining robust pair-excess savings used by the colored
Turan backend.  They are stated for the concrete lollipop carrier/intersection
semantics, including degeneracies. -/
structure PairGeometryPorts : Prop where
  pairExcess_le_five_of_close :
    ∀ {L M : Lollipop}, Close L M → pairExcess L M ≤ 5
  pairExcess_le_five_of_intriguing_near :
    ∀ {L M : Lollipop},
      TheoremOneEndToEnd.PaulsenLinearAlgebra.distSq2
        (R2.ofPoint L.center) (R2.ofPoint M.center) ≤
          L.radius ^ 2 + M.radius ^ 2 →
        pairExcess L M ≤ 5
  pairExcess_le_four_of_close_intriguing :
    ∀ {L M : Lollipop}, Close L M → Intriguing L M →
      pairExcess L M ≤ 4

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
theorem pairExcess_le_five_of_close (ports : PairGeometryPorts)
    {L M : Lollipop} (hclose : Close L M) : pairExcess L M ≤ 5 :=
  ports.pairExcess_le_five_of_close hclose

/-- Intriguing-pair saving. -/
theorem pairExcess_le_five_of_intriguing (ports : PairGeometryPorts)
    {L M : Lollipop} (hintr : Intriguing L M) : pairExcess L M ≤ 5 := by
  rcases hintr with hdisj | hnear
  · exact pairExcess_le_five_of_cc_empty hdisj
  · exact ports.pairExcess_le_five_of_intriguing_near hnear

/-- Combined close/intriguing saving. -/
theorem pairExcess_le_four_of_close_intriguing (ports : PairGeometryPorts)
    {L M : Lollipop} (hclose : Close L M) (hintr : Intriguing L M) :
    pairExcess L M ≤ 4 :=
  ports.pairExcess_le_four_of_close_intriguing hclose hintr

end PairGeometry
end EndToEnd
end Concrete
end Lollipop
