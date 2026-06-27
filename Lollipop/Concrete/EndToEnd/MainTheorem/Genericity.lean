import Lollipop.Concrete.EndToEnd.Lower.Genericity
import Lollipop.Concrete.EndToEnd.TranslationGenericity

/-!
# Main theorem spine: lower genericity

This file states the concrete genericity-avoidance theorem needed by the final
certificate-free endpoint.

The theorem is not a caller-facing certificate.  It is the named target for
the finite bad-locus avoidance proof.
-/

noncomputable section

namespace Lollipop
namespace Concrete
namespace EndToEnd
namespace MainTheorem
namespace Genericity

/-- There are no three pairwise-distinct indices in `Fin n` when `n < 3`. -/
theorem no_three_distinct_fin_of_lt_three {n : ℕ} (hn : n < 3) :
    ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → False := by
  intro i j k hij hik hjk
  have hijv : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
  have hikv : i.1 ≠ k.1 := fun h => hik (Fin.ext h)
  have hjkv : j.1 ≠ k.1 := fun h => hjk (Fin.ext h)
  have hi3 : i.1 < 3 := lt_trans i.2 hn
  have hj3 : j.1 < 3 := lt_trans j.2 hn
  have hk3 : k.1 < 3 := lt_trans k.2 hn
  omega

/-- For `n < 3`, the triple-contact bad locus is empty and hence avoidable. -/
theorem dense_compl_tripleBadUnion_of_lt_three {n : ℕ} (hn : n < 3) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  rw [Lower.GenericityPort.tripleBadUnion_eq_empty_of_no_three_distinct
    (no_three_distinct_fin_of_lt_three hn)]
  simp

/-- Ordered triples of pairwise-distinct indices.  This packages the index
and proof arguments in `Lower.GenericityPort.tripleBadUnion` into one finite
type, so the remaining density theorem can be reduced to finitely many fixed
triple-incidence loci. -/
abbrev OrderedTripleIndex (n : ℕ) :=
  {ijk : Fin n × Fin n × Fin n //
    ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2}

/-- The good locus for one ordered triple of pairwise-distinct indices. -/
def orderedTripleGood {n : ℕ} (t : OrderedTripleIndex n) :
    Set (Lower.ArrangementParameter n) :=
  (Lower.GenericityPort.tripleBadSet
    t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2.1 t.2.2.2)ᶜ

/-- Parameter locus where one selected pair has finite carrier contact. -/
def pairFiniteGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p | ((p.toArrangement i).carrier ∩
    (p.toArrangement j).carrier).Finite}

/-- A stronger, elementary good locus for one pair: unequal circles and
nonparallel stems.  This is the explicit geometric condition currently used
as the next density target for pair-finiteness. -/
def pairRegularGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p |
    (p.toArrangement i).circle ≠ (p.toArrangement j).circle ∧
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0}

/-- Stronger open pair-regular locus: distinct centers and nonparallel stems.
This implies `pairRegularGood`, but is better suited to finite neighborhood
arguments because it is visibly open in the center/radial parameter space. -/
def pairCenterRegularGood {n : ℕ} (i j : Fin n) :
    Set (Lower.ArrangementParameter n) :=
  {p |
    (p.toArrangement i).center ≠ (p.toArrangement j).center ∧
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0}

/-- The center-regular locus is open. -/
theorem isOpen_pairCenterRegularGood {n : ℕ} (i j : Fin n) :
    IsOpen (pairCenterRegularGood i j) := by
  have hcenter_i : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement i).center) :=
    Lower.continuous_lollipop_center_comp
      (Lower.continuous_toLollipop.comp (continuous_apply i))
  have hcenter_j : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement j).center) :=
    Lower.continuous_lollipop_center_comp
      (Lower.continuous_toLollipop.comp (continuous_apply j))
  have hradial_i : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement i).radial) :=
    Lower.continuous_lollipop_radial_comp
      (Lower.continuous_toLollipop.comp (continuous_apply i))
  have hradial_j : Continuous (fun p : Lower.ArrangementParameter n =>
      (p.toArrangement j).radial) :=
    Lower.continuous_lollipop_radial_comp
      (Lower.continuous_toLollipop.comp (continuous_apply j))
  have hcenterOpen : IsOpen {p : Lower.ArrangementParameter n |
      (p.toArrangement i).center ≠ (p.toArrangement j).center} :=
    isOpen_ne_fun hcenter_i hcenter_j
  have hdet : Continuous (fun p : Lower.ArrangementParameter n =>
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial) :=
    continuous_detPoint_comp hradial_i hradial_j
  have hdetOpen : IsOpen {p : Lower.ArrangementParameter n |
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0} :=
    isOpen_ne_fun hdet continuous_const
  change IsOpen
    ({p : Lower.ArrangementParameter n |
      (p.toArrangement i).center ≠ (p.toArrangement j).center} ∩
    {p : Lower.ArrangementParameter n |
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0})
  exact hcenterOpen.inter hdetOpen

/-- Distinct circles plus nonparallel stems imply finite carrier contact. -/
theorem pairCrossingSet_finite_of_circle_ne_of_nonparallel
    {L M : Lollipop} (hcircle : L.circle ≠ M.circle)
    (hdet : detPoint L.radial M.radial ≠ 0) :
    (pairCrossingSet L M).Finite := by
  have hccFin : (cc L M).Finite :=
    finite_circle_intersection_of_ne hcircle
  have hrcFin : (rc L M).Finite :=
    finite_ray_circle_intersection L M
  have hcrFin : (cr L M).Finite :=
    finite_circle_ray_intersection L M
  have hrrFin : (rr L M).Finite := by
    by_cases hrr : (rr L M).Nonempty
    · exact finite_of_subsingleton_of_mem
        (rr_subsingleton_of_transverse hdet) hrr.some_mem
    · rw [Set.not_nonempty_iff_eq_empty.mp hrr]
      exact Set.finite_empty
  rw [pairCrossingSet_decompose]
  exact ((hccFin.union hrcFin).union hcrFin).union hrrFin

/-- The elementary pair-regular locus is contained in the finite-contact
locus. -/
theorem pairRegularGood_subset_pairFiniteGood {n : ℕ} (i j : Fin n) :
    pairRegularGood i j ⊆ pairFiniteGood i j := by
  intro p hp
  exact pairCrossingSet_finite_of_circle_ne_of_nonparallel hp.1 hp.2

/-- Distinct centers force distinct circle sets. -/
theorem circle_ne_of_center_ne {L M : Lollipop}
    (hcenter : L.center ≠ M.center) :
    L.circle ≠ M.circle := by
  intro hcircle
  have hsphere : concreteSphere L ≠ concreteSphere M := by
    intro hsphere
    exact hcenter (congrArg EuclideanGeometry.Sphere.center hsphere)
  have hccFinite : (cc L M).Finite := by
    apply finite_of_forall_mem_eq_left_or_right
    intro a b x ha hb hx hab
    exact eq_or_eq_of_mem_cc_of_two_witnesses hsphere hab ha hb hx
  have hcircleSubset : L.circle ⊆ cc L M := by
    intro x hx
    exact ⟨hx, by simpa [hcircle] using hx⟩
  exact (_root_.Lollipop.Concrete.EndToEnd.Lollipop.circle_infinite L)
    (hccFinite.subset hcircleSubset)

/-- Center-regular pairs are pair-regular in the carrier-finiteness sense. -/
theorem pairCenterRegularGood_subset_pairRegularGood {n : ℕ}
    (i j : Fin n) :
    pairCenterRegularGood i j ⊆ pairRegularGood i j := by
  intro p hp
  exact ⟨circle_ne_of_center_ne hp.1, hp.2⟩

/-- Center-regular pairs have finite carrier contact. -/
theorem pairCenterRegularGood_subset_pairFiniteGood {n : ℕ}
    (i j : Fin n) :
    pairCenterRegularGood i j ⊆ pairFiniteGood i j :=
  (pairCenterRegularGood_subset_pairRegularGood i j).trans
    (pairRegularGood_subset_pairFiniteGood i j)

/-- Translate one parameter in an arrangement parameter vector. -/
def translateParameterAt {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) (v : Point) :
    Lower.ArrangementParameter n :=
  fun a =>
    if _h : a = k then
      ⟨((p a).1.1 + v, (p a).1.2), (p a).2⟩
    else p a

@[simp] theorem translateParameterAt_zero {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) :
    translateParameterAt p k 0 = p := by
  funext a
  by_cases ha : a = k
  · simp [translateParameterAt, ha]
  · simp [translateParameterAt, ha]

theorem translateParameterAt_apply_self {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) (v : Point) :
    (translateParameterAt p k v).toArrangement k =
      TranslationGenericity.translate (p.toArrangement k) v := by
  ext <;>
    simp [translateParameterAt, Lower.ArrangementParameter.toArrangement,
      Lower.LollipopParameter.toLollipop, TranslationGenericity.translate]

theorem translateParameterAt_apply_ne {n : ℕ}
    (p : Lower.ArrangementParameter n) {a k : Fin n} (v : Point)
    (hak : a ≠ k) :
    (translateParameterAt p k v).toArrangement a =
      p.toArrangement a := by
  simp [translateParameterAt, Lower.ArrangementParameter.toArrangement, hak]

/-- The one-parameter translation path is continuous in the raw center/radial
parameter space. -/
theorem continuous_translateParameterAt {n : ℕ}
    (p : Lower.ArrangementParameter n) (k : Fin n) :
    Continuous (fun v : Point => translateParameterAt p k v) := by
  apply continuous_pi
  intro a
  by_cases ha : a = k
  · rw [continuous_induced_rng]
    change Continuous (fun v : Point => (translateParameterAt p k v a).1)
    simp [translateParameterAt, ha]
    constructor <;> fun_prop
  · rw [show (fun v : Point => translateParameterAt p k v a) =
        fun _v : Point => p a by
      funext v
      simp [translateParameterAt, ha]]
    exact continuous_const

/-- The center-regular locus is dense for every ordered distinct pair. -/
theorem dense_pairCenterRegularGood {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Dense (pairCenterRegularGood i j) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases
    (Lower.GenericityPort.dense_compl_parallelBadSet i j hij).exists_mem_open
      hU hUne with
    ⟨p, hpParallel, hpU⟩
  have hpDet :
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0 := by
    change p ∉ Lower.GenericityPort.parallelBadSet i j hij at hpParallel
    exact hpParallel
  by_cases hcenter :
      (p.toArrangement i).center ≠ (p.toArrangement j).center
  · exact ⟨p, hpU, hcenter, hpDet⟩
  · have hcenterEq :
        (p.toArrangement i).center = (p.toArrangement j).center :=
      not_not.mp hcenter
    let V : Set (Lower.ArrangementParameter n) :=
      U ∩ (Lower.GenericityPort.parallelBadSet i j hij)ᶜ
    have hVopen : IsOpen V :=
      hU.inter (Lower.GenericityPort.isOpen_compl_parallelBadSet i j hij)
    have hpV : p ∈ V := ⟨hpU, hpParallel⟩
    let γ : Point → Lower.ArrangementParameter n :=
      fun v => translateParameterAt p j v
    have hγcont : Continuous γ :=
      continuous_translateParameterAt p j
    have hpreOpen : IsOpen (γ ⁻¹' V) := hVopen.preimage hγcont
    have hzero : (0 : Point) ∈ γ ⁻¹' V := by
      change γ 0 ∈ V
      simpa [γ] using hpV
    have hnhds : γ ⁻¹' V ∈ nhds (0 : Point) :=
      hpreOpen.mem_nhds hzero
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
    let v : Point := (ε / 2) • (p.toArrangement i).unitRadial
    have hεhalf : 0 < ε / 2 := by linarith
    have hv_ne : v ≠ 0 := by
      exact smul_ne_zero (ne_of_gt hεhalf)
        (p.toArrangement i).unitRadial_ne_zero
    have hvball : v ∈ Metric.ball (0 : Point) ε := by
      have hhalf_lt : |ε| / 2 < ε := by
        rw [abs_of_pos hεpos]
        linarith
      simpa [Metric.mem_ball, dist_eq_norm, v, norm_smul,
        Real.norm_eq_abs, abs_of_pos hεhalf,
        (p.toArrangement i).norm_unitRadial] using hhalf_lt
    have hqV : γ v ∈ V := hεsub hvball
    refine ⟨γ v, hqV.1, ?_⟩
    have hi :
        (γ v).toArrangement i = p.toArrangement i := by
      simpa [γ] using
        translateParameterAt_apply_ne p (a := i) (k := j) v hij
    have hj :
        (γ v).toArrangement j =
          TranslationGenericity.translate (p.toArrangement j) v := by
      simpa [γ] using translateParameterAt_apply_self p j v
    have hcenterNe :
        ((γ v).toArrangement i).center ≠
          ((γ v).toArrangement j).center := by
      intro hcent
      rw [hi, hj] at hcent
      change (p.toArrangement i).center =
        (p.toArrangement j).center + v at hcent
      have hv_zero : v = 0 := by
        calc
          v = ((p.toArrangement j).center + v) -
              (p.toArrangement j).center := by module
          _ = (p.toArrangement i).center -
              (p.toArrangement j).center := by rw [← hcent]
          _ = 0 := by rw [hcenterEq]; module
      exact hv_ne hv_zero
    constructor
    · exact hcenterNe
    · have hqParallel :
          γ v ∉ Lower.GenericityPort.parallelBadSet i j hij := hqV.2
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0 at hqParallel
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0
      exact hqParallel

/-- Finite index type for ordered distinct pairs. -/
abbrev OrderedDistinctPairIndex (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 ≠ ij.2}

/-- All ordered distinct pairs are center-regular. -/
def allPairCenterRegularGood {n : ℕ} :
    Set (Lower.ArrangementParameter n) :=
  ⋂ ij : OrderedDistinctPairIndex n,
    pairCenterRegularGood ij.1.1 ij.1.2

/-- The all-pairs center-regular locus is open. -/
theorem isOpen_allPairCenterRegularGood {n : ℕ} :
    IsOpen (allPairCenterRegularGood (n := n)) := by
  classical
  unfold allPairCenterRegularGood
  apply isOpen_iInter_of_finite
  intro ij
  exact isOpen_pairCenterRegularGood ij.1.1 ij.1.2

/-- The all-pairs center-regular locus is dense. -/
theorem dense_allPairCenterRegularGood {n : ℕ} :
    Dense (allPairCenterRegularGood (n := n)) := by
  classical
  unfold allPairCenterRegularGood
  exact
    Lower.GenericityPort.dense_iInter_fintype_of_open_dense
      (fun ij : OrderedDistinctPairIndex n =>
        pairCenterRegularGood ij.1.1 ij.1.2)
      (by
        intro ij
        exact isOpen_pairCenterRegularGood ij.1.1 ij.1.2)
      (by
        intro ij
        exact dense_pairCenterRegularGood ij.1.1 ij.1.2 ij.2)

/-- An arrangement in the all-pairs center-regular locus has finite contact
between every distinct pair of carriers. -/
theorem pairFiniteArrangement_of_mem_allPairCenterRegularGood {n : ℕ}
    {p : Lower.ArrangementParameter n}
    (hp : p ∈ allPairCenterRegularGood (n := n)) :
    TranslationGenericity.PairFiniteArrangement p.toArrangement := by
  intro i j hij
  have hpij :
      p ∈ pairCenterRegularGood i j := by
    exact Set.mem_iInter.mp hp ⟨(i, j), hij⟩
  exact (pairCenterRegularGood_subset_pairFiniteGood i j hpij)

/-- Around a point in an open all-pairs center-regular neighborhood, small
translations of one selected center remain inside that same neighborhood. -/
theorem exists_norm_ball_translateParameterAt_subset_open_allPairCenterRegularGood
    {n : ℕ} {p : Lower.ArrangementParameter n} (k : Fin n)
    {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hpPair : p ∈ allPairCenterRegularGood (n := n)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : Point, ‖v‖ < ε →
        translateParameterAt p k v ∈
          U ∩ allPairCenterRegularGood (n := n) := by
  let V : Set (Lower.ArrangementParameter n) :=
    U ∩ allPairCenterRegularGood (n := n)
  have hVopen : IsOpen V :=
    hU.inter isOpen_allPairCenterRegularGood
  have hpV : p ∈ V := ⟨hpU, hpPair⟩
  let γ : Point → Lower.ArrangementParameter n :=
    fun v => translateParameterAt p k v
  have hγcont : Continuous γ :=
    continuous_translateParameterAt p k
  have hpreOpen : IsOpen (γ ⁻¹' V) := hVopen.preimage hγcont
  have hzero : (0 : Point) ∈ γ ⁻¹' V := by
    change γ 0 ∈ V
    simpa [γ] using hpV
  have hnhds : γ ⁻¹' V ∈ nhds (0 : Point) :=
    hpreOpen.mem_nhds hzero
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro v hv
  exact hεsub (by simpa [Metric.mem_ball, dist_eq_norm] using hv)

/-- If a translated full parameter remains in the all-pairs center-regular
locus, then every old member of the `k`-prefix has finite contact with the
translated `k`th lollipop. -/
theorem pairContactsFinite_prefix_translate_of_mem_allPairCenterRegularGood
    {n k : ℕ} {p : Lower.ArrangementParameter n} (hk : k < n)
    {v : Point}
    (hp :
      translateParameterAt p ⟨k, hk⟩ v ∈
        allPairCenterRegularGood (n := n)) :
    TranslationGenericity.PairContactsFinite
      (PlanarInsertion.prefixArrangement p.toArrangement k (Nat.le_of_lt hk))
      (TranslationGenericity.translate (p.toArrangement ⟨k, hk⟩) v) := by
  intro i
  let q : Lower.ArrangementParameter n := translateParameterAt p ⟨k, hk⟩ v
  have hqfinite :
      TranslationGenericity.PairFiniteArrangement q.toArrangement :=
    pairFiniteArrangement_of_mem_allPairCenterRegularGood hp
  let ii : Fin n := ⟨i.1, lt_trans i.2 hk⟩
  let kk : Fin n := ⟨k, hk⟩
  have hik : ii ≠ kk := by
    intro h
    have hv := congrArg (fun x : Fin n => x.1) h
    dsimp [ii, kk] at hv
    omega
  have hqi : q.toArrangement ii = p.toArrangement ii := by
    simpa [q, ii, kk] using
      translateParameterAt_apply_ne p (a := ii) (k := kk) v hik
  have hqk :
      q.toArrangement kk =
        TranslationGenericity.translate (p.toArrangement kk) v := by
    simpa [q, kk] using translateParameterAt_apply_self p kk v
  have hfin := hqfinite ii kk hik
  simpa [PlanarInsertion.prefixArrangement, ii, kk, hqi, hqk] using hfin

/-- Updating the `k`th center and then taking the `(k+1)`-prefix is the same
as appending the translated `k`th lollipop to the old `k`-prefix. -/
theorem prefix_translateParameterAt_succ_eq_snoc
    {n k : ℕ} (p : Lower.ArrangementParameter n) (hk : k < n)
    (v : Point) :
    PlanarInsertion.prefixArrangement
        (translateParameterAt p ⟨k, hk⟩ v).toArrangement
        (k + 1) (Nat.succ_le_of_lt hk) =
      Insertion.snocArrangement
        (PlanarInsertion.prefixArrangement p.toArrangement k
          (Nat.le_of_lt hk))
        (TranslationGenericity.translate (p.toArrangement ⟨k, hk⟩) v) := by
  funext i
  by_cases hik : i.1 < k
  · let ii : Fin n := ⟨i.1, i.2.trans_le (Nat.succ_le_of_lt hk)⟩
    let iiOld : Fin n := ⟨i.1, lt_trans hik hk⟩
    let kk : Fin n := ⟨k, hk⟩
    have hii : ii = iiOld := by
      exact Fin.ext rfl
    have hine : ii ≠ kk := by
      intro h
      have hv := congrArg (fun x : Fin n => x.1) h
      dsimp [ii, kk] at hv
      omega
    have happly :
        (translateParameterAt p kk v).toArrangement ii =
          p.toArrangement ii := by
      simpa [kk] using
        translateParameterAt_apply_ne p (a := ii) (k := kk) v hine
    simp [PlanarInsertion.prefixArrangement, Insertion.snocArrangement,
      hik, happly, hii, ii, iiOld, kk]
  · have hi : i = Fin.last k := Insertion.fin_eq_last_of_not_lt hik
    subst i
    let kk : Fin n := ⟨k, hk⟩
    have happly :
        (translateParameterAt p kk v).toArrangement kk =
          TranslationGenericity.translate (p.toArrangement kk) v := by
      simpa [kk] using translateParameterAt_apply_self p kk v
    simp [PlanarInsertion.prefixArrangement, Insertion.snocArrangement,
      happly, kk]

/-- One step of the finite prefix genericization: translate the `k`th
lollipop while staying in the prescribed open all-pairs regular locus, and
extend no-triple position from the `k`-prefix to the `(k+1)`-prefix. -/
theorem exists_translateParameterAt_step_prefix_noTriple
    {n k : ℕ} {p : Lower.ArrangementParameter n} (hk : k < n)
    {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hpPair : p ∈ allPairCenterRegularGood (n := n))
    (htriple :
      TranslationGenericity.NoTripleCarrierPoints
        (PlanarInsertion.prefixArrangement p.toArrangement k
          (Nat.le_of_lt hk))) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∈ allPairCenterRegularGood (n := n) ∧
        TranslationGenericity.NoTripleCarrierPoints
          (PlanarInsertion.prefixArrangement q.toArrangement (k + 1)
            (Nat.succ_le_of_lt hk)) ∧
        ∃ v : Point, q = translateParameterAt p ⟨k, hk⟩ v := by
  obtain ⟨ε, hεpos, hball⟩ :=
    exists_norm_ball_translateParameterAt_subset_open_allPairCenterRegularGood
      ⟨k, hk⟩ hU hpU hpPair
  let Aold : Arrangement k :=
    PlanarInsertion.prefixArrangement p.toArrangement k (Nat.le_of_lt hk)
  let Lnew : Lollipop := p.toArrangement ⟨k, hk⟩
  have hfinite : TranslationGenericity.PairFiniteArrangement Aold := by
    exact TranslationGenericity.pairFiniteArrangement_prefix
      p.toArrangement (Nat.le_of_lt hk)
      (pairFiniteArrangement_of_mem_allPairCenterRegularGood hpPair)
  have hcontacts :
      ∀ v : Point, ‖v‖ < ε →
        TranslationGenericity.PairContactsFinite Aold
          (TranslationGenericity.translate Lnew v) := by
    intro v hv
    have hpvPair :
        translateParameterAt p ⟨k, hk⟩ v ∈
          allPairCenterRegularGood (n := n) := (hball v hv).2
    simpa [Aold, Lnew] using
      pairContactsFinite_prefix_translate_of_mem_allPairCenterRegularGood
        (p := p) hk hpvPair
  obtain ⟨v, hv, _hpair, htri⟩ :=
    TranslationGenericity.exists_norm_lt_pairFinite_noTriple_snoc_translate
      Aold Lnew hfinite htriple hεpos hcontacts
  let q : Lower.ArrangementParameter n := translateParameterAt p ⟨k, hk⟩ v
  have hqOpenPair :
      q ∈ U ∩ allPairCenterRegularGood (n := n) := hball v hv
  refine ⟨q, hqOpenPair.1, hqOpenPair.2, ?_, ⟨v, rfl⟩⟩
  change
    TranslationGenericity.NoTripleCarrierPoints
      (PlanarInsertion.prefixArrangement
        (translateParameterAt p ⟨k, hk⟩ v).toArrangement
        (k + 1) (Nat.succ_le_of_lt hk))
  rw [prefix_translateParameterAt_succ_eq_snoc p hk v]
  simpa [Aold, Lnew] using htri

/-- Finite prefix induction for the concrete triple-genericity construction.

Starting from any point in an open all-pairs center-regular locus, repeatedly
translate the next indexed lollipop by a sufficiently small vector.  The
construction stays in the same open set and extends no-triple position from
the current prefix to the next prefix at each step. -/
theorem exists_mem_open_allPairCenterRegularGood_prefix_noTriple
    {n : ℕ} {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) {p : Lower.ArrangementParameter n}
    (hpU : p ∈ U) (hpPair : p ∈ allPairCenterRegularGood (n := n)) :
    ∀ k : ℕ, ∀ hk : k ≤ n,
      ∃ q : Lower.ArrangementParameter n,
        q ∈ U ∧
          q ∈ allPairCenterRegularGood (n := n) ∧
          TranslationGenericity.NoTripleCarrierPoints
            (PlanarInsertion.prefixArrangement q.toArrangement k hk) := by
  intro k
  induction k with
  | zero =>
      intro hk
      refine ⟨p, hpU, hpPair, ?_⟩
      exact TranslationGenericity.noTripleCarrierPoints_empty
        (PlanarInsertion.prefixArrangement p.toArrangement 0 hk)
  | succ k ih =>
      intro hkSucc
      have hklt : k < n := Nat.lt_of_succ_le hkSucc
      have hk : k ≤ n := Nat.le_of_lt hklt
      rcases ih hk with ⟨p', hp'U, hp'Pair, hp'Triple⟩
      rcases
        exists_translateParameterAt_step_prefix_noTriple
          (p := p') hklt hU hp'U hp'Pair hp'Triple with
        ⟨q, hqU, hqPair, hqTriple, _hv⟩
      refine ⟨q, hqU, hqPair, ?_⟩
      simpa [Nat.succ_eq_add_one] using hqTriple

/-- Every open set meeting the all-pairs center-regular locus also contains a
point whose full concrete arrangement has no triple carrier point. -/
theorem exists_mem_open_allPairCenterRegularGood_noTriple
    {n : ℕ} {U : Set (Lower.ArrangementParameter n)}
    (hU : IsOpen U) {p : Lower.ArrangementParameter n}
    (hpU : p ∈ U) (hpPair : p ∈ allPairCenterRegularGood (n := n)) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∈ allPairCenterRegularGood (n := n) ∧
        TranslationGenericity.NoTripleCarrierPoints q.toArrangement := by
  rcases
    exists_mem_open_allPairCenterRegularGood_prefix_noTriple
      hU hpU hpPair n le_rfl with
    ⟨q, hqU, hqPair, hqTriple⟩
  refine ⟨q, hqU, hqPair, ?_⟩
  rw [PlanarInsertion.prefix_full q.toArrangement] at hqTriple
  exact hqTriple

/-- The elementary pair-regular locus is dense for every ordered distinct
pair.  The proof first enters the already-proved nonparallel-stem locus, then
translates only the second center inside that open set.  Radials are unchanged,
so nonparallelness is preserved, while the nonzero center translation forces
the two circle sets to be distinct. -/
theorem dense_pairRegularGood {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Dense (pairRegularGood i j) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases
    (Lower.GenericityPort.dense_compl_parallelBadSet i j hij).exists_mem_open
      hU hUne with
    ⟨p, hpParallel, hpU⟩
  have hpDet :
      detPoint (p.toArrangement i).radial
        (p.toArrangement j).radial ≠ 0 := by
    change p ∉ Lower.GenericityPort.parallelBadSet i j hij at hpParallel
    exact hpParallel
  by_cases hcircle :
      (p.toArrangement i).circle ≠ (p.toArrangement j).circle
  · exact ⟨p, hpU, hcircle, hpDet⟩
  · have hcircleEq :
        (p.toArrangement i).circle = (p.toArrangement j).circle :=
      not_not.mp hcircle
    have hcenterEq :
        (p.toArrangement i).center = (p.toArrangement j).center := by
      by_contra hcenterNe
      exact hcircle (circle_ne_of_center_ne hcenterNe)
    let V : Set (Lower.ArrangementParameter n) :=
      U ∩ (Lower.GenericityPort.parallelBadSet i j hij)ᶜ
    have hVopen : IsOpen V :=
      hU.inter (Lower.GenericityPort.isOpen_compl_parallelBadSet i j hij)
    have hpV : p ∈ V := ⟨hpU, hpParallel⟩
    let γ : Point → Lower.ArrangementParameter n :=
      fun v => translateParameterAt p j v
    have hγcont : Continuous γ :=
      continuous_translateParameterAt p j
    have hpreOpen : IsOpen (γ ⁻¹' V) := hVopen.preimage hγcont
    have hzero : (0 : Point) ∈ γ ⁻¹' V := by
      change γ 0 ∈ V
      simpa [γ] using hpV
    have hnhds : γ ⁻¹' V ∈ nhds (0 : Point) :=
      hpreOpen.mem_nhds hzero
    rcases Metric.mem_nhds_iff.mp hnhds with ⟨ε, hεpos, hεsub⟩
    let v : Point := (ε / 2) • (p.toArrangement i).unitRadial
    have hεhalf : 0 < ε / 2 := by linarith
    have hv_ne : v ≠ 0 := by
      exact smul_ne_zero (ne_of_gt hεhalf)
        (p.toArrangement i).unitRadial_ne_zero
    have hvball : v ∈ Metric.ball (0 : Point) ε := by
      have hhalf_lt : |ε| / 2 < ε := by
        rw [abs_of_pos hεpos]
        linarith
      simpa [Metric.mem_ball, dist_eq_norm, v, norm_smul,
        Real.norm_eq_abs, abs_of_pos hεhalf,
        (p.toArrangement i).norm_unitRadial] using hhalf_lt
    have hqV : γ v ∈ V := hεsub hvball
    refine ⟨γ v, hqV.1, ?_⟩
    have hi :
        (γ v).toArrangement i = p.toArrangement i := by
      simpa [γ] using
        translateParameterAt_apply_ne p (a := i) (k := j) v hij
    have hj :
        (γ v).toArrangement j =
          TranslationGenericity.translate (p.toArrangement j) v := by
      simpa [γ] using translateParameterAt_apply_self p j v
    have hcenterNe :
        ((γ v).toArrangement i).center ≠
          ((γ v).toArrangement j).center := by
      intro hcent
      rw [hi, hj] at hcent
      change (p.toArrangement i).center =
        (p.toArrangement j).center + v at hcent
      have hv_zero : v = 0 := by
        calc
          v = ((p.toArrangement j).center + v) -
              (p.toArrangement j).center := by module
          _ = (p.toArrangement i).center -
              (p.toArrangement j).center := by rw [← hcent]
          _ = 0 := by rw [hcenterEq]; module
      exact hv_ne hv_zero
    constructor
    · exact circle_ne_of_center_ne hcenterNe
    · have hqParallel :
          γ v ∉ Lower.GenericityPort.parallelBadSet i j hij := hqV.2
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0 at hqParallel
      change detPoint ((γ v).toArrangement i).radial
        ((γ v).toArrangement j).radial ≠ 0
      exact hqParallel

/-- Two-lollipop arrangement used to feed the translation-avoidance theorem
for a fixed old pair. -/
def twoArrangement (L M : Lollipop) : Arrangement 2 :=
  fun a => if a = (0 : Fin 2) then L else M

@[simp] theorem twoArrangement_zero (L M : Lollipop) :
    twoArrangement L M (0 : Fin 2) = L := by
  simp [twoArrangement]

@[simp] theorem twoArrangement_one (L M : Lollipop) :
    twoArrangement L M (1 : Fin 2) = M := by
  simp [twoArrangement]

theorem pairFinite_twoArrangement_of_finite {L M : Lollipop}
    (hfinite : (L.carrier ∩ M.carrier).Finite) :
    TranslationGenericity.PairFiniteArrangement (twoArrangement L M) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · simpa using hfinite
  · simpa [Set.inter_comm] using hfinite
  · exact False.elim (hab rfl)

/-- Local triple-contact avoidance for one ordered triple.

If the first two carriers already have finite contact, then translating the
third lollipop inside any open parameter neighborhood avoids common points of
the three selected carriers.  This is the bridge from the tracked
`TranslationGenericity` module to the remaining finite-avoidance theorem. -/
theorem exists_mem_open_not_tripleBadSet_of_pairFinite_at {n : ℕ}
    {p : Lower.ArrangementParameter n} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hfinite :
      ((p.toArrangement i).carrier ∩
        (p.toArrangement j).carrier).Finite)
    {U : Set (Lower.ArrangementParameter n)} (hU : IsOpen U)
    (hpU : p ∈ U) :
    ∃ q : Lower.ArrangementParameter n,
      q ∈ U ∧
        q ∉ Lower.GenericityPort.tripleBadSet i j k hij hik hjk := by
  classical
  let Aij : Arrangement 2 :=
    twoArrangement (p.toArrangement i) (p.toArrangement j)
  have hAijFinite : TranslationGenericity.PairFiniteArrangement Aij := by
    simpa [Aij] using pairFinite_twoArrangement_of_finite hfinite
  let γ : Point → Lower.ArrangementParameter n :=
    fun v => translateParameterAt p k v
  have hγcont : Continuous γ :=
    continuous_translateParameterAt p k
  have hpreOpen : IsOpen (γ ⁻¹' U) := hU.preimage hγcont
  have hzero : (0 : Point) ∈ γ ⁻¹' U := by
    change γ 0 ∈ U
    simpa [γ] using hpU
  obtain ⟨v, hvU, havoid⟩ :=
    TranslationGenericity.exists_mem_open_noTripleContactWithInserted_translate
      Aij (p.toArrangement k) hAijFinite hpreOpen hzero
  refine ⟨γ v, hvU, ?_⟩
  intro hbad
  rcases hbad with ⟨x, hx⟩
  rcases hx with ⟨hxij, hxk⟩
  rcases hxij with ⟨hxi, hxj⟩
  have hxiOld : x ∈ (p.toArrangement i).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      hik] using hxi
  have hxjOld : x ∈ (p.toArrangement j).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      hjk] using hxj
  have hxkNew :
      x ∈ (TranslationGenericity.translate (p.toArrangement k) v).carrier := by
    simpa [γ, Lower.ArrangementParameter.toArrangement, translateParameterAt,
      Lower.LollipopParameter.toLollipop, TranslationGenericity.translate]
      using hxk
  have hdisj := havoid (i := (0 : Fin 2)) (j := (1 : Fin 2)) (by decide)
  exact Set.disjoint_left.mp hdisj
    (by simpa [Aij] using (show x ∈ (Aij (0 : Fin 2)).carrier ∩
        (TranslationGenericity.translate (p.toArrangement k) v).carrier from
        ⟨hxiOld, hxkNew⟩))
    (by simpa [Aij] using (show x ∈ (Aij (1 : Fin 2)).carrier ∩
        (TranslationGenericity.translate (p.toArrangement k) v).carrier from
        ⟨hxjOld, hxkNew⟩))

/-- Fixed-triple density is reduced to density of finite contact for the
first selected pair. -/
theorem dense_orderedTripleGood_of_pairFiniteGood_dense {n : ℕ}
    (t : OrderedTripleIndex n)
    (hdense : Dense (pairFiniteGood t.1.1 t.1.2.1)) :
    Dense (orderedTripleGood t) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases hdense.exists_mem_open hU hUne with ⟨p, hpfinite, hpU⟩
  rcases
    exists_mem_open_not_tripleBadSet_of_pairFinite_at
      t.2.1 t.2.2.1 t.2.2.2 hpfinite hU hpU with
    ⟨q, hqU, hqgood⟩
  exact ⟨q, hqU, by simpa [orderedTripleGood] using hqgood⟩

/-- Fixed-triple density is also reduced to density of the stronger elementary
pair-regular locus. -/
theorem dense_orderedTripleGood_of_pairRegularGood_dense {n : ℕ}
    (t : OrderedTripleIndex n)
    (hdense : Dense (pairRegularGood t.1.1 t.1.2.1)) :
    Dense (orderedTripleGood t) :=
  dense_orderedTripleGood_of_pairFiniteGood_dense t
    (hdense.mono (pairRegularGood_subset_pairFiniteGood t.1.1 t.1.2.1))

/-- Every fixed ordered-triple good locus is dense. -/
theorem dense_orderedTripleGood {n : ℕ}
    (t : OrderedTripleIndex n) :
    Dense (orderedTripleGood t) :=
  dense_orderedTripleGood_of_pairRegularGood_dense t
    (dense_pairRegularGood t.1.1 t.1.2.1 t.2.1)

/-- The complement of the triple bad union is exactly the finite intersection
of the fixed ordered-triple good loci. -/
theorem compl_tripleBadUnion_eq_iInter_orderedTripleGood {n : ℕ} :
    ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) =
      ⋂ t : OrderedTripleIndex n, orderedTripleGood t := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_iInter]
    intro t
    change p ∉
      Lower.GenericityPort.tripleBadSet
        t.1.1 t.1.2.1 t.1.2.2 t.2.1 t.2.2.1 t.2.2.2
    intro hbad
    apply hp
    unfold Lower.GenericityPort.tripleBadUnion
    exact Set.mem_iUnion.mpr ⟨t.1.1,
      Set.mem_iUnion.mpr ⟨t.1.2.1,
        Set.mem_iUnion.mpr ⟨t.1.2.2,
          Set.mem_iUnion.mpr ⟨t.2.1,
            Set.mem_iUnion.mpr ⟨t.2.2.1,
              Set.mem_iUnion.mpr ⟨t.2.2.2, hbad⟩⟩⟩⟩⟩⟩
  · intro hp hbad
    unfold Lower.GenericityPort.tripleBadUnion at hbad
    rcases Set.mem_iUnion.mp hbad with ⟨i, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨j, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨k, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hij, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hik, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hjk, hbad⟩
    let t : OrderedTripleIndex n := ⟨(i, j, k), ⟨hij, hik, hjk⟩⟩
    have hgood : p ∈ orderedTripleGood t := Set.mem_iInter.mp hp t
    change p ∉ Lower.GenericityPort.tripleBadSet i j k hij hik hjk at hgood
    exact hgood hbad

/-- The parameter is outside the explicit triple-bad union iff its concrete
arrangement has no triple carrier points. -/
theorem not_mem_tripleBadUnion_iff_noTripleCarrierPoints {n : ℕ}
    (p : Lower.ArrangementParameter n) :
    p ∉ (Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n)) ↔
      TranslationGenericity.NoTripleCarrierPoints p.toArrangement := by
  constructor
  · intro hnot i j k hij hik hjk
    rw [Set.disjoint_left]
    intro x hxi hxj
    apply hnot
    unfold Lower.GenericityPort.tripleBadUnion
    exact Set.mem_iUnion.mpr ⟨i,
      Set.mem_iUnion.mpr ⟨j,
        Set.mem_iUnion.mpr ⟨k,
          Set.mem_iUnion.mpr ⟨hij,
            Set.mem_iUnion.mpr ⟨hik,
              Set.mem_iUnion.mpr ⟨hjk,
                ⟨x, by
                  simpa only [Lower.ArrangementParameter.toArrangement,
                    Set.mem_inter_iff] using ⟨⟨hxi.1, hxj.1⟩, hxi.2⟩⟩⟩⟩⟩⟩⟩⟩
  · intro htriple hbad
    unfold Lower.GenericityPort.tripleBadUnion at hbad
    rcases Set.mem_iUnion.mp hbad with ⟨i, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨j, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨k, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hij, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hik, hbad⟩
    rcases Set.mem_iUnion.mp hbad with ⟨hjk, hbad⟩
    rcases hbad with ⟨x, hx⟩
    have hx' :
        x ∈ (p.toArrangement i).carrier ∩ (p.toArrangement k).carrier :=
      ⟨hx.1.1, hx.2⟩
    have hx'' :
        x ∈ (p.toArrangement j).carrier ∩ (p.toArrangement k).carrier :=
      ⟨hx.1.2, hx.2⟩
    exact Set.disjoint_left.mp (htriple i j k hij hik hjk) hx' hx''

/-- Direct forward form of the triple-bad-union bridge. -/
theorem not_mem_tripleBadUnion_of_noTripleCarrierPoints {n : ℕ}
    {p : Lower.ArrangementParameter n}
    (htriple : TranslationGenericity.NoTripleCarrierPoints p.toArrangement) :
    p ∉ (Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n)) :=
  (not_mem_tripleBadUnion_iff_noTripleCarrierPoints p).2 htriple

/-- Finite-index reduction for the triple-contact density theorem.  It is
enough to prove that every fixed ordered-triple good locus is open dense. -/
theorem dense_compl_tripleBadUnion_of_orderedTriple_open_dense {n : ℕ}
    (hopen : ∀ t : OrderedTripleIndex n, IsOpen (orderedTripleGood t))
    (hdense : ∀ t : OrderedTripleIndex n, Dense (orderedTripleGood t)) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  classical
  have hfinite :
      Dense (⋂ t : OrderedTripleIndex n, orderedTripleGood t) :=
    Lower.GenericityPort.dense_iInter_fintype_of_open_dense
      (orderedTripleGood (n := n)) hopen hdense
  rwa [compl_tripleBadUnion_eq_iInter_orderedTripleGood]

/-- Once the fixed ordered-triple good loci are known to be open, their
density is already proved by `dense_orderedTripleGood`. -/
theorem dense_compl_tripleBadUnion_of_orderedTriple_open {n : ℕ}
    (hopen : ∀ t : OrderedTripleIndex n, IsOpen (orderedTripleGood t)) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) :=
  dense_compl_tripleBadUnion_of_orderedTriple_open_dense
    hopen dense_orderedTripleGood

/-- Remaining triple-contact avoidance theorem for the only nontrivial range
`3 ≤ n`. -/
theorem dense_compl_tripleBadUnion_ge_three (n : ℕ) (_hn : 3 ≤ n) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  rcases dense_allPairCenterRegularGood.exists_mem_open hU hUne with
    ⟨p, hpPair, hpU⟩
  rcases
    exists_mem_open_allPairCenterRegularGood_noTriple
      hU hpU hpPair with
    ⟨q, hqU, _hqPair, hqTriple⟩
  exact ⟨q, hqU, not_mem_tripleBadUnion_of_noTripleCarrierPoints hqTriple⟩

/-- The complement of the triple-contact bad locus is dense in every finite
arrangement parameter space.

This is the remaining concrete finite-avoidance fact needed for the lower
genericization argument.  The nonparallel-stem complement is already proved
open dense in `Lower.GenericityPort.dense_compl_parallelBadUnion`. -/
theorem dense_compl_tripleBadUnion (n : ℕ) :
    Dense
      ((Lower.GenericityPort.tripleBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  by_cases hn : n < 3
  · exact dense_compl_tripleBadUnion_of_lt_three hn
  · exact dense_compl_tripleBadUnion_ge_three n (by omega)

/-- The reduced chamber-bad locus is avoidable.

This combines the remaining triple-contact density target with the existing
open dense nonparallel-stem theorem. -/
theorem dense_compl_chamberBadUnion (n : ℕ) :
    Dense
      ((Lower.GenericityPort.chamberBadUnion :
        Set (Lower.ArrangementParameter n))ᶜ) := by
  have hparallelDense :
      Dense
        ((Lower.GenericityPort.parallelBadUnion :
          Set (Lower.ArrangementParameter n))ᶜ) :=
    Lower.GenericityPort.dense_compl_parallelBadUnion
  have hparallelOpen :
      IsOpen
        ((Lower.GenericityPort.parallelBadUnion :
          Set (Lower.ArrangementParameter n))ᶜ) :=
    Lower.GenericityPort.isOpen_compl_parallelBadUnion
  have htp :
      Dense
        (((Lower.GenericityPort.parallelBadUnion :
            Set (Lower.ArrangementParameter n))ᶜ) ∩
          ((Lower.GenericityPort.tripleBadUnion :
            Set (Lower.ArrangementParameter n))ᶜ)) :=
    hparallelDense.inter_of_isOpen_left
      (dense_compl_tripleBadUnion n) hparallelOpen
  simpa [Lower.GenericityPort.chamberBadUnion, Set.compl_union,
    Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using htp

/-- Every finite strict pair chamber contains a generic arrangement.

This is the all-`n` concrete finite-avoidance theorem needed by the lower
construction after topology supplies the generic Euler equality. -/
theorem chamberGenericityAvoidance_all :
    ∀ n : ℕ, Lower.GenericityPort.ChamberGenericityAvoidance n := by
  intro n
  exact { dense_good := dense_compl_chamberBadUnion n }

theorem chamberGenericityAvoidance (n : ℕ) :
    Lower.GenericityPort.ChamberGenericityAvoidance n :=
  chamberGenericityAvoidance_all n

end Genericity
end MainTheorem
end EndToEnd
end Concrete
end Lollipop
