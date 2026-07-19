/- Copyright (c) 2025 LARA, EPFL. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LARA, EPFL -/

import old_lean_folder.JordanCurveTheorem.SectionJ_PathConnectivity
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Section K: Analysis Infrastructure

Thin wrappers for the set-distance facts used by the Jordan-curve development.
-/

open Set Topology Metric

noncomputable section

/-- The distance between two sets, defined as the infimum of pairwise distances. -/
def setDist (K K' : Set E2') : ℝ :=
  sInf {r | ∃ p ∈ K, ∃ p' ∈ K', r = dist p p'}

/-- The set distance is a lower bound on every pairwise distance. -/
theorem setDist_le_dist {K K' : Set E2'} {p p' : E2'}
    (hp : p ∈ K) (hp' : p' ∈ K') : setDist K K' ≤ dist p p' :=
  csInf_le
    ⟨0, fun _ ⟨_, _, _, _, hr⟩ => hr ▸ dist_nonneg⟩
    ⟨p, hp, p', hp', rfl⟩

/-- Set distance is nonnegative for nonempty sets. -/
theorem setDist_nonneg {K K' : Set E2'}
    (hK : K.Nonempty) (hK' : K'.Nonempty) : 0 ≤ setDist K K' := by
  obtain ⟨p, hp⟩ := hK
  obtain ⟨p', hp'⟩ := hK'
  unfold setDist
  exact le_csInf
    ⟨dist p p', p, hp, p', hp', rfl⟩
    (fun _ ⟨_, _, _, _, hr⟩ => hr ▸ dist_nonneg)

/-- Distance between two compact nonempty sets is attained. -/
theorem compact_distance {K K' : Set E2'}
    (hK : IsCompact K) (hK' : IsCompact K')
    (hKne : K.Nonempty) (hK'ne : K'.Nonempty) :
    ∃ p ∈ K, ∃ p' ∈ K', setDist K K' = dist p p' := by
  have hcont_inf : ContinuousOn (fun p => infDist p K') K :=
    (continuous_infDist_pt K').continuousOn
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hKne hcont_inf
  obtain ⟨p', hp', hd⟩ := hK'.exists_infDist_eq_dist hK'ne p
  refine ⟨p, hp, p', hp', le_antisymm (setDist_le_dist hp hp') ?_⟩
  unfold setDist
  apply le_csInf
  · exact ⟨dist p p', p, hp, p', hp', rfl⟩
  rintro _ ⟨q, hq, q', hq', rfl⟩
  calc
    dist p p' = infDist p K' := hd.symm
    _ ≤ infDist q K' := hpmin hq
    _ ≤ dist q q' := infDist_le_dist_of_mem hq'

/-- A minimizing pair for the distance between two compact nonempty sets. -/
theorem setDist_eq_dist_of_compact {K K' : Set E2'}
    (hK : IsCompact K) (hK' : IsCompact K')
    (hKne : K.Nonempty) (hK'ne : K'.Nonempty) :
    ∃ p ∈ K, ∃ p' ∈ K', ∀ q ∈ K, ∀ q' ∈ K', dist p p' ≤ dist q q' := by
  obtain ⟨p, hp, p', hp', heq⟩ := compact_distance hK hK' hKne hK'ne
  exact ⟨p, hp, p', hp', fun q hq q' hq' => heq ▸ setDist_le_dist hq hq'⟩

/-- A connected subset of `ℝ` contains every interval between two of its points. -/
theorem connected_Icc_subset {S : Set ℝ} (hS : IsConnected S)
    {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) : Icc a b ⊆ S :=
  hS.isPreconnected.Icc_subset ha hb

end
