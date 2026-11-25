import Mathlib
import NlsGge.Atomic.G3.G3007
import NlsGge.Atomic.G3.G3018
import NlsGge.Atomic.G3.G3021NearBase
import NlsGge.Atomic.G3.G3021NearRatio

/- G3-021 supporting module NEARINITIAL (proof development, AUTHOR; not self-reviewed; NOT the G3_021 head).
   Target NlsGge/Atomic/G3/G3021NearInitial.lean, namespace NlsGge.GKDefinitionDesign.
   Generic form of landed G3_018 for the segment from the NEARER endpoint: the proof is the proof of G3_018 with
   betaOmega/betaSegmentPoint/betaRootRatioAlong/betaSegmentDensity replaced by nearOmega/nearSegPoint/nearRatio/nearDensity,
   the ratio bound G3_009 replaced by near_ratio_bound (no nearness hypothesis is needed because it holds by construction),
   and the sequence hypothesis weakened to what the proof uses (collapsed off-endpoint limit, convergence).
   Reuses G3_007 (zeta analyticity and bound on the isolating ball) and the g3018_* helper lemmas. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem near_initial_bound (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hcoll : φ0 ∈ collapsedSet m) (hnot : φ0 ∉ endpointSet m)
    (hv : Tendsto v atTop (𝓝 φ0)) :
  ∃ C d : ℝ, ∃ J : ℕ, 0 < C ∧ 0 < d ∧
    ∀ j : ℕ, J ≤ j →
      d ≤ ‖nearOmega m (v j)‖ ∧
      IntervalIntegrable (nearDensity n m (v j)) volume 0 1 ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        ‖∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t‖ ≤ C * Real.sqrt ε := by
  have hφ0 : φ0 ∈ sourceW := hcoll.1
  have hgap0 : gamma2 φ0 m = 0 := hcoll.2
  have hω0 : nearOmega m φ0 ≠ 0 := G3021N.omega_ne m φ0 hφ0 hnot
  have hw0 : 0 < ‖nearOmega m φ0‖ := norm_pos_iff.2 hω0
  have hω0v : nearOmega m φ0 = muSeq φ0 m - tauN φ0 m := by
    unfold nearOmega; rw [G3021N.near_collapsed_value m φ0 hφ0 hgap0]
  obtain ⟨V7, C7, hV7o, hφV7, -, -, hA7⟩ := G3_007 φ0 hφ0
  obtain ⟨V9, C9, hV9o, hφV9, -, hC9pos, hA9⟩ := near_ratio_bound φ0 hφ0
  have hEV7 : ∀ᶠ j in atTop, v j ∈ V7 := hv.eventually (hV7o.mem_nhds hφV7)
  have hEV9 : ∀ᶠ j in atTop, v j ∈ V9 := hv.eventually (hV9o.mem_nhds hφV9)
  have hωt : Tendsto (fun j => ‖nearOmega m (v j)‖) atTop (𝓝 ‖nearOmega m φ0‖) := by
    have h := (G3021N.omega_tendsto m v φ0 hφ0 hgap0 hv).norm
    rwa [← hω0v] at h
  have hgt : Tendsto (fun j => ‖gap (v j) m‖) atTop (𝓝 0) := by
    have h := (g3s1_gap_tendsto v φ0 m hφ0 hgap0 hv).norm
    rwa [norm_zero] at h
  have hgE : ∀ᶠ j in atTop, ‖gap (v j) m‖ < 1 := hgt.eventually_lt_const one_pos
  have hωlo : ∀ᶠ j in atTop, ‖nearOmega m φ0‖ / 2 < ‖nearOmega m (v j)‖ :=
    hωt.eventually_const_lt (show ‖nearOmega m φ0‖ / 2 < ‖nearOmega m φ0‖ by linarith)
  have hωhi : ∀ᶠ j in atTop, ‖nearOmega m (v j)‖ < ‖nearOmega m φ0‖ + 1 :=
    hωt.eventually_lt_const (show ‖nearOmega m φ0‖ < ‖nearOmega m φ0‖ + 1 by linarith)
  have hall : ∀ᶠ j in atTop, v j ∈ V7 ∧ v j ∈ V9 ∧ ‖gap (v j) m‖ < 1 ∧
      ‖nearOmega m φ0‖ / 2 < ‖nearOmega m (v j)‖ ∧ ‖nearOmega m (v j)‖ < ‖nearOmega m φ0‖ + 1 :=
    hEV7.and (hEV9.and (hgE.and (hωlo.and hωhi)))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hall
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ‖nearOmega m φ0‖ + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = |C7 * Lib.c3w n m| := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact abs_nonneg _
  have hW0 : 0 ≤ W := by rw [hW]; linarith
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ K = C9 * Real.sqrt (1 + W) * Real.sqrt W * Z :=
    ⟨C9 * Real.sqrt (1 + W) * Real.sqrt W * Z,
      mul_nonneg (mul_nonneg (mul_nonneg hC9pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hZ0, rfl⟩
  refine ⟨2 * K + 1, ‖nearOmega m φ0‖ / 2, J, by linarith, half_pos hw0, fun j hj => ?_⟩
  obtain ⟨hVj7, hVj9, hgj, hωlo_j, hωhi_j⟩ := hJ j hj
  have hωpos : 0 < ‖nearOmega m (v j)‖ := by linarith
  have hω_ne : nearOmega m (v j) ≠ 0 := norm_pos_iff.1 hωpos
  have hxWj : ‖nearOmega m (v j)‖ ≤ W := by rw [hW]; exact hωhi_j.le
  obtain ⟨hfam, hA⟩ := hA7 (v j) hVj7
  obtain ⟨_, _, _, hspec⟩ := hfam
  obtain ⟨hanal, hbnd⟩ := hA n m hmn
  have hsegc : Continuous (fun t : ℝ => nearSegPoint m (v j) t) := G3021N.seg_continuous m (v j)
  have hζc : ContinuousOn (fun t : ℝ => betaZeta n m (v j) (nearSegPoint m (v j) t))
      (Icc (0 : ℝ) 1) :=
    hanal.continuousOn.comp hsegc.continuousOn
      (fun t ht => G3021N.seg_mem (C := discC φ0) (R := discR φ0) m (v j) hspec t ht)
  have hζb : ∀ t ∈ Icc (0 : ℝ) 1, ‖betaZeta n m (v j) (nearSegPoint m (v j) t)‖ ≤ Z := by
    intro t ht
    have h1 := hbnd _ (G3021N.seg_mem (C := discC φ0) (R := discR φ0) m (v j) hspec t ht)
    rw [hZdef]
    exact h1.trans (le_abs_self _)
  have hstdM : Measurable (fun t : ℝ => standardRoot (v j) m (nearSegPoint m (v j) t)) :=
    (g3018_stdRoot_measurable (tauN (v j) m) (gamma2 (v j) m)).comp hsegc.measurable
  have hnumC : Measurable (fun t : ℝ => normalizedRoot n m (v j) - nearSegPoint m (v j) t) :=
    measurable_const.sub hsegc.measurable
  have hratM : Measurable (fun t : ℝ => nearRatio n m (v j) t) := by
    unfold nearRatio
    exact hnumC.div hstdM
  have hmeasI : AEStronglyMeasurable (fun t : ℝ => nearDensity n m (v j) t)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => nearRatio n m (v j) t)
        (volume.restrict (Icc (0 : ℝ) 1)) := hratM.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ => betaZeta n m (v j) (nearSegPoint m (v j) t))
        (volume.restrict (Icc (0 : ℝ) 1)) := hζc.aestronglyMeasurable measurableSet_Icc
    have h3 : AEStronglyMeasurable
        (fun t : ℝ => nearRatio n m (v j) t * betaZeta n m (v j) (nearSegPoint m (v j) t))
        (volume.restrict (Icc (0 : ℝ) 1)) := h1.mul h2
    exact h3.mul aestronglyMeasurable_const
  have hsub : Set.uIoc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable (fun t : ℝ => nearDensity n m (v j) t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    hmeasI.mono_set hsub
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ‖nearDensity n m (v j) t‖ ≤ K * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    obtain ⟨_, hrat⟩ := hA9 (v j) hVj9 n m hmn hω_ne t ht
    have ht0 : 0 < t := ht.1
    have hdens : ‖nearDensity n m (v j) t‖ =
        ‖nearRatio n m (v j) t‖ * ‖betaZeta n m (v j) (nearSegPoint m (v j) t)‖ *
          ‖nearOmega m (v j)‖ := by
      unfold nearDensity
      rw [norm_mul, norm_mul]
    rw [hdens, g3018_rpow_neg_half ht0]
    exact g3018_real_bound (norm_nonneg _) (hζb t (Ioo_subset_Icc_self ht)) hωpos hxWj
      (le_of_lt hgj) hC9pos.le hZ0 ht0 hrat hK
  have hgint : IntervalIntegrable (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul K
  have hae1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 :=
    (measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := (1 : ℝ)))).mono
      fun t ht h => ht (by rw [h]; exact Set.mem_singleton 1)
  have hae2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc (0 : ℝ) 1 →
      ‖nearDensity n m (v j) t‖ ≤ K * t ^ (-(1 / 2 : ℝ)) :=
    hae1.mono fun t ht hI => hpt t ⟨hI.1, lt_of_le_of_ne hI.2 ht⟩
  have hintg : IntervalIntegrable (fun t : ℝ => nearDensity n m (v j) t) volume 0 1 := by
    refine IntervalIntegrable.mono_fun' hgint hmeas ?_
    rw [Set.uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae2
  refine ⟨le_of_lt hωlo_j, hintg, fun ε hε => ?_⟩
  have hε0 : 0 ≤ ε := hε.1.le
  have hbd : IntervalIntegrable (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) volume 0 ε := by
    apply IntervalIntegrable.mono_set hgint
    rw [Set.uIcc_of_le hε0, Set.uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hε.2.le
  have hae3 : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) ε)),
      ‖nearDensity n m (v j) t‖ ≤ K * t ^ (-(1 / 2 : ℝ)) := by
    rw [Set.uIoc_of_le hε0]
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun t ht => hpt t ⟨ht.1, lt_of_le_of_lt ht.2 hε.2⟩)
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hae3 hbd
  have hI : ∫ t in (0 : ℝ)..ε, K * t ^ (-(1 / 2 : ℝ)) = K * (2 * Real.sqrt ε) := by
    rw [intervalIntegral.integral_const_mul, g3018_integral_rpow]
  calc ‖∫ t in (0 : ℝ)..ε, nearDensity n m (v j) t‖
      ≤ |∫ t in (0 : ℝ)..ε, K * t ^ (-(1 / 2 : ℝ))| := hnorm
    _ = K * (2 * Real.sqrt ε) := by
      rw [hI, abs_of_nonneg (mul_nonneg hK0 (mul_nonneg two_pos.le (Real.sqrt_nonneg ε)))]
    _ ≤ (2 * K + 1) * Real.sqrt ε := by nlinarith [Real.sqrt_nonneg ε]

end
end NlsGge.GKDefinitionDesign
