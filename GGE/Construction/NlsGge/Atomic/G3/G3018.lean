import Mathlib
import NlsGge.Atomic.G3.G3InitialHost
import NlsGge.Atomic.G3.G3007
import NlsGge.Atomic.G3.G3009
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G3.G3S1Support

                                                                                                              
                                                                                                                     
                                                                                                                      
                                                                                                                           
                                                                                                                    
                                                                                                                      
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Borel measurability of the standard root in its spectral variable (Complex.sqrt = a ^ (2⁻¹)). -/
theorem g3018_stdRoot_measurable (τ g : ℂ) : Measurable (fun z : ℂ => stdRoot38 τ g z) := by
  unfold stdRoot38
  have hsq : Measurable (fun a : ℂ => Complex.sqrt a) := by
    unfold Complex.sqrt
    exact measurable_id.pow_const _
  have hden : Measurable (fun z : ℂ => (τ - z) ^ 2) :=
    (measurable_const.sub measurable_id).pow_const 2
  have hq : Measurable (fun z : ℂ => g / 4 / (τ - z) ^ 2) :=
    measurable_const.div hden
  exact (measurable_const.sub measurable_id).mul (hsq.comp (measurable_const.sub hq))

theorem g3018_rpow_neg_half {t : ℝ} (ht : 0 < t) : t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹ := by
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]

theorem g3018_alg (C9 q Z s p x : ℝ) (hs : 0 < s) (hp : 0 < p) (hxs : x = s * s) :
    C9 * q / (p * s) * Z * x = C9 * Z * (q * s) / p := by
  subst hxs
  have hs' : s ≠ 0 := hs.ne'
  have hp' : p ≠ 0 := hp.ne'
  field_simp

/-- Pointwise bound on the segment density: ‖ratio‖ ‖zeta‖ ‖omega‖ ≤ K t^(-1/2), with K uniform. -/
theorem g3018_real_bound {ρ z x g t C9 Z W K : ℝ} (hz0 : 0 ≤ z) (hz : z ≤ Z) (hx : 0 < x)
    (hxW : x ≤ W) (hg1 : g ≤ 1) (hC9 : 0 ≤ C9) (hZ : 0 ≤ Z) (ht : 0 < t)
    (hρ : ρ ≤ C9 * Real.sqrt (g + x) / (Real.sqrt t * Real.sqrt x))
    (hK : K = C9 * Real.sqrt (1 + W) * Real.sqrt W * Z) :
    ρ * z * x ≤ K * (Real.sqrt t)⁻¹ := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hp : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hxs : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx.le).symm
  have hq : Real.sqrt (g + x) ≤ Real.sqrt (1 + W) := Real.sqrt_le_sqrt (by linarith)
  have hsW : Real.sqrt x ≤ Real.sqrt W := Real.sqrt_le_sqrt hxW
  have hQ0 : 0 ≤ Real.sqrt (1 + W) := Real.sqrt_nonneg _
  have hq0 : 0 ≤ Real.sqrt (g + x) := Real.sqrt_nonneg _
  have hqs : Real.sqrt (g + x) * Real.sqrt x ≤ Real.sqrt (1 + W) * Real.sqrt W :=
    mul_le_mul hq hsW hs.le hQ0
  have hA : 0 ≤ C9 * Z := mul_nonneg hC9 hZ
  have hstep1 : ρ * z ≤ C9 * Real.sqrt (g + x) / (Real.sqrt t * Real.sqrt x) * Z :=
    mul_le_mul hρ hz hz0 (div_nonneg (mul_nonneg hC9 hq0) (mul_pos hp hs).le)
  have hstep2 : ρ * z * x ≤ C9 * Real.sqrt (g + x) / (Real.sqrt t * Real.sqrt x) * Z * x :=
    mul_le_mul_of_nonneg_right hstep1 hx.le
  have heq : C9 * Real.sqrt (g + x) / (Real.sqrt t * Real.sqrt x) * Z * x =
      C9 * Z * (Real.sqrt (g + x) * Real.sqrt x) / Real.sqrt t :=
    g3018_alg C9 (Real.sqrt (g + x)) Z (Real.sqrt x) (Real.sqrt t) x hs hp hxs
  have hstep3 : C9 * Z * (Real.sqrt (g + x) * Real.sqrt x) / Real.sqrt t ≤
      C9 * Z * (Real.sqrt (1 + W) * Real.sqrt W) / Real.sqrt t :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqs hA) hp.le
  calc ρ * z * x ≤ C9 * Real.sqrt (g + x) / (Real.sqrt t * Real.sqrt x) * Z * x := hstep2
    _ = C9 * Z * (Real.sqrt (g + x) * Real.sqrt x) / Real.sqrt t := heq
    _ ≤ C9 * Z * (Real.sqrt (1 + W) * Real.sqrt W) / Real.sqrt t := hstep3
    _ = K * (Real.sqrt t)⁻¹ := by rw [hK]; ring

/-- Integral of t^(-1/2) from 0 to ε is 2 √ε (integrability on [0, ε] comes from `intervalIntegrable_rpow'`). -/
theorem g3018_integral_rpow (ε : ℝ) :
    ∫ t in (0 : ℝ)..ε, t ^ (-(1 / 2 : ℝ)) = 2 * Real.sqrt ε := by
  rw [integral_rpow (r := -(1 / 2 : ℝ)) (Or.inl (by norm_num))]
  rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by norm_num,
    Real.zero_rpow (show (1 / 2 : ℝ) ≠ 0 by norm_num), Real.sqrt_eq_rpow]
  ring

theorem G3_018 (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hseq : CollapsingOffEndpointSequence m v φ0) :
  ∃ C d : ℝ, ∃ J : ℕ, 0 < C ∧ 0 < d ∧
    ∀ j : ℕ, J ≤ j →
      d ≤ ‖betaOmega m (v j)‖ ∧
      IntervalIntegrable (betaSegmentDensity n m (v j)) volume 0 1 ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1,
        ‖betaInitialSegment n m (v j) ε‖ ≤ C*Real.sqrt ε := by
  obtain ⟨⟨hcoll, hnot⟩, hv, hmem⟩ := hseq
  have hφ0 : φ0 ∈ sourceW := hcoll.1
  have hgap0 : gamma2 φ0 m = 0 := hcoll.2
  have hω0 : betaOmega m φ0 ≠ 0 := g3s1_omega_ne m φ0 hφ0 hnot
  have hw0 : 0 < ‖betaOmega m φ0‖ := norm_pos_iff.2 hω0
  obtain ⟨V7, C7, hV7o, hφV7, -, -, hA7⟩ := G3_007 φ0 hφ0
  obtain ⟨V9, C9, hV9o, hφV9, -, hC9pos, hA9⟩ := G3_009 φ0 hφ0
  -- eventual membership and uniform size bounds along the sequence
  have hEV7 : ∀ᶠ j in atTop, v j ∈ V7 := hv.eventually (hV7o.mem_nhds hφV7)
  have hEV9 : ∀ᶠ j in atTop, v j ∈ V9 := hv.eventually (hV9o.mem_nhds hφV9)
  have hωt : Tendsto (fun j => ‖betaOmega m (v j)‖) atTop (𝓝 ‖betaOmega m φ0‖) :=
    (g3s1_omega_tendsto v φ0 m hφ0 hgap0 hv).norm
  have hgt : Tendsto (fun j => ‖gap (v j) m‖) atTop (𝓝 0) := by
    have h := (g3s1_gap_tendsto v φ0 m hφ0 hgap0 hv).norm
    rwa [norm_zero] at h
  have hgE : ∀ᶠ j in atTop, ‖gap (v j) m‖ < 1 := hgt.eventually_lt_const one_pos
  have hωlo : ∀ᶠ j in atTop, ‖betaOmega m φ0‖ / 2 < ‖betaOmega m (v j)‖ :=
    hωt.eventually_const_lt (show ‖betaOmega m φ0‖ / 2 < ‖betaOmega m φ0‖ by linarith)
  have hωhi : ∀ᶠ j in atTop, ‖betaOmega m (v j)‖ < ‖betaOmega m φ0‖ + 1 :=
    hωt.eventually_lt_const (show ‖betaOmega m φ0‖ < ‖betaOmega m φ0‖ + 1 by linarith)
  have hall : ∀ᶠ j in atTop, v j ∈ V7 ∧ v j ∈ V9 ∧ ‖gap (v j) m‖ < 1 ∧
      ‖betaOmega m φ0‖ / 2 < ‖betaOmega m (v j)‖ ∧ ‖betaOmega m (v j)‖ < ‖betaOmega m φ0‖ + 1 :=
    hEV7.and (hEV9.and (hgE.and (hωlo.and hωhi)))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hall
  -- uniform constants
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ‖betaOmega m φ0‖ + 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = |C7 * Lib.c3w n m| := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Z := by rw [hZdef]; exact abs_nonneg _
  have hW0 : 0 ≤ W := by rw [hW]; linarith
  obtain ⟨K, hK0, hK⟩ : ∃ K : ℝ, 0 ≤ K ∧ K = C9 * Real.sqrt (1 + W) * Real.sqrt W * Z :=
    ⟨C9 * Real.sqrt (1 + W) * Real.sqrt W * Z,
      mul_nonneg (mul_nonneg (mul_nonneg hC9pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) hZ0, rfl⟩
  refine ⟨2 * K + 1, ‖betaOmega m φ0‖ / 2, J, by linarith, half_pos hw0, fun j hj => ?_⟩
  obtain ⟨hVj7, hVj9, hgj, hωlo_j, hωhi_j⟩ := hJ j hj
  have hωpos : 0 < ‖betaOmega m (v j)‖ := by linarith
  have hω_ne : betaOmega m (v j) ≠ 0 := norm_pos_iff.1 hωpos
  have hxWj : ‖betaOmega m (v j)‖ ≤ W := by rw [hW]; exact hωhi_j.le
  have hnear : ‖muSeq (v j) m - lamMinus (v j) m‖ ≤ ‖muSeq (v j) m - lamPlus (v j) m‖ :=
    (hmem j).2
  -- zeta: analyticity on the isolating ball and a uniform bound along the segment
  obtain ⟨hfam, hA⟩ := hA7 (v j) hVj7
  obtain ⟨_, _, _, hspec⟩ := hfam
  obtain ⟨hanal, hbnd⟩ := hA n m hmn
  have hsegc : Continuous (fun t : ℝ => betaSegmentPoint m (v j) t) := by
    unfold betaSegmentPoint
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hζc : ContinuousOn (fun t : ℝ => betaZeta n m (v j) (betaSegmentPoint m (v j) t))
      (Icc (0 : ℝ) 1) :=
    hanal.continuousOn.comp hsegc.continuousOn
      (fun t ht => g3m2_seg_mem (discC φ0) (discR φ0) m (v j) hspec t ht)
  have hζb : ∀ t ∈ Icc (0 : ℝ) 1, ‖betaZeta n m (v j) (betaSegmentPoint m (v j) t)‖ ≤ Z := by
    intro t ht
    have h1 := hbnd _ (g3m2_seg_mem (discC φ0) (discR φ0) m (v j) hspec t ht)
    rw [hZdef]
    exact h1.trans (le_abs_self _)
  -- measurability of the density on (0,1]: Borel measurable root factor, continuous zeta factor
  have hstdM : Measurable (fun t : ℝ => standardRoot (v j) m (betaSegmentPoint m (v j) t)) :=
    (g3018_stdRoot_measurable (tauN (v j) m) (gamma2 (v j) m)).comp hsegc.measurable
  have hnumC : Measurable (fun t : ℝ => normalizedRoot n m (v j) - betaSegmentPoint m (v j) t) :=
    measurable_const.sub hsegc.measurable
  have hratM : Measurable (fun t : ℝ => betaRootRatioAlong n m (v j) t) := by
    unfold betaRootRatioAlong
    exact hnumC.div hstdM
  have hmeasI : AEStronglyMeasurable (fun t : ℝ => betaSegmentDensity n m (v j) t)
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun t : ℝ => betaRootRatioAlong n m (v j) t)
        (volume.restrict (Icc (0 : ℝ) 1)) := hratM.aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun t : ℝ => betaZeta n m (v j) (betaSegmentPoint m (v j) t))
        (volume.restrict (Icc (0 : ℝ) 1)) := hζc.aestronglyMeasurable measurableSet_Icc
    have h3 : AEStronglyMeasurable
        (fun t : ℝ => betaRootRatioAlong n m (v j) t * betaZeta n m (v j) (betaSegmentPoint m (v j) t))
        (volume.restrict (Icc (0 : ℝ) 1)) := h1.mul h2
    exact h3.mul aestronglyMeasurable_const
  have hsub : Set.uIoc (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [Set.uIoc_of_le zero_le_one]
    exact Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable (fun t : ℝ => betaSegmentDensity n m (v j) t)
      (volume.restrict (Set.uIoc (0 : ℝ) 1)) :=
    hmeasI.mono_set hsub
  -- pointwise bound on (0,1) with the uniform constant K
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1, ‖betaSegmentDensity n m (v j) t‖ ≤ K * t ^ (-(1 / 2 : ℝ)) := by
    intro t ht
    obtain ⟨_, hrat⟩ := hA9 (v j) hVj9 n m hmn hnear hω_ne t ht
    have ht0 : 0 < t := ht.1
    have hdens : ‖betaSegmentDensity n m (v j) t‖ =
        ‖betaRootRatioAlong n m (v j) t‖ * ‖betaZeta n m (v j) (betaSegmentPoint m (v j) t)‖ *
          ‖betaOmega m (v j)‖ := by
      unfold betaSegmentDensity
      rw [norm_mul, norm_mul]
    rw [hdens, g3018_rpow_neg_half ht0]
    exact g3018_real_bound (norm_nonneg _) (hζb t (Ioo_subset_Icc_self ht)) hωpos hxWj
      (le_of_lt hgj) hC9pos.le hZ0 ht0 hrat hK
  -- integrability: the bound K t^(-1/2) is integrable on (0,1) (proved before any integral identity)
  have hgint : IntervalIntegrable (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(1 / 2))).const_mul K
  have hae1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 :=
    (measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := (1 : ℝ)))).mono
      fun t ht h => ht (by rw [h]; exact Set.mem_singleton 1)
  have hae2 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioc (0 : ℝ) 1 →
      ‖betaSegmentDensity n m (v j) t‖ ≤ K * t ^ (-(1 / 2 : ℝ)) :=
    hae1.mono fun t ht hI => hpt t ⟨hI.1, lt_of_le_of_ne hI.2 ht⟩
  have hintg : IntervalIntegrable (fun t : ℝ => betaSegmentDensity n m (v j) t) volume 0 1 := by
    refine IntervalIntegrable.mono_fun' hgint hmeas ?_
    rw [Set.uIoc_of_le zero_le_one]
    exact (ae_restrict_iff' measurableSet_Ioc).2 hae2
  refine ⟨le_of_lt hωlo_j, hintg, fun ε hε => ?_⟩
  -- the initial segment estimate
  have hε0 : 0 ≤ ε := hε.1.le
  have hbd : IntervalIntegrable (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) volume 0 ε := by
    apply IntervalIntegrable.mono_set hgint
    rw [Set.uIcc_of_le hε0, Set.uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hε.2.le
  have hae3 : ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) ε)),
      ‖betaSegmentDensity n m (v j) t‖ ≤ K * t ^ (-(1 / 2 : ℝ)) := by
    rw [Set.uIoc_of_le hε0]
    exact (ae_restrict_iff' measurableSet_Ioc).2
      (ae_of_all _ fun t ht => hpt t ⟨ht.1, lt_of_le_of_lt ht.2 hε.2⟩)
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hae3 hbd
  have hI : ∫ t in (0 : ℝ)..ε, K * t ^ (-(1 / 2 : ℝ)) = K * (2 * Real.sqrt ε) := by
    rw [intervalIntegral.integral_const_mul, g3018_integral_rpow]
  have hdef : betaInitialSegment n m (v j) ε = ∫ t in (0 : ℝ)..ε, betaSegmentDensity n m (v j) t :=
    rfl
  rw [hdef]
  calc ‖∫ t in (0 : ℝ)..ε, betaSegmentDensity n m (v j) t‖
      ≤ |∫ t in (0 : ℝ)..ε, K * t ^ (-(1 / 2 : ℝ))| := hnorm
    _ = K * (2 * Real.sqrt ε) := by
      rw [hI, abs_of_nonneg (mul_nonneg hK0 (mul_nonneg two_pos.le (Real.sqrt_nonneg ε)))]
    _ ≤ (2 * K + 1) * Real.sqrt ε := by nlinarith [Real.sqrt_nonneg ε]

end
end NlsGge.GKDefinitionDesign
