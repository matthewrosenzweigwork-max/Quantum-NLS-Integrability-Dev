import NlsGge.Spectral.ActualQuasimomentumEndpointSqrtE02_38
set_option autoImplicit false
noncomputable section
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot Filter Topology

theorem actualQuasimomentum_sub_sq_le_of_tendsto_E02_38 (u : PhysicalL2) (m : ℤ) (a : ℝ)
    (ha : actualPhysicalUnitHalfTrace32 u a = (Real.cos (m*Real.pi) : ℂ))
    (hlim : Tendsto (actualQuasimomentumE02_38 u) (𝓝[{z : ℂ | 0 < z.im}] (a:ℂ))
      (𝓝 ((m:ℂ)*Real.pi))) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, 0 < z.im → ‖z - a‖ < r →
      ‖actualQuasimomentumE02_38 u z - m*Real.pi‖^2 ≤ C * ‖z - a‖ := by
  have hdiff : AnalyticAt ℂ (actualPhysicalUnitHalfTrace32 u) (a : ℂ) :=
    analyticOnNhd_actualPhysicalUnitHalfTrace32 u _ (Set.mem_univ _)
  have hC1 : ContDiffAt ℝ 1 (actualPhysicalUnitHalfTrace32 u) (a : ℂ) :=
    ((hdiff.contDiffAt (n := 1)).restrict_scalars ℝ)
  obtain ⟨K, t, ht, hK⟩ := hC1.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (a:ℂ),
      dist (actualQuasimomentumE02_38 u z) ((m:ℂ)*Real.pi) < 1/2 :=
    (Metric.tendsto_nhds.mp hlim) (1/2) (by norm_num)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨8 * (K : ℝ), min ε δ, lt_min hε hδ, ?_⟩
  intro z hz hza
  have hza1 : ‖z - a‖ < ε := lt_of_lt_of_le hza (min_le_left _ _)
  have hza2 : ‖z - a‖ < δ := lt_of_lt_of_le hza (min_le_right _ _)
  have hzt : z ∈ t := hεt (by simpa [Metric.mem_ball, dist_eq_norm] using hza1)
  have hat : (a : ℂ) ∈ t := hεt (Metric.mem_ball_self hε)
  have hLip : ‖actualPhysicalUnitHalfTrace32 u z - actualPhysicalUnitHalfTrace32 u a‖ ≤
      K * ‖z - a‖ := by
    have := hK.norm_sub_le hzt hat
    simpa using this
  have hk : dist (actualQuasimomentumE02_38 u z) ((m:ℂ)*Real.pi) < 1/2 :=
    hδs ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hza2, hz⟩
  set k := actualQuasimomentumE02_38 u z with hkdef
  have e : ((m * Real.pi : ℝ) : ℂ) = (m : ℂ) * (Real.pi : ℂ) := by push_cast; ring
  have hw : ‖k - ((m * Real.pi : ℝ) : ℂ)‖ ≤ 1 := by
    rw [e]; rw [dist_eq_norm] at hk; linarith
  have hcos := (isActualQuasimomentumBranch_actualQuasimomentumE02_38 u).2.1 z hz
  have hsin : Complex.sin ((m * Real.pi : ℝ) : ℂ) = 0 := by
    rw [← Complex.ofReal_sin]
    have : Real.sin (m * Real.pi) = 0 := Real.sin_int_mul_pi m
    simp [this]
  have hcw : Complex.cos (k - ((m * Real.pi : ℝ) : ℂ)) =
      actualPhysicalUnitHalfTrace32 u z * (Real.cos (m * Real.pi) : ℂ) := by
    rw [Complex.cos_sub, hsin, mul_zero, add_zero]
    rw [show Complex.cos k = actualPhysicalUnitHalfTrace32 u z from hcos]
    rw [← Complex.ofReal_cos]
  have hcsq : (Real.cos (m * Real.pi) : ℂ) * (Real.cos (m * Real.pi) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← sq, Real.cos_sq', Real.sin_int_mul_pi]
    simp
  have h1c : 1 - Complex.cos (k - ((m * Real.pi : ℝ) : ℂ)) =
      (actualPhysicalUnitHalfTrace32 u a - actualPhysicalUnitHalfTrace32 u z) *
        (Real.cos (m * Real.pi) : ℂ) := by
    rw [hcw, ha]
    linear_combination (-1 : ℂ) * hcsq
  have hnc : ‖(Real.cos (m * Real.pi) : ℂ)‖ = 1 := by
    have : ‖(Real.cos (m * Real.pi) : ℂ)‖ ^ 2 = 1 := by
      rw [sq, ← norm_mul, hcsq]; simp
    nlinarith [norm_nonneg (Real.cos (m * Real.pi) : ℂ)]
  have hmain := complex_norm_sq_le_eight_norm_one_sub_cos_E02_38 _ hw
  rw [h1c, norm_mul, hnc, mul_one,
    norm_sub_rev (actualPhysicalUnitHalfTrace32 u (a : ℂ))] at hmain
  rw [e] at hmain
  have hL : ‖actualPhysicalUnitHalfTrace32 u z - actualPhysicalUnitHalfTrace32 u (a : ℂ)‖ ≤
      (K : ℝ) * ‖z - (a : ℂ)‖ := hLip
  calc _ ≤ _ := hmain
    _ ≤ 8 * ((K : ℝ) * ‖z - (a : ℂ)‖) := by linarith
    _ = 8 * (K : ℝ) * ‖z - (a : ℂ)‖ := by ring


end NlsGge.SpectralFoundations
