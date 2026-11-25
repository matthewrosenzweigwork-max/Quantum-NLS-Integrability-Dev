import NlsGge.GK38.TauGammaDenominator
import NlsGge.GK38.TauGammaAnalyticProbe
import NlsGge.GK38.TauGammaSincBounds
import NlsGge.GK38.PeriodicLabellingProbe

/-! All-index free and genuinely nonzero complex triangular collapsed-gap regressions. -/
set_option autoImplicit false
open Filter Topology Set Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem tauGamma_free_values38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (n : ℤ) :
    tauN38 C R 0 n = (n : ℂ) * (Real.pi : ℂ) ∧ gamma2N38 C R 0 n = 0 ∧
      lamDot 0 n = tauN38 C R 0 n ∧ criticalDenominator38 C R 0 n ≠ 0 := by
  have hw : (0 : PotPair) ∈ gkW := by simpa only [realSlice_zero] using realSlice_mem_gkW 0
  have ht := tau_pair_mean38 C R hsel 0 hw n
  have hg := gamma2_pair_gap38 C R hsel 0 hw n
  rw [lamPlus_zero38, lamMinus_zero38] at ht hg
  have ht' : tauN38 C R 0 n = (n : ℂ) * (Real.pi : ℂ) := by rw [ht]; simp only [countingCenter38]; ring
  have hg' : gamma2N38 C R 0 n = 0 := by simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using hg
  exact ⟨ht', hg', gamma2_zero_critical_eq_tau38 C R hsel 0 hw n hg',
    critical_denominator_nonzero38 C R hsel 0 hw n⟩

theorem tauGamma_nonfree_negative_collapsed38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) :
    tauN38 C R (realSlice (constL2 1)) (-1) = (-Real.sqrt (Real.pi ^ 2 + 1) : ℂ) ∧
      gamma2N38 C R (realSlice (constL2 1)) (-1) = 0 ∧
      lamDot (realSlice (constL2 1)) (-1) = tauN38 C R (realSlice (constL2 1)) (-1) ∧
      criticalDenominator38 C R (realSlice (constL2 1)) (-1) ≠ 0 := by
  have hw := realSlice_mem_gkW (constL2 1)
  have ht := tau_pair_mean38 C R hsel _ hw (-1)
  have hg := gamma2_pair_gap38 C R hsel _ hw (-1)
  rw [realType_const_negative_labels38.1, realType_const_negative_labels38.2] at ht hg
  have ht' : tauN38 C R (realSlice (constL2 1)) (-1) = (-Real.sqrt (Real.pi ^ 2 + 1) : ℂ) := by
    rw [ht]; push_cast; ring
  have hg' : gamma2N38 C R (realSlice (constL2 1)) (-1) = 0 := by simpa using hg
  exact ⟨ht', hg', gamma2_zero_critical_eq_tau38 C R hsel _ hw (-1) hg',
    critical_denominator_nonzero38 C R hsel _ hw (-1)⟩

theorem tauGamma_nonfree_open_central38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) :
    tauN38 C R (realSlice (constL2 1)) 0 = 0 ∧ gamma2N38 C R (realSlice (constL2 1)) 0 = 4 := by
  have hw := realSlice_mem_gkW (constL2 1)
  rw [tau_pair_mean38 C R hsel _ hw 0, gamma2_pair_gap38 C R hsel _ hw 0,
    realType_const_central_labels38.1, realType_const_central_labels38.2]
  norm_num

theorem tauGamma_triangular_values38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (a : ℂ) (hw : (constL2 a, (0 : PhysicalL2)) ∈ gkW) (n : ℤ) :
    tauN38 C R (constL2 a, 0) n = (n : ℂ) * (Real.pi : ℂ) ∧
      gamma2N38 C R (constL2 a, 0) n = 0 ∧ lamDot (constL2 a, 0) n = (n : ℂ) * (Real.pi : ℂ) := by
  have hl := labelling_probe_triangular38 (constL2 a) n
  have ht := tau_pair_mean38 C R hsel _ hw n
  have hg := gamma2_pair_gap38 C R hsel _ hw n
  rw [hl.1, hl.2] at ht hg
  have ht' : tauN38 C R (constL2 a, 0) n = (n : ℂ) * (Real.pi : ℂ) := by
    rw [ht]; simp only [countingCenter38]; ring
  have hg' : gamma2N38 C R (constL2 a, 0) n = 0 := by simpa using hg
  exact ⟨ht', hg', (gamma2_zero_critical_eq_tau38 C R hsel _ hw n hg').trans ht'⟩

theorem tauGamma_nonzero_triangular_in_W38 : ∃ a : ℝ, 0 < a ∧
    (constL2 (a : ℂ), (0 : PhysicalL2)) ∈ gkW ∧ (constL2 (a : ℂ), (0 : PhysicalL2)) ≠ 0 ∧
    ∀ n : ℤ, tauN (constL2 (a : ℂ), 0) n = (n : ℂ) * (Real.pi : ℂ) ∧
      gamma2 (constL2 (a : ℂ), 0) n = 0 ∧ lamDot (constL2 (a : ℂ), 0) n = (n : ℂ) * (Real.pi : ℂ) := by
  let q : PotPair := (constL2 1, 0)
  have hw0 : (0 : PotPair) ∈ gkW := by simpa only [realSlice_zero] using realSlice_mem_gkW 0
  have hc : ContinuousAt (fun a : ℝ => a • q) 0 := by fun_prop
  have ht : ∀ᶠ a : ℝ in 𝓝 0, a • q ∈ gkW :=
    hc.eventually (Filter.eventually_mem_set.mpr (by simpa only [zero_smul] using isOpen_gkW.mem_nhds hw0))
  obtain ⟨r, hr, hsmall⟩ := Metric.eventually_nhds_iff_ball.mp ht
  let a := r / 2
  have ha : 0 < a := half_pos hr
  have haball : a ∈ ball (0 : ℝ) r := by simp only [mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha]; dsimp [a]; linarith
  have he : a • q = (constL2 (a : ℂ), (0 : PhysicalL2)) := by
    simp only [q, Prod.smul_mk, realType_const_real_smul38, smul_zero]
  have hw : (constL2 (a : ℂ), (0 : PhysicalL2)) ∈ gkW := he ▸ hsmall a haball
  haveI : IsProbabilityMeasure spatialMeasure := by unfold spatialMeasure; infer_instance
  have hnorm : ‖constL2 (a : ℂ)‖ = a := by
    unfold constL2
    rw [Lp.norm_const' (μ := spatialMeasure) (p := (2 : ENNReal)) (c := (a : ℂ))
      (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)]
    simp [measureReal_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hne : (constL2 (a : ℂ), (0 : PhysicalL2)) ≠ 0 := by
    intro hz
    have heq := congrArg Prod.fst hz
    change constL2 (a : ℂ) = 0 at heq
    rw [heq, norm_zero] at hnorm
    linarith
  exact ⟨a, ha, hw, hne, tauGamma_triangular_values38 discC discR isolating_selectors_admissible38 _ hw⟩

end
end NlsGge.GK38
