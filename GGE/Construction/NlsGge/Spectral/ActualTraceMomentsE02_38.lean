import NlsGge.Spectral.ActualTraceFormulaE02_38
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # All spectral moments up to order `2j` (campaign 38), odd ones included -/

/-- Every moment `∫ t^m v`, `m ≤ 2j`, is finite and equals `-π · b_{m+1} i^{m+1}` with the local
coefficient `b = riccatiQuasiCoeff38 U`. -/
theorem actualTraceMoments_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u))
    (U : ℝ → ℂ) (hUs : ContDiff ℝ ∞ U) (hUp : Function.Periodic U 1)
    (hae : (fun s : ℝ => (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) (s : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0:ℝ) 2)] U)
    (j : ℕ) :
    ∀ m ≤ 2*j, Integrable (fun t : ℝ => t^m * actualGapHeightE02_38 u t) ∧
      riccatiQuasiCoeff38 U (m+1) * Complex.I ^ (m+1) =
        -(1 / Real.pi : ℂ) * ∫ t, (t^m * actualGapHeightE02_38 u t : ℝ) := by
  set v := actualGapHeightE02_38 u with hvdef
  set K := 2*j+1 with hK
  have hvc : Continuous v := continuous_actualGapHeightE02_38 u
  have hv0 : ∀ t, 0 ≤ v t := actualGapHeightE02_38_nonneg u
  have hherg := actualQuasimomentum_herglotz_E02_38 u hu
  -- integrability of v/(1+|t|)
  have hvi : Integrable (fun t => v t / (1 + |t|)) := by
    have hI := (hherg Complex.I (by simp)).1
    refine hI.norm.mono' ((hvc.div (continuous_const.add continuous_abs)
      (fun t => ne_of_gt (show (0:ℝ) < 1 + |t| by have := abs_nonneg t; linarith))).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
    have hpos : 0 < 1 + |t| := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hv0 t) hpos.le), norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hv0 t)]
    apply div_le_div_of_nonneg_left (hv0 t)
    · rw [norm_pos_iff, sub_ne_zero]; intro h; have := congrArg Complex.im h; simp at this
    · calc ‖(t:ℂ) - Complex.I‖ ≤ ‖(t:ℂ)‖ + ‖Complex.I‖ := norm_sub_le _ _
        _ = 1 + |t| := by rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]; ring
  -- coefficients
  let a : ℕ → ℂ := fun m => riccatiQuasiCoeff38 U (m+1) * Complex.I ^ (m+1)
  have ha : ∀ m ≤ 2*j, (a m).im = 0 := by
    intro m _
    rcases Nat.even_or_odd m with ⟨i, hi⟩ | ⟨i, hi⟩
    · -- m = 2i: b_{2i+1} purely imaginary
      have hb := riccatiQuasiCoeff38_odd_re U hUs hUp i
      have hm : m + 1 = 2*i + 1 := by omega
      set b := riccatiQuasiCoeff38 U (2*i+1)
      have hbI : b = (b.im : ℂ) * Complex.I := Complex.ext (by simp [hb]) (by simp)
      have hm2 : m = 2*i := by omega
      have hae' : a m = b * (Complex.I^(2*i) * Complex.I) := by
        simp only [a, pow_succ, hm2]
        rfl
      rw [hae', complex_I_pow_two_mul_E02_38, hbI]
      rcases neg_one_pow_eq_or ℂ i with h | h <;>
        simp [h, Complex.mul_im, Complex.mul_re]
    · -- m = 2i+1: b_{2i+2} real
      have hb := riccatiQuasiCoeff38_even_im U hUs hUp (i+1)
      have hm : m + 1 = 2*(i+1) := by omega
      simp only [a, hm, complex_I_pow_two_mul_E02_38]
      rcases neg_one_pow_eq_or ℂ (i+1) with h | h <;>
        simp [h, Complex.mul_im, hb]
  -- the expansion
  obtain ⟨η₁, B, hη₁, hB⟩ := actualQuasimomentum_imaginaryAxis_expansion_E02_38 u U hUs hUp hae K
  have hsum_eq : ∀ y : ℝ, 0 < y →
      ∑ m ∈ Finset.range (2*j+1), a m / (Complex.I * y) ^ (m+1) =
        ∑ m ∈ Finset.Icc 1 K, riccatiQuasiCoeff38 U m * (y:ℂ)⁻¹ ^ m := by
    intro y hy
    have hy0 : (y:ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, hK]
    apply Finset.sum_congr rfl
    intro m _
    simp only [a, mul_pow]
    rw [add_comm 1 m, inv_pow]
    field_simp
  have hexp : Tendsto (fun y : ℝ => (y:ℂ)^(2*j+1) * ((1/Real.pi : ℂ) *
      (∫ t, (v t : ℂ)/((t:ℂ) - Complex.I*y)) -
      ∑ m ∈ Finset.range (2*j+1), a m / (Complex.I*y)^(m+1))) atTop (𝓝 0) := by
    have hlim : Tendsto (fun y : ℝ => B / y) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop η₁] with y hy
    have hypos : 0 < y := by linarith
    have hz : 0 < (Complex.I * (y:ℂ)).im := by simp [hypos]
    have hk := (hherg (Complex.I*y) hz).2
    have hrep : (1/Real.pi : ℂ) * (∫ t, (v t : ℂ)/((t:ℂ) - Complex.I*y)) =
        actualQuasimomentumE02_38 u (Complex.I*y) - Complex.I*y := by
      rw [hk]; ring
    rw [hrep, hsum_eq y hypos, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hypos]
    calc y^(2*j+1) * ‖_‖ ≤ y^(2*j+1) * (B * y⁻¹ ^ (K+1)) :=
          mul_le_mul_of_nonneg_left (hB y hy) (by positivity)
      _ = B / y := by
          simp only [hK, inv_pow]
          field_simp
          ring
  have hHM := herglotz_moments_of_expansion_E02_38 v hv0 hvc.measurable hvi j a ha hexp
  exact hHM

end NlsGge.SpectralFoundations
end
