import NlsGge.GK38.PoissonSpectralODE

/-! The actual spectral commutation identity, with AC and integrability earned. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory NlsGge.GK38
namespace NlsGge.GK38.PoissonSpectral38
noncomputable section

theorem integral_spectralGradientWedge38_eq_zero (φ : PotPair) (z w : ℂ) :
    (∫ s in (0 : ℝ)..1, spectralGradientWedge38 φ z w s) = 0 := by
  by_cases hzw : z = w
  · subst w
    have hz : spectralGradientWedge38 φ z z = (fun _ => 0) := by
      funext s
      unfold spectralGradientWedge38
      ring
    simp only [hz, intervalIntegral.integral_zero]
  · have hi := (intervalIntegrable_spectralGradientWedge38 φ z w).const_mul
      (2 * Complex.I * (z - w))
    have hftc := ac_integral_eq_sub38 (ac_cyclicTraceProduct38 φ z w) hi
      (ae_hasDerivAt_cyclicTraceProduct38 φ z w) ⟨1, zero_le_one, le_rfl⟩
    have hend : cyclicTraceProduct38 φ z w 1 - cyclicTraceProduct38 φ z w 0 = 0 := by
      simp only [cyclicTraceProduct38, cyclicMatrix38_one, cyclicMatrix38_zero, sub_self]
    have hprod : (2 * Complex.I * (z - w)) *
        (∫ s in (0 : ℝ)..1, spectralGradientWedge38 φ z w s) = 0 := by
      rw [intervalIntegral.integral_const_mul] at hftc
      exact hftc.trans hend
    have hc : (2 * Complex.I * (z - w)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero)
        (sub_ne_zero.mpr hzw)
    exact (mul_eq_zero.mp hprod).resolve_left hc

theorem spectralDiscrimPoisson38_eq_zero (φ : PotPair) (z w : ℂ) :
    spectralDiscrimPoisson38 φ z w = 0 := by
  simp only [spectralDiscrimPoisson38, integral_spectralGradientWedge38_eq_zero, mul_zero]

/-- Actual Hamiltonian directions have the required representatives only a.e. -/
theorem spectralDiscrimHamField38_rep (φ : PotPair) (w : ℂ) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (spectralDiscrimHamField38 φ w) s =
        -Complex.I * gradDiscrim38 φ w s 1 ∧
      potRepSnd38 (spectralDiscrimHamField38 φ w) s =
        Complex.I * gradDiscrim38 φ w s 0 := by
  filter_upwards [gradDiscrimL2_rep φ w,
    ae_restrict_of_ae (coverRep38_smul_ae (-Complex.I) (gradDiscrimL2 φ w).2),
    ae_restrict_of_ae (coverRep38_smul_ae Complex.I (gradDiscrimL2 φ w).1)]
    with s hr h0 h1
  constructor
  · change coverRep38 (-Complex.I • (gradDiscrimL2 φ w).2) s = _
    exact h0.trans (congrArg (fun a : ℂ => -Complex.I * a) hr.2)
  · change coverRep38 (Complex.I • (gradDiscrimL2 φ w).1) s = _
    exact h1.trans (congrArg (fun a : ℂ => Complex.I * a) hr.1)

theorem spectralHamPairing38_eq_wedge_ae (φ : PotPair) (z w : ℂ) :
    (fun s => gradDiscrim38 φ z s 0 *
        potRepFst38 (spectralDiscrimHamField38 φ w) s +
      gradDiscrim38 φ z s 1 * potRepSnd38 (spectralDiscrimHamField38 φ w) s)
      =ᵐ[volume.restrict (uIoc (0 : ℝ) 1)]
        (fun s => -Complex.I * spectralGradientWedge38 φ z w s) := by
  rw [uIoc_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
  filter_upwards [spectralDiscrimHamField38_rep φ w] with s hs
  rw [hs.1, hs.2]
  unfold spectralGradientWedge38
  ring

theorem intervalIntegrable_spectralHamPairing38 (φ : PotPair) (z w : ℂ) :
    IntervalIntegrable (fun s => gradDiscrim38 φ z s 0 *
        potRepFst38 (spectralDiscrimHamField38 φ w) s +
      gradDiscrim38 φ z s 1 * potRepSnd38 (spectralDiscrimHamField38 φ w) s)
        volume 0 1 :=
  ((intervalIntegrable_spectralGradientWedge38 φ z w).const_mul (-Complex.I)).congr_ae
    (spectralHamPairing38_eq_wedge_ae φ z w).symm

theorem gradDiscrimCLM_spectralDiscrimHamField38 (φ : PotPair) (z w : ℂ) :
    gradDiscrimCLM φ z (spectralDiscrimHamField38 φ w) =
      spectralDiscrimPoisson38 φ z w := by
  rw [gradDiscrimCLM_apply, spectralDiscrimPoisson38,
    ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr_ae_restrict (spectralHamPairing38_eq_wedge_ae φ z w)

theorem spectralDiscrimCommuteTarget : SpectralDiscrimCommuteTarget := by
  intro φ z w
  exact ⟨intervalIntegrable_spectralGradientWedge38 φ z w,
    spectralDiscrimPoisson38_eq_zero φ z w,
    gradDiscrimCLM_spectralDiscrimHamField38 φ z w⟩

/-- The same concrete bracket is the actual directional derivative. -/
theorem actual_fderiv_discrim_hamField_eq_zero (φ : PotPair) (z w : ℂ) :
    fderiv ℂ (fun ψ => NlsGge.GK38.discrim ψ z) φ (spectralDiscrimHamField38 φ w) = 0 := by
  rw [(hasFDerivAt_discrim z φ).fderiv,
    gradDiscrimCLM_spectralDiscrimHamField38, spectralDiscrimPoisson38_eq_zero]

end
end NlsGge.GK38.PoissonSpectral38
