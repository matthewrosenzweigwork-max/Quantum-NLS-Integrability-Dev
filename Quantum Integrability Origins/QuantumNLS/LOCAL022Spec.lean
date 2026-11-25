import QuantumNLS.ResetNormalizationUniquenessLOCAL022
/-! integrator-authored trusted spec for LOCAL-022 thm:reset-normalization-uniqueness (Terra r142 ACCEPT,
parametrized over the common indexed-mass functional q with q n 0 = 0, per integrator instruction).
Statement copied verbatim from ResetNormalizationUniquenessLOCAL022 e0cc17e8; Cphys is the physical
reflection-conjugation u ↦ conj(u(-·)) (Cphys_apply, rfl). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle InnerProductSpace ComplexConjugate
namespace LOCAL022Spec
open QuantumNLS.ResetNormalizationUniqueness

set_option maxHeartbeats 4000000 in
theorem thm_reset_normalization_uniqueness_spec
    (L : ℝ) [Fact (0 < L)] {r : ℝ} (hr : 0 < r)
    (q : ℤ → Lp ℂ 2 (volume : Measure (AddCircle L)) → ℝ)
    (hq0 : ∀ n, q n 0 = 0)
    (Φ₁ Φ₂ : Lp ℂ 2 (volume : Measure (AddCircle L)) → S2 ℤ)
    (hΦ₁ : IsStronglySymplecticOn
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₁)
    (hΦ₂ : IsStronglySymplecticOn
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r)
      (Metric.ball (0 : S2 ℤ) r) Φ₂)
    (han₁ : AnalyticOnNhd ℝ Φ₁
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (han₂ : AnalyticOnNhd ℝ Φ₂
      (Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r))
    (hm₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      ∀ n, ‖Φ₁ u n‖ ^ 2 = q n u)
    (hm₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      ∀ n, ‖Φ₂ u n‖ ^ 2 = q n u)
    (hD₁ : ∀ h, fderiv ℝ Φ₁ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hD₂ : ∀ h, fderiv ℝ Φ₂ 0 h = QuantumNLS.Fourier.fourierL2 L h)
    (hsym₁ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ (Cphys L u) = star (Φ₁ u))
    (hsym₂ : ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₂ (Cphys L u) = star (Φ₂ u)) :
    ∀ u ∈ Metric.ball (0 : Lp ℂ 2 (volume : Measure (AddCircle L))) r,
      Φ₁ u = Φ₂ u :=
  QuantumNLS.ResetNormalizationUniquenessLOCAL022.thm_reset_normalization_uniqueness L hr q hq0 Φ₁ Φ₂ hΦ₁ hΦ₂
    han₁ han₂ hm₁ hm₂ hD₁ hD₂ hsym₁ hsym₂

theorem Cphys_apply (L : ℝ) [Fact (0 < L)] (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    Cphys L u = star (reflectR L u) := rfl
end LOCAL022Spec
#print axioms LOCAL022Spec.thm_reset_normalization_uniqueness_spec
