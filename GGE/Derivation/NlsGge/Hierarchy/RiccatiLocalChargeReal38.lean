import NlsGge.Hierarchy.RiccatiWronskianIdentity38
import NlsGge.Hierarchy.FormalLogExactness38
import NlsGge.Hierarchy.RiccatiLocalChargeRealPrereq38
import Mathlib.Tactic

/-! Batch 38: reality of the local charges, E06-only.

For every smooth period-one field `u` and every `j`, the local charge
`∫₀¹ (-1)^{j+1} u p_{2j+1}` (paper/v2.tex lines 956-959) has zero imaginary
part. PROOF-ROUTE DEPARTURE: the source obtains reality from the spectral trace
formula (line 145, via Molnar); here it follows from the formal Wronskian
identity `(uΓ + ūΔ)(1 - ΓΔ) = D(ΓΔ)` (`riccatiWronskian38`), the cleared
formal logarithm (`formalLog_exact38`), the evaluation of the jet swap as
complex conjugation and the vanishing of periodic integrals of total
derivatives. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff

/-- Odd coefficients of `uΓ + ūΔ`: `k!(u p_k - ū σ p_k)` is a formal total
derivative. -/
theorem riccatiOddCoefficient_exact38 (k : ℕ) (hk : Odd k) :
    ∃ ℓ : Poly, (k.factorial : Poly) *
      (MvPolynomial.X (false, 0) * p k -
        MvPolynomial.X (true, 0) * jetSwapHom38 (p k)) = spatialD ℓ := by
  have hP : PowerSeries.constantCoeff (riccatiGamma38 * riccatiDelta38) = 0 := by
    rw [map_mul]
    have h0 : PowerSeries.constantCoeff riccatiGamma38 = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, riccatiGamma38,
        PowerSeries.coeff_mk]
      simp [p]
    rw [h0, zero_mul]
  obtain ⟨ℓ, hℓ⟩ := formalLog_exact38 spatialD
    (PowerSeries.C (MvPolynomial.X (false, 0)) * riccatiGamma38 +
      PowerSeries.C (MvPolynomial.X (true, 0)) * riccatiDelta38)
    (riccatiGamma38 * riccatiDelta38) hP riccatiWronskian38 k
  refine ⟨ℓ, Eq.trans ?_ hℓ⟩
  congr 1
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, riccatiGamma38,
    riccatiDelta38, PowerSeries.coeff_mk, PowerSeries.coeff_mk, hk.neg_one_pow]
  change _ = _ + MvPolynomial.X (true, 0) * (-1 * riccatiSwap38 (p k))
  ring_nf
  rfl

/-- Reality of the local charges: for every smooth period-one field and every
`j`, `Im ∫₀¹ (-1)^{j+1} u p_{2j+1} = 0`. -/
theorem formalChargeIntegrand_im_eq_zero38 (j : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)).im = 0 := by
  obtain ⟨ℓ, hℓ⟩ := riccatiOddCoefficient_exact38 (2 * j + 1) (odd_two_mul_add_one j)
  exact formalChargeIntegrand_im_eq_zero_of_exact38 j u hu hper ℓ hℓ

/-- Consequently the local charge equals the real number `Re Q^loc`. -/
theorem formalChargeIntegrand_integral_eq_re38 (j : ℕ) (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hper : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)) =
      (((∫ x in (0 : ℝ)..1, riccatiJetEvaluation u x (formalChargeIntegrand j)).re : ℝ) : ℂ) :=
  (Complex.ext rfl (by simp [formalChargeIntegrand_im_eq_zero38 j u hu hper]))

end NlsGge.HierarchyRiccati.Core

end
