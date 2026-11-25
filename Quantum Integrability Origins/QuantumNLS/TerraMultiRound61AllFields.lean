import QuantumNLS.TerraMultiRound61ScalarBridge

/-! Remove the nonzero-field split from the physical scalar identity. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open scoped InnerProductSpace
namespace QuantumNLS.TerraMultiRound61AllFields
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound61ScalarBridge
variable {L : ℝ} [Fact (0 < L)]

theorem scalar_cauchy_all {a Y κ : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 < κ) (u : L2T L)
    (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) (x r : Ell2)
    (hx : fieldMap L a (by linarith) x = u)
    (hr : fieldMap L a (by linarith) r = ratioL2 hY hlog hκ.le u hsmall) :
    CauchyUniqueness.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)
      ((Y : ℂ) * Complex.I) = -Complex.I * scalar L a x r := by
  by_cases hu : u = 0
  · rw [hu] at hx ⊢
    rw [scalar_inner ha, hx, PhysicalQuantumMeasure.measure_zero]
    simp [CauchyUniqueness.cauchyTransform]
  · exact scalar_cauchy ha hY hlog hκ u hu hsmall x r hx hr

theorem scalar_real_poisson_all {a Y κ : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 < κ) (u : L2T L)
    (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) (x r : Ell2)
    (hx : fieldMap L a (by linarith) x = u)
    (hr : fieldMap L a (by linarith) r = ratioL2 hY hlog hκ.le u hsmall) :
    (scalar L a x r).re =
      ∫ t, QuantumNLS.CauchyUniqueness.pk Y (-t) ∂(PhysicalQuantumMeasure.measure hκ u) := by
  by_cases hu : u = 0
  · rw [hu] at hx ⊢
    rw [scalar_inner ha, hx, PhysicalQuantumMeasure.measure_zero]
    simp
  · exact scalar_real_poisson ha hY hlog hκ u hu hsmall x r hx hr

#print axioms scalar_cauchy_all
#print axioms scalar_real_poisson_all
end QuantumNLS.TerraMultiRound61AllFields
