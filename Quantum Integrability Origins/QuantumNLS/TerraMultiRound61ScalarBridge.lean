import QuantumNLS.TerraMultiRound59REG007
import QuantumNLS.RootEnergyMomentPhysical
import QuantumNLS.RootH1RatioCauchy
import QuantumNLS.PhysicalL2Normalization
import QuantumNLS.RootH1PositiveSpectral

/-! The signed scalar of the actual ratio equals the physical Cauchy transform. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory ComplexConjugate
open scoped InnerProductSpace
namespace QuantumNLS.TerraMultiRound61ScalarBridge
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RiccatiExpansions
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.RootH1RatioBounds

variable {L : ℝ} [Fact (0 < L)]

theorem scalar_inner {a : ℝ} (ha : 1 / 2 < a) (x r : Ell2) :
    scalar L a x r = inner ℂ (fieldMap L a (by linarith) x)
      (fieldMap L a (by linarith) r) := by
  exact QuantumNLS.RootEnergyMomentPhysical.floquetJ_inner ha x r

theorem scalar_cauchy {a Y κ : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) (x r : Ell2)
    (hx : fieldMap L a (by linarith) x = u)
    (hr : fieldMap L a (by linarith) r = ratioL2 hY hlog hκ.le u hsmall) :
    CauchyUniqueness.cauchyTransform (PhysicalQuantumMeasure.measure hκ u)
      ((Y : ℂ) * Complex.I) = -Complex.I * scalar L a x r := by
  rw [QuantumNLS.PhysicalL2Normalization.measure_eq_Mmeas]
  rw [scalar_inner ha, hx, hr]
  exact QuantumNLS.RootH1RatioCauchy.ratio_cauchy hY hlog hκ u hu hsmall

theorem scalar_real_poisson {a Y κ : ℝ} (ha : 1 / 2 < a) (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L) (hκ : 0 < κ) (u : L2T L) (hu : u ≠ 0)
    (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y) (x r : Ell2)
    (hx : fieldMap L a (by linarith) x = u)
    (hr : fieldMap L a (by linarith) r = ratioL2 hY hlog hκ.le u hsmall) :
    (scalar L a x r).re =
      ∫ t, QuantumNLS.CauchyUniqueness.pk Y (-t) ∂(PhysicalQuantumMeasure.measure hκ u) := by
  have hc := scalar_cauchy ha hY hlog hκ u hu hsmall x r hx hr
  have hi := QuantumNLS.CauchyUniqueness.im_cauchy (PhysicalQuantumMeasure.measure hκ u) hY 0
  simp only [Complex.ofReal_zero, zero_add, QuantumNLS.CauchyUniqueness.poisson, zero_sub] at hi
  rw [hc] at hi
  simpa using hi

#print axioms scalar_inner
#print axioms scalar_cauchy
#print axioms scalar_real_poisson
end QuantumNLS.TerraMultiRound61ScalarBridge
