import QuantumNLS.R275Unconditional
/-! integrator-authored trusted spec for R-275B7656 moments:thm:moments (review record r33 FULL support): headline statement(s) copied verbatim from R275Unconditional (QuantumNLS.R275Unconditional). -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.R275Spec
open QuantumNLS.R275Unconditional
open QuantumNLS.ClassicalCharges QuantumNLS.CauchyUniqueness
open QuantumNLS.FullMass QuantumNLS.SmoothScalarMomentsAsymptotic
open QuantumNLS.SmoothScalarMomentsCauchy
open QuantumNLS.SmoothScalarMomentsPhysical
variable {L : ℝ} [Fact (0 < L)] {f : ℝ → ℂ}

set_option maxHeartbeats 8000000 in
theorem R_275B7656_spec (κ : ℝ) (hκ : 0 < κ) (hf : SmoothPeriodic L f) :
    (∀ j : ℕ, (charge L κ f j).im = 0) ∧
    ∀ r : ℕ, Integrable (fun t : ℝ => |t| ^ r) (Mmeas κ (smoothL2 hf)) ∧
      ((∫ t : ℝ, t ^ r ∂(Mmeas κ (smoothL2 hf)) : ℝ) : ℂ) = charge L κ f (r + 1) := by
  exact QuantumNLS.R275Unconditional.R_275B7656 κ hκ hf

end QuantumNLS.R275Spec
#print axioms QuantumNLS.R275Spec.R_275B7656_spec
