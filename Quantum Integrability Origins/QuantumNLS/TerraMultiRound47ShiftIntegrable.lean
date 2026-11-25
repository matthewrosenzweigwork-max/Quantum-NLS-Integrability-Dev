import QuantumNLS.TerraMultiRound47PhysicalShift

/-! Integrability of the physical Laplace-shift integrand. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound47ShiftIntegrable
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.TerraMultiRound47PhysicalShift

/-- The pointwise physical shifted integrand is Bochner integrable over the
positive half-line, with no restriction on Y. -/
theorem physical_shift_integrable (L : ℝ) [hL : Fact (0 < L)] {a : ℝ}
    (ha : 1 / 2 < a) (Y x : ℝ) (u : Ell2) :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y)) (Ioi 0) := by
  let B : ℝ := (Real.sqrt L)⁻¹ * ∑' k, ‖toField L a u k‖
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hg : IntegrableOn (fun v : ℝ => Real.exp (-v) * B) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mul_const B
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    have hc : Continuous (fun v : ℝ => physRep L a u (x - v / Y)) :=
      (physRep_continuous L ha u).comp (continuous_const.sub (continuous_id.div_const Y))
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).mul hc
  · filter_upwards with v
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_left (physRep_sup_bound hL.out ha u (x - v / Y)) (Real.exp_pos _).le

/-- The actual physical Laplace-shift formula together with its integrability. -/
theorem physical_resolvent_laplace_integrable (L : ℝ) [hL : Fact (0 < L)] {a Y : ℝ}
    (ha : 1 / 2 < a) (hY : 0 < |Y|) (u : Ell2) (x : ℝ) :
    IntegrableOn (fun v : ℝ => (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y)) (Ioi 0) ∧
    physRep L a (signedCLM L Y hY u) x = (Y⁻¹ : ℂ) *
      ∫ v : ℝ in Ioi 0, (Real.exp (-v) : ℂ) * physRep L a u (x - v / Y) :=
  ⟨physical_shift_integrable L ha Y x u, physical_resolvent_laplace L ha hY u x⟩

#print axioms physical_shift_integrable
#print axioms physical_resolvent_laplace_integrable
end QuantumNLS.TerraMultiRound47ShiftIntegrable
