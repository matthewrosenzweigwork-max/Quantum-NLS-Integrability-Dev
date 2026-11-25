import QuantumNLS.Local003Final
/-! integrator-authored trusted spec for LOCAL-003 thm:reset-uniform-reduction (terra_review r190 FULL ACCEPT): headline statement(s) copied verbatim from Local003Final (QuantumNLS.Local003Final). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.L003Spec
open QuantumNLS.Local003Final
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local003Analytic
  QuantumNLS.Local003Isometry QuantumNLS.Local003Inst QuantumNLS.Local003First
variable {L κ r : ℝ}
open QuantumNLS.Local002Bridge QuantumNLS.PhysicalTensor

set_option maxHeartbeats 8000000 in
theorem reset_uniform_reduction_profile_spec [Fact (0 < L)] (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ∃ (a : L2T L → ℝ) (b : L2T L → ℂ),
        AnalyticOnNhd ℝ a (ball 0 ρ) ∧ AnalyticOnNhd ℝ b (ball 0 ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, SmallCompression L κ (circleRep u) n r) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ h : SmallCompression L κ (circleRep u) n r, ∀ v : E2,
          reducedMatrix2 L κ (circleRep u) n r h v =
            vec2 ((a u : ℂ) * v 0 + conj (b u) * v 1) (b u * v 0 + (a u : ℂ) * v 1)) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r →
            ∃ Eig : Submodule ℂ (H2 L),
              (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (circleRep u) (parity n)) ∧
              Module.finrank ℂ Eig =
                Multiset.count lam {((a u + ‖b u‖ : ℝ) : ℂ), ((a u - ‖b u‖ : ℝ) : ℂ)}) ∧
          ‖((a u + ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧ ‖((a u - ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧
          (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r → lam ≠ ((a u + ‖b u‖ : ℝ) : ℂ) →
            lam ≠ ((a u - ‖b u‖ : ℝ) : ℂ) →
            ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) lam R) ∧
          (((a u + ‖b u‖ : ℝ) : ℂ) = ((a u - ‖b u‖ : ℝ) : ℂ) ↔ b u = 0)) ∧
        AnalyticOnNhd ℝ (fun u : L2T L => ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b u)
          (ball 0 ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          ‖((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b u -
              QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ≤ C * ‖u‖ ^ 3) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          DifferentiableAt ℝ (fun w : L2T L =>
            ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) u ∧
          ‖fderiv ℝ (fun w : L2T L =>
              ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) u -
            fderiv ℝ (fun w : L2T L =>
              ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) 0‖ ≤ C * ‖u‖ ^ 2) := by
  exact QuantumNLS.Local003Final.reset_uniform_reduction_profile hL hκ hr hr2

end QuantumNLS.L003Spec
#print axioms QuantumNLS.L003Spec.reset_uniform_reduction_profile_spec
