import QuantumNLS.Local002Analytic
import QuantumNLS.LocalSpectralReduced

/-! Real-analyticity of the actual compression on the LOCAL-002 ball. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002

/-- Composing the LOCAL-002 projection with the two fixed free-basis maps
preserves its real analyticity. -/
theorem compression_analytic {L κ r ρ : ℝ} (hyp : FreeResolventHyp L κ)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (n : ℤ)
    (hρ : 2 * Real.sqrt κ * Cconst L r * ρ ≤ 1) :
    AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) =>
      compressionMatrix L κ (u : ℝ → ℂ) n r) (ball 0 ρ) := by
  let F : (H2 L →L[ℂ] H2 L) →L[ℂ] (E2 →L[ℂ] E2) :=
    (ContinuousLinearMap.compL ℂ E2 (H2 L) E2 (ContinuousLinearMap.adjoint (embed L n))).comp
      ((ContinuousLinearMap.compL ℂ E2 (H2 L) (H2 L)).flip (embed L n))
  intro u hu
  have hp := proj_analytic hyp hr hr2 n hρ u hu
  have h := ((F.restrictScalars ℝ).analyticAt _).comp hp
  exact h

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.compression_analytic
