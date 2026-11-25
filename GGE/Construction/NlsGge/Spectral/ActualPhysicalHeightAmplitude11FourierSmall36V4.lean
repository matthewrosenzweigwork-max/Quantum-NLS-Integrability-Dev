import NlsGge.Spectral.ActualPhysicalHeightAmplitudeFamilyFourierUniformDecay36V8
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped UniformConvergence Topology

namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis

/-- Uniform smallness of the actual 11-amplitude Fourier transforms, uniformly
in the physical endpoint and bounded height. This isolates the inner Fourier
bound used by the first-pair estimate. -/
theorem actualPhysicalHeightAmplitude11_fourierSmall36V4
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖Real.Lp.fourierTransformCLM ℝ ℂ
          (actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀ p)
          (x / Real.pi)‖ < ε := by
  intro ε hε
  let A : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀ →
      Lp (α := ℝ) ℂ 1 (volume : Measure ℝ) :=
    actualPhysicalHeightAmplitude11Family36V6 u Y₀ hY₀
  have hscale : Tendsto (fun x : ℝ => x / Real.pi)
      (Filter.cocompact ℝ) (Filter.cocompact ℝ) := by
    simpa only [div_eq_mul_inv] using
      (Filter.tendsto_cocompact_mul_right₀
        (a := Real.pi⁻¹) (inv_ne_zero Real.pi_ne_zero))
  have hfamily := actualPhysicalHeightAmplitude11Family36V8_fourierUniformDecay
    u Y₀ hY₀
  have huniform : TendstoUniformly
      (fun (ξ : ℝ) (q : Set.range A) =>
        Real.Lp.fourierTransformCLM ℝ ℂ q.1 (ξ / Real.pi))
      (fun _ : Set.range A => (0 : ℂ)) (Filter.cocompact ℝ) := by
    have h := UniformFun.tendsto_iff_tendstoUniformly.mp (hfamily.comp hscale)
    simpa only [Function.comp_def, UniformFun.toFun_ofFun, A] using h
  have he := Metric.tendstoUniformly_iff.mp huniform ε hε
  filter_upwards [he] with x hx
  intro p
  let q : Set.range A := ⟨A p, ⟨p, rfl⟩⟩
  have hft : ‖Real.Lp.fourierTransformCLM ℝ ℂ (A p) (x / Real.pi)‖ < ε := by
    simpa only [q, dist_zero_left] using hx q
  simpa only [A] using hft

end NlsGge.SpectralFoundations
end
