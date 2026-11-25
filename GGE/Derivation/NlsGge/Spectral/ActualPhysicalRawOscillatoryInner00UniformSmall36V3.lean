import NlsGge.Spectral.ActualPhysicalHeightAmplitudeFamilyFourierUniformDecay36V8
import NlsGge.Spectral.ActualPhysicalRawOscillatoryInnerNormBounds36V3
import Mathlib.Topology.MetricSpace.Pseudo.Basic
set_option autoImplicit false
noncomputable section
open Filter MeasureTheory
open scoped Topology UniformConvergence
namespace NlsGge.SpectralFoundations
open NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
/-- The actual raw 00-channel oscillatory inner integrals tend uniformly to
zero in endpoint and bounded nonnegative height, including height zero.
The raw cover is used only through its already proved integral identity. -/
theorem actualPhysicalRawOscillatoryInner00_uniformSmall36V3
    (u : PhysicalL2) (Y₀ : ℝ) (hY₀ : 0 ≤ Y₀) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in cocompact ℝ,
      ∀ p : Set.Icc (0 : ℝ) 1 × Set.Icc (0 : ℝ) Y₀,
        ‖∫ r in (0 : ℝ)..(p.1 : ℝ),
          Complex.exp (2*Complex.I*((x : ℂ)+Complex.I*((p.2 : ℝ) : ℂ))*
            (((p.1 : ℝ) : ℂ)-(r : ℂ))) *
            star (naturalPhysicalCoverL2 u (r : SpectralCircle))‖ < ε := by
  let A := actualPhysicalHeightAmplitude00Family36V6 u Y₀ hY₀
  have hscale : Tendsto (fun x : ℝ => x / Real.pi)
      (cocompact ℝ) (cocompact ℝ) := by
    simpa only [div_eq_mul_inv] using
      (Filter.tendsto_cocompact_mul_right₀
        (a := Real.pi⁻¹) (inv_ne_zero Real.pi_ne_zero))
  have hfamily := actualPhysicalHeightAmplitude00Family36V8_fourierUniformDecay
    u Y₀ hY₀
  have hu : TendstoUniformly
      (fun (x : ℝ) (q : Set.range A) =>
        Real.Lp.fourierTransformCLM ℝ ℂ q.1 (x / Real.pi))
      (fun _ : Set.range A => (0 : ℂ)) (cocompact ℝ) := by
    have h := UniformFun.tendsto_iff_tendstoUniformly.mp (hfamily.comp hscale)
    simpa only [Function.comp_def, UniformFun.toFun_ofFun, A] using h
  have he := Metric.tendstoUniformly_iff.mp hu ε hε
  filter_upwards [he] with x hx
  intro p
  let q : Set.range A := ⟨A p, ⟨p, rfl⟩⟩
  have hft : ‖Real.Lp.fourierTransformCLM ℝ ℂ (A p) (x / Real.pi)‖ < ε := by
    simpa only [q, dist_zero_left] using hx q
  exact lt_of_le_of_lt
    (actualPhysicalRawOscillatoryInner00_norm_le_fourier36V3 u Y₀ hY₀ p x) hft
end NlsGge.SpectralFoundations
end
