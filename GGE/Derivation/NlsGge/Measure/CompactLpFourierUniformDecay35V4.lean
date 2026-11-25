import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.UniformSpace.Ascoli

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory
open scoped Topology UniformConvergence

namespace NlsGge.Schur

/-- A compact family of genuine L¹ classes has Fourier transforms tending to zero
uniformly over the family. The compactness hypothesis is explicit: applications
must first construct the actual compact subset of `Lp ℂ 1`. -/
theorem compactLpFourierUniformDecay35V4
    {K : Set (Lp (α := ℝ) ℂ 1)} (hK : IsCompact K) :
    Tendsto
      (UniformFun.ofFun ∘ fun ξ : ℝ =>
        fun q : K => Real.Lp.fourierTransformCLM ℝ ℂ q.1 ξ)
      (Filter.cocompact ℝ)
      (𝓝 (UniformFun.ofFun (fun _ : K => (0 : ℂ)))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let FT := Real.Lp.fourierTransformCLM ℝ ℂ
  let F : ℝ → K → ℂ := fun ξ q => FT q.1 ξ
  have hcontinuous : Continuous (fun q : K => UniformFun.ofFun (FT q.1)) := by
    exact BoundedContinuousFunction.isInducing_coeFn.continuous.comp
      (FT.continuous.comp continuous_subtype_val)
  have heq : Equicontinuous F := by
    rw [equicontinuous_iff_continuous]
    change Continuous (fun q : K => UniformFun.ofFun (FT q.1))
    exact hcontinuous
  have hpoint : Tendsto F (Filter.cocompact ℝ) (𝓝 (fun _ : K => (0 : ℂ))) := by
    rw [tendsto_pi_nhds]
    intro q
    change Tendsto (fun ξ : ℝ => Real.Lp.fourierTransform q.1 ξ)
      (Filter.cocompact ℝ) (𝓝 0)
    simpa only [Real.Lp.fourierTransform_apply] using
      (Real.zero_at_infty_fourier (q.1 : ℝ → ℂ))
  exact (Equicontinuous.tendsto_uniformFun_iff_pi heq
    (Filter.cocompact ℝ) (fun _ : K => (0 : ℂ))).2 hpoint

end NlsGge.Schur
