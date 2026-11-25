import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Operator-norm control for scalar multiplication on a continuous-linear-map
endomorphism space, isolated from the concrete paired-space instance search. -/
theorem genericCenterFactor_norm_smul_clm_prerequisiteV2_25
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMulCommClass ℂ ℂ E]
    (c : ℂ) (T : E →L[ℂ] E) :
    ‖c • T‖ ≤ ‖c‖ * ‖T‖ := by
  exact ContinuousLinearMap.opNorm_smul_le (𝕜' := ℂ) c T

/-- Analyticity of scalar multiplication on a continuous-linear-map
endomorphism space, under its actual normed-module structure. -/
theorem genericCenterFactor_analytic_smul_clm_prerequisiteV2_25
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [SMulCommClass ℂ ℂ E]
    (U : Set ℂ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (T : E →L[ℂ] E) :
    AnalyticOnNhd ℂ (fun z => f z • T) U := by
  letI : NormedSpace ℂ (E →L[ℂ] E) := ContinuousLinearMap.toNormedSpace
  exact hf.smul analyticOnNhd_const

end NlsGge.Schur
