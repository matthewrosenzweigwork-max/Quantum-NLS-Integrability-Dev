import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Operator-norm limits preserve compactness. Under the normed hypotheses below, the
continuous-linear-map topology is the operator-norm topology. Pointwise (strong or weak
operator) convergence is outside this statement. -/

set_option autoImplicit false

namespace NlsGge.Atomic

/-- A pointwise family of compact continuous linear maps remains compact at any
operator-norm limit. The codomain must be complete. -/
theorem compact_of_operatorNorm_limit
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {T : ℕ → E →L[𝕜] F} {S : E →L[𝕜] F}
    (h : ∀ n, IsCompactOperator (T n))
    (ht : Filter.Tendsto T Filter.atTop (nhds S)) : IsCompactOperator S := by
  exact isCompactOperator_of_tendsto ht (Filter.Eventually.of_forall h)


/-- The same result stated as convergence of the operator-norm difference to zero. -/
theorem compact_of_operatorNorm_difference_tendsto_zero
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {T : ℕ → E →L[𝕜] F} {S : E →L[𝕜] F}
    (h : ∀ n, IsCompactOperator (T n))
    (ht : Filter.Tendsto (fun n => ‖T n - S‖) Filter.atTop (nhds (0 : ℝ))) :
    IsCompactOperator S := by
  apply compact_of_operatorNorm_limit h
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa using ht

end NlsGge.Atomic
