import NlsGge.GK38.AbelianPaddedJacobianEquicontinuity
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Actual local COMPLEX analytic implicit level map. Invertibility of the
actual partial derivative is an explicit local input, earned separately by
the actual common inverse tube. No global solution/extension oracle. -/
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_local_complex_analytic_level_of_inverse38 (n : ℤ)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq)
    (hQ : (p6PaddedJacobian38 n φ₀ s₀).IsInvertible) :
    ∃ ψ : PotPair → Lib.L2Seq, ψ φ₀=s₀ ∧ AnalyticAt ℂ ψ φ₀ ∧
      (∀ᶠ φ in 𝓝 φ₀, p6PaddedFn38 n (φ,ψ φ)=p6PaddedFn38 n (φ₀,s₀)) ∧
      (∀ᶠ p : PotPair × Lib.L2Seq in 𝓝 (φ₀,s₀),
        p6PaddedFn38 n p=p6PaddedFn38 n (φ₀,s₀) ↔ ψ p.1=p.2) := by
  have hc : ContDiffAt ℂ ω (p6PaddedFn38 n) (φ₀,s₀) :=
    (p6PaddedFn_analytic38 n (φ₀,s₀) ⟨hφ₀,mem_univ _⟩).contDiffAt
  have hω : (ω : ℕ∞ω) ≠ 0 := by simp
  have hpart : ((fderiv ℂ (p6PaddedFn38 n) (φ₀,s₀)).comp
      (ContinuousLinearMap.inr ℂ PotPair Lib.L2Seq)).IsInvertible := by
    rw [p6PaddedFn_joint_inr_fderiv38 n φ₀ hφ₀ s₀]
    exact hQ
  let ψ : PotPair → Lib.L2Seq := hc.implicitFunction hω hpart
  exact ⟨ψ,hc.implicitFunction_apply_self hω hpart,
    (hc.contDiffAt_implicitFunction hω hpart).analyticAt,
    hc.eventually_apply_implicitFunction hω hpart,
    hc.eventually_apply_eq_iff_implicitFunction hω hpart⟩

end
end NlsGge.GK38
