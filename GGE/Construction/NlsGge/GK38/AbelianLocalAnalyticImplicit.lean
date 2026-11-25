import NlsGge.GK38.AbelianSolutionTopology
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Uncompiled actual local analytic implicit prefix. The explicit hQ is an
ordinary intermediate actual-derivative invertibility input, to be realized
by the concrete P4 kernel/Fredholm theorem before any final P5 credit.
No invertibility or local solution oracle is defined or assumed globally. -/
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5RealJointFn_inr_fderiv38 (n : ℤ) (u : PhysicalL2) (t : P3RealSpace38 n) :
    (fderiv ℝ (fun p : PhysicalL2 × P3RealSpace38 n => p3RealFn38 n p.1 p.2) (u,t)).comp
      (ContinuousLinearMap.inr ℝ PhysicalL2 (P3RealSpace38 n)) =
        fderiv ℝ (p3RealFn38 n u) t := by
  have hj := (p5RealJointFn_analytic38 n (u,t) (mem_univ _)).differentiableAt.hasFDerivAt
  have he := hj.comp t (hasFDerivAt_prodMk_right u t)
  exact he.fderiv.symm

theorem p5Actual_local_analytic_implicit_of_actual_inverse38 (n : ℤ)
    (u₀ : PhysicalL2) (t₀ : P3RealSpace38 n) (hzero : p3RealFn38 n u₀ t₀=0)
    (hQ : (fderiv ℝ (p3RealFn38 n u₀) t₀).IsInvertible) :
    ∃ ψ : PhysicalL2 → P3RealSpace38 n, ψ u₀=t₀ ∧ AnalyticAt ℝ ψ u₀ ∧
      (∀ᶠ u in 𝓝 u₀, p3RealFn38 n u (ψ u)=0) ∧
      (∀ᶠ p : PhysicalL2 × P3RealSpace38 n in 𝓝 (u₀,t₀),
        p3RealFn38 n p.1 p.2=0 ↔ ψ p.1=p.2) := by
  let f : PhysicalL2 × P3RealSpace38 n → P3RealSpace38 n :=
    fun p => p3RealFn38 n p.1 p.2
  have hc : ContDiffAt ℝ ω f (u₀,t₀) :=
    (p5RealJointFn_analytic38 n (u₀,t₀) (mem_univ _)).contDiffAt
  have hω : (ω : ℕ∞ω) ≠ 0 := by simp
  have hpart : ((fderiv ℝ f (u₀,t₀)).comp
      (ContinuousLinearMap.inr ℝ PhysicalL2 (P3RealSpace38 n))).IsInvertible := by
    rw [p5RealJointFn_inr_fderiv38]
    exact hQ
  let ψ : PhysicalL2 → P3RealSpace38 n := hc.implicitFunction hω hpart
  refine ⟨ψ,hc.implicitFunction_apply_self hω hpart,
    (hc.contDiffAt_implicitFunction hω hpart).analyticAt,?_,?_⟩
  · simpa only [f,hzero] using hc.eventually_apply_implicitFunction hω hpart
  · simpa only [f,hzero] using hc.eventually_apply_eq_iff_implicitFunction hω hpart

end
end NlsGge.GK38
