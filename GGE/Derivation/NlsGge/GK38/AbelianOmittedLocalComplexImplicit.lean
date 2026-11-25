import NlsGge.GK38.AbelianLocalAnalyticImplicit
import NlsGge.GK38.AbelianPaddedInverseRestriction
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Local complex analytic charts for the ACTUAL omitted period map. The
invertible actual partial derivative is explicit, and can be earned from
literal padded block invertibility. These charts support faithful continuation
of normalized zeros; no global gluing conclusion is assumed. -/
set_option autoImplicit false
open Set Filter Topology
open scoped ContDiff
namespace NlsGge.GK38
noncomputable section

theorem p6OmittedFn_joint_inr_fderiv38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (t : P2Space38 n) :
    (fderiv ℂ (p2Fn38 n) (φ,t)).comp
      (ContinuousLinearMap.inr ℂ PotPair (P2Space38 n))=
        fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (φ,y)) t := by
  have hi : HasFDerivAt (fun y : P2Space38 n => (φ,y))
      (ContinuousLinearMap.inr ℂ PotPair (P2Space38 n)) t := by
    convert (hasFDerivAt_const φ t).prodMk (hasFDerivAt_id t) using 1 <;> ext y <;> rfl
  have hj := (p2Fn_analytic38 n (φ,t) ⟨hφ,mem_univ _⟩).differentiableAt.hasFDerivAt.comp t hi
  exact hj.fderiv.symm

theorem p6OmittedFn_local_complex_analytic_zero_of_inverse38 (n : ℤ)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (t₀ : P2Space38 n)
    (hzero : p2Fn38 n (φ₀,t₀)=0)
    (hQ : (fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ₀,t)) t₀).IsInvertible) :
    ∃ ψ : PotPair → P2Space38 n, ψ φ₀=t₀ ∧ AnalyticAt ℂ ψ φ₀ ∧
      (∀ᶠ φ in 𝓝 φ₀, p2Fn38 n (φ,ψ φ)=0) ∧
      (∀ᶠ p : PotPair × P2Space38 n in 𝓝 (φ₀,t₀),
        p2Fn38 n p=0 ↔ ψ p.1=p.2) := by
  have hc : ContDiffAt ℂ ω (p2Fn38 n) (φ₀,t₀) :=
    (p2Fn_analytic38 n (φ₀,t₀) ⟨hφ₀,mem_univ _⟩).contDiffAt
  have hω : (ω : ℕ∞ω) ≠ 0 := by simp
  have hpart : ((fderiv ℂ (p2Fn38 n) (φ₀,t₀)).comp
      (ContinuousLinearMap.inr ℂ PotPair (P2Space38 n))).IsInvertible := by
    rw [p6OmittedFn_joint_inr_fderiv38 n φ₀ hφ₀ t₀]
    exact hQ
  let ψ : PotPair → P2Space38 n := hc.implicitFunction hω hpart
  refine ⟨ψ,hc.implicitFunction_apply_self hω hpart,
    (hc.contDiffAt_implicitFunction hω hpart).analyticAt,?_,?_⟩
  · simpa only [hzero] using hc.eventually_apply_implicitFunction hω hpart
  · simpa only [hzero] using hc.eventually_apply_eq_iff_implicitFunction hω hpart

end
end NlsGge.GK38
