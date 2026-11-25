import NlsGge.GK38.AbelianRatioCutBound
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Source-only actual scalar spectral derivative of the omitted ratio,
identified with the fixed joint Frechet direction BEFORE analytic or compact
parameter bounds are used. The input remains a genuine arbitrary full lp2. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem angleOmittedRatio_spectral_deriv_joint_analytic38 (m : ℤ) :
    AnalyticOnNhd ℂ
      (fun p : (PotPair × Lib.L2Seq) × ℂ =>
        deriv (fun z => p2OmittedRatio38 m (p.1,z)) p.2)
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1,p.2) ∈ a5OmittedRootDomain38 m} := by
  let S : Set ((PotPair × Lib.L2Seq) × ℂ) :=
    {p | (p.1.1,p.2) ∈ a5OmittedRootDomain38 m}
  let ev : (((PotPair × Lib.L2Seq) × ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ ((0,0),1)
  have hS : IsOpen S := (isOpen_a5OmittedRootDomain38 m).preimage (by fun_prop)
  have he (q : (PotPair × Lib.L2Seq) × ℂ) (hq : q ∈ S) :
      ev (fderiv ℂ (p2OmittedRatio38 m) q)=
        deriv (fun z => p2OmittedRatio38 m (q.1,z)) q.2 := by
    have hf := (p2OmittedRatio_analytic38 m q hq).differentiableAt.hasFDerivAt
    have hi : HasDerivAt (fun z : ℂ => (q.1,z)) ((0,0),1) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    exact (hf.comp_hasDerivAt q.2 hi).deriv.symm
  intro p hp
  have h := (ev.analyticAt (fderiv ℂ (p2OmittedRatio38 m) p)).comp
    (p2OmittedRatio_analytic38 m p hp).fderiv
  apply h.congr
  filter_upwards [hS.mem_nhds hp] with q hq
  exact he q hq

/-- Actual finite exceptional rows are bounded on their ORIGINAL filled
spectral discs by compactness ONLY in the scalar spectral variable. -/
theorem angleOmittedRatio_finite_spectral_deriv_bound38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hfam : IsolatingFamily38 φ₀ C R)
    (S : Finset ℤ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ p : PotPair × Lib.L2Seq, p ∈ ball (φ₀,s₀) ε →
        ∀ m ∈ S, ∀ z ∈ closedBall (C m) (R m),
          ‖deriv (fun w => p2OmittedRatio38 m (p,w)) z‖ ≤ B := by
  apply p2FiniteCompact_parameter_bound38 S
    (fun m p z => deriv (fun w => p2OmittedRatio38 m (p,w)) z)
    (φ₀,s₀) (fun m => closedBall (C m) (R m)) (fun _ _ => isCompact_closedBall _ _)
  intro m _hm z hz
  exact angleOmittedRatio_spectral_deriv_joint_analytic38 m ((φ₀,s₀),z)
    (a5OwnClosedBall_omittedDomain38 φ₀ hφ₀ C R hfam m z hz)

end
end NlsGge.GK38
