import NlsGge.GK38.AbelianPaddedPeriodMapBound
import NlsGge.GK38.AbelianBoundedHolomorphicDerivative
import NlsGge.GK38.AbelianPaddedJacobianColumns

/-! Actual ALL-signed Jacobians inherit one local Lipschitz constant from
the genuine common bound for their actual holomorphic padded period maps.
This is equicontinuity, not a false locally-uniform-zero-tail assertion. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6PaddedFn_hasFDerivAt38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    HasFDerivAt (fun t : Lib.L2Seq => p6PaddedFn38 n (φ,t))
      (p6PaddedJacobian38 n φ s) s := by
  let A := fderiv ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s)
  let S : Lib.L2Seq →L[ℂ] Lib.L2Seq :=
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).comp
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n)
  have ha : AnalyticAt ℂ (fun t : P2Space38 n => p2Fn38 n (φ,t)) (p2Restrict38 n s) :=
    AnalyticAt.comp (g := p2Fn38 n) (f := fun t : P2Space38 n => (φ,t))
      (p2Fn_analytic38 n (φ,p2Restrict38 n s) ⟨hφ,mem_univ _⟩)
      (analyticAt_const.prod analyticAt_id)
  have hf : HasFDerivAt
      (fun t : Lib.L2Seq => p2Fn38 n (φ,p2Restrict38 n t))
      (A.comp (p2Restrict38 n)) s :=
    ha.differentiableAt.hasFDerivAt.comp s ((p2Restrict38 n).hasFDerivAt (x := s))
  have he : HasFDerivAt (fun t : Lib.L2Seq =>
      p2Extend38 n (p2Fn38 n (φ,p2Restrict38 n t)))
      ((p2Extend38 n).comp (A.comp (p2Restrict38 n))) s :=
    ((p2Extend38 n).hasFDerivAt (x := p2Fn38 n (φ,p2Restrict38 n s))).comp s hf
  have hs : HasFDerivAt (fun t : Lib.L2Seq => (2 : ℂ) • S t) ((2 : ℂ) • S) s :=
    (S.hasFDerivAt (x := s)).const_smul (2 : ℂ)
  exact he.add hs

theorem p6PaddedFn_joint_inr_fderiv38 (n : ℤ) (φ : PotPair) (hφ : φ ∈ gkW)
    (s : Lib.L2Seq) :
    (fderiv ℂ (p6PaddedFn38 n) (φ,s)).comp
      (ContinuousLinearMap.inr ℂ PotPair Lib.L2Seq)=p6PaddedJacobian38 n φ s := by
  have hi : HasFDerivAt (fun t : Lib.L2Seq => (φ,t))
      (ContinuousLinearMap.inr ℂ PotPair Lib.L2Seq) s := by
    convert (hasFDerivAt_const φ s).prodMk (hasFDerivAt_id s) using 1 <;> ext x <;> rfl
  have hj := (p6PaddedFn_analytic38 n (φ,s) ⟨hφ,mem_univ _⟩).differentiableAt.hasFDerivAt.comp s hi
  exact hj.unique (p6PaddedFn_hasFDerivAt38 n φ hφ s)

theorem p6PaddedJacobian_difference_le_joint_fderiv38 (n : ℤ)
    (p q : PotPair × Lib.L2Seq) (hp : p.1 ∈ gkW) (hq : q.1 ∈ gkW) :
    ‖p6PaddedJacobian38 n p.1 p.2-p6PaddedJacobian38 n q.1 q.2‖ ≤
      ‖fderiv ℂ (p6PaddedFn38 n) p-fderiv ℂ (p6PaddedFn38 n) q‖ := by
  rw [← p6PaddedFn_joint_inr_fderiv38 n p.1 hp p.2,
    ← p6PaddedFn_joint_inr_fderiv38 n q.1 hq q.2,← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℂ PotPair Lib.L2Seq))

theorem p6PaddedJacobian_local_uniform_lipschitz38
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (s₀ : Lib.L2Seq) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ball (φ₀,s₀) r ⊆ gkW ×ˢ (univ : Set Lib.L2Seq) ∧
      ∀ n : ℤ, ∀ p ∈ ball (φ₀,s₀) r, ∀ q ∈ ball (φ₀,s₀) r,
        ‖p6PaddedJacobian38 n p.1 p.2-p6PaddedJacobian38 n q.1 q.2‖ ≤ L*‖p-q‖ := by
  obtain ⟨U,hU,hUW,V,hV,M,hM,hbound⟩ := p6PaddedFn_uniform_norm_bound38 φ₀ hφ₀ s₀
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (prod_mem_nhds hU hV)
  have hdom : ball (φ₀,s₀) R ⊆ gkW ×ˢ (univ : Set Lib.L2Seq) :=
    fun p hp => ⟨hUW (hball hp).1,mem_univ _⟩
  have hquarter : R/4 ≤ R := by linarith
  refine ⟨R/4,32*M/R^2,by positivity,by positivity,
    (ball_subset_ball hquarter).trans hdom,?_⟩
  intro n p hp q hq
  have hpR := ball_subset_ball hquarter hp
  have hqR := ball_subset_ball hquarter hq
  apply (p6PaddedJacobian_difference_le_joint_fderiv38 n p q (hdom hpR).1 (hdom hqR).1).trans
  exact P6HolomorphicBounds.norm_fderiv_sub_le_of_ball_bound
    (p6PaddedFn38 n) (φ₀,s₀) R M hR ((p6PaddedFn_analytic38 n).mono hdom)
    (fun z hz => hbound z.1 (hball hz).1 z.2 (hball hz).2 n) p q hp hq

end
end NlsGge.GK38
