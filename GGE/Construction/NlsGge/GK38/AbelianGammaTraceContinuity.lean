import NlsGge.GK38.AbelianGammaFiniteTraces

/-! Uncompiled actual scalar trace continuity. Absolute summability is earned
before the finite-subset net is passed to the limit. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p5Gamma_trace_local_lipschitz38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ closedBall φ₀ r ⊆ gkW ∧
      (∀ φ ∈ closedBall φ₀ r, Summable (fun m : ℤ => ‖gamma2 φ m‖)) ∧
      ∀ φ ∈ closedBall φ₀ r, ∀ ψ ∈ closedBall φ₀ r,
        ‖(∑' m : ℤ, gamma2 ψ m)-(∑' m : ℤ, gamma2 φ m)‖ ≤ L*‖ψ-φ‖ := by
  obtain ⟨r,B,hr,hB,hW,hs,_hd,hfinite⟩ := p5Gamma_finite_trace_local_cauchy38 φ₀ hφ₀
  have hsub : closedBall φ₀ r ⊆ closedBall φ₀ (2*r) :=
    closedBall_subset_closedBall (by linarith)
  refine ⟨r,B/r,hr,div_nonneg hB hr.le,hsub.trans hW,(fun φ hφ => hs φ (hsub hφ)),?_⟩
  intro φ hφ ψ hψ
  have htφ : Tendsto (fun S : Finset ℤ => ∑ m ∈ S, gamma2 φ m)
      atTop (𝓝 (∑' m : ℤ, gamma2 φ m)) := (hs φ (hsub hφ)).of_norm.hasSum
  have htψ : Tendsto (fun S : Finset ℤ => ∑ m ∈ S, gamma2 ψ m)
      atTop (𝓝 (∑' m : ℤ, gamma2 ψ m)) := (hs ψ (hsub hψ)).of_norm.hasSum
  exact le_of_tendsto' ((htψ.sub htφ).norm) (fun S => hfinite S φ hφ ψ hψ)

theorem p5Gamma_trace_continuousAt38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ContinuousAt (fun φ : PotPair => ∑' m : ℤ, gamma2 φ m) φ₀ := by
  obtain ⟨r,L,hr,hL,_hW,_hs,h⟩ := p5Gamma_trace_local_lipschitz38 φ₀ hφ₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hL1 : 0 < L+1 := by linarith
  refine ⟨min r (ε/(L+1)),lt_min hr (div_pos hε hL1),?_⟩
  intro ψ hψ
  have hψr : ψ ∈ closedBall φ₀ r := (lt_of_lt_of_le hψ (min_le_left _ _)).le
  have hψd : dist ψ φ₀ < ε/(L+1) := lt_of_lt_of_le hψ (min_le_right _ _)
  have hb := h φ₀ (mem_closedBall_self hr.le) ψ hψr
  rw [dist_eq_norm] at hψd ⊢
  have he : ‖ψ-φ₀‖*(L+1) < ε := (lt_div_iff₀ hL1).mp hψd
  exact hb.trans_lt (by nlinarith [norm_nonneg (ψ-φ₀)])

end
end NlsGge.GK38
