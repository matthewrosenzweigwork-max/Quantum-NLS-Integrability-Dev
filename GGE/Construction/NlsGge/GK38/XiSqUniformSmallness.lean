import NlsGge.GK38.XiSqChiMajorant

set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

theorem a5Tau_uniform_tail38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ V, ∀ n : ℤ, (N:ℤ) < |n| →
        ‖tauN φ n - (n:ℂ)*(Real.pi:ℂ)‖ < ε := by
  obtain ⟨V,hV,N,ht⟩ := l2_continuous_local_tails38 a5TauShift38 φ₀
    (a5TauShift_analytic38 φ₀ hφ₀).continuousAt ε hε
  refine ⟨V ∩ gkW, inter_mem hV (isOpen_gkW.mem_nhds hφ₀), inter_subset_right, N, ?_⟩
  intro φ hφ n hn
  rw [← a5TauShift_value38 φ hφ.2 n]
  exact ht φ hφ.1 n hn

/-- Endpoint algebra and genuine gap-square control put the WHOLE actual segment in the ball. -/
theorem a5OwnCut_ball_of_small38 (φ : PotPair) (hφ : φ ∈ gkW) (n : ℤ)
    (ε : ℝ) (hε : 0 < ε)
    (ht : ‖tauN φ n - (n:ℂ)*(Real.pi:ℂ)‖ < ε/2)
    (hg : ‖gamma2 φ n‖ < ε^2) :
    segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball ((n:ℂ)*(Real.pi:ℂ)) ε := by
  have hsq : ‖lamPlus φ n-lamMinus φ n‖^2 = ‖gamma2 φ n‖ := by
    rw [gamma2_value38 φ hφ n, norm_pow]
  have hgap : ‖lamPlus φ n-lamMinus φ n‖ < ε := by nlinarith [norm_nonneg (lamPlus φ n-lamMinus φ n)]
  have hhalf : ‖(lamPlus φ n-lamMinus φ n)/2‖ < ε/2 := by
    rw [Complex.norm_div, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    linarith
  apply (convex_ball ((n:ℂ)*(Real.pi:ℂ)) ε).segment_subset
  · rw [mem_ball_iff_norm]
    have he : lamMinus φ n-(n:ℂ)*(Real.pi:ℂ) =
        (tauN φ n-(n:ℂ)*(Real.pi:ℂ))-(lamPlus φ n-lamMinus φ n)/2 := by
      rw [tauN_value38 φ hφ n]
      ring
    rw [he]
    exact (norm_sub_le _ _).trans_lt (by linarith)
  · rw [mem_ball_iff_norm]
    have he : lamPlus φ n-(n:ℂ)*(Real.pi:ℂ) =
        (tauN φ n-(n:ℂ)*(Real.pi:ℂ))+(lamPlus φ n-lamMinus φ n)/2 := by
      rw [tauN_value38 φ hφ n]
      ring
    rw [he]
    exact (norm_add_le _ _).trans_lt (by linarith)

/-- Actual Hilbert continuity earns ONE neighbourhood and cutoff containing all far own cuts. -/
theorem a5OwnCut_uniform_ball38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ U, ∀ n : ℤ, (N:ℤ) < |n| →
        segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball ((n:ℂ)*(Real.pi:ℂ)) ε := by
  obtain ⟨Ut,hUt,hUtW,Nt,ht⟩ := a5Tau_uniform_tail38 φ₀ hφ₀ (ε/2) (by positivity)
  obtain ⟨Ug,hUg,_hUgW,Ng,hg⟩ := a5Gamma2_uniform_tail38 φ₀ hφ₀ (ε^2) (by positivity)
  refine ⟨Ut ∩ Ug, inter_mem hUt hUg, fun φ hφ => hUtW hφ.1, max Nt Ng, ?_⟩
  intro φ hφ n hn
  have hnt : (Nt:ℤ) < |n| := by have h := le_max_left Nt Ng; omega
  have hng : (Ng:ℤ) < |n| := by have h := le_max_right Nt Ng; omega
  exact a5OwnCut_ball_of_small38 φ (hUtW hφ.1) n ε hε
    (ht φ hφ.1 n hnt) (hg φ hφ.2 n hng)

end
end NlsGge.GK38
