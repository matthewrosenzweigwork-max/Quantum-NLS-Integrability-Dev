import NlsGge.GK38.TauGammaExteriorL2

/-! Exterior tails are earned from two actual analytic Hilbert-valued maps. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem exterior_l2_realizations38 : ∃ A B : PotPair → Lib.L2Z,
    (∀ φ ∈ gkW, ∀ n : ℤ, A φ n = exteriorFactor38 φ n (lamDot φ n) - 1 ∧
      B φ n = deriv (exteriorFactor38 φ n) (lamDot φ n)) ∧
    AnalyticOnNhd ℂ A gkW ∧ AnalyticOnNhd ℂ B gkW := by
  obtain ⟨A, hA, hAa⟩ := local_l2_analytic_realization38 gkW
    (fun φ n => exteriorFactor38 φ n (lamDot φ n) - 1) isOpen_gkW
    (fun n => (exterior_critical_analytic38 n).sub analyticOnNhd_const)
    (fun φ hφ => (exterior_critical_l2_38 φ hφ).1)
  obtain ⟨B, hB, hBa⟩ := local_l2_analytic_realization38 gkW
    (fun φ n => deriv (exteriorFactor38 φ n) (lamDot φ n)) isOpen_gkW
    exterior_deriv_critical_analytic38 (fun φ hφ => (exterior_critical_l2_38 φ hφ).2)
  exact ⟨A, B, fun φ hφ n => ⟨hA φ hφ n, hB φ hφ n⟩, hAa, hBa⟩

theorem exterior_uniform_tail38 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧ ∃ N : ℕ,
      ∀ φ ∈ V, ∀ n : ℤ, (N : ℤ) < |n| →
        ‖exteriorFactor38 φ n (lamDot φ n) - 1‖ < ε ∧
          ‖deriv (exteriorFactor38 φ n) (lamDot φ n)‖ < ε := by
  obtain ⟨A, B, he, hAa, hBa⟩ := exterior_l2_realizations38
  obtain ⟨UA, hUA, NA, htA⟩ := l2_continuous_local_tails38 A φ₀ (hAa φ₀ hφ₀).continuousAt ε hε
  obtain ⟨UB, hUB, NB, htB⟩ := l2_continuous_local_tails38 B φ₀ (hBa φ₀ hφ₀).continuousAt ε hε
  refine ⟨UA ∩ (UB ∩ gkW), inter_mem hUA (inter_mem hUB (isOpen_gkW.mem_nhds hφ₀)),
    fun φ hφ => hφ.2.2, max NA NB, fun φ hφ n hn => ?_⟩
  have hNA : (NA : ℤ) ≤ (max NA NB : ℕ) := by exact_mod_cast le_max_left NA NB
  have hNB : (NB : ℤ) ≤ (max NA NB : ℕ) := by exact_mod_cast le_max_right NA NB
  rw [← (he φ hφ.2.2 n).1, ← (he φ hφ.2.2 n).2]
  exact ⟨htA φ hφ.1 n (hNA.trans_lt hn), htB φ hφ.2.1 n (hNB.trans_lt hn)⟩

end
end NlsGge.GK38
