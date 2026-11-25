import NlsGge.GK38.TauGammaValueBounds
import NlsGge.GK38.TauGammaCriticalTails

/-! Pointwise square sums give a common coordinate bound, without being used to invent tails. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem local_l2_coordinate_bound38 (a : PotPair → ℤ → ℂ) (φ₀ : PotPair)
    (ha : IsLocUnifL2Seq a φ₀) : ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ φ ∈ U, ∀ n : ℤ, ‖a φ n‖ ≤ K := by
  obtain ⟨U, hU, C, h⟩ := ha
  let T := max C 0
  have hT : 0 ≤ T := le_max_right C 0
  refine ⟨U, hU, T + 1, by positivity, fun φ hφ n => ?_⟩
  have ht := (h φ hφ).1.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
  have hpoint : ‖a φ n‖ ^ 2 ≤ T := by
    have ht' : ‖a φ n‖ ^ 2 ≤ ∑' m : ℤ, ‖a φ m‖ ^ 2 := by simpa only [Finset.sum_singleton] using ht
    exact ht'.trans ((h φ hφ).2.trans (le_max_left C 0))
  nlinarith [norm_nonneg (a φ n), sq_nonneg T]

theorem critical_delta_local_bound38 (C : PotPair → ℤ → ℂ) (R : PotPair → ℤ → ℝ)
    (hsel : AdmissibleSelectors38 C R) (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair, U ∈ 𝓝 φ₀ ∧ U ⊆ gkW ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ φ ∈ U, ∀ n : ℤ, ‖lamDot φ n - tauN38 C R φ n‖ ≤ K := by
  have hcrit : IsLocUnifL2Seq (fun φ n => lamDot φ n - (n : ℂ) * (Real.pi : ℂ)) φ₀ := by
    obtain ⟨V, hV, B, _, h⟩ := critical_l2 φ₀
    exact ⟨V, hV, B, h⟩
  obtain ⟨U₁, hU₁, K₁, hK₁, h₁⟩ := local_l2_coordinate_bound38 _ φ₀ hcrit
  obtain ⟨U₂, hU₂, K₂, hK₂, h₂⟩ := local_l2_coordinate_bound38 _ φ₀
    (tauGamma_l2_38 C R hsel φ₀ hφ₀).1
  refine ⟨U₁ ∩ (U₂ ∩ gkW), inter_mem hU₁ (inter_mem hU₂ (isOpen_gkW.mem_nhds hφ₀)),
    fun φ hφ => hφ.2.2, K₁ + K₂, add_nonneg hK₁ hK₂, fun φ hφ n => ?_⟩
  have he : lamDot φ n - tauN38 C R φ n =
      (lamDot φ n - (n : ℂ) * (Real.pi : ℂ)) - (tauN38 C R φ n - (n : ℂ) * (Real.pi : ℂ)) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add (h₁ φ hφ.1 n) (h₂ φ hφ.2.1 n))

end
end NlsGge.GK38
