import Mathlib
import NlsGge.ThirdConsultation.G2.ActionSeries036A
import NlsGge.GK38.ContourAction
import NlsGge.GK38.TauGammaValueBounds
import NlsGge.GK38.TauGammaContourGlue
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.XiSqCanonical
import NlsGge.GK38.XiSqFullEstimates

set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38
noncomputable section

namespace NlsGge.GKDefinitionDesign

/-- Local l1 bound of the action series on a ball (4 action = gamma2 * xiSq). -/
theorem gk_action_local_l1 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ r : ℝ, 0 < r ∧ ball φ₀ r ⊆ gkW ∧ ∃ B : ℝ,
      ∀ y ∈ ball φ₀ r, Summable (fun n : ℤ => ‖gkActionC38 y n‖) ∧
        ∑' n : ℤ, ‖gkActionC38 y n‖ ≤ B := by
  obtain ⟨V₁, hV₁, -, B₁, hB₁, h1⟩ :=
    tauGamma_common_value_bound38 discC discR isolating_selectors_admissible38 φ₀ hφ₀
  obtain ⟨U, hU, c, hc⟩ := a5XiSqError_l2_38 xiSq38 xiSq38_spec φ₀ hφ₀
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1
    (inter_mem (inter_mem hV₁ hU) (isOpen_gkW.mem_nhds hφ₀))
  refine ⟨r, hr, fun y hy => (hsub hy).2, (2 + c) / 4 * B₁, fun y hy => ?_⟩
  have hyV := (hsub hy).1.1
  have hyU := (hsub hy).1.2
  have hyW := (hsub hy).2
  obtain ⟨-, -, hgs, -, -, hgb⟩ := h1 y hyV
  obtain ⟨hxs, hxb⟩ := hc y hyU
  have hxi : ∀ n : ℤ, ‖xiSq38 n y‖ ≤ 2 + c := by
    intro n
    have hterm : ‖xiSq38 n y - 1‖ ^ 2 ≤ c := by
      have := hxs.le_tsum n (fun j _ => sq_nonneg _)
      exact this.trans hxb
    have h2 : ‖xiSq38 n y - 1‖ ≤ 1 + c := by
      by_cases h : ‖xiSq38 n y - 1‖ ≤ 1
      · have : 0 ≤ c := (sq_nonneg _).trans hterm
        linarith
      · push_neg at h
        nlinarith [norm_nonneg (xiSq38 n y - 1)]
    calc ‖xiSq38 n y‖ = ‖(xiSq38 n y - 1) + 1‖ := by rw [sub_add_cancel]
      _ ≤ ‖xiSq38 n y - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 + c := by rw [norm_one]; linarith
  have hγ : Summable (fun n : ℤ => ‖gamma2 y n‖) := hgs
  have hγb : ∑' n : ℤ, ‖gamma2 y n‖ ≤ B₁ := hgb
  have hle : ∀ n : ℤ, ‖gkActionC38 y n‖ ≤ (2 + c) / 4 * ‖gamma2 y n‖ := by
    intro n
    have hm := xiSq38_multiplied n y hyW
    have h4 : ‖gkActionC38 y n‖ = ‖gamma2 y n‖ * ‖xiSq38 n y‖ / 4 := by
      have : ‖(4 : ℂ) * gkActionC38 y n‖ = ‖gamma2 y n * xiSq38 n y‖ := by rw [hm]
      rw [norm_mul, norm_mul] at this
      have h4' : ‖(4 : ℂ)‖ = 4 := by simp
      rw [h4'] at this
      linarith
    rw [h4]
    have := hxi n
    have h0 := norm_nonneg (gamma2 y n)
    nlinarith
  have hsum : Summable (fun n : ℤ => ‖gkActionC38 y n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hγ.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' n : ℤ, ‖gkActionC38 y n‖ ≤ ∑' n : ℤ, (2 + c) / 4 * ‖gamma2 y n‖ :=
        hsum.tsum_le_tsum hle (hγ.mul_left _)
    _ = (2 + c) / 4 * ∑' n : ℤ, ‖gamma2 y n‖ := tsum_mul_left
    _ ≤ (2 + c) / 4 * B₁ := by
        have hc0 : 0 ≤ c := by
          have := hxs.le_tsum 0 (fun j _ => sq_nonneg _)
          exact (sq_nonneg _).trans (this.trans hxb)
        exact mul_le_mul_of_nonneg_left hγb (by positivity)

end NlsGge.GKDefinitionDesign
end
