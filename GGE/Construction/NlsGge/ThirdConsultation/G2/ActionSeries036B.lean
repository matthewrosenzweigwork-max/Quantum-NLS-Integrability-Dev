import Mathlib
import NlsGge.ThirdConsultation.G2.ActionSeries036A

set_option autoImplicit false
open Set Filter Topology Metric Finset
noncomputable section

namespace NlsGge.GKDefinitionDesign

theorem tail_le_of_l1_lip {X : Type*} [NormedAddCommGroup X] (a : ℤ → X → ℂ) (x₀ y : X) (L : ℝ)
    (h0 : Summable (fun n => ‖a n x₀‖)) (h1 : Summable (fun n => ‖a n y‖))
    (hL : ∑' n, ‖a n y - a n x₀‖ ≤ L * ‖y - x₀‖) (F : Finset ℤ) :
    ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i y‖ ≤
      ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i x₀‖ + L * ‖y - x₀‖ := by
  have hd : Summable (fun n => ‖a n y - a n x₀‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_sub_le _ _) (h1.add h0)
  have hdn : ∀ n, 0 ≤ ‖a n y - a n x₀‖ := fun _ => norm_nonneg _
  calc ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i y‖
      ≤ ∑' i : ↥((F : Set ℤ)ᶜ), (‖a i x₀‖ + ‖a i y - a i x₀‖) := by
        apply Summable.tsum_le_tsum
        · intro i
          have := norm_le_norm_add_norm_sub' (a i y) (a i x₀)
          have h2 : ‖a i y‖ ≤ ‖a i x₀‖ + ‖a i y - a i x₀‖ := by
            calc ‖a i y‖ = ‖a i x₀ + (a i y - a i x₀)‖ := by rw [add_sub_cancel]
              _ ≤ _ := norm_add_le _ _
          exact h2
        · exact h1.subtype _
        · exact (h0.add hd).subtype _
    _ = ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i x₀‖ + ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i y - a i x₀‖ :=
        (h0.subtype _).tsum_add (hd.subtype _)
    _ ≤ _ := by
        have h3 := hd.sum_add_tsum_compl (s := F)
        have h4 : 0 ≤ ∑ n ∈ F, ‖a n y - a n x₀‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
        linarith

theorem hasSumLocUnif_of_l1_lip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Set E) (a : ℤ → E → ℂ)
    (h : ∀ x₀ ∈ s, ∃ V ∈ 𝓝 x₀, ∃ L : ℝ, Summable (fun n => ‖a n x₀‖) ∧
      ∀ y ∈ V, Summable (fun n => ‖a n y‖) ∧
        ∑' n, ‖a n y - a n x₀‖ ≤ L * ‖y - x₀‖) :
    HasSumLocallyUniformlyOn (fun n y => ‖a n y‖) (fun y => ∑' n, ‖a n y‖) s ∧
    HasSumLocallyUniformlyOn a (fun y => ∑' n, a n y) s := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ x₀ ∈ s, ∃ t ∈ 𝓝[s] x₀, (∀ y ∈ t, Summable (fun n => ‖a n y‖)) ∧
      ∀ᶠ F : Finset ℤ in atTop, ∀ y ∈ t,
      ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i y‖ < ε := by
    intro ε hε x₀ hx₀
    obtain ⟨V, hV, L, h0, hy⟩ := h x₀ hx₀
    have hy' := hy
    set L' : ℝ := max L 0 + 1 with hL'
    have hL'pos : 0 < L' := by positivity
    refine ⟨V ∩ ball x₀ (ε / (2 * L')), mem_nhdsWithin_of_mem_nhds
      (inter_mem hV (ball_mem_nhds _ (by positivity))),
      fun y hy => (hy' y hy.1).1, ?_⟩
    have hT : ∀ᶠ F : Finset ℤ in atTop, ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i x₀‖ < ε / 2 := by
      have hs := h0.hasSum
      have hev : ∀ᶠ F : Finset ℤ in atTop, (∑' n, ‖a n x₀‖) - ε / 2 < ∑ n ∈ F, ‖a n x₀‖ :=
        (tendsto_order.1 hs).1 _ (by linarith)
      filter_upwards [hev] with F hF
      have := h0.sum_add_tsum_compl (s := F)
      linarith
    filter_upwards [hT] with F hF y hyt
    obtain ⟨hy1, hy2⟩ := hy y hyt.1
    have hb := tail_le_of_l1_lip a x₀ y L h0 hy1 hy2 F
    have hd : ‖y - x₀‖ < ε / (2 * L') := by
      have := hyt.2; rwa [mem_ball, dist_eq_norm] at this
    have hLn : L * ‖y - x₀‖ ≤ L' * ‖y - x₀‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [hL']; linarith [le_max_left L 0]
    have h2 : L' * ‖y - x₀‖ < ε / 2 := by
      calc L' * ‖y - x₀‖ < L' * (ε / (2 * L')) := mul_lt_mul_of_pos_left hd hL'pos
        _ = ε / 2 := by field_simp
    linarith
  refine ⟨?_, ?_⟩
  · rw [HasSumLocallyUniformlyOn, Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x₀ hx₀
    obtain ⟨t, ht, hsum, hev⟩ := key ε hε x₀ hx₀
    refine ⟨t, ht, hev.mono fun F hF y hy => ?_⟩
    have h1 := (hsum y hy).sum_add_tsum_compl (s := F)
    have hnn : 0 ≤ ∑' i : ↥((F : Set ℤ)ᶜ), ‖a i y‖ := tsum_nonneg (fun _ => norm_nonneg _)
    rw [Real.dist_eq, ← h1]
    simp only [add_sub_cancel_left, abs_of_nonneg hnn]
    exact hF y hy
  · rw [HasSumLocallyUniformlyOn, Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x₀ hx₀
    obtain ⟨t, ht, hsum, hev⟩ := key ε hε x₀ hx₀
    refine ⟨t, ht, hev.mono fun F hF y hy => ?_⟩
    have h1 := (Summable.of_norm (hsum y hy)).sum_add_tsum_compl (s := F)
    rw [dist_eq_norm, ← h1]
    simp only [add_sub_cancel_left]
    exact lt_of_le_of_lt (norm_tsum_le_tsum_norm ((hsum y hy).subtype _)) (hF y hy)

end NlsGge.GKDefinitionDesign
end
