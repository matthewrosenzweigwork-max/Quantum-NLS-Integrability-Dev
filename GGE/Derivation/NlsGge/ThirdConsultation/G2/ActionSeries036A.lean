import Mathlib

set_option autoImplicit false
open Set Filter Topology Metric Finset
noncomputable section

namespace NlsGge.GKDefinitionDesign

theorem schwarz_l1_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℤ → E → ℂ) {x₀ : E} {r B : ℝ} (hr : 0 < r)
    (hd : ∀ n, DifferentiableOn ℂ (a n) (ball x₀ r))
    (hs : ∀ y ∈ ball x₀ r, Summable (fun n => ‖a n y‖) ∧ ∑' n, ‖a n y‖ ≤ B)
    {y : E} (hy : y ∈ ball x₀ r) :
    Summable (fun n => ‖a n y - a n x₀‖) ∧
      ∑' n, ‖a n y - a n x₀‖ ≤ (2 * B + 1) / r * ‖y - x₀‖ := by
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hB0 : 0 ≤ B := (tsum_nonneg (fun n => norm_nonneg _)).trans (hs x₀ hx₀).2
  set k : E := y - x₀ with hk
  set ρ : ℝ := ‖k‖ with hρ
  have hρr : ρ < r := by simpa [mem_ball, dist_eq_norm, hk, hρ] using hy
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hfin : ∀ S : Finset ℤ, ∑ n ∈ S, ‖a n y - a n x₀‖ ≤ (2 * B + 1) / r * ρ := by
    intro S
    rcases hρ0.eq_or_lt with h0 | hpos
    · have hk0 : k = 0 := norm_eq_zero.1 h0.symm
      have hyx : y = x₀ := sub_eq_zero.1 hk0
      subst hyx
      simp [← h0]
    · set R : ℝ := r / ρ with hR
      have hR1 : 1 < R := by rw [hR, lt_div_iff₀ hpos]; linarith
      have hR0 : 0 < R := by linarith
      let g : ℤ → ℂ → ℂ := fun n t => a n (x₀ + t • k) - a n x₀
      let ε : ℤ → ℂ := fun n =>
        if (g n 1) = 0 then 1 else (starRingEnd ℂ (g n 1)) / ((‖g n 1‖ : ℝ) : ℂ)
      have hε1 : ∀ n, ‖ε n‖ ≤ 1 := by
        intro n
        by_cases h : g n 1 = 0
        · simp [ε, h]
        · have hn : 0 < ‖g n 1‖ := norm_pos_iff.2 h
          simp only [ε, h, if_false, norm_div, Complex.norm_conj, Complex.norm_real,
            norm_norm]
          rw [div_self hn.ne']
      have hεg : ∀ n, ε n * g n 1 = ((‖g n 1‖ : ℝ) : ℂ) := by
        intro n
        by_cases h : g n 1 = 0
        · simp [ε, h]
        · have hn : ((‖g n 1‖ : ℝ) : ℂ) ≠ 0 := by
            exact_mod_cast (norm_pos_iff.2 h).ne'
          simp only [ε, h, if_false]
          rw [div_mul_eq_mul_div, div_eq_iff hn, Complex.conj_mul']
          push_cast; ring
      let G : ℂ → ℂ := fun t => ∑ n ∈ S, ε n * g n t
      have hmaps : ∀ t ∈ ball (0 : ℂ) R, x₀ + t • k ∈ ball x₀ r := by
        intro t ht
        rw [mem_ball_zero_iff] at ht
        rw [mem_ball, dist_eq_norm]
        simp only [add_sub_cancel_left, norm_smul]
        calc ‖t‖ * ρ < R * ρ := mul_lt_mul_of_pos_right ht hpos
          _ = r := by rw [hR]; field_simp
      have hGd : DifferentiableOn ℂ G (ball (0 : ℂ) R) := by
        have hGs : G = ∑ n ∈ S, (fun t : ℂ => ε n * g n t) := by
          funext t; simp [G, Finset.sum_apply]
        rw [hGs]
        apply DifferentiableOn.sum
        intro n _
        apply DifferentiableOn.const_mul
        apply DifferentiableOn.sub _ (differentiableOn_const _)
        have hlin : DifferentiableOn ℂ (fun t : ℂ => x₀ + t • k) (ball (0 : ℂ) R) := by
          apply Differentiable.differentiableOn; fun_prop
        exact (hd n).comp hlin hmaps
      have hG0 : G 0 = 0 := by simp [G, g]
      have hGmaps : MapsTo G (ball (0 : ℂ) R) (closedBall (G 0) (2 * B)) := by
        intro t ht
        rw [hG0, mem_closedBall_zero_iff]
        have hmem := hmaps t ht
        have hsum1 := (hs _ hmem).1
        have hsum0 := (hs x₀ hx₀).1
        calc ‖G t‖ ≤ ∑ n ∈ S, ‖ε n * g n t‖ := norm_sum_le _ _
          _ ≤ ∑ n ∈ S, (‖a n (x₀ + t • k)‖ + ‖a n x₀‖) := by
              apply Finset.sum_le_sum
              intro n _
              rw [norm_mul]
              have := hε1 n
              have h2 : ‖g n t‖ ≤ ‖a n (x₀ + t • k)‖ + ‖a n x₀‖ := norm_sub_le _ _
              calc ‖ε n‖ * ‖g n t‖ ≤ 1 * ‖g n t‖ :=
                    mul_le_mul_of_nonneg_right this (norm_nonneg _)
                _ ≤ _ := by rw [one_mul]; exact h2
          _ = ∑ n ∈ S, ‖a n (x₀ + t • k)‖ + ∑ n ∈ S, ‖a n x₀‖ := Finset.sum_add_distrib
          _ ≤ B + B := by
              gcongr
              · exact (hsum1.sum_le_tsum S (fun _ _ => norm_nonneg _)).trans (hs _ hmem).2
              · exact (hsum0.sum_le_tsum S (fun _ _ => norm_nonneg _)).trans (hs x₀ hx₀).2
          _ = 2 * B := by ring
      have h1 : (1 : ℂ) ∈ ball (0 : ℂ) R := by
        rw [mem_ball_zero_iff]; simpa using hR1
      have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hGd hGmaps h1
      rw [hG0, dist_zero_right, dist_zero_right] at hsch
      have hG1 : G 1 = ((∑ n ∈ S, ‖a n y - a n x₀‖ : ℝ) : ℂ) := by
        simp only [G, g, one_smul, hk, add_sub_cancel]
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        have := hεg n
        simpa [g, hk] using this
      rw [hG1, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))] at hsch
      simp only [norm_one, mul_one] at hsch
      calc ∑ n ∈ S, ‖a n y - a n x₀‖ ≤ 2 * B / R := hsch
        _ ≤ (2 * B + 1) / R := by gcongr; linarith
        _ = (2 * B + 1) / r * ρ := by rw [hR]; field_simp
  have hnn : ∀ n, 0 ≤ ‖a n y - a n x₀‖ := fun _ => norm_nonneg _
  exact ⟨summable_of_sum_le hnn hfin, tsum_le_of_sum_le' (by positivity) hfin⟩

end NlsGge.GKDefinitionDesign
end
