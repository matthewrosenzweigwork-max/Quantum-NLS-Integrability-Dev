import Mathlib

/- G6039 SUP2 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6039Sup2Core.lean, namespace NlsGge.ThirdConsultation.G6039S.  SUPPORT (no packet
   increment) for the analyticity clause of Pro's parametric_even_tail_descent: a Lipschitz bound for a bounded
   holomorphic function on a Banach ball, from Mathlib's Schwarz lemma Complex.dist_le_div_mul_dist_of_mapsTo_ball
   (Analysis/Complex/Schwarz.lean:189 in this repo's pinned Mathlib d13f23b7).  This gives the uniform convergence
   of the finite-tail descents (Pro: "local boundedness ... jointly in P and the action tail"). -/
set_option autoImplicit false

open Set Metric

namespace NlsGge.ThirdConsultation.G6039S
noncomputable section

theorem lipschitz_of_bdd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → ℂ) (r ρ M : ℝ) (hρr : ρ < r)
    (hg : DifferentiableOn ℂ g (ball (0 : E) r)) (hM : ∀ x ∈ ball (0 : E) r, ‖g x‖ ≤ M)
    (x y : E) (hx : ‖x‖ ≤ ρ) (hy : ‖y‖ ≤ ρ) :
    ‖g x - g y‖ ≤ 2 * M / (r - ρ) * ‖x - y‖ := by
  have hrρ : 0 < r - ρ := sub_pos.2 hρr
  have hyb : y ∈ ball (0 : E) r := by rw [mem_ball, dist_zero_right]; linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y hyb)
  have hsub : ball y (r - ρ) ⊆ ball (0 : E) r := by
    intro z hz
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ < (r - ρ) + ρ := by linarith
      _ = r := by ring
  have h2 : ∀ z ∈ ball (0 : E) r, ‖g z - g y‖ ≤ 2 * M := fun z hz =>
    (norm_sub_le _ _).trans (by linarith [hM z hz, hM y hyb])
  by_cases hxy : x ∈ ball y (r - ρ)
  · have hmaps : MapsTo g (ball y (r - ρ)) (closedBall (g y) (2 * M)) := fun z hz => by
      rw [mem_closedBall, dist_eq_norm]; exact h2 z (hsub hz)
    have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (hg.mono hsub) hmaps hxy
    rwa [dist_eq_norm, dist_eq_norm] at h
  · have hd : r - ρ ≤ ‖x - y‖ := by
      rw [mem_ball, dist_eq_norm, not_lt] at hxy; exact hxy
    have hxb : x ∈ ball (0 : E) r := by rw [mem_ball, dist_zero_right]; linarith
    calc ‖g x - g y‖ ≤ 2 * M := h2 x hxb
      _ = 2 * M / (r - ρ) * (r - ρ) := by field_simp
      _ ≤ 2 * M / (r - ρ) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_left hd (div_nonneg (by linarith) hrρ.le)

end
end NlsGge.ThirdConsultation.G6039S
