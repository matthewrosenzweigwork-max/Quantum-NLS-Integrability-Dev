import Mathlib
import QuantumNLS.Local007Mul

/-! LOCAL-007 stage Z2: the conditional `ζ` clause, abstractly.

`ζ_n = g_n · s_n` with `s ∈ ℓ∞` analytic, `s(u) - 1 = O(‖u‖²)`, `D s(u) = O(‖u‖)`, and `g : E → ℓ²` analytic with
`g(0) = 0`, `‖Dg(u) - F‖ ≤ C_g ‖u‖²` (`F` of norm `≤ 1`): then `u ↦ s(u)·g(u)` is analytic into `ℓ²` and
`‖D(s g)(u) - F‖ ≤ K ‖u‖²` on the ball. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction Metric Set
namespace QuantumNLS.Local007Zeta
open QuantumNLS.Local007Mul (Seq mulCLM mulCLM_apply norm_mulSeq_le mulSeq)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mulCLM_one (g : Seq) : mulCLM (1 : ℤ →ᵇ ℝ) g = g := by
  apply lp.ext; funext n; simp [mulCLM_apply]

theorem zeta_clause {ρ Cs Cg : ℝ} (hρ : 0 < ρ) (hCs : 0 ≤ Cs) (hCg : 0 ≤ Cg)
    {ss : E → (ℤ →ᵇ ℝ)} (hss : AnalyticOnNhd ℝ ss (ball (0 : E) ρ))
    (hss1 : ∀ u ∈ ball (0 : E) ρ, ‖ss u - 1‖ ≤ Cs * ‖u‖ ^ 2)
    (hss2 : ∀ u ∈ ball (0 : E) ρ, ‖fderiv ℝ ss u‖ ≤ Cs * ‖u‖)
    {G : E → Seq} (hG : AnalyticOnNhd ℝ G (ball (0 : E) ρ)) (hG0 : G 0 = 0)
    (F : E →L[ℝ] Seq) (hF : ∀ h, ‖F h‖ ≤ ‖h‖)
    (hGd : ∀ u ∈ ball (0 : E) ρ, ‖fderiv ℝ G u - F‖ ≤ Cg * ‖u‖ ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ AnalyticOnNhd ℝ (fun u => mulCLM (ss u) (G u)) (ball (0 : E) ρ) ∧
      ∀ u ∈ ball (0 : E) ρ, ‖fderiv ℝ (fun w => mulCLM (ss w) (G w)) u - F‖ ≤ K * ‖u‖ ^ 2 := by
  set Kg : ℝ := 1 + Cg * ρ ^ 2 with hKg
  have hKg0 : 0 ≤ Kg := by positivity
  have hsubball : ∀ u ∈ ball (0 : E) ρ, closedBall (0 : E) ‖u‖ ⊆ ball (0 : E) ρ := by
    intro u hu y hy
    rw [mem_closedBall, dist_zero_right] at hy
    rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_lt hy (by simpa using hu)
  have hGdiff : ∀ y ∈ ball (0 : E) ρ, DifferentiableAt ℝ G y := fun y hy => (hG y hy).differentiableAt
  have hGb : ∀ u ∈ ball (0 : E) ρ, ‖G u‖ ≤ Kg * ‖u‖ := by
    intro u hu
    have hconv : Convex ℝ (closedBall (0 : E) ‖u‖) := convex_closedBall _ _
    have hmv := hconv.norm_image_sub_le_of_norm_fderiv_le (f := fun w => G w - F w) (C := Cg * ‖u‖ ^ 2)
      (fun y hy => (hGdiff y (hsubball u hu hy)).sub F.differentiableAt)
      (fun y hy => by
        have hyb := hsubball u hu hy
        have hh := ((hGdiff y hyb).hasFDerivAt.sub F.hasFDerivAt).fderiv
        have hh' : fderiv ℝ (fun w => G w - F w) y = fderiv ℝ G y - F := hh
        rw [hh']
        refine (hGd y hyb).trans ?_
        have : ‖y‖ ≤ ‖u‖ := by simpa [mem_closedBall, dist_zero_right] using hy
        have h2 : ‖y‖ ^ 2 ≤ ‖u‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
        exact mul_le_mul_of_nonneg_left h2 hCg)
      (show (0 : E) ∈ closedBall (0 : E) ‖u‖ by simp) (show u ∈ closedBall (0 : E) ‖u‖ by simp)
    simp only [hG0, map_zero, sub_zero, zero_sub, norm_neg] at hmv
    have h1 : ‖G u‖ ≤ ‖F u‖ + ‖G u - F u‖ := by
      calc ‖G u‖ = ‖F u + (G u - F u)‖ := by rw [add_sub_cancel]
        _ ≤ _ := norm_add_le _ _
    have hu2 : ‖u‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (by simpa using hu : ‖u‖ < ρ)) 2
    calc ‖G u‖ ≤ ‖u‖ + Cg * ‖u‖ ^ 2 * ‖u‖ := h1.trans (add_le_add (hF u) hmv)
      _ ≤ Kg * ‖u‖ := by
        rw [hKg]
        nlinarith [norm_nonneg u, mul_le_mul_of_nonneg_left hu2 hCg, mul_nonneg hCg (sq_nonneg ‖u‖)]
  refine ⟨Cs * Kg + Cs * (1 + Cg * ρ ^ 2) + Cg, by positivity, ?_, ?_⟩
  · intro u hu
    exact AnalyticAt.comp_of_eq (g := fun p : (ℤ →ᵇ ℝ) × Seq => mulCLM p.1 p.2) (f := fun x => (ss x, G x))
      (ContinuousLinearMap.analyticAt_bilinear mulCLM (ss u, G u)) ((hss u hu).prod (hG u hu)) rfl
  · intro u hu
    have hssd : HasFDerivAt ss (fderiv ℝ ss u) u := ((hss u hu).differentiableAt).hasFDerivAt
    have hGd0 : HasFDerivAt G (fderiv ℝ G u) u := (hGdiff u hu).hasFDerivAt
    have hpr := mulCLM.hasFDerivAt_of_bilinear hssd hGd0
    rw [hpr.fderiv]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    have e1 : (mulCLM.precompR E (ss u) (fderiv ℝ G u)) h = mulCLM (ss u) (fderiv ℝ G u h) := rfl
    have e2 : (mulCLM.precompL E (fderiv ℝ ss u) (G u)) h = mulCLM (fderiv ℝ ss u h) (G u) := rfl
    have e3 : mulCLM (ss u) (fderiv ℝ G u h) = mulCLM (ss u - 1) (fderiv ℝ G u h) + fderiv ℝ G u h := by
      rw [map_sub, ContinuousLinearMap.sub_apply, mulCLM_one]; abel
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, e1, e2, e3]
    have hsplit : mulCLM (ss u - 1) (fderiv ℝ G u h) + fderiv ℝ G u h + mulCLM (fderiv ℝ ss u h) (G u) - F h =
        mulCLM (fderiv ℝ ss u h) (G u) + mulCLM (ss u - 1) (fderiv ℝ G u h) + (fderiv ℝ G u h - F h) := by abel
    rw [hsplit]
    have hu2 : ‖u‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (le_of_lt (by simpa using hu : ‖u‖ < ρ)) 2
    have hnu : 0 ≤ ‖u‖ := norm_nonneg _
    have hdG : ‖fderiv ℝ G u h - F h‖ ≤ Cg * ‖u‖ ^ 2 * ‖h‖ := by
      have := (fderiv ℝ G u - F).le_opNorm h
      rw [ContinuousLinearMap.sub_apply] at this
      exact this.trans (mul_le_mul_of_nonneg_right (hGd u hu) (norm_nonneg _))
    have hT1 : ‖mulCLM (fderiv ℝ ss u h) (G u)‖ ≤ Cs * Kg * ‖u‖ ^ 2 * ‖h‖ := by
      have h1 := norm_mulSeq_le (fderiv ℝ ss u h) (G u)
      have h2 : ‖fderiv ℝ ss u h‖ ≤ Cs * ‖u‖ * ‖h‖ :=
        ((fderiv ℝ ss u).le_opNorm h).trans (mul_le_mul_of_nonneg_right (hss2 u hu) (norm_nonneg _))
      calc ‖mulCLM (fderiv ℝ ss u h) (G u)‖ ≤ ‖fderiv ℝ ss u h‖ * ‖G u‖ := h1
        _ ≤ (Cs * ‖u‖ * ‖h‖) * (Kg * ‖u‖) :=
            mul_le_mul h2 (hGb u hu) (norm_nonneg _) (by positivity)
        _ = Cs * Kg * ‖u‖ ^ 2 * ‖h‖ := by ring
    have hT2 : ‖mulCLM (ss u - 1) (fderiv ℝ G u h)‖ ≤ Cs * (1 + Cg * ρ ^ 2) * ‖u‖ ^ 2 * ‖h‖ := by
      have h1 := norm_mulSeq_le (ss u - 1) (fderiv ℝ G u h)
      have h2 : ‖fderiv ℝ G u h‖ ≤ (1 + Cg * ρ ^ 2) * ‖h‖ := by
        have h3 : ‖fderiv ℝ G u h‖ ≤ ‖F h‖ + ‖fderiv ℝ G u h - F h‖ := by
          calc ‖fderiv ℝ G u h‖ = ‖F h + (fderiv ℝ G u h - F h)‖ := by rw [add_sub_cancel]
            _ ≤ _ := norm_add_le _ _
        have h4 : Cg * ‖u‖ ^ 2 * ‖h‖ ≤ Cg * ρ ^ 2 * ‖h‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 hCg) (norm_nonneg _)
        nlinarith [hF h, norm_nonneg h]
      calc ‖mulCLM (ss u - 1) (fderiv ℝ G u h)‖ ≤ ‖ss u - 1‖ * ‖fderiv ℝ G u h‖ := h1
        _ ≤ (Cs * ‖u‖ ^ 2) * ((1 + Cg * ρ ^ 2) * ‖h‖) :=
            mul_le_mul (hss1 u hu) h2 (norm_nonneg _) (by positivity)
        _ = Cs * (1 + Cg * ρ ^ 2) * ‖u‖ ^ 2 * ‖h‖ := by ring
    calc ‖mulCLM (fderiv ℝ ss u h) (G u) + mulCLM (ss u - 1) (fderiv ℝ G u h) + (fderiv ℝ G u h - F h)‖
        ≤ ‖mulCLM (fderiv ℝ ss u h) (G u)‖ + ‖mulCLM (ss u - 1) (fderiv ℝ G u h)‖ + ‖fderiv ℝ G u h - F h‖ :=
          norm_add₃_le
      _ ≤ (Cs * Kg + Cs * (1 + Cg * ρ ^ 2) + Cg) * ‖u‖ ^ 2 * ‖h‖ := by nlinarith [hT1, hT2, hdG]

end QuantumNLS.Local007Zeta
#print axioms QuantumNLS.Local007Zeta.zeta_clause

