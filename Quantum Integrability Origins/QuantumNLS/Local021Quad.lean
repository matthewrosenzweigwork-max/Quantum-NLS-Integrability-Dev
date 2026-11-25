import Mathlib

/-!
# LOCAL-021, stage 6: an odd real-analytic map has a quadratic differential error

Used for the unit-coupling quadratic bound `‖Dζ(u) - 𝓕‖ ≤ C ‖u‖²` of the exact-modulus map: the phase covariance
`ζ(e^{iπ}u) = e^{iπ}ζ(u)` makes `ζ` odd, so (full operator-norm analyticity at `0`) `D²ζ(0) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048
noncomputable section

open scoped Topology
open Filter Set Metric

namespace QuantumNLS.Local021

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_comp_neg' {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : E → V) (x : E) :
    fderiv ℝ (fun y => h (-y)) x = -fderiv ℝ h (-x) := by
  have h1 := (ContinuousLinearEquiv.neg ℝ (M := E)).comp_right_fderiv (f := h) (x := x)
  have h2 : (fun y => h (-y)) = h ∘ ⇑(ContinuousLinearEquiv.neg ℝ (M := E)) := rfl
  rw [h2, h1]
  ext v
  simp

/-- `f` odd near `0` and `C³` at `0` give `‖Df(x) - Df(0)‖ ≤ C‖x‖²` near `0`. -/
theorem quad_of_odd {f : E → F} (hf : ContDiffAt ℝ 3 f 0) (hodd : ∀ᶠ x in 𝓝 (0 : E), f (-x) = -f x) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ x : E, ‖x‖ < δ → ‖fderiv ℝ f x - fderiv ℝ f 0‖ ≤ C * ‖x‖ ^ 2 := by
  set g : E → (E →L[ℝ] F) := fderiv ℝ f with hg
  have hg2 : ContDiffAt ℝ 2 g 0 := hf.fderiv_right (by norm_num)
  -- g is even near 0
  have hgeven : ∀ᶠ x in 𝓝 (0 : E), g (-x) = g x := by
    filter_upwards [hodd.eventually_nhds] with x hx
    have h1 : (fun y => f (-y)) =ᶠ[𝓝 x] fun y => -f y := hx
    have h2 := h1.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp_neg', fderiv_fun_neg] at h2
    exact (neg_inj.1 h2)
  -- G = fderiv g is odd at 0, hence G 0 = 0
  have hG0 : fderiv ℝ g 0 = 0 := by
    have h1 : (fun y => g (-y)) =ᶠ[𝓝 (0 : E)] g := hgeven
    have h2 := h1.fderiv_eq (𝕜 := ℝ)
    rw [fderiv_comp_neg', neg_zero] at h2
    have h3 : (2 : ℝ) • fderiv ℝ g 0 = 0 :=
      (two_smul ℝ (fderiv ℝ g 0)).trans (by nth_rewrite 2 [h2.symm]; exact add_neg_cancel _)
    exact (smul_eq_zero.1 h3).resolve_left (by norm_num)
  -- Lipschitz bound on G = fderiv g near 0
  have hG1 : ContDiffAt ℝ 1 (fderiv ℝ g) 0 := hg2.fderiv_right (by norm_num)
  obtain ⟨M, t, ht, hlip⟩ := hG1.exists_lipschitzOnWith
  have hGev : ∀ᶠ x in 𝓝 (0 : E), ContDiffAt ℝ 2 g x := hg2.eventually (by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hGev.and ht)
  have hdiffg : ∀ x ∈ ball (0 : E) δ, DifferentiableAt ℝ g x := fun x hx =>
    ((hball (by simpa using hx)).1.differentiableAt (by norm_num))
  have hG_le : ∀ x ∈ ball (0 : E) δ, ‖fderiv ℝ g x‖ ≤ M * ‖x‖ := by
    intro x hx
    have h0 : (0 : E) ∈ t := mem_of_mem_nhds ht
    have := hlip.dist_le_mul x (hball (by simpa using hx)).2 0 h0
    simpa [hG0, dist_eq_norm] using this
  have hM0 : 0 ≤ (M : ℝ) := M.2
  refine ⟨M, δ, hM0, hδ, fun x hx => ?_⟩
  have hxs : closedBall (0 : E) ‖x‖ ⊆ ball (0 : E) δ := by
    intro y hy
    rw [mem_closedBall_zero_iff] at hy
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hy hx
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (𝕜 := ℝ) (s := closedBall (0 : E) ‖x‖) (C := M * ‖x‖)
    (fun y hy => hdiffg y (hxs hy))
    (fun y hy => by
      have h1 := hG_le y (hxs hy)
      rw [mem_closedBall_zero_iff] at hy
      exact h1.trans (mul_le_mul_of_nonneg_left hy hM0))
    (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg x))
    (by rw [mem_closedBall_zero_iff])
  simpa [pow_two, mul_assoc] using this

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.quad_of_odd
