import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# `thm:reset-moser` (LOCAL-017), item 5c: operator Gronwall estimate for the variational equation

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "The full variational equation and Gronwall's inequality give
`‖DS_t(z) − 1‖ ≤ e^{C‖z‖²} − 1`, `‖DS_t(z)^{-1}‖ ≤ e^{C‖z‖²}`."

`gronwall_op`: if `U : ℝ → (X →L X)`, `U 0 = 1`, `U' = A U` and `‖A t‖ ≤ κ` on `[0,1]`, then `‖U t − 1‖ ≤ e^{κ t} − 1 ≤ κ e^{κ}` on `[0,1]` (Mathlib's
`norm_le_gronwallBound_of_norm_deriv_right_le`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section

open Set

namespace QuantumNLS.ResetMoserGronwallOp

theorem exp_sub_one_le {y : ℝ} (hy : 0 ≤ y) : Real.exp y - 1 ≤ y * Real.exp y := by
  have h := Real.add_one_le_exp (-y)
  have e : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos y]

theorem gronwall_op {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    {U A : ℝ → X →L[ℝ] X} {κ : ℝ} (hκ : 0 ≤ κ) (hU0 : U 0 = 1)
    (hd : ∀ t, HasDerivAt U (A t * U t) t) (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖A t‖ ≤ κ) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖U t - 1‖ ≤ Real.exp κ - 1 ∧ ‖U t - 1‖ ≤ κ * Real.exp κ := by
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => U t - 1)
    (f' := fun t => A t * U t) (δ := 0) (K := κ) (ε := κ) (a := 0) (b := 1)
    (fun x _ => ((hd x).sub_const 1).continuousAt.continuousWithinAt)
    (fun x _ => ((hd x).sub_const 1).hasDerivWithinAt)
    (by simp [hU0])
    (fun x hx => by
      have h1 : ‖A x * U x‖ ≤ ‖A x‖ * ‖U x‖ := ContinuousLinearMap.opNorm_comp_le (A x) (U x)
      have h2 : ‖U x‖ ≤ ‖U x - 1‖ + 1 := by
        calc ‖U x‖ = ‖(U x - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖U x - 1‖ + ‖(1 : X →L[ℝ] X)‖ := norm_add_le _ _
          _ ≤ ‖U x - 1‖ + 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      have h3 := hA x ⟨hx.1, hx.2.le⟩
      calc ‖A x * U x‖ ≤ ‖A x‖ * ‖U x‖ := h1
        _ ≤ κ * (‖U x - 1‖ + 1) := mul_le_mul h3 h2 (norm_nonneg _) hκ
        _ = κ * ‖U x - 1‖ + κ := by ring)
  intro t ht
  have h := hG t ht
  simp only [sub_zero] at h
  by_cases hk : κ = 0
  · subst hk
    simp [gronwallBound] at h
    simp [h]
  · have e : gronwallBound 0 κ κ t = Real.exp (κ * t) - 1 := by
      simp [gronwallBound, hk]
    rw [e] at h
    have h1 : Real.exp (κ * t) ≤ Real.exp κ := Real.exp_le_exp.2 (by nlinarith [ht.2, ht.1])
    refine ⟨h.trans (by linarith), h.trans ?_⟩
    have := exp_sub_one_le (mul_nonneg hκ ht.1)
    calc Real.exp (κ * t) - 1 ≤ κ * t * Real.exp (κ * t) := this
      _ ≤ κ * 1 * Real.exp κ := by
          apply mul_le_mul _ h1 (Real.exp_pos _).le (by positivity)
          nlinarith [ht.2]
      _ = κ * Real.exp κ := by ring

end QuantumNLS.ResetMoserGronwallOp

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoserGronwallOp.gronwall_op
