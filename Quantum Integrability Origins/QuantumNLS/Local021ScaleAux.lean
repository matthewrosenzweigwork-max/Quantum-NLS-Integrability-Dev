import Mathlib

/-!
# LOCAL-021, stage 4 (auxiliary): the derivative of a map under a dilation relation

If `f(s x) = c • g(x)` near `z` (`s ≠ 0`, `c ≠ 0`) then `Df(s z) = (s⁻¹ c) • Dg(z)`.  (Both sides are `0` when `g`, equivalently `f`, is not differentiable.)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open scoped Topology
open Filter Set Metric

namespace QuantumNLS.Local021

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_smul_scale {f g : E → F} {s c : ℝ} (hs : s ≠ 0) (hc : c ≠ 0) {z : E}
    (hev : (fun x => f (s • x)) =ᶠ[𝓝 z] fun x => c • g x) :
    fderiv ℝ f (s • z) = (s⁻¹ * c) • fderiv ℝ g z := by
  have hlin : HasFDerivAt (fun x : E => s • x) (s • ContinuousLinearMap.id ℝ E) z :=
    (hasFDerivAt_id z).const_smul s
  have hlin' : HasFDerivAt (fun w : E => s⁻¹ • w) (s⁻¹ • ContinuousLinearMap.id ℝ E) (s • z) :=
    (hasFDerivAt_id (s • z)).const_smul s⁻¹
  have hz' : s⁻¹ • s • z = z := inv_smul_smul₀ hs z
  by_cases hg : DifferentiableAt ℝ g z
  · have h1 : HasFDerivAt (fun x => c • g x) (c • fderiv ℝ g z) z := hg.hasFDerivAt.const_smul c
    have h2 : HasFDerivAt (fun x => f (s • x)) (c • fderiv ℝ g z) z := h1.congr_of_eventuallyEq hev
    have h2' : HasFDerivAt (fun x => f (s • x)) (c • fderiv ℝ g z) (s⁻¹ • s • z) := by rw [hz']; exact h2
    have h3 := h2'.comp (s • z) hlin'
    have h4 : ((fun x => f (s • x)) ∘ fun w : E => s⁻¹ • w) = f := by
      funext w; simp [smul_inv_smul₀ hs]
    rw [h4] at h3
    rw [h3.fderiv]
    ext v
    simp [smul_smul, mul_comm]
  · have hf : ¬ DifferentiableAt ℝ f (s • z) := by
      intro hf
      apply hg
      have h5 : DifferentiableAt ℝ (fun x => f (s • x)) z := hf.comp z hlin.differentiableAt
      have h6 : DifferentiableAt ℝ (fun x => c • g x) z := h5.congr_of_eventuallyEq hev.symm
      have h7 := h6.const_smul c⁻¹
      refine h7.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      simp [smul_smul, inv_mul_cancel₀ hc]
    rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hg]; simp

end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.fderiv_smul_scale
