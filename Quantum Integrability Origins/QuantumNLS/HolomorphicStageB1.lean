import Mathlib
import QuantumNLS.HolomorphicCauchyC1

/-!
# C2 stage B1: Cauchy representation of the derivative and the second-order remainder

For `f : E → F` (complex normed spaces, `F` complete) with `DifferentiableOn ℂ f U`, `U` open:
* `fderiv_apply_eq_circleIntegral`: if `y + ζ • v ∈ U` for `‖ζ‖ ≤ 1`, then
  `fderiv ℂ f y v = (2πi)⁻¹ • ∮_{|ζ|=1} ζ⁻² • f (y + ζ • v)` (one-variable Cauchy formula on the slice,
  `DifferentiableOn.deriv_eq_smul_circleIntegral`);
* `norm_sub_sub_fderiv_le`: on a convex set `S ⊆ U` where `fderiv ℂ f` is `Λ`-Lipschitz,
  `‖f (w + k) − f w − fderiv ℂ f w k‖ ≤ Λ ‖k‖²` (real mean value inequality along the segment).

These are the ingredients of stage B (complex differentiability of `fderiv ℂ f`), not the full stage B.
Standard axioms only.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric Complex Set

namespace QuantumNLS.HolomorphicStageB1

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem fderiv_apply_eq_circleIntegral {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : DifferentiableOn ℂ f U) {y v : E} (hy : y ∈ U) (hyv : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → y + ζ • v ∈ U) :
    fderiv ℂ f y v = (2 * Real.pi * Complex.I)⁻¹ •
      ∮ ζ in C(0, 1), (1 / ζ ^ 2) • f (y + ζ • v) := by
  have hg : DifferentiableOn ℂ (fun ζ : ℂ => f (y + ζ • v)) (closedBall 0 1) := by
    intro ζ hζ
    rw [mem_closedBall_zero_iff] at hζ
    have hd : DifferentiableAt ℂ f (y + ζ • v) := hf.differentiableAt (hU.mem_nhds (hyv ζ hζ))
    have hl : DifferentiableAt ℂ (fun s : ℂ => y + s • v) ζ := by fun_prop
    exact (hd.comp ζ hl).differentiableWithinAt
  have key := hg.deriv_eq_smul_circleIntegral zero_lt_one
  have hd0 : DifferentiableAt ℂ f y := hf.differentiableAt (hU.mem_nhds hy)
  have hderiv : deriv (fun ζ : ℂ => f (y + ζ • v)) 0 = fderiv ℂ f y v :=
    (QuantumNLS.HolomorphicCauchyC1.hasDerivAt_line hd0 v).deriv
  simp only [sub_zero] at key
  rw [hderiv] at key
  have hne : (2 * Real.pi * Complex.I) ≠ 0 := by
    have : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
    exact mul_ne_zero this Complex.I_ne_zero
  rw [key, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem norm_sub_sub_fderiv_le {U : Set E} (hU : IsOpen U) {f : E → F} (hf : DifferentiableOn ℂ f U)
    {S : Set E} (hSU : S ⊆ U) (hS : Convex ℝ S) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ p ∈ S, ∀ q ∈ S, ‖fderiv ℂ f p - fderiv ℂ f q‖ ≤ Λ * ‖p - q‖)
    {w k : E} (hw : w ∈ S) (hwk : w + k ∈ S) :
    ‖f (w + k) - f w - fderiv ℂ f w k‖ ≤ Λ * ‖k‖ ^ 2 := by
  have hreal : ∀ τ : ℝ, w + τ • k ∈ U →
      HasDerivAt (fun s : ℝ => f (w + s • k)) (fderiv ℂ f (w + τ • k) k) τ := by
    intro τ hτ
    have hd : DifferentiableAt ℂ f (w + τ • k) := hf.differentiableAt (hU.mem_nhds hτ)
    have hl : HasDerivAt (fun s : ℝ => w + s • k) k τ := by
      simpa using ((hasDerivAt_id τ).smul_const k).const_add w
    have hf' : HasFDerivAt f ((fderiv ℂ f (w + τ • k)).restrictScalars ℝ) (w + τ • k) :=
      (hd.hasFDerivAt).restrictScalars ℝ
    have := hf'.comp_hasDerivAt τ hl
    exact this
  have seg : ∀ τ ∈ Icc (0 : ℝ) 1, w + τ • k ∈ S := by
    intro τ hτ
    have := hS.add_smul_sub_mem hw hwk hτ
    simpa using this
  let g : ℝ → F := fun τ => f (w + τ • k) - τ • fderiv ℂ f w k
  have hg : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt g
      (fderiv ℂ f (w + x • k) k - fderiv ℂ f w k) (Icc (0 : ℝ) 1) x := by
    intro x hx
    have hxU : w + x • k ∈ U := hSU (seg x hx)
    have h1 := hreal x hxU
    have h2 : HasDerivAt (fun τ : ℝ => τ • fderiv ℂ f w k) (fderiv ℂ f w k) x := by
      simpa using (hasDerivAt_id x).smul_const (fderiv ℂ f w k)
    exact ((h1.sub h2)).hasDerivWithinAt
  have hbound : ∀ x ∈ Ico (0 : ℝ) 1,
      ‖fderiv ℂ f (w + x • k) k - fderiv ℂ f w k‖ ≤ Λ * ‖k‖ ^ 2 := by
    intro x hx
    have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
    have hdiff := hΛ (w + x • k) (seg x hxI) w hw
    have hpt : ‖(w + x • k) - w‖ = x * ‖k‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hx.1]
    rw [hpt] at hdiff
    have hk0 : 0 ≤ ‖k‖ := norm_nonneg k
    calc ‖fderiv ℂ f (w + x • k) k - fderiv ℂ f w k‖
        = ‖(fderiv ℂ f (w + x • k) - fderiv ℂ f w) k‖ := by
          rw [ContinuousLinearMap.sub_apply]
      _ ≤ ‖fderiv ℂ f (w + x • k) - fderiv ℂ f w‖ * ‖k‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (Λ * (x * ‖k‖)) * ‖k‖ := mul_le_mul_of_nonneg_right hdiff hk0
      _ ≤ Λ * ‖k‖ ^ 2 := by
          have hx1 : x ≤ 1 := hx.2.le
          have hx0 : 0 ≤ x := hx.1
          have : x * ‖k‖ * ‖k‖ ≤ ‖k‖ ^ 2 := by nlinarith [norm_nonneg k]
          nlinarith [mul_nonneg hΛ0 (mul_nonneg hx0 hk0)]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := fun x =>
      fderiv ℂ f (w + x • k) k - fderiv ℂ f w k) (a := 0) (b := 1) (C := Λ * ‖k‖ ^ 2) hg hbound 1
    ⟨zero_le_one, le_rfl⟩
  have hg1 : g 1 - g 0 = f (w + k) - f w - fderiv ℂ f w k := by
    simp only [g, one_smul, zero_smul, add_zero]
    abel
  rw [← hg1]
  simpa using hmv

end QuantumNLS.HolomorphicStageB1

#print axioms QuantumNLS.HolomorphicStageB1.fderiv_apply_eq_circleIntegral
#print axioms QuantumNLS.HolomorphicStageB1.norm_sub_sub_fderiv_le
