import QuantumNLS.SymplecticBracket

/-!
# R-C4F43CA8 `thm:root-involution`, part (2C-b2a): scalar and constant rules for the Poisson brackets

Realized inputs (frozen): `SymplecticBracket.pbR`, `pbR_eq_omega`, `gradient`, `hamField`, `omega`, `pbC`.

Proved here (standard axioms only):
* `pbR_const_add_left`, `pbR_const_add_right`: adding a real constant does not change the real bracket.
* `pbR_const_mul_left`, `pbR_const_mul_right`: real scalar multiplication (differentiable case).
* `pbC_const_add_left`, `pbC_const_add_right`: the complex bracket ignores complex constants.
* `pbC_real_scalar`: `pbC (α f) (β g) u = (αβ) pbC f g u` for real `α, β`, given differentiability of the real and
  imaginary parts at `u`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RootBracketScalars

open QuantumNLS.SymplecticBracket

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pbR_const_add_left (r : ℝ) (g K : H → ℝ) (u : H) :
    pbR (fun v => r + g v) K u = pbR g K u := by
  unfold pbR hamField
  rw [fderiv_const_add]

theorem pbR_const_add_right (r : ℝ) (f g : H → ℝ) (u : H) :
    pbR f (fun v => r + g v) u = pbR f g u := by
  unfold pbR hamField SymplecticBracket.gradient
  rw [fderiv_const_add]

theorem pbR_const_mul_left (α : ℝ) (f K : H → ℝ) (u : H) (hf : DifferentiableAt ℝ f u) :
    pbR (fun v => α * f v) K u = α * pbR f K u := by
  unfold pbR
  rw [fderiv_const_mul hf α]
  simp [smul_eq_mul]

theorem gradient_const_mul (β : ℝ) (g : H → ℝ) (u : H) (hg : DifferentiableAt ℝ g u) :
    SymplecticBracket.gradient (fun v => β * g v) u = β • SymplecticBracket.gradient g u := by
  unfold SymplecticBracket.gradient
  rw [fderiv_const_mul hg β, map_smul, smul_comm]

theorem pbR_const_mul_right (β : ℝ) (f g : H → ℝ) (u : H) (hg : DifferentiableAt ℝ g u) :
    pbR f (fun v => β * g v) u = β * pbR f g u := by
  rw [pbR_eq_omega, pbR_eq_omega, gradient_const_mul β g u hg]
  unfold SymplecticBracket.omega
  have hs : β • SymplecticBracket.gradient g u = ((β : ℝ) : ℂ) • SymplecticBracket.gradient g u :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) β _
  rw [hs, inner_smul_right]
  simp [Complex.mul_im]
  ring

theorem pbC_const_add_left (c : ℂ) (G K : H → ℂ) (u : H) :
    pbC (fun v => c + G v) K u = pbC G K u := by
  unfold pbC
  simp only [Complex.add_re, Complex.add_im, pbR_const_add_left]

theorem pbC_const_add_right (c : ℂ) (F K : H → ℂ) (u : H) :
    pbC F (fun v => c + K v) u = pbC F K u := by
  unfold pbC
  simp only [Complex.add_re, Complex.add_im, pbR_const_add_right]

theorem pbC_real_scalar (α β : ℝ) (f g : H → ℂ) (u : H)
    (hf1 : DifferentiableAt ℝ (fun v => (f v).re) u) (hf2 : DifferentiableAt ℝ (fun v => (f v).im) u)
    (hg1 : DifferentiableAt ℝ (fun v => (g v).re) u) (hg2 : DifferentiableAt ℝ (fun v => (g v).im) u) :
    pbC (fun v => ((α : ℝ) : ℂ) * f v) (fun v => ((β : ℝ) : ℂ) * g v) u =
      ((α * β : ℝ) : ℂ) * pbC f g u := by
  have a1 : pbR (fun v => α * (f v).re) (fun v => β * (g v).re) u =
      α * β * pbR (fun v => (f v).re) (fun v => (g v).re) u := by
    rw [pbR_const_mul_left α (fun v => (f v).re) _ u hf1, pbR_const_mul_right β _ _ u hg1]
    ring
  have a2 : pbR (fun v => α * (f v).im) (fun v => β * (g v).im) u =
      α * β * pbR (fun v => (f v).im) (fun v => (g v).im) u := by
    rw [pbR_const_mul_left α (fun v => (f v).im) _ u hf2, pbR_const_mul_right β _ _ u hg2]
    ring
  have a3 : pbR (fun v => α * (f v).im) (fun v => β * (g v).re) u =
      α * β * pbR (fun v => (f v).im) (fun v => (g v).re) u := by
    rw [pbR_const_mul_left α (fun v => (f v).im) _ u hf2, pbR_const_mul_right β _ _ u hg1]
    ring
  have a4 : pbR (fun v => α * (f v).re) (fun v => β * (g v).im) u =
      α * β * pbR (fun v => (f v).re) (fun v => (g v).im) u := by
    rw [pbR_const_mul_left α (fun v => (f v).re) _ u hf1, pbR_const_mul_right β _ _ u hg2]
    ring
  unfold pbC
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]
  apply Complex.ext
  · dsimp only
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [a1, a2]
    ring
  · dsimp only
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [a3, a4]
    ring

end QuantumNLS.RootBracketScalars

#print axioms QuantumNLS.RootBracketScalars.pbC_real_scalar
#print axioms QuantumNLS.RootBracketScalars.pbC_const_add_left
