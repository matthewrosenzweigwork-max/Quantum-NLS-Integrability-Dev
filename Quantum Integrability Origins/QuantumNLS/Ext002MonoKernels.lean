import Mathlib
import QuantumNLS.Ext002OddKernels

/-!
# EXT-002 / V-01 full monodromy (owner decision D4), stage 1: source-pinned diagonal kernels

Owner decision D4 (`implementation/ops/contracts/OWNER_DECISIONS_DEF043_DEF035_EXT005_EXT002_2026-11-16.md`,
sha256 37414179…): source-pinned full monodromy `T = [[A, cB], [C, D]]`, interval translation and gauge
bound to the report/Vlaar conventions.

Conventions pinned here (scalar kernels of the diagonal entries):
* Vlaar thesis (2.4.1) (printed p. 20): `A_λ = e^{−iλL/2} Σₙ γⁿ ∫_{J^{2n}_+} e^{−iλ Σⱼ (−1)ʲ yⱼ}
  Πⱼ odd Φ*(yⱼ) Πⱼ even Φ(yⱼ)`, `J = [−L/2, L/2]`, `J^{k}_+ = {y₁ > ⋯ > y_k}`; with creation variables
  `xₐ = y_{2a−1}` and annihilation variables `yₐ = y_{2a}` the phase is `e^{−iλL/2} e^{iλ Σ(xₐ − yₐ)}`
  on `x₁ > y₁ > ⋯ > x_r > y_r` (report `A04.tex:16-36`, `source/chapters/foundations/A04.tex:19-25`).
* Vlaar (2.4.4) (printed p. 21): `D_λ = e^{iλL/2} Σₙ γⁿ ∫ e^{iλ Σⱼ (−1)ʲ yⱼ} Πⱼ even Φ* Πⱼ odd Φ`; odd
  variables are annihilation `yₐ`, even are creation `xₐ`, phase `e^{iλL/2} e^{−iλ Σ(yₐ − xₐ)}` on
  `y₁ > x₁ > ⋯ > y_r > x_r` (A04.tex:26-31).
* Translation by `L/2` to `(0,L)` (A04.tex:32-35, periodic_basis.tex:356-358) and multiplication of
  the transfer by `e^{iLz/2}` (periodic_basis.tex:358): `sourceA_gauge`, `sourceD_gauge` identify the
  gauged translated kernels with the accepted DEF-048 kernels `rawPlus`/`rawMinus`
  (periodic_basis.tex:314-321, `BetheTransferKernelAdjoint`); `zero_field_gauge` is the zero-field
  term `1 + e^{izL}` (A04.tex:35-36).
The off-diagonal scalar kernels (Vlaar (2.4.2)-(2.4.3)) are `Ext002OddKernels` (read-only).
No operator, field, or identification is postulated here.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.Ext002MonoKernels
open BetheTransferKernelAdjoint

/-- Vlaar (2.4.1), centered interval, `r` creation variables `x` (odd positions) and `r`
annihilation variables `y` (even positions). The chamber is tested after translating back to `(0,L)`. -/
def sourceA {r : ℕ} (L : ℝ) (z : ℂ) (x y : Fin r → ℝ) : ℂ := by
  classical
  exact if PlusOrder L (fun i => x i + L/2) (fun i => y i + L/2) then
    Complex.exp (-(Complex.I * z * L / 2)) *
      Complex.exp (-(Complex.I * z * ((∑ i, y i - ∑ i, x i : ℝ) : ℂ))) else 0

/-- Vlaar (2.4.4), centered interval; odd positions are the annihilation variables `y`. -/
def sourceD {r : ℕ} (L : ℝ) (z : ℂ) (x y : Fin r → ℝ) : ℂ := by
  classical
  exact if MinusOrder L (fun i => x i + L/2) (fun i => y i + L/2) then
    Complex.exp (Complex.I * z * L / 2) *
      Complex.exp (Complex.I * z * ((∑ i, x i - ∑ i, y i : ℝ) : ℂ)) else 0

lemma sum_shift {r : ℕ} (L : ℝ) (x y : Fin r → ℝ) :
    (∑ i, (x i - L/2)) - ∑ i, (y i - L/2) = ∑ i, x i - ∑ i, y i := by
  simp only [Finset.sum_sub_distrib]
  ring

/-- **A entry**: translation by `L/2` and the gauge `e^{iLz/2}` give the DEF-048 upper kernel. -/
theorem sourceA_gauge {r : ℕ} (L : ℝ) (z : ℂ) (x y : Fin r → ℝ) :
    Complex.exp (Complex.I * z * L / 2) *
      sourceA L z (fun i => x i - L/2) (fun i => y i - L/2) = rawPlus L z x y := by
  classical
  unfold sourceA rawPlus
  simp only [sub_add_cancel]
  split_ifs with h
  · rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [displacement, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · simp

/-- **D entry**: translation by `L/2` and the gauge `e^{iLz/2}` give the DEF-048 lower kernel. -/
theorem sourceD_gauge {r : ℕ} (L : ℝ) (z : ℂ) (x y : Fin r → ℝ) :
    Complex.exp (Complex.I * z * L / 2) *
      sourceD L z (fun i => x i - L/2) (fun i => y i - L/2) = rawMinus L z x y := by
  classical
  unfold sourceD rawMinus
  simp only [sub_add_cancel]
  split_ifs with h
  · rw [← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  · simp

/-- The zero-field terms `e^{−iλL/2} + e^{iλL/2}` of `A + D`, gauged, give `1 + e^{izL}`. -/
theorem zero_field_gauge (L : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * z * L / 2) *
      (Complex.exp (-(Complex.I * z * L / 2)) + Complex.exp (Complex.I * z * L / 2)) =
        1 + Complex.exp (Complex.I * L * z) := by
  rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
  rw [show Complex.I * z * L / 2 + -(Complex.I * z * L / 2) = 0 by ring, Complex.exp_zero]
  congr 1
  congr 1
  ring

end QuantumNLS.Ext002MonoKernels

#print axioms QuantumNLS.Ext002MonoKernels.sourceA_gauge
#print axioms QuantumNLS.Ext002MonoKernels.sourceD_gauge
#print axioms QuantumNLS.Ext002MonoKernels.zero_field_gauge
