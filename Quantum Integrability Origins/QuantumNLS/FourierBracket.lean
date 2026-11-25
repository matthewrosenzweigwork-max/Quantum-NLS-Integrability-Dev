import Mathlib
import QuantumNLS.SymplecticBracket
import QuantumNLS.Fourier

/-!
# DEF-015 at the mass-`L` Fourier modes: cross-mode bracket and the physical coordinate convention

Owner: haiku_inventory (round 19c). Source `definitions.tex` lines 9–12 (DEF-001: `e_n = L^{−1/2}e^{2πinx/L}`,
`û(n) = ⟨e_n,u⟩`, inner product linear in the second variable) and lines 93–95 (DEF-015).

Built on the frozen `SymplecticBracket 056a23e2` (DEF-015 realization) and the codebase's Fourier layer
(`QuantumNLS.Fourier`: `modeLp`, `fourierL2`, `coeff`, `inner_mode_mode` via `fourierL2_modeLp`).

Proved:

* `coeff_eq_inner_mode`: the codebase coefficient `coeff L u n` equals `⟨e_n, u⟩` (physical convention, DEF-001);
* `inner_mode_mode`: orthonormality `⟨e_m, e_n⟩ = δ_{mn}` (from the unitary `fourierL2`);
* `norm_modeLp`: `‖e_n‖ = 1` (mass-`L` normalization);
* `pbC_coord_conj_coord`: for any `e,f`, `{⟨e,·⟩, conj⟨f,·⟩} = −i⟨e,f⟩`, and `pbC_coord_coord`: `{⟨e,·⟩,⟨f,·⟩} = 0`;
* `fourier_bracket_delta`: `{û(m), conj û(n)} = −i δ_{mn}` and `{û(m), û(n)} = 0` on `L²(𝕋_L)`;
* gradient conventions: `gradient_eq_of_hasFDerivAt` (genuine derivative), `gradient_eq_zero_of_not_differentiable`
  (totalized convention), and `coord_hasFDerivAt` (the coordinates are differentiable, so their gradients are genuine).

No flow, conservation, or new differentiability assumption is introduced.
-/

namespace QuantumNLS.FourierBracket

open InnerProductSpace ComplexConjugate
open QuantumNLS.SymplecticBracket QuantumNLS.Fourier QuantumNLS.PhysicalTensor

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] InnerProductSpace.complexToReal

/-- Totalized convention: a non-differentiable functional has zero (totalized) Fréchet derivative,
hence zero gradient. This is a convention, not a derivative. -/
lemma gradient_eq_zero_of_not_differentiable {F : H → ℝ} {u : H}
    (hF : ¬ DifferentiableAt ℝ F u) : SymplecticBracket.gradient F u = 0 := by
  unfold SymplecticBracket.gradient
  rw [fderiv_zero_of_not_differentiableAt hF]
  simp

/-- Genuine derivative: if `F` has Fréchet derivative `φ` at `u`, then `φ h = 2 Re⟨∇F(u), h⟩`. -/
lemma gradient_eq_of_hasFDerivAt {F : H → ℝ} {u : H} {φ : H →L[ℝ] ℝ} (hF : HasFDerivAt F φ u) (h : H) :
    φ h = 2 * inner ℝ (SymplecticBracket.gradient F u) h := by
  have := fderiv_eq_two_inner_gradient F u h
  rw [hF.fderiv] at this
  exact this

/-- The real-linear coordinate `v ↦ Re⟨e,v⟩` is Fréchet differentiable with derivative `⟨e,·⟩_ℝ`. -/
lemma coord_hasFDerivAt (e u : H) :
    HasFDerivAt (fun v => inner ℝ e v) (innerSL ℝ e : H →L[ℝ] ℝ) u := by
  have : (fun v => inner ℝ e v) = ⇑(innerSL ℝ e : H →L[ℝ] ℝ) := funext fun v => rfl
  rw [this]
  exact (innerSL ℝ e : H →L[ℝ] ℝ).hasFDerivAt

lemma omega_half_smul (a b : H) : omega ((2 : ℝ)⁻¹ • a) ((2 : ℝ)⁻¹ • b) = (1 / 4) * omega a b := by
  unfold omega
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right] <;> ring

lemma re_inner_swap (e f : H) : (inner ℂ f e).re = (inner ℂ e f).re := by
  rw [← inner_conj_symm e f, Complex.conj_re]

/-- `{Re⟨e,·⟩, Re⟨f,·⟩} = ½ Im⟨e,f⟩`. -/
lemma pbR_xx (e f u : H) :
    pbR (fun v => inner ℝ e v) (fun v => inner ℝ f v) u = (inner ℂ e f).im / 2 := by
  rw [pbR_eq_omega, gradient_innerR, gradient_innerR, omega_half_smul]
  unfold omega
  ring

/-- `{Re⟨e,·⟩, Im⟨f,·⟩} = ½ Re⟨e,f⟩`, with `Im⟨f,·⟩ = Re⟨i f,·⟩`. -/
lemma pbR_xy (e f u : H) :
    pbR (fun v => inner ℝ e v) (fun v => inner ℝ (Complex.I • f) v) u = (inner ℂ e f).re / 2 := by
  rw [pbR_eq_omega, gradient_innerR, gradient_innerR, omega_half_smul]
  unfold omega
  rw [inner_smul_right]
  simp [Complex.mul_im] <;> ring

/-- `{Im⟨e,·⟩, Im⟨f,·⟩} = ½ Im⟨e,f⟩`. -/
lemma pbR_yy (e f u : H) :
    pbR (fun v => inner ℝ (Complex.I • e) v) (fun v => inner ℝ (Complex.I • f) v) u
      = (inner ℂ e f).im / 2 := by
  rw [pbR_eq_omega, gradient_innerR, gradient_innerR, omega_half_smul]
  unfold omega
  rw [inner_smul_left, inner_smul_right]
  simp
  ring

/-- `{Im⟨e,·⟩, Re⟨f,·⟩} = −½ Re⟨e,f⟩` (skew symmetry with `pbR_xy`). -/
lemma pbR_yx (e f u : H) :
    pbR (fun v => inner ℝ (Complex.I • e) v) (fun v => inner ℝ f v) u = -((inner ℂ e f).re / 2) := by
  rw [pbR_swap, pbR_xy, re_inner_swap]

/-- **General cross-coordinate bracket.** For the coordinates `z_e = ⟨e,·⟩` and `z_f = ⟨f,·⟩`:
`{z_e, z̄_f} = −i ⟨e,f⟩`. -/
theorem pbC_coord_conj_coord (e f u : H) :
    pbC (fun v => inner ℂ e v) (fun v => (starRingEnd ℂ) (inner ℂ f v)) u
      = -Complex.I * inner ℂ e f := by
  have hx : (fun v => (inner ℂ e v).re) = fun v => inner ℝ e v :=
    funext fun v => re_inner_coord e v
  have hy : (fun v => (inner ℂ e v).im) = fun v => inner ℝ (Complex.I • e) v :=
    funext fun v => im_inner_coord e v
  have hxf : (fun v => ((starRingEnd ℂ) (inner ℂ f v)).re) = fun v => inner ℝ f v :=
    funext fun v => by rw [Complex.conj_re]; exact re_inner_coord f v
  have hyf : (fun v => ((starRingEnd ℂ) (inner ℂ f v)).im) = fun v => -(inner ℝ (Complex.I • f) v) :=
    funext fun v => by rw [Complex.conj_im, im_inner_coord f v]
  unfold pbC
  rw [hx, hy, hxf, hyf, pbR_neg_right, pbR_neg_right, pbR_xx, pbR_yy, pbR_yx, pbR_xy]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im] <;> ring
  · simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- **Same-sign coordinates commute:** `{z_e, z_f} = 0`. -/
theorem pbC_coord_coord (e f u : H) :
    pbC (fun v => inner ℂ e v) (fun v => inner ℂ f v) u = 0 := by
  have hx : (fun v => (inner ℂ e v).re) = fun v => inner ℝ e v :=
    funext fun v => re_inner_coord e v
  have hy : (fun v => (inner ℂ e v).im) = fun v => inner ℝ (Complex.I • e) v :=
    funext fun v => im_inner_coord e v
  have hxf : (fun v => (inner ℂ f v).re) = fun v => inner ℝ f v :=
    funext fun v => re_inner_coord f v
  have hyf : (fun v => (inner ℂ f v).im) = fun v => inner ℝ (Complex.I • f) v :=
    funext fun v => im_inner_coord f v
  unfold pbC
  rw [hx, hy, hxf, hyf, pbR_xx, pbR_yy, pbR_yx, pbR_xy]
  apply Complex.ext
  · simp <;> ring
  · simp <;> ring

end General

section Fourier

attribute [local instance] InnerProductSpace.complexToReal

variable (L : ℝ) [Fact (0 < L)]

/-- **Physical coordinate convention (DEF-001).** The codebase coefficient equals the inner product
with the mass-`L` Fourier mode: `û(n) = ⟨e_n, u⟩`. -/
theorem coeff_eq_inner_mode (u : L2T L) (n : ℤ) :
    coeff L (u : AddCircle L → ℂ) n = inner ℂ (modeLp L n) u := by
  have h1 : inner ℂ (modeLp L n) u = inner ℂ (fourierL2 L (modeLp L n)) (fourierL2 L u) :=
    ((fourierL2 L).inner_map_map _ _).symm
  rw [h1, fourierL2_modeLp, lp.inner_single_left, fourierL2_apply]
  simp

/-- **Orthonormality** of the mass-`L` Fourier modes: `⟨e_m, e_n⟩ = δ_{mn}`. -/
theorem inner_mode_mode (m n : ℤ) :
    inner ℂ (modeLp L m) (modeLp L n) = if m = n then 1 else 0 := by
  rw [← coeff_eq_inner_mode, coeff_congr_ae L (coeFn_modeLp L n), coeff_mode]

/-- **Unit norm** of the mass-`L` Fourier modes. -/
theorem norm_modeLp (n : ℤ) : ‖modeLp L n‖ = 1 := by
  have h := inner_mode_mode L n n
  rw [if_pos rfl] at h
  have h' : RCLike.re (inner ℂ (modeLp L n) (modeLp L n)) = ‖modeLp L n‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [h] at h'
  have h3 : ‖modeLp L n‖ ^ 2 = 1 := by simpa using h'.symm
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3

/-- **DEF-015 at the Fourier modes.** `{û(m), conj û(n)} = −i δ_{mn}` on `L²(𝕋_L)`. -/
theorem fourier_bracket_delta (m n : ℤ) (u : L2T L) :
    pbC (fun v : L2T L => inner ℂ (modeLp L m) v)
        (fun v => (starRingEnd ℂ) (inner ℂ (modeLp L n) v)) u
      = if m = n then -Complex.I else 0 := by
  rw [pbC_coord_conj_coord, inner_mode_mode]
  split_ifs <;> simp

/-- **Unit-mode normalization** `{û(n), conj û(n)} = −i` (DEF-015 normalization at `e_n`). -/
theorem fourier_bracket_norm (n : ℤ) (u : L2T L) :
    pbC (fun v : L2T L => inner ℂ (modeLp L n) v)
        (fun v => (starRingEnd ℂ) (inner ℂ (modeLp L n) v)) u = -Complex.I := by
  rw [fourier_bracket_delta]
  simp

/-- `{û(m), û(n)} = 0` on `L²(𝕋_L)`. -/
theorem fourier_bracket_same (m n : ℤ) (u : L2T L) :
    pbC (fun v : L2T L => inner ℂ (modeLp L m) v) (fun v => inner ℂ (modeLp L n) v) u = 0 :=
  pbC_coord_coord _ _ _

/-- **Physical-coordinate form.** On `L²(𝕋_L)` the coordinate `v ↦ ⟨e_n, v⟩` is the codebase Fourier
coefficient, so `{û(m), conj û(n)} = −i δ_{mn}` with `û(n) = coeff L · n`. -/
theorem fourier_bracket_coeff (m n : ℤ) (u : L2T L) :
    pbC (fun v : L2T L => coeff L (v : AddCircle L → ℂ) m)
        (fun v => (starRingEnd ℂ) (coeff L (v : AddCircle L → ℂ) n)) u
      = if m = n then -Complex.I else 0 := by
  have hm : (fun v : L2T L => coeff L (v : AddCircle L → ℂ) m) = fun v => inner ℂ (modeLp L m) v :=
    funext fun v => coeff_eq_inner_mode L v m
  have hn : (fun v : L2T L => (starRingEnd ℂ) (coeff L (v : AddCircle L → ℂ) n))
      = fun v => (starRingEnd ℂ) (inner ℂ (modeLp L n) v) :=
    funext fun v => by rw [coeff_eq_inner_mode L v n]
  rw [hm, hn, fourier_bracket_delta]

/-! The genuine-derivative statement for the coordinates `⟨e_n,·⟩` is the general lemma
`coord_hasFDerivAt` combined with `gradient_eq_of_hasFDerivAt` (section `General`), applied to `H = L2T L`;
it is not restated here, to avoid a second elaboration of the real inner product on `Lp`. -/

end Fourier

end QuantumNLS.FourierBracket
