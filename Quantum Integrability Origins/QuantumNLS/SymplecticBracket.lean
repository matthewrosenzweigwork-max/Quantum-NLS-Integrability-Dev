import Mathlib
import QuantumNLS.PhysicalTensor

/-!
# DEF-015: physical symplectic form and Poisson bracket

Owner: haiku_inventory (round 19, reassigned). Source `definitions.tex` lines 93–95 (DEF-015), with DEF-001
(line 9): the physical Hilbert space `L²(𝕋_L;ℂ)`, inner product linear in the second variable.

Realization (no supplied bracket, no flow, no conservation):

* the real Hilbert space underlying a complex Hilbert space `H` has `⟨h,k⟩_ℝ = Re⟨h,k⟩_ℂ`
  (`real_inner_eq_re_inner`); `Ω(h,k) = 2 Im⟨h,k⟩_ℂ` (`omega`);
* the gradient `∇F(u)` of a real functional is the Riesz representative of the Fréchet derivative,
  `∇F(u) = ½ · toDual⁻¹(dF(u))`, so that `dF(u)[h] = 2 Re⟨∇F(u),h⟩` (`fderiv_eq_two_inner_gradient`);
* `X_F = −i∇F` (`hamField`); the real bracket is `{F,G} = dF[X_G]` (`pbR`);
* complex brackets extend complex bilinearly (`pbC`): `{F,G} = {F₁,G₁} − {F₂,G₂} + i({F₂,G₁} + {F₁,G₂})`.

Proved clauses: `Ω` alternating and nondegenerate (`omega_swap`, `omega_self`, `omega_mul_I`); `{F,G} = Ω(∇F,∇G)`
for every real `F,G`, unconditionally (`pbR_eq_omega`), hence skew (`pbR_swap`) and bilinear
(`pbR_neg_left`, `pbR_neg_right`); the normalization `{z, z̄} = −i` for the coordinate `z = ⟨e,·⟩` of a unit
vector `e` (`pbC_coord_conj`, the DEF-015 normalization), and its instance on the physical space `L2T L`
(`pbC_coord_conj_phys`).
-/

namespace QuantumNLS.SymplecticBracket

open InnerProductSpace ComplexConjugate
open QuantumNLS.PhysicalTensor

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- the realification `⟨h,k⟩_ℝ = Re⟨h,k⟩_ℂ` is a def in Mathlib (not an instance); activated locally
attribute [local instance] InnerProductSpace.complexToReal

/-- DEF-015: `Ω(h,k) = 2 Im⟨h,k⟩` on the real space underlying `H` (`⟨·,·⟩` linear in the second slot). -/
noncomputable def omega (h k : H) : ℝ := 2 * (inner ℂ h k).im

/-- Gradient of a real functional (DEF-015): `∇F(u) = ½ · toDual⁻¹(dF(u))`. -/
noncomputable def gradient (F : H → ℝ) (u : H) : H :=
  (2 : ℝ)⁻¹ • (toDual ℝ H).symm (fderiv ℝ F u)

/-- DEF-015: `dF(u)[h] = 2 Re⟨∇F(u), h⟩` (the real inner product of the realification). -/
lemma fderiv_eq_two_inner_gradient (F : H → ℝ) (u h : H) :
    fderiv ℝ F u h = 2 * inner ℝ (gradient F u) h := by
  unfold gradient
  rw [real_inner_smul_left, toDual_symm_apply]
  ring

/-- DEF-015: Hamiltonian vector field `X_F = −i∇F`. -/
noncomputable def hamField (F : H → ℝ) (u : H) : H := (-Complex.I) • gradient F u

/-- DEF-015 real bracket: `{F,G}(u) = dF(u)[X_G(u)]`. -/
noncomputable def pbR (F G : H → ℝ) (u : H) : ℝ := fderiv ℝ F u (hamField G u)

/-- DEF-015 complex bracket: complex bilinear extension of the real bracket. For `F = F₁ + iF₂`,
`G = G₁ + iG₂`: `{F,G} = {F₁,G₁} − {F₂,G₂} + i({F₂,G₁} + {F₁,G₂})`. -/
noncomputable def pbC (F G : H → ℂ) (u : H) : ℂ :=
  ⟨pbR (fun v => (F v).re) (fun v => (G v).re) u - pbR (fun v => (F v).im) (fun v => (G v).im) u,
    pbR (fun v => (F v).im) (fun v => (G v).re) u + pbR (fun v => (F v).re) (fun v => (G v).im) u⟩

lemma re_neg_I_mul (z : ℂ) : ((-Complex.I) * z).re = z.im := by
  simp

lemma omega_swap (h k : H) : omega h k = - omega k h := by
  unfold omega
  have h1 : (starRingEnd ℂ) (inner ℂ h k) = inner ℂ k h := inner_conj_symm k h
  rw [← h1, Complex.conj_im]
  ring

/-- `⟨h,h⟩ = ‖h‖²` (real). -/
lemma inner_self_eq_ofReal (h : H) : inner ℂ h h = ((‖h‖ ^ 2 : ℝ) : ℂ) := by
  simp [inner_self_eq_norm_sq_to_K]

lemma omega_self (h : H) : omega h h = 0 := by
  unfold omega
  rw [inner_self_eq_ofReal, Complex.ofReal_im]
  ring

/-- Nondegeneracy witness: `Ω(h, I·h) = 2‖h‖²`. -/
lemma omega_mul_I (h : H) : omega h (Complex.I • h) = 2 * ‖h‖ ^ 2 := by
  unfold omega
  rw [inner_smul_right, inner_self_eq_ofReal]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Bracket of gradients.** `{F,G} = Ω(∇F,∇G)` for all real `F,G`; no differentiability is needed
(a missing derivative makes both sides vanish). -/
lemma pbR_eq_omega (F G : H → ℝ) (u : H) :
    pbR F G u = omega (gradient F u) (gradient G u) := by
  unfold pbR hamField omega
  rw [fderiv_eq_two_inner_gradient, real_inner_eq_re_inner ℂ, RCLike.re_to_complex, inner_smul_right,
    re_neg_I_mul]

/-- The real bracket is skew-symmetric. -/
lemma pbR_swap (F G : H → ℝ) (u : H) : pbR F G u = - pbR G F u := by
  rw [pbR_eq_omega, pbR_eq_omega, omega_swap]

lemma pbR_self (F : H → ℝ) (u : H) : pbR F F u = 0 := by
  rw [pbR_eq_omega, omega_self]

lemma gradient_neg (G : H → ℝ) (u : H) :
    gradient (fun v => -(G v)) u = -(gradient G u) := by
  unfold gradient
  rw [show (fun v => -(G v)) = -G from rfl, fderiv_neg, map_neg, smul_neg]

lemma pbR_neg_right (F G : H → ℝ) (u : H) :
    pbR F (fun v => -(G v)) u = - pbR F G u := by
  unfold pbR hamField
  rw [gradient_neg, smul_neg, map_neg]

lemma pbR_neg_left (F G : H → ℝ) (u : H) :
    pbR (fun v => -(F v)) G u = - pbR F G u := by
  unfold pbR
  rw [show (fun v => -(F v)) = -F from rfl, fderiv_neg, neg_apply]

/-- Gradient of the real part of `⟨w,·⟩`: `∇⟨w,·⟩_ℝ = w/2`. -/
lemma gradient_innerR (w : H) (u : H) :
    gradient (fun v => inner ℝ w v) u = (2 : ℝ)⁻¹ • w := by
  have hd : fderiv ℝ (fun v => inner ℝ w v) u = innerSL ℝ w := by
    have : (fun v => inner ℝ w v) = ⇑(innerSL ℝ w) := by
      ext v
      rfl
    rw [this, ContinuousLinearMap.fderiv]
  have h2 : (toDual ℝ H).symm (innerSL ℝ w) = w := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    ext v
    rfl
  unfold gradient
  rw [hd, h2]

/-- Real part of the coordinate `⟨e,·⟩`. -/
lemma re_inner_coord (e v : H) : (inner ℂ e v).re = inner ℝ e v :=
  (real_inner_eq_re_inner ℂ e v).symm

/-- Imaginary part of the coordinate `⟨e,·⟩`, as `Re⟨ie, ·⟩`. -/
lemma im_inner_coord (e v : H) : (inner ℂ e v).im = inner ℝ (Complex.I • e) v := by
  rw [real_inner_eq_re_inner ℂ, inner_smul_left]
  simp

/-- **Normalization of the real pair.** For a unit vector `e`, `{Re⟨e,·⟩, Im⟨e,·⟩} = 1/2`. -/
lemma pbR_coord_re_im {e : H} (he : ‖e‖ = 1) (u : H) :
    pbR (fun v => inner ℝ e v) (fun v => inner ℝ (Complex.I • e) v) u = 1 / 2 := by
  rw [pbR_eq_omega, gradient_innerR, gradient_innerR]
  unfold omega
  simp [RCLike.real_smul_eq_coe_smul, inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K, he]

/-- **DEF-015 normalization `{z, z̄} = −i`.** For the coordinate `z(v) = ⟨e,v⟩` of a unit vector `e`,
`{z, z̄} = −i` (constant in `u`). -/
theorem pbC_coord_conj {e : H} (he : ‖e‖ = 1) (u : H) :
    pbC (fun v => inner ℂ e v) (fun v => (starRingEnd ℂ) (inner ℂ e v)) u = -Complex.I := by
  have hx : (fun v => (inner ℂ e v).re) = fun v => inner ℝ e v := by
    ext v
    exact re_inner_coord e v
  have hy : (fun v => (inner ℂ e v).im) = fun v => inner ℝ (Complex.I • e) v := by
    ext v
    exact im_inner_coord e v
  have hxc : (fun v => ((starRingEnd ℂ) (inner ℂ e v)).re) = fun v => inner ℝ e v := by
    ext v
    rw [Complex.conj_re]
    exact re_inner_coord e v
  have hyc : (fun v => ((starRingEnd ℂ) (inner ℂ e v)).im) = fun v => -(inner ℝ (Complex.I • e) v) := by
    ext v
    rw [Complex.conj_im, im_inner_coord e v]
  unfold pbC
  rw [hx, hy, hxc, hyc]
  have h1 := pbR_coord_re_im he u
  have hxx := pbR_self (fun v => inner ℝ e v) u
  have hyy := pbR_self (fun v => inner ℝ (Complex.I • e) v) u
  have hyx := pbR_swap (fun v => inner ℝ e v) (fun v => inner ℝ (Complex.I • e) v) u
  rw [pbR_neg_right, pbR_neg_right, hyy, hxx, h1]
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.I_re, sub_neg_eq_add, sub_zero, zero_add]
    norm_num
  · simp only [Complex.neg_im, Complex.I_im]
    linarith [hyx, h1]

end General

section Physical

variable (L : ℝ) [Fact (0 < L)]

/-- **DEF-015 on the physical space `L²(𝕋_L;ℂ)`** (`L2T L`, DEF-001). -/
theorem pbC_coord_conj_phys {e : L2T L} (he : ‖e‖ = 1) (u : L2T L) :
    pbC (fun v : L2T L => inner ℂ e v) (fun v => (starRingEnd ℂ) (inner ℂ e v)) u
      = -Complex.I :=
  pbC_coord_conj he u

end Physical

end QuantumNLS.SymplecticBracket
