import Mathlib
import NlsGge.ThirdConsultation.G2.Reparam032D
import NlsGge.ThirdConsultation.G2.Reparam032F

/- G2-032 HOMOTOPY032 part 3 = Reparam032G (proof development, AUTHOR; SUPPORTING lemmas, not a packet; not self-reviewed).
   Radial homotopy between the isolating circle and the Joukowski-type ellipse, in the common ray angle
   β(t) := ellArg p q t of the ellipse. With w := τ − C, r(α) := rayR w R α (exit radius of the disc),
     H(s,t) := τ + ((1−s) r(β t) + s ‖E(t)‖) e^{iβ t},   E(t) := ellF p q t, p = (γ/4)ρ, q = (γ/4)ρ⁻¹.
   Proved (for 1 < ρ, γ ≠ 0, the endpoints τ ± γ/2 and the ellipse strictly inside the open disc):
   (i) H(1,t) = τ + E(t); (ii) H(0,t) = C + R e^{iθ(t)} when the circle angle θ is supplied with
   C + R e^{iθ t} = τ + r(β t) e^{iβ t}; (iii) 2π-periodicity in t; (iv) normSq(H(s,t) − C) ≤ R²
   for s ∈ [0,1]; (v) H(s,t) ∉ segment ℝ (τ − γ/2) (τ + γ/2) (the gap cut) for s ∈ [0,1].
   Smoothness (C²) and the ρ choice are separate modules. -/
set_option autoImplicit false
open scoped Real

namespace NlsGge.GKDefinitionDesign
namespace G2032Homo
noncomputable section

/-- Scaled ellipse coefficients `p = (γ/4)ρ`, `q = (γ/4)ρ⁻¹`. -/
def pOf (γ : ℂ) (ρ : ℝ) : ℂ := γ / 4 * (ρ : ℂ)

def qOf (γ : ℂ) (ρ : ℝ) : ℂ := γ / 4 * ((ρ⁻¹ : ℝ) : ℂ)

/-- The radial homotopy in the common ellipse ray angle. -/
def homH (τ C γ : ℂ) (R ρ s t : ℝ) : ℂ :=
  τ + (((1 - s) * NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
      (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t) +
      s * ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t‖ : ℝ) : ℂ) *
    Complex.exp ((NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t : ℂ) *
      Complex.I)

theorem pOf_ne_zero (γ : ℂ) (ρ : ℝ) (hγ : γ ≠ 0) (hρ : 0 < ρ) : pOf γ ρ ≠ 0 :=
  mul_ne_zero (div_ne_zero hγ (by norm_num)) (Complex.ofReal_ne_zero.mpr hρ.ne')

theorem pq_norm_lt (γ : ℂ) (ρ : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ) :
    ‖qOf γ ρ‖ < ‖pOf γ ρ‖ := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hg : 0 < ‖γ / 4‖ := norm_pos_iff.mpr (div_ne_zero hγ (by norm_num))
  have hinv : ρ⁻¹ < ρ := by
    have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    have h2 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
    nlinarith
  unfold qOf pOf
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hρ0.le, Real.norm_of_nonneg (inv_nonneg.mpr hρ0.le)]
  exact mul_lt_mul_of_pos_left hinv hg

theorem ellF_pq (γ : ℂ) (ρ t : ℝ) :
    NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t =
      γ / 4 * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
        ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) := by
  unfold NlsGge.GKDefinitionDesign.G2032Ellipse.ellF pOf qOf
  rw [show ((-t : ℝ) : ℂ) * Complex.I = -((t : ℂ) * Complex.I) by push_cast; ring]
  ring

theorem im_combo (ρ t : ℝ) :
    ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
        ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)).im =
      (ρ - ρ⁻¹) * Real.sin t := by
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.sin_neg, Real.cos_neg]
  ring

theorem norm_ellF_pos (γ : ℂ) (ρ : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ) (t : ℝ) :
    0 < ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t‖ := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  rw [NlsGge.GKDefinitionDesign.G2032Ellipse.norm_ellF_eq _ _ (pq_norm_lt γ ρ hγ hρ)]
  exact mul_pos (norm_pos_iff.mpr (pOf_ne_zero γ ρ hγ hρ0))
    (norm_pos_iff.mpr (NlsGge.GKDefinitionDesign.G2032Ellipse.one_add_ellZ_ne_zero _ _
      (pq_norm_lt γ ρ hγ hρ) t))

/-- Boundary value at s = 1: the homotopy is the ellipse. -/
theorem homH_one (τ C γ : ℂ) (R ρ : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ) (t : ℝ) :
    homH τ C γ R ρ 1 t =
      τ + NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t := by
  unfold homH
  simp only [sub_self, zero_mul, zero_add, one_mul]
  conv_rhs =>
    rw [NlsGge.GKDefinitionDesign.G2032Ellipse.ellF_eq_norm_mul_exp _ _
      (pq_norm_lt γ ρ hγ hρ) t]

/-- Boundary value at s = 0: the homotopy is the circle, given the angle relation `hθ`. -/
theorem homH_zero (τ C γ : ℂ) (R ρ : ℝ) (θ : ℝ → ℝ)
    (hθ : ∀ t, C + (R : ℂ) * Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) =
      τ + ((NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
        (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t) : ℝ) : ℂ) *
        Complex.exp ((NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t : ℂ) *
          Complex.I)) (t : ℝ) :
    homH τ C γ R ρ 0 t = C + (R : ℂ) * Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) := by
  unfold homH
  simp only [sub_zero, one_mul, zero_mul, add_zero]
  exact (hθ t).symm

theorem exp_real_add_two_pi (a : ℝ) :
    Complex.exp ((((a + 2 * π : ℝ)) : ℂ) * Complex.I) = Complex.exp ((a : ℂ) * Complex.I) := by
  rw [show ((((a + 2 * π : ℝ)) : ℂ)) * Complex.I = (a : ℂ) * Complex.I + 2 * π * Complex.I by
    push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem ellF_add_two_pi (p q : ℂ) (t : ℝ) :
    NlsGge.GKDefinitionDesign.G2032Ellipse.ellF p q (t + 2 * π) =
      NlsGge.GKDefinitionDesign.G2032Ellipse.ellF p q t := by
  unfold NlsGge.GKDefinitionDesign.G2032Ellipse.ellF
  have h1 : Complex.exp ((((t + 2 * π : ℝ)) : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I) :=
    exp_real_add_two_pi t
  have h2 : Complex.exp (-((((t + 2 * π : ℝ)) : ℂ) * Complex.I)) =
      Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul (((t : ℂ) * Complex.I))]
    have : (-1 : ℂ) * ((((t + 2 * π : ℝ)) : ℂ) * Complex.I) =
        (-1 : ℂ) * ((t : ℂ) * Complex.I) + (-1 : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, mul_comm (-1 : ℂ) (2 * π * Complex.I)]
    rw [show (2 * (π : ℂ) * Complex.I) * (-1 : ℂ) = ((-1 : ℤ) : ℂ) * (2 * π * Complex.I) by
      push_cast; ring, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [h1, h2]

theorem rayR_add_two_pi (w : ℂ) (R : ℝ) (α : ℝ) :
    NlsGge.GKDefinitionDesign.G2032Homotopy.rayR w R (α + 2 * π) =
      NlsGge.GKDefinitionDesign.G2032Homotopy.rayR w R α := by
  simp only [NlsGge.GKDefinitionDesign.G2032Homotopy.rayR, NlsGge.GKDefinitionDesign.G2032Homotopy.rayB,
    NlsGge.GKDefinitionDesign.G2032Homotopy.rayD, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Periodicity in the angle variable: the homotopy closes up for every s. -/
theorem homH_periodic (τ C γ : ℂ) (R ρ : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ) (s t : ℝ) :
    homH τ C γ R ρ s (t + 2 * π) = homH τ C γ R ρ s t := by
  unfold homH
  rw [NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg_add_two_pi, rayR_add_two_pi,
    ellF_add_two_pi, exp_real_add_two_pi]


/-- Algebraic core of the cut-avoidance argument: a point of the homotopy on the gap segment forces
the ellipse to be real along the gap direction. -/
theorem dir_core (γ e : ℂ) (ρ t nE ρs d : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ)
    (he : ‖e‖ = 1) (hρs : 0 < ρs) (hnE : 0 < nE)
    (hEX : γ / 4 * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
        ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) = (nE : ℂ) * e)
    (hd : (ρs : ℂ) * e = ((d : ℝ) : ℂ) / 2 * γ) (hdabs : |d| ≤ 1) :
    ρs ≤ ‖γ‖ / 2 ∧ ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ nE = ‖γ‖ * (ρ + ρ⁻¹) / 4 ∧
      ((‖γ‖ / 2 : ℝ) : ℂ) * e = ((c / 2 : ℝ) : ℂ) * γ := by
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hinv : ρ⁻¹ < ρ := by
    have h1 : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hρ0.ne'
    have h2 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
    nlinarith
  have hK0 : (0 : ℝ) < ρ + ρ⁻¹ := by linarith [inv_pos.mpr hρ0]
  have hK2 : 2 < ρ + ρ⁻¹ := by
    have h3 : ρ⁻¹ * (ρ - 1) ^ 2 = ρ + ρ⁻¹ - 2 := by
      field_simp
      ring
    have h4 : 0 < ρ⁻¹ * (ρ - 1) ^ 2 := mul_pos (inv_pos.mpr hρ0) (by nlinarith)
    linarith
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  -- Step 1: the imaginary part of X(t) vanishes.
  set X : ℂ := (ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
    ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I) with hXdef
  have hX : γ * (X * (ρs : ℂ)) = γ * (((2 * nE * d : ℝ)) : ℂ) := by
    push_cast
    linear_combination (4 * (ρs : ℂ)) * hEX + (4 * (nE : ℂ)) * hd
  have hXr : X * (ρs : ℂ) = ((2 * nE * d : ℝ) : ℂ) := mul_left_cancel₀ hγ hX
  have him0 := congrArg Complex.im hXr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at him0
  have himX : X.im = (ρ - ρ⁻¹) * Real.sin t := by
    rw [hXdef]
    exact im_combo ρ t
  have hsin : Real.sin t = 0 := by
    rw [himX] at him0
    rcases mul_eq_zero.mp him0 with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exfalso
        linarith
      · exact h'
    · exfalso
      linarith
  -- Step 2: X = (ρ + ρ⁻¹) cos t, and cos² = 1.
  have hc2 : Real.cos t * Real.cos t = 1 := by
    have h := Real.sin_sq_add_cos_sq t
    rw [hsin] at h
    nlinarith [h]
  have hexp1 : Complex.exp ((t : ℂ) * Complex.I) = (Real.cos t : ℂ) := by
    apply Complex.ext
    · simp only [Complex.exp_ofReal_mul_I_re, Complex.ofReal_re]
    · simp only [Complex.exp_ofReal_mul_I_im, Complex.ofReal_im, hsin]
  have hexp2 : Complex.exp (((-t : ℝ) : ℂ) * Complex.I) = (Real.cos t : ℂ) := by
    apply Complex.ext
    · simp only [Complex.exp_ofReal_mul_I_re, Complex.ofReal_re, Real.cos_neg]
    · simp only [Complex.exp_ofReal_mul_I_im, Complex.ofReal_im, Real.sin_neg, hsin, neg_zero]
  have hXc : X = ((ρ + ρ⁻¹ : ℝ) : ℂ) * (Real.cos t : ℂ) := by
    rw [hXdef, hexp1, hexp2]
    push_cast
    ring
  have hcabs : |Real.cos t| = 1 := by
    have h := abs_mul_abs_self (Real.cos t)
    rw [hc2] at h
    nlinarith [abs_nonneg (Real.cos t)]
  -- Step 3: the norm identity nE = ‖γ‖ (ρ + ρ⁻¹) / 4.
  have hEc : (nE : ℂ) * e = γ / 4 * (((ρ + ρ⁻¹ : ℝ) : ℂ) * (Real.cos t : ℂ)) := by
    rw [← hXc, ← hEX]
  have hnorm : nE = ‖γ‖ * (ρ + ρ⁻¹) / 4 := by
    have lhs : ‖(nE : ℂ) * e‖ = nE := by
      rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hnE.le]
    have h4 : ‖γ / 4‖ = ‖γ‖ / 4 := by
      rw [norm_div]
      norm_num
    have rhs : ‖γ / 4 * (((ρ + ρ⁻¹ : ℝ) : ℂ) * (Real.cos t : ℂ))‖ = ‖γ‖ * (ρ + ρ⁻¹) / 4 := by
      simp only [norm_mul, h4, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK0, hcabs]
      ring
    calc nE = ‖(nE : ℂ) * e‖ := lhs.symm
      _ = _ := by rw [hEc, rhs]
  -- Step 4: ‖γ‖ e = γ cos t.
  have hKc : ((ρ : ℂ) + (ρ : ℂ)⁻¹) / 4 ≠ 0 := by
    have : (ρ : ℂ) + (ρ : ℂ)⁻¹ = ((ρ + ρ⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr hK0.ne') (by norm_num)
  have h4c : (nE : ℂ) = (‖γ‖ : ℂ) * ((ρ : ℂ) + (ρ : ℂ)⁻¹) / 4 := by
    rw [hnorm]
    push_cast
    ring
  have hEc' : (nE : ℂ) * e = γ / 4 * (((ρ : ℂ) + (ρ : ℂ)⁻¹) * (Real.cos t : ℂ)) := by
    rw [hEc]
    push_cast
    ring
  have h5 : ((ρ : ℂ) + (ρ : ℂ)⁻¹) / 4 * ((‖γ‖ : ℂ) * e) =
      ((ρ : ℂ) + (ρ : ℂ)⁻¹) / 4 * (γ * (Real.cos t : ℂ)) := by
    linear_combination hEc' - e * h4c
  have h6 : (‖γ‖ : ℂ) * e = γ * (Real.cos t : ℂ) := mul_left_cancel₀ hKc h5
  -- Step 5: the bound on ρs, and the sign data.
  have hn1 : ‖(ρs : ℂ) * e‖ = ρs := by
    rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_of_nonneg hρs.le]
  have hn2 : ‖((d : ℝ) : ℂ) / 2 * γ‖ = |d| / 2 * ‖γ‖ := by
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hρle : ρs ≤ ‖γ‖ / 2 := by
    have h := hn1
    rw [hd, hn2] at h
    nlinarith [mul_le_mul_of_nonneg_right hdabs hγn.le]
  refine ⟨hρle, Real.cos t, mul_self_eq_one_iff.mp hc2, hnorm, ?_⟩
  rw [show ((‖γ‖ / 2 : ℝ) : ℂ) = (‖γ‖ : ℂ) / 2 by push_cast; ring,
    show ((Real.cos t / 2 : ℝ) : ℂ) = (Real.cos t : ℂ) / 2 by push_cast; ring]
  linear_combination (1 / 2 : ℂ) * h6

/-- The homotopy stays in the closed disc of the isolating circle. -/
theorem homH_normSq_le (τ C γ : ℂ) (R ρ s t : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ)
    (hw : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2)
    (hin : Complex.normSq ((τ - C) +
      NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t) < R ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Complex.normSq (homH τ C γ R ρ s t - C) ≤ R ^ 2 := by
  have hpq := pq_norm_lt γ ρ hγ hρ
  have hE1 := NlsGge.GKDefinitionDesign.G2032Ellipse.ellF_eq_norm_mul_exp (pOf γ ρ) (qOf γ ρ) hpq t
  have hEpos := norm_ellF_pos γ ρ hγ hρ t
  have hr := NlsGge.GKDefinitionDesign.G2032Homotopy.rayR_pos (τ - C) R
    (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t) hw
  have hlt : ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t‖ <
      NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
        (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t) := by
    apply NlsGge.GKDefinitionDesign.G2032Homotopy.lt_rayR_of_normSq_lt (τ - C) R _ _ hw (norm_nonneg _)
    rw [← hE1]
    exact hin
  have hzC : homH τ C γ R ρ s t - C =
      (τ - C) + (((1 - s) * NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R
        (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t) +
        s * ‖NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t‖ : ℝ) : ℂ) *
        Complex.exp ((NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t : ℂ) *
          Complex.I) := by
    unfold homH
    ring
  rw [hzC]
  apply NlsGge.GKDefinitionDesign.G2032Homotopy.normSq_le_of_le_rayR (τ - C) R _ _ hw
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hr.le, mul_nonneg hs0 hEpos.le]
  · nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hlt.le)]

/-- The homotopy never meets the gap segment `[τ − γ/2, τ + γ/2]` (for s ∈ [0,1]). -/
theorem homH_not_mem_cut (τ C γ : ℂ) (R ρ s t : ℝ) (hγ : γ ≠ 0) (hρ : 1 < ρ)
    (hw : (τ - C).re ^ 2 + (τ - C).im ^ 2 < R ^ 2)
    (hA : Complex.normSq ((τ - C) + γ / 2) < R ^ 2)
    (hB : Complex.normSq ((τ - C) - γ / 2) < R ^ 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    homH τ C γ R ρ s t ∉ segment ℝ (τ - γ / 2) (τ + γ / 2) := by
  intro hmem
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hmem
  rw [Complex.real_smul, Complex.real_smul] at hz
  have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hpq := pq_norm_lt γ ρ hγ hρ
  have hE1 := NlsGge.GKDefinitionDesign.G2032Ellipse.ellF_eq_norm_mul_exp (pOf γ ρ) (qOf γ ρ) hpq t
  have hE2 := ellF_pq γ ρ t
  have hEpos := norm_ellF_pos γ ρ hγ hρ t
  have hγn : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hr := NlsGge.GKDefinitionDesign.G2032Homotopy.rayR_pos (τ - C) R
    (NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t) hw
  have he : ‖Complex.exp ((NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t : ℂ) *
      Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  unfold homH at hz
  set β := NlsGge.GKDefinitionDesign.G2032Ellipse.ellArg (pOf γ ρ) (qOf γ ρ) t with hβ
  set E := NlsGge.GKDefinitionDesign.G2032Ellipse.ellF (pOf γ ρ) (qOf γ ρ) t with hEdef
  set r := NlsGge.GKDefinitionDesign.G2032Homotopy.rayR (τ - C) R β with hrdef
  set nE := ‖E‖ with hnEdef
  set ρs := (1 - s) * r + s * nE with hρsdef
  set e := Complex.exp ((β : ℂ) * Complex.I) with hedef
  have hρs : 0 < ρs := by
    have hm := lt_min hr hEpos
    rw [hρsdef]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr (min_le_left r nE)),
      mul_nonneg hs0 (sub_nonneg.mpr (min_le_right r nE)), min_le_left r nE]
  have hd : (ρs : ℂ) * e = ((b - a : ℝ) : ℂ) / 2 * γ := by
    push_cast
    linear_combination (-1 : ℂ) * hz + τ * hab'
  have hdabs : |b - a| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hEX : γ / 4 * ((ρ : ℂ) * Complex.exp ((t : ℂ) * Complex.I) +
      ((ρ⁻¹ : ℝ) : ℂ) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)) = (nE : ℂ) * e := by
    rw [← hE2, hE1]
  obtain ⟨hcon, c, hc, hnEeq, hkey⟩ :=
    dir_core γ e ρ t nE ρs (b - a) hγ hρ he hρs hEpos hEX hd hdabs
  have hnE2 : ‖γ‖ / 2 < nE := by
    rw [hnEeq]
    nlinarith [mul_pos hγn (sub_pos.mpr (show (2 : ℝ) < ρ + ρ⁻¹ from by
      have h3 : ρ⁻¹ * (ρ - 1) ^ 2 = ρ + ρ⁻¹ - 2 := by
        field_simp
        ring
      have h4 : 0 < ρ⁻¹ * (ρ - 1) ^ 2 := mul_pos (inv_pos.mpr hρ0) (by nlinarith)
      linarith))]
  have hn : Complex.normSq ((τ - C) + ((‖γ‖ / 2 : ℝ) : ℂ) * e) < R ^ 2 := by
    rcases hc with rfl | rfl
    · have h : (τ - C) + ((‖γ‖ / 2 : ℝ) : ℂ) * e = (τ - C) + γ / 2 := by
        rw [hkey]
        push_cast
        ring
      rw [h]
      exact hA
    · have h : (τ - C) + ((‖γ‖ / 2 : ℝ) : ℂ) * e = (τ - C) - γ / 2 := by
        rw [hkey]
        push_cast
        ring
      rw [h]
      exact hB
  have hr2 : ‖γ‖ / 2 < r :=
    NlsGge.GKDefinitionDesign.G2032Homotopy.lt_rayR_of_normSq_lt (τ - C) R β (‖γ‖ / 2) hw
      (by positivity) hn
  have hmin := lt_min hr2 hnE2
  have hρs_gt : ‖γ‖ / 2 < ρs := by
    rw [hρsdef]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr (le_of_lt (lt_min hr2 hnE2))),
      mul_nonneg hs0 (sub_nonneg.mpr (le_of_lt (lt_min hr2 hnE2))),
      min_le_left r nE, min_le_right r nE]
  linarith

end
end G2032Homo
end NlsGge.GKDefinitionDesign

