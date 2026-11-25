import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS031Analytic

/- KSPS-031 SHARP CORE (proof development, AUTHOR; not reviewed). Intended target
   NlsGge/ThirdConsultation/KSPS/KSPS031SharpCore.lean, module NlsGge.ThirdConsultation.KSPS.KSPS031SharpCore.
   Pure (Mathlib + landed KSPS031Analytic) pieces of Pro round 16 §2.3 (PRO_DEFINITION_RESPONSE_FP80_16.md):
   cosine/sine bounds on a strip, the second-order cosine Taylor estimate, and the exact algebra
     Δ − 2cos(θ+δ) = Dinv·P·(r0+r1) − Dinv·Q·(αR01+βR10) + 2i·I·P·((sinθ − sin a) − Dinv·β·α·sin a)
                     − 2(cos(θ+δ) − cosθ + δ sinθ),
   with P = (2ia)^{-(N+1)}, Q = (2ia)^{-N}, δ = i(2i)^{-(N+1)} I a^{-(N+1)}, r0 = 2ia R00 − e^{-ia} I,
   r1 = 2ia R11 + e^{ia} I, starting from the exact KSPS015W.disc_identity form. The diagonal leading terms
   cancel against 2δ sin a exactly as in Pro §2.3. The limit lemma turns "residuals → 0" into the little-o of
   the sharp head. -/
set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS031SharpCore
noncomputable section

/-! ### Trigonometric bounds -/

theorem two_cos_eq' (z : ℂ) :
    2 * Complex.cos z = Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) := by
  simp only [Complex.cos, neg_mul]
  ring

theorem two_I_sin_eq' (z : ℂ) :
    2 * Complex.I * Complex.sin z = Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) := by
  simp only [Complex.sin, neg_mul]
  linear_combination (Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) * Complex.I_sq

theorem norm_exp_mul_I_le (z : ℂ) : ‖Complex.exp (z * Complex.I)‖ ≤ Real.exp |z.im| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have h : (z * Complex.I).re = -z.im := by simp [Complex.mul_re]
  rw [h]
  exact neg_le_abs _

theorem norm_exp_neg_mul_I_le (z : ℂ) : ‖Complex.exp (-(z * Complex.I))‖ ≤ Real.exp |z.im| := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have h : (-(z * Complex.I)).re = z.im := by simp [Complex.mul_re]
  rw [h]
  exact le_abs_self _

theorem norm_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := two_cos_eq' z
  have h2 : ‖2 * Complex.cos z‖ ≤ 2 * Real.exp |z.im| := by
    rw [h]
    calc _ ≤ ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖ := norm_add_le _ _
      _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
          add_le_add (norm_exp_mul_I_le z) (norm_exp_neg_mul_I_le z)
      _ = 2 * Real.exp |z.im| := by ring
  rw [norm_mul, Complex.norm_ofNat] at h2
  linarith

theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h := two_I_sin_eq' z
  have h2 : ‖2 * Complex.I * Complex.sin z‖ ≤ 2 * Real.exp |z.im| := by
    rw [h]
    calc _ ≤ ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖ := norm_sub_le _ _
      _ ≤ Real.exp |z.im| + Real.exp |z.im| :=
          add_le_add (norm_exp_mul_I_le z) (norm_exp_neg_mul_I_le z)
      _ = 2 * Real.exp |z.im| := by ring
  rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one] at h2
  linarith

theorem norm_sin_sub_self_le {δ : ℂ} (h : ‖δ‖ ≤ 1) : ‖Complex.sin δ - δ‖ ≤ ‖δ‖ ^ 2 := by
  have hb := Complex.sin_bound h
  have e : Complex.sin δ - δ = (Complex.sin δ - (δ - δ ^ 3 / 6)) - δ ^ 3 / 6 := by ring
  have h3 : ‖δ ^ 3 / 6‖ = ‖δ‖ ^ 3 / 6 := by rw [norm_div, norm_pow, Complex.norm_ofNat]
  have hn := norm_nonneg δ
  have p3 : ‖δ‖ ^ 3 ≤ ‖δ‖ ^ 2 := pow_le_pow_of_le_one hn h (by norm_num)
  have p5 : ‖δ‖ ^ 5 ≤ ‖δ‖ ^ 2 := pow_le_pow_of_le_one hn h (by norm_num)
  have p2 : 0 ≤ ‖δ‖ ^ 2 := by positivity
  rw [e]
  calc _ ≤ ‖Complex.sin δ - (δ - δ ^ 3 / 6)‖ + ‖δ ^ 3 / 6‖ := norm_sub_le _ _
    _ ≤ ‖δ‖ ^ 2 := by rw [h3]; linarith

theorem norm_cos_sub_one_le_sq {δ : ℂ} (h : ‖δ‖ ≤ 1) : ‖Complex.cos δ - 1‖ ≤ ‖δ‖ ^ 2 := by
  have hc := NlsGge.ThirdConsultation.KSPS031Analytic.norm_cos_sub_one_le h
  have hn := norm_nonneg δ
  have p4 : ‖δ‖ ^ 4 ≤ ‖δ‖ ^ 2 := pow_le_pow_of_le_one hn h (by norm_num)
  have p2 : 0 ≤ ‖δ‖ ^ 2 := by positivity
  linarith

/-- Second-order Taylor bound for the cosine. -/
theorem cos_taylor2 (θ δ : ℂ) (hδ : ‖δ‖ ≤ 1) :
    ‖Complex.cos (θ + δ) - Complex.cos θ + δ * Complex.sin θ‖ ≤
      2 * Real.exp |θ.im| * ‖δ‖ ^ 2 := by
  have e : Complex.cos (θ + δ) - Complex.cos θ + δ * Complex.sin θ =
      Complex.cos θ * (Complex.cos δ - 1) - Complex.sin θ * (Complex.sin δ - δ) := by
    rw [Complex.cos_add]
    ring
  rw [e]
  have h1 := norm_cos_le_exp θ
  have h2 := norm_sin_le_exp θ
  have h3 := norm_cos_sub_one_le_sq hδ
  have h4 := norm_sin_sub_self_le hδ
  calc _ ≤ ‖Complex.cos θ * (Complex.cos δ - 1)‖ + ‖Complex.sin θ * (Complex.sin δ - δ)‖ :=
        norm_sub_le _ _
    _ = ‖Complex.cos θ‖ * ‖Complex.cos δ - 1‖ + ‖Complex.sin θ‖ * ‖Complex.sin δ - δ‖ := by
        rw [norm_mul, norm_mul]
    _ ≤ Real.exp |θ.im| * ‖δ‖ ^ 2 + Real.exp |θ.im| * ‖δ‖ ^ 2 := by
        gcongr
    _ = 2 * Real.exp |θ.im| * ‖δ‖ ^ 2 := by ring

theorem norm_sin_le_two_mul {x : ℂ} (h : ‖x‖ ≤ 1) : ‖Complex.sin x‖ ≤ 2 * ‖x‖ := by
  have hs := NlsGge.ThirdConsultation.KSPS031Analytic.norm_sin_le_of_le_one h
  have hn := norm_nonneg x
  have p3 : ‖x‖ ^ 3 ≤ ‖x‖ := pow_le_of_le_one hn h (by norm_num)
  have p5 : ‖x‖ ^ 5 ≤ ‖x‖ := pow_le_of_le_one hn h (by norm_num)
  linarith

/-- Lipschitz bound for the sine near a real point. -/
theorem norm_sin_sub_sin_real_le (θ : ℂ) (a : ℝ) (h : ‖θ - a‖ ≤ 1) :
    ‖Complex.sin θ - Complex.sin a‖ ≤ 2 * Real.exp |θ.im| * ‖θ - a‖ := by
  rw [Complex.sin_sub_sin]
  have hx : ‖(θ - a) / 2‖ ≤ 1 := by
    rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg (θ - a)]
  have h1 := norm_sin_le_two_mul hx
  have h2 := norm_cos_le_exp ((θ + a) / 2)
  have him : |((θ + a) / 2).im| ≤ |θ.im| := by
    have : ((θ + (a : ℂ)) / 2).im = θ.im / 2 := by simp
    rw [this, abs_div, abs_two]
    linarith [abs_nonneg θ.im]
  have h3 : Real.exp |((θ + a) / 2).im| ≤ Real.exp |θ.im| := Real.exp_le_exp.2 him
  rw [norm_div, Complex.norm_ofNat] at h1
  rw [norm_mul, norm_mul, Complex.norm_ofNat]
  calc 2 * ‖Complex.sin ((θ - a) / 2)‖ * ‖Complex.cos ((θ + a) / 2)‖
      ≤ 2 * (2 * (‖θ - a‖ / 2)) * Real.exp |θ.im| := by
        gcongr
        exact h2.trans h3
    _ = 2 * Real.exp |θ.im| * ‖θ - a‖ := by ring

theorem norm_sin_real_le_one (a : ℝ) : ‖Complex.sin (a : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sin_le_one a

theorem abs_im_le_of_real (θ : ℂ) (a : ℝ) : |θ.im| ≤ ‖θ - a‖ := by
  have h : (θ - (a : ℂ)).im = θ.im := by simp
  rw [← h]
  exact Complex.abs_im_le_norm _

/-! ### Exact algebra and the pointwise sharp bound -/

/-- The sharp correction δ = i (2i)^{-(N+1)} I a^{-(N+1)} equals i·I·(2ia)^{-(N+1)}. -/
theorem delta_eq (N : ℕ) (a Ic : ℂ) :
    Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic * a ^ (-((N + 1 : ℕ) : ℤ)) =
      Complex.I * Ic * ((2 * Complex.I * a) ^ (N + 1))⁻¹ := by
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, mul_pow, mul_inv]
  ring

theorem sharp_identity (θ δ Δ Dinv α β R00 R11 R01 R10 Ic P Q ν : ℂ) (a : ℂ)
    (hν : ν = 2 * Complex.I * a)
    (hid : Δ - 2 * Complex.cos θ = Dinv * (Q * (R00 + R11 - α * R01 - β * R10)))
    (hPν : P * ν = Q) (hD : Dinv * (1 - β * α) = 1) (hδ : δ = Complex.I * Ic * P) :
    Δ - 2 * Complex.cos (θ + δ) =
      Dinv * P * ((ν * R00 - Complex.exp (-(Complex.I * a)) * Ic) +
          (ν * R11 + Complex.exp (Complex.I * a) * Ic)) -
        Dinv * Q * (α * R01 + β * R10) +
        2 * Complex.I * Ic * P * ((Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a) -
        2 * (Complex.cos (θ + δ) - Complex.cos θ + δ * Complex.sin θ) := by
  have hsin : 2 * Complex.I * Complex.sin a =
      Complex.exp (Complex.I * a) - Complex.exp (-(Complex.I * a)) := by
    rw [two_I_sin_eq', mul_comm a Complex.I]
  linear_combination hid - Dinv * (R00 + R11) * hPν + Dinv * P * Ic * hsin -
    2 * Complex.I * Ic * P * Complex.sin a * hD + 2 * Complex.sin θ * hδ

/-- Pointwise sharp bound at one large real parameter a. -/
theorem sharp_pointwise (N : ℕ) (a : ℝ) (θ Δ Dinv α β R00 R11 R01 R10 Ic : ℂ) (S Cφ : ℝ)
    (hX : 1 ≤ |a|) (hS : 0 ≤ S) (hCφ : 0 ≤ Cφ) (hCX : Cφ ≤ |a|) (hIX : ‖Ic‖ ≤ |a|)
    (hθ : ‖θ - a‖ ≤ Cφ / |a|) (hα : ‖α‖ ≤ S / (2 * |a|)) (hβ : ‖β‖ ≤ S / (2 * |a|))
    (hD : Dinv * (1 - β * α) = 1) (hDn : ‖Dinv‖ ≤ 2)
    (hid : Δ - 2 * Complex.cos θ =
      Dinv * (((2 * Complex.I * a) ^ N)⁻¹ * (R00 + R11 - α * R01 - β * R10))) :
    |a| ^ (N + 1) * ‖Δ - 2 * Complex.cos (θ + Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) *
        Ic * (a : ℂ) ^ (-((N + 1 : ℕ) : ℤ)))‖ ≤
      2 * (‖2 * Complex.I * a * R00 - Complex.exp (-(Complex.I * a)) * Ic‖ +
          ‖2 * Complex.I * a * R11 + Complex.exp (Complex.I * a) * Ic‖) +
        2 * S * (‖R01‖ + ‖R10‖) +
        (2 * ‖Ic‖ * (6 * Cφ + S ^ 2) + 12 * ‖Ic‖ ^ 2) / |a| := by
  set X : ℝ := |a| with hXdef
  have hX0 : 0 < X := by linarith
  have ha0 : (a : ℂ) ≠ 0 := by
    intro h
    rw [Complex.ofReal_eq_zero] at h
    rw [hXdef, h, abs_zero] at hX
    norm_num at hX
  have hν0 : (2 * Complex.I * (a : ℂ)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) ha0
  have hνn : ‖2 * Complex.I * (a : ℂ)‖ = 2 * X := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      mul_one]
  obtain ⟨P, hP⟩ : ∃ P : ℂ, P = ((2 * Complex.I * (a : ℂ)) ^ (N + 1))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ, Q = ((2 * Complex.I * (a : ℂ)) ^ N)⁻¹ := ⟨_, rfl⟩
  have hPν : P * (2 * Complex.I * (a : ℂ)) = Q := by
    rw [hP, hQ, pow_succ]
    field_simp
  have hPn : ‖P‖ = ((2 * X) ^ (N + 1))⁻¹ := by rw [hP, norm_inv, norm_pow, hνn]
  have hQn : ‖Q‖ = ((2 * X) ^ N)⁻¹ := by rw [hQ, norm_inv, norm_pow, hνn]
  have h2X : 0 < 2 * X := by linarith
  -- X^(N+1) ‖P‖ ≤ 1, ‖P‖ ≤ 1/X, X^(N+1) ‖Q‖ ≤ X
  have hXP : X ^ (N + 1) * ‖P‖ ≤ 1 := by
    rw [hPn, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hX0.le (by linarith) _
  have hPX : ‖P‖ ≤ 1 / X := by
    rw [hPn, one_div]
    apply inv_anti₀ hX0
    calc X ≤ 2 * X := by linarith
      _ ≤ (2 * X) ^ (N + 1) := le_self_pow₀ (by linarith) (by omega)
  have hXQ : X ^ (N + 1) * ‖Q‖ ≤ X := by
    rw [hQn, pow_succ, mul_comm (X ^ N) X, mul_assoc, ← div_eq_mul_inv]
    have : X ^ N / (2 * X) ^ N ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact pow_le_pow_left₀ hX0.le (by linarith) _
    nlinarith
  have hP0 := norm_nonneg P
  -- the correction
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℂ, δ = Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic *
      (a : ℂ) ^ (-((N + 1 : ℕ) : ℤ)) := ⟨_, rfl⟩
  have hδ : δ = Complex.I * Ic * P := by rw [hδdef, delta_eq, hP]
  rw [← hδdef]
  have hδn : ‖δ‖ = ‖Ic‖ * ‖P‖ := by rw [hδ, norm_mul, norm_mul, Complex.norm_I, one_mul]
  have hIc0 := norm_nonneg Ic
  have hδ1 : ‖δ‖ ≤ 1 := by
    rw [hδn]
    calc ‖Ic‖ * ‖P‖ ≤ X * (1 / X) := mul_le_mul hIX hPX hP0 hX0.le
      _ = 1 := by field_simp
  -- phase facts
  have hθ1 : ‖θ - a‖ ≤ 1 := by
    refine hθ.trans ?_
    rw [div_le_one hX0]; exact hCX
  have hexp : Real.exp |θ.im| ≤ 3 := by
    have h1 : |θ.im| ≤ 1 := (abs_im_le_of_real θ a).trans hθ1
    have h2 : Real.exp |θ.im| ≤ Real.exp 1 := Real.exp_le_exp.2 h1
    have h3 := Real.exp_one_lt_d9
    norm_num at h3
    linarith
  have hexp0 : 0 ≤ Real.exp |θ.im| := (Real.exp_pos _).le
  -- the exact identity
  rw [← hQ] at hid
  have hE := sharp_identity θ δ Δ Dinv α β R00 R11 R01 R10 Ic P Q (2 * Complex.I * (a : ℂ)) a rfl
    hid hPν hD hδ
  rw [hE]
  set r0 : ℂ := 2 * Complex.I * (a : ℂ) * R00 - Complex.exp (-(Complex.I * a)) * Ic with hr0
  set r1 : ℂ := 2 * Complex.I * (a : ℂ) * R11 + Complex.exp (Complex.I * a) * Ic with hr1
  set T4 : ℂ := Complex.cos (θ + δ) - Complex.cos θ + δ * Complex.sin θ with hT4
  -- piece bounds
  have hXN : 0 ≤ X ^ (N + 1) := by positivity
  have B1 : X ^ (N + 1) * ‖Dinv * P * (r0 + r1)‖ ≤ 2 * (‖r0‖ + ‖r1‖) := by
    rw [norm_mul, norm_mul]
    have hr : ‖r0 + r1‖ ≤ ‖r0‖ + ‖r1‖ := norm_add_le _ _
    have hs0 : 0 ≤ ‖r0‖ + ‖r1‖ := by positivity
    calc X ^ (N + 1) * (‖Dinv‖ * ‖P‖ * ‖r0 + r1‖)
        ≤ X ^ (N + 1) * (2 * ‖P‖ * (‖r0‖ + ‖r1‖)) := by gcongr
      _ = 2 * (‖r0‖ + ‖r1‖) * (X ^ (N + 1) * ‖P‖) := by ring
      _ ≤ 2 * (‖r0‖ + ‖r1‖) * 1 := by gcongr
      _ = 2 * (‖r0‖ + ‖r1‖) := by ring
  have B2 : X ^ (N + 1) * ‖Dinv * Q * (α * R01 + β * R10)‖ ≤ 2 * S * (‖R01‖ + ‖R10‖) := by
    rw [norm_mul, norm_mul]
    have hab : ‖α * R01 + β * R10‖ ≤ S / (2 * X) * (‖R01‖ + ‖R10‖) := by
      calc ‖α * R01 + β * R10‖ ≤ ‖α‖ * ‖R01‖ + ‖β‖ * ‖R10‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ S / (2 * X) * ‖R01‖ + S / (2 * X) * ‖R10‖ := by gcongr
        _ = S / (2 * X) * (‖R01‖ + ‖R10‖) := by ring
    have hR0 : 0 ≤ ‖R01‖ + ‖R10‖ := by positivity
    have hSX : 0 ≤ S / (2 * X) := by positivity
    calc X ^ (N + 1) * (‖Dinv‖ * ‖Q‖ * ‖α * R01 + β * R10‖)
        ≤ X ^ (N + 1) * (2 * ‖Q‖ * (S / (2 * X) * (‖R01‖ + ‖R10‖))) := by gcongr
      _ = 2 * (S / (2 * X)) * (‖R01‖ + ‖R10‖) * (X ^ (N + 1) * ‖Q‖) := by ring
      _ ≤ 2 * (S / (2 * X)) * (‖R01‖ + ‖R10‖) * X := by gcongr
      _ = S * (‖R01‖ + ‖R10‖) := by field_simp <;> ring
      _ ≤ 2 * S * (‖R01‖ + ‖R10‖) := by nlinarith
  have B3 : X ^ (N + 1) * ‖2 * Complex.I * Ic * P *
      ((Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a)‖ ≤
      2 * ‖Ic‖ * (6 * Cφ + S ^ 2) / X := by
    have hs1 : ‖Complex.sin θ - Complex.sin a‖ ≤ 6 * Cφ / X := by
      have h := norm_sin_sub_sin_real_le θ a hθ1
      calc _ ≤ 2 * Real.exp |θ.im| * ‖θ - a‖ := h
        _ ≤ 2 * 3 * (Cφ / X) := by gcongr
        _ = 6 * Cφ / X := by ring
    have hs2 : ‖Dinv * β * α * Complex.sin a‖ ≤ S ^ 2 / X := by
      rw [norm_mul, norm_mul, norm_mul]
      have hsa := norm_sin_real_le_one a
      have hSX : 0 ≤ S / (2 * X) := by positivity
      calc ‖Dinv‖ * ‖β‖ * ‖α‖ * ‖Complex.sin a‖ ≤ 2 * (S / (2 * X)) * (S / (2 * X)) * 1 := by
            gcongr
        _ = S ^ 2 / (2 * X ^ 2) := by field_simp <;> ring
        _ ≤ S ^ 2 / X := by
            apply div_le_div_of_nonneg_left (sq_nonneg S) hX0
            nlinarith
    have hsum : ‖(Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a‖ ≤
        (6 * Cφ + S ^ 2) / X := by
      calc _ ≤ ‖Complex.sin θ - Complex.sin a‖ + ‖Dinv * β * α * Complex.sin a‖ := norm_sub_le _ _
        _ ≤ 6 * Cφ / X + S ^ 2 / X := add_le_add hs1 hs2
        _ = (6 * Cφ + S ^ 2) / X := by ring
    rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
    have hq0 : 0 ≤ (6 * Cφ + S ^ 2) / X := by positivity
    calc X ^ (N + 1) * (2 * ‖Ic‖ * ‖P‖ *
          ‖(Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a‖)
        ≤ X ^ (N + 1) * (2 * ‖Ic‖ * ‖P‖ * ((6 * Cφ + S ^ 2) / X)) := by gcongr
      _ = 2 * ‖Ic‖ * ((6 * Cφ + S ^ 2) / X) * (X ^ (N + 1) * ‖P‖) := by ring
      _ ≤ 2 * ‖Ic‖ * ((6 * Cφ + S ^ 2) / X) * 1 := by gcongr
      _ = 2 * ‖Ic‖ * (6 * Cφ + S ^ 2) / X := by ring
  have B4 : X ^ (N + 1) * ‖2 * T4‖ ≤ 12 * ‖Ic‖ ^ 2 / X := by
    have hT := cos_taylor2 θ δ hδ1
    rw [norm_mul, Complex.norm_ofNat]
    have hT' : ‖T4‖ ≤ 6 * (‖Ic‖ * ‖P‖) ^ 2 := by
      calc ‖T4‖ ≤ 2 * Real.exp |θ.im| * ‖δ‖ ^ 2 := hT
        _ ≤ 2 * 3 * ‖δ‖ ^ 2 := by gcongr
        _ = 6 * (‖Ic‖ * ‖P‖) ^ 2 := by rw [hδn]; ring
    calc X ^ (N + 1) * (2 * ‖T4‖) ≤ X ^ (N + 1) * (2 * (6 * (‖Ic‖ * ‖P‖) ^ 2)) := by gcongr
      _ = 12 * ‖Ic‖ ^ 2 * ‖P‖ * (X ^ (N + 1) * ‖P‖) := by ring
      _ ≤ 12 * ‖Ic‖ ^ 2 * ‖P‖ * 1 := by gcongr
      _ ≤ 12 * ‖Ic‖ ^ 2 * (1 / X) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hPX (by positivity)
      _ = 12 * ‖Ic‖ ^ 2 / X := by ring
  -- triangle inequality
  have htri : ‖Dinv * P * (r0 + r1) - Dinv * Q * (α * R01 + β * R10) +
        2 * Complex.I * Ic * P * ((Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a) -
        2 * T4‖ ≤
      ‖Dinv * P * (r0 + r1)‖ + ‖Dinv * Q * (α * R01 + β * R10)‖ +
        ‖2 * Complex.I * Ic * P * ((Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a)‖ +
        ‖2 * T4‖ := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    refine (norm_add_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  have hmul := mul_le_mul_of_nonneg_left htri hXN
  have e2 : (2 * ‖Ic‖ * (6 * Cφ + S ^ 2) + 12 * ‖Ic‖ ^ 2) / X =
      2 * ‖Ic‖ * (6 * Cφ + S ^ 2) / X + 12 * ‖Ic‖ ^ 2 / X := by ring
  rw [e2]
  have hsplit : X ^ (N + 1) * (‖Dinv * P * (r0 + r1)‖ + ‖Dinv * Q * (α * R01 + β * R10)‖ +
        ‖2 * Complex.I * Ic * P * ((Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a)‖ +
        ‖2 * T4‖) =
      X ^ (N + 1) * ‖Dinv * P * (r0 + r1)‖ + X ^ (N + 1) * ‖Dinv * Q * (α * R01 + β * R10)‖ +
        X ^ (N + 1) * ‖2 * Complex.I * Ic * P *
          ((Complex.sin θ - Complex.sin a) - Dinv * β * α * Complex.sin a)‖ +
        X ^ (N + 1) * ‖2 * T4‖ := by ring
  linarith [B1, B2, B3, B4, hmul, hsplit]

/-- Little-o assembly along the cofinite filter on ℤ. -/
theorem sharp_limit (N : ℕ) (a : ℤ → ℝ) (θ Δ Dinv α β R00 R11 R01 R10 : ℤ → ℂ) (Ic : ℂ)
    (S Cφ : ℝ) (hS : 0 ≤ S) (hCφ : 0 ≤ Cφ)
    (ha : Tendsto (fun j => |a j|) cofinite atTop)
    (hev : ∀ᶠ j in cofinite,
      ‖θ j - a j‖ ≤ Cφ / |a j| ∧ ‖α j‖ ≤ S / (2 * |a j|) ∧ ‖β j‖ ≤ S / (2 * |a j|) ∧
      Dinv j * (1 - β j * α j) = 1 ∧ ‖Dinv j‖ ≤ 2 ∧
      Δ j - 2 * Complex.cos (θ j) =
        Dinv j * (((2 * Complex.I * (a j : ℂ)) ^ N)⁻¹ *
          (R00 j + R11 j - α j * R01 j - β j * R10 j)))
    (h0 : Tendsto (fun j => 2 * Complex.I * (a j : ℂ) * R00 j -
      Complex.exp (-(Complex.I * a j)) * Ic) cofinite (𝓝 0))
    (h1 : Tendsto (fun j => 2 * Complex.I * (a j : ℂ) * R11 j +
      Complex.exp (Complex.I * a j) * Ic) cofinite (𝓝 0))
    (h01 : Tendsto R01 cofinite (𝓝 0)) (h10 : Tendsto R10 cofinite (𝓝 0)) :
    Tendsto (fun j => |a j| ^ (N + 1) * ‖Δ j - 2 * Complex.cos (θ j + Complex.I *
        (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic * (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ)))‖)
      cofinite (𝓝 0) := by
  set K : ℝ := 2 * ‖Ic‖ * (6 * Cφ + S ^ 2) + 12 * ‖Ic‖ ^ 2 with hK
  have hg : Tendsto (fun j => 2 * (‖2 * Complex.I * (a j : ℂ) * R00 j -
        Complex.exp (-(Complex.I * a j)) * Ic‖ +
        ‖2 * Complex.I * (a j : ℂ) * R11 j + Complex.exp (Complex.I * a j) * Ic‖) +
      2 * S * (‖R01 j‖ + ‖R10 j‖) + K / |a j|) cofinite (𝓝 0) := by
    have t0 := h0.norm
    have t1 := h1.norm
    have t2 := h01.norm
    have t3 := h10.norm
    have t4 : Tendsto (fun j => K / |a j|) cofinite (𝓝 0) := tendsto_const_nhds.div_atTop ha
    rw [norm_zero] at t0 t1 t2 t3
    have := (((t0.add t1).const_mul 2).add ((t2.add t3).const_mul (2 * S))).add t4
    simpa using this
  have hbig : ∀ᶠ j in cofinite, max (max 1 Cφ) ‖Ic‖ ≤ |a j| :=
    (tendsto_atTop.1 ha) (max (max 1 Cφ) ‖Ic‖)
  refine squeeze_zero' (Eventually.of_forall (fun j => by positivity)) ?_ hg
  filter_upwards [hev, hbig] with j hj hb
  obtain ⟨hθ, hα, hβ, hD, hDn, hid⟩ := hj
  have hX : 1 ≤ |a j| := (le_max_left _ _).trans ((le_max_left _ _).trans hb)
  have hCX : Cφ ≤ |a j| := (le_max_right _ _).trans ((le_max_left _ _).trans hb)
  have hIX : ‖Ic‖ ≤ |a j| := (le_max_right _ _).trans hb
  exact sharp_pointwise N (a j) (θ j) (Δ j) (Dinv j) (α j) (β j) (R00 j) (R11 j) (R01 j) (R10 j) Ic
    S Cφ hX hS hCφ hCX hIX hθ hα hβ hD hDn hid

/-- Size of the sharp correction. -/
theorem delta_norm_le (N : ℕ) (a : ℝ) (Ic : ℂ) (hX : 1 ≤ |a|) :
    ‖Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic * (a : ℂ) ^ (-((N + 1 : ℕ) : ℤ))‖ ≤
      ‖Ic‖ / |a| := by
  rw [delta_eq, norm_mul, norm_mul, Complex.norm_I, one_mul, norm_inv, norm_pow, norm_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, mul_one, ← div_eq_mul_inv]
  have hX0 : 0 < |a| := by linarith
  apply div_le_div_of_nonneg_left (norm_nonneg _) hX0
  calc |a| ≤ 2 * |a| := by linarith
    _ ≤ (2 * |a|) ^ (N + 1) := le_self_pow₀ (by linarith) (by omega)

/-- From the little-o limit: eventually the corrected phase is in the chart radius and the
    doubled discriminant error is at most ε / |a|^(N+1). -/
theorem sharp_eventually (N : ℕ) (a : ℤ → ℝ) (θ Δ : ℤ → ℂ) (Ic : ℂ) (Cφ : ℝ)
    (ha : Tendsto (fun j => |a j|) cofinite atTop)
    (hθ : ∀ᶠ j in cofinite, ‖θ j - a j‖ ≤ Cφ / |a j|)
    (hlim : Tendsto (fun j => |a j| ^ (N + 1) * ‖Δ j - 2 * Complex.cos (θ j + Complex.I *
        (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic * (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ)))‖)
      cofinite (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ j in cofinite,
      ‖(θ j + Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic *
          (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ))) - a j‖ < Real.pi / 8 ∧
      2 * ‖Δ j - 2 * Complex.cos (θ j + Complex.I *
        (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic * (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ)))‖ ≤
        ε / |a j| ^ (N + 1) := by
  have hsmall := hlim.eventually (gt_mem_nhds (half_pos hε))
  have hbig : ∀ᶠ j in cofinite, max 1 (16 * (|Cφ| + ‖Ic‖)) ≤ |a j| :=
    (tendsto_atTop.1 ha) _
  filter_upwards [hsmall, hbig, hθ] with j hs hb hθj
  have hX : 1 ≤ |a j| := (le_max_left _ _).trans hb
  have h16 : 16 * (|Cφ| + ‖Ic‖) ≤ |a j| := (le_max_right _ _).trans hb
  have hX0 : 0 < |a j| := by linarith
  have hδ := delta_norm_le N (a j) Ic hX
  refine ⟨?_, ?_⟩
  · have e : (θ j + Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic *
          (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ))) - a j =
        (θ j - a j) + Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic *
          (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ)) := by ring
    rw [e]
    have h1 : Cφ / |a j| ≤ 1 / 16 := by
      rw [div_le_iff₀ hX0]
      have := le_abs_self Cφ
      nlinarith [norm_nonneg Ic]
    have h2 : ‖Ic‖ / |a j| ≤ 1 / 16 := by
      rw [div_le_iff₀ hX0]
      nlinarith [abs_nonneg Cφ]
    have hpi := Real.pi_gt_three
    calc _ ≤ ‖θ j - a j‖ + ‖Complex.I * (2 * Complex.I) ^ (-((N + 1 : ℕ) : ℤ)) * Ic *
          (a j : ℂ) ^ (-((N + 1 : ℕ) : ℤ))‖ := norm_add_le _ _
      _ ≤ 1 / 16 + 1 / 16 := add_le_add (hθj.trans h1) (hδ.trans h2)
      _ < Real.pi / 8 := by linarith
  · have hpow : 0 < |a j| ^ (N + 1) := pow_pos hX0 _
    rw [le_div_iff₀ hpow]
    linarith

end
end NlsGge.ThirdConsultation.KSPS031SharpCore
