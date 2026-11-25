import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS021Host
import NlsGge.ThirdConsultation.KSPS.KSPS016Support
import NlsGge.ThirdConsultation.KSPS.KSPS011Support4

                                                                                                                  
                                                                               
                                                                                                             
                                                                                                              
                                             
                                                                                                                    
                                                                                                                              
                                                                                          
                                                                               
                                                                                                                 
                                                                                                                      
                                                                                              
                                                                                                                
                                           
                                                                                                                       
                                                                                                 
                                                                                                         
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS021W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS

/-! ### Pure lemmas -/

theorem Q_lower (α β : ℂ) (hα : ‖α‖ ≤ 1 / 4) (hβ : ‖β‖ ≤ 1 / 4) :
    1 / 2 ≤ ‖(1 - α) * (1 - β) / (1 - α * β)‖ := by
  have h1 : 3 / 4 ≤ ‖1 - α‖ := by
    have := norm_sub_norm_le (1 : ℂ) α
    rw [norm_one] at this
    linarith
  have h2 : 3 / 4 ≤ ‖1 - β‖ := by
    have := norm_sub_norm_le (1 : ℂ) β
    rw [norm_one] at this
    linarith
  have hab : ‖α * β‖ ≤ 1 / 16 := by
    rw [norm_mul]
    have := mul_le_mul hα hβ (norm_nonneg β) (by norm_num)
    linarith
  have h3 : ‖1 - α * β‖ ≤ 17 / 16 := by
    have := norm_sub_le (1 : ℂ) (α * β)
    rw [norm_one] at this
    linarith
  have h4 : 0 < ‖1 - α * β‖ := by
    have := norm_sub_norm_le (1 : ℂ) (α * β)
    rw [norm_one] at this
    linarith
  rw [norm_div, norm_mul, le_div_iff₀ h4]
  have := mul_le_mul h1 h2 (by norm_num) (norm_nonneg _)
  nlinarith

theorem sin_bound_pure (Q s dE G Y sg : ℂ) (hQ : 1 / 2 ≤ ‖Q‖) (hsg : ‖sg‖ = 1)
    (h : dE = 0 - (Q * (2 * Complex.I * s) + Complex.I * sg * G + Y)) :
    ‖s‖ ≤ ‖dE‖ + ‖G‖ + ‖Y‖ := by
  have e : Q * (2 * Complex.I * s) = -(dE + Complex.I * sg * G + Y) := by
    rw [h]; ring
  have hn : ‖Q * (2 * Complex.I * s)‖ = 2 * ‖Q‖ * ‖s‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat]
    ring
  have hb : ‖-(dE + Complex.I * sg * G + Y)‖ ≤ ‖dE‖ + ‖G‖ + ‖Y‖ := by
    rw [norm_neg]
    calc ‖dE + Complex.I * sg * G + Y‖ ≤ ‖dE + Complex.I * sg * G‖ + ‖Y‖ := norm_add_le _ _
      _ ≤ ‖dE‖ + ‖Complex.I * sg * G‖ + ‖Y‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖dE‖ + ‖G‖ + ‖Y‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, hsg]
        ring
  have h2 : 2 * ‖Q‖ * ‖s‖ ≤ ‖dE‖ + ‖G‖ + ‖Y‖ := by
    rw [← hn, e]
    exact hb
  have hs0 := norm_nonneg s
  nlinarith

theorem cos_sub_one_le_sin_sq (ε : ℂ) (hε : ‖ε‖ ≤ 1 / 2) :
    ‖Complex.cos ε - 1‖ ≤ ‖Complex.sin ε‖ ^ 2 := by
  have hεI : ‖ε * Complex.I‖ = ‖ε‖ := by rw [norm_mul, Complex.norm_I, mul_one]
  have hεI' : ‖-(ε * Complex.I)‖ = ‖ε‖ := by rw [norm_neg, hεI]
  have h1 : ‖Complex.exp (ε * Complex.I) - 1‖ ≤ 2 * ‖ε‖ := by
    have h := Complex.norm_exp_sub_one_le (x := ε * Complex.I) (by rw [hεI]; linarith)
    rwa [hεI] at h
  have h2 : ‖Complex.exp (-(ε * Complex.I)) - 1‖ ≤ 2 * ‖ε‖ := by
    have h := Complex.norm_exp_sub_one_le (x := -(ε * Complex.I)) (by rw [hεI']; linarith)
    rwa [hεI'] at h
  have hc : Complex.cos ε - 1 =
      ((Complex.exp (ε * Complex.I) - 1) + (Complex.exp (-(ε * Complex.I)) - 1)) / 2 := by
    linear_combination (1 / 2 : ℂ) * NlsGge.ThirdConsultation.KSPS015W.two_cos_eq ε
  have hc1 : ‖Complex.cos ε - 1‖ ≤ 1 := by
    rw [hc, norm_div, Complex.norm_ofNat]
    have := norm_add_le (Complex.exp (ε * Complex.I) - 1) (Complex.exp (-(ε * Complex.I)) - 1)
    rw [div_le_one (by norm_num)]
    linarith
  have hc2 : 1 ≤ ‖Complex.cos ε + 1‖ := by
    have e : Complex.cos ε + 1 = 2 + (Complex.cos ε - 1) := by ring
    rw [e]
    have := norm_sub_norm_le (2 : ℂ) (-(Complex.cos ε - 1))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_ofNat] at this
    linarith
  have hid : (Complex.cos ε - 1) * (Complex.cos ε + 1) = -(Complex.sin ε ^ 2) := by
    linear_combination (Complex.sin_sq_add_cos_sq ε)
  have hn : ‖Complex.cos ε - 1‖ * ‖Complex.cos ε + 1‖ = ‖Complex.sin ε‖ ^ 2 := by
    rw [← norm_mul, hid, norm_neg, norm_pow]
  have h0 := norm_nonneg (Complex.cos ε - 1)
  nlinarith

theorem cos_int_mul_pi_c (n : ℤ) : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
  have e : ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) = Complex.cos ((n : ℂ) * (Real.pi : ℂ)) := by
    rw [Complex.ofReal_cos]
    push_cast
    ring
  rw [← e, Real.cos_int_mul_pi]
  push_cast
  ring

theorem neg_one_zpow_mul_self (n : ℤ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← mul_zpow]
  norm_num

theorem norm_neg_one_zpow (n : ℤ) : ‖(-1 : ℂ) ^ n‖ = 1 := by
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

theorem shift (θ : ℂ) (n : ℤ) :
    Complex.cos θ = (-1 : ℂ) ^ n * Complex.cos (θ - (n : ℂ) * (Real.pi : ℂ)) ∧
    Complex.sin θ = (-1 : ℂ) ^ n * Complex.sin (θ - (n : ℂ) * (Real.pi : ℂ)) := by
  have hs : Complex.sin ((n : ℂ) * (Real.pi : ℂ)) = 0 := Complex.sin_int_mul_pi n
  have hc := cos_int_mul_pi_c n
  have hsq := neg_one_zpow_mul_self n
  rw [Complex.cos_sub, Complex.sin_sub, hs, hc]
  constructor
  · linear_combination (-Complex.cos θ) * hsq
  · linear_combination (-Complex.sin θ) * hsq

theorem abs_le_w (n : ℤ) : |(n : ℝ)| ≤ indexWeight n := by
  unfold indexWeight
  exact Real.abs_le_sqrt (by nlinarith)

theorem wl2_iff (N : ℕ) (e : ℤ → ℂ) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ) e ↔
      Summable (fun n : ℤ => (indexWeight n ^ (N + 1) * ‖e n‖) ^ 2) := by
  unfold WeightedL2Error
  have hrp : ∀ n : ℤ, indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) * ‖e n‖ ^ 2 =
      (indexWeight n ^ (N + 1) * ‖e n‖) ^ 2 := by
    intro n
    rw [show (2 * ((N + 1 : ℕ) : ℝ)) = ((2 * (N + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  simp_rw [hrp]

theorem wl2_of_eventually (N : ℕ) (e : ℤ → ℂ) (t : ℤ → ℝ) (ht : Summable (fun n => t n ^ 2))
    (h : ∀ᶠ n : ℤ in Filter.cofinite, indexWeight n ^ (N + 1) * ‖e n‖ ≤ t n) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ) e := by
  rw [wl2_iff]
  refine Summable.of_norm_bounded_eventually ht ?_
  filter_upwards [h] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 : 0 ≤ indexWeight n ^ (N + 1) * ‖e n‖ :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _) (norm_nonneg _)
  exact pow_le_pow_left₀ h0 hn 2

theorem eventually_le_of_sq (t : ℤ → ℝ) (ht : Summable (fun n => t n ^ 2)) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℤ in Filter.cofinite, t n ≤ δ := by
  have h := ht.tendsto_cofinite_zero
  have h2 : ∀ᶠ n : ℤ in Filter.cofinite, t n ^ 2 < δ ^ 2 :=
    h.eventually (gt_mem_nhds (by positivity))
  filter_upwards [h2] with n hn
  by_contra hc
  push_neg at hc
  nlinarith

theorem eventually_w_ge (M : ℝ) : ∀ᶠ n : ℤ in Filter.cofinite, M ≤ indexWeight n := by
  filter_upwards [KSPS015W.eventually_natAbs ⌈M⌉₊] with n hn
  have h1 : ((⌈M⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn
  rw [Int.cast_abs] at h1
  push_cast at h1
  linarith [Nat.le_ceil M, abs_le_w n]

theorem tau_pure (N : ℕ) (w X d f1 f2 D1 D2 c1 s : ℝ) (hw : 1 ≤ w) (hwX : w ≤ 2 * X)
    (hd : 0 ≤ d) (hc1 : 0 ≤ c1) (hf1 : w ^ N * f1 ≤ D1) (hf2 : w ^ N * f2 ≤ D2)
    (hs : s ≤ d + (f1 + f2) + 2 * c1 / (2 * X) ^ (N + 1)) :
    w ^ N * s ≤ w ^ (N + 1) * d + D1 + D2 + 2 * c1 * (1 / w) := by
  have hw0 : 0 < w := by linarith
  have hwN : 0 < w ^ N := pow_pos hw0 N
  have h1 : w ^ N * d ≤ w ^ (N + 1) * d :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hw (Nat.le_succ N)) hd
  have hpow : w ^ (N + 1) ≤ (2 * X) ^ (N + 1) := pow_le_pow_left₀ hw0.le hwX _
  have hwN1 : 0 < w ^ (N + 1) := pow_pos hw0 _
  have h2 : w ^ N * (2 * c1 / (2 * X) ^ (N + 1)) ≤ 2 * c1 * (1 / w) := by
    calc w ^ N * (2 * c1 / (2 * X) ^ (N + 1)) ≤ w ^ N * (2 * c1 / w ^ (N + 1)) := by
          gcongr
      _ = 2 * c1 * (1 / w) := by
          rw [pow_succ]
          field_simp
  have h3 := mul_le_mul_of_nonneg_left hs hwN.le
  have e : w ^ N * (d + (f1 + f2) + 2 * c1 / (2 * X) ^ (N + 1)) =
      w ^ N * d + w ^ N * f1 + w ^ N * f2 + w ^ N * (2 * c1 / (2 * X) ^ (N + 1)) := by ring
  rw [e] at h3
  linarith

theorem sq_weight_le (N : ℕ) (hN : 1 ≤ N) (w s t : ℝ) (hw : 1 ≤ w) (hs : 0 ≤ s)
    (hst : w ^ N * s ≤ t) (ht : t ≤ 1) :
    w ^ (N + 1) * s ^ 2 ≤ t := by
  have hw0 : 0 ≤ w := by linarith
  have h0 : 0 ≤ w ^ N * s := mul_nonneg (pow_nonneg hw0 _) hs
  have h1 : w ^ (N + 1) ≤ w ^ (2 * N) := pow_le_pow_right₀ hw (by omega)
  have h2 : w ^ (N + 1) * s ^ 2 ≤ w ^ (2 * N) * s ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg s)
  have h3 : w ^ (2 * N) * s ^ 2 = (w ^ N * s) ^ 2 := by ring
  have h4 : (w ^ N * s) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ h0 hst 2
  have ht0 : 0 ≤ t := le_trans h0 hst
  nlinarith

theorem claim1_pure (N : ℕ) (hN : 1 ≤ N) (w t : ℝ) (hw : 1 ≤ w) (ht : t ≤ 1)
    (Δ c s ε sg : ℂ) (hc : c = sg * Complex.cos ε) (hs : s = sg * Complex.sin ε)
    (hsg : ‖sg‖ = 1) (hε : ‖ε‖ ≤ 1 / 2) (hst : w ^ N * ‖s‖ ≤ t) :
    w ^ (N + 1) * ‖Δ - 2 * sg‖ ≤ w ^ (N + 1) * ‖Δ - 2 * c‖ + 2 * t := by
  have hw0 : 0 ≤ w := by linarith
  have hsn : ‖s‖ = ‖Complex.sin ε‖ := by rw [hs, norm_mul, hsg, one_mul]
  have e : Δ - 2 * sg = (Δ - 2 * c) + 2 * sg * (Complex.cos ε - 1) := by rw [hc]; ring
  have hb : ‖Δ - 2 * sg‖ ≤ ‖Δ - 2 * c‖ + 2 * ‖s‖ ^ 2 := by
    rw [e]
    calc ‖(Δ - 2 * c) + 2 * sg * (Complex.cos ε - 1)‖
        ≤ ‖Δ - 2 * c‖ + ‖2 * sg * (Complex.cos ε - 1)‖ := norm_add_le _ _
      _ = ‖Δ - 2 * c‖ + 2 * ‖Complex.cos ε - 1‖ := by
          rw [norm_mul, norm_mul, hsg, Complex.norm_ofNat]; ring
      _ ≤ ‖Δ - 2 * c‖ + 2 * ‖s‖ ^ 2 := by
          rw [hsn]; gcongr; exact cos_sub_one_le_sin_sq ε hε
  have hsq := sq_weight_le N hN w ‖s‖ t hw (norm_nonneg _) hst ht
  have hwp : 0 ≤ w ^ (N + 1) := pow_nonneg hw0 _
  have := mul_le_mul_of_nonneg_left hb hwp
  nlinarith

theorem Qa_bound (w X S : ℝ) (α β : ℂ) (hw : 0 < w) (hwX : w ≤ 2 * X) (hS : 0 ≤ S)
    (hDinv : ‖(1 - β * α)⁻¹‖ ≤ 2) (hα : ‖α‖ ≤ S / (2 * X)) (hβ : ‖β‖ ≤ S / (2 * X)) :
    ‖(β - α) / (1 - α * β)‖ ≤ 4 * S / w := by
  have hX : 0 < 2 * X := by linarith
  have e : (β - α) / (1 - α * β) = (β - α) * (1 - β * α)⁻¹ := by rw [div_eq_mul_inv, mul_comm α β]
  have hba : ‖β - α‖ ≤ 2 * S / w := by
    have h1 : ‖β - α‖ ≤ S / (2 * X) + S / (2 * X) := (norm_sub_le _ _).trans (add_le_add hβ hα)
    have h2 : S / (2 * X) + S / (2 * X) = 2 * S / (2 * X) := by ring
    have h3 : 2 * S / (2 * X) ≤ 2 * S / w := div_le_div_of_nonneg_left (by linarith) hw hwX
    linarith
  rw [e, norm_mul]
  calc ‖β - α‖ * ‖(1 - β * α)⁻¹‖ ≤ (2 * S / w) * 2 :=
        mul_le_mul hba hDinv (norm_nonneg _) (by positivity)
    _ = 4 * S / w := by ring

theorem z_identity (Δ δ aE s H sg Qa : ℂ) (hsg : sg * sg = 1)
    (hδ : aE = δ - (Qa * (2 * Complex.I * s) + Complex.I * sg * H)) :
    sg * (Δ + δ) / 2 - 1 - Complex.I * H / 2 =
      sg * ((Δ - 2 * sg) + aE + Qa * (2 * Complex.I * s)) / 2 := by
  have e : δ = aE + Qa * (2 * Complex.I * s) + Complex.I * sg * H := by rw [hδ]; ring
  rw [e]
  linear_combination (Complex.I * H / 2 + 1) * hsg

theorem kappa_pure (N : ℕ) (w S d1 t : ℝ) (hw : 1 ≤ w) (hS : 0 ≤ S)
    (Δ' aE Qa s sg : ℂ) (hsg : ‖sg‖ = 1) (hd1 : w ^ (N + 1) * ‖Δ'‖ ≤ d1)
    (hQa : ‖Qa‖ ≤ 4 * S / w) (hst : w ^ N * ‖s‖ ≤ t) :
    w ^ (N + 1) * ‖sg * (Δ' + aE + Qa * (2 * Complex.I * s)) / 2‖ ≤
      (d1 + w ^ (N + 1) * ‖aE‖ + 8 * S * t) / 2 := by
  have hw0 : 0 < w := by linarith
  have hwp : 0 ≤ w ^ (N + 1) := pow_nonneg hw0.le _
  have hn : ‖sg * (Δ' + aE + Qa * (2 * Complex.I * s)) / 2‖ =
      ‖Δ' + aE + Qa * (2 * Complex.I * s)‖ / 2 := by
    rw [norm_div, norm_mul, hsg, one_mul, Complex.norm_ofNat]
  have hb : ‖Δ' + aE + Qa * (2 * Complex.I * s)‖ ≤ ‖Δ'‖ + ‖aE‖ + ‖Qa‖ * (2 * ‖s‖) := by
    calc _ ≤ ‖Δ' + aE‖ + ‖Qa * (2 * Complex.I * s)‖ := norm_add_le _ _
      _ ≤ ‖Δ'‖ + ‖aE‖ + ‖Qa * (2 * Complex.I * s)‖ := by gcongr; exact norm_add_le _ _
      _ = ‖Δ'‖ + ‖aE‖ + ‖Qa‖ * (2 * ‖s‖) := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat]; ring
  have hq : w ^ (N + 1) * (‖Qa‖ * (2 * ‖s‖)) ≤ 8 * S * t := by
    have h1 : w ^ (N + 1) * (‖Qa‖ * (2 * ‖s‖)) ≤ w ^ (N + 1) * (4 * S / w * (2 * ‖s‖)) := by
      gcongr
    have h2 : w ^ (N + 1) * (4 * S / w * (2 * ‖s‖)) = 8 * S * (w ^ N * ‖s‖) := by
      rw [pow_succ]; field_simp; ring
    have h3 : 8 * S * (w ^ N * ‖s‖) ≤ 8 * S * t := mul_le_mul_of_nonneg_left hst (by positivity)
    linarith
  rw [hn]
  have := mul_le_mul_of_nonneg_left hb hwp
  have e : w ^ (N + 1) * (‖Δ'‖ + ‖aE‖ + ‖Qa‖ * (2 * ‖s‖)) =
      w ^ (N + 1) * ‖Δ'‖ + w ^ (N + 1) * ‖aE‖ + w ^ (N + 1) * (‖Qa‖ * (2 * ‖s‖)) := by ring
  rw [e] at this
  have e2 : w ^ (N + 1) * (‖Δ' + aE + Qa * (2 * Complex.I * s)‖ / 2) =
      (w ^ (N + 1) * ‖Δ' + aE + Qa * (2 * Complex.I * s)‖) / 2 := by ring
  rw [e2]
  linarith

theorem claim2_pure (N : ℕ) (hN : 1 ≤ N) (w : ℝ) (hw : 1 ≤ w) (arg H : ℂ) (k h : ℝ)
    (hk : w ^ (N + 1) * ‖arg - 1 - Complex.I * H / 2‖ ≤ k) (hH : w ^ N * ‖H‖ ≤ h)
    (hr : k + h / 2 ≤ 1 / 2) :
    w ^ (N + 1) * ‖2 * Complex.log arg - Complex.I * H‖ ≤ 2 * (k + h / 2) + 2 * k := by
  set z : ℂ := arg - 1 with hz
  have hw0 : 0 < w := by linarith
  have hwN1 : 1 ≤ w ^ N := one_le_pow₀ hw
  have hwNN : w ^ N ≤ w ^ (N + 1) := pow_le_pow_right₀ hw (Nat.le_succ N)
  have hk0 : 0 ≤ k := le_trans (mul_nonneg (pow_nonneg hw0.le _) (norm_nonneg _)) hk
  have hzb : w ^ N * ‖z‖ ≤ k + h / 2 := by
    have h1 : ‖z‖ ≤ ‖z - Complex.I * H / 2‖ + ‖H‖ / 2 := by
      have := norm_add_le (z - Complex.I * H / 2) (Complex.I * H / 2)
      rw [sub_add_cancel] at this
      have e : ‖Complex.I * H / 2‖ = ‖H‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_ofNat]
      linarith
    have h2 : w ^ N * ‖z - Complex.I * H / 2‖ ≤ k :=
      le_trans (mul_le_mul_of_nonneg_right hwNN (norm_nonneg _)) hk
    have h3 := mul_le_mul_of_nonneg_left h1 (pow_nonneg hw0.le N)
    have e : w ^ N * (‖z - Complex.I * H / 2‖ + ‖H‖ / 2) =
        w ^ N * ‖z - Complex.I * H / 2‖ + (w ^ N * ‖H‖) / 2 := by ring
    rw [e] at h3
    linarith
  have hz2 : ‖z‖ ≤ 1 / 2 := by
    have : ‖z‖ ≤ w ^ N * ‖z‖ := le_mul_of_one_le_left (norm_nonneg _) hwN1
    linarith
  have hlog : ‖Complex.log (1 + z) - z‖ ≤ ‖z‖ ^ 2 := by
    have h1 := Complex.norm_log_one_add_sub_self_le (z := z) (by linarith)
    have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    have h3 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    linarith
  have hsq := sq_weight_le N hN w ‖z‖ (k + h / 2) hw (norm_nonneg _) hzb (by linarith)
  have e : 2 * Complex.log arg - Complex.I * H =
      2 * (Complex.log (1 + z) - z) + 2 * (z - Complex.I * H / 2) := by
    rw [hz]; ring_nf
  have hb : ‖2 * Complex.log arg - Complex.I * H‖ ≤
      2 * ‖z‖ ^ 2 + 2 * ‖z - Complex.I * H / 2‖ := by
    rw [e]
    calc _ ≤ ‖2 * (Complex.log (1 + z) - z)‖ + ‖2 * (z - Complex.I * H / 2)‖ := norm_add_le _ _
      _ = 2 * ‖Complex.log (1 + z) - z‖ + 2 * ‖z - Complex.I * H / 2‖ := by
          rw [norm_mul, norm_mul, Complex.norm_ofNat]
      _ ≤ 2 * ‖z‖ ^ 2 + 2 * ‖z - Complex.I * H / 2‖ := by gcongr
  have hwp : 0 ≤ w ^ (N + 1) := pow_nonneg hw0.le _
  have := mul_le_mul_of_nonneg_left hb hwp
  have e2 : w ^ (N + 1) * (2 * ‖z‖ ^ 2 + 2 * ‖z - Complex.I * H / 2‖) =
      2 * (w ^ (N + 1) * ‖z‖ ^ 2) + 2 * (w ^ (N + 1) * ‖z - Complex.I * H / 2‖) := by ring
  rw [e2] at this
  linarith

/-! ### Spectral facts at the Dirichlet root -/

theorem dirichletNumerator_mu {N : ℕ} (φ : SobolevC N) (n : ℤ) :
    KSPSWKB.dirichletNumerator φ (mu φ n) = 0 := by
  have h := muSeq_root38 (toPotPair φ) n
  rw [dirichletChar_eq, div_eq_zero_iff] at h
  rcases h with h | h
  · unfold KSPSWKB.dirichletNumerator mu
    linear_combination h
  · exact absurd h dirichlet_denominator_ne_zero38

theorem phase_small {N : ℕ} (φ : SobolevC N) (lam : ℂ) (n : ℤ) (w a : ℝ) (hw : 0 < w)
    (hlam1 : 1 ≤ ‖lam‖) (hwX : w ≤ 2 * ‖lam‖)
    (hd : ‖lam - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / w) :
    ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ lam - (n : ℂ) * (Real.pi : ℂ)‖ ≤
      (a + ∑ k ∈ Finset.Icc 1 N, ‖integralRiccatiLeft φ k‖) / w := by
  rw [KSPS015W.wkbPhase_eq]
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      ‖((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k‖ ≤ ‖integralRiccatiLeft φ k‖ / w := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    rw [norm_mul, norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one,
      inv_mul_eq_div]
    have hp : w ≤ (2 * ‖lam‖) ^ k := hwX.trans (le_self_pow₀ (by linarith) (by omega))
    exact div_le_div_of_nonneg_left (norm_nonneg _) hw hp
  have hsum : ‖Complex.I * ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k‖ ≤
      (∑ k ∈ Finset.Icc 1 N, ‖integralRiccatiLeft φ k‖) / w := by
    rw [norm_mul, Complex.norm_I, one_mul, Finset.sum_div]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have e : lam + Complex.I * ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k - (n : ℂ) * (Real.pi : ℂ) =
      (lam - (n : ℂ) * (Real.pi : ℂ)) + Complex.I * ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k := by ring
  rw [e, add_div]
  exact (norm_add_le _ _).trans (add_le_add hd hsum)

/-! ### Rough localization from the KSPS-019 head (an explicit hypothesis of exactly its landed type) -/

theorem mu_localization_of
    (h19 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          ‖mu φ n-(n:ℂ)*Real.pi‖ +
          ‖criticalEigenvalue φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ))
    {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  have hmu : ∀ n : ℤ, mu φ' n = mu φ n := by
    intro n
    unfold mu
    rw [← hφ']
    rfl
  obtain ⟨C, N0, hC, h⟩ := h19 (|sobolevNorm 1 φ'| + 1) (by positivity)
  have h' := h φ' (by linarith [le_abs_self (sobolevNorm 1 φ')])
  set F : Finset ℤ := Finset.Icc (-((N0 + 1 : ℕ) : ℤ)) ((N0 + 1 : ℕ) : ℤ) with hF
  have hsum0 : 0 ≤ ∑ m ∈ F, ‖mu φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (KSPS015W.one_le_w m)))
  refine ⟨2 * C + ∑ m ∈ F, ‖mu φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m,
    add_nonneg (by linarith) hsum0, fun n => ?_⟩
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (KSPS015W.one_le_w n)
  by_cases hn : n ∈ F
  · have h1 : ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ * indexWeight n ≤
        2 * C + ∑ m ∈ F, ‖mu φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m := by
      have := Finset.single_le_sum
        (f := fun m => ‖mu φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m)
        (fun m _ => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (KSPS015W.one_le_w m))) hn
      linarith
    rw [le_div_iff₀ hw0]
    exact h1
  · rw [hF, Finset.mem_Icc] at hn
    have hlt : ((N0 + 1 : ℕ) : ℤ) < |n| := by
      by_contra hc
      push_neg at hc
      exact hn ⟨by linarith [neg_abs_le n], by linarith [le_abs_self n]⟩
    have hnat : N0 + 1 < n.natAbs := by
      have : ((N0 + 1 : ℕ) : ℤ) < (n.natAbs : ℤ) := by rw [Int.natCast_natAbs]; exact hlt
      exact_mod_cast this
    have hnR : ((n.natAbs : ℕ) : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
    have hb := h' n (by omega)
    rw [hmu n, hnR] at hb
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℕ) : ℝ) ≤ ((n.natAbs : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n.natAbs)
      rw [hnR] at this
      simpa using this
    have hpos : 0 < |(n : ℝ)| := by linarith
    have hw2 := KSPS015W.w_le_two n hn1
    have hc0 : 0 ≤ ‖criticalEigenvalue φ' n - (n : ℂ) * (Real.pi : ℂ)‖ := norm_nonneg _
    have h2 : ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ C / |(n : ℝ)| := by linarith
    have h3 : C / |(n : ℝ)| ≤ 2 * C / indexWeight n := by
      rw [div_le_div_iff₀ hpos hw0]
      nlinarith
    have h4 : 2 * C / indexWeight n ≤
        (2 * C + ∑ m ∈ F, ‖mu φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m) / indexWeight n :=
      div_le_div_of_nonneg_right (by linarith) hw0.le
    linarith

/-! ### Bounding sequences (literal real abbreviations) -/

def Jsum {N : ℕ} (φ : SobolevC N) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, ‖integralRiccatiLeft φ k‖

def tau (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  indexWeight n ^ (N + 1) * ‖KSPSWKB.dirichletError N φ (mu φ) n‖ +
    ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
    ‖physicalFourier (iteratedDerivative N φ.2) n‖ +
    2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)

def dE1 (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  indexWeight n ^ (N + 1) *
    ‖discriminant φ (mu φ n) -
      2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n))‖ + 2 * tau N φ n

def kappa (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  (dE1 N φ n + indexWeight n ^ (N + 1) * ‖KSPSWKB.antitraceError N φ (mu φ) n‖ +
    8 * KSPS016W.Sb φ * tau N φ n) / 2

def rho (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  kappa N φ n + (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
    ‖physicalFourier (iteratedDerivative N φ.2) n‖) / 2

/-! ### The tail estimate at one index -/

/-- The improved sine estimate and the phase localization at the Dirichlet root (tail). -/
theorem sine_tail (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h3 : (1 : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n) :
    indexWeight n ^ N * ‖Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n))‖ ≤ tau N φ n ∧
    ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2 := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h2
  have hX0 : 0 < ‖mu φ n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (mu φ n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨hDinv, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (mu φ n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq : KSPS016W.Sb φ / (2 * ‖mu φ n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hQ := Q_lower (KSPSWKB.alpha φ (mu φ n) 0) (KSPSWKB.beta φ (mu φ n) 0)
    (hα.trans hq) (hβ.trans hq)
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h3
    rw [Int.cast_abs] at this
    simpa using this
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  -- (1) improved sine estimate
  have hsgn1 : ‖(-1 : ℂ) ^ (n + 1)‖ = 1 := norm_neg_one_zpow (n + 1)
  have hs1 := sin_bound_pure
    ((1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
      (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0))
    (Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)))
    (KSPSWKB.dirichletError N φ (mu φ) n)
    (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n)
    (2 * (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * mu φ n) ^ (N + 1) * integralRiccatiLeft φ (N + 1))
    ((-1 : ℂ) ^ (n + 1)) hQ hsgn1
    (by unfold KSPSWKB.dirichletError; rw [dirichletNumerator_mu φ n])
  have hY : ‖2 * (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * mu φ n) ^ (N + 1) * integralRiccatiLeft φ (N + 1)‖ =
      2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖mu φ n‖) ^ (N + 1) := by
    rw [norm_mul, norm_div, norm_mul, hsgn1, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_ofNat]
    ring
  have hG : ‖physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n‖ ≤
      ‖physicalFourier (toPotPair φ).1 (-n)‖ + ‖physicalFourier (toPotPair φ).2 n‖ := norm_add_le _ _
  rw [hY] at hs1
  have hst : indexWeight n ^ N * ‖Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n))‖ ≤
      tau N φ n := by
    unfold tau
    exact tau_pure N (indexWeight n) ‖mu φ n‖ _ _ _ _ _ _ _ hw1 hwX (norm_nonneg _) (norm_nonneg _)
      hF1 hF2 (by linarith)
  -- (2) the discriminant at mu
  have hε : ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2 := by
    have := phase_small φ (mu φ n) n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    linarith
  exact ⟨hst, hε⟩

theorem tail_core (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h3 : (1 : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tau N φ n ≤ 1) (h6 : rho N φ n ≤ 1 / 2) :
    indexWeight n ^ (N + 1) * ‖discriminant φ (mu φ n) - 2 * (-1 : ℂ) ^ n‖ ≤ dE1 N φ n ∧
    indexWeight n ^ (N + 1) * ‖KSPSWKB.normingError N φ n‖ ≤
      2 * rho N φ n + 2 * kappa N φ n := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha (mu φ) hxi n h2
  have hX0 : 0 < ‖mu φ n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (mu φ n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨hDinv, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (mu φ n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq : KSPS016W.Sb φ / (2 * ‖mu φ n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hQ := Q_lower (KSPSWKB.alpha φ (mu φ n) 0) (KSPSWKB.beta φ (mu φ n) 0)
    (hα.trans hq) (hβ.trans hq)
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h3
    rw [Int.cast_abs] at this
    simpa using this
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  -- (1) improved sine estimate
  have hsgn1 : ‖(-1 : ℂ) ^ (n + 1)‖ = 1 := norm_neg_one_zpow (n + 1)
  have hs1 := sin_bound_pure
    ((1 - KSPSWKB.alpha φ (mu φ n) 0) * (1 - KSPSWKB.beta φ (mu φ n) 0) /
      (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0))
    (Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)))
    (KSPSWKB.dirichletError N φ (mu φ) n)
    (physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n)
    (2 * (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * mu φ n) ^ (N + 1) * integralRiccatiLeft φ (N + 1))
    ((-1 : ℂ) ^ (n + 1)) hQ hsgn1
    (by unfold KSPSWKB.dirichletError; rw [dirichletNumerator_mu φ n])
  have hY : ‖2 * (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * mu φ n) ^ (N + 1) * integralRiccatiLeft φ (N + 1)‖ =
      2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖mu φ n‖) ^ (N + 1) := by
    rw [norm_mul, norm_div, norm_mul, hsgn1, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_ofNat]
    ring
  have hG : ‖physicalFourier (toPotPair φ).1 (-n) + physicalFourier (toPotPair φ).2 n‖ ≤
      ‖physicalFourier (toPotPair φ).1 (-n)‖ + ‖physicalFourier (toPotPair φ).2 n‖ := norm_add_le _ _
  rw [hY] at hs1
  have hst : indexWeight n ^ N * ‖Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n))‖ ≤
      tau N φ n := by
    unfold tau
    exact tau_pure N (indexWeight n) ‖mu φ n‖ _ _ _ _ _ _ _ hw1 hwX (norm_nonneg _) (norm_nonneg _)
      hF1 hF2 (by linarith)
  -- (2) the discriminant at mu
  have hε : ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2 := by
    have := phase_small φ (mu φ n) n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    linarith
  obtain ⟨hcs, hsn⟩ := shift (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)) n
  have hc1 := claim1_pure N hN (indexWeight n) (tau N φ n) hw1 h5 (discriminant φ (mu φ n))
    (Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)))
    (Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)))
    (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n) - (n : ℂ) * (Real.pi : ℂ))
    ((-1 : ℂ) ^ n) hcs hsn (norm_neg_one_zpow n) hε hst
  have hb1 : indexWeight n ^ (N + 1) * ‖discriminant φ (mu φ n) - 2 * (-1 : ℂ) ^ n‖ ≤ dE1 N φ n := by
    unfold dE1
    exact hc1
  refine ⟨hb1, ?_⟩
  -- (3) the norming constant
  have hQa := Qa_bound (indexWeight n) ‖mu φ n‖ (KSPS016W.Sb φ) (KSPSWKB.alpha φ (mu φ n) 0)
    (KSPSWKB.beta φ (mu φ n) 0) hw0 hwX hS0 hDinv hα hβ
  have hz := z_identity (discriminant φ (mu φ n)) (KSPSWKB.antitrace φ (mu φ n))
    (KSPSWKB.antitraceError N φ (mu φ) n)
    (Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n)))
    (physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n)
    ((-1 : ℂ) ^ n)
    ((KSPSWKB.beta φ (mu φ n) 0 - KSPSWKB.alpha φ (mu φ n) 0) /
      (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0))
    (neg_one_zpow_mul_self n) (by unfold KSPSWKB.antitraceError; rfl)
  have hk := kappa_pure N (indexWeight n) (KSPS016W.Sb φ) (dE1 N φ n) (tau N φ n) hw1 hS0
    (discriminant φ (mu φ n) - 2 * (-1 : ℂ) ^ n) (KSPSWKB.antitraceError N φ (mu φ) n)
    ((KSPSWKB.beta φ (mu φ n) 0 - KSPSWKB.alpha φ (mu φ n) 0) /
      (1 - KSPSWKB.alpha φ (mu φ n) 0 * KSPSWKB.beta φ (mu φ n) 0))
    (Complex.sin (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (mu φ n))) ((-1 : ℂ) ^ n)
    (norm_neg_one_zpow n) hb1 hQa hst
  rw [← hz] at hk
  have hH : indexWeight n ^ N *
      ‖physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n‖ ≤
      ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
        ‖physicalFourier (iteratedDerivative N φ.2) n‖ := by
    have := norm_sub_le (physicalFourier (toPotPair φ).1 (-n)) (physicalFourier (toPotPair φ).2 n)
    have h8 := mul_le_mul_of_nonneg_left this (pow_nonneg hw0.le N)
    rw [mul_add] at h8
    linarith
  have hr : kappa N φ n + (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ +
        ‖physicalFourier (iteratedDerivative N φ.2) n‖) / 2 ≤ 1 / 2 := by
    unfold rho at h6
    exact h6
  have hc2 := claim2_pure N hN (indexWeight n) hw1
    ((-1 : ℂ) ^ n * (discriminant φ (mu φ n) + KSPSWKB.antitrace φ (mu φ n)) / 2)
    (physicalFourier (toPotPair φ).1 (-n) - physicalFourier (toPotPair φ).2 n)
    (kappa N φ n) _ (by unfold kappa; exact hk) hH hr
  unfold KSPSWKB.normingError KSPSWKB.normingLog
  unfold rho
  exact hc2

/-! ### The weighted estimates (conditional on the KSPS-015/016 head conclusions at xi = mu) -/

theorem dirichlet_boundary_asymptotics_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖mu φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h15 : WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => discriminant φ (mu φ n) - 2 * Complex.cos (wkbPhase φ (mu φ n))))
    (h16 : AntiTraceDirichletWKB N φ (mu φ)) :
    DirichletBoundaryWeightedL2 N φ := by
  obtain ⟨hA, hD⟩ := h16
  rw [wl2_iff] at h15 hA hD
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hI : Summable (fun n : ℤ => (2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)) ^ 2) :=
    KSPS015W.sq_summable_mul_left _ KSPS016W.sq_summable_inv_w
  have hτ : Summable (fun n : ℤ => tau N φ n ^ 2) := by
    unfold tau
    exact KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add hD hF1) hF2) hI
  have hd1 : Summable (fun n : ℤ => dE1 N φ n ^ 2) := by
    unfold dE1
    exact KSPS015W.sq_summable_add h15 (KSPS015W.sq_summable_mul_left 2 hτ)
  have hκ : Summable (fun n : ℤ => kappa N φ n ^ 2) := by
    have h := KSPS015W.sq_summable_mul_left (1 / 2)
      (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add hd1 hA)
        (KSPS015W.sq_summable_mul_left (8 * KSPS016W.Sb φ) hτ))
    refine h.congr (fun n => ?_)
    unfold kappa
    ring
  have hρ : Summable (fun n : ℤ => rho N φ n ^ 2) := by
    have h := KSPS015W.sq_summable_add hκ
      (KSPS015W.sq_summable_mul_left (1 / 2) (KSPS015W.sq_summable_add hF1 hF2))
    refine h.congr (fun n => ?_)
    unfold rho
    ring
  have hfin : Summable (fun n : ℤ => (2 * rho N φ n + 2 * kappa N φ n) ^ 2) :=
    KSPS015W.sq_summable_add (KSPS015W.sq_summable_mul_left 2 hρ) (KSPS015W.sq_summable_mul_left 2 hκ)
  have e1 := KSPS015W.eventually_natAbs
    (⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1)
  have e2 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tau N φ) hτ 1 one_pos
  have e6 := eventually_le_of_sq (rho N φ) hρ (1 / 2) (by norm_num)
  refine ⟨wl2_of_eventually N _ (dE1 N φ) hd1 ?_, wl2_of_eventually N _ _ hfin ?_⟩
  · filter_upwards [e1, e2, e3, e4, e5, e6] with n g1 g2 g3 g4 g5 g6
    exact (tail_core N hN φ a ha hxi n g1 g2 (by exact_mod_cast g3) g4 g5 g6).1
  · filter_upwards [e1, e2, e3, e4, e5, e6] with n g1 g2 g3 g4 g5 g6
    exact (tail_core N hN φ a ha hxi n g1 g2 (by exact_mod_cast g3) g4 g5 g6).2

end
end NlsGge.ThirdConsultation.KSPS021W
