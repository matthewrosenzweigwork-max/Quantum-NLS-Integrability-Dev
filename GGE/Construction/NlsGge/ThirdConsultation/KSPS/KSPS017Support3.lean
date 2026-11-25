import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Support2
import NlsGge.ThirdConsultation.KSPS.KSPS015Support

                                                                                                                    
                                                                                                                   
                                                                                                                   
                                                                                                    
                                                                                             
                                                                                                                 
                                                                                                                   
                                                                                                           
                                                                                                             
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

theorem scale_le (N : ℕ) {w X B : ℝ} (hw : 0 < w) (hwX : w ≤ 2 * X) (hB : 0 ≤ B) {T : ℂ}
    (hT : ‖T‖ ≤ ((2 * X) ^ N)⁻¹ * B) : w ^ (N + 1) * ‖T‖ ≤ w * B := by
  have h2X : 0 < 2 * X := lt_of_lt_of_le hw hwX
  have hr : (w / (2 * X)) ^ N ≤ 1 := pow_le_one₀ (div_nonneg hw.le h2X.le) ((div_le_one h2X).2 hwX)
  calc w ^ (N + 1) * ‖T‖ ≤ w ^ (N + 1) * (((2 * X) ^ N)⁻¹ * B) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = w * ((w / (2 * X)) ^ N * B) := by rw [div_pow, pow_succ]; ring
    _ ≤ w * (1 * B) := by gcongr
    _ = w * B := by ring

theorem bound_T1 (N : ℕ) (w X S K P : ℝ) (d a b a' b' e x : ℂ)
    (hw : 0 < w) (hX1 : 1 ≤ X) (hS : 0 ≤ S) (hK : 0 ≤ K) (hP : 0 ≤ P) (hdi : ‖d⁻¹‖ ≤ 2)
    (ha : ‖a‖ ≤ S / (2 * X)) (hb : ‖b‖ ≤ S / (2 * X)) (ha' : ‖a'‖ ≤ K / X ^ 2) (hb' : ‖b'‖ ≤ K / X ^ 2)
    (he : ‖e‖ = ((2 * X) ^ N)⁻¹) (hx : ‖x‖ ≤ P / w) :
    ‖-(-(b' * a + b * a')) / d ^ 2 * (e * x)‖ ≤ ((2 * X) ^ N)⁻¹ * (4 * K * S * (P / w)) := by
  have hX0 : 0 < X := by linarith
  have hen : 0 ≤ ((2 * X) ^ N)⁻¹ := by positivity
  have hX2 : 1 ≤ X ^ 2 := by nlinarith
  have hk1 : K / X ^ 2 ≤ K := div_le_self hK hX2
  have hs1 : S / (2 * X) ≤ S / 2 := div_le_div_of_nonneg_left hS (by norm_num) (by linarith)
  have hd' : ‖b' * a + b * a'‖ ≤ K * S := by
    have h1 : ‖b' * a‖ ≤ K * (S / 2) := by
      rw [norm_mul]; exact mul_le_mul (hb'.trans hk1) (ha.trans hs1) (norm_nonneg _) hK
    have h2 : ‖b * a'‖ ≤ S / 2 * K := by
      rw [norm_mul]; exact mul_le_mul (hb.trans hs1) (ha'.trans hk1) (norm_nonneg _) (by linarith)
    have := norm_add_le (b' * a) (b * a')
    linarith
  have h4 : ‖d⁻¹‖ ^ 2 ≤ 4 := by
    calc ‖d⁻¹‖ ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hdi 2
      _ = 4 := by norm_num
  have hq : ‖b' * a + b * a'‖ / ‖d‖ ^ 2 ≤ K * S * 4 := by
    rw [div_eq_mul_one_div, one_div, ← inv_pow, ← norm_inv]
    exact mul_le_mul hd' h4 (sq_nonneg _) (by positivity)
  rw [norm_mul, norm_div, norm_neg, norm_neg, norm_mul, norm_pow, he]
  calc ‖b' * a + b * a'‖ / ‖d‖ ^ 2 * (((2 * X) ^ N)⁻¹ * ‖x‖)
      ≤ K * S * 4 * (((2 * X) ^ N)⁻¹ * (P / w)) :=
        mul_le_mul hq (mul_le_mul_of_nonneg_left hx hen) (by positivity) (by positivity)
    _ = ((2 * X) ^ N)⁻¹ * (4 * K * S * (P / w)) := by ring

theorem bound_T2 (N : ℕ) (w X P : ℝ) (z d e x : ℂ)
    (hw : 0 < w) (hX1 : 1 ≤ X) (hP : 0 ≤ P) (hz : ‖z‖ = X) (hdi : ‖d⁻¹‖ ≤ 2)
    (he : ‖e‖ = ((2 * X) ^ N)⁻¹) (hx : ‖x‖ ≤ P / w) :
    ‖d⁻¹ * (-((N : ℂ) * z⁻¹ * e) * x)‖ ≤ ((2 * X) ^ N)⁻¹ * (2 * N * X⁻¹ * (P / w)) := by
  have hX0 : 0 < X := by linarith
  rw [norm_mul, norm_mul, norm_neg, norm_mul, norm_mul, norm_inv z, hz, he, Complex.norm_natCast]
  calc ‖d⁻¹‖ * ((N : ℝ) * X⁻¹ * ((2 * X) ^ N)⁻¹ * ‖x‖)
      ≤ 2 * ((N : ℝ) * X⁻¹ * ((2 * X) ^ N)⁻¹ * (P / w)) :=
        mul_le_mul hdi (mul_le_mul_of_nonneg_left hx (by positivity)) (by positivity) (by norm_num)
    _ = ((2 * X) ^ N)⁻¹ * (2 * N * X⁻¹ * (P / w)) := by ring

theorem bound_T3 (N : ℕ) (X S K U V FU FL : ℝ) (d a b a' b' e r10 r01 p10 p01 : ℂ)
    (hX1 : 1 ≤ X) (hS : 0 ≤ S) (hK : 0 ≤ K) (hdi : ‖d⁻¹‖ ≤ 2)
    (ha : ‖a‖ ≤ S / (2 * X)) (hb : ‖b‖ ≤ S / (2 * X)) (ha' : ‖a'‖ ≤ K / X ^ 2) (hb' : ‖b'‖ ≤ K / X ^ 2)
    (he : ‖e‖ = ((2 * X) ^ N)⁻¹) (hr10 : ‖r10‖ ≤ U) (hr01 : ‖r01‖ ≤ V)
    (hp10 : ‖p10‖ ≤ FU) (hp01 : ‖p01‖ ≤ FL) :
    ‖d⁻¹ * e * (-(a' * r10 + a * p10) - (b' * r01 + b * p01))‖ ≤ ((2 * X) ^ N)⁻¹ *
      (2 * (K / X ^ 2 * U + S / (2 * X) * FU + K / X ^ 2 * V + S / (2 * X) * FL)) := by
  have hX0 : 0 < X := by linarith
  have hen : 0 ≤ ((2 * X) ^ N)⁻¹ := by positivity
  have hSX : 0 ≤ S / (2 * X) := by positivity
  have hKX : 0 ≤ K / X ^ 2 := by positivity
  have hQ : ‖-(a' * r10 + a * p10) - (b' * r01 + b * p01)‖ ≤
      K / X ^ 2 * U + S / (2 * X) * FU + K / X ^ 2 * V + S / (2 * X) * FL := by
    have e1 : ‖a' * r10‖ ≤ K / X ^ 2 * U := by rw [norm_mul]; exact mul_le_mul ha' hr10 (norm_nonneg _) hKX
    have e2 : ‖a * p10‖ ≤ S / (2 * X) * FU := by rw [norm_mul]; exact mul_le_mul ha hp10 (norm_nonneg _) hSX
    have e3 : ‖b' * r01‖ ≤ K / X ^ 2 * V := by rw [norm_mul]; exact mul_le_mul hb' hr01 (norm_nonneg _) hKX
    have e4 : ‖b * p01‖ ≤ S / (2 * X) * FL := by rw [norm_mul]; exact mul_le_mul hb hp01 (norm_nonneg _) hSX
    have f1 := norm_sub_le (-(a' * r10 + a * p10)) (b' * r01 + b * p01)
    have f2 := norm_add_le (a' * r10) (a * p10)
    have f3 := norm_add_le (b' * r01) (b * p01)
    rw [norm_neg] at f1
    linarith
  have hQ0 : 0 ≤ K / X ^ 2 * U + S / (2 * X) * FU + K / X ^ 2 * V + S / (2 * X) * FL :=
    le_trans (norm_nonneg _) hQ
  rw [norm_mul, norm_mul, he]
  calc ‖d⁻¹‖ * ((2 * X) ^ N)⁻¹ * ‖-(a' * r10 + a * p10) - (b' * r01 + b * p01)‖
      ≤ 2 * ((2 * X) ^ N)⁻¹ * (K / X ^ 2 * U + S / (2 * X) * FU + K / X ^ 2 * V + S / (2 * X) * FL) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hdi hen) hQ (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem bound_T4 (N : ℕ) (w X S G I0 : ℝ) (d a b e pp M : ℂ)
    (hX1 : 1 ≤ X) (hS : 0 ≤ S) (hd : d = 1 - b * a) (hd0 : d ≠ 0) (hdi : ‖d⁻¹‖ ≤ 2)
    (ha : ‖a‖ ≤ S / (2 * X)) (hb : ‖b‖ ≤ S / (2 * X))
    (he : ‖e‖ = ((2 * X) ^ N)⁻¹) (hM : ‖M‖ ≤ I0 / X) (hpp : ‖pp - M‖ ≤ G / w) :
    ‖(d⁻¹ - 1) * e * pp‖ ≤ ((2 * X) ^ N)⁻¹ * (2 * (S / (2 * X)) ^ 2 * (I0 / X + G / w)) := by
  have hX0 : 0 < X := by linarith
  have hen : 0 ≤ ((2 * X) ^ N)⁻¹ := by positivity
  have hSX : 0 ≤ S / (2 * X) := by positivity
  have hdd : d⁻¹ - 1 = d⁻¹ * (b * a) := by
    have h1 : d * d⁻¹ = 1 := mul_inv_cancel₀ hd0
    linear_combination h1 + (-d⁻¹) * hd
  have hba : ‖b * a‖ ≤ (S / (2 * X)) ^ 2 := by
    rw [norm_mul, sq]; exact mul_le_mul hb ha (norm_nonneg _) hSX
  have hppn : ‖pp‖ ≤ I0 / X + G / w := by
    have := norm_add_le (pp - M) M
    rw [sub_add_cancel] at this
    linarith
  rw [hdd, norm_mul, norm_mul, norm_mul, he]
  calc ‖d⁻¹‖ * ‖b * a‖ * ((2 * X) ^ N)⁻¹ * ‖pp‖
      ≤ 2 * (S / (2 * X)) ^ 2 * ((2 * X) ^ N)⁻¹ * (I0 / X + G / w) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hdi hba (norm_nonneg _) (by norm_num)) hen)
          hppn (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem scaled_T2 (N : ℕ) (w X P : ℝ) (hw : 0 < w) (hX1 : 1 ≤ X) (hP : 0 ≤ P) :
    w * (2 * N * X⁻¹ * (P / w)) ≤ 2 * N * P := by
  have hX0 : 0 < X := by linarith
  have e1 : w * (2 * N * X⁻¹ * (P / w)) = 2 * N * P * X⁻¹ := by field_simp
  rw [e1]
  have hXi : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hX1
  have h0 : 0 ≤ 2 * (N : ℝ) * P := by positivity
  calc 2 * N * P * X⁻¹ ≤ 2 * N * P * 1 := mul_le_mul_of_nonneg_left hXi h0
    _ = 2 * N * P := by ring

theorem scaled_T3 (w X S K U V FU FL : ℝ) (hw : 0 < w) (hX1 : 1 ≤ X) (hwX : w ≤ 2 * X)
    (hS : 0 ≤ S) (hK : 0 ≤ K) (hU : 0 ≤ U) (hV : 0 ≤ V) (hFU : 0 ≤ FU) (hFL : 0 ≤ FL) :
    w * (2 * (K / X ^ 2 * U + S / (2 * X) * FU + K / X ^ 2 * V + S / (2 * X) * FL)) ≤
      4 * K * U + 2 * S * FU + 4 * K * V + 2 * S * FL := by
  have hX0 : 0 < X := by linarith
  have h2X : 0 < 2 * X := by linarith
  have h1 : w / (2 * X) ≤ 1 := (div_le_one h2X).2 hwX
  have h1' : 0 ≤ w / (2 * X) := by positivity
  have r1 : w * (K / X ^ 2) ≤ 2 * K := by
    have e1 : w * (K / X ^ 2) = (w / (2 * X)) * (2 * K / X) := by field_simp
    rw [e1]
    have h2 : 2 * K / X ≤ 2 * K := div_le_self (by positivity) hX1
    calc w / (2 * X) * (2 * K / X) ≤ 1 * (2 * K) := mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ = 2 * K := by ring
  have r2 : w * (S / (2 * X)) ≤ S := by
    have e1 : w * (S / (2 * X)) = (w / (2 * X)) * S := by field_simp
    rw [e1]
    calc w / (2 * X) * S ≤ 1 * S := mul_le_mul_of_nonneg_right h1 hS
      _ = S := by ring
  have e2 : w * (2 * (K / X ^ 2 * U + S / (2 * X) * FU + K / X ^ 2 * V + S / (2 * X) * FL)) =
      2 * ((w * (K / X ^ 2)) * U + (w * (S / (2 * X))) * FU + (w * (K / X ^ 2)) * V +
        (w * (S / (2 * X))) * FL) := by ring
  rw [e2]
  have k1 := mul_le_mul_of_nonneg_right r1 hU
  have k2 := mul_le_mul_of_nonneg_right r2 hFU
  have k3 := mul_le_mul_of_nonneg_right r1 hV
  have k4 := mul_le_mul_of_nonneg_right r2 hFL
  linarith

theorem scaled_T4 (w X S G I0 : ℝ) (hw : 0 < w) (hX1 : 1 ≤ X) (hwX : w ≤ 2 * X)
    (hS : 0 ≤ S) (hG : 0 ≤ G) (hI0 : 0 ≤ I0) :
    w * (2 * (S / (2 * X)) ^ 2 * (I0 / X + G / w)) ≤ 2 * S ^ 2 * (I0 / w) + S ^ 2 * G := by
  have hX0 : 0 < X := by linarith
  have h2X : 0 < 2 * X := by linarith
  have e1 : w * (2 * (S / (2 * X)) ^ 2 * (I0 / X + G / w)) =
      S ^ 2 * (w / (2 * X)) * (1 / X) * (I0 / X) + S ^ 2 * (1 / (2 * X ^ 2)) * G := by
    field_simp
  rw [e1]
  have h1 : w / (2 * X) ≤ 1 := (div_le_one h2X).2 hwX
  have h2 : 1 / X ≤ 1 := by rw [div_le_one hX0]; exact hX1
  have h3 : I0 / X ≤ 2 * (I0 / w) := by
    rw [div_le_iff₀ hX0]
    have e2 : 2 * (I0 / w) * X = I0 * (2 * X / w) := by field_simp
    rw [e2]
    have h5 : 1 ≤ 2 * X / w := by rw [le_div_iff₀ hw]; linarith
    exact le_mul_of_one_le_right hI0 h5
  have h4 : 1 / (2 * X ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have k1 : S ^ 2 * (w / (2 * X)) * (1 / X) * (I0 / X) ≤ S ^ 2 * 1 * 1 * (2 * (I0 / w)) := by
    have a1 : 0 ≤ w / (2 * X) := by positivity
    have a2 : 0 ≤ 1 / X := by positivity
    have a3 : 0 ≤ I0 / X := by positivity
    have m1 : S ^ 2 * (w / (2 * X)) ≤ S ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 hS2
    have m2 : S ^ 2 * (w / (2 * X)) * (1 / X) ≤ S ^ 2 * 1 * 1 :=
      mul_le_mul m1 h2 a2 (by positivity)
    exact mul_le_mul m2 h3 a3 (by positivity)
  have k2 : S ^ 2 * (1 / (2 * X ^ 2)) * G ≤ S ^ 2 * 1 * G :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hS2) hG
  linarith

/-- The pure numerical estimate behind the glue. -/
theorem pure_bound (N : ℕ) (w X S K P U V FU FL G I0 : ℝ)
    (z d a b a' b' e x r10 r01 p10 p01 pp M E : ℂ)
    (hw : 0 < w) (hX1 : 1 ≤ X) (hwX : w ≤ 2 * X) (hS : 0 ≤ S) (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hFU : 0 ≤ FU) (hFL : 0 ≤ FL) (hG : 0 ≤ G) (hI0 : 0 ≤ I0)
    (hz : ‖z‖ = X) (hd : d = 1 - b * a) (hd0 : d ≠ 0) (hdi : ‖d⁻¹‖ ≤ 2)
    (ha : ‖a‖ ≤ S / (2 * X)) (hb : ‖b‖ ≤ S / (2 * X)) (ha' : ‖a'‖ ≤ K / X ^ 2) (hb' : ‖b'‖ ≤ K / X ^ 2)
    (he : ‖e‖ = ((2 * X) ^ N)⁻¹) (hx : ‖x‖ ≤ P / w) (hr10 : ‖r10‖ ≤ U) (hr01 : ‖r01‖ ≤ V)
    (hp10 : ‖p10‖ ≤ FU) (hp01 : ‖p01‖ ≤ FL) (hM : ‖M‖ ≤ I0 / X) (hpp : ‖pp - M‖ ≤ G / w)
    (hE : E = -(-(b' * a + b * a')) / d ^ 2 * (e * x) +
        d⁻¹ * (-((N : ℂ) * z⁻¹ * e) * x + e * (pp - (a' * r10 + a * p10) - (b' * r01 + b * p01))) - e * M) :
    w ^ (N + 1) * ‖E‖ ≤ (4 * K * S + 2 * N + 4 * K + 2 * S + 2 * S ^ 2 + 1) *
      (P + U + V + FU + FL + I0 / w + G) := by
  have hX0 : 0 < X := by linarith
  have hsplit : E = -(-(b' * a + b * a')) / d ^ 2 * (e * x) + d⁻¹ * (-((N : ℂ) * z⁻¹ * e) * x) +
      d⁻¹ * e * (-(a' * r10 + a * p10) - (b' * r01 + b * p01)) + (d⁻¹ - 1) * e * pp + e * (pp - M) := by
    rw [hE]; ring
  have s1 := scale_le N hw hwX (by positivity) (bound_T1 N w X S K P d a b a' b' e x hw hX1 hS hK hP hdi ha hb ha' hb' he hx)
  have s2 := scale_le N hw hwX (by positivity) (bound_T2 N w X P z d e x hw hX1 hP hz hdi he hx)
  have s3 := scale_le N hw hwX (by positivity)
    (bound_T3 N X S K U V FU FL d a b a' b' e r10 r01 p10 p01 hX1 hS hK hdi ha hb ha' hb' he hr10 hr01 hp10 hp01)
  have s4 := scale_le N hw hwX (by positivity) (bound_T4 N w X S G I0 d a b e pp M hX1 hS hd hd0 hdi ha hb he hM hpp)
  have hen : 0 ≤ ((2 * X) ^ N)⁻¹ := by positivity
  have s5 := scale_le N hw hwX (by positivity)
    (show ‖e * (pp - M)‖ ≤ ((2 * X) ^ N)⁻¹ * (G / w) by rw [norm_mul, he]; exact mul_le_mul_of_nonneg_left hpp hen)
  have q1 : w * (4 * K * S * (P / w)) = 4 * K * S * P := by field_simp
  have q2 := scaled_T2 N w X P hw hX1 hP
  have q3 := scaled_T3 w X S K U V FU FL hw hX1 hwX hS hK hU hV hFU hFL
  have q4 := scaled_T4 w X S G I0 hw hX1 hwX hS hG hI0
  have q5 : w * (G / w) = G := by field_simp
  have hn : ‖E‖ ≤ ‖-(-(b' * a + b * a')) / d ^ 2 * (e * x)‖ + ‖d⁻¹ * (-((N : ℂ) * z⁻¹ * e) * x)‖ +
      ‖d⁻¹ * e * (-(a' * r10 + a * p10) - (b' * r01 + b * p01))‖ + ‖(d⁻¹ - 1) * e * pp‖ + ‖e * (pp - M)‖ := by
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  have hwN : 0 ≤ w ^ (N + 1) := by positivity
  have hsum := mul_le_mul_of_nonneg_left hn hwN
  have hKS : 0 ≤ K * S := mul_nonneg hK hS
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hIw : 0 ≤ I0 / w := by positivity
  set C : ℝ := 4 * K * S + 2 * N + 4 * K + 2 * S + 2 * S ^ 2 + 1 with hCdef
  have c1 : (4 * K * S + 2 * N) * P ≤ C * P := mul_le_mul_of_nonneg_right (by linarith) hP
  have c2 : (4 * K) * U ≤ C * U := mul_le_mul_of_nonneg_right (by linarith) hU
  have c3 : (2 * S) * FU ≤ C * FU := mul_le_mul_of_nonneg_right (by linarith) hFU
  have c4 : (4 * K) * V ≤ C * V := mul_le_mul_of_nonneg_right (by linarith) hV
  have c5 : (2 * S) * FL ≤ C * FL := mul_le_mul_of_nonneg_right (by linarith) hFL
  have c6 : (2 * S ^ 2) * (I0 / w) ≤ C * (I0 / w) := mul_le_mul_of_nonneg_right (by linarith) hIw
  have c7 : (S ^ 2 + 1) * G ≤ C * G := mul_le_mul_of_nonneg_right (by linarith) hG
  have hexp : C * (P + U + V + FU + FL + I0 / w + G) =
      C * P + C * U + C * V + C * FU + C * FL + C * (I0 / w) + C * G := by ring
  rw [hexp]
  linarith


theorem inv_w_sq_summable : Summable (fun n : ℤ => (1 / indexWeight n) ^ 2) := by
  refine Summable.of_norm_bounded_eventually ((Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)) ?_
  filter_upwards [eventually_cofinite_ne 0] with n hn
  have hw2 : indexWeight n ^ 2 = 1 + (n : ℝ) ^ 2 := by
    unfold indexWeight; rw [Real.sq_sqrt (by positivity)]
  have hn2 : 0 < (n : ℝ) ^ 2 := by
    have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow, one_pow, hw2]
  exact one_div_le_one_div_of_le hn2 (by linarith)

/-- On the open tail beyond the KSPS-014 threshold the discriminant equals the explicit KSPS-015 expression. -/
theorem disc_eventuallyEq {N : ℕ} (φ : SobolevC N)
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    {xi0 : ℂ} (hxi0 : KSPSVolterra.threshold N (sobolevNorm N φ) < ‖xi0‖) :
    discriminant φ =ᶠ[𝓝 xi0] fun z : ℂ => 2 * Complex.cos (wkbPhase φ z) +
      (1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0)⁻¹ *
        (((2 * Complex.I * z) ^ N)⁻¹ *
          (Rfun φ false 0 z + Rfun φ true 1 z - KSPSWKB.alpha φ z 0 * Rfun φ true 0 z -
            KSPSWKB.beta φ z 0 * Rfun φ false 1 z)) := by
  set B : ℝ := sobolevNorm N φ with hBdef
  have hT1 : 1 ≤ KSPSVolterra.threshold N B := by
    unfold KSPSVolterra.threshold
    have := Finset.sum_nonneg (fun k hk => KSPSWKB.endpointCoefficientBound_nonneg N B k hk)
    linarith
  have hopen : IsOpen {z : ℂ | KSPSVolterra.threshold N B < ‖z‖} :=
    isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hxi0] with z hz
  have hz' : KSPSVolterra.threshold N B < ‖z‖ := hz
  have hzpos : 0 < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzpos; exact lt_irrefl _ hzpos
  have hthr : WKBThreshold N B z := ⟨hzpos, hz'.le⟩
  have hdet := KSPSWKB.initialColumns_det_bound N B φ z le_rfl hthr
  have hdetv : Matrix.det (KSPSWKB.initialColumns φ z) =
      1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0 := by
    simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
  rw [hdetv] at hdet
  have hD : 1 - KSPSWKB.beta φ z 0 * KSPSWKB.alpha φ z 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; norm_num at hdet
  have hid := KSPS015W.disc_identity φ ⟨z, hz0⟩ h13 (h14 ⟨z, hz0⟩ hthr) hD
  have e1 : Rfun φ false 0 z = KSPS015W.rf φ ⟨z, hz0⟩ 0 := by unfold Rfun; rw [dif_neg hz0]; rfl
  have e2 : Rfun φ true 1 z = KSPS015W.rt φ ⟨z, hz0⟩ 1 := by unfold Rfun; rw [dif_neg hz0]; rfl
  have e3 : Rfun φ true 0 z = KSPS015W.rt φ ⟨z, hz0⟩ 0 := by unfold Rfun; rw [dif_neg hz0]; rfl
  have e4 : Rfun φ false 1 z = KSPS015W.rf φ ⟨z, hz0⟩ 1 := by unfold Rfun; rw [dif_neg hz0]; rfl
  rw [e1, e2, e3, e4]
  linear_combination hid

/-- KSPS-017 from the differentiated endpoint estimates (S017-2, S017-3) and the KSPS-011..014 head conclusions. -/
theorem discriminant_derivative_WKB_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h11 : ∃ eLower eUpper : ℤ → ℂ,
      SquareSummable eLower ∧ SquareSummable eUpper ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eLower n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eUpper n / indexValue n)
    (h12 : ∃ e1 e2 : ℤ → ℂ,
      SquareSummable e1 ∧ SquareSummable e2 ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (h17d : ∃ g1 g2 : ℤ → ℂ, SquareSummable g1 ∧ SquareSummable g2 ∧ ∀ n : ℤ,
      deriv (Rfun φ false 0) (xi n) =
          -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1) +
            g1 n / (indexValue n : ℂ) ∧
      deriv (Rfun φ true 1) (xi n) =
          -Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1) +
            g2 n / (indexValue n : ℂ))
    (h17o : ∃ fU fL : ℤ → ℂ, SquareSummable fU ∧ SquareSummable fL ∧ ∀ n : ℤ,
      ‖deriv (Rfun φ true 0) (xi n)‖ ≤ ‖fU n‖ ∧ ‖deriv (Rfun φ false 1) (xi n)‖ ≤ ‖fL n‖) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => deriv (discriminant φ) (xi n) - KSPSWKB.discriminantDerivativeMain N φ xi n) := by
  obtain ⟨eL, eU, hL, hU, h11'⟩ := h11
  obtain ⟨c1, c2, hs1, hs2, h12'⟩ := h12
  obtain ⟨g1, g2, hg1, hg2, h17d'⟩ := h17d
  obtain ⟨fU, fL, hfU, hfL, h17o'⟩ := h17o
  set B : ℝ := sobolevNorm N φ with hBdef
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N,
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k hk => KSPSWKB.endpointCoefficientBound_nonneg N B k hk)
  obtain ⟨KA, hKA, hAd⟩ := endpointCoeff_deriv φ false
  obtain ⟨KB, hKB, hBd⟩ := endpointCoeff_deriv φ true
  set K : ℝ := KA + KB with hKdef
  have hK0 : 0 ≤ K := by positivity
  set I0 : ℝ := ‖integralRiccatiLeft φ (N + 1)‖ with hI0def
  set C : ℝ := 4 * K * S + 2 * N + 4 * K + 2 * S + 2 * S ^ 2 + 1 with hCdef
  set Uf : ℤ → ℝ := fun n => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖ with hUf
  set Vf : ℤ → ℝ := fun n => ‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖ with hVf
  set Pf : ℤ → ℝ := fun n => ‖c1 n‖ + ‖c2 n‖ + S * (Uf n + Vf n) with hPf
  set Gf : ℤ → ℝ := fun n => ‖g1 n‖ + ‖g2 n‖ with hGf
  set Zf : ℤ → ℝ := fun n => Pf n + Uf n + Vf n + ‖fU n‖ + ‖fL n‖ + I0 / indexWeight n + Gf n with hZf
  -- summability of the dominating sequence
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have sU : Summable (fun n => Uf n ^ 2) := KSPS015W.sq_summable_add hF1 hU
  have sV : Summable (fun n => Vf n ^ 2) := KSPS015W.sq_summable_add hF2 hL
  have sP : Summable (fun n => Pf n ^ 2) :=
    KSPS015W.sq_summable_add (KSPS015W.sq_summable_add hs1 hs2)
      (KSPS015W.sq_summable_mul_left S (KSPS015W.sq_summable_add sU sV))
  have sG : Summable (fun n => Gf n ^ 2) := KSPS015W.sq_summable_add hg1 hg2
  have sI : Summable (fun n : ℤ => (I0 / indexWeight n) ^ 2) := by
    have := KSPS015W.sq_summable_mul_left I0 inv_w_sq_summable
    refine this.congr (fun n => ?_)
    rw [mul_one_div]
  have sZ : Summable (fun n => Zf n ^ 2) :=
    KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add (KSPS015W.sq_summable_add sP sU) sV) hfU) hfL) sI) sG
  have ht : Summable (fun n => (C * Zf n) ^ 2) := KSPS015W.sq_summable_mul_left C sZ
  set T : ℝ := NlsGge.ThirdConsultation.KSPSVolterra.threshold N B with hTdef
  set n0 : ℕ := ⌈a⌉₊ + ⌈T + 1⌉₊ + 1 with hn0
  have hbound : ∀ n : ℤ, (n0 : ℤ) ≤ |n| →
      indexWeight n ^ (N + 1) *
        ‖deriv (discriminant φ) (xi n) - KSPSWKB.discriminantDerivativeMain N φ xi n‖ ≤ C * Zf n := by
    intro n hn
    obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a (T + 1) ha xi hxi n hn
    have hz : xi n ≠ 0 := by
      intro h; rw [h, norm_zero] at hX1; norm_num at hX1
    set ξ : ℂ := xi n with hξ
    set X : ℝ := ‖ξ‖ with hXdef
    set w : ℝ := indexWeight n with hwdef
    have hX0 : 0 < X := by linarith
    have hthr : WKBThreshold N B ξ := ⟨hX0, by linarith⟩
    have hdet := KSPSWKB.initialColumns_det_bound N B φ ξ le_rfl hthr
    have hdetv : Matrix.det (KSPSWKB.initialColumns φ ξ) =
        1 - KSPSWKB.beta φ ξ 0 * KSPSWKB.alpha φ ξ 0 := by
      simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
    rw [hdetv] at hdet
    have hD : 1 - KSPSWKB.beta φ ξ 0 * KSPSWKB.alpha φ ξ 0 ≠ 0 := by
      intro h; rw [h, norm_zero] at hdet; norm_num at hdet
    have hDinv : ‖(1 - KSPSWKB.beta φ ξ 0 * KSPSWKB.alpha φ ξ 0)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hpos : 0 < ‖1 - KSPSWKB.beta φ ξ 0 * KSPSWKB.alpha φ ξ 0‖ := by linarith
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    have heq := disc_eventuallyEq φ h13 h14 (show T < ‖ξ‖ by linarith)
    -- derivatives
    obtain ⟨a', hA', ha'⟩ := hAd ξ hX1
    obtain ⟨b', hB', hb'⟩ := hBd ξ hX1
    have hA'' : HasDerivAt (fun z : ℂ => KSPSWKB.alpha φ z 0) a' ξ := hA'
    have hB'' : HasDerivAt (fun z : ℂ => KSPSWKB.beta φ z 0) b' ξ := hB'
    have hR : ∀ (b : Bool) (i : Fin 2), HasDerivAt (Rfun φ b i) (deriv (Rfun φ b i) ξ) ξ :=
      fun b i => (Rfun_differentiableAt φ b i hz).hasDerivAt
    have hθ := phaseDerivative_eq_deriv N φ ξ hz
    have hcos := (hθ.ccos).const_mul (2 : ℂ)
    have hDd := (hB''.mul hA'').const_sub (1 : ℂ)
    have hDi := hDd.inv hD
    have hε := hasDerivAt_eps N hz
    have hXd := (((hR false 0).add (hR true 1)).sub (hA''.mul (hR true 0))).sub (hB''.mul (hR false 1))
    have hG := hcos.add (hDi.mul (hε.mul hXd))
    have hderiv := heq.deriv_eq.trans hG.deriv
    -- the values
    set r00 : ℂ := Rfun φ false 0 ξ with hr00
    set r11 : ℂ := Rfun φ true 1 ξ with hr11
    set r10 : ℂ := Rfun φ true 0 ξ with hr10
    set r01 : ℂ := Rfun φ false 1 ξ with hr01
    set M : ℂ := -2 * Complex.I * (-1 : ℂ) ^ n / (2 * Complex.I * ξ) * integralRiccatiLeft φ (N + 1) with hMdef
    have hw0 : 0 < w := lt_of_lt_of_le one_pos (KSPS015W.one_le_w n)
    have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
    have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
    have h2Iξ : 2 * Complex.I * ξ ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hz
    -- main term
    have hmain : KSPSWKB.discriminantDerivativeMain N φ xi n =
        -2 * Complex.sin (wkbPhase φ ξ) * KSPSWKB.phaseDerivative φ ξ +
          ((2 * Complex.I * ξ) ^ N)⁻¹ * M := by
      unfold KSPSWKB.discriminantDerivativeMain
      rw [← hξ, hMdef, zpow_add_one₀ hm1, pow_succ]
      field_simp
    -- diagonal values (KSPS-012, KSPS-013)
    have hLow : r00 = KSPSWKB.endpointDiagonalLower N φ xi n := rfl
    have hUpp : r11 = KSPSWKB.endpointDiagonalUpper N φ xi n := rfl
    have hsum : r00 + r11 = (c1 n + c2 n) / (w : ℂ) := by
      rw [hLow, hUpp, (h12' n).1, (h12' n).2, ← h13 (N + 1) ⟨by omega, le_rfl⟩, zpow_add_one₀ hm1]
      unfold indexValue
      ring
    have hs : ‖r00 + r11‖ ≤ (‖c1 n‖ + ‖c2 n‖) / w := by
      rw [hsum, norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) hw0.le
    have hdivle : ∀ e : ℂ, ‖e / (indexValue n : ℂ)‖ ≤ ‖e‖ := by
      intro e
      unfold indexValue
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      exact div_le_self (norm_nonneg _) (KSPS015W.one_le_w n)
    have hu : ‖r10‖ ≤ Uf n := by
      have hR' : KSPSWKB.endpointRemainderUpper N φ xi n = (-1 : ℂ) ^ N * r10 := by
        simp only [KSPSWKB.endpointRemainderUpper, hr10, Rfun, hξ, dif_neg (show xi n ≠ 0 from hz)]
      have hn1 : ‖r10‖ = ‖KSPSWKB.endpointRemainderUpper N φ xi n‖ := by
        rw [hR', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [hn1, (h11' n).2]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hdivle _))
      rw [norm_mul, norm_mul, Complex.norm_I, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, one_mul]
    have hv : ‖r01‖ ≤ Vf n := by
      have hR' : KSPSWKB.endpointRemainderLower N φ xi n = r01 := rfl
      rw [← hR', (h11' n).1]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hdivle _))
      rw [norm_mul, norm_mul, Complex.norm_I, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, one_mul]
    have hα : ‖KSPSWKB.alpha φ ξ 0‖ ≤ S / (2 * X) :=
      KSPSWKB.endpointSum_norm_le B φ le_rfl false ξ hX1
    have hβ : ‖KSPSWKB.beta φ ξ 0‖ ≤ S / (2 * X) :=
      KSPSWKB.endpointSum_norm_le B φ le_rfl true ξ hX1
    have hX2 : 0 < X ^ 2 := by positivity
    have ha'' : ‖a'‖ ≤ K / X ^ 2 :=
      ha'.trans (div_le_div_of_nonneg_right (by linarith) hX2.le)
    have hb'' : ‖b'‖ ≤ K / X ^ 2 :=
      hb'.trans (div_le_div_of_nonneg_right (by linarith) hX2.le)
    have hε' : ‖((2 * Complex.I * ξ) ^ N)⁻¹‖ = ((2 * X) ^ N)⁻¹ := by
      rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    have hSw : S / (2 * X) ≤ S / w := div_le_div_of_nonneg_left hS0 hw0 hwX
    have hx : ‖r00 + r11 - KSPSWKB.alpha φ ξ 0 * r10 - KSPSWKB.beta φ ξ 0 * r01‖ ≤ Pf n / w := by
      have k1 : ‖KSPSWKB.alpha φ ξ 0 * r10‖ ≤ S / w * Uf n := by
        rw [norm_mul]; exact mul_le_mul (hα.trans hSw) hu (norm_nonneg _) (by positivity)
      have k2 : ‖KSPSWKB.beta φ ξ 0 * r01‖ ≤ S / w * Vf n := by
        rw [norm_mul]; exact mul_le_mul (hβ.trans hSw) hv (norm_nonneg _) (by positivity)
      have k3 := norm_sub_le (r00 + r11 - KSPSWKB.alpha φ ξ 0 * r10) (KSPSWKB.beta φ ξ 0 * r01)
      have k4 := norm_sub_le (r00 + r11) (KSPSWKB.alpha φ ξ 0 * r10)
      have k5 : Pf n / w = (‖c1 n‖ + ‖c2 n‖) / w + S / w * Uf n + S / w * Vf n := by
        rw [hPf]; field_simp; ring
      rw [k5]
      linarith
    have hM : ‖M‖ ≤ I0 / X := by
      have : ‖M‖ = I0 / X := by
        rw [hMdef, norm_mul, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I,
          norm_zpow, norm_neg, norm_one, one_zpow, Complex.norm_ofNat, ← hXdef, ← hI0def]
        field_simp
      exact le_of_eq this
    have hpp : ‖deriv (Rfun φ false 0) ξ + deriv (Rfun φ true 1) ξ - M‖ ≤ Gf n / w := by
      have e : deriv (Rfun φ false 0) ξ + deriv (Rfun φ true 1) ξ - M = (g1 n + g2 n) / (w : ℂ) := by
        rw [(h17d' n).1, (h17d' n).2, ← h13 (N + 1) ⟨by omega, le_rfl⟩, hMdef]
        unfold indexValue
        ring
      rw [e, norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) hw0.le
    have hPn : 0 ≤ Pf n := by
      have : 0 ≤ Uf n := le_trans (norm_nonneg _) hu
      have : 0 ≤ Vf n := le_trans (norm_nonneg _) hv
      simp only [hPf]; positivity
    have hGn : 0 ≤ Gf n := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hp10 := (h17o' n).1
    have hp01 := (h17o' n).2
    have key := pure_bound N w X S K (Pf n) (Uf n) (Vf n) ‖fU n‖ ‖fL n‖ (Gf n) I0
      ξ (1 - KSPSWKB.beta φ ξ 0 * KSPSWKB.alpha φ ξ 0) (KSPSWKB.alpha φ ξ 0) (KSPSWKB.beta φ ξ 0) a' b'
      ((2 * Complex.I * ξ) ^ N)⁻¹ (r00 + r11 - KSPSWKB.alpha φ ξ 0 * r10 - KSPSWKB.beta φ ξ 0 * r01)
      r10 r01 (deriv (Rfun φ true 0) ξ) (deriv (Rfun φ false 1) ξ)
      (deriv (Rfun φ false 0) ξ + deriv (Rfun φ true 1) ξ) M
      (deriv (discriminant φ) ξ - KSPSWKB.discriminantDerivativeMain N φ xi n)
      hw0 hX1 hwX hS0 hK0 hPn
      (le_trans (norm_nonneg _) hu) (le_trans (norm_nonneg _) hv) (norm_nonneg _) (norm_nonneg _)
      hGn (norm_nonneg _) rfl rfl hD hDinv hα hβ ha'' hb'' hε' hx hu hv hp10 hp01 hM hpp
      (by rw [hderiv, hmain]; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.inv_apply, hr00, hr11, hr10, hr01]; ring)
    exact key
  -- summability
  unfold WeightedL2Error
  have hrp : ∀ n : ℤ, indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) =
      (indexWeight n ^ (N + 1)) ^ 2 := by
    intro n
    rw [show (2 * ((N + 1 : ℕ) : ℝ)) = ((2 * (N + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  refine Summable.of_norm_bounded_eventually ht ?_
  filter_upwards [KSPS015W.eventually_natAbs n0] with n hn
  beta_reduce
  rw [hrp n, ← mul_pow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 : 0 ≤ indexWeight n ^ (N + 1) *
      ‖deriv (discriminant φ) (xi n) - KSPSWKB.discriminantDerivativeMain N φ xi n‖ :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one (KSPS015W.one_le_w n)) _) (norm_nonneg _)
  exact pow_le_pow_left₀ h0 (hbound n hn) 2

end
end NlsGge.ThirdConsultation.KSPS017W
