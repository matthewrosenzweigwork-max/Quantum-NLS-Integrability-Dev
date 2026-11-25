                                                                                                                                 
                                                                                                                      
                                                                                                   
                                                                               
import Mathlib
import NlsGge.Atomic.KSN.KSN015
import NlsGge.Atomic.KSN.KSN016Host

set_option autoImplicit false
open Filter Topology

namespace NlsGge.Atomic.KSN016
open NlsGge.ThirdConsultation.KSN

lemma natAbs_cast (k : ℤ) : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
  rw [Nat.cast_natAbs]; push_cast; rfl

lemma summable_sq : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) := by
  have := (Real.summable_one_div_int_pow (p := 2)).2 (by norm_num)
  exact this

lemma summable_sq_shift (n : ℤ) : Summable (fun k : ℤ => 1 / ((k : ℝ) - n) ^ 2) := by
  have := (Equiv.subRight n).summable_iff.2 summable_sq
  refine this.congr (fun k => ?_)
  simp [Function.comp, sub_eq_add_neg]

lemma tsum_sq_shift (n : ℤ) :
    ∑' k : ℤ, 1 / ((k : ℝ) - n) ^ 2 = ∑' k : ℤ, 1 / (k : ℝ) ^ 2 := by
  have := (Equiv.subRight n).tsum_eq (fun k : ℤ => 1 / (k : ℝ) ^ 2)
  simpa [Function.comp] using this

/-- the squared kernel -/
noncomputable def wq (n k : ℤ) : ℝ := 1 / (((k : ℝ) ^ 2) * (((k : ℝ) - n) ^ 2))

lemma wq_nonneg (n k : ℤ) : 0 ≤ wq n k := by unfold wq; positivity

lemma alg_wq (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x - y ≠ 0) :
    1 / (x ^ 2 * y ^ 2) ≤ (2 / (x - y) ^ 2) * (1 / x ^ 2 + 1 / y ^ 2) := by
  have h1 : 0 < x ^ 2 := by positivity
  have h2 : 0 < y ^ 2 := by positivity
  have h3 : 0 < (x - y) ^ 2 := by positivity
  rw [show (2 / (x - y) ^ 2) * (1 / x ^ 2 + 1 / y ^ 2) =
      2 * (x ^ 2 + y ^ 2) / ((x - y) ^ 2 * (x ^ 2 * y ^ 2)) by field_simp; ring]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg (x + y), mul_pos h1 h2, mul_nonneg (sq_nonneg (x+y)) (mul_pos h1 h2).le]

lemma wq_le (n k : ℤ) (hn : n ≠ 0) :
    wq n k ≤ (2 / (n : ℝ) ^ 2) * (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - n) ^ 2) := by
  unfold wq
  by_cases hk : k = 0
  · subst hk; simp; positivity
  by_cases hkn : k = n
  · subst hkn; simp; positivity
  have hx : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hy : (k : ℝ) - n ≠ 0 := by
    intro h; apply hkn; exact_mod_cast sub_eq_zero.1 h
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have := alg_wq (k : ℝ) ((k : ℝ) - n) hx hy (by simpa using hn')
  simpa using this

/-- sum bound of the squared kernel -/
lemma wq_sum (n : ℤ) (hn : n ≠ 0) :
    Summable (wq n) ∧ ∑' k : ℤ, wq n k ≤ (4 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
  have hs : Summable (fun k : ℤ => (2 / (n : ℝ) ^ 2) *
      (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - n) ^ 2)) :=
    (summable_sq.add (summable_sq_shift n)).mul_left _
  have hsum : Summable (wq n) :=
    Summable.of_nonneg_of_le (wq_nonneg n) (fun k => wq_le n k hn) hs
  refine ⟨hsum, ?_⟩
  calc ∑' k : ℤ, wq n k ≤ ∑' k : ℤ, (2 / (n : ℝ) ^ 2) *
        (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - n) ^ 2) :=
        hsum.tsum_le_tsum (fun k => wq_le n k hn) hs
    _ = (2 / (n : ℝ) ^ 2) * (∑' k : ℤ, 1 / (k : ℝ) ^ 2 + ∑' k : ℤ, 1 / ((k : ℝ) - n) ^ 2) := by
        rw [tsum_mul_left, (summable_sq.tsum_add (summable_sq_shift n))]
    _ = (4 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
        rw [tsum_sq_shift]; ring


lemma amgm1 (p q s m : ℝ) (hsm : s * m = 1) (hs : 0 ≤ s) :
    p ^ 2 * q ≤ (m * (p ^ 2 * q ^ 2) + s * p ^ 2) / 2 := by
  have : m * (p ^ 2 * q ^ 2) + s * p ^ 2 - 2 * (p ^ 2 * q) = p ^ 2 * s * (m * q - 1) ^ 2 := by
    linear_combination (-(p ^ 2 * (m * q ^ 2 - 2 * q))) * hsm
  have h2 : 0 ≤ p ^ 2 * s * (m * q - 1) ^ 2 := by positivity
  linarith

lemma amgm3 (p q s m : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hm : 1 ≤ m) :
    s * p * q ^ 2 ≤ (m * (p ^ 2 * q ^ 2) + s * q ^ 2) / 2 := by
  have : m * (p ^ 2 * q ^ 2) + s * q ^ 2 - 2 * (s * p * q ^ 2) =
      q ^ 2 * ((m - 1) * p ^ 2 + (p - s) ^ 2 + s * (1 - s)) := by ring
  have h2 : 0 ≤ q ^ 2 * ((m - 1) * p ^ 2 + (p - s) ^ 2 + s * (1 - s)) := by
    have : 0 ≤ (m - 1) * p ^ 2 := mul_nonneg (by linarith) (sq_nonneg p)
    have : 0 ≤ s * (1 - s) := mul_nonneg hs (by linarith)
    positivity
  linarith

lemma final_real (κ1 κ2 p q s m : ℝ) (h1 : 0 ≤ κ1) (h2 : 0 ≤ κ2) (_hp : 0 ≤ p) (_hq : 0 ≤ q)
    (hs : 0 ≤ s) (hm : 1 ≤ m) (hsm : s * m = 1) :
    κ1 * 2 * (p ^ 2 * q) + κ2 * 2 * (2 * (p ^ 2 * q ^ 2) + s * p * q ^ 2) ≤
      (κ1 + 5 * κ2) * (m * (p * q) ^ 2 + s * (p ^ 2 + q ^ 2)) := by
  have a1 := amgm1 p q s m hsm hs
  have hs1 : s ≤ 1 := by nlinarith
  have a3 := amgm3 p q s m hs hs1 hm
  have a2 : p ^ 2 * q ^ 2 ≤ m * (p ^ 2 * q ^ 2) := by
    have : 0 ≤ p ^ 2 * q ^ 2 := by positivity
    nlinarith
  have e1 : 0 ≤ m * (p ^ 2 * q ^ 2) := by positivity
  have e2 : 0 ≤ s * p ^ 2 := by positivity
  have e3 : 0 ≤ s * q ^ 2 := by positivity
  have k1 := mul_le_mul_of_nonneg_left a1 h1
  have k2 := mul_le_mul_of_nonneg_left a2 h2
  have k3 := mul_le_mul_of_nonneg_left a3 h2
  have k4 := mul_nonneg h1 e3
  have k5 := mul_nonneg h2 e2
  have k6 := mul_nonneg h2 e1
  have k7 := mul_nonneg h1 e1
  have hh : (p * q) ^ 2 = p ^ 2 * q ^ 2 := by ring
  rw [hh]
  nlinarith


lemma key_id (c a e d X : ℂ) (hX : X ≠ 0) (hd : d ≠ 0) (hden : d + e ≠ 0) :
    (c / X + a) / (d + e) - c / (X * d) = a / (d + e) - (c / X) * e / ((d + e) * d) := by
  field_simp
  ring

lemma cx_bound (B : ℝ) (hB : 0 < B) (c a δ : ℂ) (x y m : ℝ)
    (hc : ‖c‖ ≤ B) (hx : 1 ≤ |x|) (hy : 1 ≤ |y|) (hm : 1 ≤ m)
    (ha : ‖a‖ ≤ B * (|x|⁻¹) ^ 2) (hδ : ‖δ‖ ≤ B * m⁻¹)
    (hlow : Real.pi * |y| / 2 ≤ ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖) :
    ‖(c / (x : ℂ) + a) / (((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ))‖ ≤
        (4 * B / Real.pi) * (|x|⁻¹ * |y|⁻¹) ∧
    ‖(c / (x : ℂ) + a) / (((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)) -
        c / ((x : ℂ) * ((y : ℂ) * (Real.pi : ℂ)))‖ ≤
      (B / Real.pi + 5 * (B / Real.pi) ^ 2) *
        (m * (|x|⁻¹ * |y|⁻¹) ^ 2 + m⁻¹ * ((|x|⁻¹) ^ 2 + (|y|⁻¹) ^ 2)) := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hπ0 : 0 < Real.pi := by linarith
  have hxa : 0 < |x| := by linarith
  have hya : 0 < |y| := by linarith
  have hx0 : x ≠ 0 := fun h => by simp [h] at hxa
  have hy0 : y ≠ 0 := fun h => by simp [h] at hya
  have hm0 : 0 < m := by linarith
  have hp0 : 0 < |x|⁻¹ := inv_pos.2 hxa
  have hq0 : 0 < |y|⁻¹ := inv_pos.2 hya
  have hs0 : 0 < m⁻¹ := inv_pos.2 hm0
  have hp1 : |x|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have hs1 : m⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hm
  have hsm : m⁻¹ * m = 1 := inv_mul_cancel₀ hm0.ne'
  have hnx : ‖(x : ℂ)‖ = |x| := by simp
  have hcx : ‖c / (x : ℂ)‖ ≤ B * |x|⁻¹ := by
    rw [norm_div, hnx, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hc hp0.le
  have hnum : ‖c / (x : ℂ) + a‖ ≤ 2 * B * |x|⁻¹ := by
    calc ‖c / (x : ℂ) + a‖ ≤ ‖c / (x : ℂ)‖ + ‖a‖ := norm_add_le _ _
      _ ≤ B * |x|⁻¹ + B * (|x|⁻¹) ^ 2 := add_le_add hcx ha
      _ ≤ 2 * B * |x|⁻¹ := by nlinarith [mul_pos hB hp0, mul_nonneg hB.le (mul_nonneg hp0.le (sub_nonneg.2 hp1))]
  have he : ‖c / (x : ℂ) + a - δ‖ ≤ 2 * B * |x|⁻¹ + B * m⁻¹ :=
    calc ‖c / (x : ℂ) + a - δ‖ ≤ ‖c / (x : ℂ) + a‖ + ‖δ‖ := norm_sub_le _ _
      _ ≤ 2 * B * |x|⁻¹ + B * m⁻¹ := add_le_add hnum hδ
  have hd : ‖(y : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |y| := by
    rw [norm_mul]; simp [abs_of_pos hπ0, mul_comm]
  have hdenpos : 0 < ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖ :=
    lt_of_lt_of_le (by positivity) hlow
  have hinv : ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖⁻¹ ≤ 2 * |y|⁻¹ / Real.pi := by
    have := inv_anti₀ (by positivity) hlow
    refine this.trans_eq ?_
    field_simp
  have hdinv : ‖(y : ℂ) * (Real.pi : ℂ)‖⁻¹ = |y|⁻¹ / Real.pi := by
    rw [hd]; field_simp
  have hden0 : ((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ) ≠ 0 := norm_pos_iff.1 hdenpos
  have hd0 : (y : ℂ) * (Real.pi : ℂ) ≠ 0 := by
    have : (y : ℂ) ≠ 0 := by exact_mod_cast hy0
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hπ0.ne'
    exact mul_ne_zero ‹_› ‹_›
  have hX0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hinv0 : 0 ≤ ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖⁻¹ := inv_nonneg.2 hdenpos.le
  constructor
  · rw [norm_div, div_eq_mul_inv]
    calc ‖c / (x : ℂ) + a‖ * ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖⁻¹
        ≤ (2 * B * |x|⁻¹) * (2 * |y|⁻¹ / Real.pi) :=
          mul_le_mul hnum hinv hinv0 (by positivity)
      _ = (4 * B / Real.pi) * (|x|⁻¹ * |y|⁻¹) := by ring
  · rw [key_id c a (c / (x : ℂ) + a - δ) ((y : ℂ) * (Real.pi : ℂ)) (x : ℂ) hX0 hd0 hden0]
    have h1 : ‖a / (((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ))‖ ≤
        (B * (|x|⁻¹) ^ 2) * (2 * |y|⁻¹ / Real.pi) := by
      rw [norm_div, div_eq_mul_inv]
      exact mul_le_mul ha hinv hinv0 (by positivity)
    have h2 : ‖(c / (x : ℂ)) * (c / (x : ℂ) + a - δ) /
        ((((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)) * ((y : ℂ) * (Real.pi : ℂ)))‖ ≤
        (B * |x|⁻¹) * (2 * B * |x|⁻¹ + B * m⁻¹) * ((2 * |y|⁻¹ / Real.pi) * (|y|⁻¹ / Real.pi)) := by
      rw [norm_div, norm_mul, norm_mul, div_eq_mul_inv, mul_inv, hdinv]
      have hq' : 0 ≤ |y|⁻¹ / Real.pi := by positivity
      refine mul_le_mul (mul_le_mul hcx he (norm_nonneg _) (by positivity)) ?_ ?_ (by positivity)
      · exact mul_le_mul hinv le_rfl hq' (by positivity)
      · exact mul_nonneg hinv0 hq'
    have hk := final_real (B / Real.pi) ((B / Real.pi) ^ 2) |x|⁻¹ |y|⁻¹ m⁻¹ m
      (by positivity) (by positivity) hp0.le hq0.le hs0.le hm hsm
    calc _ ≤ _ := norm_sub_le _ _
      _ ≤ (B * (|x|⁻¹) ^ 2) * (2 * |y|⁻¹ / Real.pi) +
          (B * |x|⁻¹) * (2 * B * |x|⁻¹ + B * m⁻¹) * ((2 * |y|⁻¹ / Real.pi) * (|y|⁻¹ / Real.pi)) :=
          add_le_add h1 h2
      _ = (B / Real.pi) * 2 * ((|x|⁻¹) ^ 2 * |y|⁻¹) + (B / Real.pi) ^ 2 * 2 *
          (2 * ((|x|⁻¹) ^ 2 * (|y|⁻¹) ^ 2) + m⁻¹ * |x|⁻¹ * (|y|⁻¹) ^ 2) := by ring
      _ ≤ _ := hk


lemma hlow_lem (B : ℝ) (hB : 0 < B) (c a δ : ℂ) (x y m : ℝ) (K : ℕ)
    (hc : ‖c‖ ≤ B) (hK : 2 * B < K) (hK1 : 1 ≤ K) (hx : (K : ℝ) ≤ |x|) (hmK : (K : ℝ) ≤ m)
    (hy : 1 ≤ |y|)
    (ha : ‖a‖ ≤ B * (|x|⁻¹) ^ 2) (hδ : ‖δ‖ ≤ B * m⁻¹) :
    Real.pi * |y| / 2 ≤ ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖ := by
  have hπ : 3 < Real.pi := Real.pi_gt_three
  have hπ0 : 0 < Real.pi := by linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hxa : 0 < |x| := lt_of_lt_of_le hK0 hx
  have hm0 : 0 < m := lt_of_lt_of_le hK0 hmK
  have hp0 : 0 < |x|⁻¹ := inv_pos.2 hxa
  have hpK : |x|⁻¹ ≤ (K : ℝ)⁻¹ := inv_anti₀ hK0 hx
  have hsK : m⁻¹ ≤ (K : ℝ)⁻¹ := inv_anti₀ hK0 hmK
  have hp1 : |x|⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (hKR.trans hx)
  have hBK : B * (K : ℝ)⁻¹ < 1 / 2 := by
    rw [← div_eq_mul_inv, div_lt_iff₀ hK0]; linarith
  have hnx : ‖(x : ℂ)‖ = |x| := by simp
  have hcx : ‖c / (x : ℂ)‖ ≤ B * |x|⁻¹ := by
    rw [norm_div, hnx, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hc hp0.le
  have he : ‖c / (x : ℂ) + a - δ‖ ≤ 2 * B * |x|⁻¹ + B * m⁻¹ :=
    calc ‖c / (x : ℂ) + a - δ‖ ≤ ‖c / (x : ℂ) + a‖ + ‖δ‖ := norm_sub_le _ _
      _ ≤ (‖c / (x : ℂ)‖ + ‖a‖) + ‖δ‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (B * |x|⁻¹ + B * (|x|⁻¹) ^ 2) + B * m⁻¹ := by gcongr
      _ ≤ 2 * B * |x|⁻¹ + B * m⁻¹ := by
          nlinarith [mul_nonneg hB.le (mul_nonneg hp0.le (sub_nonneg.2 hp1))]
  have he2 : ‖c / (x : ℂ) + a - δ‖ < 3 / 2 := by
    have : 2 * B * |x|⁻¹ + B * m⁻¹ ≤ 3 * (B * (K : ℝ)⁻¹) := by
      nlinarith [mul_le_mul_of_nonneg_left hpK hB.le, mul_le_mul_of_nonneg_left hsK hB.le]
    linarith
  have hd : ‖(y : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |y| := by
    rw [norm_mul]; simp [abs_of_pos hπ0, mul_comm]
  have h3 : ‖(y : ℂ) * (Real.pi : ℂ)‖ ≤
      ‖((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)‖ + ‖c / (x : ℂ) + a - δ‖ := by
    have := norm_sub_le (((y : ℂ) * (Real.pi : ℂ)) + (c / (x : ℂ) + a - δ)) (c / (x : ℂ) + a - δ)
    simpa using this
  rw [hd] at h3
  nlinarith


lemma pt (B : ℝ) (hB : 0 < B) (K : ℕ) (hK : 2 * B < K) (hK1 : 1 ≤ K)
    (τ μ : ℤ → ℂ) (c₁ : ℂ) (hc : ‖c₁‖ ≤ B)
    (h1 : ∀ k : ℤ, K ≤ k.natAbs →
        ‖τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ B / (k.natAbs : ℝ) ^ 2)
    (h2 : ∀ n : ℤ, K ≤ n.natAbs →
        ‖μ n - (n : ℂ) * Real.pi‖ ≤ B / (n.natAbs : ℝ))
    (n k : ℤ) (hn : K ≤ n.natAbs) (hk : K ≤ k.natAbs) (hkn : k ≠ n) :
    τ k - μ n ≠ 0 ∧
    ‖midpointRatioTail K τ (μ n) n k‖ ≤
      (4 * B / Real.pi) * (|(k : ℝ)|⁻¹ * |(k : ℝ) - n|⁻¹) ∧
    ‖midpointRatioTail K τ (μ n) n k - (c₁ / (Real.pi : ℂ)) * (((1 / ((k : ℝ) * ((k : ℝ) - n)) : ℝ)) : ℂ)‖ ≤
      (B / Real.pi + 5 * (B / Real.pi) ^ 2) *
        ((n.natAbs : ℝ) * (|(k : ℝ)|⁻¹ * |(k : ℝ) - n|⁻¹) ^ 2 +
          (n.natAbs : ℝ)⁻¹ * ((|(k : ℝ)|⁻¹) ^ 2 + (|(k : ℝ) - n|⁻¹) ^ 2)) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hkR : (K : ℝ) ≤ |(k : ℝ)| := by rw [← natAbs_cast]; exact_mod_cast hk
  have hnR : (K : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
  have hyR : 1 ≤ |(k : ℝ) - n| := by
    have : (1 : ℤ) ≤ |k - n| := Int.one_le_abs (sub_ne_zero.2 hkn)
    have h' : (1 : ℝ) ≤ ((|k - n| : ℤ) : ℝ) := by exact_mod_cast this
    simpa using h'
  have hm1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := hKR.trans hnR
  have ha : ‖τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ B * (|(k : ℝ)|⁻¹) ^ 2 := by
    refine (h1 k hk).trans_eq ?_
    rw [natAbs_cast]; field_simp
  have hδ : ‖μ n - (n : ℂ) * Real.pi‖ ≤ B * (n.natAbs : ℝ)⁻¹ := by
    refine (h2 n hn).trans_eq ?_
    rw [div_eq_mul_inv]
  have e1 : (((k : ℝ)) : ℂ) = (k : ℂ) := Complex.ofReal_intCast k
  have e2 : ((((k : ℝ) - n : ℝ)) : ℂ) = (k : ℂ) - n := by push_cast; ring
  have hlow := hlow_lem B hB c₁ (τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)) (μ n - (n : ℂ) * Real.pi) (k : ℝ) ((k : ℝ) - n) (n.natAbs : ℝ) K hc hK hK1 hkR hnR hyR
    ha hδ
  have hid : τ k - μ n = (((k : ℝ) - n : ℝ) : ℂ) * (Real.pi : ℂ) +
      (c₁ / ((k : ℝ) : ℂ) + (τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)) -
        (μ n - (n : ℂ) * Real.pi)) := by
    rw [e1, e2]; ring
  rw [← hid] at hlow
  have hne : τ k - μ n ≠ 0 := by
    intro h; rw [h] at hlow; simp at hlow
    have : 0 < Real.pi * |(k : ℝ) - n| := by
      have := Real.pi_pos; positivity
    linarith
  have hcb := cx_bound B hB c₁ (τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)) (μ n - (n : ℂ) * Real.pi) (k : ℝ) ((k : ℝ) - n) (n.natAbs : ℝ) hc (hKR.trans hkR) hyR hm1
    ha hδ (by rw [← hid]; exact hlow)
  rw [← hid] at hcb
  have hT : midpointRatioTail K τ (μ n) n k = (c₁ / ((k : ℝ) : ℂ) + (τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ))) / (τ k - μ n) := by
    unfold midpointRatioTail
    rw [if_pos ⟨hk, hkn⟩, e1]
    congr 1; field_simp; ring
  refine ⟨hne, ?_, ?_⟩
  · rw [hT]; exact hcb.1
  · rw [hT]
    refine le_trans (le_of_eq ?_) hcb.2
    congr 2
    have hk0 : (k : ℂ) ≠ 0 := by
      have : k ≠ 0 := by rintro rfl; simp at hk; omega
      exact_mod_cast this
    have hkn' : (k : ℂ) - n ≠ 0 := by
      intro h; exact hkn (by exact_mod_cast sub_eq_zero.1 h)
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    rw [e1, e2]; push_cast
    field_simp


lemma inv_abs_sq (x : ℝ) : (|x|⁻¹) ^ 2 = 1 / x ^ 2 := by
  rw [inv_pow, sq_abs, one_div]

lemma u_sq (a b : ℝ) : (|a|⁻¹ * |b|⁻¹) ^ 2 = 1 / (a ^ 2 * b ^ 2) := by
  rw [mul_pow, inv_abs_sq, inv_abs_sq, one_div_mul_one_div]

lemma natAbs_sq (n : ℤ) : ((n.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
  rw [natAbs_cast, sq_abs]

noncomputable def fF (K : ℕ) (n k : ℤ) : ℝ :=
  if k = 0 ∨ k = n ∨ k ∈ Finset.Ioo (-(K : ℤ)) (K : ℤ) then (0 : ℝ)
  else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))

noncomputable def f0 (n k : ℤ) : ℝ :=
  if k = 0 ∨ k = n then (0 : ℝ) else 1 / ((k : ℝ) * ((k : ℝ) - (n : ℝ)))

lemma mem_S_iff (K : ℕ) (hK1 : 1 ≤ K) (n k : ℤ) :
    (K ≤ k.natAbs ∧ k ≠ n) ↔ ¬ (k = 0 ∨ k = n ∨ k ∈ Finset.Ioo (-(K : ℤ)) (K : ℤ)) := by
  simp only [Finset.mem_Ioo]
  omega

/-- per-`n` estimate -/
lemma per_n (B : ℝ) (hB : 0 < B) (K : ℕ) (hK : 2 * B < K) (hK1 : 1 ≤ K)
    (τ μ : ℤ → ℂ) (c₁ : ℂ) (hc : ‖c₁‖ ≤ B)
    (h1 : ∀ k : ℤ, K ≤ k.natAbs →
        ‖τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ B / (k.natAbs : ℝ) ^ 2)
    (h2 : ∀ n : ℤ, K ≤ n.natAbs →
        ‖μ n - (n : ℂ) * Real.pi‖ ≤ B / (n.natAbs : ℝ))
    (n : ℤ) (hn : K ≤ n.natAbs) (CF : ℝ)
    (hF : Summable (fF K n))
    (hV : ∑' k : ℤ, f0 n k = 2 / (n : ℝ) ^ 2)
    (hCF : |∑' k : ℤ, fF K n k - ∑' k : ℤ, f0 n k| ≤ CF / |(n : ℝ)|) :
    (∀ k : ℤ, K ≤ k.natAbs → k ≠ n → τ k - μ n ≠ 0) ∧
    Summable (midpointRatioTail K τ (μ n) n) ∧
    Summable (fun k : ℤ => ‖midpointRatioTail K τ (μ n) n k‖ ^ 2) ∧
    ‖∑' k : ℤ, midpointRatioTail K τ (μ n) n k‖ ≤
      ((B / Real.pi + 5 * (B / Real.pi) ^ 2) * (6 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) +
        (B / Real.pi) * (2 + CF)) / (n.natAbs : ℝ) ∧
    ∑' k : ℤ, ‖midpointRatioTail K τ (μ n) n k‖ ^ 2 ≤
      ((4 * B / Real.pi) ^ 2 * (4 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2)) / (n.natAbs : ℝ) ^ 2 := by
  have hπ0 : 0 < Real.pi := Real.pi_pos
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hm1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := hKR.trans (by exact_mod_cast hn)
  have hm0 : 0 < (n.natAbs : ℝ) := by linarith
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn; omega
  set m : ℝ := (n.natAbs : ℝ) with hm
  set S0 : ℝ := ∑' k : ℤ, 1 / (k : ℝ) ^ 2 with hS0
  have hS0nn : 0 ≤ S0 := tsum_nonneg (fun k => by positivity)
  have hnm : (n : ℝ) ^ 2 = m ^ 2 := (natAbs_sq n).symm
  obtain ⟨hwS, hwB⟩ := wq_sum n hn0
  rw [hnm] at hwB
  set t : ℤ → ℂ := midpointRatioTail K τ (μ n) n with ht
  set L : ℝ := B / Real.pi + 5 * (B / Real.pi) ^ 2 with hL
  have hL0 : 0 ≤ L := by positivity
  set G : ℤ → ℝ := fun k => m * wq n k + m⁻¹ * (1 / (k : ℝ) ^ 2 + 1 / ((k : ℝ) - n) ^ 2) with hG
  have hG0 : ∀ k, 0 ≤ G k := fun k => by
    have := wq_nonneg n k; simp only [hG]; positivity
  have hGs : Summable G :=
    (hwS.mul_left m).add ((summable_sq.add (summable_sq_shift n)).mul_left m⁻¹)
  have hGt : ∑' k, G k ≤ 6 * S0 / m := by
    have : ∑' k, G k = m * ∑' k, wq n k + m⁻¹ * (S0 + S0) := by
      simp only [hG]
      rw [(hwS.mul_left m).tsum_add ((summable_sq.add (summable_sq_shift n)).mul_left m⁻¹),
        tsum_mul_left, tsum_mul_left, summable_sq.tsum_add (summable_sq_shift n), tsum_sq_shift]
    rw [this]
    have h3 : m * ∑' k, wq n k ≤ m * (4 * S0 / m ^ 2) := mul_le_mul_of_nonneg_left hwB hm0.le
    have h4 : m * (4 * S0 / m ^ 2) = 4 * S0 / m := by field_simp
    have h5 : 6 * S0 / m = 4 * S0 / m + m⁻¹ * (S0 + S0) := by field_simp; ring
    rw [h5]; linarith
  -- pointwise facts
  have hpt : ∀ k : ℤ, (K ≤ k.natAbs ∧ k ≠ n) →
      τ k - μ n ≠ 0 ∧ ‖t k‖ ≤ (4 * B / Real.pi) * (|(k : ℝ)|⁻¹ * |(k : ℝ) - n|⁻¹) ∧
      ‖t k - (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ)‖ ≤ L * G k := by
    intro k ⟨hk, hkn⟩
    obtain ⟨a1, a2, a3⟩ := pt B hB K hK hK1 τ μ c₁ hc h1 h2 n k hn hk hkn
    have hfk : fF K n k = 1 / ((k : ℝ) * ((k : ℝ) - n)) := by
      unfold fF; rw [if_neg ((mem_S_iff K hK1 n k).1 ⟨hk, hkn⟩)]
    refine ⟨a1, a2, ?_⟩
    rw [hfk]
    refine a3.trans (le_of_eq ?_)
    rw [u_sq, inv_abs_sq, inv_abs_sq]
    simp only [hG, hL, wq]
    rfl
  have hall : ∀ k : ℤ, ‖t k‖ ^ 2 ≤ (4 * B / Real.pi) ^ 2 * wq n k := by
    intro k
    by_cases hS : K ≤ k.natAbs ∧ k ≠ n
    · obtain ⟨-, a2, -⟩ := hpt k hS
      calc ‖t k‖ ^ 2 ≤ ((4 * B / Real.pi) * (|(k : ℝ)|⁻¹ * |(k : ℝ) - n|⁻¹)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) a2 2
        _ = (4 * B / Real.pi) ^ 2 * wq n k := by rw [mul_pow, u_sq]; rfl
    · have h0 : t k = 0 := by simp [ht, midpointRatioTail, hS]
      rw [h0, norm_zero]
      simpa using mul_nonneg (sq_nonneg (4 * B / Real.pi)) (wq_nonneg n k)
  have hfz : ∀ k : ℤ, ¬ (K ≤ k.natAbs ∧ k ≠ n) → fF K n k = 0 := by
    intro k hS
    unfold fF
    rw [if_pos]
    by_contra hc'
    exact hS ((mem_S_iff K hK1 n k).2 hc')
  have hr : ∀ k : ℤ, ‖t k - (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ)‖ ≤ L * G k := by
    intro k
    by_cases hS : K ≤ k.natAbs ∧ k ≠ n
    · exact (hpt k hS).2.2
    · have h0 : t k = 0 := by simp [ht, midpointRatioTail, hS]
      rw [h0, hfz k hS]
      simp only [Complex.ofReal_zero, mul_zero, sub_self, norm_zero]
      exact mul_nonneg hL0 (hG0 k)
  refine ⟨fun k hk hkn => (hpt k ⟨hk, hkn⟩).1, ?_⟩
  have hsr : Summable (fun k : ℤ => t k - (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ)) :=
    Summable.of_norm_bounded (hGs.mul_left L) hr
  have hgs : Summable (fun k : ℤ => (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ)) :=
    (Complex.summable_ofReal.2 hF).mul_left _
  have hts : Summable t := by
    have := hsr.add hgs
    simpa using this
  have hsq : Summable (fun k : ℤ => ‖t k‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hall (hwS.mul_left _)
  refine ⟨hts, hsq, ?_, ?_⟩
  · have e1 : ∑' k, t k = ∑' k, (t k - (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ)) +
        ∑' k, (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ) := by
      rw [← hsr.tsum_add hgs]; simp
    have b1 : ‖∑' k, (t k - (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ))‖ ≤ L * (6 * S0 / m) :=
      calc _ ≤ ∑' k, L * G k := tsum_of_norm_bounded (hGs.mul_left L).hasSum hr
        _ = L * ∑' k, G k := tsum_mul_left
        _ ≤ L * (6 * S0 / m) := mul_le_mul_of_nonneg_left hGt hL0
    have hnabs : |(n : ℝ)| = m := (natAbs_cast n).symm
    have hsum : |∑' k, fF K n k| ≤ (2 + CF) / m := by
      have h6 : |∑' k, fF K n k| ≤ |∑' k, fF K n k - ∑' k, f0 n k| + |∑' k, f0 n k| := by
        have := abs_add_le (∑' k, fF K n k - ∑' k, f0 n k) (∑' k, f0 n k)
        simpa using this
      have hCF' : |∑' k, fF K n k - ∑' k, f0 n k| ≤ CF / m := by rwa [hnabs] at hCF
      rw [hV] at h6 hCF'
      have h7 : |2 / (n : ℝ) ^ 2| = 2 / m ^ 2 := by
        rw [abs_of_nonneg (by positivity), hnm]
      have h8 : 2 / m ^ 2 ≤ 2 / m := by
        rw [div_le_div_iff₀ (by positivity) hm0]; nlinarith
      rw [h7] at h6
      calc _ ≤ _ := h6
        _ ≤ CF / m + 2 / m := add_le_add hCF' h8
        _ = (2 + CF) / m := by ring
    have b2 : ‖∑' k, (c₁ / (Real.pi : ℂ)) * ((fF K n k : ℝ) : ℂ)‖ ≤ (B / Real.pi) * ((2 + CF) / m) := by
      rw [tsum_mul_left, ← Complex.ofReal_tsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_div]
      have hpn : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [abs_of_pos hπ0]
      rw [hpn]
      exact mul_le_mul (div_le_div_of_nonneg_right hc hπ0.le) hsum (abs_nonneg _) (by positivity)
    calc ‖∑' k, t k‖ ≤ _ := by rw [e1]; exact norm_add_le _ _
      _ ≤ L * (6 * S0 / m) + (B / Real.pi) * ((2 + CF) / m) := add_le_add b1 b2
      _ = (L * (6 * S0) + (B / Real.pi) * (2 + CF)) / m := by ring
  · calc ∑' k, ‖t k‖ ^ 2 ≤ ∑' k, (4 * B / Real.pi) ^ 2 * wq n k :=
          hsq.tsum_le_tsum hall (hwS.mul_left _)
      _ = (4 * B / Real.pi) ^ 2 * ∑' k, wq n k := tsum_mul_left
      _ ≤ (4 * B / Real.pi) ^ 2 * (4 * S0 / m ^ 2) :=
          mul_le_mul_of_nonneg_left hwB (by positivity)
      _ = ((4 * B / Real.pi) ^ 2 * (4 * S0)) / m ^ 2 := by ring

end NlsGge.Atomic.KSN016

namespace NlsGge.ThirdConsultation.KSN
open Set Filter Topology MeasureTheory
open NlsGge.Atomic.KSN016

theorem KSN016_main (B : ℝ) (hB : 0 < B) :
  ∃ (K N : ℕ) (C : ℝ), 1 ≤ K ∧ K ≤ N ∧ 0 ≤ C ∧
    ∀ (τ μ : ℤ → ℂ) (c₁ : ℂ), ‖c₁‖ ≤ B →
      (∀ k : ℤ, K ≤ k.natAbs →
        ‖τ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ B / (k.natAbs : ℝ)^2) →
      (∀ n : ℤ, N ≤ n.natAbs →
        ‖μ n - (n : ℂ) * Real.pi‖ ≤ B / (n.natAbs : ℝ)) →
      ∀ n : ℤ, N ≤ n.natAbs →
        (∀ k : ℤ, K ≤ k.natAbs → k ≠ n → τ k - μ n ≠ 0) ∧
        Summable (midpointRatioTail K τ (μ n) n) ∧
        Summable (fun k : ℤ => ‖midpointRatioTail K τ (μ n) n k‖^2) ∧
        ‖∑' k : ℤ, midpointRatioTail K τ (μ n) n k‖ ≤ C / (n.natAbs : ℝ) ∧
        (∑' k : ℤ, ‖midpointRatioTail K τ (μ n) n k‖^2) ≤ C / (n.natAbs : ℝ)^2 := by
  have hπ0 : 0 < Real.pi := Real.pi_pos
  set K : ℕ := ⌈2 * B⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hK : 2 * B < K := by
    have := Nat.le_ceil (2 * B)
    rw [hKdef]; push_cast; linarith
  obtain ⟨CF, hCF⟩ := (NlsGge.Atomic.KSN015.ksn015_statement).2 (Finset.Ioo (-(K : ℤ)) (K : ℤ))
  refine ⟨K, K, max 0 (max
    ((B / Real.pi + 5 * (B / Real.pi) ^ 2) * (6 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2) +
        (B / Real.pi) * (2 + CF))
    ((4 * B / Real.pi) ^ 2 * (4 * ∑' k : ℤ, 1 / (k : ℝ) ^ 2))), hK1, le_rfl, le_max_left _ _, ?_⟩
  intro τ μ c₁ hc h1 h2 n hn
  have hn0 : n ≠ 0 := by
    intro h; subst h; simp only [Int.natAbs_zero] at hn; omega
  have hm0 : (0 : ℝ) < (n.natAbs : ℝ) := by
    have : 0 < n.natAbs := by omega
    exact_mod_cast this
  obtain ⟨hne, hs1, hs2, hb1, hb2⟩ := per_n B hB K hK hK1 τ μ c₁ hc h1 h2 n hn CF
    (hCF n hn0).1 (NlsGge.Atomic.KSN015.ksn015_statement.1 n hn0).2 (hCF n hn0).2
  refine ⟨hne, hs1, hs2, hb1.trans ?_, hb2.trans ?_⟩
  · exact div_le_div_of_nonneg_right
      ((le_max_left _ _).trans (le_max_right _ _)) hm0.le
  · exact div_le_div_of_nonneg_right
      ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)

end NlsGge.ThirdConsultation.KSN

