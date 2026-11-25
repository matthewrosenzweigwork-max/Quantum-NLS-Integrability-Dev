import Mathlib
import NlsGge.Atomic.KSN.KSN002
import NlsGge.Atomic.KSN.KSN013Core
import NlsGge.Atomic.KSN.KSN016
import NlsGge.GK38.Lib.EntireProductsC34a

/- KSN017 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target
   NlsGge/Atomic/KSN/KSN017Core.lean. Supporting (non-packet) PotPair-level core of KSN-017 (Pro round 15, head
   unchanged). For ONE common isolating geometry (C,R,c,J), uniform bounds Aa (G2-026 coefficient), Γ (⟨k⟩²|γ_k²|),
   Bm (first-order midpoint remainder, mass coefficient and Dirichlet localization), all chosen before φ:
   for |n| ≥ N₀,  ‖(deltaFactor n φ μ_n)⁻¹ - (-1)^n‖ ≤ C₀/|n|.
   Route (KSN Lemma 3.2): for k ≠ n,
     S_k/π_k · (λ̇_k-μ)/S_k · (kπ-μ)/(λ̇_k-μ) = (kπ-μ)/π_k,
   so (symmetric products)  P · criticalOmittedProduct · ∏(1+β_k) = π_n · sincAt n μ  with
   β_k = -(λ̇_k-kπ)/(λ̇_k-μ) (free factor: landed Lib.multipliable_omit / omitProd_zero_eq_sincAt).
   criticalOmittedProduct = 1+O(1/n): landed ksn013_disc_estimate (μ_n lies in the common nth disc).
   ∏(1+β) = 1+O(1/n): KSN016_main (signed sum + square sum of the tail, τ := λ̇, λ̇-midpoint = γ²a) plus finitely
   many small labels, then log/exp.  1/sincAt n μ = (-1)^n + O(|μ-nπ|).  See KSN017_ROUTE.md. -/
set_option autoImplicit false

open Set Filter Topology Metric SummationFilter
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

/-- Product with a square-summable perturbation controlled by its signed sum. -/
theorem ksn017_signed_prod {ι : Type*} (b : ι → ℂ) (hb : Summable b)
    (hb2 : Summable fun i => ‖b i‖ ^ 2) (hhalf : ∀ i, ‖b i‖ ≤ 1 / 2) (s1 s2 : ℝ)
    (h1 : ‖∑' i, b i‖ ≤ s1) (h2 : ∑' i, ‖b i‖ ^ 2 ≤ s2) (hs : s1 + s2 ≤ 1) :
    Multipliable (fun i => 1 + b i) ∧ ‖(∏' i, (1 + b i)) - 1‖ ≤ 2 * (s1 + s2) := by
  have hne : ∀ i, 1 + b i ≠ 0 := by
    intro i h
    have : b i = -1 := by linear_combination h
    have h3 := hhalf i
    rw [this, norm_neg, norm_one] at h3
    linarith
  have hd : ∀ i, ‖Complex.log (1 + b i) - b i‖ ≤ ‖b i‖ ^ 2 := by
    intro i
    have hlt : ‖b i‖ < 1 := by linarith [hhalf i]
    refine (Complex.norm_log_one_add_sub_self_le hlt).trans ?_
    have h0 : (1 - ‖b i‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith [hhalf i]
    have hsq := sq_nonneg ‖b i‖
    nlinarith
  have hds : Summable fun i => Complex.log (1 + b i) - b i :=
    Summable.of_norm_bounded hb2 hd
  have hls : Summable fun i => Complex.log (1 + b i) := by
    have := hds.add hb
    simpa using this
  have hm : Multipliable (fun i => 1 + b i) := Complex.multipliable_of_summable_log hls
  refine ⟨hm, ?_⟩
  have hexp := Complex.cexp_tsum_eq_tprod hne hls
  have hsplit : ∑' i, Complex.log (1 + b i) = ∑' i, (Complex.log (1 + b i) - b i) + ∑' i, b i := by
    rw [← hds.tsum_add hb]; simp
  have hdn : ‖∑' i, (Complex.log (1 + b i) - b i)‖ ≤ s2 :=
    (tsum_of_norm_bounded hb2.hasSum hd).trans h2
  have hL : ‖∑' i, Complex.log (1 + b i)‖ ≤ s1 + s2 := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    linarith
  rw [← hexp]
  refine (Complex.norm_exp_sub_one_le (hL.trans hs)).trans ?_
  linarith

/-- `sin (nπ + ε) = (-1)^n sin ε`. -/
theorem ksn017_sin_shift (n : ℤ) (ε : ℂ) :
    Complex.sin ((n : ℂ) * (Real.pi : ℂ) + ε) = (-1 : ℂ) ^ n * Complex.sin ε := by
  rw [Complex.sin_add, Complex.sin_int_mul_pi]
  have hc : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = (-1 : ℂ) ^ n := by
    have h := Real.cos_int_mul_pi n
    have e : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) = ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) := by
      push_cast; rfl
    rw [e, h]; push_cast; rfl
  rw [hc]; ring

theorem ksn017_neg_one_zpow_norm (n : ℤ) : ‖(-1 : ℂ) ^ n‖ = 1 := by
  rw [norm_zpow, norm_neg, norm_one, one_zpow]

theorem ksn017_neg_one_zpow_sq (n : ℤ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num

/-- `1/sincAt n μ = (-1)^n + O(|μ - nπ|)`. -/
theorem ksn017_sinc_inv (n : ℤ) (μ : ℂ) (hε : ‖μ - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2) :
    Lib.sincAt n μ ≠ 0 ∧
    ‖(Lib.sincAt n μ)⁻¹ - (-1 : ℂ) ^ n‖ ≤ 2 * ‖μ - (n : ℂ) * (Real.pi : ℂ)‖ := by
  set ε := μ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have hσ := ksn017_neg_one_zpow_norm n
  have hσσ := ksn017_neg_one_zpow_sq n
  by_cases h0 : μ = (n : ℂ) * (Real.pi : ℂ)
  · have hv : Lib.sincAt n μ = (-1 : ℂ) ^ n := by
      unfold Lib.sincAt
      rw [if_pos h0, Real.cos_int_mul_pi]; push_cast; rfl
    rw [hv]
    refine ⟨by intro h; rw [h, norm_zero] at hσ; norm_num at hσ, ?_⟩
    have : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
      exact inv_eq_of_mul_eq_one_right hσσ
    rw [this, sub_self, norm_zero]; positivity
  · have hε0 : ε ≠ 0 := sub_ne_zero.mpr h0
    have hμ : μ = (n : ℂ) * (Real.pi : ℂ) + ε := by rw [hεdef]; ring
    have hv : Lib.sincAt n μ = (-1 : ℂ) ^ n * (Complex.sin ε / ε) := by
      unfold Lib.sincAt
      rw [if_neg h0, ← hεdef, hμ, ksn017_sin_shift]; ring
    set q := Complex.sin ε / ε with hq
    have hε1 : ‖ε‖ ≤ 1 := by linarith
    have hb := Complex.sin_bound hε1
    have hεp : 0 < ‖ε‖ := norm_pos_iff.mpr hε0
    -- ‖sin ε - ε‖ ≤ ‖ε‖^3/6 + ‖ε‖^5/100 ≤ ‖ε‖^3/4
    have hse : ‖Complex.sin ε - ε‖ ≤ ‖ε‖ ^ 3 / 4 := by
      have e : Complex.sin ε - ε = (Complex.sin ε - (ε - ε ^ 3 / 6)) - ε ^ 3 / 6 := by ring
      rw [e]
      refine (norm_sub_le _ _).trans ?_
      have h6 : ‖ε ^ 3 / 6‖ = ‖ε‖ ^ 3 / 6 := by rw [norm_div, norm_pow]; norm_num
      rw [h6]
      have h5 : ‖ε‖ ^ 5 ≤ ‖ε‖ ^ 3 := pow_le_pow_of_le_one (norm_nonneg _) hε1 (by norm_num)
      have : 0 ≤ ‖ε‖ ^ 3 := by positivity
      linarith
    have hq1 : ‖q - 1‖ ≤ ‖ε‖ ^ 2 / 4 := by
      have e : q - 1 = (Complex.sin ε - ε) / ε := by rw [hq]; field_simp
      rw [e, norm_div, div_le_iff₀ hεp]
      calc ‖Complex.sin ε - ε‖ ≤ ‖ε‖ ^ 3 / 4 := hse
        _ = ‖ε‖ ^ 2 / 4 * ‖ε‖ := by ring
    have hq14 : ‖q - 1‖ ≤ 1 / 16 := by
      refine hq1.trans ?_
      have : ‖ε‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg ε]
      linarith
    have hqn : (1 : ℝ) / 2 ≤ ‖q‖ := by
      have := norm_sub_norm_le (1 : ℂ) q
      rw [norm_one, norm_sub_rev] at this
      linarith
    have hq0 : q ≠ 0 := by intro h; rw [h, norm_zero] at hqn; norm_num at hqn
    have hσ0 : (-1 : ℂ) ^ n ≠ 0 := by intro h; rw [h, norm_zero] at hσ; norm_num at hσ
    rw [hv]
    refine ⟨mul_ne_zero hσ0 hq0, ?_⟩
    have hinv : ((-1 : ℂ) ^ n * q)⁻¹ - (-1 : ℂ) ^ n = (-1 : ℂ) ^ n * ((1 - q) / q) := by
      have : ((-1 : ℂ) ^ n)⁻¹ = (-1 : ℂ) ^ n := by
        exact inv_eq_of_mul_eq_one_right hσσ
      rw [mul_inv, this]; field_simp
    rw [hinv, norm_mul, hσ, one_mul, norm_div, norm_sub_rev, div_le_iff₀ (by linarith)]
    have h2 : ‖ε‖ ^ 2 / 4 ≤ ‖ε‖ := by nlinarith
    nlinarith

/-- The perturbation comparing the critical point with the free lattice point. -/
def ksn017Beta (n : ℤ) (φ : PotPair) (μ : ℂ) (k : ℤ) : ℂ :=
  if k = n then 0 else -((lamDot φ k - (k : ℂ) * Real.pi) / (lamDot φ k - μ))

/-- The exact product identity `P · criticalOmittedProduct · ∏(1+β) = π_n · sincAt n μ`. -/
theorem ksn017_prod_eq (n : ℤ) (φ : PotPair) (μ : ℂ)
    (hf : Multipliable (fun k => a5OmittedRootFactor38 n k (φ, μ)) (symmetricIcc ℤ))
    (hF : Multipliable (fun k => criticalOmittedFactor n k φ μ))
    (hS : ∀ k, k ≠ n → stdRoot38 (tauN φ k) (gamma2 φ k) μ ≠ 0)
    (hD : ∀ k, k ≠ n → lamDot φ k - μ ≠ 0)
    (hβ : Multipliable (fun k => 1 + ksn017Beta n φ μ k)) :
    a5OmittedRootProduct38 n (φ, μ) * criticalOmittedProduct n φ μ *
        (∏' k, (1 + ksn017Beta n φ μ k)) = (Lib.piN n : ℂ) * Lib.sincAt n μ := by
  have h1 := hf.hasProd
  have h2 := hF.hasProd.mono_left (symmetricIcc ℤ).le_atTop
  have h3 := hβ.hasProd.mono_left (symmetricIcc ℤ).le_atTop
  have h4 := (h1.mul h2).mul h3
  have he : (fun k => a5OmittedRootFactor38 n k (φ, μ) * criticalOmittedFactor n k φ μ *
      (1 + ksn017Beta n φ μ k)) =
      fun k => if k = n then 1 else Lib.prodFactor (Lib.sigmaOf (0 : Lib.L2Seq)) μ k := by
    funext k
    by_cases hk : k = n
    · simp [hk, a5OmittedRootFactor38, criticalOmittedFactor, ksn017Beta]
    · have hs := hS k hk
      have hd := hD k hk
      have hp : (Lib.piN k : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero k
      simp only [a5OmittedRootFactor38, criticalOmittedFactor, ksn017Beta, if_neg hk, rootFactor38,
        Lib.prodFactor, Lib.sigmaOf_zero_eq, Lib.sigmaZero]
      field_simp
      ring
  rw [he] at h4
  have hv : (Lib.piN n : ℂ) * Lib.sincAt n μ =
      ∏'[symmetricIcc ℤ] k : ℤ, (if k = n then 1 else Lib.prodFactor (Lib.sigmaOf (0 : Lib.L2Seq)) μ k) := by
    rw [← Lib.omitProd_zero_eq_sincAt, Lib.omitProd]
    have hp : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
    field_simp
  rw [hv, h4.tprod_eq]
  rfl

theorem ksn017_natAbs_le_japanese (n : ℤ) : (n.natAbs : ℝ) ≤ japaneseBracket n := by
  unfold japaneseBracket
  rw [NlsGge.Atomic.KSN016.natAbs_cast]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

/-- Separation from the nth label: `|k - n| ≥ m/2` when `|k| < K` and `2K ≤ m = |n|`. -/
theorem ksn017_half_le (K : ℕ) (n k : ℤ) (hk : k.natAbs < K) (hn : 2 * K ≤ n.natAbs) :
    (n.natAbs : ℝ) / 2 ≤ |((k - n : ℤ) : ℝ)| := by
  have h1 : (n.natAbs : ℝ) ≤ (k.natAbs : ℝ) + ((k - n).natAbs : ℝ) := by
    have : n.natAbs ≤ k.natAbs + (k - n).natAbs := by omega
    exact_mod_cast this
  have h2 : (k.natAbs : ℝ) + 1 ≤ K := by exact_mod_cast hk
  have h3 : (2 * K : ℝ) ≤ n.natAbs := by exact_mod_cast hn
  rw [← NlsGge.Atomic.KSN016.natAbs_cast]
  linarith

/-- Assembly of the β-sums from the tail `t` (KSN-016) and a finitely supported part `s`. -/
theorem ksn017_beta_assembly (β t s : ℤ → ℂ) (hβ : ∀ k, β k = -t k + s k) (T : Finset ℤ)
    (hsupp : ∀ k ∉ T, s k = 0) (b m C16 : ℝ) (hm0 : 0 < m) (hb : 0 ≤ b) (hs : ∀ k, ‖s k‖ ≤ b / m)
    (hts : Summable t) (hts2 : Summable fun k => ‖t k‖ ^ 2)
    (htsum : ‖∑' k, t k‖ ≤ C16 / m) (htsq : ∑' k, ‖t k‖ ^ 2 ≤ C16 / m ^ 2) :
    Summable β ∧ Summable (fun k => ‖β k‖ ^ 2) ∧
      ‖∑' k, β k‖ ≤ (C16 + (T.card : ℝ) * b) / m ∧
      ∑' k, ‖β k‖ ^ 2 ≤ (2 * C16 + 2 * (T.card : ℝ) * b ^ 2) / m ^ 2 := by
  have hβf : β = fun k => -t k + s k := funext hβ
  have hsS : Summable s := summable_of_ne_finset_zero hsupp
  have hsupp2 : ∀ k ∉ T, ‖s k‖ ^ 2 = 0 := fun k hk => by rw [hsupp k hk, norm_zero]; ring
  have hsS2 : Summable fun k => ‖s k‖ ^ 2 := summable_of_ne_finset_zero hsupp2
  have hpt2 : ∀ k, ‖β k‖ ^ 2 ≤ 2 * ‖t k‖ ^ 2 + 2 * ‖s k‖ ^ 2 := by
    intro k
    rw [hβ]
    have h := norm_add_le (-t k) (s k)
    rw [norm_neg] at h
    have h2 : ‖-t k + s k‖ ^ 2 ≤ (‖t k‖ + ‖s k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    have h3 : (‖t k‖ + ‖s k‖) ^ 2 ≤ 2 * ‖t k‖ ^ 2 + 2 * ‖s k‖ ^ 2 := by
      generalize ‖t k‖ = u; generalize ‖s k‖ = v
      nlinarith [sq_nonneg (u - v)]
    exact h2.trans h3
  have hmaj : Summable fun k => 2 * ‖t k‖ ^ 2 + 2 * ‖s k‖ ^ 2 :=
    (hts2.mul_left 2).add (hsS2.mul_left 2)
  have hbS2 : Summable fun k => ‖β k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hpt2 hmaj
  have hssum : ‖∑' k, s k‖ ≤ (T.card : ℝ) * b / m := by
    rw [tsum_eq_sum (s := T) (fun k hk => hsupp k hk)]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun k _ => hs k)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_div_assoc]
  have hssq : ∑' k, ‖s k‖ ^ 2 ≤ (T.card : ℝ) * b ^ 2 / m ^ 2 := by
    rw [tsum_eq_sum (s := T) (fun k hk => hsupp2 k hk)]
    have : ∀ k ∈ T, ‖s k‖ ^ 2 ≤ (b / m) ^ 2 := fun k _ =>
      pow_le_pow_left₀ (norm_nonneg _) (hs k) 2
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, div_pow, mul_div_assoc]
  refine ⟨by rw [hβf]; exact hts.neg.add hsS, hbS2, ?_, ?_⟩
  · rw [hβf, hts.neg.tsum_add hsS, tsum_neg]
    refine (norm_add_le _ _).trans ?_
    rw [norm_neg, add_div]
    exact add_le_add htsum hssum
  · refine (hbS2.tsum_le_tsum hpt2 hmaj).trans ?_
    rw [(hts2.mul_left 2).tsum_add (hsS2.mul_left 2), tsum_mul_left, tsum_mul_left]
    have e : (2 * C16 + 2 * (T.card : ℝ) * b ^ 2) / m ^ 2 =
        2 * (C16 / m ^ 2) + 2 * ((T.card : ℝ) * b ^ 2 / m ^ 2) := by ring
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left htsq (show (0 : ℝ) ≤ 2 by norm_num)
    have h2 := mul_le_mul_of_nonneg_left hssq (show (0 : ℝ) ≤ 2 by norm_num)
    linarith

/-- Inverting the product identity. -/
theorem ksn017_invert (P x y s p : ℂ) (hid : P * x * y = p * s) (hp : p ≠ 0) (hs : s ≠ 0) :
    P ≠ 0 ∧ P / p ≠ 0 ∧ (P / p)⁻¹ = x * y * s⁻¹ := by
  have hP0 : P ≠ 0 := by
    intro h; rw [h, zero_mul, zero_mul] at hid
    exact mul_ne_zero hp hs hid.symm
  refine ⟨hP0, div_ne_zero hP0 hp, ?_⟩
  rw [inv_div]
  field_simp
  linear_combination -hid

/-- The final three-factor error estimate. -/
theorem ksn017_combine (x y w σ : ℂ) (a d e m : ℝ) (hm0 : 0 < m) (ha : 0 ≤ a)
    (hσ : ‖σ‖ = 1) (hx : ‖x - 1‖ ≤ a / m) (hy : ‖y - 1‖ ≤ d / m) (hw : ‖w - σ‖ ≤ e / m)
    (hd : d / m ≤ 1) (he : e / m ≤ 1) :
    ‖x * y * w - σ‖ ≤ (4 * a + 2 * d + e) / m := by
  have hyn : ‖y‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' y 1
    rw [norm_one] at this; linarith
  have hwn : ‖w‖ ≤ 2 := by
    have := norm_le_norm_add_norm_sub' w σ
    linarith
  have e1 : x * y * w - σ = (x - 1) * y * w + (y - 1) * w + (w - σ) := by ring
  rw [e1]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_mul, norm_mul, norm_mul]
  have ham : 0 ≤ a / m := by positivity
  have t1 : ‖x - 1‖ * ‖y‖ * ‖w‖ ≤ a / m * 2 * 2 :=
    mul_le_mul (mul_le_mul hx hyn (norm_nonneg _) ham) hwn (norm_nonneg _) (by positivity)
  have t2 : ‖y - 1‖ * ‖w‖ ≤ d / m * 2 :=
    mul_le_mul hy hwn (norm_nonneg _) ((norm_nonneg _).trans hy)
  have e2 : (4 * a + 2 * d + e) / m = a / m * 2 * 2 + d / m * 2 + e / m := by ring
  rw [e2]
  linarith

/-- A small label k (|k| < K, |n| ≥ 2K) contributes O(1/|n|). -/
theorem ksn017_small_term (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ) (hg : IsolatingGeometry38 C R c J)
    (K : ℕ) (n k : ℤ) (hk : k.natAbs < K) (hkn : k ≠ n) (hn : 2 * K ≤ n.natAbs)
    (lam μ : ℂ) (hlam : lam ∈ ball (C k) (R k)) (hμ : μ ∈ closedBall (C n) (R n))
    (M : ℝ) (hM0 : 0 ≤ M) (hnum : ‖lam - (k : ℂ) * Real.pi‖ ≤ M) :
    ‖-((lam - (k : ℂ) * Real.pi) / (lam - μ))‖ ≤ 2 * c * M / (n.natAbs : ℝ) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hm1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := by
    have : 1 ≤ n.natAbs := by omega
    exact_mod_cast this
  have hhalf := ksn017_half_le K n k hk hn
  have hden : c⁻¹ * ((n.natAbs : ℝ) / 2) ≤ ‖lam - μ‖ :=
    (mul_le_mul_of_nonneg_left hhalf (inv_nonneg.mpr hc0.le)).trans (ksn013_sep C R c J hg hkn hlam hμ)
  have hdenp : 0 < c⁻¹ * ((n.natAbs : ℝ) / 2) := by positivity
  rw [norm_neg, norm_div]
  calc ‖lam - (k : ℂ) * Real.pi‖ / ‖lam - μ‖ ≤ M / (c⁻¹ * ((n.natAbs : ℝ) / 2)) :=
        div_le_div₀ hM0 hnum hdenp hden
    _ = 2 * c * M / (n.natAbs : ℝ) := by field_simp

/-- First-order bound for the critical points from the midpoint bound and λ̇ - τ = γ²a. -/
theorem ksn017_lam_first (φ : PotPair) (hφ : φ ∈ gkW) (Aa Γ Bm : ℝ) (c₁ : ℂ)
    (ha : ∀ k, ‖a5CriticalA38 k φ‖ ≤ Aa) (hΓ : ∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ Γ)
    (hmid : ∀ k : ℤ, k ≠ 0 → ‖tauN φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ Bm / (k.natAbs : ℝ) ^ 2)
    (k : ℤ) (hk : k ≠ 0) :
    ‖lamDot φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤
      (max Bm 0 + max Γ 0 * max Aa 0 + 1) / (k.natAbs : ℝ) ^ 2 := by
  have hk1 : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hk
  have hk2 : (0 : ℝ) < (k.natAbs : ℝ) ^ 2 := by positivity
  have hΓ0 : 0 ≤ max Γ 0 := le_max_right _ _
  have hAa0 : 0 ≤ max Aa 0 := le_max_right _ _
  have hid := a5CriticalA_identity38 k φ hφ
  have e : lamDot φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ) =
      (tauN φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)) + gamma2 φ k * a5CriticalA38 k φ := by
    rw [← hid]; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hg2 : ‖gamma2 φ k * a5CriticalA38 k φ‖ ≤ max Γ 0 * max Aa 0 / (k.natAbs : ℝ) ^ 2 := by
    rw [norm_mul, le_div_iff₀ hk2]
    have hjb : (k.natAbs : ℝ) ^ 2 ≤ japaneseBracket k ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (ksn017_natAbs_le_japanese k) 2
    have hγ : (k.natAbs : ℝ) ^ 2 * ‖gamma2 φ k‖ ≤ max Γ 0 :=
      (mul_le_mul_of_nonneg_right hjb (norm_nonneg _)).trans ((hΓ k).trans (le_max_left _ _))
    have hA : ‖a5CriticalA38 k φ‖ ≤ max Aa 0 := (ha k).trans (le_max_left _ _)
    calc ‖gamma2 φ k‖ * ‖a5CriticalA38 k φ‖ * (k.natAbs : ℝ) ^ 2
        = ((k.natAbs : ℝ) ^ 2 * ‖gamma2 φ k‖) * ‖a5CriticalA38 k φ‖ := by ring
      _ ≤ max Γ 0 * max Aa 0 := mul_le_mul hγ hA (norm_nonneg _) hΓ0
  have hm1' : ‖tauN φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ max Bm 0 / (k.natAbs : ℝ) ^ 2 :=
    (hmid k hk).trans (div_le_div_of_nonneg_right (le_max_left _ _) hk2.le)
  calc _ ≤ max Bm 0 / (k.natAbs : ℝ) ^ 2 + max Γ 0 * max Aa 0 / (k.natAbs : ℝ) ^ 2 :=
        add_le_add hm1' hg2
    _ ≤ (max Bm 0 + max Γ 0 * max Aa 0 + 1) / (k.natAbs : ℝ) ^ 2 := by
        rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hk2.le

/-- Bound of the critical points near the lattice for every label. -/
theorem ksn017_lam_near (C : ℤ → ℂ) (R : ℤ → ℝ) (B16 : ℝ) (hB : 0 ≤ B16) (c₁ : ℂ) (hc₁ : ‖c₁‖ ≤ B16)
    (lam : ℤ → ℂ) (h0 : lam 0 ∈ ball (C 0) (R 0))
    (h1 : ∀ k : ℤ, k ≠ 0 → ‖lam k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ B16 / (k.natAbs : ℝ) ^ 2)
    (k : ℤ) : ‖lam k - (k : ℂ) * Real.pi‖ ≤ 2 * B16 + ‖C 0‖ + R 0 := by
  have hR : 0 ≤ R 0 := by
    rw [mem_ball] at h0; exact (dist_nonneg).trans h0.le
  by_cases hk0 : k = 0
  · subst hk0
    rw [mem_ball, dist_eq_norm] at h0
    have : lam 0 - ((0 : ℤ) : ℂ) * Real.pi = (lam 0 - C 0) + C 0 := by simp
    rw [this]
    refine (norm_add_le _ _).trans ?_
    linarith
  · have hk1 : (1 : ℝ) ≤ (k.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hk0
    have hb1 : B16 / (k.natAbs : ℝ) ^ 2 ≤ B16 := div_le_self hB (by nlinarith)
    have hb2 : ‖c₁ / (k : ℂ)‖ ≤ B16 := by
      rw [norm_div, Complex.norm_intCast, ← NlsGge.Atomic.KSN016.natAbs_cast]
      exact (div_le_self (norm_nonneg _) hk1).trans hc₁
    have e : lam k - (k : ℂ) * Real.pi = (lam k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)) + c₁ / (k : ℂ) := by
      ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := h1 k hk0
    have : 0 ≤ ‖C 0‖ := norm_nonneg _
    linarith


/-- The β-product for one label n (tail from KSN-016, finitely many small labels). -/
theorem ksn017_beta_prod (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ) (hg : IsolatingGeometry38 C R c J)
    (φ : PotPair) (n : ℤ) (K : ℕ) (C16 M b κ D : ℝ) (hC16 : 0 ≤ C16) (hM0 : 0 ≤ M)
    (hb : b = 2 * c * M) (hb0 : 0 ≤ b)
    (hκ : κ = ((Finset.Ioo (-(K : ℤ)) K).card : ℝ)) (hκ0 : 0 ≤ κ)
    (hD : D = (C16 + κ * b) + (2 * C16 + 2 * κ * b ^ 2))
    (hm0 : (0 : ℝ) < (n.natAbs : ℝ)) (hmbig : 4 * D + 1 ≤ (n.natAbs : ℝ)) (hn2K : 2 * K ≤ n.natAbs)
    (hμc : muSeq φ n ∈ closedBall (C n) (R n)) (hlam : ∀ k, lamDot φ k ∈ ball (C k) (R k))
    (hnear : ∀ k : ℤ, ‖lamDot φ k - (k : ℂ) * Real.pi‖ ≤ M)
    (hts : Summable (midpointRatioTail K (lamDot φ) (muSeq φ n) n))
    (hts2 : Summable fun k => ‖midpointRatioTail K (lamDot φ) (muSeq φ n) n k‖ ^ 2)
    (htsum : ‖∑' k, midpointRatioTail K (lamDot φ) (muSeq φ n) n k‖ ≤ C16 / (n.natAbs : ℝ))
    (htsq : ∑' k, ‖midpointRatioTail K (lamDot φ) (muSeq φ n) n k‖ ^ 2 ≤ C16 / (n.natAbs : ℝ) ^ 2) :
    Multipliable (fun k => 1 + ksn017Beta n φ (muSeq φ n) k) ∧
      ‖(∏' k, (1 + ksn017Beta n φ (muSeq φ n) k)) - 1‖ ≤ 2 * (D / (n.natAbs : ℝ)) := by
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  -- β = -t + s
  have hβeq : ∀ k, ksn017Beta n φ (muSeq φ n) k =
      -midpointRatioTail K (lamDot φ) (muSeq φ n) n k +
        (if k.natAbs < K ∧ k ≠ n then
          -((lamDot φ k - (k : ℂ) * Real.pi) / (lamDot φ k - muSeq φ n)) else 0) := by
    intro k
    simp only [ksn017Beta, midpointRatioTail]
    by_cases hkn : k = n
    · simp [hkn]
    · by_cases hK : K ≤ k.natAbs
      · have h1 : ¬ (k.natAbs < K ∧ k ≠ n) := by omega
        rw [if_neg hkn, if_pos ⟨hK, hkn⟩, if_neg h1]
        ring
      · have h1 : k.natAbs < K ∧ k ≠ n := ⟨by omega, hkn⟩
        have h2 : ¬ (K ≤ k.natAbs ∧ k ≠ n) := by omega
        rw [if_neg hkn, if_neg h2, if_pos h1]
        ring
  have hsupp : ∀ k ∉ Finset.Ioo (-(K : ℤ)) K, (if k.natAbs < K ∧ k ≠ n then
      -((lamDot φ k - (k : ℂ) * Real.pi) / (lamDot φ k - muSeq φ n)) else (0 : ℂ)) = 0 := by
    intro k hk
    have : ¬ (k.natAbs < K ∧ k ≠ n) := by
      rintro ⟨h1, -⟩
      apply hk
      rw [Finset.mem_Ioo]
      omega
    rw [if_neg this]
  have hsb : ∀ k, ‖(if k.natAbs < K ∧ k ≠ n then
      -((lamDot φ k - (k : ℂ) * Real.pi) / (lamDot φ k - muSeq φ n)) else (0 : ℂ))‖ ≤
        b / (n.natAbs : ℝ) := by
    intro k
    by_cases hk : k.natAbs < K ∧ k ≠ n
    · rw [if_pos hk, hb]
      exact ksn017_small_term C R c J hg K n k hk.1 hk.2 hn2K (lamDot φ k) (muSeq φ n) (hlam k) hμc
        M hM0 (hnear k)
    · rw [if_neg hk, norm_zero]; positivity
  obtain ⟨hbS, hbS2, hb1, hb2⟩ := ksn017_beta_assembly (ksn017Beta n φ (muSeq φ n))
    (midpointRatioTail K (lamDot φ) (muSeq φ n) n) _ hβeq (Finset.Ioo (-(K : ℤ)) K) hsupp
    b (n.natAbs : ℝ) C16 hm0 hb0 hsb hts hts2 htsum htsq
  rw [← hκ] at hb1 hb2
  have hm1 : (1 : ℝ) ≤ (n.natAbs : ℝ) := by linarith
  have hs12 : (C16 + κ * b) / (n.natAbs : ℝ) + (2 * C16 + 2 * κ * b ^ 2) / (n.natAbs : ℝ) ^ 2 ≤
      D / (n.natAbs : ℝ) := by
    have h2 : (2 * C16 + 2 * κ * b ^ 2) / (n.natAbs : ℝ) ^ 2 ≤
        (2 * C16 + 2 * κ * b ^ 2) / (n.natAbs : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hm0 (by nlinarith)
    rw [hD, add_div (C16 + κ * b)]
    linarith
  have hDm : D / (n.natAbs : ℝ) ≤ 1 / 4 := by
    rw [div_le_iff₀ hm0]; nlinarith
  have hhalfβ : ∀ k, ‖ksn017Beta n φ (muSeq φ n) k‖ ≤ 1 / 2 := by
    intro k
    have h1 : ‖ksn017Beta n φ (muSeq φ n) k‖ ^ 2 ≤
        (2 * C16 + 2 * κ * b ^ 2) / (n.natAbs : ℝ) ^ 2 := by
      have := hbS2.sum_le_tsum {k} (fun j _ => sq_nonneg _)
      rw [Finset.sum_singleton] at this
      exact this.trans hb2
    have hs1n : 0 ≤ (C16 + κ * b) / (n.natAbs : ℝ) := by positivity
    have h2 : ‖ksn017Beta n φ (muSeq φ n) k‖ ^ 2 ≤ (1 / 2) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) (by norm_num)).mp h2
  obtain ⟨hβm, hy⟩ := ksn017_signed_prod (ksn017Beta n φ (muSeq φ n)) hbS hbS2 hhalfβ _ _ hb1 hb2
    (by linarith)
  exact ⟨hβm, hy.trans (mul_le_mul_of_nonneg_left hs12 (by norm_num))⟩

/-- The KSN-017 estimate for one common geometry and uniform bounds (PotPair level), large labels. -/
theorem ksn017_core (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (J : ℕ)
    (hg : IsolatingGeometry38 C R c J) (Aa Γ Bm : ℝ) :
    ∃ (N₀ : ℕ) (C₀ : ℝ), 1 ≤ N₀ ∧ 0 ≤ C₀ ∧
      ∀ φ : PotPair, φ ∈ gkW → IsolatingSpectral38 φ C R →
      (∀ k, ‖a5CriticalA38 k φ‖ ≤ Aa) → (∀ k, japaneseBracket k ^ 2 * ‖gamma2 φ k‖ ≤ Γ) →
      ∀ c₁ : ℂ, ‖c₁‖ ≤ Bm →
      (∀ k : ℤ, k ≠ 0 → ‖tauN φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ Bm / (k.natAbs : ℝ) ^ 2) →
      (∀ n : ℤ, n ≠ 0 → ‖muSeq φ n - (n : ℂ) * Real.pi‖ ≤ Bm / (n.natAbs : ℝ)) →
      ∀ n : ℤ, N₀ ≤ n.natAbs →
        Multipliable (fun k => a5OmittedRootFactor38 n k (φ, muSeq φ n)) (symmetricIcc ℤ) →
        deltaFactor n φ (muSeq φ n) ≠ 0 ∧
        ‖(deltaFactor n φ (muSeq φ n))⁻¹ - (-1 : ℂ) ^ n‖ ≤ C₀ / (n.natAbs : ℝ) := by
  obtain ⟨A₀, hA₀, hdisc⟩ := ksn013_disc_estimate C R c J hg Aa Γ
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  obtain ⟨Bm', hBm'⟩ : ∃ b : ℝ, b = max Bm 0 := ⟨_, rfl⟩
  have hBm0 : 0 ≤ Bm' := hBm' ▸ le_max_right _ _
  have hBmle : Bm ≤ Bm' := hBm' ▸ le_max_left _ _
  obtain ⟨B16, hB16⟩ : ∃ b : ℝ, b = max Bm 0 + max Γ 0 * max Aa 0 + 1 := ⟨_, rfl⟩
  have hGA : 0 ≤ max Γ 0 * max Aa 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hB16p : 0 < B16 := by rw [hB16]; positivity
  have hBB : Bm' ≤ B16 := by rw [hB16, ← hBm']; linarith
  obtain ⟨K, N16, C16, hK1, hKN, hC16, h16⟩ := KSN016_main B16 hB16p
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * B16 + ‖C 0‖ + R 0 := ⟨_, rfl⟩
  have hR0 : 0 < R 0 := (hg.1 0).1
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = ((Finset.Ioo (-(K : ℤ)) K).card : ℝ) := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := hκ ▸ Nat.cast_nonneg _
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 2 * c * M := ⟨_, rfl⟩
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (C16 + κ * b) + (2 * C16 + 2 * κ * b ^ 2) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  refine ⟨N16 + 2 * K + ⌈4 * D + 2 * Bm' + A₀⌉₊ + 1, 4 * A₀ + 2 * (2 * D) + 2 * Bm',
    by omega, by positivity, ?_⟩
  intro φ hφ hsp ha hΓ c₁ hc₁ hmid hmu n hn hf
  have hceil := Nat.le_ceil (4 * D + 2 * Bm' + A₀)
  have hmbig : 4 * D + 2 * Bm' + A₀ + 1 ≤ (n.natAbs : ℝ) := by
    have h1 : ((N16 + 2 * K + ⌈4 * D + 2 * Bm' + A₀⌉₊ + 1 : ℕ) : ℝ) ≤ (n.natAbs : ℝ) :=
      Nat.cast_le.mpr hn
    push_cast at h1
    have : (0 : ℝ) ≤ N16 + 2 * K := by positivity
    linarith
  have hm0 : (0 : ℝ) < (n.natAbs : ℝ) := by linarith
  have hn0 : n ≠ 0 := by intro h; rw [h] at hm0; simp at hm0
  have hn16 : N16 ≤ n.natAbs := by omega
  have hn2K : 2 * K ≤ n.natAbs := by omega
  have hμb : muSeq φ n ∈ ball (C n) (R n) := (hsp.1 n).2.1
  have hμc : muSeq φ n ∈ closedBall (C n) (R n) := ball_subset_closedBall hμb
  obtain ⟨hFm, hS, hx⟩ := hdisc φ hφ hsp ha hΓ n (muSeq φ n) hμc
  have hlam : ∀ k, lamDot φ k ∈ ball (C k) (R k) := fun k => (hsp.1 k).2.2.2.1
  have hDne : ∀ k, k ≠ n → lamDot φ k - muSeq φ n ≠ 0 := by
    intro k hk h
    have h1 := ksn013_sep C R c J hg hk (hlam k) hμc
    rw [h, norm_zero] at h1
    have h2 := ksn013_one_le_abs hk
    have : 0 < c⁻¹ * |((k - n : ℤ) : ℝ)| := mul_pos (inv_pos.mpr hc0) (by linarith)
    linarith
  have hlam1 : ∀ k : ℤ, k ≠ 0 →
      ‖lamDot φ k - (k : ℂ) * Real.pi - c₁ / (k : ℂ)‖ ≤ B16 / (k.natAbs : ℝ) ^ 2 := by
    intro k hk
    rw [hB16]; exact ksn017_lam_first φ hφ Aa Γ Bm c₁ ha hΓ hmid k hk
  have hc₁' : ‖c₁‖ ≤ B16 := by linarith
  have hmu' : ∀ j : ℤ, N16 ≤ j.natAbs → ‖muSeq φ j - (j : ℂ) * Real.pi‖ ≤ B16 / (j.natAbs : ℝ) := by
    intro j hj
    have hj0 : j ≠ 0 := by intro h; rw [h] at hj; simp at hj; omega
    have hjp : (0 : ℝ) < (j.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hj0
    exact (hmu j hj0).trans (div_le_div_of_nonneg_right (by linarith) hjp.le)
  obtain ⟨-, hts, hts2, htsum, htsq⟩ := h16 (lamDot φ) (muSeq φ) c₁ hc₁'
    (fun k hk => hlam1 k (by intro h; rw [h] at hk; simp at hk; omega)) hmu' n hn16
  have hnear := ksn017_lam_near C R B16 hB16p.le c₁ hc₁' (lamDot φ) (hlam 0) hlam1
  obtain ⟨hβm, hy⟩ := ksn017_beta_prod C R c J hg φ n K C16 M b κ D hC16 hM0 hb hb0 hκ hκ0 hD hm0
    (by linarith) hn2K hμc hlam (fun k => hM ▸ hnear k) hts hts2 htsum htsq
  have hε : ‖muSeq φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ Bm' / (n.natAbs : ℝ) :=
    (hmu n hn0).trans (div_le_div_of_nonneg_right hBmle hm0.le)
  have hεh : Bm' / (n.natAbs : ℝ) ≤ 1 / 2 := by rw [div_le_iff₀ hm0]; nlinarith
  obtain ⟨hsinc0, hw⟩ := ksn017_sinc_inv n (muSeq φ n) (hε.trans hεh)
  have hid := ksn017_prod_eq n φ (muSeq φ n) hf hFm hS hDne hβm
  have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
  obtain ⟨-, hδ0, hinv⟩ := ksn017_invert _ _ _ _ _ hid hpi hsinc0
  refine ⟨hδ0, ?_⟩
  change ‖(a5OmittedRootProduct38 n (φ, muSeq φ n) / (Lib.piN n : ℂ))⁻¹ - (-1 : ℂ) ^ n‖ ≤ _
  rw [hinv]
  have hx' : ‖criticalOmittedProduct n φ (muSeq φ n) - 1‖ ≤ A₀ / (n.natAbs : ℝ) :=
    hx.trans (div_le_div_of_nonneg_left hA₀ hm0 (ksn017_natAbs_le_japanese n))
  have hy' : ‖(∏' k, (1 + ksn017Beta n φ (muSeq φ n) k)) - 1‖ ≤ (2 * D) / (n.natAbs : ℝ) :=
    hy.trans (le_of_eq (mul_div_assoc _ _ _).symm)
  have hw' : ‖(Lib.sincAt n (muSeq φ n))⁻¹ - (-1 : ℂ) ^ n‖ ≤ 2 * Bm' / (n.natAbs : ℝ) :=
    hw.trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left hε (by norm_num)) (mul_div_assoc _ _ _).symm)
  have hdm : 2 * D / (n.natAbs : ℝ) ≤ 1 := (div_le_one hm0).mpr (by linarith)
  have hem : 2 * Bm' / (n.natAbs : ℝ) ≤ 1 := (div_le_one hm0).mpr (by linarith)
  exact ksn017_combine _ _ _ _ A₀ (2 * D) (2 * Bm') (n.natAbs : ℝ) hm0 hA₀
    (ksn017_neg_one_zpow_norm n) hx' hy' hw' hdm hem

end
end NlsGge.ThirdConsultation.KSN
