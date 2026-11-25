import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS023Support
import NlsGge.ThirdConsultation.KSPS.KSPS017Host

                                                                                                                  
                                                                                                               
                                                                                                             
                                                                                                                  
                                                                                                                 
                           
                                                                                                     
                                                                                 
                                                                                                               
                                                                                                              
                                                                                                                 
                                                                                                                 
                                                                                                         
                                                                                
                                                                                                                 
                                                                                                             
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS024W
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W

/-! ### Pure lemmas -/

theorem crit_sine_identity (sε θp e IL Y sg : ℂ) (hsg : sg * sg = 1)
    (h : e = 0 - (-2 * (sg * sε) * θp + 2 * Complex.I * (-sg) / Y * IL)) :
    sε = -(Complex.I * IL / Y) + ((1 - θp) * sε + sg * e / 2) := by
  linear_combination (-(sg / 2)) * h + (-(sε * θp + Complex.I * IL / Y)) * hsg

theorem crit_product_identity (sε θp e IL Y sg : ℂ) (hsg : sg * sg = 1)
    (h : e = 0 - (-2 * (sg * sε) * θp + 2 * Complex.I * (-sg) / Y * IL)) :
    sε * θp = sg * e / 2 - Complex.I * IL / Y := by
  linear_combination (-(sg / 2)) * h + (-(sε * θp + Complex.I * IL / Y)) * hsg

def Lp {N : ℕ} (φ : SobolevC N) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * ‖integralRiccatiLeft φ k‖

theorem Lp_nonneg {N : ℕ} (φ : SobolevC N) : 0 ≤ Lp φ :=
  Finset.sum_nonneg (fun k _ => by positivity)

theorem phaseDerivative_sub_one_le {N : ℕ} (φ : SobolevC N) (lam : ℂ) (hlam : 1 ≤ ‖lam‖) :
    ‖KSPSWKB.phaseDerivative φ lam - 1‖ ≤ Lp φ / ‖lam‖ ^ 2 := by
  have hl0 : 0 < ‖lam‖ := by linarith
  unfold KSPSWKB.phaseDerivative
  rw [sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, one_mul, Lp, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  have h2 : ‖(2 * Complex.I) ^ (-(k : ℤ))‖ ≤ 1 := by
    rw [norm_zpow, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h3 : ‖lam ^ (-((k + 1 : ℕ) : ℤ))‖ ≤ 1 / ‖lam‖ ^ 2 := by
    rw [norm_zpow, zpow_neg, zpow_natCast, one_div]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hlam (by omega))
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast]
  calc (k : ℝ) * ‖(2 * Complex.I) ^ (-(k : ℤ))‖ * ‖lam ^ (-((k + 1 : ℕ) : ℤ))‖ *
        ‖integralRiccatiLeft φ k‖
      ≤ (k : ℝ) * 1 * (1 / ‖lam‖ ^ 2) * ‖integralRiccatiLeft φ k‖ := by gcongr
    _ = (k : ℝ) * ‖integralRiccatiLeft φ k‖ / ‖lam‖ ^ 2 := by ring

/-! ### Spectral facts at the critical root -/

theorem deriv_discriminant_crit {N : ℕ} (φ : SobolevC N) (n : ℤ) :
    deriv (discriminant φ) (criticalEigenvalue φ n) = 0 :=
  (lamDot_enumeration38 (toPotPair φ)).1 n

/-! ### Rough localization from the KSPS-019 head (an explicit hypothesis of exactly its landed type) -/

theorem crit_localization_of
    (h19 : ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        ∀ n : ℤ, N ≤ n.natAbs →
          ‖mu φ n-(n:ℂ)*Real.pi‖ +
          ‖criticalEigenvalue φ n-(n:ℂ)*Real.pi‖ ≤
            C/(n.natAbs:ℝ))
    {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n := by
  obtain ⟨φ', hφ'⟩ := NlsGge.ThirdConsultation.KSPS011Support4.exists_toPair_eq hN φ
  have hcr : ∀ n : ℤ, criticalEigenvalue φ' n = criticalEigenvalue φ n := by
    intro n
    unfold criticalEigenvalue
    rw [← hφ']
    rfl
  obtain ⟨C, N0, hC, h⟩ := h19 (|sobolevNorm 1 φ'| + 1) (by positivity)
  have h' := h φ' (by linarith [le_abs_self (sobolevNorm 1 φ')])
  set F : Finset ℤ := Finset.Icc (-((N0 + 1 : ℕ) : ℤ)) ((N0 + 1 : ℕ) : ℤ) with hF
  have hsum0 : 0 ≤ ∑ m ∈ F, ‖criticalEigenvalue φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m :=
    Finset.sum_nonneg (fun m _ => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (KSPS015W.one_le_w m)))
  refine ⟨2 * C + ∑ m ∈ F, ‖criticalEigenvalue φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m,
    add_nonneg (by linarith) hsum0, fun n => ?_⟩
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (KSPS015W.one_le_w n)
  by_cases hn : n ∈ F
  · have h1 : ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ * indexWeight n ≤
        2 * C + ∑ m ∈ F, ‖criticalEigenvalue φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m := by
      have := Finset.single_le_sum
        (f := fun m => ‖criticalEigenvalue φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m)
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
    rw [hcr n, hnR] at hb
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℕ) : ℝ) ≤ ((n.natAbs : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n.natAbs)
      rw [hnR] at this
      simpa using this
    have hpos : 0 < |(n : ℝ)| := by linarith
    have hw2 := KSPS015W.w_le_two n hn1
    have hc0 : 0 ≤ ‖mu φ' n - (n : ℂ) * (Real.pi : ℂ)‖ := norm_nonneg _
    have h2 : ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ C / |(n : ℝ)| := by linarith
    have h3 : C / |(n : ℝ)| ≤ 2 * C / indexWeight n := by
      rw [div_le_div_iff₀ hpos hw0]
      nlinarith
    have h4 : 2 * C / indexWeight n ≤
        (2 * C + ∑ m ∈ F, ‖criticalEigenvalue φ m - (m : ℂ) * (Real.pi : ℂ)‖ * indexWeight m) /
          indexWeight n :=
      div_le_div_of_nonneg_right (by linarith) hw0.le
    linarith

/-! ### Bounding sequences (literal abbreviations) -/

def critE (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℂ :=
  deriv (discriminant φ) (criticalEigenvalue φ n) -
    KSPSWKB.discriminantDerivativeMain N φ (criticalEigenvalue φ) n

def tauC (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  indexWeight n ^ (N + 1) * ‖critE N φ n‖ +
    2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)

def psiC (N : ℕ) (φ : SobolevC N) (n : ℤ) : ℝ :=
  (4 + 4 * Lp φ) * tauC N φ n + indexWeight n ^ (N + 1) * ‖critE N φ n‖ / 2

def boundC (N : ℕ) (φ : SobolevC N) (CT : ℝ) (n : ℤ) : ℝ :=
  psiC N φ n + Lsum φ * (2 * psiC N φ n) + CT * 2 ^ (N + 2) * (1 / indexWeight n)

/-! ### The tail estimate at one index -/

theorem tail024A (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈2 * Lp φ + 1⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tauC N φ n ≤ 1) :
    ∃ r2 : ℂ, indexWeight n ^ (N + 1) * ‖r2‖ ≤ psiC N φ n ∧
      criticalEigenvalue φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (criticalEigenvalue φ n)⁻¹ -
          (n : ℂ) * (Real.pi : ℂ) = r2 := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a (2 * Lp φ + 1) ha (criticalEigenvalue φ) hxi n h1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hLp0 := Lp_nonneg φ
  have hroot := deriv_discriminant_crit φ n
  set X : ℂ := criticalEigenvalue φ n with hXdef
  set θp : ℂ := KSPSWKB.phaseDerivative φ X with hθpdef
  set IL : ℂ := integralRiccatiLeft φ (N + 1) with hILdef
  set e : ℂ := critE N φ n with hedef
  -- theta' bounds
  have hθ1 := phaseDerivative_sub_one_le φ X hX1
  rw [← hθpdef] at hθ1
  have hX2 : ‖X‖ ≤ ‖X‖ ^ 2 := by nlinarith [hX1]
  have hθ2 : ‖θp - 1‖ ≤ 1 / 2 := by
    refine hθ1.trans ?_
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hθl : 1 / 2 ≤ ‖θp‖ := by
    have h := norm_sub_le θp (θp - 1)
    rw [sub_sub_cancel, norm_one] at h
    linarith
  have hθ4 : ‖1 - θp‖ ≤ 4 * Lp φ / indexWeight n ^ 2 := by
    rw [norm_sub_rev]
    refine hθ1.trans ?_
    have hw2 : indexWeight n ^ 2 ≤ 4 * ‖X‖ ^ 2 := by nlinarith [hwX, hw0]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hw2 hLp0]
  -- (1) the exact identity at the critical root
  obtain ⟨-, hsn⟩ := shift (NlsGge.ThirdConsultation.KSPS.wkbPhase φ X) n
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ X with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have hsg1 : (-1 : ℂ) ^ (n + 1) = -(-1 : ℂ) ^ n := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; ring
  have he : e = 0 - (-2 * ((-1 : ℂ) ^ n * Complex.sin ε) * θp +
      2 * Complex.I * (-(-1 : ℂ) ^ n) / (2 * Complex.I * X) ^ (N + 1) * IL) := by
    rw [hedef]
    unfold critE KSPSWKB.discriminantDerivativeMain
    rw [← hXdef, hroot, ← hθpdef, ← hθ, hsn, hsg1, ← hILdef]
  have hsi := crit_sine_identity (Complex.sin ε) θp e IL ((2 * Complex.I * X) ^ (N + 1))
    ((-1 : ℂ) ^ n) (neg_one_zpow_mul_self n) he
  have hpi := crit_product_identity (Complex.sin ε) θp e IL ((2 * Complex.I * X) ^ (N + 1))
    ((-1 : ℂ) ^ n) (neg_one_zpow_mul_self n) he
  -- the sine estimate
  have hY : ‖(2 * Complex.I * X) ^ (N + 1)‖ = (2 * ‖X‖) ^ (N + 1) := by
    rw [norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hX0 : 0 < ‖X‖ := by linarith
  have hYpos : 0 < (2 * ‖X‖) ^ (N + 1) := by positivity
  have hs : ‖Complex.sin ε‖ ≤ ‖e‖ + (0 + 0) + 2 * ‖IL‖ / (2 * ‖X‖) ^ (N + 1) := by
    have hr : ‖(-1 : ℂ) ^ n * e / 2 - Complex.I * IL / (2 * Complex.I * X) ^ (N + 1)‖ ≤
        ‖e‖ / 2 + ‖IL‖ / (2 * ‖X‖) ^ (N + 1) := by
      refine (norm_sub_le _ _).trans (le_of_eq ?_)
      rw [norm_div, norm_mul, norm_neg_one_zpow, one_mul, Complex.norm_ofNat, norm_div, norm_mul,
        Complex.norm_I, one_mul, hY]
    rw [← hpi, norm_mul] at hr
    have h6 : ‖Complex.sin ε‖ * (1 / 2) ≤ ‖Complex.sin ε‖ * ‖θp‖ :=
      mul_le_mul_of_nonneg_left hθl (norm_nonneg _)
    have h7 : 2 * ‖IL‖ / (2 * ‖X‖) ^ (N + 1) = 2 * (‖IL‖ / (2 * ‖X‖) ^ (N + 1)) := by ring
    rw [h7]
    linarith
  have hst : indexWeight n ^ N * ‖Complex.sin ε‖ ≤ tauC N φ n := by
    have h8 := tau_pure N (indexWeight n) ‖X‖ ‖e‖ 0 0 0 0 ‖IL‖ ‖Complex.sin ε‖ hw1 hwX (norm_nonneg _)
      (norm_nonneg _) (by simp) (by simp) hs
    unfold tauC
    rw [← hedef, ← hILdef]
    linarith
  -- eps is small
  have hε : ‖ε‖ ≤ 1 / 2 := by
    have := phase_small φ X n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    rw [hεdef, hθ]
    linarith
  have hεs := eps_le_two_sin ε hε
  have hss := norm_sin_sub_self_le ε (by linarith)
  -- (2) the remainder r2
  set r2 : ℂ := (ε - Complex.sin ε) + ((1 - θp) * Complex.sin ε + (-1 : ℂ) ^ n * e / 2) with hr2def
  have hr2 : indexWeight n ^ (N + 1) * ‖r2‖ ≤ psiC N φ n := by
    have hb : ‖r2‖ ≤ 4 * ‖Complex.sin ε‖ ^ 2 +
        4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖ + ‖e‖ / 2 := by
      have e1 : ‖ε - Complex.sin ε‖ ≤ 4 * ‖Complex.sin ε‖ ^ 2 := by
        rw [norm_sub_rev]
        refine hss.trans ?_
        calc ‖ε‖ ^ 2 ≤ (2 * ‖Complex.sin ε‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hεs 2
          _ = 4 * ‖Complex.sin ε‖ ^ 2 := by ring
      have e2 : ‖(1 - θp) * Complex.sin ε‖ ≤ 4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hθ4 (norm_nonneg _)
      have e3 : ‖(-1 : ℂ) ^ n * e / 2‖ = ‖e‖ / 2 := by
        rw [norm_div, norm_mul, norm_neg_one_zpow, one_mul, Complex.norm_ofNat]
      calc ‖r2‖ ≤ ‖ε - Complex.sin ε‖ +
            (‖(1 - θp) * Complex.sin ε‖ + ‖(-1 : ℂ) ^ n * e / 2‖) := by
            rw [hr2def]
            exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
        _ ≤ _ := by rw [e3]; linarith
    have hsq := sq_weight_le N hN (indexWeight n) ‖Complex.sin ε‖ (tauC N φ n) hw1 (norm_nonneg _) hst h5
    have hlin : indexWeight n ^ (N + 1) * (4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖) ≤
        4 * Lp φ * tauC N φ n := by
      have e : indexWeight n ^ (N + 1) * (4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖) =
          4 * Lp φ * (indexWeight n ^ N * ‖Complex.sin ε‖) / indexWeight n := by
        rw [pow_succ]
        field_simp
      rw [e]
      have h0 : 0 ≤ 4 * Lp φ * (indexWeight n ^ N * ‖Complex.sin ε‖) :=
        mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hw0.le _) (norm_nonneg _))
      refine (div_le_self h0 hw1).trans ?_
      exact mul_le_mul_of_nonneg_left hst (by linarith)
    have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
    have h6 := mul_le_mul_of_nonneg_left hb hwp
    have e : indexWeight n ^ (N + 1) * (4 * ‖Complex.sin ε‖ ^ 2 +
        4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖ + ‖e‖ / 2) =
        4 * (indexWeight n ^ (N + 1) * ‖Complex.sin ε‖ ^ 2) +
          indexWeight n ^ (N + 1) * (4 * Lp φ / indexWeight n ^ 2 * ‖Complex.sin ε‖) +
          indexWeight n ^ (N + 1) * ‖e‖ / 2 := by ring
    rw [e] at h6
    unfold psiC
    rw [← hedef]
    linarith
  -- g(lamDot) - n pi = r2
  have hg : X + KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ - (n : ℂ) * (Real.pi : ℂ) = r2 := by
    rw [phase_poly_eq φ X, ← hθ, ← hILdef]
    have e : θ = ε + (n : ℂ) * (Real.pi : ℂ) := by rw [hεdef]; ring
    rw [e, hr2def]
    linear_combination hsi
  exact ⟨r2, hr2, hg⟩

theorem tail024 (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈2 * Lp φ + 1⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tauC N φ n ≤ 1)
    (hL : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2)) :
    indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖ ≤
      boundC N φ CT n := by
  obtain ⟨r2, hr2, hg⟩ := tail024A N hN φ a ha hxi n h1 h4 h5
  obtain ⟨hν1, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := hν1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  set X : ℂ := criticalEigenvalue φ n with hXdef
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have hμν : |(n : ℝ)| ≤ ‖X‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) X
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxi n
    rw [← hXdef] at h9
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
    linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hμ0 : X ≠ 0 := by intro h0; rw [h0, norm_zero] at hμν; linarith
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hμi : ‖X⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖X⁻¹ - ls⁻¹‖ ≤ ‖X - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hμ0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hμν hlsν hν0.le (norm_nonneg _)
  have hlip := phasePoly_lip φ (N + 1) _ _ hμi hlsi
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖X - ls‖ / |(n : ℝ)| ^ 2 := by
    refine hlip.trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  have hDeq : (X - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) = (0 : ℂ) / 2 + r2 := by
    rw [zero_div, zero_add, ← hg]
    linear_combination (-1 : ℂ) * hgs
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT / |(n : ℝ)| ^ (N + 2) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hG : indexWeight n ^ N * ‖(0 : ℂ)‖ ≤ 0 := by simp
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hfin := final_pure N (indexWeight n) |(n : ℝ)| (Lsum φ) CT 0
    (psiC N φ n) (X - ls) 0 r2
    (KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ - KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹)
    (ls - spectralPolynomial φ n)
    hw1 hn1R hwν hL0 hL hCT hDeq hΔp hT0 hG hr2
  have e : X - spectralPolynomial φ n =
      r2 - (KSPSRiccati.phasePolynomial φ (N + 1) X⁻¹ -
        KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) + (ls - spectralPolynomial φ n) := by
    linear_combination hDeq
  rw [e]
  have e2 : (4 : ℝ) * 0 + 2 * psiC N φ n = 2 * psiC N φ n := by ring
  rw [e2] at hfin
  unfold boundC
  exact hfin

/-! ### The weighted estimate (conditional on the KSPS-017 head conclusion at xi = criticalEigenvalue) -/

theorem critical_spectral_expansion_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖criticalEigenvalue φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h17 : WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => deriv (discriminant φ) (criticalEigenvalue φ n) -
        KSPSWKB.discriminantDerivativeMain N φ (criticalEigenvalue φ) n)) :
    WeightedL2Error (N+1)
      (fun n => criticalEigenvalue φ n - spectralPolynomial φ n) := by
  rw [wl2_iff] at h17
  have hE : Summable (fun n : ℤ => (indexWeight n ^ (N + 1) * ‖critE N φ n‖) ^ 2) := h17
  -- the inverse-phase germ (K = N + 1)
  obtain ⟨ζ, hζa, hζ0, hev, hcoef⟩ :=
    NlsGge.ThirdConsultation.KSPS023T.spectralCoefficient_consistent φ (N + 1) le_rfl
  obtain ⟨CT0, hCT0⟩ := (hζa.hasFPowerSeriesAt.isBigO_sub_partialSum_pow (N + 2)).bound
  set CT : ℝ := max CT0 0 with hCTdef
  have hCT : 0 ≤ CT := le_max_right _ _
  have htay0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y - ∑ k ∈ Finset.Icc 1 (N + 1),
      KSPSRiccati.spectralCoefficient φ k * y ^ k‖ ≤ CT * ‖y‖ ^ (N + 2) := by
    filter_upwards [hCT0] with y hy
    rw [zero_add, partialSum_eq φ ζ hζ0 hcoef y, norm_pow, norm_norm] at hy
    exact hy.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hsmall0 : ∀ᶠ y : ℂ in 𝓝 0, ‖ζ y‖ ≤ 1 := by
    have h := hζa.continuousAt.eventually (Metric.closedBall_mem_nhds (ζ 0) one_pos)
    filter_upwards [h] with y hy
    rw [dist_eq_norm, hζ0, sub_zero] at hy
    exact hy
  have et := tendsto_inv_int.eventually htay0
  have es := tendsto_inv_int.eventually hsmall0
  have ee := tendsto_inv_int.eventually hev
  -- summability of the bound
  have hI : Summable (fun n : ℤ => (2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n)) ^ 2) :=
    KSPS015W.sq_summable_mul_left _ KSPS016W.sq_summable_inv_w
  have hτ : Summable (fun n : ℤ => tauC N φ n ^ 2) := by
    unfold tauC
    exact KSPS015W.sq_summable_add hE hI
  have hψ : Summable (fun n : ℤ => psiC N φ n ^ 2) := by
    have h := KSPS015W.sq_summable_add
      (KSPS015W.sq_summable_mul_left (4 + 4 * Lp φ) hτ)
      (KSPS015W.sq_summable_mul_left (1 / 2) hE)
    refine h.congr (fun n => ?_)
    unfold psiC
    ring
  have hb : Summable (fun n : ℤ => boundC N φ CT n ^ 2) := by
    have h := KSPS015W.sq_summable_add (KSPS015W.sq_summable_add hψ
      (KSPS015W.sq_summable_mul_left (Lsum φ) (KSPS015W.sq_summable_mul_left 2 hψ)))
      (KSPS015W.sq_summable_mul_left (CT * 2 ^ (N + 2)) KSPS016W.sq_summable_inv_w)
    refine h.congr (fun n => ?_)
    unfold boundC
    ring
  have hs : ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hs]
  have e1 := KSPS015W.eventually_natAbs (⌈a⌉₊ + ⌈2 * Lp φ + 1⌉₊ + 1)
  have e3 := KSPS015W.eventually_natAbs 1
  have e4 := eventually_w_ge (2 * (a + Jsum φ))
  have e5 := eventually_le_of_sq (tauC N φ) hτ 1 one_pos
  have e6 := KSPS015W.eventually_natAbs ⌈2 * Lsum φ⌉₊
  refine wl2_of_eventually N _ (boundC N φ CT) hb ?_
  filter_upwards [e1, e3, e4, e5, e6, et, es, ee] with n g1 g3 g4 g5 g6 g7 g8 g9
  have hL : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2 := by
    have h7 : ((⌈2 * Lsum φ⌉₊ : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g6
    rw [Int.cast_abs] at h7
    push_cast at h7
    have h8 := Nat.le_ceil (2 * Lsum φ)
    have h9 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast g3
      rw [Int.cast_abs] at this
      simpa using this
    nlinarith
  exact tail024 N hN φ a ha hxi ζ CT hCT n g1 g4 g5 hL g9.1 g9.2 g8 g7

end
end NlsGge.ThirdConsultation.KSPS024W
