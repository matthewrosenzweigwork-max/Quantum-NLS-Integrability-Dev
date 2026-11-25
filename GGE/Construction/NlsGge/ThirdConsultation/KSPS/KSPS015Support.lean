import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS015Host
import NlsGge.ThirdConsultation.KSPS.KSPS012Host
import NlsGge.ThirdConsultation.KSPS.KSPS014Support1
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.G1.IBP038Support
import NlsGge.Sobolev.PeriodicBridge

                                                                                                                  
                                                                            
                                                                                                               
                                                                                                      
                                              
                                                                                                                       
                                                                                                                          
                                                                                               
                                                                                                     
                                                                                                                  
                                                                                                                      
                                     
                                                                                                                   
                                                                                                               
                                                                                              
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS015W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

/-! ### (1) Periodicity of the coefficient traces -/

theorem integral_cover_eq_fourier0 (u : PhysicalL2) :
    ∫ s in (0 : ℝ)..1, coverRep38 u s = physicalFourier u 0 := by
  unfold physicalFourier
  rw [fourierCoeff_eq_intervalIntegral (u : AddCircle (1 : ℝ) → ℂ) 0 0]
  simp only [zero_add, div_one, one_smul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys u] with s hs _
  rw [hs]
  simp

theorem integral_cover_weakDerivative (w : PhysicalL2) (hw : physicalSobolev 1 w) :
    ∫ s in (0 : ℝ)..1, coverRep38 (weakDerivative w) s = 0 := by
  rw [integral_cover_eq_fourier0, physicalFourier_weakDerivative w hw 0]
  simp

theorem coefficientTrace_one {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    KSPSWKB.coefficientTrace φ b k 1 = KSPSWKB.coefficientTrace φ b k 0 := by
  have h := integral_cover_weakDerivative _
    (NlsGge.ThirdConsultation.KSPSSupport.h150_coef_H1 N (le_trans hk1 hkN) φ b k hk1 hkN)
  simp only [KSPSWKB.coefficientTrace, intervalIntegral.integral_same, h]

theorem alpha_one {N : ℕ} (φ : SobolevC N) (lam : ℂ) :
    KSPSWKB.alpha φ lam 1 = KSPSWKB.alpha φ lam 0 := by
  unfold KSPSWKB.alpha
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [coefficientTrace_one φ false k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2]

theorem beta_one {N : ℕ} (φ : SobolevC N) (lam : ℂ) :
    KSPSWKB.beta φ lam 1 = KSPSWKB.beta φ lam 0 := by
  unfold KSPSWKB.beta
  congr 1
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [coefficientTrace_one φ true k (Finset.mem_Icc.1 hk).1 (Finset.mem_Icc.1 hk).2]

/-! ### (2) The phase at x = 1 -/

theorem prefix_false_one {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    NlsGge.ThirdConsultation.KSPSRiccati.«prefix» φ false k 1 = integralRiccatiLeft φ k := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.«prefix» integralRiccatiLeft
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [coverRep38_ae_phys (toPotPair φ).1,
    coverRep38_ae_phys (riccatiLeft φ k)] with x h1 h2 _
  show coverRep38 (toPotPair φ).1 x * coverRep38 (riccatiLeft φ k) x = _
  rw [h1, h2]

theorem prefix_true_one {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    NlsGge.ThirdConsultation.KSPSRiccati.«prefix» φ true k 1 = integralRiccatiRight φ k := rfl

theorem wkbPhase_eq {N : ℕ} (φ : SobolevC N) (lam : ℂ) :
    wkbPhase φ lam = lam + Complex.I * ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k := by
  unfold NlsGge.ThirdConsultation.KSPS.wkbPhase
  congr 2
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [zpow_neg, zpow_natCast]

theorem phaseFactor_false_one {N : ℕ} (φ : SobolevC N) (lam : ℂ) :
    NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ false lam 1 =
      Complex.exp (∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k) := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor
  simp only [prefix_false_one]
  simp

theorem phaseFactor_true_one {N : ℕ} (φ : SobolevC N) (lam : ℂ)
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k) :
    NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ true lam 1 =
      Complex.exp (-∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k) := by
  unfold NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor
  have hs : ∑ k ∈ Finset.Icc 1 N,
      ((2 * Complex.I * lam) ^ k)⁻¹ * NlsGge.ThirdConsultation.KSPSRiccati.«prefix» φ true k 1 =
      ∑ k ∈ Finset.Icc 1 N, ((2 * Complex.I * lam) ^ k)⁻¹ * integralRiccatiLeft φ k := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_Icc.1 hk
    rw [prefix_true_one, h13 k ⟨hk'.1, by omega⟩]
  rw [hs]
  simp

/-! ### Literal abbreviations of the x = 1 column pieces -/

def ef {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) : ℂ :=
  Complex.exp (-(Complex.I * lam.1 * ((1 : ℝ) : ℂ))) *
    NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ false lam.1 1

def et {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) : ℂ :=
  Complex.exp (Complex.I * lam.1 * ((1 : ℝ) : ℂ)) *
    NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ true lam.1 1

def rf {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) : Fin 2 → ℂ :=
  KSPSWKB.sourceRemainderVector φ false lam 1

def rt {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) : Fin 2 → ℂ :=
  KSPSWKB.sourceRemainderVector φ true lam 1

theorem ef_eq {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) :
    ef φ lam = Complex.exp (-(wkbPhase φ lam.1 * Complex.I)) := by
  unfold ef
  rw [phaseFactor_false_one, ← Complex.exp_add, wkbPhase_eq]
  congr 1
  push_cast
  linear_combination (∑ k ∈ Finset.Icc 1 N,
    ((2 * Complex.I * lam.1) ^ k)⁻¹ * integralRiccatiLeft φ k) * Complex.I_sq

theorem et_eq {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k) :
    et φ lam = Complex.exp (wkbPhase φ lam.1 * Complex.I) := by
  unfold et
  rw [phaseFactor_true_one φ lam.1 h13, ← Complex.exp_add, wkbPhase_eq]
  congr 1
  push_cast
  linear_combination (-(∑ k ∈ Finset.Icc 1 N,
    ((2 * Complex.I * lam.1) ^ k)⁻¹ * integralRiccatiLeft φ k)) * Complex.I_sq

theorem two_cos_eq (z : ℂ) :
    2 * Complex.cos z = Complex.exp (z * Complex.I) + Complex.exp (-(z * Complex.I)) := by
  simp only [Complex.cos, neg_mul]
  ring

theorem two_I_sin_eq (z : ℂ) :
    2 * Complex.I * Complex.sin z = Complex.exp (z * Complex.I) - Complex.exp (-(z * Complex.I)) := by
  simp only [Complex.sin, neg_mul]
  linear_combination (Complex.exp (-(z * Complex.I)) - Complex.exp (z * Complex.I)) * Complex.I_sq

theorem ef_add_et {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k) :
    ef φ lam + et φ lam = 2 * Complex.cos (wkbPhase φ lam.1) := by
  rw [ef_eq, et_eq φ lam h13, two_cos_eq]
  ring

theorem et_sub_ef {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k) :
    et φ lam - ef φ lam = 2 * Complex.I * Complex.sin (wkbPhase φ lam.1) := by
  rw [ef_eq, et_eq φ lam h13, two_I_sin_eq]

/-! ### (3) Exact entries of the explicit WKB monodromy -/

theorem explicit_formula {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) :
    KSPSWKB.explicitWKBMonodromy N φ lam =
      (1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0)⁻¹ •
        !![ef φ lam - KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 * et φ lam +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rf φ lam 0 - KSPSWKB.alpha φ lam.1 0 * rt φ lam 0),
           KSPSWKB.beta φ lam.1 0 * (et φ lam - ef φ lam) +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rt φ lam 0 - KSPSWKB.beta φ lam.1 0 * rf φ lam 0);
           KSPSWKB.alpha φ lam.1 0 * (ef φ lam - et φ lam) +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rf φ lam 1 - KSPSWKB.alpha φ lam.1 0 * rt φ lam 1),
           et φ lam - KSPSWKB.alpha φ lam.1 0 * KSPSWKB.beta φ lam.1 0 * ef φ lam +
              ((2 * Complex.I * lam.1) ^ N)⁻¹ * (rt φ lam 1 - KSPSWKB.beta φ lam.1 0 * rf φ lam 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KSPSWKB.explicitWKBMonodromy, KSPSWKB.wkbColumns, KSPSWKB.wkbColumn, KSPSWKB.initialColumns,
      NlsGge.ThirdConsultation.KSPSVolterra.adjugate2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_fin_two, alpha_one, beta_one, ef, et, rf, rt, -mul_eq_mul_left_iff] <;> ring

theorem disc_identity {N : ℕ} (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (hM : monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (hD : 1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0 ≠ 0) :
    discriminant φ lam.1 - 2 * Complex.cos (wkbPhase φ lam.1) =
      (1 - KSPSWKB.beta φ lam.1 0 * KSPSWKB.alpha φ lam.1 0)⁻¹ *
        (((2 * Complex.I * lam.1) ^ N)⁻¹ *
          (rf φ lam 0 + rt φ lam 1 - KSPSWKB.alpha φ lam.1 0 * rt φ lam 0 -
            KSPSWKB.beta φ lam.1 0 * rf φ lam 1)) := by
  unfold discriminant
  rw [discrim_eq, hM, explicit_formula, ← ef_add_et φ lam h13]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  field_simp
  ring

/-! ### (4) Real estimates -/

theorem weighted_bound (N : ℕ) (w X S c U V : ℝ) (Dinv ε s α β u v : ℂ)
    (hw : 0 < w) (hX : 0 < X) (hwX : w ≤ 2 * X) (hS : 0 ≤ S) (hc : 0 ≤ c) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hD : ‖Dinv‖ ≤ 2) (hε : ‖ε‖ = ((2 * X) ^ N)⁻¹) (hs : ‖s‖ ≤ c / w)
    (hα : ‖α‖ ≤ S / (2 * X)) (hβ : ‖β‖ ≤ S / (2 * X)) (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ V) :
    w ^ (N + 1) * ‖Dinv * (ε * (s - α * u - β * v))‖ ≤ 2 * (c + S * (U + V)) := by
  have h2X : 0 < 2 * X := by linarith
  set r : ℝ := w / (2 * X) with hr
  have hr0 : 0 ≤ r := div_nonneg hw.le h2X.le
  have hr1 : r ≤ 1 := by rw [hr, div_le_one h2X]; exact hwX
  have hrN : r ^ N ≤ 1 := pow_le_one₀ hr0 hr1
  have hrN1 : r ^ (N + 1) ≤ 1 := pow_le_one₀ hr0 hr1
  have hSX : 0 ≤ S / (2 * X) := div_nonneg hS h2X.le
  have hinner : ‖s - α * u - β * v‖ ≤ c / w + S / (2 * X) * (U + V) := by
    have e1 : ‖s - α * u - β * v‖ ≤ ‖s‖ + ‖α‖ * ‖u‖ + ‖β‖ * ‖v‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul]
      have := norm_sub_le s (α * u)
      rw [norm_mul] at this
      linarith
    have e2 : ‖α‖ * ‖u‖ ≤ S / (2 * X) * U :=
      mul_le_mul hα hu (norm_nonneg _) hSX
    have e3 : ‖β‖ * ‖v‖ ≤ S / (2 * X) * V :=
      mul_le_mul hβ hv (norm_nonneg _) hSX
    have e4 : S / (2 * X) * (U + V) = S / (2 * X) * U + S / (2 * X) * V := by ring
    linarith
  have hεn : 0 ≤ ((2 * X) ^ N)⁻¹ := inv_nonneg.mpr (pow_nonneg h2X.le N)
  have hE : ‖Dinv * (ε * (s - α * u - β * v))‖ ≤
      2 * (((2 * X) ^ N)⁻¹ * (c / w + S / (2 * X) * (U + V))) := by
    rw [norm_mul, norm_mul, hε]
    exact mul_le_mul hD (mul_le_mul_of_nonneg_left hinner hεn) (mul_nonneg hεn (norm_nonneg _)) (by norm_num)
  have hw0 : w ≠ 0 := hw.ne'
  have hX0 : 2 * X ≠ 0 := h2X.ne'
  have hXne : X ≠ 0 := hX.ne'
  have k1 : w ^ (N + 1) * (((2 * X) ^ N)⁻¹ * (c / w)) = r ^ N * c := by
    rw [hr, div_pow]
    field_simp
    ring
  have k2 : w ^ (N + 1) * (((2 * X) ^ N)⁻¹ * (S / (2 * X) * (U + V))) = r ^ (N + 1) * (S * (U + V)) := by
    rw [hr, div_pow]
    field_simp
    ring
  have hwN : 0 ≤ w ^ (N + 1) := pow_nonneg hw.le _
  have hSUV : 0 ≤ S * (U + V) := mul_nonneg hS (add_nonneg hU hV)
  calc w ^ (N + 1) * ‖Dinv * (ε * (s - α * u - β * v))‖
      ≤ w ^ (N + 1) * (2 * (((2 * X) ^ N)⁻¹ * (c / w + S / (2 * X) * (U + V)))) :=
        mul_le_mul_of_nonneg_left hE hwN
    _ = 2 * (w ^ (N + 1) * (((2 * X) ^ N)⁻¹ * (c / w)) +
          w ^ (N + 1) * (((2 * X) ^ N)⁻¹ * (S / (2 * X) * (U + V)))) := by ring
    _ = 2 * (r ^ N * c + r ^ (N + 1) * (S * (U + V))) := by rw [k1, k2]
    _ ≤ 2 * (1 * c + 1 * (S * (U + V))) := by
        have := mul_le_mul_of_nonneg_right hrN hc
        have := mul_le_mul_of_nonneg_right hrN1 hSUV
        linarith
    _ = 2 * (c + S * (U + V)) := by ring

theorem sq_summable_add {f g : ℤ → ℝ} (hf : Summable (fun n => f n ^ 2)) (hg : Summable (fun n => g n ^ 2)) :
    Summable (fun n => (f n + g n) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) ((hf.mul_left 2).add (hg.mul_left 2))
  nlinarith [sq_nonneg (f n - g n)]

theorem sq_summable_mul_left {f : ℤ → ℝ} (K : ℝ) (hf : Summable (fun n => f n ^ 2)) :
    Summable (fun n => (K * f n) ^ 2) := by
  simp_rw [mul_pow]
  exact hf.mul_left _

theorem eventually_natAbs (N0 : ℕ) : ∀ᶠ n : ℤ in Filter.cofinite, (N0 : ℤ) ≤ |n| := by
  rw [Filter.eventually_cofinite]
  apply (Set.finite_Icc (-(N0 : ℤ)) N0).subset
  intro n hn
  simp only [Set.mem_setOf_eq, not_le] at hn
  rw [Set.mem_Icc]
  constructor <;> cases abs_cases n <;> omega

theorem one_le_w (n : ℤ) : 1 ≤ indexWeight n := by
  unfold indexWeight
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (n : ℝ)])

theorem w_le_two (n : ℤ) (hn : 1 ≤ |(n : ℝ)|) : indexWeight n ≤ 2 * |(n : ℝ)| := by
  unfold indexWeight
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
  rw [this]; nlinarith

/-- Tail facts for a sample sequence close to n pi. -/
theorem tail_facts (a T : ℝ) (ha : 0 ≤ a) (xi : ℤ → ℂ)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (n : ℤ) (hn : ((⌈a⌉₊ + ⌈T⌉₊ + 1 : ℕ) : ℤ) ≤ |n|) :
    1 ≤ ‖xi n‖ ∧ T ≤ ‖xi n‖ ∧ indexWeight n ≤ 2 * ‖xi n‖ := by
  set ν : ℝ := |(n : ℝ)| with hν
  have hnR : ((⌈a⌉₊ + ⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ ν := by
    rw [hν, ← Int.cast_abs]
    exact_mod_cast hn
  push_cast at hnR
  have hca := Nat.le_ceil a
  have hcT := Nat.le_ceil T
  have hc0 : (0 : ℝ) ≤ (⌈a⌉₊ : ℝ) := Nat.cast_nonneg _
  have hc1 : (0 : ℝ) ≤ (⌈T⌉₊ : ℝ) := Nat.cast_nonneg _
  have hν1 : 1 ≤ ν := by linarith
  have hνa : a ≤ ν := by linarith
  have hνT : T ≤ ν := by linarith
  have hw1 := one_le_w n
  have h1 := hxi n
  have h2 : a / indexWeight n ≤ a := div_le_self ha hw1
  have h3 : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * ν := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, hν]; ring
  have h4 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (xi n)
  rw [norm_sub_rev, h3] at h4
  have hpi := Real.pi_gt_three
  have h5 : 3 * ν ≤ Real.pi * ν := mul_le_mul_of_nonneg_right hpi.le (by linarith)
  have hX : 2 * ν ≤ ‖xi n‖ := by linarith
  have hw2 := w_le_two n hν1
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ### The weighted sequence estimate (conditional on the KSPS-011/012/013/014 head conclusions) -/

theorem discriminant_WKB_sequence_of
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
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => discriminant φ (xi n) - 2 * Complex.cos (wkbPhase φ (xi n))) := by
  obtain ⟨eL, eU, hL, hU, h11'⟩ := h11
  obtain ⟨e1, e2, hs1, hs2, h12'⟩ := h12
  set B : ℝ := sobolevNorm N φ with hBdef
  set S : ℝ := ∑ k ∈ Finset.Icc 1 N,
    NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k hk => KSPSWKB.endpointCoefficientBound_nonneg N B k hk)
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have ht : Summable (fun n : ℤ => (2 * (‖e1 n‖ + ‖e2 n‖ +
      S * ((‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖) +
        (‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖)))) ^ 2) := by
    refine sq_summable_mul_left 2 ?_
    refine sq_summable_add (sq_summable_add hs1 hs2) (sq_summable_mul_left S ?_)
    exact sq_summable_add (sq_summable_add hF1 hU) (sq_summable_add hF2 hL)
  set T : ℝ := NlsGge.ThirdConsultation.KSPSVolterra.threshold N B with hTdef
  set n0 : ℕ := ⌈a⌉₊ + ⌈T⌉₊ + 1 with hn0
  -- the pointwise tail bound
  have hbound : ∀ n : ℤ, (n0 : ℤ) ≤ |n| →
      indexWeight n ^ (N + 1) * ‖discriminant φ (xi n) - 2 * Complex.cos (wkbPhase φ (xi n))‖ ≤
        2 * (‖e1 n‖ + ‖e2 n‖ +
          S * ((‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖) +
            (‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖))) := by
    intro n hn
    obtain ⟨hX1, hXT, hwX⟩ := tail_facts a T ha xi hxi n hn
    have hz : xi n ≠ 0 := by
      intro h; rw [h, norm_zero] at hX1; norm_num at hX1
    have hX0 : 0 < ‖xi n‖ := by linarith
    have hthr : WKBThreshold N B (xi n) := ⟨hX0, hXT⟩
    set lam : {z : ℂ // z ≠ 0} := ⟨xi n, hz⟩ with hlamdef
    have hdet := KSPSWKB.initialColumns_det_bound N B φ (xi n) le_rfl hthr
    have hdetv : Matrix.det (KSPSWKB.initialColumns φ (xi n)) =
        1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0 := by
      simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
    rw [hdetv] at hdet
    have hD : 1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0 ≠ 0 := by
      intro h; rw [h, norm_zero] at hdet; norm_num at hdet
    have hid := disc_identity φ lam h13 (h14 lam hthr) hD
    have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (one_le_w n)
    have hwc : (indexWeight n : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
    -- the diagonal sum
    have hLow : rf φ lam 0 = KSPSWKB.endpointDiagonalLower N φ xi n := by
      simp only [KSPSWKB.endpointDiagonalLower, dif_neg hz]; rfl
    have hUpp : rt φ lam 1 = KSPSWKB.endpointDiagonalUpper N φ xi n := by
      simp only [KSPSWKB.endpointDiagonalUpper, dif_neg hz]; rfl
    have hm1 : (-1 : ℂ) ≠ 0 := by norm_num
    have hsum : rf φ lam 0 + rt φ lam 1 = (e1 n + e2 n) / (indexWeight n : ℂ) := by
      rw [hLow, hUpp, (h12' n).1, (h12' n).2, ← h13 (N + 1) ⟨by omega, le_rfl⟩, zpow_add_one₀ hm1]
      unfold indexValue
      ring
    have hs : ‖rf φ lam 0 + rt φ lam 1‖ ≤ (‖e1 n‖ + ‖e2 n‖) / indexWeight n := by
      rw [hsum, norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) hw0.le
    -- off-diagonal terms
    have hdivle : ∀ e : ℂ, ‖e / (indexValue n : ℂ)‖ ≤ ‖e‖ := by
      intro e
      unfold indexValue
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hw0.le]
      exact div_le_self (norm_nonneg _) (one_le_w n)
    have hu : ‖rt φ lam 0‖ ≤ ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖ := by
      have hR : KSPSWKB.endpointRemainderUpper N φ xi n = (-1 : ℂ) ^ N * rt φ lam 0 := by
        simp only [KSPSWKB.endpointRemainderUpper, dif_neg hz]; rfl
      have hn1 : ‖rt φ lam 0‖ = ‖KSPSWKB.endpointRemainderUpper N φ xi n‖ := by
        rw [hR, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [hn1, (h11' n).2]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hdivle _))
      rw [norm_mul, norm_mul, Complex.norm_I, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, one_mul]
    have hv : ‖rf φ lam 1‖ ≤ ‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖ := by
      have hR : KSPSWKB.endpointRemainderLower N φ xi n = rf φ lam 1 := by
        simp only [KSPSWKB.endpointRemainderLower, dif_neg hz]; rfl
      rw [← hR, (h11' n).1]
      refine (norm_add_le _ _).trans (add_le_add (le_of_eq ?_) (hdivle _))
      rw [norm_mul, norm_mul, Complex.norm_I, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, one_mul]
    have hα : ‖KSPSWKB.alpha φ (xi n) 0‖ ≤ S / (2 * ‖xi n‖) :=
      KSPSWKB.endpointSum_norm_le B φ le_rfl false (xi n) hX1
    have hβ : ‖KSPSWKB.beta φ (xi n) 0‖ ≤ S / (2 * ‖xi n‖) :=
      KSPSWKB.endpointSum_norm_le B φ le_rfl true (xi n) hX1
    have hDinv : ‖(1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      have hpos : 0 < ‖1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0‖ := by linarith
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith
    have hε : ‖((2 * Complex.I * xi n) ^ N)⁻¹‖ = ((2 * ‖xi n‖) ^ N)⁻¹ := by
      rw [norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    have key := weighted_bound N (indexWeight n) ‖xi n‖ S (‖e1 n‖ + ‖e2 n‖)
      (‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ + ‖eU n‖)
      (‖physicalFourier (iteratedDerivative N φ.2) n‖ + ‖eL n‖)
      (1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0)⁻¹ ((2 * Complex.I * xi n) ^ N)⁻¹
      (rf φ lam 0 + rt φ lam 1) (KSPSWKB.alpha φ (xi n) 0) (KSPSWKB.beta φ (xi n) 0)
      (rt φ lam 0) (rf φ lam 1)
      hw0 hX0 hwX hS0 (by positivity) (by positivity) (by positivity) hDinv hε hs hα hβ hu hv
    have hE : discriminant φ (xi n) - 2 * Complex.cos (wkbPhase φ (xi n)) =
        (1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0)⁻¹ *
          (((2 * Complex.I * xi n) ^ N)⁻¹ *
            (rf φ lam 0 + rt φ lam 1 - KSPSWKB.alpha φ (xi n) 0 * rt φ lam 0 -
              KSPSWKB.beta φ (xi n) 0 * rf φ lam 1)) := hid
    rw [hE]
    exact key
  -- summability
  unfold WeightedL2Error
  have hrp : ∀ n : ℤ, indexWeight n ^ (2 * ((N + 1 : ℕ) : ℝ)) =
      (indexWeight n ^ (N + 1)) ^ 2 := by
    intro n
    rw [show (2 * ((N + 1 : ℕ) : ℝ)) = ((2 * (N + 1) : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  refine Summable.of_norm_bounded_eventually ht ?_
  filter_upwards [eventually_natAbs n0] with n hn
  beta_reduce
  rw [hrp n, ← mul_pow, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 : 0 ≤ indexWeight n ^ (N + 1) *
      ‖discriminant φ (xi n) - 2 * Complex.cos (wkbPhase φ (xi n))‖ :=
    mul_nonneg (pow_nonneg (le_trans zero_le_one (one_le_w n)) _) (norm_nonneg _)
  exact pow_le_pow_left₀ h0 (hbound n hn) 2

end
end NlsGge.ThirdConsultation.KSPS015W
