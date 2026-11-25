import Mathlib
import NlsGge.Atomic.I.I037
import NlsGge.Birkhoff.S03Measure38
import NlsGge.Measure.CountableSupport

                                                                                                                  
                                                                                               
                                  
                                                                                                          
                                                                                                                    
                                                                                                               
                                                                                                                  
                                                                                                             
                                                                                                                
                                                                                                               
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open NlsGge.Pilot NlsGge.Measure NlsGge.Birkhoff
open NlsGge.Atomic.I037

namespace NlsGge.ThirdConsultation.I038M

theorem allSobolev_eq :
    {z : ℤ → ℂ | ∀ r : ℕ, SobolevSquareSummable (r : ℝ) z} =
      ⋂ r : ℕ, {z : ℤ → ℂ | Summable (fun n : ℤ => sobolevWeight38 r n * ‖z n‖ ^ 2)} := by
  ext z; simp only [Set.mem_setOf_eq, Set.mem_iInter, SobolevSquareSummable, sobolevWeight38,
    Real.rpow_eq_pow]

theorem measurableSet_good (w : ℤ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    MeasurableSet {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)} := by
  have h1 : MeasurableSet {z : ℤ → ℂ | ∀ r : ℕ, SobolevSquareSummable (r : ℝ) z} := by
    rw [allSobolev_eq]
    exact MeasurableSet.iInter fun r => measurableSet_sequenceSummable _ (sobolevWeight38_nonneg r)
  exact h1.inter (measurableSet_sequenceSummable w hw)

theorem ae_good (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable (fun n : ℤ => w n / q n))
    (hpoly : ∀ r : ℕ, Summable (fun n : ℤ => sobolevWeight38 r n / q n)) :
    ∀ᵐ z ∂countableComplexGaussian q, (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2) := by
  have h1 : ∀ᵐ z ∂countableComplexGaussian q, ∀ r : ℕ, SobolevSquareSummable (r : ℝ) z := by
    rw [ae_all_iff]
    intro r
    filter_upwards [ae_sequenceSummable q (sobolevWeight38 r) hq (sobolevWeight38_nonneg r) (hpoly r)]
      with z hz
    simpa only [SobolevSquareSummable, sobolevWeight38, Real.rpow_eq_pow] using hz
  filter_upwards [h1, ae_sequenceSummable q w hq hw hsum] with z hz1 hz2 using ⟨hz1, hz2⟩

theorem measure_good_eq_one (q w : ℤ → ℝ) (hq : ∀ n, 0 < q n) (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable (fun n : ℤ => w n / q n))
    (hpoly : ∀ r : ℕ, Summable (fun n : ℤ => sobolevWeight38 r n / q n)) :
    countableComplexGaussian q {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)} = 1 :=
  (prob_compl_eq_zero_iff (measurableSet_good w hw)).1 (ae_iff.1 (ae_good q w hq hw hsum hpoly))

/-! ### The factorial-power instance -/

/-- `⟨n⟩^{2(r+1)} ≤ ((r+1)!)^p · W(2πn)`: one term of the entire series dominates. -/
theorem bracket_pow_le {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℕ) (n : ℤ) :
    japaneseBracket n ^ (2 * (r + 1)) ≤
      ((Nat.factorial (r + 1) : ℝ)) ^ p * factorialPowerWeight p c (2 * Real.pi * n) := by
  set K : ℝ := ((Nat.factorial (r + 1) : ℝ)) ^ p with hK
  have hF1 : (1 : ℝ) ≤ (Nat.factorial (r + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hK1 : 1 ≤ K := Real.one_le_rpow hF1 (by linarith)
  have hK0 : 0 < K := by linarith
  have hW1 := weight_ge_one hp hc (2 * Real.pi * n)
  have hterm : factorialPowerTerm p c (2 * Real.pi * n) (r + 1) ≤ factorialPowerWeight p c (2 * Real.pi * n) :=
    (summable_term hp hc _).le_tsum (r + 1) (fun j _ => term_nonneg hc _ j)
  have hjb2 : japaneseBracket n ^ 2 = 1 + (n : ℝ) ^ 2 := by
    unfold japaneseBracket; exact Real.sq_sqrt (by positivity)
  by_cases hn : n = 0
  · subst hn
    have : japaneseBracket 0 = 1 := by unfold japaneseBracket; simp
    rw [this, one_pow]
    nlinarith
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      nlinarith [sq_abs (n : ℝ)]
    have hpi := Real.pi_gt_three
    have hb : japaneseBracket n ^ 2 ≤ (2 * Real.pi * n) ^ 2 := by
      rw [hjb2, show (2 * Real.pi * n) ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 by ring]
      have hpi2 : 9 < Real.pi ^ 2 := by nlinarith
      nlinarith
    have h1 : japaneseBracket n ^ (2 * (r + 1)) ≤ (2 * Real.pi * n) ^ (2 * (r + 1)) := by
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (by positivity) hb _
    have h2 : (2 * Real.pi * n) ^ (2 * (r + 1)) ≤ K * factorialPowerTerm p c (2 * Real.pi * n) (r + 1) := by
      unfold factorialPowerTerm
      rw [← hK, mul_div_assoc', mul_comm K, mul_div_assoc, div_self hK0.ne', mul_one]
      have hpow : 0 ≤ (2 * Real.pi * n) ^ (2 * (r + 1)) := by rw [pow_mul]; positivity
      nlinarith [(hc (r + 1)).1]
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hterm hK0.le))

theorem rate_poly {p : ℝ} (hp : 1 ≤ p) {c : ℕ → ℝ} (hc : ∀ j, 1 ≤ c j ∧ c j ≤ 2) (r : ℕ) :
    Summable (fun n : ℤ => sobolevWeight38 r n / factorialPowerWeight p c (2 * Real.pi * n)) := by
  set K : ℝ := ((Nat.factorial (r + 1) : ℝ)) ^ p with hK
  have hF1 : (1 : ℝ) ≤ (Nat.factorial (r + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos (r + 1)
  have hK0 : 0 < K := Real.rpow_pos_of_pos (by linarith) _
  have hS := (summable_japaneseBracket_rpow_neg 2 (by norm_num)).mul_left K
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (sobolevWeight38_nonneg r n)
    (by linarith [weight_ge_one hp hc (2 * Real.pi * n)])) (fun n => ?_) hS
  have hb0 : 0 < japaneseBracket n := by
    unfold japaneseBracket; exact Real.sqrt_pos.2 (by positivity)
  have hW0 : 0 < factorialPowerWeight p c (2 * Real.pi * n) := by
    linarith [weight_ge_one hp hc (2 * Real.pi * n)]
  have hsw : sobolevWeight38 r n = japaneseBracket n ^ (2 * r) := by
    unfold sobolevWeight38
    rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hneg : Real.rpow (japaneseBracket n) (-2) = (japaneseBracket n ^ 2)⁻¹ := by
    rw [Real.rpow_eq_pow, Real.rpow_neg hb0.le, Real.rpow_two]
  rw [hsw, hneg, div_le_iff₀ hW0]
  have hle := bracket_pow_le hp hc r n
  have e : japaneseBracket n ^ (2 * (r + 1)) = japaneseBracket n ^ (2 * r) * japaneseBracket n ^ 2 := by
    rw [← pow_add]; ring_nf
  rw [e] at hle
  have hb2 : 0 < japaneseBracket n ^ 2 := by positivity
  calc japaneseBracket n ^ (2 * r)
      = (japaneseBracket n ^ (2 * r) * japaneseBracket n ^ 2) * (japaneseBracket n ^ 2)⁻¹ := by
        field_simp
    _ ≤ (K * factorialPowerWeight p c (2 * Real.pi * n)) * (japaneseBracket n ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hle (inv_nonneg.2 hb2.le)
    _ = K * (japaneseBracket n ^ 2)⁻¹ * factorialPowerWeight p c (2 * Real.pi * n) := by ring

/-- I-038 conjuncts `MeasurableSet Ω` and `γ Ω = 1`, with the head's literal Ω and γ. -/
theorem omega_conjuncts (p : ℝ) (hp : 2 < p) (c : BoundedCoefficients 1 2) :
    MeasurableSet {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) * ‖z n‖ ^ 2 *
        japaneseBracket n ^ (2 / p - 2))} ∧
    countableComplexGaussian (fun n : ℤ => factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)))
      {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
        Summable (fun n : ℤ => factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) * ‖z n‖ ^ 2 *
          japaneseBracket n ^ (2 / p - 2))} = 1 := by
  have hc : ∀ j, 1 ≤ c.val j ∧ c.val j ≤ 2 := c.property.2.2
  have hp1 : 1 ≤ p := by linarith
  set a : ℤ → ℝ := fun n => factorialPowerWeight p c.val (2 * Real.pi * (n : ℝ)) with ha
  have ha0 : ∀ n, 0 < a n := fun n => by
    simp only [ha]; linarith [weight_ge_one hp1 hc (2 * Real.pi * (n : ℝ))]
  set w : ℤ → ℝ := fun n => a n * japaneseBracket n ^ (2 / p - 2) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (ha0 n).le (Real.rpow_nonneg (by unfold japaneseBracket; positivity) _)
  have hset : {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
      Summable (fun n : ℤ => a n * ‖z n‖ ^ 2 * japaneseBracket n ^ (2 / p - 2))} =
      {z : ℤ → ℂ | (∀ r : ℕ, SobolevSquareSummable (r : ℝ) z) ∧
        Summable (fun n : ℤ => w n * ‖z n‖ ^ 2)} := by
    ext z; simp only [Set.mem_setOf_eq, hw]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, h2.congr fun n => by ring⟩
  have hsum : Summable (fun n : ℤ => w n / a n) := by
    refine (summable_bracket_rpow p hp).congr fun n => ?_
    simp only [hw]; field_simp [(ha0 n).ne']; rfl
  rw [hset]
  exact ⟨measurableSet_good w hw0, measure_good_eq_one a w ha0 hw0 hsum (rate_poly hp1 hc)⟩

end NlsGge.ThirdConsultation.I038M
