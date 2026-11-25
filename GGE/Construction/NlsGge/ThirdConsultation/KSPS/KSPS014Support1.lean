import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS014Host
import NlsGge.GK38.GradFundamentalDet
import NlsGge.ThirdConsultation.KSPSSupport.A1U01

                                                                                                                    
                                                                                                     
                                                    
                                                                                                              
                                                                                        
                                                                                                        
                                                                                       
                                                                                                                  
                                               
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPSWKB
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS

/-! ### Values at x = 0 -/

theorem prefix_at_zero {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) :
    NlsGge.ThirdConsultation.KSPSRiccati.«prefix» φ b k 0 = 0 := by
  simp [NlsGge.ThirdConsultation.KSPSRiccati.«prefix»]

theorem phaseFactor_at_zero {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor φ b lam 0 = 1 := by
  simp [NlsGge.ThirdConsultation.KSPSRiccati.phaseFactor, prefix_at_zero]

theorem coefficientTrace_at_zero {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) :
    coefficientTrace φ b k 0 = coefficientTraceZero φ b k := by
  simp [coefficientTrace]

theorem sourceRemainderVector_at_zero {N : ℕ} (φ : SobolevC N) (b : Bool)
    (lam : {z : ℂ // z ≠ 0}) : sourceRemainderVector φ b lam 0 = 0 := by
  funext i
  simp [sourceRemainderVector, NlsGge.ThirdConsultation.KSPSVolterra.integrateVector]

theorem wkbColumns_zero
    (N : ℕ) (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0}) :
    KSPSWKB.wkbColumns φ lam 0 = KSPSWKB.initialColumns φ lam.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wkbColumns, wkbColumn, initialColumns, phaseFactor_at_zero, sourceRemainderVector_at_zero]

/-! ### 2x2 adjugate -/

theorem mul_adjugate2 (A : Matrix (Fin 2) (Fin 2) ℂ) :
    A * NlsGge.ThirdConsultation.KSPSVolterra.adjugate2 A = A.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [NlsGge.ThirdConsultation.KSPSVolterra.adjugate2, Matrix.det_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-! ### Reduction of the head to the column identity -/

theorem WKB_monodromy_entries_of_columns (N : ℕ) (φ : SobolevC N) (lam : {z : ℂ // z ≠ 0})
    (hdet : (1 / 2 : ℝ) ≤ ‖Matrix.det (initialColumns φ lam.1)‖)
    (hcol : ∀ (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1),
      wkbColumns φ lam x = fundPair (toPotPair φ) lam.1 ⟨x, hx⟩ * initialColumns φ lam.1) :
    (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      (1 / 2 : ℝ) ≤ ‖Matrix.det (KSPSWKB.wkbColumns φ lam x)‖) ∧
    monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam := by
  have hd0 : Matrix.det (initialColumns φ lam.1) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    norm_num at hdet
  refine ⟨fun x hx => ?_, ?_⟩
  · rw [hcol x hx, Matrix.det_mul, det_fundPair38, one_mul]
    exact hdet
  · unfold explicitWKBMonodromy
    rw [hcol 1 ⟨zero_le_one, le_rfl⟩, Matrix.mul_assoc, mul_adjugate2, Matrix.mul_smul, Matrix.mul_one,
      smul_smul, inv_mul_cancel₀ hd0, one_smul, monodromyPair_eq_fundPair]

/-! ### Endpoint coefficient bounds -/

theorem traceZero_norm_le (f g : PhysicalL2) :
    ‖∫ t in (0 : ℝ)..1, coverRep38 f t - ((1 - t : ℝ) : ℂ) * coverRep38 g t‖ ≤ ‖f‖ + ‖g‖ := by
  have hf := intervalIntegrable_coverRep38_one f
  have hg := intervalIntegrable_coverRep38_one g
  have hbound : ‖∫ t in (0 : ℝ)..1, coverRep38 f t - ((1 - t : ℝ) : ℂ) * coverRep38 g t‖ ≤
      ∫ t in (0 : ℝ)..1, (‖coverRep38 f t‖ + ‖coverRep38 g t‖) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ (hf.norm.add hg.norm)
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
    have ht1 : 1 - t ≤ 1 := by linarith [ht.1]
    calc ‖coverRep38 f t - ((1 - t : ℝ) : ℂ) * coverRep38 g t‖
        ≤ ‖coverRep38 f t‖ + ‖((1 - t : ℝ) : ℂ) * coverRep38 g t‖ := norm_sub_le _ _
      _ = ‖coverRep38 f t‖ + (1 - t) * ‖coverRep38 g t‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0]
      _ ≤ ‖coverRep38 f t‖ + ‖coverRep38 g t‖ := by
          have := norm_nonneg (coverRep38 g t)
          nlinarith
  rw [intervalIntegral.integral_add hf.norm hg.norm] at hbound
  linarith [integral_coverRep38_le_one f, integral_coverRep38_le_one g]

theorem coefficientTraceZero_norm_le {N : ℕ} (φ : SobolevC N) (b : Bool) (k : ℕ) :
    ‖coefficientTraceZero φ b k‖ ≤
      ‖NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k‖ +
        ‖weakDerivative (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k)‖ :=
  traceZero_norm_le _ _

theorem norm_fst_add_snd_le {N : ℕ} (φ : SobolevC N) :
    ‖φ.1‖ + ‖φ.2‖ ≤ 2 * sobolevNorm N φ := by
  have h1 : ‖φ.1‖ ≤ sobolevNorm N φ := by
    unfold sobolevNorm
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖φ.2‖])
  have h2 : ‖φ.2‖ ≤ sobolevNorm N φ := by
    unfold sobolevNorm
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖φ.1‖])
  linarith

theorem endpoint_coefficient_set_bounded
    (N k : ℕ) (hNk : 1 ≤ k ∧ k ≤ N) (B : ℝ) :
    BddAbove ({0} ∪ {r : ℝ | ∃ (φ : SobolevC N) (b : Bool),
      sobolevNorm N φ ≤ max B 0 ∧
      r = ‖KSPSWKB.coefficientTraceZero φ b k‖}) := by
  have hN : 1 ≤ N := le_trans hNk.1 hNk.2
  obtain ⟨D, hD, hH⟩ := NlsGge.ThirdConsultation.KSPSSupport.h161_coef_H1 N hN (2 * max B 0)
    (by positivity)
  refine ⟨(1 + 2 * Real.pi) * D, ?_⟩
  rintro r (hr | ⟨φ, b, hφ, rfl⟩)
  · rw [Set.mem_singleton_iff.mp hr]
    have : 0 ≤ 1 + 2 * Real.pi := by positivity
    positivity
  · have hS : ‖φ.1‖ + ‖φ.2‖ ≤ 2 * max B 0 := by
      have := norm_fst_add_snd_le φ
      linarith
    obtain ⟨h1, hn⟩ := hH φ hS b k hNk.1 hNk.2
    set f := NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b k with hf
    have hL2 : ‖f‖ ≤ physicalSobolevNorm 1 f :=
      NlsGge.ThirdConsultation.KSPSSupport.h161_L2_le_psn1 f h1
    have hd := (psn_deriv 0 (u := f) (by simpa using h1)).2
    have hd' : ‖weakDerivative f‖ ≤ 2 * Real.pi * physicalSobolevNorm 1 f := by
      have e := NlsGge.ThirdConsultation.KSPSSupport.h161_norm_eq_psn0 (weakDerivative f)
      simp only [Nat.cast_zero, zero_add, Nat.cast_one] at hd
      rw [← e]
      exact hd
    have ht := coefficientTraceZero_norm_le φ b k
    rw [← hf] at ht
    have hpi : 0 ≤ 2 * Real.pi := by positivity
    calc ‖coefficientTraceZero φ b k‖ ≤ ‖f‖ + ‖weakDerivative f‖ := ht
      _ ≤ physicalSobolevNorm 1 f + 2 * Real.pi * physicalSobolevNorm 1 f := add_le_add hL2 hd'
      _ = (1 + 2 * Real.pi) * physicalSobolevNorm 1 f := by ring
      _ ≤ (1 + 2 * Real.pi) * D := mul_le_mul_of_nonneg_left hn (by positivity)

theorem coefficientTraceZero_le_bound {N : ℕ} (B : ℝ) (φ : SobolevC N) (hB : sobolevNorm N φ ≤ B)
    (b : Bool) (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
    ‖coefficientTraceZero φ b k‖ ≤ NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k := by
  have hk' := Finset.mem_Icc.mp hk
  exact le_csSup (endpoint_coefficient_set_bounded N k hk' B)
    (Or.inr ⟨φ, b, le_trans hB (le_max_left _ _), rfl⟩)

theorem endpointCoefficientBound_nonneg (N : ℕ) (B : ℝ) (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
    0 ≤ NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k :=
  le_csSup (endpoint_coefficient_set_bounded N k (Finset.mem_Icc.mp hk) B) (Or.inl rfl)

/-- The truncated endpoint sum is at most S/(2|lam|), S the threshold sum. -/
theorem endpointSum_norm_le {N : ℕ} (B : ℝ) (φ : SobolevC N) (hB : sobolevNorm N φ ≤ B)
    (b : Bool) (lam : ℂ) (hlam : 1 ≤ ‖lam‖) :
    ‖-Complex.I * ∑ k ∈ Finset.Icc 1 N,
        ((2 * Complex.I * lam) ^ k)⁻¹ * coefficientTrace φ b k 0‖ ≤
      (∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k) /
        (2 * ‖lam‖) := by
  have hl0 : 0 < 2 * ‖lam‖ := by linarith
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Finset.sum_div]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k hk => ?_))
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hc := coefficientTraceZero_le_bound B φ hB b k hk
  have hc0 := endpointCoefficientBound_nonneg N B k hk
  rw [coefficientTrace_at_zero, norm_mul, norm_inv, norm_pow, norm_mul, norm_mul, Complex.norm_I,
    Complex.norm_ofNat, mul_one]
  have hpow : 2 * ‖lam‖ ≤ (2 * ‖lam‖) ^ k := le_self_pow₀ (by linarith) (by omega)
  have hpos : 0 < (2 * ‖lam‖) ^ k := by positivity
  rw [inv_mul_eq_div]
  calc ‖coefficientTraceZero φ b k‖ / (2 * ‖lam‖) ^ k
      ≤ NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k / (2 * ‖lam‖) ^ k :=
        div_le_div_of_nonneg_right hc hpos.le
    _ ≤ NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k / (2 * ‖lam‖) :=
        div_le_div_of_nonneg_left hc0 hl0 hpow

theorem initialColumns_det_bound (N : ℕ) (B : ℝ) (φ : SobolevC N) (lam : ℂ)
    (hB : sobolevNorm N φ ≤ B) (hlam : WKBThreshold N B lam) :
    (1 / 2 : ℝ) ≤ ‖Matrix.det (initialColumns φ lam)‖ := by
  obtain ⟨_, hT⟩ := hlam
  set S := ∑ k ∈ Finset.Icc 1 N, NlsGge.ThirdConsultation.KSPSVolterra.endpointCoefficientBound N B k
    with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k hk => endpointCoefficientBound_nonneg N B k hk)
  have hT' : 1 + S ≤ ‖lam‖ := hT
  have hl1 : 1 ≤ ‖lam‖ := by linarith
  have hl0 : 0 < 2 * ‖lam‖ := by linarith
  have hhalf : S / (2 * ‖lam‖) ≤ 1 / 2 := by
    rw [div_le_iff₀ hl0]
    linarith
  have ha : ‖alpha φ lam 0‖ ≤ 1 / 2 :=
    (endpointSum_norm_le B φ hB false lam hl1).trans hhalf
  have hb : ‖beta φ lam 0‖ ≤ 1 / 2 :=
    (endpointSum_norm_le B φ hB true lam hl1).trans hhalf
  have hdet : Matrix.det (initialColumns φ lam) = 1 - beta φ lam 0 * alpha φ lam 0 := by
    simp [initialColumns, Matrix.det_fin_two]
  rw [hdet]
  have hab : ‖beta φ lam 0 * alpha φ lam 0‖ ≤ 1 / 4 := by
    rw [norm_mul]
    have := norm_nonneg (beta φ lam 0)
    have := norm_nonneg (alpha φ lam 0)
    nlinarith
  have h1 : ‖(1 : ℂ)‖ - ‖beta φ lam 0 * alpha φ lam 0‖ ≤ ‖1 - beta φ lam 0 * alpha φ lam 0‖ :=
    norm_sub_norm_le _ _
  rw [norm_one] at h1
  linarith

/-- KSPS-014 conclusion from the column identity (Pro support `wkbColumns_eq_fundPair_mul`, an explicit
    hypothesis here; it is the remaining analytic leaf). -/
theorem WKB_monodromy_entries_of_column_identity
    (N : ℕ) (B : ℝ) (φ : SobolevC N)
    (lam : {z : ℂ // z ≠ 0})
    (hB : sobolevNorm N φ ≤ B)
    (hlam : WKBThreshold N B lam.1)
    (hcol : ∀ (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1),
      KSPSWKB.wkbColumns φ lam x =
        fundPair (toPotPair φ) lam.1 ⟨x, hx⟩ * KSPSWKB.initialColumns φ lam.1) :
    (∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      (1 / 2 : ℝ) ≤ ‖Matrix.det (KSPSWKB.wkbColumns φ lam x)‖) ∧
    monodromyPair (toPotPair φ) lam.1 =
      KSPSWKB.explicitWKBMonodromy N φ lam :=
  WKB_monodromy_entries_of_columns N φ lam (initialColumns_det_bound N B φ lam.1 hB hlam) hcol

end
end NlsGge.ThirdConsultation.KSPSWKB
