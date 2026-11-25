import Mathlib
import NlsGge.ThirdConsultation.M.MW1Smooth
import NlsGge.ThirdConsultation.M.MRound11Host

   
                                                                                        
                                        

                                                                                                                  
                                                                                                                     

                                                                                                                  
                                                                                                           
                                                                 
                                                                                                            
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.MTwoModeW

open NlsGge.ThirdConsultation.MTwoMode NlsGge.Atomic.M.M054 NlsGge.Atomic.KST003

theorem oneDerivativeWeight_indexWeight :
    NlsGge.ThirdConsultation.M.OneDerivativeWeight indexWeight :=
  ⟨fun _ => 1, fun _ => le_refl _, fun _ => rfl, fun _ _ => by norm_num,
    fun k => (mul_one _).symm⟩

theorem indexWeight_le_of_oneDerivative (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (k : ℤ) : indexWeight k ≤ w k := by
  obtain ⟨v, hv1, _, _, hwv⟩ := hw
  rw [hwv k]
  exact le_mul_of_one_le_right (indexWeight_pos k).le (hv1 k)

theorem potentialEnergy_mono (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (φ : NlsGge.GK38.PotPair) :
    potentialCoefficientEnergy indexWeight φ ≤ potentialCoefficientEnergy w φ := by
  unfold potentialCoefficientEnergy
  refine ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal ?_
  have h : indexWeight k ^ 2 ≤ w k ^ 2 :=
    pow_le_pow_left₀ (indexWeight_pos k).le (indexWeight_le_of_oneDerivative w hw k) 2
  exact mul_le_mul_of_nonneg_right h (by positivity)

theorem potentialNorm_mono (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w) (φ : NlsGge.GK38.PotPair)
    (hφ : potentialCoefficientEnergy w φ ≠ ⊤) :
    potentialCoefficientNorm indexWeight φ ≤ potentialCoefficientNorm w φ :=
  Real.sqrt_le_sqrt (ENNReal.toReal_mono hφ (potentialEnergy_mono w hw φ))

/-- Iteration of the contraction of the landed M-022 square bound on the `w0` carrier. -/
theorem iter_contract (φ : NlsGge.GK38.PotPair)
    (hφ0 : potentialCoefficientEnergy indexWeight φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hq : 4 * potentialCoefficientNorm indexWeight φ ^ 2 / indexWeight n ≤ 1 / 2)
    (g : KSTPairL2) (hg : shiftedPairEnergy indexWeight n false (coefficientPair g) ≠ ⊤) (m : ℕ) :
    shiftedPairEnergy indexWeight n false
        (coefficientPair ((((ambientT φ n lam hlam) ^ 2) ^ m) g)) ≠ ⊤ ∧
      shiftedPairNorm indexWeight n false
        (coefficientPair ((((ambientT φ n lam hlam) ^ 2) ^ m) g)) ≤
        (1 / 2 : ℝ) ^ m * shiftedPairNorm indexWeight n false (coefficientPair g) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have h := NlsGge.ThirdConsultation.M.T_squared_bound indexWeight oneDerivativeWeight_indexWeight
      φ hφ0 n lam hlam ((((ambientT φ n lam hlam) ^ 2) ^ m) g) ih1
    have e : (((ambientT φ n lam hlam) ^ 2) ^ (m + 1)) g =
        T φ n lam hlam (T φ n lam hlam ((((ambientT φ n lam hlam) ^ 2) ^ m) g)) := by
      rw [pow_succ', ContinuousLinearMap.mul_apply, sq, ContinuousLinearMap.mul_apply]
      rfl
    rw [e]
    refine ⟨h.1, h.2.trans ?_⟩
    calc (4 * potentialCoefficientNorm indexWeight φ ^ 2 / indexWeight n) *
          shiftedPairNorm indexWeight n false
            (coefficientPair ((((ambientT φ n lam hlam) ^ 2) ^ m) g))
        ≤ (1 / 2) * ((1 / 2 : ℝ) ^ m * shiftedPairNorm indexWeight n false (coefficientPair g)) :=
          mul_le_mul hq ih2 (Real.sqrt_nonneg _) (by norm_num)
      _ = (1 / 2 : ℝ) ^ (m + 1) * shiftedPairNorm indexWeight n false (coefficientPair g) := by
          ring

/-- Absolute summability of the ambient even powers from the weighted source threshold. -/
theorem summable_sq_powers_of_weighted
    (w : ℤ → ℝ) (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair) (hφ : potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ) (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold : 8 * potentialCoefficientNorm w φ ^ 2 ≤ indexWeight n) :
    Summable fun j : ℕ => ‖(ambientT φ n lam hlam ^ 2) ^ j‖ := by
  have hφ0 : potentialCoefficientEnergy indexWeight φ ≠ ⊤ :=
    ne_top_of_le_ne_top hφ (potentialEnergy_mono w hw φ)
  have hN0 := potentialNorm_mono w hw φ hφ
  have hρ := indexWeight_pos n
  have hq : 4 * potentialCoefficientNorm indexWeight φ ^ 2 / indexWeight n ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ]
    have h0 : 0 ≤ potentialCoefficientNorm indexWeight φ := Real.sqrt_nonneg _
    have := pow_le_pow_left₀ h0 hN0 2
    nlinarith [this, hthreshold]
  set T0 := ambientT φ n lam hlam with hT0
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = Real.sqrt smoothK * potentialCoefficientNorm indexWeight φ :=
    ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hC]; exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound : ∀ m : ℕ, ‖(T0 ^ 2) ^ (m + 1)‖ ≤ ‖T0‖ * C * (1 / 2 : ℝ) ^ m := by
    intro m
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    obtain ⟨hg1, hg2⟩ := T_smooth φ hφ0 n lam hlam f
    obtain ⟨hh1, hh2⟩ := iter_contract φ hφ0 n lam hlam hq (T φ n lam hlam f) hg1 m
    have hnorm := norm_le_shifted n _ hh1
    have e : ((T0 ^ 2) ^ (m + 1)) f = T0 (((T0 ^ 2) ^ m) (T φ n lam hlam f)) := by
      have hc : Commute T0 ((T0 ^ 2) ^ m) := ((Commute.refl T0).pow_right 2).pow_right m
      have e1 : (T0 ^ 2) ^ (m + 1) = (T0 * (T0 ^ 2) ^ m) * T0 := by
        rw [hc.eq, pow_succ, sq, mul_assoc]
      rw [e1, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
      rfl
    rw [e]
    calc ‖T0 (((T0 ^ 2) ^ m) (T φ n lam hlam f))‖
        ≤ ‖T0‖ * ‖((T0 ^ 2) ^ m) (T φ n lam hlam f)‖ := T0.le_opNorm _
      _ ≤ ‖T0‖ * ((1 / 2 : ℝ) ^ m * (C * ‖f‖)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          refine hnorm.trans (hh2.trans ?_)
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [hC]
          exact hg2
      _ = ‖T0‖ * C * (1 / 2 : ℝ) ^ m * ‖f‖ := by ring
  have hg : Summable fun m : ℕ => ‖T0‖ * C * (1 / 2 : ℝ) ^ m :=
    (summable_geometric_two).mul_left (‖T0‖ * C)
  have hs : Summable fun m : ℕ => ‖(T0 ^ 2) ^ (m + 1)‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hbound (by simpa using hg)
  exact (summable_nat_add_iff 1).1 hs

end NlsGge.ThirdConsultation.MTwoModeW

end
