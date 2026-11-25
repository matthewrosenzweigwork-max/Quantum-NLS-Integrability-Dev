import Mathlib
import NlsGge.Atomic.KSN.KSN018Host
import NlsGge.Atomic.KSN.KSN010Host
import NlsGge.Atomic.KSN.KSN004Host
import NlsGge.Atomic.KSN.KSN002
import NlsGge.ThirdConsultation.G5033Host

                                                                                                                               
                                                                                                                  
                                                                                                   
                                                                                                                         
                                                                                                                          
                                                                                                                        
                                                                                                              
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

theorem ksn018_sqrt8 : (Real.sqrt 8 : ℂ) = 2 * (Real.sqrt 2 : ℂ) := by
  have h : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h]; push_cast; ring

theorem ksn018_sqrt2_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

theorem ksn018_sqrt2_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact_mod_cast this.ne'

theorem ksn018_smooth_false (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ)
    (hcp : cartesianZExtended n 1 (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      gk16ActualScalarZPlus38 sourceF n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (hZ : sourceZ n 1 (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      ((tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
          muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
        ((1 : ℤ) : ℂ) * Complex.I * antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
          (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) /
          (2 * deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
            (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))) *
        eta n 1 (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)) :
    smoothingCoefficient N x false n =
      xiN38 n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) *
        Complex.exp (Complex.I * betaSum n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)) *
        (((tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
          (1 : ℂ) * Complex.I * antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
            (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) *
            (deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))⁻¹ / 2) *
          eta n 1 (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)) +
      ((rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2 -
        (1 : ℂ) * (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n) / 2) := by
  set φ := pairPotential (N : ℝ) (Nat.cast_nonneg N) x with hφ
  have hZP : gk16ActualScalarZPlus38 sourceF n φ = 2 * sourceZ n 1 φ := by
    rw [← hcp]; unfold sourceZ; ring
  unfold smoothingCoefficient scalarBirkhoff cartesianX cartesianY gk16ScalarXModel38 gk16ScalarYModel38
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hZP, hZ, ksn018_sqrt8]
  have h2 := ksn018_sqrt2_ne
  have hs := ksn018_sqrt2_sq
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  push_cast
  field_simp
  simp only [hs]
  ring

theorem ksn018_smooth_true (N : ℕ) (x : PairScale (N : ℝ)) (n : ℤ)
    (hcm : cartesianZExtended n (-1) (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      gk16ActualScalarZMinus38 sourceF n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x))
    (hZ : sourceZ n (-1) (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) =
      ((tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
          muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
        ((-1 : ℤ) : ℂ) * Complex.I * antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
          (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) /
          (2 * deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
            (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))) *
        eta n (-1) (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)) :
    smoothingCoefficient N x true n =
      xiN38 n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) *
        Complex.exp (-Complex.I * betaSum n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)) *
        (((tauN (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n -
            muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) -
          (-1 : ℂ) * Complex.I * antiDiscrim (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
            (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n) *
            (deltaFactor n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)
              (muSeq (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) n))⁻¹ / 2) *
          eta n (-1) (pairPotential (N : ℝ) (Nat.cast_nonneg N) x)) +
      ((rawCoefficient (N : ℝ) x true (-n) + rawCoefficient (N : ℝ) x false n) / 2 -
        (-1 : ℂ) * (rawCoefficient (N : ℝ) x true (-n) - rawCoefficient (N : ℝ) x false n) / 2) := by
  set φ := pairPotential (N : ℝ) (Nat.cast_nonneg N) x with hφ
  have hZM : gk16ActualScalarZMinus38 sourceF n φ = 2 * sourceZ n (-1) φ := by
    rw [← hcm]; unfold sourceZ; ring
  unfold smoothingCoefficient scalarBirkhoff cartesianX cartesianY gk16ScalarXModel38 gk16ScalarYModel38
  simp only [↓reduceIte]
  rw [hZM, hZ, ksn018_sqrt8]
  have h2 := ksn018_sqrt2_ne
  have hs := ksn018_sqrt2_sq
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  push_cast
  field_simp
  simp only [hs]
  ring

end
end NlsGge.ThirdConsultation.KSN
