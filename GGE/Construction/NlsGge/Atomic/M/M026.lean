import Mathlib
import NlsGge.Atomic.M.M026Local
import NlsGge.ThirdConsultation.M.MW1Power
import NlsGge.ThirdConsultation.M.MW2Series
import NlsGge.Atomic.KST.KST012
import NlsGge.Atomic.KST.KST016

   
                                                                               

                                                                                                                  
                                                                                                                   
                                                                                                   
                                                                                                             
                                                                                                         

                                                                                                                        
                                                                                                                  
                                                                                                                
                                                                       
  

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open scoped InnerProduct InnerProductSpace
open NlsGge.Atomic.KST003 NlsGge.Atomic.KST004

private theorem diag_odd_gen_w
    (φ : NlsGge.GK38.PotPair) (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hT : Summable fun j : ℕ =>
      ‖(NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2) ^ j‖)
    (i : Bool) :
    ((lam - (n : ℂ) * (Real.pi : ℂ)) -
        NlsGge.ThirdConsultation.MTwoMode.schurEntry φ n lam hlam i i =
      ∑' j : ℕ, NlsGge.ThirdConsultation.MTwoMode.schurPathTerm φ n lam hlam
        (2 * j + 1) i i) ∧
    (∑' j : ℕ, NlsGge.ThirdConsultation.MTwoMode.schurPathTerm φ n lam hlam
        (2 * j + 1) i i =
      inner ℂ (NlsGge.ThirdConsultation.MTwoMode.schurFrame n i : KSTPairL2)
        (NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam
          ((Ring.inverse
            (1 - NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam ^ 2) :
              NlsGge.ThirdConsultation.MTwoModeSupp.EndH)
            (NlsGge.Atomic.KST012.potentialOnPn
              (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n
              (NlsGge.ThirdConsultation.MTwoMode.schurFrame n i : KSTPairL2))))) :=
  ⟨NlsGge.ThirdConsultation.MTwoModeW.schurDiagonal_eq_odd_w φ n lam hlam hT i,
    (NlsGge.ThirdConsultation.MTwoModeW.hasSum_odd_paths_w φ n lam hlam hT i i).tsum_eq⟩

theorem schur_fourier_remainder_weighted
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ :
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    NlsGge.ThirdConsultation.MTwoMode.offDiagonal φ n lam hlam plus -
        NlsGge.ThirdConsultation.MTwoMode.fourierPotential φ plus
          (if plus then 2 * n else -2 * n) =
      NlsGge.ThirdConsultation.MTwoMode.schurEvenRemainder
        φ n lam hlam plus := by
  have hT := NlsGge.ThirdConsultation.MTwoModeW.summable_sq_powers_of_weighted
    w hw φ hφ n lam hlam hthreshold
  obtain ⟨_, _, hB, hC⟩ := NlsGge.ThirdConsultation.MTwoModeW.reducedBC_fourier_remainders_w
    (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam hT
  cases plus
  · change NlsGge.Atomic.KST016.reducedC
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam -
      NlsGge.Atomic.KST016.coveredCoeff
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) true (-2 * n) =
      NlsGge.Atomic.KST016.remainderC
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam
    rw [hC]
    ring
  · change NlsGge.Atomic.KST016.reducedB
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam -
      NlsGge.Atomic.KST016.coveredCoeff
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) false (2 * n) =
      NlsGge.Atomic.KST016.remainderB
        (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n lam hlam
    rw [hB]
    ring

theorem schur_diagonal_odd_formula_weighted
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ :
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    let T := NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam
    let e : NlsGge.Atomic.KST003.KSTPairL2 :=
      NlsGge.ThirdConsultation.MTwoMode.schurFrame n
        (if plus then false else true)
    let V := NlsGge.Atomic.KST012.potentialOnPn
      (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n
    (if plus then
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalPlus φ n lam hlam
      else
        NlsGge.ThirdConsultation.MTwoMode.schurDiagonalMinus φ n lam hlam) =
        NlsGge.ThirdConsultation.MTwoMode.schurOddRemainder
          φ n lam hlam plus ∧
      NlsGge.ThirdConsultation.MTwoMode.schurOddRemainder
          φ n lam hlam plus =
        inner ℂ e (T ((Ring.inverse (1 - T ^ 2) :
          NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ] NlsGge.Atomic.KST003.KSTPairL2) (V e))) := by
  intro T e V
  have hT := NlsGge.ThirdConsultation.MTwoModeW.summable_sq_powers_of_weighted
    w hw φ hφ n lam hlam hthreshold
  cases plus
  · exact diag_odd_gen_w φ n lam hlam hT true
  · exact diag_odd_gen_w φ n lam hlam hT false

theorem schur_even_remainder_inverse_formula_weighted
    (w : ℤ → ℝ)
    (hw : NlsGge.ThirdConsultation.M.OneDerivativeWeight w)
    (φ : NlsGge.GK38.PotPair)
    (hφ :
      NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ) (lam : ℂ)
    (hlam : lam ∈ NlsGge.Atomic.KST004.spectralStrip n)
    (hthreshold :
      8 * NlsGge.ThirdConsultation.MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
        NlsGge.Atomic.M.M054.indexWeight n)
    (plus : Bool) :
    let T := NlsGge.ThirdConsultation.MTwoMode.ambientT φ n lam hlam
    let i : Bool := if plus then false else true
    let er : NlsGge.Atomic.KST003.KSTPairL2 :=
      NlsGge.ThirdConsultation.MTwoMode.schurFrame n i
    let ec : NlsGge.Atomic.KST003.KSTPairL2 :=
      NlsGge.ThirdConsultation.MTwoMode.schurFrame n (!i)
    let V := NlsGge.Atomic.KST012.potentialOnPn
      (NlsGge.ThirdConsultation.MTwoMode.schurPhysicalPair φ) n
    NlsGge.ThirdConsultation.MTwoMode.schurEvenRemainder
        φ n lam hlam plus =
      inner ℂ er ((T ^ 2) ((Ring.inverse (1 - T ^ 2) :
          NlsGge.Atomic.KST003.KSTPairL2 →L[ℂ] NlsGge.Atomic.KST003.KSTPairL2) (V ec))) := by
  intro T i er ec V
  have hT := NlsGge.ThirdConsultation.MTwoModeW.summable_sq_powers_of_weighted
    w hw φ hφ n lam hlam hthreshold
  cases plus
  · exact (NlsGge.ThirdConsultation.MTwoModeW.hasSum_even_paths_w φ n lam hlam hT true false).tsum_eq
  · exact (NlsGge.ThirdConsultation.MTwoModeW.hasSum_even_paths_w φ n lam hlam hT false true).tsum_eq

end NlsGge.ThirdConsultation.M

end
