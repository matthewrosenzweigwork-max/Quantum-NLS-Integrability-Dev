import Mathlib
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.G1.ProductBounds
import NlsGge.ThirdConsultation.G1.WkbStructure
import NlsGge.ThirdConsultation.G1.Wkb035A
import NlsGge.Atomic.G1.G1034
import NlsGge.ThirdConsultation.KSPSRiccatiHost
import NlsGge.ThirdConsultation.KSPSSupport
import NlsGge.ThirdConsultation.KSPSSupport.CORE01
import NlsGge.ThirdConsultation.KSPSSupport.RHO01

                                                          
                                                                                                   
                                                                                               
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSSupport
noncomputable section

theorem h150_coef_false {N : ℕ} (φ : SobolevC N) (k : ℕ) :
    KSPSRiccati.coefficient φ false k = wkbR (toPotPair φ) k := rfl

/-- C1: the first coefficient is the negated side input (both sides). -/
theorem h150_C1 {N : ℕ} (φ : SobolevC N) (b : Bool) :
    KSPSRiccati.coefficient φ b 1 = -KSPSRiccati.sideInput φ b := by
  cases b
  · rw [h150_coef_false]
    exact wkbR_one (toPotPair φ)
  · rw [h150_coef_true]
    simp [wkbR_one, KSPSRiccati.sideInput]

/-- C3 (left): the left recurrence is the G1 recurrence. -/
theorem h150_C3_false {N : ℕ} (φ : SobolevC N) (k : ℕ) (hk : 1 ≤ k) :
    KSPSRiccati.coefficient φ false (k + 1) =
      KSPSRiccati.signedDerivative false (KSPSRiccati.coefficient φ false k) +
        physicalProduct (KSPSRiccati.sidePotential φ false)
          (KSPSRiccati.recurrenceProduct φ false k) := by
  show wkbR (toPotPair φ) (k + 1) = weakDerivative (wkbR (toPotPair φ) k) +
    physicalProduct (toPotPair φ).1
      (∑ j ∈ Finset.Icc 1 (k - 1), physicalProduct (wkbR (toPotPair φ) j) (wkbR (toPotPair φ) (k - j)))
  exact wkbR_succ _ k hk

/-- C3 (right): the right recurrence has the opposite derivative sign, and the products pick up
the sign (-1)^k, so the swap recurrence is reproduced exactly. -/
theorem h150_C3_true {N : ℕ} (φ : SobolevC N) (k : ℕ) (hk : 1 ≤ k) :
    KSPSRiccati.coefficient φ true (k + 1) =
      KSPSRiccati.signedDerivative true (KSPSRiccati.coefficient φ true k) +
        physicalProduct (KSPSRiccati.sidePotential φ true)
          (KSPSRiccati.recurrenceProduct φ true k) := by
  have hW := wkbR_succ (Prod.swap (toPotPair φ)) k hk
  have hsum : (∑ j ∈ Finset.Icc 1 (k - 1),
      physicalProduct (((-1 : ℂ) ^ (j + 1)) • wkbR (Prod.swap (toPotPair φ)) j)
        (((-1 : ℂ) ^ (k - j + 1)) • wkbR (Prod.swap (toPotPair φ)) (k - j))) =
      (-1 : ℂ) ^ k • ∑ j ∈ Finset.Icc 1 (k - 1),
        physicalProduct (wkbR (Prod.swap (toPotPair φ)) j) (wkbR (Prod.swap (toPotPair φ)) (k - j)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    rw [physicalProduct_smul_left, physicalProduct_smul_right, smul_smul,
      h150_sign_pair j (k - j) k (by omega)]
  show ((-1 : ℂ) ^ (k + 1 + 1)) • wkbR (Prod.swap (toPotPair φ)) (k + 1) =
    -weakDerivative (((-1 : ℂ) ^ (k + 1)) • wkbR (Prod.swap (toPotPair φ)) k) +
      physicalProduct (Prod.swap (toPotPair φ)).1
        (∑ j ∈ Finset.Icc 1 (k - 1),
          physicalProduct (((-1 : ℂ) ^ (j + 1)) • wkbR (Prod.swap (toPotPair φ)) j)
            (((-1 : ℂ) ^ (k - j + 1)) • wkbR (Prod.swap (toPotPair φ)) (k - j)))
  rw [hW, hsum, physicalProduct_smul_right, weakDerivative_smul,
    show (-1 : ℂ) ^ (k + 1 + 1) = (-1 : ℂ) ^ k by ring,
    show (-1 : ℂ) ^ (k + 1) = -(-1 : ℂ) ^ k by ring]
  simp only [neg_smul, neg_neg, smul_add]

/-- C3 for both sides: the productInL2 facts and the signed recurrence at index k+1 (1 <= k <= N). -/
theorem h150_C3 {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (b : Bool) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    (∀ j ∈ Finset.Icc 1 (k - 1),
      productInL2 (KSPSRiccati.coefficient φ b j) (KSPSRiccati.coefficient φ b (k - j))) ∧
    productInL2 (KSPSRiccati.sidePotential φ b) (KSPSRiccati.recurrenceProduct φ b k) ∧
    KSPSRiccati.coefficient φ b (k + 1) =
      KSPSRiccati.signedDerivative b (KSPSRiccati.coefficient φ b k) +
        physicalProduct (KSPSRiccati.sidePotential φ b) (KSPSRiccati.recurrenceProduct φ b k) := by
  refine ⟨fun j hj => ?_, productInL2_of_H1 _ _ (h150_side_H1 N hN φ b), ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact productInL2_of_H1 _ _ (h150_coef_H1 N hN φ b j h1 (by omega))
  · cases b
    · exact h150_C3_false φ k hk1
    · exact h150_C3_true φ k hk1

end
end NlsGge.ThirdConsultation.KSPSSupport
