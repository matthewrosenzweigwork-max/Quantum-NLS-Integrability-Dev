import NlsGge.Atomic.M.M005
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.ThirdConsultation.M.PeriodicGN036A
import NlsGge.ThirdConsultation.M.PeriodicGN036B

set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.HierarchyRiccati.Core
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.MRiccati

def lowerSobolevCast (i m : ℕ) (u : NlsGge.Atomic.Common.PhysicalSobolev38 (m : ℝ)) :
    NlsGge.Atomic.Common.PhysicalSobolev38 (i : ℝ) :=
  if h : i ≤ m then NlsGge.ThirdConsultation.M.lowerSobolevCast i m h u else 0

end NlsGge.ThirdConsultation.MRiccati

namespace NlsGge.ThirdConsultation.MEstimates

def derivativeSupNorm {m : ℕ} (i : ℕ)
    (u : NlsGge.Atomic.Common.PhysicalSobolev38 (m : ℝ)) : ℝ :=
  if h : i + 1 ≤ m then NlsGge.ThirdConsultation.M.derivativeSupNorm i h u else 0

end NlsGge.ThirdConsultation.MEstimates

namespace NlsGge.GKDefinitionDesign

theorem ordinarySobolevCarrier38_eq_M (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
  ordinarySobolevCarrier38 m u = NlsGge.ThirdConsultation.M.ordinarySobolevCoordinates m u := rfl

theorem physicalSobolevEmbed_eq_M (m : ℕ)
    (u : PhysicalSobolev38 (m : ℝ)) :
  physicalSobolevEmbed m u = NlsGge.ThirdConsultation.M.physicalOfSobolev u := by
  apply physicalFourierL2.injective
  apply lp.ext
  funext n
  rw [physicalFourierL2_apply, physicalFourierL2_apply]
  unfold NlsGge.ThirdConsultation.M.physicalOfSobolev
  rw [riccatiSobolevIteratedDerivativeL2CLMRecovery30First_fourier]
  unfold riccatiSobolevJetCoefficientL2Recovery28Second
  rw [pow_zero, one_mul]
  exact (ordinarySobolevCarrier38_fourier m u n).symm

end NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M

theorem periodic_GN (m i : ℕ) (hm : 0 < m) (hi : i < m) :
  ∃ C : ℝ, 0 < C ∧ ∀ u : SobolevR m,
    NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm i u ≤
      C * ‖u‖ ^ (((i : ℝ) + (1/2 : ℝ)) / (m : ℝ)) *
        ‖physicalOfSobolev u‖ ^
          (1 - ((i : ℝ) + (1/2 : ℝ)) / (m : ℝ)) ∧
    ∀ j : ℕ, j ≤ m →
      ‖physicalSobolevDerivative38 j
        (NlsGge.ThirdConsultation.MRiccati.lowerSobolevCast j m u)‖ ≤
      C * ‖u‖ ^ ((j : ℝ) / (m : ℝ)) *
        ‖physicalOfSobolev u‖ ^ (1 - (j : ℝ) / (m : ℝ)) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨2 ^ (i + 3) * (2 * Real.pi) ^ m, by positivity, fun u => ⟨?_, ?_⟩⟩
  · unfold NlsGge.ThirdConsultation.MEstimates.derivativeSupNorm
    rw [dif_pos (by omega)]
    have h1 := NlsGge.ThirdConsultation.MPeriodicGN.GN_sup m i hi u
    unfold derivativeSupNorm physicalOfSobolev
    rw [show ordinarySobolevCoordinates m u = ordinarySobolevCarrier38 m u from rfl]
    exact h1.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hpi hi.le) (by positivity))
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _))).trans_eq (by ring))
  · intro j hj
    unfold NlsGge.ThirdConsultation.MRiccati.lowerSobolevCast
    rw [dif_pos hj]
    have h1 := NlsGge.ThirdConsultation.MPeriodicGN.GN_deriv m j hj hm u
      (lowerSobolevCast j m hj u) ((physicalSobolevFourierEquiv38 (j : ℝ)).apply_symm_apply _)
    unfold physicalOfSobolev
    rw [show ordinarySobolevCoordinates m u = ordinarySobolevCarrier38 m u from rfl]
    have h2 : (2 * Real.pi) ^ j ≤ 2 ^ (i + 3) * (2 * Real.pi) ^ m :=
      (pow_le_pow_right₀ hpi hj).trans (le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by norm_num)))
    exact h1.trans ((mul_le_mul_of_nonneg_right h2
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (Real.rpow_nonneg (norm_nonneg _) _))).trans_eq (by ring))

end NlsGge.ThirdConsultation.M
