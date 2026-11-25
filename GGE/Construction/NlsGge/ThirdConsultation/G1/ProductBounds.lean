import Mathlib
import NlsGge.ThirdConsultation.G1.Round5
import NlsGge.Atomic.LIB.LIB087
import NlsGge.NLS38.SeqConv38a
import NlsGge.NLS38.NonlinCarrier38

                                                                                                            
                                                                                                     
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem physicalSobolev_iff_ordinary (r : ℝ) (u : PhysicalL2) :
    physicalSobolev r u ↔ SobolevSquareSummable r (physicalFourier u) := by
  rw [← fourierSeq38_mem_iff r u, mem_seqSobolev38_iff]
  rfl

theorem productInL2_of_H1 (u v : PhysicalL2) (hu : physicalSobolev 1 u) : productInL2 u v := by
  have hu1 := (physicalSobolev_iff_ordinary 1 u).1 hu
  have h := NlsGge.Atomic.LIB006.h1MulL2_coe_ae u hu1 v
  exact (Lp.memLp (NlsGge.Atomic.LIB005.h1MulL2 u hu1 v)).ae_eq h

theorem physicalProduct_domain_of_H1
    (u v : PhysicalL2)
    (hu : physicalSobolev 1 u) (hv : physicalSobolev 1 v) :
    productInL2 u v :=
  productInL2_of_H1 u v hu

theorem physicalProduct_eq_h1MulL2 (u v : PhysicalL2)
    (hu1 : SobolevSquareSummable 1 (physicalFourier u)) :
    physicalProduct u v = NlsGge.Atomic.LIB005.h1MulL2 u hu1 v := by
  have hd : productInL2 u v := productInL2_of_H1 u v ((physicalSobolev_iff_ordinary 1 u).2 hu1)
  apply Lp.ext
  filter_upwards [physicalProduct_ae u v hd, NlsGge.Atomic.LIB006.h1MulL2_coe_ae u hu1 v] with x h1 h2
  rw [h1, h2]

theorem psn_eq_hn (m : ℕ) (u : PhysicalL2) :
    physicalSobolevNorm (m : ℝ) u = hn m (fourierSeq38 u) := by
  unfold physicalSobolevNorm hn
  congr 1
  refine tsum_congr (fun n => ?_)
  have h : Real.rpow (japaneseBracket n) (2 * (m : ℝ)) = japaneseBracket n ^ (2 * m) := by
    rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_natCast _ _
  rw [h]
  rfl

theorem psn_eq_L2 (m : ℕ) (u : PhysicalL2) (hu : SobolevSquareSummable (m : ℝ) (physicalFourier u)) :
    physicalSobolevNorm (m : ℝ) u =
      ‖NlsGge.Pilot.physicalSobolevL2 (m : ℝ) u hu‖ := by
  have h := NlsGge.Pilot.physicalSobolevL2_norm_sq (m : ℝ) u hu
  rw [← Real.sqrt_sq (norm_nonneg (NlsGge.Pilot.physicalSobolevL2 (m : ℝ) u hu)), h]
  unfold physicalSobolevNorm
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr (fun n => ?_)
  have hb : japaneseBracket (-n) = japaneseBracket n := by simp [japaneseBracket]
  simp only [Equiv.neg_apply, hb]
  have e : ‖(reflectedFourierL2 u (-n))‖ = ‖physicalFourier u n‖ := by
    have := fourierSeq38_apply u (-n)
    simp only [neg_neg] at this
    show ‖fourierSeq38 u (-n)‖ = _
    rw [this, norm_neg]
  rw [e]

end NlsGge.GKDefinitionDesign
end
