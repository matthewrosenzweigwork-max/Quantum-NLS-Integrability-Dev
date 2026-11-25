import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.ThirdConsultation.PDE.CarrierCastCore
import NlsGge.Atomic.KSN.KSN021Host

                                                                                                                
                                                                                                                         
                                                                                                                  
                                                                                                                  
                                                                                                                     
                                                                                                                  
                                                                         

set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.PDE

theorem coe_equiv_real (s : ℝ) (hs : 0 ≤ s) (u : PhysicalSobolev38 s) :
    carrierCoe38 s (physicalSobolevFourierEquiv38 s u) =
      fourierSeq38 (physicalSobolevEmbedRealExponent s hs u) := by
  funext n
  unfold physicalSobolevEmbedRealExponent sequenceSobolevEmbedRealExponent
  show _ = (reflectedFourierL2 (reflectedFourierL2.symm _) : ℤ → ℂ) n
  rw [LinearIsometryEquiv.apply_symm_apply]
  show _ = carrierCoe38 0 (carrierIncl38 hs (physicalSobolevFourierEquiv38 s u)) n
  rw [carrierCoe38_incl38]

theorem tinv_sub_eq (r : ℕ) (z : ℤ → ℂ) (hz : z ∈ seqSobolev38 (r : ℝ)) :
    actualBirkhoffTop38.Tinv z - z =
      fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed r (carrierMk38 (r : ℝ) z hz)) -
        reflectedFourierL2.symm (sequenceSobolevEmbed r (carrierMk38 (r : ℝ) z hz))) := by
  have hz0 : z ∈ seqSobolev38 0 := by
    have := carrierCoe38_mem 0 (carrierIncl38 (r := 0) (s := (r : ℝ)) (Nat.cast_nonneg r) (carrierMk38 (r : ℝ) z hz))
    rwa [carrierCoe38_incl38, carrierCoe38_mk] at this
  have hw : seqToLp38 z hz0 = sequenceSobolevEmbed r (carrierMk38 (r : ℝ) z hz) := by
    apply lp.ext
    funext n
    show z n = carrierCoe38 0 (carrierIncl38 (r := 0) (s := (r : ℝ)) (Nat.cast_nonneg r) (carrierMk38 (r : ℝ) z hz)) n
    rw [carrierCoe38_incl38, carrierCoe38_mk]
  show actualTinv38 z - z = _
  rw [actualTinv38_of_mem z hz0, fourierSeq38_sub]
  funext n
  show fourierSeq38 (actualPhiInv (seqToLp38 z hz0)) n - z n =
    fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed r (carrierMk38 (r : ℝ) z hz))) n -
      (reflectedFourierL2 (reflectedFourierL2.symm (sequenceSobolevEmbed r (carrierMk38 (r : ℝ) z hz))) : ℤ → ℂ) n
  rw [LinearIsometryEquiv.apply_symm_apply, ← hw]
  rfl

theorem actualTinv38_smooth_top
    (hK21 : ∀ (N : ℕ) (hN : 1 ≤ N),
        AnalyticOnNhd ℝ (inverseSmoothing N) Set.univ ∧
        (∀ z : SobolevCarrier38 (N : ℝ),
          fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
            reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∈ seqSobolev38 ((N : ℝ) + 1) ∧
          physicalSobolevEmbedRealExponent ((N : ℝ) + 1) (by positivity) (inverseSmoothing N z) =
            physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
              reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∧
        (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : SobolevCarrier38 (N : ℝ), ‖z‖ ≤ B → ‖inverseSmoothing N z‖ ≤ C))
    (r : ℕ) (hr : 1 ≤ r) :
    ∀ z ∈ seqSobolev38 (r : ℝ),
      actualBirkhoffTop38.Tinv z - z ∈ seqSobolev38 ((r + 1 : ℕ) : ℝ) := by
  intro z hz
  rw [tinv_sub_eq r z hz, show ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 by push_cast; ring]
  exact ((hK21 r hr).2.1 _).1

theorem actualTinv38_analytic_smooth_top
    (hK21 : ∀ (N : ℕ) (hN : 1 ≤ N),
        AnalyticOnNhd ℝ (inverseSmoothing N) Set.univ ∧
        (∀ z : SobolevCarrier38 (N : ℝ),
          fourierSeq38 (physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
            reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∈ seqSobolev38 ((N : ℝ) + 1) ∧
          physicalSobolevEmbedRealExponent ((N : ℝ) + 1) (by positivity) (inverseSmoothing N z) =
            physicalInverseBirkhoff (sequenceSobolevEmbed N z) -
              reflectedFourierL2.symm (sequenceSobolevEmbed N z)) ∧
        (∀ B : ℝ, 0 ≤ B → ∃ C : ℝ, 0 ≤ C ∧
          ∀ z : SobolevCarrier38 (N : ℝ), ‖z‖ ≤ B → ‖inverseSmoothing N z‖ ≤ C))
    (r : ℕ) (hr : 1 ≤ r) :
    AnalyticOnNhd ℝ
      (carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun z => actualBirkhoffTop38.Tinv z - z)
        (actualTinv38_smooth_top hK21 r hr)) Set.univ := by
  have hcast : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by push_cast; ring
  have heq : carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ) (fun z => actualBirkhoffTop38.Tinv z - z)
      (actualTinv38_smooth_top hK21 r hr) =
      fun c => carrierMk38 ((r + 1 : ℕ) : ℝ)
        (carrierCoe38 ((r : ℝ) + 1) (physicalSobolevFourierEquiv38 ((r : ℝ) + 1) (inverseSmoothing r c)))
        (CarrierCastAux.carrier_cast_mem hcast _) := by
    funext c
    apply carrierExt38
    rw [carrierMap38_coe, carrierCoe38_mk, coe_equiv_real ((r : ℝ) + 1) (by positivity),
      ((hK21 r hr).2.1 c).2]
    have hcc : carrierMk38 (r : ℝ) (carrierCoe38 (r : ℝ) c) (carrierCoe38_mem _ c) = c := carrierExt38 rfl
    rw [tinv_sub_eq r _ (carrierCoe38_mem _ c), hcc]
  rw [heq]
  intro c _
  have hA : AnalyticAt ℝ (inverseSmoothing r) c := (hK21 r hr).1 c (mem_univ c)
  have hEA : AnalyticAt ℝ (fun c => physicalSobolevFourierEquiv38 ((r : ℝ) + 1) (inverseSmoothing r c)) c :=
    AnalyticAt.comp (g := fun u => physicalSobolevFourierEquiv38 ((r : ℝ) + 1) u) (f := inverseSmoothing r)
      ((physicalSobolevFourierEquiv38 ((r : ℝ) + 1)).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _) hA
  have hC := CarrierCastAux.carrier_cast_analytic hcast
    (physicalSobolevFourierEquiv38 ((r : ℝ) + 1) (inverseSmoothing r c)) (mem_univ _)
  exact AnalyticAt.comp
    (g := fun y : SobolevCarrier38 ((r : ℝ) + 1) =>
      carrierMk38 ((r + 1 : ℕ) : ℝ) (carrierCoe38 ((r : ℝ) + 1) y) (CarrierCastAux.carrier_cast_mem hcast y))
    (f := fun c => physicalSobolevFourierEquiv38 ((r : ℝ) + 1) (inverseSmoothing r c)) hC hEA

end NlsGge.ThirdConsultation.PDE
