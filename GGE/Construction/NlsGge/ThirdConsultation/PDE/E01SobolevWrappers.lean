import NlsGge.ThirdConsultation.PDE.BirkhoffTop
import NlsGge.NLS38.LaxConsequences38
import NlsGge.Spectral.ActualLabelledGapActionAllNE02_38
import NlsGge.Atomic.PDE.PDE047

set_option autoImplicit false

open NlsGge.Atomic.Common NlsGge.Pilot NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE

namespace NlsGge.GKDefinitionDesign

noncomputable section

theorem E01_sobolev_diffeomorphism (m : ℕ) :
  AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ ∧
  AnalyticOnNhd ℝ (inverseBirkhoffSobolev m) Set.univ ∧
  Function.LeftInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  Function.RightInverse (inverseBirkhoffSobolev m) (birkhoffSobolev m) ∧
  (∀ u : PhysicalSobolev38 (m : ℝ),
    sequenceSobolevEmbed m (birkhoffSobolev m u) =
      physicalBirkhoff (physicalSobolevEmbed m u)) ∧
  (∀ z : SobolevCarrier38 (m : ℝ),
    physicalSobolevEmbed m (inverseBirkhoffSobolev m z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed m z)) := by
  have hForwardZero :
      AnalyticOnNhd ℝ (birkhoffSobolev 0) Set.univ := by
    have hTC : AnalyticOnNhd ℝ (actualTC38 0) Set.univ := by
      rw [← actualT38_carrier_eq 0]
      exact actualT38_analytic 0
    let e := physicalSobolevFourierEquiv38 ((0 : ℕ) : ℝ)
    have hEq :
        (fun u : PhysicalSobolev38 ((0 : ℕ) : ℝ) => actualTC38 0 (e u)) =
          birkhoffSobolev 0 := by
      funext u
      change birkhoffSobolev 0 (e.symm (e u)) = birkhoffSobolev 0 u
      rw [LinearIsometryEquiv.symm_apply_apply]
    have hComp :
        AnalyticOnNhd ℝ
          (fun u : PhysicalSobolev38 ((0 : ℕ) : ℝ) => actualTC38 0 (e u)) Set.univ := by
      intro u _
      exact (hTC (e u) (Set.mem_univ _)).comp
        ((e.toContinuousLinearEquiv.toContinuousLinearMap).analyticAt u)
    rw [hEq] at hComp
    exact hComp

  have hInverseZero :
      AnalyticOnNhd ℝ (inverseBirkhoffSobolev 0) Set.univ := by
    have hTinvC : AnalyticOnNhd ℝ (actualTinvC38 0) Set.univ := by
      rw [← actualTinv38_carrier_eq 0]
      exact actualTinv38_analytic 0
    let e := physicalSobolevFourierEquiv38 ((0 : ℕ) : ℝ)
    have hEq :
        (fun z : SobolevCarrier38 ((0 : ℕ) : ℝ) => e.symm (actualTinvC38 0 z)) =
          inverseBirkhoffSobolev 0 := by
      funext z
      change e.symm (e (inverseBirkhoffSobolev 0 z)) = inverseBirkhoffSobolev 0 z
      rw [LinearIsometryEquiv.symm_apply_apply]
    have hComp :
        AnalyticOnNhd ℝ
          (fun z : SobolevCarrier38 ((0 : ℕ) : ℝ) => e.symm (actualTinvC38 0 z)) Set.univ := by
      intro z _
      exact ((e.symm.toContinuousLinearEquiv.toContinuousLinearMap).analyticAt
        (actualTinvC38 0 z)).comp (hTinvC z (Set.mem_univ _))
    rw [hEq] at hComp
    exact hComp

  have hForward : AnalyticOnNhd ℝ (birkhoffSobolev m) Set.univ := by
    by_cases hm0 : m = 0
    · subst m
      exact hForwardZero
    · have hm : 1 ≤ m := by omega
      exact (G6027 m hm).1

  have hInverse : AnalyticOnNhd ℝ (inverseBirkhoffSobolev m) Set.univ := by
    by_cases hm0 : m = 0
    · subst m
      exact hInverseZero
    · have hm : 1 ≤ m := by omega
      exact (G6027 m hm).2.1

  have hCompat := birkhoffSobolev_inverse_compatible_all m
  exact ⟨hForward, hInverse, hCompat.1, hCompat.2.1,
    (fun u => (hCompat.2.2.1 u).2),
    (fun z => (hCompat.2.2.2 z).2)⟩

theorem E01_action_conserved
    (u : PhysicalSobolev38 ((1 : ℕ) : ℝ)) (t : ℝ) (n : ℤ) :
  actualGapActionAllE02_38
    (NlsGge.NLS38.nlsFlowL2 t (physicalSobolevEmbed 1 u)) n =
      actualGapActionAllE02_38 (physicalSobolevEmbed 1 u) n := by
  let uL2 : PhysicalL2 := physicalSobolevEmbed 1 u
  have hu : SobolevSquareSummable 1 (physicalFourier uL2) :=
    by simpa only [Nat.cast_one] using
      (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) uL2).mp (physicalSobolevEmbed_mem 1 u)
  exact NlsGge.NLS38.actualGapActionAllE02_38_eq_of_halfTrace_eq
    (NlsGge.NLS38.nlsFlowL2 t uL2) uL2
    (fun z => by
      change NlsGge.ThirdConsultation.PDE.actualHalfTrace
        (NlsGge.NLS38.nlsFlowL2 t uL2) z =
          NlsGge.ThirdConsultation.PDE.actualHalfTrace uL2 z
      exact NlsGge.ThirdConsultation.PDE.actual_halfTrace_h1_conserved hu t z) n

end
end NlsGge.GKDefinitionDesign
