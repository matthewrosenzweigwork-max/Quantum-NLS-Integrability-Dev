import Mathlib
import NlsGge.Atomic.G5.G5002
import NlsGge.Atomic.G5.G5003Chain
import NlsGge.Atomic.G5.G5017Host
import NlsGge.ThirdConsultation.G5.G5017Support1

                                                                                                                  
                                                                                                         
                                                                                                                           
                                                                                                                              
                                                                                                                
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.ThirdConsultation.G5017Support1

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5003 (n a : ℤ) (ha : a = 1 ∨ a = -1)
    (u : PhysicalL2) (hu : gamma2 (realSlice u) n = 0) :
  let φ := realSlice u
  pairGradient (cartesianZExtended n a) φ =
    (2 : ℂ) • (pairGradient (fun ψ => tauN ψ n) φ -
      pairGradient (fun ψ => muSeq ψ n) φ) +
    (2 * (a : ℂ) * Complex.I) •
      (antiDiscrim φ (muSeq φ n) • pairGradient (radiusQuotient n) φ +
        radiusQuotient n φ •
          (pairGradient (fun ψ => antiDiscrim ψ (muSeq φ n)) φ +
            deriv (antiDiscrim φ) (muSeq φ n) •
              pairGradient (fun ψ => muSeq ψ n) φ)) := by
  intro φ
  obtain ⟨D, hHZ, hHLead, -, -⟩ := g5002_complex n a ha u hu
  have hφB : φ ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  have hgk : φ ∈ gkW := g5001_gk φ hφB
  obtain ⟨V, hVn, hVo, hVS, hq, hψ, -⟩ := G5001 n u
  have hφV : φ ∈ V := mem_of_mem_nhds hVn
  have hτ : DifferentiableAt ℂ (fun ψ : PotPair => tauN ψ n) φ := (tauN_analytic n φ hgk).differentiableAt
  have hμ : DifferentiableAt ℂ (fun ψ : PotPair => muSeq ψ n) φ :=
    (analyticOnNhd_muSeq_complex38 n φ hgk).differentiableAt
  have hqd : DifferentiableAt ℂ (radiusQuotient n) φ := (hq φ hφV).differentiableAt
  have hch := g5003_chain φ (fun ψ : PotPair => muSeq ψ n) hμ
  have hLeadfun : cartesianLeading n a = fun ψ : PotPair =>
      2 * (tauN ψ n - muSeq ψ n) + 2 * (a : ℂ) * Complex.I * radiusQuotient n ψ *
        antiDiscrim ψ (muSeq ψ n) := by
    funext ψ; rfl
  have hH : HasFDerivAt (cartesianLeading n a)
      ((2 : ℂ) • (fderiv ℂ (fun ψ : PotPair => tauN ψ n) φ - fderiv ℂ (fun ψ : PotPair => muSeq ψ n) φ) +
        ((2 * (a : ℂ) * Complex.I * radiusQuotient n φ) •
            (fderiv ℂ (fun ψ : PotPair => antiDiscrim ψ (muSeq φ n)) φ +
              deriv (antiDiscrim φ) (muSeq φ n) • fderiv ℂ (fun ψ : PotPair => muSeq ψ n) φ) +
          antiDiscrim φ (muSeq φ n) •
            ((2 * (a : ℂ) * Complex.I) • fderiv ℂ (radiusQuotient n) φ))) φ := by
    rw [hLeadfun]
    exact ((hτ.hasFDerivAt.sub hμ.hasFDerivAt).const_mul 2).add
      ((hqd.hasFDerivAt.const_mul (2 * (a : ℂ) * Complex.I)).mul hch)
  have hD := hHLead.unique hH
  have hfd := hHZ.fderiv.trans hD
  unfold pairGradient
  rw [hfd]
  have key : ∀ L : PotPair →L[ℂ] ℂ, pairGradientCLM L = pairGradientL L := fun L => rfl
  simp only [key, map_add, map_sub, map_smul]
  module

end
end NlsGge.GKDefinitionDesign
