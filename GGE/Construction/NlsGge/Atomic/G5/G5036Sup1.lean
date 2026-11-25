import Mathlib
import NlsGge.Atomic.G5.G5031Host
import NlsGge.Atomic.G5.G5031Sup3
import NlsGge.Atomic.G5.G5FlowBridge
import NlsGge.Atomic.G1.G1082Sup5
import NlsGge.GK38.TauGamma
import NlsGge.ThirdConsultation.G5.G5017Support1

                                                                                       
                                                                                         
                                                                                                                                  
                                                                                                                              
                                                                                            
                                                                               
                                                                                           
                                                                                                                                     
                                                                                                                                 
                                                                                                                                 
                                                                        
                                                                                                                                   
                              
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.LIB

namespace NlsGge.GKDefinitionDesign
namespace G5036Sup1
noncomputable section

/-- An `IsSpectralFlow` curve solves the physical single-gap ODE. -/
theorem isSpectralFlow_hasDerivAt (k : ℤ) (c : ℝ → PhysicalL2) (hflow : IsSpectralFlow k c)
    (t : ℝ) : HasDerivAt c (singleGapField k (c t)) t := by
  have h := (ContinuousLinearMap.fst ℝ PhysicalL2 PhysicalL2).hasFDerivAt.comp_hasDerivAt t (hflow t)
  rw [muSeq_eq_gkMu38] at h
  exact h

/-- At a real point with open m- and n-gaps, `{theta_m,theta_n}` is differentiable and its derivative kills every
    discriminant Hamiltonian field, given G5-035 at that point. -/
theorem anglePoisson_fderiv_hamField (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (hn : gamma2 (realSlice u) n ≠ 0)
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ)
    (h35 : ∀ lam : ℂ, doubleAngleDiscriminantBracket m n (realSlice u) lam = 0) (w : ℂ) :
    DifferentiableAt ℂ (anglePoisson m n) (realSlice u) ∧
      fderiv ℂ (anglePoisson m n) (realSlice u)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) w) = 0 := by
  obtain ⟨Vm, θm, hVm, hxm, hanm, hdm⟩ := hprim u m hm
  obtain ⟨Vn, θn, hVn, hxn, hann, hdn⟩ := hprim u n hn
  have hcm : ContDiffAt ℂ 2 θm (realSlice u) := (hanm _ hxm).contDiffAt
  have hcn : ContDiffAt ℂ 2 θn (realSlice u) := (hann _ hxn).contDiffAt
  have hVo : IsOpen (Vm ∩ Vn) := hVm.inter hVn
  have hxV : realSlice u ∈ Vm ∩ Vn := ⟨hxm, hxn⟩
  have hPeq : anglePoisson m n =ᶠ[𝓝 (realSlice u)] constantPoisson G5031Sup3.Jmap θm θn := by
    filter_upwards [hVo.mem_nhds hxV] with ψ hψ
    simp only [anglePoisson, constantPoisson_apply, hdm ψ hψ.1, hdn ψ hψ.2]
    rfl
  refine ⟨(G5031Sup3.differentiableAt_constantPoisson hcm hcn).congr_of_eventuallyEq hPeq, ?_⟩
  have hF : PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) w =
      G5031Sup3.Jmap (fderiv ℂ (fun ψ : PotPair => discrim ψ w) (realSlice u)) := by
    rw [(hasFDerivAt_gradDiscrimCLM (realSlice u) w).fderiv, G5031Sup3.Jmap_apply,
      NlsGge.ThirdConsultation.G5017Support1.pairGradientCLM_gradDiscrimCLM]
    try rfl
  have hs := G5031Sup3.isSkew_Jmap (fderiv ℂ (anglePoisson m n) (realSlice u))
    (fderiv ℂ (fun ψ : PotPair => discrim ψ w) (realSlice u))
  have h0 : fderiv ℂ (fun ψ : PotPair => discrim ψ w) (realSlice u)
      (G5031Sup3.Jmap (fderiv ℂ (anglePoisson m n) (realSlice u))) = 0 := h35 w
  rw [hF, hs, h0, neg_zero]

/-- GK 18.7 (first step): along an actual isospectral spectral flow the gaps m, n stay open and `{theta_m,theta_n}` is constant. -/
theorem core36 (k m n : ℤ) (c : ℝ → PhysicalL2)
    (hflow : IsSpectralFlow k c)
    (hm : gamma2 (realSlice (c 0)) m ≠ 0) (hn : gamma2 (realSlice (c 0)) n ≠ 0)
    (hiso : ∀ t : ℝ, isospectral (c 0) (c t))
    (hprim : ∀ (w : PhysicalL2) (j : ℤ), gamma2 (realSlice w) j ≠ 0 →
      ∃ (V : Set PotPair) (θ : PotPair → ℂ), IsOpen V ∧ realSlice w ∈ V ∧
        AnalyticOnNhd ℂ θ V ∧ ∀ ψ ∈ V, fderiv ℂ θ ψ = angleDerivative j ψ)
    (h35 : ∀ (u : PhysicalL2) (m n : ℤ), gamma2 (realSlice u) m ≠ 0 →
      gamma2 (realSlice u) n ≠ 0 →
      ∀ lam : ℂ, doubleAngleDiscriminantBracket m n (realSlice u) lam = 0) :
    ∀ t : ℝ, gamma2 (realSlice (c t)) m ≠ 0 ∧ gamma2 (realSlice (c t)) n ≠ 0 ∧
      anglePoisson m n (realSlice (c t)) = anglePoisson m n (realSlice (c 0)) := by
  have hgam : ∀ (j : ℤ) (t : ℝ), gamma2 (realSlice (c t)) j = gamma2 (realSlice (c 0)) j := by
    intro j t
    rw [(tauGamma_real38 (c t) j).2, (tauGamma_real38 (c 0) j).2,
      isospectral_gapLower_eq (hiso t) j, isospectral_gapUpper_eq (hiso t) j]
  have hopen : ∀ t : ℝ, gamma2 (realSlice (c t)) m ≠ 0 ∧ gamma2 (realSlice (c t)) n ≠ 0 :=
    fun t => ⟨by rw [hgam m t]; exact hm, by rw [hgam n t]; exact hn⟩
  have hder : ∀ t : ℝ, HasDerivAt (fun s => anglePoisson m n (realSlice (c s))) 0 t := by
    intro t
    obtain ⟨hmt, hnt⟩ := hopen t
    obtain ⟨hd, hz⟩ := anglePoisson_fderiv_hamField (c t) m n hmt hnt hprim
      (h35 (c t) m n hmt hnt) (muSeq (realSlice (c t)) k)
    have hchain := (hd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t (hflow t)
    have e : ((fderiv ℂ (anglePoisson m n) (realSlice (c t))).restrictScalars ℝ)
        (PoissonSpectral38.spectralDiscrimHamField38 (realSlice (c t))
          (muSeq (realSlice (c t)) k)) = 0 := hz
    rw [e] at hchain
    exact hchain
  intro t
  refine ⟨(hopen t).1, (hopen t).2, ?_⟩
  have hdiff : Differentiable ℝ (fun s => anglePoisson m n (realSlice (c s))) :=
    fun s => (hder s).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff (fun s => (hder s).deriv) t 0

end
end G5036Sup1
end NlsGge.GKDefinitionDesign
