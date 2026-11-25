import Mathlib
import NlsGge.ThirdConsultation.M.MOdd4Core
import NlsGge.Atomic.M.M018Charge
import NlsGge.Atomic.M.M006
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.G1.NormCalculus
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.Birkhoff.BirkhoffAPI38

                                                                             
                                                                                                                 
                                                                                                                      
                                                                   
                                                    
                                                                                                                     
                                          
                                                                                                                   
                                                                                                           
                                                                     
                                                                                              
                                                                                            
                                                                                                   
                                                                                                             
                                                                                                               
                                                                         
set_option autoImplicit false
open Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.Birkhoff
open NlsGge.Sobolev38 NlsGge.Atomic.Common
open scoped ContDiff

namespace NlsGge.ThirdConsultation.MOdd
noncomputable section

theorem physicalOfSobolev_injective (m : ℕ) :
    Function.Injective (NlsGge.ThirdConsultation.M.physicalOfSobolev :
      NlsGge.ThirdConsultation.M.SobolevR m → PhysicalL2) := by
  intro x y h
  apply (physicalSobolevFourierEquiv38 (m : ℝ)).injective
  apply carrierCoe38_injective
  funext n
  rw [← NlsGge.ThirdConsultation.M018C.fourierSeq38_physicalOfSobolev,
    ← NlsGge.ThirdConsultation.M018C.fourierSeq38_physicalOfSobolev, h]

theorem physicalOfSobolev_lowerSobolevCast' (i m : ℕ) (him : i ≤ m)
    (u : NlsGge.ThirdConsultation.M.SobolevR m) :
    NlsGge.ThirdConsultation.M.physicalOfSobolev (NlsGge.ThirdConsultation.M.lowerSobolevCast i m him u) =
      NlsGge.ThirdConsultation.M.physicalOfSobolev u := by
  rw [← physicalSobolevEmbed_eq_M, ← physicalSobolevEmbed_eq_M]
  apply fourierSeq38_injective
  funext n
  rw [physicalSobolevEmbed_fourier, physicalSobolevEmbed_fourier]
  unfold NlsGge.ThirdConsultation.M.lowerSobolevCast
  rw [LinearIsometryEquiv.apply_symm_apply, carrierCoe38_incl38]

theorem continuous_lowerSobolevCast (i m : ℕ) (him : i ≤ m) :
    Continuous (NlsGge.ThirdConsultation.M.lowerSobolevCast i m him) := by
  unfold NlsGge.ThirdConsultation.M.lowerSobolevCast
  exact (physicalSobolevFourierEquiv38 (i : ℝ)).symm.continuous.comp
    ((carrierIncl38 _).continuous.comp (physicalSobolevFourierEquiv38 (m : ℝ)).continuous)

/-- Every `H^N` field has a real-slice pair lift in `SobolevC N`. -/
theorem exists_realSlice_lift (N : ℕ) (x : NlsGge.ThirdConsultation.M.SobolevR N) :
    ∃ ψ : NlsGge.ThirdConsultation.KSPS.SobolevC N,
      NlsGge.ThirdConsultation.KSPS.toPotPair ψ =
        realSlice (NlsGge.ThirdConsultation.M.physicalOfSobolev x) := by
  have h1 : physicalSobolev (N : ℝ) (NlsGge.ThirdConsultation.M.physicalOfSobolev x) :=
    (NlsGge.ThirdConsultation.M018C.pairSobolev_realSlice N x).1
  have h2 : fourierSeq38 (star (NlsGge.ThirdConsultation.M.physicalOfSobolev x)) ∈ seqSobolev38 (N : ℝ) :=
    (physicalSobolev_iff_mem N _).1 (g2045b_psob_star (N : ℝ) _ h1)
  refine ⟨(x, (physicalSobolevFourierEquiv38 (N : ℝ)).symm (carrierMk38 (N : ℝ) _ h2)), Prod.ext ?_ ?_⟩
  · exact physicalSobolevEmbed_eq_M N x
  · show physicalSobolevEmbed N ((physicalSobolevFourierEquiv38 (N : ℝ)).symm (carrierMk38 (N : ℝ) _ h2)) =
      star (NlsGge.ThirdConsultation.M.physicalOfSobolev x)
    apply fourierSeq38_injective
    funext n
    rw [physicalSobolevEmbed_fourier]
    simp

end
end NlsGge.ThirdConsultation.MOdd

namespace NlsGge.ThirdConsultation.M
noncomputable section

theorem odd_hierarchy_charge_eq_signedCharge
    (m : ℕ) (hm : 1 ≤ m) (u : SobolevR m)
    (φ : KSPS.SobolevC (2 * m))
    (hpair : KSPS.toPotPair φ = realSlice (physicalOfSobolev u)) :
    hierarchyCharge φ ⟨2 * m + 1, (by omega), (by omega)⟩ =
      (((-1 : ℝ) ^ (m + 1) * signedCharge m u : ℝ) : ℂ) := by
  have hle : m ≤ 2 * m := by omega
  set w : SobolevR (2 * m) := φ.1 with hwdef
  have hw : physicalOfSobolev w = physicalOfSobolev u := by
    have h := congrArg Prod.fst hpair
    rw [realSlice_fst] at h
    rw [← h, hwdef, ← physicalSobolevEmbed_eq_M]
    rfl
  have hφw : KSPS.toPotPair φ = realSlice (physicalOfSobolev w) := by rw [hpair, hw]
  have hu : lowerSobolevCast m (2 * m) hle w = u := by
    apply NlsGge.ThirdConsultation.MOdd.physicalOfSobolev_injective m
    rw [NlsGge.ThirdConsultation.MOdd.physicalOfSobolev_lowerSobolevCast', hw]
  have hdense : DenseRange ((↑) : PhysicalFourierPolynomial38 ((2 * m : ℕ) : ℝ) → SobolevR (2 * m)) :=
    UniformSpace.Completion.denseRange_coe
  obtain ⟨v, hvmem, hvlim⟩ := mem_closure_iff_seq_limit.1 (hdense w)
  choose p hp using hvmem
  have hsm : ∀ j, ∃ (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f 1),
      RepresentsSmoothField (v j) f hf hper := by
    intro j
    obtain ⟨f, hf, hper, hrep⟩ := exists_smooth_of_polynomial (2 * m) (p j)
    rw [hp j] at hrep
    exact ⟨f, hf, hper, hrep⟩
  choose f hf hper hrep using hsm
  choose ψ hψ using fun j => NlsGge.ThirdConsultation.MOdd.exists_realSlice_lift (2 * m) (v j)
  have hj : ∀ j, hierarchyCharge (ψ j) ⟨2 * m + 1, (by omega), (by omega)⟩ =
      (((-1 : ℝ) ^ (m + 1) * signedCharge m (lowerSobolevCast m (2 * m) hle (v j)) : ℝ) : ℂ) := by
    intro j
    have hrep' : RepresentsSmoothField (lowerSobolevCast m (2 * m) hle (v j)) (f j) (hf j) (hper j) := by
      unfold RepresentsSmoothField
      rw [NlsGge.ThirdConsultation.MOdd.physicalOfSobolev_lowerSobolevCast']
      exact hrep j
    have hpair' : KSPS.toPotPair (ψ j) =
        realSlice (physicalOfSobolev (lowerSobolevCast m (2 * m) hle (v j))) := by
      rw [NlsGge.ThirdConsultation.MOdd.physicalOfSobolev_lowerSobolevCast']
      exact hψ j
    exact NlsGge.ThirdConsultation.MOdd.odd_hierarchy_charge_eq_signedCharge_smooth m hm
      (lowerSobolevCast m (2 * m) hle (v j)) (ψ j) (f j) (hf j) (hper j) hrep' hpair'
  have hL : Tendsto (fun j => hierarchyCharge (ψ j) ⟨2 * m + 1, (by omega), (by omega)⟩) atTop
      (𝓝 (hierarchyCharge φ ⟨2 * m + 1, (by omega), (by omega)⟩)) :=
    NlsGge.ThirdConsultation.M018C.hierarchyCharge_tendsto_of_lift (2 * m + 1) (by omega) w v ψ φ
      hvlim hψ hφw
  have hR : Tendsto (fun j => hierarchyCharge (ψ j) ⟨2 * m + 1, (by omega), (by omega)⟩) atTop
      (𝓝 ((((-1 : ℝ) ^ (m + 1) * signedCharge m u : ℝ) : ℂ))) := by
    simp only [hj]
    rw [← hu]
    have hc : Continuous (fun x : SobolevR (2 * m) =>
        (((-1 : ℝ) ^ (m + 1) * signedCharge m (lowerSobolevCast m (2 * m) hle x) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_const.mul ((continuous_signedCharge m).comp
        (NlsGge.ThirdConsultation.MOdd.continuous_lowerSobolevCast m (2 * m) hle)))
    exact (hc.tendsto w).comp hvlim
  exact tendsto_nhds_unique hL hR

end
end NlsGge.ThirdConsultation.M
