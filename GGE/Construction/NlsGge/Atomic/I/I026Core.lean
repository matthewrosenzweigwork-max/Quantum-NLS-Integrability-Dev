import Mathlib
import NlsGge.Atomic.I.IEnsembleCore
import NlsGge.Birkhoff.H03Diagonal38b

                                                                                                                 
                                                                                  
                                                                                                              
                                                                                                                
                                                                                                                      
                                                                                                                 
                                                                                                                  
                                                                                                                    
                                                                                                                        
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.I

namespace NlsGge.ThirdConsultation.I026C

/-- The house test on `h^m` attached to an ordinary-Fourier test on `H^m`. -/
def houseTest (m : ℕ) (F : SobolevHilbert (m : ℝ) →ᵇ ℝ) : SobolevCarrier38 (m : ℝ) →ᵇ ℝ :=
  F.compContinuous ⟨fun x => ofCarrier38 (m : ℝ) (reflC38 (m : ℝ) x), continuous_physFS_comp38 m⟩

theorem houseTest_apply (m : ℕ) (F : SobolevHilbert (m : ℝ) →ᵇ ℝ) (u : PhysicalL2) :
    houseTest m F (physH38 m u) = F (physFS38 m u) := rfl

theorem i026_of (Bk : BirkhoffTop38) (hB : ∀ z : ℤ → ℂ, Bk.cleanΦinv z = physicalOfSequence z)
    (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (Λ : ℕ → Finset ℤ) (hΛ : IsExhaustion38 Λ) :
    let W := weight c.val
    Tendsto (fun N : ℕ => finiteRelativeNormalizer W (Λ N)) atTop
      (𝓝 (limitNormalizer W)) ∧
    (∀ N : ℕ, finiteRelativeNormalizer W (Λ N) =
      ∫ z : ℤ → ℂ, Real.exp (-remainderForWeight W
        (physicalOfSequence (projFin38 (Λ N) z))) ∂fullWeightSequenceGaussian c.val) ∧
    ∀ m : ℕ, IsProbabilityMeasure ((physicalLaw W).map (physFS38 m)) ∧
      (∀ N : ℕ, IsProbabilityMeasure ((finiteGapLaw W (Λ N)).map (physFS38 m))) ∧
      ∀ F : SobolevHilbert (m : ℝ) →ᵇ ℝ,
        Tendsto (fun N : ℕ => ∫ u : PhysicalL2, F (physFS38 m u) ∂finiteGapLaw W (Λ N))
          atTop (𝓝 (∫ u : PhysicalL2, F (physFS38 m u) ∂physicalLaw W)) := by
  dsimp only
  obtain ⟨hl, _hlu, hb⟩ := c.property
  have hb' : ∀ j : ℕ, lower ≤ c.val j := fun j => (hb j).1
  have hu' : ∀ j : ℕ, c.val j ≤ upper := fun j => (hb j).2
  have hW := weight_continuous38 hl hb' hu'
  have hfin := fun N : ℕ => NlsGge.ThirdConsultation.IEnsC.ensemble_finite_of Bk hB lower upper c (Λ N)
  have hZW := NlsGge.ThirdConsultation.IEnsC.ZW_eq_of Bk hB lower upper c
  have hmuW := NlsGge.ThirdConsultation.IEnsC.muW_eq_of Bk hB lower upper c
  obtain ⟨⟨hden, -⟩, hweak⟩ := Bk.weak_convergence_S04_38 lower upper c.val hl hb' hu' hΛ
  refine ⟨?_, fun N => ?_, fun m => ⟨?_, fun N => ?_, fun F => ?_⟩⟩
  · rw [← hZW]
    exact hden.congr (fun N => (hfin N).1)
  · rw [← (hfin N).1, Bk.ZΛ38_eq_integral_global lower upper c.val hl hb' hu' (Λ N)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [Bk.Rbar38_of_mem c.val (projFin38_mem_Omega038 c.val (Λ N) z),
      ← NlsGge.ThirdConsultation.I017C.remainderForWeight_eq c.val hW, hB]
  · rw [← hmuW]
    haveI := Bk.isProbabilityMeasure_muW38 lower upper c.val hl hb' hu'
    exact (Measure.isProbabilityMeasure_map_iff (measurable_physFS38 m).aemeasurable).2 inferInstance
  · rw [← (hfin N).2.2]
    haveI := Bk.isProbabilityMeasure_nu38 lower upper c.val hl hb' hu' (Λ N)
    exact (Measure.isProbabilityMeasure_map_iff (measurable_physFS38 m).aemeasurable).2 inferInstance
  · have h := hweak m (houseTest m F)
    simp only [houseTest_apply] at h
    rw [← hmuW]
    exact h.congr (fun N => by rw [(hfin N).2.2])

end NlsGge.ThirdConsultation.I026C
