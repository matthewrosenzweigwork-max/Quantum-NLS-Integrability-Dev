import Mathlib
import NlsGge.Atomic.F.F010Sup1
import NlsGge.Atomic.F.F010Core

                                                                                                 
                                                                                                             
                                                                                                               
                                                                                                            
                                                                                                         
                                                                                                           
                                                                                                        
                                                                                                         
                                                                                                                 
set_option autoImplicit false
noncomputable section
open MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff

namespace NlsGge.ThirdConsultation.F010Aux

theorem measurable_inverseOnSobolev (m : ℕ) (hm : 2 ≤ m) :
    Measurable (NlsGge.ThirdConsultation.F.inverseOnSobolev m) :=
  (continuous_inverseOnSobolev m hm).measurable

theorem measurable_inverseOnSequence (m : ℕ) (hm : 2 ≤ m) :
    Measurable (NlsGge.ThirdConsultation.F.inverseOnSequence m) :=
  (measurable_inverseOnSobolev m hm).comp measurable_gaussianRealization38

theorem measurable_finiteGapField (m N : ℕ) (hm : 2 ≤ m) :
    Measurable (NlsGge.ThirdConsultation.F.finiteGapField m N) :=
  (measurable_inverseOnSobolev m hm).comp (measurable_PN38 m N)

theorem measurable_finiteDensity (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) :
    Measurable (NlsGge.ThirdConsultation.F.finiteDensity m β) :=
  measurable_dens hm hβ (measurable_inverseOnSequence m hm)

/-- The finite-gap law is a genuine pushforward: its values are given by preimages. -/
theorem finiteGapLaw_apply (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) {s : Set (Hm1 m)}
    (hs : MeasurableSet s) :
    NlsGge.ThirdConsultation.F.finiteGapLaw m β s =
      ((ENNReal.ofReal (NlsGge.ThirdConsultation.F.finiteNormalizer m β))⁻¹ •
        (gammaM38 m β).withDensity
          (fun z => ENNReal.ofReal (NlsGge.ThirdConsultation.F.finiteDensity m β z)))
        (NlsGge.ThirdConsultation.F.inverseOnSequence m ⁻¹' s) :=
  Measure.map_apply (measurable_inverseOnSequence m hm) hs

theorem finiteGapApprox_apply (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (N : ℕ) {s : Set (Hm1 m)}
    (hs : MeasurableSet s) :
    NlsGge.ThirdConsultation.F.finiteGapApprox m β N s =
      ((ENNReal.ofReal (NlsGge.ThirdConsultation.F.finiteGapNormalizer m β N))⁻¹ •
        (gammaM38 m β).withDensity
          (fun z => ENNReal.ofReal
            (Real.exp (-Rm38 m β (NlsGge.ThirdConsultation.F.finiteGapField m N z)))))
        (NlsGge.ThirdConsultation.F.finiteGapField m N ⁻¹' s) :=
  Measure.map_apply (measurable_finiteGapField m N hm) hs

end NlsGge.ThirdConsultation.F010Aux
