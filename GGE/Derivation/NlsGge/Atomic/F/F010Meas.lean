import Mathlib
import NlsGge.Atomic.F.F010Sup1
import NlsGge.Atomic.F.F010Core

/- F010 MEAS PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/F/F010Meas.lean. Supporting lemmas (no packet increment), answering reviewer note M1 (h794):
   in pinned Mathlib `IsProbabilityMeasure (μ.map f)` holds for every f (Dirac fallback of Measure.map), so the
   F-010 law clauses do not by themselves certify that the pushforwards are genuine. This module exports the
   measurability that the F-010 proof already uses: the literal inverse of the fixed G6 map is continuous
   (F010Aux.continuous_inverseOnSobolev, from G6027 analyticity), the Gaussian realization and the low-mode
   projection are measurable (landed measurable_gaussianRealization38, measurable_PN38), and the density
   is measurable (F010Aux.measurable_dens). Hence finiteGapLaw and finiteGapApprox are true pushforwards.
   Needs ROOT MAIN PROBE (imports F010Sup1/G6027); proof terms checked in mirror selftest F010MEAS_SELFTEST01. -/
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
