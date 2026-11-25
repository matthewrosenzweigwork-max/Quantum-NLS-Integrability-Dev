/- T-033 PRODUCTION02 (codex_luna05, AUTHOR; independent review pending).
   Target NlsGge/Atomic/T/T033.lean, namespace NlsGge.ThirdConsultation.T.
   Head VERBATIM from followup13 STATEMENTS/T.md §T-033; round 17 retains it unchanged.
   Route: specialize the proved W12 exact tilt result at the concrete PDE actual Birkhoff and one-smoothing
   inputs, then use I.actual_ensemble_eq_I for muW/ZW, tiltBounded38_val for the numerator, and Ddelta's
   existing T-031 definition. T-032 exposes the same remainder_tilt_identity38 core used by W12.
   PRODUCTION02 differs from PRODUCTION01 only by importing the module that declares I.actual_ensemble_eq_I,
   identified by root's main-probe diagnostic. -/
import Mathlib
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Atomic.T.T031
import NlsGge.Atomic.T.T032
import NlsGge.Atomic.T.T027
import NlsGge.Atomic.G6.G6014
import NlsGge.Atomic.G6.G6027
import NlsGge.Atomic.G6.G6028
import NlsGge.Atomic.M.M049
import NlsGge.Atomic.R.R110
import NlsGge.Atomic.R.R115
import NlsGge.Atomic.I.I025
import NlsGge.ThirdConsultation.I.ActualEnsembleBridge
import NlsGge.Birkhoff.W12Tilt38g
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem lowerWeightTilt_exact_moment
    (lo up : ℝ) (c : BoundedCoefficients lo up) (delta : ℝ)
    (hd0 : 0 < delta) (hd : delta * up < lo) :
    (∀ᵐ u ∂muW c, EB38 c.val u ≠ ⊤) ∧
    Integrable (fun u : PhysicalL2 => Real.exp (delta * (EB38 c.val u).toReal))
      (muW c) ∧
    (∫ u : PhysicalL2, Real.exp (delta * (EB38 c.val u).toReal) ∂muW c) =
      ZW (tiltBounded38 c hd0 hd) / (ZW c * Ddelta c delta) := by
  have hInt := PDE.actualBirkhoffInput38.tilt_integrable_W12_38 c hd0 hd
  have hAE := PDE.actualBirkhoffInput38.ae_muW38_EB_ne_top c hd0 hd
  have hMoment := PDE.actualBirkhoffInput38.tilt_integral_W12_38 c hd0 hd

  have hActual := NlsGge.ThirdConsultation.I.actual_ensemble_eq_I lo up c
  have hMu : muW c = PDE.actualBirkhoffInput38.muW38 c.val := by
    simpa [muW, PDE.actualMuW, PDE.actualBirkhoffInput38_top] using hActual.2.2.1.symm
  have hZW : ZW c = PDE.actualBirkhoffInput38.ZW38 c.val := by
    simpa [ZW, PDE.actualBirkhoffInput38_top] using hActual.1.symm

  let ct := tiltBounded38 c hd0 hd
  have hTiltVal : ct.val = tiltCoef38 c.val delta := tiltBounded38_val c hd0 hd
  have hActualTilt :=
    NlsGge.ThirdConsultation.I.actual_ensemble_eq_I (lo - delta * up) up ct
  have hZWTilt : ZW ct = PDE.actualBirkhoffInput38.ZW38 (tiltCoef38 c.val delta) := by
    calc
      ZW ct = PDE.actualBirkhoffInput38.ZW38 ct.val := by
        simpa [ZW, PDE.actualBirkhoffInput38_top] using hActualTilt.1.symm
      _ = PDE.actualBirkhoffInput38.ZW38 (tiltCoef38 c.val delta) := by rw [hTiltVal]

  refine ⟨?_, ?_, ?_⟩
  · rw [hMu]
    exact hAE
  · rw [hMu]
    exact hInt
  · rw [hMu, hZWTilt, hZW]
    change
      (∫ u : PhysicalL2, Real.exp (delta * (EB38 c.val u).toReal)
        ∂PDE.actualBirkhoffInput38.muW38 c.val) =
        PDE.actualBirkhoffInput38.ZW38 (tiltCoef38 c.val delta) /
          (PDE.actualBirkhoffInput38.ZW38 c.val * Dtilt38 c.val delta)
    simpa [Ddelta] using hMoment

end
end NlsGge.ThirdConsultation.T
