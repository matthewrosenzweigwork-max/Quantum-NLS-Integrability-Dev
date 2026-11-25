import NlsGge.Analysis.NaturalCover
import NlsGge.Schur.ParityFourier
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! Genuine parity and Fourier-coefficient compatibility of the natural cover.
The independent complex fields and original physical Fourier weights are unchanged. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Analysis
open NlsGge.Pilot NlsGge.Schur

local instance : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure
  infer_instance

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

theorem naturalPhysicalCoverL2_halfTranslation (u : PhysicalL2) :
    halfTranslation (naturalPhysicalCoverL2 u) = naturalPhysicalCoverL2 u := by
  apply Lp.ext
  have hs := halfShift_preserving.quasiMeasurePreserving.ae_eq_comp
    (naturalPhysicalCoverL2_ae u)
  filter_upwards [halfTranslation_ae (naturalPhysicalCoverL2 u), hs,
    naturalPhysicalCoverL2_ae u] with x ht hs hu
  change naturalPhysicalCoverL2 u (x + ((1 : ℝ) : SpectralCircle)) =
    u (naturalPhysicalCover (x + ((1 : ℝ) : SpectralCircle))) at hs
  rw [ht, hs, naturalPhysicalCover_halfShift, hu]

theorem naturalPhysicalCoverL2_mem_even (u : PhysicalL2) :
    naturalPhysicalCoverL2 u ∈ scalarParity 0 := by
  apply (mem_scalarParity 0 (naturalPhysicalCoverL2 u)).mpr
  simpa [spectralSign] using naturalPhysicalCoverL2_halfTranslation u

theorem physicalCover_sourceIntegrand_integrable (u : PhysicalL2) (p : ℤ) :
    Integrable (fun x : PhysicalCircle => fourier (-p) x • u x) spatialMeasure := by
  have hu : Integrable (u : PhysicalCircle → ℂ) spatialMeasure :=
    MemLp.integrable (by norm_num) (Lp.memLp u)
  exact hu.fourier_smul (-p)

theorem physicalCover_spectralIntegrand_integrable (u : PhysicalL2) (p : ℤ) :
    Integrable (fun x : SpectralCircle =>
      fourier (-(2 * p)) x • naturalPhysicalCoverL2 u x) spectralHaar := by
  have hu : Integrable (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) spectralHaar :=
    MemLp.integrable (by norm_num) (Lp.memLp (naturalPhysicalCoverL2 u))
  exact hu.fourier_smul (-(2 * p))

/-- Both actual character integrands have already been proved integrable above.
Change of variables uses the original integrand's actual strong measurability,
and does not require an injective cover. -/
theorem naturalPhysicalCoverL2_fourier_even (u : PhysicalL2) (p : ℤ) :
    fourierCoeff (naturalPhysicalCoverL2 u) (2 * p) = physicalFourier u p := by
  have hf := physicalCover_sourceIntegrand_integrable u p
  have hfm : AEStronglyMeasurable
      (fun x : PhysicalCircle => fourier (-p) x • u x)
      (Measure.map naturalPhysicalCover spectralHaar) := by
    rw [naturalPhysicalCover_preserving.map_eq]
    exact hf.aestronglyMeasurable
  change (∫ x : SpectralCircle,
      fourier (-(2 * p)) x • naturalPhysicalCoverL2 u x ∂spectralHaar) =
    ∫ x : PhysicalCircle, fourier (-p) x • u x ∂spatialMeasure
  calc
    _ = ∫ x : SpectralCircle,
        fourier (-p) (naturalPhysicalCover x) • u (naturalPhysicalCover x)
          ∂spectralHaar := by
      apply integral_congr_ae
      filter_upwards [naturalPhysicalCoverL2_ae u] with x hx
      rw [hx, naturalPhysicalCover_fourier, mul_neg]
    _ = _ := by
      have hm := integral_map naturalPhysicalCover_preserving.measurable.aemeasurable hfm
      rw [naturalPhysicalCover_preserving.map_eq] at hm
      exact hm.symm

end NlsGge.Analysis
