import NlsGge.Sobolev.PeriodicBridge
import NlsGge.Sobolev.FiniteFourier
import NlsGge.Analysis.NaturalCover
import NlsGge.Schur.FourierMultiplier
import Mathlib.Tactic

/-! Batch 38: identification of a finite-plane field with its doubled-cover
representative, in the form required by the E02 trace formula
(`hae` hypothesis): the natural cover of `planeL2 N z`, read on `(0,2]`, is a.e.
the real-line field `planeReal N z` (smooth, 1-periodic). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur MeasureTheory
open scoped ENNReal ContDiff

theorem planeReal_cover_ae38 (N : ℕ) (z : FourierPlane N) :
    (fun s : ℝ => (naturalPhysicalCoverL2 (planeL2 N z) : SpectralCircle → ℂ)
        (s : SpectralCircle)) =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 2)] planeReal N z := by
  have h1 := naturalPhysicalCoverL2_ae (planeL2 N z)
  have h2 := naturalPhysicalCover_preserving.quasiMeasurePreserving.ae_eq_comp (planeL2_ae N z)
  have h : (naturalPhysicalCoverL2 (planeL2 N z) : SpectralCircle → ℂ) =ᵐ[spectralHaar]
      (planeField N z ∘ naturalPhysicalCover) := h1.trans h2
  have hv : (naturalPhysicalCoverL2 (planeL2 N z) : SpectralCircle → ℂ)
      =ᵐ[(volume : Measure SpectralCircle)] (planeField N z ∘ naturalPhysicalCover) := by
    rw [NlsGge.Schur.spectral_volume_eq_two_smul]
    exact Measure.ae_smul_measure h (2 : ℝ≥0∞)
  have hr := (AddCircle.measurePreserving_mk (2 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp hv
  have h02 : (0 : ℝ) + 2 = 2 := by norm_num
  rw [h02] at hr
  exact hr

theorem planeReal_smooth38 (N : ℕ) (z : FourierPlane N) :
    ContDiff ℝ ∞ (planeReal N z) :=
  (contDiff_planeReal N z).of_le le_top

end NlsGge.HierarchyRiccati.Core

end
