import NlsGge.Analysis.NaturalCoverCoefficients
import NlsGge.Schur.ParityBasis

/-! Full signed Fourier support of the actual natural cover.
Every character integrand is proved integrable before coefficient identities.
No multiplier, potential matrix or operator estimate is asserted here. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Analysis
open NlsGge.Pilot NlsGge.Schur

local instance : IsProbabilityMeasure spectralHaar := by
  unfold spectralHaar
  infer_instance

theorem physicalCover_allIntegrand_integrable (u : PhysicalL2) (m : ℤ) :
    Integrable (fun x : SpectralCircle =>
      fourier (-m) x • naturalPhysicalCoverL2 u x) spectralHaar := by
  have hu : Integrable (naturalPhysicalCoverL2 u : SpectralCircle → ℂ) spectralHaar :=
    MemLp.integrable (by norm_num) (Lp.memLp (naturalPhysicalCoverL2 u))
  exact hu.fourier_smul (-m)

theorem naturalPhysicalCoverL2_fourier_odd (u : PhysicalL2) (m : ℤ)
    (hm : m % 2 ≠ 0) :
    fourierCoeff (naturalPhysicalCoverL2 u) m = 0 := by
  have h := (mem_scalarParity_iff_fourier_support 0 (naturalPhysicalCoverL2 u)).mp
    (naturalPhysicalCoverL2_mem_even u) m (by simpa using hm)
  exact (fourierBasis_repr (T := (2 : ℝ)) (naturalPhysicalCoverL2 u) m).symm.trans h

theorem naturalPhysicalCoverL2_fourier_even_index (u : PhysicalL2) (m : ℤ)
    (hm : m % 2 = 0) :
    fourierCoeff (naturalPhysicalCoverL2 u) m = physicalFourier u (m / 2) := by
  have heven : 2 * (m / 2) = m := by omega
  simpa only [heven] using naturalPhysicalCoverL2_fourier_even u (m / 2)

theorem naturalPhysicalCoverL2_fourier_all (u : PhysicalL2) (m : ℤ) :
    fourierCoeff (naturalPhysicalCoverL2 u) m =
      if m % 2 = 0 then physicalFourier u (m / 2) else 0 := by
  by_cases hm : m % 2 = 0
  · rw [if_pos hm]
    exact naturalPhysicalCoverL2_fourier_even_index u m hm
  · rw [if_neg hm]
    exact naturalPhysicalCoverL2_fourier_odd u m hm

end NlsGge.Analysis
