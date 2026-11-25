import NlsGge.Analysis.FullCoverFourier
import NlsGge.Sobolev.PeriodicBridge

/-! Fourier Hilbert isometries with the normalized Haar convention on circles
of period one and two, together with the interval Parseval normalization. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open AddCircle

namespace NlsGge.Atomic.LIB001
open NlsGge.Pilot NlsGge.Analysis NlsGge.Schur

/-- The normalized-Haar Fourier transform on any positive-period circle is
an isometric linear equivalence onto square-summable complex sequences. -/
def normalizedFourierL2 (T : ℝ) [hT : Fact (0 < T)] :
    Lp ℂ 2 (@AddCircle.haarAddCircle T hT) ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := T)).repr

theorem normalizedFourierL2_apply (T : ℝ) [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) (n : ℤ) :
    normalizedFourierL2 T f n = fourierCoeff f n :=
  fourierBasis_repr f n

theorem normalizedHaar_parseval (T : ℝ) [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 =
      ∫ x : AddCircle T, ‖f x‖ ^ 2 ∂(@AddCircle.haarAddCircle T hT) :=
  tsum_sq_fourierCoeff f

/-- The period-one member on the repository's actual physical L² carrier. -/
def periodOneFourierL2 : PhysicalL2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ => ℂ) 2 :=
  physicalFourierL2

/-- The period-two Fourier isometry on the actual doubled-circle L² carrier. -/
def periodTwoFourierL2 : NlsGge.Schur.SpectralScalarL2 ≃ₗᵢ[ℂ]
    lp (fun _ : ℤ => ℂ) 2 :=
  (fourierBasis (T := (2 : ℝ))).repr

/-- Lifting a physical field to the doubled circle and taking its period-two
Fourier coefficients preserves the physical L² norm. -/
def physicalCoverPeriodTwoFourierL2 : PhysicalL2 →ₗᵢ[ℂ]
    lp (fun _ : ℤ => ℂ) 2 :=
  (periodTwoFourierL2.toLinearIsometry).comp naturalPhysicalCoverL2

/-- The manuscript's minus-reflected Fourier convention is the existing
physical isometry followed by index reflection and multiplication by minus one. -/
def reflectedPeriodOneFourierL2 : PhysicalL2 ≃ₗᵢ[ℂ]
    lp (fun _ : ℤ => ℂ) 2 :=
  reflectedFourierL2

theorem reflectedPeriodOneFourierL2_apply (u : PhysicalL2) (n : ℤ) :
    reflectedPeriodOneFourierL2 u n = -physicalFourier u (-n) := by
  exact reflectedFourierL2_apply u n

theorem interval_parseval (T : ℝ) (hT : 0 < T)
    {f : ℝ → ℂ}
    (hL2 : MemLp f 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    ∑' n : ℤ, ‖fourierCoeffOn hT f n‖ ^ 2 =
      T⁻¹ * ∫ x in (0 : ℝ)..T, ‖f x‖ ^ 2 := by
  simpa [smul_eq_mul] using
    (tsum_sq_fourierCoeffOn (a := (0 : ℝ)) (b := T) (f := f) hT hL2)

end NlsGge.Atomic.LIB001
