import NlsGge.Spectral.ActualPhysicalL2ZsACFundamentalWellPosedV1
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- The original-convention free diagonal rate. -/
def actualZsFreeRate32 (z : ℂ) (i : Fin 2) : ℂ :=
  if i = 0 then -Complex.I * z else Complex.I * z

/-- The everywhere nonzero inverse free diagonal factor. -/
def actualZsInverseFreeWeight32 (z : ℂ) (t : ℝ) (i : Fin 2) : ℂ :=
  Complex.exp (t • (-actualZsFreeRate32 z i))

theorem actualZsInverseFreeWeight_ne_zero32 (z : ℂ) (t : ℝ) (i : Fin 2) :
    actualZsInverseFreeWeight32 z t i ≠ 0 := Complex.exp_ne_zero _

/-- Only the true off-diagonal potential remains after removing the free evolution.
The division is by a proved nonzero exponential, with no inverse hypothesis. -/
def actualZsInteractionCoefficient32 (U : ℝ → ℂ) (z : ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i k =>
  actualZsInverseFreeWeight32 z t i *
    (if i = k then 0 else zsCoefficientComplex U z t i k) /
      actualZsInverseFreeWeight32 z t k

/-- The actual interaction state, not a termwise conjugation of raw Dyson iterates. -/
def actualZsInteractionState32 (z : ℂ)
    (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ := fun i j =>
  actualZsInverseFreeWeight32 z t i * F t i j

theorem actualZsInteractionGauge_derivative_algebra32
    (U : ℝ → ℂ) (z : ℂ) (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℝ) (i j : Fin 2) :
    (actualZsInverseFreeWeight32 z t i * (-actualZsFreeRate32 z i)) * F t i j +
      actualZsInverseFreeWeight32 z t i * (zsCoefficientComplex U z t * F t) i j =
      (actualZsInteractionCoefficient32 U z t * actualZsInteractionState32 z F t) i j := by
  have h0 := actualZsInverseFreeWeight_ne_zero32 z t 0
  have h1 := actualZsInverseFreeWeight_ne_zero32 z t 1
  fin_cases i <;>
    simp [actualZsInteractionCoefficient32, actualZsInteractionState32,
      Matrix.mul_apply, Fin.sum_univ_two, zsCoefficientComplex,
      actualZsFreeRate32] <;>
    field_simp [h0, h1] <;> ring

/-- The scalar product rule converts the original source equation to the
actual interaction equation. Its source derivative premise is realized below. -/
theorem actualZsInteractionState_hasDerivAt32
    (U : ℝ → ℂ) (z : ℂ) (F : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (t : ℝ) (i j : Fin 2)
    (hF : HasDerivAt (fun s => F s i j) ((zsCoefficientComplex U z t * F t) i j) t) :
    HasDerivAt (fun s => actualZsInteractionState32 z F s i j)
      ((actualZsInteractionCoefficient32 U z t * actualZsInteractionState32 z F t) i j) t := by
  have hw := ((hasDerivAt_id' t).smul_const (-actualZsFreeRate32 z i)).cexp
  have hp := hw.mul hF
  apply hp.congr_deriv
  simpa only [actualZsInverseFreeWeight32, one_smul] using
    actualZsInteractionGauge_derivative_algebra32 U z F t i j

/-- For EVERY actual rough physical L² input, the true Dyson fundamental matrix
after removing its free factor solves the interaction equation almost everywhere.
No continuity of the potential or interaction-series identification is assumed. -/
theorem actualPhysicalZsInteractionState_ae_hasDerivAt32
    (u : PhysicalL2) (z : ℂ) (i j : Fin 2) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 2 →
      HasDerivAt
        (fun s => actualZsInteractionState32 z
          (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) s i j)
        ((actualZsInteractionCoefficient32
          (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z t *
          actualZsInteractionState32 z
            (actualComplexZsDysonTsum (fun x => naturalPhysicalCoverL2 u (x : SpectralCircle)) z) t) i j) t := by
  filter_upwards [actualPhysicalL2ZsDysonTsum_ae_hasDerivAt_entry u z i j] with t ht
  intro hmem
  exact actualZsInteractionState_hasDerivAt32 _ z _ t i j (ht hmem)

end NlsGge.SpectralFoundations
end
