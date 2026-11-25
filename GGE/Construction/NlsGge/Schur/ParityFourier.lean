import NlsGge.Schur.FourierMultiplier
import NlsGge.Schur.ResonantIndices
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Actual half-period translation and the physical parity sector

The parity sector is a closed kernel of a bounded translation operator on L²
classes. No arbitrary L² representative is evaluated at a boundary. The full
Fourier-support characterization and interval restriction/extension isometry
remain separate obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

/-- The source boundary sign, expressed for all signed integer labels. -/
def spectralSign (n : ℤ) : ℂ := if n % 2 = 0 then 1 else -1

theorem spectralSign_eq_of_parity (m n : ℤ) (h : m % 2 = n % 2) :
    spectralSign m = spectralSign n := by simp [spectralSign, h]

/-- Translation by one is measure preserving for actual probability Haar. -/
theorem halfShift_preserving : MeasurePreserving
    (fun x : SpectralCircle => x + ((1 : ℝ) : SpectralCircle)) spectralHaar spectralHaar := by
  change MeasurePreserving (fun x : SpectralCircle => x + ((1 : ℝ) : SpectralCircle))
    AddCircle.haarAddCircle AddCircle.haarAddCircle
  exact measurePreserving_add_right AddCircle.haarAddCircle ((1 : ℝ) : SpectralCircle)

/-- The actual half-period translation on square-integrable equivalence classes. -/
def halfTranslation : SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ
    (fun x : SpectralCircle => x + ((1 : ℝ) : SpectralCircle)) halfShift_preserving).toContinuousLinearMap

theorem halfTranslation_ae (f : SpectralScalarL2) :
    halfTranslation f =ᵐ[spectralHaar]
      (fun x : SpectralCircle => f (x + ((1 : ℝ) : SpectralCircle))) :=
  Lp.coeFn_compMeasurePreserving f halfShift_preserving

theorem halfTranslation_norm (f : SpectralScalarL2) : ‖halfTranslation f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f halfShift_preserving

/-- Even character values at one are one, including negative character labels. -/
theorem spectralFourier_even_one (k : ℤ) :
    fourier (2 * k) ((1 : ℝ) : SpectralCircle) = 1 := by
  rw [fourier_coe_apply]
  convert Complex.exp_int_mul_two_pi_mul_I k using 1 <;> push_cast <;> congr 1 <;> ring

/-- The first doubled-circle character changes sign under a half-period shift. -/
theorem spectralFourier_first_one : fourier 1 ((1 : ℝ) : SpectralCircle) = -1 := by
  rw [fourier_coe_apply]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * ((1 : ℝ) : ℂ) /
      ((2 : ℝ) : ℂ) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_pi_mul_I]

/-- Character half-period values give exactly the source parity sign. -/
theorem spectralFourier_one (n : ℤ) :
    fourier n ((1 : ℝ) : SpectralCircle) = spectralSign n := by
  have hd : n = n % 2 + 2 * (n / 2) := by omega
  have hp : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hp with h | h
  · conv_lhs => rw [hd, h]
    rw [zero_add, spectralFourier_even_one]
    simp [spectralSign, h]
  · conv_lhs => rw [hd, h]
    rw [fourier_add, spectralFourier_even_one, mul_one, spectralFourier_first_one]
    simp [spectralSign, h]

/-- Spatial translation of a character, with the source sign on the left. -/
theorem spectralFourier_shift (m : ℤ) (x : SpectralCircle) :
    fourier m (x + ((1 : ℝ) : SpectralCircle)) = spectralSign m * fourier m x := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
  change fourier m x * fourier m ((1 : ℝ) : SpectralCircle) = spectralSign m * fourier m x
  rw [spectralFourier_one, mul_comm]

/-- Actual translation action on every Fourier L² basis class. -/
theorem halfTranslation_basis (m : ℤ) :
    halfTranslation (spectralBasis m) = spectralSign m • spectralBasis m := by
  apply Lp.ext
  have hm_shift := halfShift_preserving.quasiMeasurePreserving.ae_eq_comp
    (coeFn_fourierLp (T := (2 : ℝ)) 2 m)
  filter_upwards [halfTranslation_ae (spectralBasis m), hm_shift,
    coeFn_fourierLp (T := (2 : ℝ)) 2 m,
    Lp.coeFn_smul (spectralSign m) (spectralBasis m)] with x ht hs hm hout
  dsimp only [Function.comp_def] at hs
  rw [ht, hout]
  change fourierLp 2 m (x + ((1 : ℝ) : SpectralCircle)) = spectralSign m * fourierLp 2 m x
  rw [hs, hm, spectralFourier_shift]

/-- Physical parity is an operator equality on L² classes, with no boundary evaluation. -/
def scalarParity (n : ℤ) : Submodule ℂ SpectralScalarL2 :=
  (halfTranslation - spectralSign n • ContinuousLinearMap.id ℂ SpectralScalarL2).ker

theorem mem_scalarParity (n : ℤ) (f : SpectralScalarL2) :
    f ∈ scalarParity n ↔ halfTranslation f = spectralSign n • f := by
  simp [scalarParity, sub_eq_zero]

/-- The actual parity eigenspace is closed. -/
theorem scalarParity_isClosed (n : ℤ) : IsClosed (scalarParity n : Set SpectralScalarL2) :=
  (halfTranslation - spectralSign n • ContinuousLinearMap.id ℂ SpectralScalarL2).isClosed_ker

instance scalarParity_complete (n : ℤ) : CompleteSpace (scalarParity n) :=
  (scalarParity_isClosed n).completeSpace_coe

/-- Every correctly signed Fourier basis class belongs to the actual parity kernel. -/
theorem spectralBasis_mem_scalarParity (n : ℤ) (m : Sector n) :
    spectralBasis m.val ∈ scalarParity n := by
  rw [mem_scalarParity, halfTranslation_basis,
    spectralSign_eq_of_parity m.val n m.property]

/-- Square norms are integrable before physical normalization identities are used. -/
theorem spectral_integrable_norm_sq (f : SpectralScalarL2) :
    Integrable (fun x : SpectralCircle => ‖f x‖ ^ 2) spectralHaar :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

/-- The same square norm is integrable for ordinary doubled-circle volume. -/
theorem spectral_integrable_norm_sq_volume (f : SpectralScalarL2) :
    Integrable (fun x : SpectralCircle => ‖f x‖ ^ 2) volume := by
  have hf : MemLp f 2 (volume : Measure SpectralCircle) := (Lp.memLp f).of_haarAddCircle
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf

/-- The pulled-back square norm is integrable on the actual doubled real interval. -/
theorem spectral_integrableOn_norm_sq_doubled_interval (f : SpectralScalarL2) :
    IntegrableOn (fun x : ℝ => ‖f (x : SpectralCircle)‖ ^ 2)
      (Set.Ioc (0 : ℝ) 2) volume := by
  have hf : MemLp (fun x : SpectralCircle => ‖f x‖ ^ 2) 1 volume :=
    memLp_one_iff_integrable.mpr (spectral_integrable_norm_sq_volume f)
  have hp := hf.comp_measurePreserving (AddCircle.measurePreserving_mk (2 : ℝ) 0)
  simpa only [IntegrableOn, Function.comp_def, zero_add] using memLp_one_iff_integrable.mp hp

/-- The complex Hilbert norm equals the probability-Haar square integral. -/
theorem spectral_norm_sq_integral (f : SpectralScalarL2) :
    ‖f‖ ^ 2 = ∫ x : SpectralCircle, ‖f x‖ ^ 2 ∂spectralHaar := by
  calc
    ‖f‖ ^ 2 = RCLike.re (inner ℂ f f) := norm_sq_eq_re_inner (𝕜 := ℂ) f
    _ = ∫ x : SpectralCircle, RCLike.re (inner ℂ (f x) (f x)) ∂spectralHaar := by
      rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
    _ = ∫ x : SpectralCircle, ‖f x‖ ^ 2 ∂spectralHaar := by
      simp only [← norm_sq_eq_re_inner (𝕜 := ℂ)]

/-- Exact probability-Haar factor relative to the doubled physical interval.
This does not yet replace the doubled integral by a single interval integral.
-/
theorem spectral_norm_sq_doubled_interval (f : SpectralScalarL2) :
    ‖f‖ ^ 2 = (1 / 2 : ℝ) *
      ∫ x in Set.Ioc (0 : ℝ) 2, ‖f (x : SpectralCircle)‖ ^ 2 := by
  have hf := spectral_integrableOn_norm_sq_doubled_interval f
  rw [spectral_norm_sq_integral]
  change (∫ x : SpectralCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle) = _
  rw [AddCircle.integral_haarAddCircle]
  rw [← AddCircle.integral_preimage (2 : ℝ) 0 (fun x : SpectralCircle => ‖f x‖ ^ 2)]
  norm_num

end NlsGge.Schur
