import Mathlib.Analysis.Fourier.AddCircle

/-!
# Actual Fourier multiplication on the doubled spectral circle

Haar probability has mass one, while ordinary doubled-circle volume has mass
two. Multipliers are constructed on genuine L² classes using proved MemLp,
and their a.e. representative identities precede all operator identities.
No physical parity restriction or interval isometry is assumed here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace NlsGge.Schur

instance spectralPeriod_pos : Fact (0 < (2 : ℝ)) := ⟨by norm_num⟩

abbrev SpectralCircle := AddCircle (2 : ℝ)

def spectralHaar : Measure SpectralCircle := AddCircle.haarAddCircle

abbrev SpectralScalarL2 : Type := Lp ℂ 2 spectralHaar

/-- Integer Fourier characters on the doubled circle are the source exp(i*pi*m*x). -/
def spectralBasis (m : ℤ) : SpectralScalarL2 := fourierLp 2 m

/-- The source Fourier basis is unscaled for probability Haar. -/
theorem spectralBasis_norm (m : ℤ) : ‖spectralBasis m‖ = 1 :=
  (orthonormal_fourier (T := (2 : ℝ))).norm_eq_one m

/-- Every integer Fourier character is pointwise unimodular. -/
theorem spectralFourier_norm (k : ℤ) (x : SpectralCircle) : ‖fourier k x‖ = 1 := by
  simp [fourier_apply]

/-- Fourier multiplication is square-integrable before forming its L² class. -/
theorem fourierMultiplier_memLp (k : ℤ) (f : SpectralScalarL2) :
    MemLp (fun x : SpectralCircle => fourier k x * f x) 2 spectralHaar := by
  apply (Lp.memLp f).of_le_mul (c := (1 : ℝ))
    ((fourier k).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun x => by simp [norm_mul, spectralFourier_norm]

/-- Actual multiplication, with its membership proof supplied rather than assumed. -/
def fourierMultiplierValue (k : ℤ) (f : SpectralScalarL2) : SpectralScalarL2 :=
  (fourierMultiplier_memLp k f).toLp (fun x : SpectralCircle => fourier k x * f x)

/-- A.e. representative formula makes this operator independent of null-set choices. -/
theorem fourierMultiplierValue_ae (k : ℤ) (f : SpectralScalarL2) :
    fourierMultiplierValue k f =ᵐ[spectralHaar]
      (fun x : SpectralCircle => fourier k x * f x) :=
  (fourierMultiplier_memLp k f).coeFn_toLp

/-- Norm preservation follows from proved pointwise modulus preservation. -/
theorem fourierMultiplierValue_norm (k : ℤ) (f : SpectralScalarL2) :
    ‖fourierMultiplierValue k f‖ = ‖f‖ := by
  change ‖(fourierMultiplier_memLp k f).toLp
    (fun x : SpectralCircle => fourier k x * f x)‖ = ‖f‖
  rw [Lp.norm_toLp, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
    (fourierMultiplier_memLp k f).aestronglyMeasurable (Lp.aestronglyMeasurable f)
  exact Filter.Eventually.of_forall fun x => by simp [norm_mul, spectralFourier_norm]

/-- Complex linearity is proved on actual equivalence classes. -/
def fourierMultiplierLinear (k : ℤ) : SpectralScalarL2 →ₗ[ℂ] SpectralScalarL2 where
  toFun := fourierMultiplierValue k
  map_add' f g := by
    apply Lp.ext
    filter_upwards [fourierMultiplierValue_ae k (f + g),
      fourierMultiplierValue_ae k f, fourierMultiplierValue_ae k g,
      Lp.coeFn_add f g,
      Lp.coeFn_add (fourierMultiplierValue k f) (fourierMultiplierValue k g)]
      with x hsum hf hg hfg hout
    rw [hsum, hout, hfg]
    change fourier k x * (f x + g x) =
      fourierMultiplierValue k f x + fourierMultiplierValue k g x
    rw [hf, hg]
    exact mul_add _ _ _
  map_smul' c f := by
    change fourierMultiplierValue k (c • f) = c • fourierMultiplierValue k f
    apply Lp.ext
    filter_upwards [fourierMultiplierValue_ae k (c • f), fourierMultiplierValue_ae k f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (fourierMultiplierValue k f)]
      with x hsum hf hin hout
    rw [hsum, hout, hin]
    change fourier k x * (c * f x) = c * fourierMultiplierValue k f x
    rw [hf]
    simp [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]

/-- The actual bounded complex-linear Fourier multiplier on doubled-circle L². -/
def fourierMultiplier (k : ℤ) : SpectralScalarL2 →L[ℂ] SpectralScalarL2 :=
  (fourierMultiplierLinear k).mkContinuous 1
    (by
      intro f
      change ‖fourierMultiplierValue k f‖ ≤ 1 * ‖f‖
      rw [fourierMultiplierValue_norm, one_mul])

@[simp] theorem fourierMultiplier_norm_apply (k : ℤ) (f : SpectralScalarL2) :
    ‖fourierMultiplier k f‖ = ‖f‖ := fourierMultiplierValue_norm k f

/-- Full Fourier basis action, with multiplication in source order. -/
theorem fourierMultiplier_basis (k m : ℤ) :
    fourierMultiplier k (spectralBasis m) = spectralBasis (k + m) := by
  apply Lp.ext
  filter_upwards [fourierMultiplierValue_ae k (spectralBasis m),
    coeFn_fourierLp (T := (2 : ℝ)) 2 m,
    coeFn_fourierLp (T := (2 : ℝ)) 2 (k + m)] with x hmul hm hout
  change fourierMultiplierValue k (spectralBasis m) x = spectralBasis (k + m) x
  rw [hmul]
  change fourier k x * fourierLp 2 m x = fourierLp 2 (k + m) x
  rw [hm, hout, fourier_add]

/-- Exact scalar multiplier norm, using a unit Fourier basis vector. -/
theorem fourierMultiplier_norm (k : ℤ) : ‖fourierMultiplier k‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simp
  · have h := (fourierMultiplier k).le_opNorm (spectralBasis 0)
    simpa [spectralBasis_norm] using h

/-- Ordinary doubled-circle volume has twice the probability-Haar mass. -/
theorem spectral_volume_eq_two_smul :
    (volume : Measure SpectralCircle) = (2 : ℝ≥0∞) • spectralHaar := by
  simpa [spectralHaar] using (AddCircle.volume_eq_smul_haarAddCircle (T := (2 : ℝ)))

end NlsGge.Schur
