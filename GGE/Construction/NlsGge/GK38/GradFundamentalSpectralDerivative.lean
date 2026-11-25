import NlsGge.GK38.GradFundamentalSpectralVOC

/-! # K1: source spectral derivative APIs for entries, trace and antitrace.
GK Chapter I, Proposition3.1 and Corollary3.2. Every totalized deriv identity
follows an actual HasDerivAt theorem with the independent adjugate integral.
-/
set_option autoImplicit false
open Set
namespace NlsGge.GK38
noncomputable section

theorem hasDerivAt_fundSpectralIntegral38 (φ : PotPair) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    HasDerivAt (fun w => fundPair φ w t i j) (fundSpectralIntegral38 φ z t i j) z := by
  have hd := (fundEntryL38 t i j).hasFDerivAt.comp_hasDerivAt z
    (hasDerivAt_fundSpectralResolvent38 φ z)
  change HasDerivAt (fun w => fundPair φ w t i j) (fundSpectralResolvent38 φ z t i j) z at hd
  rw [fundSpectralResolvent38_voc] at hd
  exact hd

theorem deriv_fundSpectralIntegral38 (φ : PotPair) (z : ℂ)
    (t : Icc (0 : ℝ) 1) (i j : Fin 2) :
    deriv (fun w => fundPair φ w t i j) z = fundSpectralIntegral38 φ z t i j :=
  (hasDerivAt_fundSpectralIntegral38 φ z t i j).deriv

/-- Independently specified full trace of the raw unit-time spectral integral. -/
def spectralDiscrimIntegral38 (φ : PotPair) (z : ℂ) : ℂ :=
  fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 0 +
    fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 1

/-- Independently specified off-diagonal sum of the raw spectral integral. -/
def spectralAntiDiscrimIntegral38 (φ : PotPair) (z : ℂ) : ℂ :=
  fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 1 +
    fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 0

theorem hasDerivAt_discrim_spectral38 (φ : PotPair) (z : ℂ) :
    HasDerivAt (discrim φ) (spectralDiscrimIntegral38 φ z) z := by
  change HasDerivAt (fun w => discrim φ w) (spectralDiscrimIntegral38 φ z) z
  have hd := (hasDerivAt_fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 0).fun_add
    (hasDerivAt_fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 1)
  simpa only [discrim_eq, monodromyPair_eq_fundPair, spectralDiscrimIntegral38] using hd

theorem hasDerivAt_antiDiscrim_spectral38 (φ : PotPair) (z : ℂ) :
    HasDerivAt (antiDiscrim φ) (spectralAntiDiscrimIntegral38 φ z) z := by
  change HasDerivAt (fun w => antiDiscrim φ w) (spectralAntiDiscrimIntegral38 φ z) z
  have hd := (hasDerivAt_fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 0 1).fun_add
    (hasDerivAt_fundSpectralIntegral38 φ z ⟨1, zero_le_one, le_rfl⟩ 1 0)
  simpa only [antiDiscrim, monodromyPair_eq_fundPair, spectralAntiDiscrimIntegral38] using hd

theorem deriv_discrim_spectral38 (φ : PotPair) (z : ℂ) :
    deriv (discrim φ) z = spectralDiscrimIntegral38 φ z :=
  (hasDerivAt_discrim_spectral38 φ z).deriv

theorem deriv_antiDiscrim_spectral38 (φ : PotPair) (z : ℂ) :
    deriv (antiDiscrim φ) z = spectralAntiDiscrimIntegral38 φ z :=
  (hasDerivAt_antiDiscrim_spectral38 φ z).deriv

end
end NlsGge.GK38
