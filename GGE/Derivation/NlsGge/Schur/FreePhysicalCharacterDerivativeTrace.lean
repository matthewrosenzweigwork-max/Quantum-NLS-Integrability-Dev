import NlsGge.Schur.PhysicalSector
import NlsGge.Schur.FreeResolvent

/-! NEW-F02.02: actual real-variable derivatives and endpoint traces of the
source upper/lower Fourier characters. Both have free eigenvalue m*pi under
(-i*d/dx,+i*d/dx). This does not establish the full weak H1-domain iff. -/
set_option autoImplicit false
noncomputable section
namespace NlsGge.Schur

lemma sourceUpperCharacter_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier m (y : SpectralCircle))
      (Complex.I * spectralCenter m * fourier m (x : SpectralCircle)) x := by
  convert hasDerivAt_fourier (2 : ℝ) m x using 1
  unfold spectralCenter
  norm_num
  ring

lemma sourceLowerCharacter_hasDerivAt (m : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => fourier (-m) (y : SpectralCircle))
      (-Complex.I * spectralCenter m * fourier (-m) (x : SpectralCircle)) x := by
  convert hasDerivAt_fourier_neg (2 : ℝ) m x using 1
  unfold spectralCenter
  norm_num
  ring

lemma sourceUpperCharacter_free_action (m : ℤ) (x : ℝ) :
    -Complex.I * deriv (fun y : ℝ => fourier m (y : SpectralCircle)) x =
      spectralCenter m * fourier m (x : SpectralCircle) := by
  rw [(sourceUpperCharacter_hasDerivAt m x).deriv]
  calc
    _ = -(Complex.I * Complex.I) * (spectralCenter m * fourier m (x : SpectralCircle)) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

lemma sourceLowerCharacter_free_action (m : ℤ) (x : ℝ) :
    Complex.I * deriv (fun y : ℝ => fourier (-m) (y : SpectralCircle)) x =
      spectralCenter m * fourier (-m) (x : SpectralCircle) := by
  rw [(sourceLowerCharacter_hasDerivAt m x).deriv]
  calc
    _ = -(Complex.I * Complex.I) * (spectralCenter m * fourier (-m) (x : SpectralCircle)) := by ring
    _ = _ := by rw [Complex.I_mul_I]; ring

lemma sourceUpperCharacter_endpoint_parity (n : ℤ) (m : Sector n) :
    fourier m.val ((1 : ℝ) : SpectralCircle) =
      spectralSign n * fourier m.val ((0 : ℝ) : SpectralCircle) := by
  rw [spectralFourier_one, spectralSign_eq_of_parity m.val n m.property]
  simp

lemma sourceLowerCharacter_endpoint_parity (n : ℤ) (m : Sector n) :
    fourier (-m.val) ((1 : ℝ) : SpectralCircle) =
      spectralSign n * fourier (-m.val) ((0 : ℝ) : SpectralCircle) := by
  have hm : (-m.val) % 2 = n % 2 := by have h := m.property; omega
  rw [spectralFourier_one, spectralSign_eq_of_parity (-m.val) n hm]
  simp
end NlsGge.Schur
