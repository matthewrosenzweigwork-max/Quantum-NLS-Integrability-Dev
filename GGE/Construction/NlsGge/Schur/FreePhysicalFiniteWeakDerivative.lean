import NlsGge.Schur.FreePhysicalCharacterDerivativeTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! NEW-F02.02: actual finite upper/reflected-lower Fourier polynomials on
the unit interval obey the twisted trace and the genuine integration-by-parts
identity against arbitrary differentiable twisted test functions. Passing to
the full weighted domain and proving its weak-H1 iff remain separate goals. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Interval
namespace NlsGge.Schur

def sourceFiniteCharacter (n : ℤ) (upper : Bool) (S : Finset (Sector n))
    (a : Sector n → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ S, a m * fourier (if upper then m.val else -m.val) (x : SpectralCircle)

def sourceFiniteCharacterDerivative (n : ℤ) (upper : Bool) (S : Finset (Sector n))
    (a : Sector n → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ S, a m * ((if upper then Complex.I else -Complex.I) *
    spectralCenter m.val * fourier (if upper then m.val else -m.val) (x : SpectralCircle))

lemma sourceFiniteCharacter_hasDerivAt (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ) (x : ℝ) :
    HasDerivAt (sourceFiniteCharacter n upper S a)
      (sourceFiniteCharacterDerivative n upper S a x) x := by
  unfold sourceFiniteCharacter sourceFiniteCharacterDerivative
  apply HasDerivAt.fun_sum
  intro m hm
  cases upper
  · simpa using (sourceLowerCharacter_hasDerivAt m.val x).const_mul (a m)
  · simpa using (sourceUpperCharacter_hasDerivAt m.val x).const_mul (a m)

lemma sourceFiniteCharacter_endpoint_parity (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ) :
    sourceFiniteCharacter n upper S a 1 =
      spectralSign n * sourceFiniteCharacter n upper S a 0 := by
  unfold sourceFiniteCharacter
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  cases upper
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [sourceLowerCharacter_endpoint_parity n m]
    ring
  · simp only [↓reduceIte]
    rw [sourceUpperCharacter_endpoint_parity n m]
    ring

lemma sourceFiniteCharacterDerivative_continuous (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ) :
    Continuous (sourceFiniteCharacterDerivative n upper S a) := by
  unfold sourceFiniteCharacterDerivative
  apply continuous_finsetSum
  intro m hm
  exact continuous_const.mul ((continuous_const.mul continuous_const).mul
    ((map_continuous (fourier (if upper then m.val else -m.val))).comp
      (AddCircle.continuous_mk' (2 : ℝ))))

lemma sourceFiniteCharacter_weak_derivative (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ)
    (ψ ψ' : ℝ → ℂ)
    (hψ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ψ (ψ' x) x)
    (hψ' : IntervalIntegrable ψ' MeasureTheory.volume 0 1)
    (htrace : ψ 1 = spectralSign n * ψ 0) :
    (∫ x in (0 : ℝ)..1, sourceFiniteCharacter n upper S a x * ψ' x) =
      -(∫ x in (0 : ℝ)..1, sourceFiniteCharacterDerivative n upper S a x * ψ x) := by
  have hF := sourceFiniteCharacter_hasDerivAt n upper S a
  have hFp : IntervalIntegrable (sourceFiniteCharacterDerivative n upper S a)
      MeasureTheory.volume 0 1 :=
    (sourceFiniteCharacterDerivative_continuous n upper S a).intervalIntegrable 0 1
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hF x) hψ hFp hψ']
  rw [sourceFiniteCharacter_endpoint_parity n upper S a, htrace]
  have hb : (spectralSign n * sourceFiniteCharacter n upper S a 0) *
      (spectralSign n * ψ 0) = sourceFiniteCharacter n upper S a 0 * ψ 0 := by
    calc
      _ = (spectralSign n * spectralSign n) *
          (sourceFiniteCharacter n upper S a 0 * ψ 0) := by ring
      _ = _ := by rw [spectralSign_mul_self, one_mul]
  rw [hb, sub_self, zero_sub]

end NlsGge.Schur
