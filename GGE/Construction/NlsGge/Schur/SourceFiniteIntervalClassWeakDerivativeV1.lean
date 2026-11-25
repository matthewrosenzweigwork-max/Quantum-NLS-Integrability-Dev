import NlsGge.Schur.SourceFiniteFourierIntervalRepresentative
import NlsGge.Schur.SourceIntervalWeakPairingLimit

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators Interval
namespace NlsGge.Schur

/-- The genuinely reflected derivative coefficients for the finite source
polynomial, with its actual upper/lower Dirac signs. -/
def sourceFiniteDerivativeCoefficients (n : ℤ) (upper : Bool)
    (a : Sector n → ℂ) (m : Sector n) : ℂ :=
  (if upper then Complex.I else -Complex.I) * spectralCenter m.val * a m

lemma sourceFiniteCharacter_derivative_coefficients (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ) :
    sourceFiniteCharacter n upper S (sourceFiniteDerivativeCoefficients n upper a) =
      sourceFiniteCharacterDerivative n upper S a := by
  funext x
  unfold sourceFiniteCharacter sourceFiniteCharacterDerivative
  apply Finset.sum_congr rfl
  intro m hm
  unfold sourceFiniteDerivativeCoefficients
  ring

/-- Integration by parts for the actual finite Hilbert-space vectors and
actual L² test classes. Smooth representatives, their derivative, and the
source twisted trace are explicit; no weak-derivative identity is assumed. -/
lemma sourceFiniteIntervalClass_weak_derivative (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ)
    (test testDerivative : SourceIntervalL2) (ψ ψ' : ℝ → ℂ)
    (htest : test =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ)
    (htestDerivative : testDerivative =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ')
    (hψ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ψ (ψ' x) x)
    (hψ' : IntervalIntegrable ψ' volume 0 1)
    (htrace : ψ 1 = spectralSign n * ψ 0) :
    (∫ x in Set.Ioc (0 : ℝ) 1,
      scalarParityRestrict n (sourceFiniteParityFourier n upper S a) x * testDerivative x) =
    -(∫ x in Set.Ioc (0 : ℝ) 1,
      scalarParityRestrict n (sourceFiniteParityFourier n upper S
        (sourceFiniteDerivativeCoefficients n upper a)) x * test x) := by
  have hF := sourceFiniteParityFourier_ae_character n upper S a
  have hG := sourceFiniteParityFourier_ae_character n upper S
    (sourceFiniteDerivativeCoefficients n upper a)
  have hl : (∫ x in Set.Ioc (0 : ℝ) 1,
      scalarParityRestrict n (sourceFiniteParityFourier n upper S a) x * testDerivative x) =
      ∫ x in Set.Ioc (0 : ℝ) 1, sourceFiniteCharacter n upper S a x * ψ' x := by
    apply integral_congr_ae
    filter_upwards [hF, htestDerivative] with x hf ht
    rw [hf, ht]
  have hr : (∫ x in Set.Ioc (0 : ℝ) 1,
      scalarParityRestrict n (sourceFiniteParityFourier n upper S
        (sourceFiniteDerivativeCoefficients n upper a)) x * test x) =
      ∫ x in Set.Ioc (0 : ℝ) 1, sourceFiniteCharacterDerivative n upper S a x * ψ x := by
    apply integral_congr_ae
    filter_upwards [hG, htest] with x hg ht
    rw [hg, ht, sourceFiniteCharacter_derivative_coefficients]
  rw [hl, hr]
  simpa only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    sourceFiniteCharacter_weak_derivative n upper S a ψ ψ' hψ hψ' htrace

end NlsGge.Schur
