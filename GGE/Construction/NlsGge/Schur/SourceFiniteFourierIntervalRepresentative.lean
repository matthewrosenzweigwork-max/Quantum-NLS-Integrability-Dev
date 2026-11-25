import NlsGge.Schur.FreePhysicalFiniteWeakDerivative
import NlsGge.Schur.SourceIntervalFourierNet

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace NlsGge.Schur

/-- The actual restricted parity basis vector is the source interval character. -/
lemma scalarParityRestrictVector_ae_character (n : ℤ) (m : Sector n) :
    scalarParityRestrict n (scalarParityVector n m)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        (fun x : ℝ => fourier m.val (x : SpectralCircle)) := by
  have hb : (scalarParityVector n m : SpectralScalarL2)
      =ᵐ[spectralHaar] fourier m.val := by
    simpa only [scalarParityVector, Submodule.coe_mk, spectralBasis, spectralHaar] using
      (coeFn_fourierLp (T := (2 : ℝ)) 2 m.val)
  have hp := spectral_ae_pullback_first_half hb
  have hr := scalarParityRestrictValue_ae n (scalarParityVector n m)
  exact hr.trans hp

/-- Actual finite Fourier vector in the closed parity subspace, with the
lower channel genuinely reflected. -/
def sourceFiniteParityFourier (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ) : scalarParity n :=
  ∑ m ∈ S, a m • scalarParityVector n (if upper then m else negateIndex n m)

/-- Finite Fourier integration-by-parts uses a representative of the actual
restricted Hilbert-space vector, rather than an unrelated polynomial. -/
lemma sourceFiniteParityFourier_ae_character (n : ℤ) (upper : Bool)
    (S : Finset (Sector n)) (a : Sector n → ℂ) :
    scalarParityRestrict n (sourceFiniteParityFourier n upper S a)
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
        sourceFiniteCharacter n upper S a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      have hz : sourceFiniteCharacter n upper ∅ a = 0 := by
        funext x
        simp [sourceFiniteCharacter]
      rw [hz]
      simpa only [sourceFiniteParityFourier, Finset.sum_empty, map_zero] using
        (Lp.coeFn_zero ℂ 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)))
  | @insert m S hm ih =>
      let v := scalarParityVector n (if upper then m else negateIndex n m)
      let F := scalarParityRestrict n (sourceFiniteParityFourier n upper S a)
      have hsum : scalarParityRestrict n
          (sourceFiniteParityFourier n upper (insert m S) a) =
          a m • scalarParityRestrict n v + F := by
        simp only [sourceFiniteParityFourier, Finset.sum_insert hm, map_add, map_smul, v, F]
      rw [hsum]
      have hv := scalarParityRestrictVector_ae_character n
        (if upper then m else negateIndex n m)
      filter_upwards [Lp.coeFn_add (a m • scalarParityRestrict n v) F,
        Lp.coeFn_smul (a m) (scalarParityRestrict n v), hv, ih]
        with x hadd hsmul hchar hF
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      change a m * scalarParityRestrict n
          (scalarParityVector n (if upper then m else negateIndex n m)) x +
          scalarParityRestrict n (sourceFiniteParityFourier n upper S a) x = _
      rw [hchar, hF]
      cases upper <;>
        simp [sourceFiniteCharacter, Finset.sum_insert hm, negateIndex_val]

end NlsGge.Schur
