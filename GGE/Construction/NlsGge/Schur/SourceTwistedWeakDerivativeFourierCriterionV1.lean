import NlsGge.Schur.SourceIntervalCharacterCoefficientsV1
import NlsGge.Schur.SourceFreeDomainWeakDerivativeForwardV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.Schur

/-- The concrete weak derivative tested against all differentiable twisted
source tests whose function and derivative are actual interval L² classes.
This is an analytic definition, not an assumed Fourier/domain conclusion. -/
def SourceTwistedWeakDerivative (n : ℤ) (F G : SourceIntervalL2) : Prop :=
  ∀ (test testDerivative : SourceIntervalL2) (ψ ψ' : ℝ → ℂ),
    test =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ →
    testDerivative =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ' →
    (∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t) →
    IntervalIntegrable ψ' volume 0 1 →
    ψ 1 = spectralSign n * ψ 0 →
    (∫ t in Set.Ioc (0 : ℝ) 1, F t * testDerivative t) =
      -(∫ t in Set.Ioc (0 : ℝ) 1, G t * test t)

lemma sourceFreeDomain_has_twisted_weak_derivative
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool) :
    SourceTwistedWeakDerivative n (sourceCoordinateComponent n x upper)
      (sourceFreeCoordinateDerivative n x hx upper) := by
  exact sourceFreeDomain_weak_derivative_forward n x hx upper

/-- Testing the actual weak derivative against the opposite Fourier
character identifies its ordinary scalar Fourier coefficient, including m=0. -/
theorem sourceTwistedWeakDerivative_fourier_coefficients
    (n : ℤ) (F G : SourceIntervalL2) (hweak : SourceTwistedWeakDerivative n F G)
    (m : Sector n) :
    sourceScalarCoefficient n G m =
      Complex.I * spectralCenter m.val * sourceScalarCoefficient n F m := by
  let k : ℂ := -Complex.I * spectralCenter m.val
  let test : SourceIntervalL2 := scalarParityRestrict n
    (scalarParityVector n (negateIndex n m))
  let testDerivative : SourceIntervalL2 := k • test
  let ψ : ℝ → ℂ := fun t => fourier (-m.val) (t : SpectralCircle)
  let ψ' : ℝ → ℂ := fun t => k * ψ t
  have ht : test =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ := by
    simpa only [test, ψ, negateIndex_val] using
      scalarParityRestrictVector_ae_character n (negateIndex n m)
  have ht' : testDerivative =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ' := by
    filter_upwards [Lp.coeFn_smul k test, ht] with t hs ht
    simpa only [testDerivative, ψ', Pi.smul_apply, smul_eq_mul, ht] using hs
  have hψ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t := by
    intro t _
    simpa only [ψ, ψ', k] using sourceLowerCharacter_hasDerivAt m.val t
  have hψ' : IntervalIntegrable ψ' volume 0 1 := by
    have hc : Continuous ψ' := continuous_const.mul
      ((map_continuous (fourier (-m.val))).comp (AddCircle.continuous_mk' (2 : ℝ)))
    exact hc.intervalIntegrable 0 1
  have htrace : ψ 1 = spectralSign n * ψ 0 := sourceLowerCharacter_endpoint_parity n m
  have hw := hweak test testDerivative ψ ψ' ht ht' hψ hψ' htrace
  have hl : (∫ t in Set.Ioc (0 : ℝ) 1, F t * testDerivative t) =
      k * sourceScalarCoefficient n F m := by
    calc
      _ = ∫ t in Set.Ioc (0 : ℝ) 1, k * (F t * fourier (-m.val) (t : SpectralCircle)) := by
        apply integral_congr_ae
        filter_upwards [ht'] with t ht
        rw [ht]
        dsimp [ψ', ψ]
        ring
      _ = k * (∫ t in Set.Ioc (0 : ℝ) 1, F t * fourier (-m.val) (t : SpectralCircle)) :=
        integral_const_mul k _
      _ = _ := by rw [sourceScalarCoefficient_character_integral]
  have hr : (∫ t in Set.Ioc (0 : ℝ) 1, G t * test t) =
      sourceScalarCoefficient n G m := by
    calc
      _ = ∫ t in Set.Ioc (0 : ℝ) 1, G t * fourier (-m.val) (t : SpectralCircle) := by
        apply integral_congr_ae
        filter_upwards [ht] with t ht
        rw [ht]
      _ = _ := sourceScalarCoefficient_character_integral n G m
  rw [hl, hr] at hw
  calc
    _ = -(k * sourceScalarCoefficient n F m) := by
      simpa only [neg_neg] using (congrArg Neg.neg hw).symm
    _ = _ := by dsimp [k]; ring

/-- A genuine interval weak derivative forces square-summability of the
unbounded free scalar diagonal; no Fourier condition is assumed. -/
theorem sourceTwistedWeakDerivative_weighted_coordinates_memLp
    (n : ℤ) (F G : SourceIntervalL2) (hweak : SourceTwistedWeakDerivative n F G) :
    Memℓp (fun m : Sector n => spectralCenter m.val * sourceScalarCoefficient n F m) 2 := by
  have he : (fun m : Sector n => spectralCenter m.val * sourceScalarCoefficient n F m) =
      fun m : Sector n => -Complex.I * sourceScalarCoefficient n G m := by
    funext m
    rw [sourceTwistedWeakDerivative_fourier_coefficients n F G hweak m]
    symm
    calc
      _ = -(Complex.I * Complex.I) *
          (spectralCenter m.val * sourceScalarCoefficient n F m) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he]
  exact (lp.memℓp (sourceScalarCoefficient n G)).const_smul (-Complex.I)

end NlsGge.Schur
