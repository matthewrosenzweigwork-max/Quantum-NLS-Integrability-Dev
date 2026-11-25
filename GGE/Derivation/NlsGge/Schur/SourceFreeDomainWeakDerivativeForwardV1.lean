import NlsGge.Schur.SourceReflectedIntervalFourierNetV1
import NlsGge.Schur.SourceFiniteIntervalClassWeakDerivativeV1

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace NlsGge.Schur

lemma sourceCoordinateComponent_smul (n : ℤ) (x : SectorSquare n)
    (upper : Bool) (a : ℂ) :
    sourceCoordinateComponent n (a • x) upper = a • sourceCoordinateComponent n x upper := by
  unfold sourceCoordinateComponent
  rw [(parityPairRepr n).symm.map_smul]
  change scalarParityRestrict n (a • ((parityPairRepr n).symm x upper)) = _
  exact (scalarParityRestrict n).map_smul a ((parityPairRepr n).symm x upper)

lemma sourceFreeCoordinateDerivative_finite_tendsto
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool) :
    Tendsto (fun S : Finset (Sector n) =>
      scalarParityRestrict n (sourceFiniteParityFourier n upper S
        (sourceFiniteDerivativeCoefficients n upper (fun m => x (upper,m)))))
      atTop (nhds (sourceFreeCoordinateDerivative n x hx upper)) := by
  let a : ℂ := if upper then Complex.I else -Complex.I
  let y : SectorSquare n := a • freeCoordinateDirac n ⟨x,hx⟩
  have hy : sourceCoordinateComponent n y upper =
      sourceFreeCoordinateDerivative n x hx upper :=
    sourceCoordinateComponent_smul n (freeCoordinateDirac n ⟨x,hx⟩) upper a
  have hc : (fun m : Sector n => y (upper,m)) =
      sourceFiniteDerivativeCoefficients n upper (fun m => x (upper,m)) := by
    funext m
    change a * (spectralCenter m.val * x (upper,m)) =
      (if upper then Complex.I else -Complex.I) * spectralCenter m.val * x (upper,m)
    simp only [a]
    ring
  have h := sourceCoordinateComponent_finite_tendsto n y upper
  rw [hy, hc] at h
  exact h

/-- Every actual free coordinate-domain vector has the asserted source weak
first derivative in both channels. This proves the forward weak-domain
realization; the converse and full manuscript resolvent claim remain separate. -/
theorem sourceFreeDomain_weak_derivative_forward
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n) (upper : Bool)
    (test testDerivative : SourceIntervalL2) (ψ ψ' : ℝ → ℂ)
    (htest : test =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ)
    (htestDerivative : testDerivative =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] ψ')
    (hψ : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt ψ (ψ' t) t)
    (hψ' : IntervalIntegrable ψ' volume 0 1)
    (htrace : ψ 1 = spectralSign n * ψ 0) :
    (∫ t in Set.Ioc (0 : ℝ) 1, sourceCoordinateComponent n x upper t * testDerivative t) =
      -(∫ t in Set.Ioc (0 : ℝ) 1, sourceFreeCoordinateDerivative n x hx upper t * test t) := by
  apply sourceIntervalWeakPairingLimit_net
    (fun S => scalarParityRestrict n
      (sourceFiniteParityFourier n upper S (fun m => x (upper,m))))
    (fun S => scalarParityRestrict n
      (sourceFiniteParityFourier n upper S
        (sourceFiniteDerivativeCoefficients n upper (fun m => x (upper,m)))))
    (sourceCoordinateComponent n x upper) (sourceFreeCoordinateDerivative n x hx upper)
    test testDerivative
    (sourceCoordinateComponent_finite_tendsto n x upper)
    (sourceFreeCoordinateDerivative_finite_tendsto n x hx upper)
  intro S
  exact sourceFiniteIntervalClass_weak_derivative n upper S (fun m => x (upper,m))
    test testDerivative ψ ψ' htest htestDerivative hψ hψ' htrace

end NlsGge.Schur
