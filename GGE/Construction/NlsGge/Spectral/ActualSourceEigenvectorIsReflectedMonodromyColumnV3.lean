import NlsGge.Spectral.ActualReflectedPhysicalCoefficientForContinuousStateV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
open scoped Matrix
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis TransportBridgeV4

def actualSourceGraphContinuousVector
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (t : ℝ) : Fin 2 → ℂ :=
  ![actualSourceGraphContinuousRepresentative n X true t,
    actualSourceGraphContinuousRepresentative n X false t]

theorem absolutelyContinuous_actualSourceGraphContinuousVector
    (n : ℤ) (X : recoveredActualSourceFreeWeightedDomain n) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => actualSourceGraphContinuousVector n X t i) 0 1 := by
  fin_cases i
  · exact absolutelyContinuous_freeDomainContinuousComponent_source n
      (sourcePairRepr n X.val) X.property true
  · exact absolutelyContinuous_freeDomainContinuousComponent_source n
      (sourcePairRepr n X.val) X.property false

/-- The actual operator equation, on its actual graph domain, implies the
original reflected (-u,-z) first-order vector equation. -/
theorem actualSourceEigenvector_ae_originalReflectedCoefficient
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (X : recoveredActualSourceFreeWeightedDomain n)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val)
    (i : Fin 2) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (fun s => actualSourceGraphContinuousVector n X s i)
        ((zsCoefficientComplex
          (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) (-z) t *ᵥ
            actualSourceGraphContinuousVector n X t) i) t := by
  fin_cases i
  · filter_upwards [actualSourceEigenvector_continuousRepresentative_ae_reflectedDerivative
      n u z X heigen true,
      actualReflectedPhysicalCoefficient_ae_continuousState u z
        (actualSourceGraphContinuousVector n X) true] with t hd hc
    intro ht
    have he := hc ht
    change (_ *ᵥ actualSourceGraphContinuousVector n X t) 0 = _ at he
    change HasDerivAt (fun s => actualSourceGraphContinuousVector n X s 0)
      ((zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) (-z) t *ᵥ
          actualSourceGraphContinuousVector n X t) 0) t
    rw [he]
    exact hd ht
  · filter_upwards [actualSourceEigenvector_continuousRepresentative_ae_reflectedDerivative
      n u z X heigen false,
      actualReflectedPhysicalCoefficient_ae_continuousState u z
        (actualSourceGraphContinuousVector n X) false] with t hd hc
    intro ht
    have he := hc ht
    change (_ *ᵥ actualSourceGraphContinuousVector n X t) 1 = _ at he
    change HasDerivAt (fun s => actualSourceGraphContinuousVector n X s 1)
      ((zsCoefficientComplex
        (fun x => naturalPhysicalCoverL2 (-u) (x : SpectralCircle)) (-z) t *ᵥ
          actualSourceGraphContinuousVector n X t) 1) t
    rw [he]
    exact hd ht

/-- Every genuine source graph eigenvector is exactly the actual rough
fundamental column with its own initial value, including both endpoints. -/
theorem actualSourceEigenvector_eq_reflectedMonodromyColumn
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (X : recoveredActualSourceFreeWeightedDomain n)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      actualSourceGraphContinuousVector n X t =
        actualReflectedPhysicalL2ZsColumn u z (actualSourceGraphContinuousVector n X 0) t := by
  apply actualPhysicalL2Zs_vector_AC_same_initial_unique (-u) (-z) 1 (by norm_num)
  · exact (actualReflectedPhysicalL2ZsColumn_initial u z _).symm
  · exact absolutelyContinuous_actualSourceGraphContinuousVector n X
  · exact absolutelyContinuous_actualReflectedPhysicalL2ZsColumn u z _
  · exact actualSourceEigenvector_ae_originalReflectedCoefficient n u z X heigen
  · exact actualReflectedPhysicalL2ZsColumn_ae_hasDerivAt u z _

end NlsGge.SpectralFoundations
end
