import NlsGge.Spectral.ActualSourceGraphContinuousRepresentativeClassesV1
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory Filter
namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis TransportBridgeV4

/-- An actual graph eigenvector's free weak derivative equals the realized
rough physical reflected derivative class. The state is the canonical graph
reconstruction, not a newly assumed regular eigenfunction. -/
theorem actualSourceEigenvector_freeDerivative_eq_reflectedDerivativeClass
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (X : recoveredActualSourceFreeWeightedDomain n)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val)
    (b : Bool) :
    sourceFreeCoordinateDerivative n (sourcePairRepr n X.val) X.property b =
    actualContinuousReflectedDiracDerivativeClass u z
      (actualSourceGraphContinuousRepresentative n X true)
      (actualSourceGraphContinuousRepresentative n X false)
      (continuous_actualSourceGraphContinuousRepresentative n X true).continuousOn
      (continuous_actualSourceGraphContinuousRepresentative n X false).continuousOn b := by
  have he := congrArg (fun P : SourcePairL2 => P b) heigen
  change actualSourceFreeDiracMapAfterAE n X b +
    actualSourcePotentialOnRecoveredWeightedDomainAfterAE n u (star u) X b = z • X.val b at he
  rw [actualSourceFreeDiracMapAfterAE_component_eq_sourceFreeDiracAction,
    sourceFreeDiracAction, actualSourcePotentialOnRecoveredWeightedDomain_apply] at he
  cases b
  · rw [actualL2PotentialParityPairSourceOperator_apply_false,
      actualSourceGraphContinuousRepresentative_LInf_eq] at he
    let D := sourceFreeCoordinateDerivative n (sourcePairRepr n X.val) X.property false
    let P := actualSourceL2PotentialTimesLInf (star u)
      (sourceIntervalLInfOfContinuousOn (actualSourceGraphContinuousRepresentative n X true)
        (continuous_actualSourceGraphContinuousRepresentative n X true).continuousOn)
    have hd : Complex.I • D = z • X.val false - P := eq_sub_iff_add_eq.mpr he
    change D = Complex.I • (P - z • sourceIntervalL2OfContinuousOn
      (actualSourceGraphContinuousRepresentative n X false)
      (continuous_actualSourceGraphContinuousRepresentative n X false).continuousOn)
    rw [actualSourceGraphContinuousRepresentative_L2_eq]
    calc
      D = (-Complex.I) • (Complex.I • D) := by
        simp only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
      _ = (-Complex.I) • (z • X.val false - P) := by rw [hd]
      _ = Complex.I • (P - z • X.val false) := by
        simp only [smul_sub, neg_smul]
        abel
  · rw [actualL2PotentialParityPairSourceOperator_apply_true,
      actualSourceGraphContinuousRepresentative_LInf_eq] at he
    let D := sourceFreeCoordinateDerivative n (sourcePairRepr n X.val) X.property true
    let P := actualSourceL2PotentialTimesLInf u
      (sourceIntervalLInfOfContinuousOn (actualSourceGraphContinuousRepresentative n X false)
        (continuous_actualSourceGraphContinuousRepresentative n X false).continuousOn)
    have hd : (-Complex.I) • D = z • X.val true - P := eq_sub_iff_add_eq.mpr he
    change D = Complex.I • (z • sourceIntervalL2OfContinuousOn
      (actualSourceGraphContinuousRepresentative n X true)
      (continuous_actualSourceGraphContinuousRepresentative n X true).continuousOn - P)
    rw [actualSourceGraphContinuousRepresentative_L2_eq]
    calc
      D = Complex.I • ((-Complex.I) • D) := by
        simp only [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
      _ = Complex.I • (z • X.val true - P) := by rw [hd]

/-- The canonical graph representatives satisfy the actual reflected physical
rough-potential differential equation almost everywhere, as a consequence of
the genuine operator eigen-equation on its true graph domain. -/
theorem actualSourceEigenvector_continuousRepresentative_ae_reflectedDerivative
    (n : ℤ) (u : PhysicalL2) (z : ℂ)
    (X : recoveredActualSourceFreeWeightedDomain n)
    (heigen : actualSourcePerturbedDiracPMapAfterAE n u (star u) X = z • X.val)
    (b : Bool) :
    ∀ᵐ t ∂volume, t ∈ Set.uIcc (0 : ℝ) 1 →
      HasDerivAt (actualSourceGraphContinuousRepresentative n X b)
        (actualContinuousReflectedDiracDerivativeRepresentative u z
          (actualSourceGraphContinuousRepresentative n X true)
          (actualSourceGraphContinuousRepresentative n X false) b t) t := by
  have hclass := actualSourceEigenvector_freeDerivative_eq_reflectedDerivativeClass n u z X heigen b
  have hrep := (ae_restrict_iff' measurableSet_Ioc).mp
    (actualContinuousReflectedDiracDerivativeClass_ae u z
      (actualSourceGraphContinuousRepresentative n X true)
      (actualSourceGraphContinuousRepresentative n X false)
      (continuous_actualSourceGraphContinuousRepresentative n X true).continuousOn
      (continuous_actualSourceGraphContinuousRepresentative n X false).continuousOn b)
  have h0 : ∀ᵐ t ∂volume, t ≠ (0 : ℝ) := by simp [ae_iff, measure_singleton]
  filter_upwards [freeDomainContinuousComponent_source_ae_hasDerivAt n
    (sourcePairRepr n X.val) X.property b, hrep, h0] with t hd hr ht0
  intro ht
  have htcc : t ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hti : t ∈ Set.Ioc (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne htcc.1 (Ne.symm ht0), htcc.2⟩
  have hvalue := (congrArg (fun G : SourceIntervalL2 => G t) hclass).trans (hr hti)
  have hdt := hd ht
  rw [hvalue] at hdt
  exact hdt

end NlsGge.Schur
end
