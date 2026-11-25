import QuantumNLS.GlobalIndividualPeriodsR31b
/-! integrator-authored trusted spec for R-C95830E3 global:individual-periods (terra_review r211 FULL ACCEPT): headline statement(s) copied verbatim from GlobalIndividualPeriodsR31b (QuantumNLS.GlobalIndividualPeriodsR31b). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric
namespace QuantumNLS.RC958Spec
open QuantumNLS.GlobalIndividualPeriodsR31b
open PhysicalTensor (L2T)
open CompleteFlowPhysicalR107 IndividualPeriodBindingR31b
open RootMassInvolutionR8 (mass)
variable {L κ : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem global_individual_periods_spec (hκ : 0 < κ) (n : ℤ) :
    (∀ u : L2T L, phi hκ n (2 * Real.pi) u = u) ∧
    (∀ u : L2T L, phi hκ n 0 u = u ∧ ∀ t : ℝ,
      HasDerivAt (fun s => phi hκ n s u)
        ((-Complex.I) • SymplecticBracket.gradient (mass hκ n) (phi hκ n t u)) t) ∧
    (∀ (u : L2T L) (γ : ℝ → L2T L), γ 0 = u →
      (∀ t : ℝ, HasDerivAt γ ((-Complex.I) • SymplecticBracket.gradient (mass hκ n) (γ t)) t) →
      γ = fun t => phi hκ n t u) ∧
    (∀ (t : ℝ) (u : L2T L), phi hκ n t u = IndexedGlobalR27b.flow hκ n t u) ∧
    (∀ u : L2T L, mass hκ n u =
      (PhysicalQuantumMeasure.measure hκ u (Ioo
        (RootIndexedPhase.separator hκ u (n-1))
        (RootIndexedPhase.separator hκ u n))).toReal) ∧
    (∀ u : L2T L, mass hκ n u = 0 → ∀ t : ℝ, phi hκ n t u = u) := by
  exact QuantumNLS.GlobalIndividualPeriodsR31b.global_individual_periods hκ n

end QuantumNLS.RC958Spec
#print axioms QuantumNLS.RC958Spec.global_individual_periods_spec
