import QuantumNLS.IndividualPeriodBindingR31b
import QuantumNLS.AnalyticIdentity

/-! R-C95830E3, global:individual-periods, individual_periods.tex:131-154.
The defect of the already constructed global time map is analytic everywhere
and vanishes on the full LOCAL-016 ball. The accepted Hilbert identity
theorem extends this equality to every physical input. No support, positive
action, chart, mass bound or continuation hypothesis is imposed. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open Set Metric
namespace QuantumNLS.GlobalIndividualPeriodsR31b
open PhysicalTensor (L2T)
open CompleteFlowPhysicalR107 IndividualPeriodBindingR31b
open RootMassInvolutionR8 (mass)
variable {L κ : ℝ} [Fact (0 < L)]

theorem period_everywhere (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    phi hκ n (2 * Real.pi) u = u := by
  let A : L2T L → L2T L := fun v => phi hκ n (2 * Real.pi) v - v
  have hA : ∀ v, AnalyticAt ℝ A v :=
    fun v => (phi_time_analytic hκ n (2 * Real.pi) v).sub analyticAt_id
  have hlocal := IndexedPeriodTheoremR30b.reset_period_theorem (L := L) hκ
  have hz : ∀ v ∈ ball (0 : L2T L) (IndexedGlobalR27b.delta L κ), A v = 0 := by
    intro v hv
    exact sub_eq_zero.mpr (phi_local_period hκ n v (mem_ball_zero_iff.mp hv))
  exact sub_eq_zero.mp (AnalyticIdentity.identity_of_vanishing_ball A hA hlocal.1 hz u)

/-- The entire printed theorem in one named statement. The global map is
the exact LOCAL-016 flow at every time and the unique complete Hamiltonian
flow of the literal quantum indexed mass, with X_n = -i grad I_n. All L2
inputs are quantified, including infinite indexed support. The zero-action
strata are included explicitly. Only L>0 and kappa>0 are parameter hypotheses. -/
theorem global_individual_periods (hκ : 0 < κ) (n : ℤ) :
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
  refine ⟨period_everywhere hκ n, phi_initial_derivative hκ n, ?_,
    phi_eq_local_flow hκ n, fun _ => rfl, ?_⟩
  · intro u γ hγ0 hγ
    have he := IndexedGlobalR27b.solution_unique hκ n u hγ0 hγ
    funext t
    exact (congrFun he t).trans (phi_eq_local_flow hκ n t u).symm
  · intro u hu t
    rw [phi_eq_local_flow]
    exact IndexedGlobalR27b.flow_stationary hκ n u
      (IndexedFieldR27b.field_zero_of_mass_zero hκ n u hu) t

end QuantumNLS.GlobalIndividualPeriodsR31b
#print axioms QuantumNLS.GlobalIndividualPeriodsR31b.period_everywhere
#print axioms QuantumNLS.GlobalIndividualPeriodsR31b.global_individual_periods
