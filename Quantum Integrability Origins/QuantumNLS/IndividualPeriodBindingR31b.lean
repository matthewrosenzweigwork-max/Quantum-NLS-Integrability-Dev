import QuantumNLS.CompleteAnalyticFlowR107
import QuantumNLS.IndexedPeriodTheoremR30b

/-! R-C95830E3: identify the accepted complete analytic flow with the
accepted LOCAL-016 flow by uniqueness of the same actual Hamiltonian ODE.
Both sides have the same coupling, integer label, initial point and time. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
namespace QuantumNLS.IndividualPeriodBindingR31b
open PhysicalTensor (L2T)
open CompleteFlowPhysicalR107
variable {L κ : ℝ} [Fact (0 < L)]

theorem phi_initial_derivative (hκ : 0 < κ) (n : ℤ) (u : L2T L) :
    phi hκ n 0 u = u ∧ ∀ t,
      HasDerivAt (fun s => phi hκ n s u)
        (SymplecticBracket.hamField (RootMassInvolutionR8.mass hκ n)
          (phi hκ n t u)) t := by
  -- Transport the entire dependent derivative proposition, including its
  -- continuous scalar-action instance, along the accepted scalar bridge.
  let P (ns : NormedSpace ℝ (L2T L)) : Prop := by
    letI : NormedSpace ℝ (L2T L) := ns
    letI : Module ℝ (L2T L) := ns.toModule
    letI : SMul ℝ (L2T L) := ns.toSMul
    exact phi hκ n 0 u = u ∧ ∀ t,
      HasDerivAt (fun s => phi hκ n s u)
        (SymplecticBracket.hamField (RootMassInvolutionR8.mass hκ n)
          (phi hκ n t u)) t
  have hs : P (realNS (L := L)) := phi_spec (L := L) hκ n u
  exact (congrArg P (realNS_eq (L := L))).mp hs

/-- Exact equality of the two constructed flows, at every real time. -/
theorem phi_eq_local_flow (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) :
    phi hκ n t u = IndexedGlobalR27b.flow hκ n t u := by
  have hs := phi_initial_derivative hκ n u
  exact congrFun (IndexedGlobalR27b.solution_unique hκ n u hs.1 hs.2) t

theorem phi_time_analytic (hκ : 0 < κ) (n : ℤ) (t : ℝ) (u : L2T L) :
    AnalyticAt ℝ (phi hκ n t) u := by
  simpa +instances only [CompleteAnalyticFlowR107.realNormed,
    CompleteAnalyticFlowR107.realModule, CompleteAnalyticFlowR107.realSMul,
    realNS_eq] using
    CompleteAnalyticFlowR107.time_analytic (L := L) hκ n t u

theorem phi_local_period (hκ : 0 < κ) (n : ℤ) (u : L2T L)
    (hu : ‖u‖ < IndexedGlobalR27b.delta L κ) :
    phi hκ n (2 * Real.pi) u = u := by
  rw [phi_eq_local_flow]
  exact (IndexedPeriodTheoremR30b.reset_period_theorem hκ).2.2.1 n u hu

end QuantumNLS.IndividualPeriodBindingR31b
#print axioms QuantumNLS.IndividualPeriodBindingR31b.phi_initial_derivative
#print axioms QuantumNLS.IndividualPeriodBindingR31b.phi_eq_local_flow
#print axioms QuantumNLS.IndividualPeriodBindingR31b.phi_time_analytic
#print axioms QuantumNLS.IndividualPeriodBindingR31b.phi_local_period
