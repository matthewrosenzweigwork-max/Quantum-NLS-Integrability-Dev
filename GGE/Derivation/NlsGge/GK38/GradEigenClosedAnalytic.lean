import NlsGge.GK38.GradEigenRealNeumann
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38.GradEigen38
noncomputable section

theorem analyticAt_nu (u : PhysicalL2) (n : ℤ) :
    AnalyticAt ℝ (fun v : PhysicalL2 => nu v n) u := by
  have hneg : AnalyticAt ℝ (fun v : PhysicalL2 => -v) u :=
    (analyticAt_id (𝕜 := ℝ)).neg
  exact (analyticAt_gkMu38 (-u) n).comp hneg

def ClosedEquationsAnalyticTarget : Prop :=
  ∀ n : ℤ, AnalyticOnNhd ℝ (closedEquations n) univ

theorem closed_equations_analytic_target : ClosedEquationsAnalyticTarget := by
  intro n u _
  change AnalyticAt ℝ (fun v : PhysicalL2 => (gkMu v n-nu v n,deltaMu v n)) u
  exact ((analyticAt_gkMu38 u n).sub (analyticAt_nu u n)).prod
    (analyticOnNhd_deltaMu38 n u (mem_univ _))

end
end NlsGge.GK38.GradEigen38
