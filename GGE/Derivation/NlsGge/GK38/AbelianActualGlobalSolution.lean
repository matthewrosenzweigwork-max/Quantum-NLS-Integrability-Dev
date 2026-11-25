import NlsGge.GK38.AbelianGlobalAnalyticSolution
import NlsGge.GK38.AbelianActualGapJacobianInverse

/-! Uncompiled CONCRETE global P5 wrappers. The intermediate hQ is
discharged by the actual P4 gap-Jacobian inverse, not retained as a final
hypothesis. Native/source/strict package gates of the full chain remain
mandatory before any formalization completion credit. -/
set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem p5ActualSolution_real_inverse38 (n : ℤ) (p : p5RealSolutionSpace38 n) :
    (fderiv ℝ (p3RealFn38 n p.val.1) p.val.2).IsInvertible :=
  P4NumeratorVariation.actual_gap_real_jacobian_inverse n p.val.1 p.val.2 p.property.1

theorem p5Actual_global_analytic_gap_solution38 (n : ℤ) :
    ∃! σ : PhysicalL2 → P3RealSpace38 n, AnalyticOnNhd ℝ σ univ ∧
      ∀ u : PhysicalL2, σ u ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u (σ u)=0 :=
  p5Global_analytic_gap_solution_of_actual_inverse38 n (p5ActualSolution_real_inverse38 n)

theorem p5Actual_global_analytic_original_chart_solution38 (n : ℤ) :
    ∃! σ : PhysicalL2 → P3RealSpace38 n, AnalyticOnNhd ℝ σ univ ∧
      ∀ (u : PhysicalL2) (C : ℤ → ℂ) (R : ℤ → ℝ),
        IsolatingFamily38 (realSlice u) C R →
        ∃ s : Lib.L2Seq, (∀ k : ℤ, (s k).im=0) ∧
          p2Restrict38 n s=p3RealInclude38 n (σ u) ∧
          (∀ k : ℤ, Lib.sigmaOf s k ∈ Metric.ball (C k) (R k)) ∧
          p2Fn38 n (realSlice u,p2Restrict38 n s)=0 :=
  p5Global_analytic_original_chart_solution_of_actual_inverse38 n
    (p5ActualSolution_real_inverse38 n)

end
end NlsGge.GK38
