import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.DirichletRealGreen
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Parameter continuity of the independent two-state Green integral.
Only accepted F3 analytic continuous-map evaluation is needed. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations

theorem dirichletState_param_continuous38 (u : PhysicalL2) (i : Fin 2) :
    Continuous (fun p : ℂ × DirichletTime38 => dirichletState38 u p.1 p.2 i) := by
  have hJ : Continuous (fun p : PotPair × ℂ => fundContP p.1 p.2) :=
    continuousOn_univ.mp analyticOnNhd_fundContP.continuousOn
  have hA : Continuous (fun z : ℂ => (realSlice u, z)) := continuous_const.prodMk continuous_id
  have hcomp := hJ.comp hA
  have hF : Continuous (fun z : ℂ => fundContP (realSlice u) z) := by
    simpa only [Function.comp_def] using hcomp
  have hEval : Continuous (fun p : PairCont38 × DirichletTime38 => p.1 p.2) := continuous_eval
  have hA : Continuous (fun p : ℂ × DirichletTime38 => (fundContP (realSlice u) p.1, p.2)) :=
    (hF.comp continuous_fst).prodMk continuous_snd
  have hcompEval := hEval.comp hA
  have hE : Continuous (fun p : ℂ × DirichletTime38 => fundContP (realSlice u) p.1 p.2) := by
    simpa only [Function.comp_def] using hcompEval
  have hi (j : Fin 2) : Continuous
      (fun p : ℂ × DirichletTime38 => fundPair (realSlice u) p.1 p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp hE)
  simpa only [dirichletState38, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] using
    (hi 0).fun_add (hi 1)

/-- Globally continuous time extension used only to realize parameter integration. -/
def dirichletGreenExt38 (u : PhysicalL2) (μ ν : ℂ) : ℝ → ℂ :=
  Set.IccExtend zero_le_one (fun t : DirichletTime38 =>
    dirichletState38 u μ t 0 * dirichletState38 u ν t 1 +
      dirichletState38 u μ t 1 * dirichletState38 u ν t 0)

theorem dirichletGreenExt_eq38 (u : PhysicalL2) (μ ν : ℂ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : dirichletGreenExt38 u μ ν s = dirichletGreenKernel38 u μ ν s := by
  rw [dirichletGreenExt38, Set.IccExtend_of_mem _ _ hs]
  simp only [dirichletGreenKernel38, dirichletState_eq_actual38]

theorem dirichletGreenExt_param_continuous38 (u : PhysicalL2) (μ : ℂ) :
    Continuous (fun p : ℂ × ℝ => dirichletGreenExt38 u μ p.1 p.2) := by
  have hc (i : Fin 2) : Continuous
      (fun p : ℂ × DirichletTime38 => dirichletState38 u μ p.2 i) := by
    have hJ := dirichletState_param_continuous38 u i
    have hA : Continuous (fun p : ℂ × DirichletTime38 => (μ, p.2)) :=
      continuous_const.prodMk continuous_snd
    have hcomp := hJ.comp hA
    simpa only [Function.comp_def] using hcomp
  have hf := ((hc 0).fun_mul (dirichletState_param_continuous38 u 1)).fun_add
    ((hc 1).fun_mul (dirichletState_param_continuous38 u 0))
  have hp : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one) := continuous_projIcc
  have hA : Continuous (fun p : ℂ × ℝ => (p.1, Set.projIcc (0 : ℝ) 1 zero_le_one p.2)) :=
    continuous_fst.prodMk (hp.comp continuous_snd)
  have hcomp := hf.comp hA
  simpa only [Function.comp_def, dirichletGreenExt38, Set.IccExtend] using hcomp

/-- Actual fixed-interval integral depends continuously on the spectral parameter. -/
theorem dirichletGreenIntegral_continuous38 (u : PhysicalL2) (μ : ℂ) :
    Continuous (fun ν : ℂ => ∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u μ ν s) := by
  have hc := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun ν s => dirichletGreenExt38 u μ ν s)
    (dirichletGreenExt_param_continuous38 u μ) (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  have he : (fun ν : ℂ => ∫ s in (0 : ℝ)..1, dirichletGreenKernel38 u μ ν s) =
      fun ν : ℂ => ∫ s in Icc (0 : ℝ) 1, dirichletGreenExt38 u μ ν s := by
    funext ν
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    exact (dirichletGreenExt_eq38 u μ ν hs).symm
  rw [he]
  exact hc

end
end NlsGge.GK38
