import NlsGge.GK38.DirichletRealGreenParam
import NlsGge.GK38.EigenvalueCompactnessPhaseBound
import NlsGge.GK38.EigenvalueCompactnessPhaseActualProbe

/-! The independent actual fixed-column clockwise phase, with all rough-integral prerequisites. -/
set_option autoImplicit false
open Filter Topology Set MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def phaseCandidate38 (u : PhysicalL2) (x s : ℝ) : ℝ := x * s -
  ∫ r in (0 : ℝ)..s, (e02Pot38 u r *
    (actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] r 1 /
      actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] r 0)).re

theorem phaseCandidate_eq_periodicPhase38 (u : PhysicalL2) (x s : ℝ) :
    phaseCandidate38 u x s = periodicPhase38 u x 1 s := by
  simp only [phaseCandidate38, periodicPhase38, realInitial38, star_one]

theorem dirichletState_eq_normalizedFirst38 (u : PhysicalL2) (x : ℝ) (t : DirichletTime38) :
    dirichletState38 u (x : ℂ) t 0 = normalizedFirst38 u x 1 t := by
  simp only [dirichletState38, normalizedFirst38, realInitial38, star_one, div_one]

theorem phaseCandidate_integrable38 (u : PhysicalL2) (x : ℝ) (t : DirichletTime38) :
    IntervalIntegrable (fun r => (e02Pot38 u r *
      (actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] r 1 /
        actualPhysicalFloquetState33 u (x : ℂ) ![1, 1] r 0)).re) volume 0 (t : ℝ) := by
  simpa only [periodicState38, realInitial38, star_one] using
    periodicPhase_intervalIntegrable38 u x 1 (by simp) t

theorem phaseCandidate_realization38 (u : PhysicalL2) (x : ℝ) :
    ContinuousOn (phaseCandidate38 u x) (Icc 0 1) ∧ phaseCandidate38 u x 0 = 0 ∧
    ∀ t : DirichletTime38, dirichletState38 u (x : ℂ) t 0 ≠ 0 ∧
      dirichletState38 u (x : ℂ) t 0 / (‖dirichletState38 u (x : ℂ) t 0‖ : ℂ) =
        Complex.exp (-Complex.I * (phaseCandidate38 u x t : ℂ)) := by
  have h := periodicPhase_realization38 u x 1 (by simp)
  have he : periodicPhase38 u x 1 = phaseCandidate38 u x :=
    funext fun s => (phaseCandidate_eq_periodicPhase38 u x s).symm
  rw [he] at h
  simpa only [← dirichletState_eq_normalizedFirst38] using h

theorem dirichlet_normalizedPhase38 (u : PhysicalL2) (x : ℝ) :
    NormalizedPhase38 (fun t : DirichletTime38 => dirichletState38 u (x : ℂ) t 0)
      (fun t : DirichletTime38 => phaseCandidate38 u x t) := by
  have h := phaseCandidate_realization38 u x
  have hA : Continuous (fun t : DirichletTime38 => ((x : ℂ), t)) :=
    continuous_const.prodMk continuous_id
  have hcomp := (dirichletState_param_continuous38 u 0).comp hA
  have hG : Continuous (fun t : DirichletTime38 => dirichletState38 u (x : ℂ) t 0) := by
    simpa only [Function.comp_def] using hcomp
  exact ⟨hG, h.1.comp_continuous continuous_subtype_val (fun t => t.property), h.2.1, h.2.2⟩

theorem phaseCandidate_displacement38 (u : PhysicalL2) (x : ℝ) (t : DirichletTime38) :
    |phaseCandidate38 u x t - x * (t : ℝ)| ≤ ‖u‖ := by
  rw [phaseCandidate_eq_periodicPhase38]
  exact periodicPhase_displacement38 u x 1 (by simp) t

theorem phaseCandidate_free_one38 (x : ℝ) : phaseCandidate38 0 x 1 = x := by
  rw [phaseCandidate_eq_periodicPhase38]
  exact periodicPhase_free_one38 x 1 (by simp)

end
end NlsGge.GK38
