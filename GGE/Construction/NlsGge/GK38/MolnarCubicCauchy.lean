import NlsGge.Spectral.ActualQuasimomentumDecayE02_38

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations

noncomputable def molnarShift38 (u : PhysicalL2) (z : ℂ) : ℂ :=
  extendFrom {w : ℂ | 0 < w.im} (actualQuasimomentumE02_38 u) z - z

theorem molnarShift_differentiable38 (u : PhysicalL2) :
    DifferentiableOn ℂ (molnarShift38 u) {z : ℂ | 0 < z.im} := by
  have hk := isActualQuasimomentumBranch_actualQuasimomentumE02_38 u
  have hext : ∀ z ∈ {w : ℂ | 0 < w.im},
      extendFrom {w : ℂ | 0 < w.im} (actualQuasimomentumE02_38 u) z =
        actualQuasimomentumE02_38 u z := extendFrom_extends hk.1.continuousOn
  intro z hz
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have h1 : DifferentiableAt ℂ (fun w => actualQuasimomentumE02_38 u w - w) z :=
    (hk.1 z hz).differentiableAt.sub differentiableAt_id
  apply (h1.congr_of_eventuallyEq _).differentiableWithinAt
  filter_upwards [hopen.mem_nhds hz] with w hw
  simp only [molnarShift38, hext w hw]

theorem molnarShift_continuous38 (u : PhysicalL2) :
    ContinuousOn (molnarShift38 u) {z : ℂ | 0 ≤ z.im} :=
  (continuousOn_extend_actualQuasimomentumE02_38 u).sub continuousOn_id

theorem molnarShift_boundary38 (u : PhysicalL2) (t : ℝ) :
    molnarShift38 u (t : ℂ) = actualQuasimomentumBoundaryE02_38 u t - (t : ℂ) := rfl

/-- The exact first cubic target: actual H1 boundary-shift cube is integrable and has zero integral. -/
theorem actual_quasimomentum_shift_cube_integral38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (fun t : ℝ =>
      (actualQuasimomentumBoundaryE02_38 u t - (t : ℂ)) ^ 3) ∧
    (∫ t : ℝ, (actualQuasimomentumBoundaryE02_38 u t - (t : ℂ)) ^ 3) = 0 := by
  obtain ⟨C, _, hdec⟩ := actualQuasimomentum_decay_E02_38 u hu
  have hcubebound : ∀ w : ℂ, 0 ≤ w.im →
      ‖molnarShift38 u w ^ 3‖ ≤ C ^ 3 / Real.sqrt (1 + ‖w‖) ^ 3 := by
    intro w hw
    rw [norm_pow]
    calc
      ‖molnarShift38 u w‖ ^ 3 ≤ (C / Real.sqrt (1 + ‖w‖)) ^ 3 :=
        pow_le_pow_left₀ (norm_nonneg _) (hdec w hw) 3
      _ = _ := div_pow _ _ _
  have hcube := cauchy_decay_E02_38 (fun w => molnarShift38 u w ^ 3) (C ^ 3)
    ((molnarShift_differentiable38 u).pow 3)
    ((molnarShift_continuous38 u).pow 3) hcubebound
  simpa only [molnarShift_boundary38] using hcube

end NlsGge.GK38.MolnarBounds38
