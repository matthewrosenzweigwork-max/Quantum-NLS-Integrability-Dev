import NlsGge.GK38.GradTauGammaCircleTransfer
import NlsGge.GK38.GradTauGammaKernelContinuity

/-! The actual K1 arbitrary complex shift estimates control weighted
discriminant contour gradients at each fixed time. Constants precede every
potential, contour family, bounded weight, time, and signed integer mode. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def k4aDiscrimContourVec38 (φ : PotPair) (w : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (t : Icc (0 : ℝ) 1) : PairVec38 := fun i =>
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun z => w z * gradDiscrim38 φ z t i) c r

theorem k4aWeightedDiscrimContourMass38 (R c r A : ℝ) (hr : 0 ≤ r) (hA : 0 ≤ A) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : PotPair, ‖φ‖ ≤ R →
      ∀ C : ℤ → ℂ, ∀ ρ : ℤ → ℝ,
        (∀ n, 0 < ρ n ∧ ρ n ≤ r) →
        (∀ n z, z ∈ sphere (C n) (ρ n) → ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ c) →
        ∀ w : ℤ → ℂ → ℂ,
          (∀ n, ContinuousOn (w n) (sphere (C n) (ρ n))) →
          (∀ n z, z ∈ sphere (C n) (ρ n) → ‖w n z‖ ≤ A) →
          ∀ t : Icc (0 : ℝ) 1,
            k1SquareBound38 (fun n =>
              pairPointMass38 (k4aDiscrimContourVec38 φ (w n) (C n) (ρ n) t)) B := by
  obtain ⟨B, hB, hseq⟩ := k4aDiscrimComponentSequence38 R c
  refine ⟨2 * (r ^ 2 * (A ^ 2 * B)), by positivity, ?_⟩
  intro φ hφ C ρ hρ hshift w hw hwA t
  have hcomp (i : Fin 2) : Continuous (fun z : ℂ => gradDiscrim38 φ z t i) := by
    have harg : Continuous (fun z : ℂ => (z, t)) := continuous_id.prodMk continuous_const
    have hj := (k4aGradDiscrim_time_spectral_continuous38 φ).comp harg
    simpa only [Function.comp_def] using (continuous_apply i).comp hj
  have hscalar (i : Fin 2) : k1SquareBound38 (fun n =>
      ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z => w n z * gradDiscrim38 φ z t i) (C n) (ρ n)‖ ^ 2)
      (r ^ 2 * (A ^ 2 * B)) := by
    apply (k4aScalarCircleSequence38 C ρ
      (fun n z => w n z * gradDiscrim38 φ z t i) r (A ^ 2 * B)
      (fun n => (hρ n).1) hr (fun n => (hρ n).2)
      (fun n => (hw n).mul (hcomp i).continuousOn) ?_).2
    apply k4aWeightedSequence38 (fun n => sphere (C n) (ρ n))
      (fun _ z => gradDiscrim38 φ z t i) w A B hA hwA
    intro υ hυ
    exact hseq φ hφ υ (fun n => hshift n (υ n) (hυ n)) t i
  apply k1SquareBound38_of_finite (fun n => pairPointMass38_nonneg _)
  intro T
  change ∑ n ∈ T, (_ + _) ≤ _
  rw [Finset.sum_add_distrib]
  have h0 := (hscalar 0).1 T
  have h1 := (hscalar 1).1 T
  change _ + _ ≤ _
  simp only [k4aDiscrimContourVec38]
  linarith

end
end NlsGge.GK38
