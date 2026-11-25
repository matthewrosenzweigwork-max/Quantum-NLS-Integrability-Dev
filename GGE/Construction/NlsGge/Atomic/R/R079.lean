import NlsGge.Weights.DerivativeAsymptotics
import NlsGge.Definitions.PilotInterfaces

namespace NlsGge.ThirdConsultation.R

/-- R-079: derivative ratios from tilted moments (wrapper over
`NlsGge.Weights.weight_uniform_derivative_asymptotics`, R := 16). Binding repair: the
unbounded `∀ c, AdmittedCoefficients c` becomes `AdmittedCoefficients lower upper c` with
the interval parameters before `c`. -/
theorem weight_uniform_derivative_asymptotics (lower upper : ℝ)
    (hlower : 0 < lower) (hlower_upper : lower ≤ upper) :
    ∃ C R : ℝ, 0 < R ∧ ∀ c : ℕ → ℝ, NlsGge.Pilot.AdmittedCoefficients lower upper c →
      ∀ r : ℝ, r ≥ R →
        |deriv (NlsGge.Weights.weight c) r / NlsGge.Weights.weight c r - 2 * r ^ (-1 / 2 : ℝ)| ≤
            C * r ^ (-3 / 4 : ℝ) ∧
          |deriv (deriv (NlsGge.Weights.weight c)) r / NlsGge.Weights.weight c r - 4 / r| ≤
            C * r ^ (-5 / 4 : ℝ) := by
  obtain ⟨C, _hC, h⟩ :=
    NlsGge.Weights.weight_uniform_derivative_asymptotics lower upper hlower hlower_upper
  refine ⟨C, 16, by norm_num, fun c hc r hr => ?_⟩
  obtain ⟨-, -, hb⟩ := hc
  exact h c (fun j => (hb j).1) (fun j => (hb j).2) r hr

end NlsGge.ThirdConsultation.R
