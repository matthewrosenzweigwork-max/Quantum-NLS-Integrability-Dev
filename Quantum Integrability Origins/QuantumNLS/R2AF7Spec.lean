import QuantumNLS.EKernelBound

/-! integrator-authored trusted spec for R-2AF76530 `lem:E-kernel`
(quantitative/static_finite_gap.tex:69-108, sha256 a7feff61…). Objects written independently:
K_N^f(t,u) = (N/κ)(f t − f u) arctan(κ/(N(t−u))), K_N^f(t,t) = 0; K^f(t,u) = ∫₀¹ f'(u+s(t−u)) ds;
λ = N⁻¹ Σ δ_{q_j}; μ = ρ dt; W₁ = inf over probability couplings of ∫|x−y|; ‖g‖∞ = sup |g|.
Claim: for κ > 0 and a density bound Mρ there is C (depending only on κ, Mρ) such that for all
N ≥ 1, q, measurable 0 ≤ ρ ≤ Mρ probability density, f ∈ C_c², and W₁(λ,μ) = w ∈ [0,1]:
|∬K_N^f dλ⊗λ − ∬K^f dμ⊗μ| ≤ C‖f'‖(√w + N^{-2/3}) + 2‖f''‖w. -/

open MeasureTheory
open scoped ENNReal

namespace QuantumNLS.R2AF7Spec

noncomputable def sKN (κ : ℝ) (N : ℕ) (f : ℝ → ℝ) (t u : ℝ) : ℝ :=
  if t = u then 0 else ((N : ℝ) / κ) * (f t - f u) * Real.arctan (κ / ((N : ℝ) * (t - u)))

noncomputable def sKf (f : ℝ → ℝ) (t u : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..1, deriv f (u + s * (t - u))

noncomputable def sSup (g : ℝ → ℝ) : ℝ := ⨆ x, |g x|

noncomputable def sLam (N : ℕ) (q : Fin N → ℝ) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (q j)

noncomputable def sMu (ρ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (ρ t))

noncomputable def sW1 (a b : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (cp : Measure (ℝ × ℝ)) (_ : IsProbabilityMeasure cp ∧ cp.map Prod.fst = a ∧ cp.map Prod.snd = b),
    ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂cp

def Spec : Prop :=
  ∀ (κ Mρ : ℝ), 0 < κ → ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ (q : Fin N → ℝ) (ρ : ℝ → ℝ), Measurable ρ →
    (∀ t, 0 ≤ ρ t) → (∀ t, ρ t ≤ Mρ) → IsProbabilityMeasure (sMu ρ) →
    ∀ (f : ℝ → ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
    ∀ w : ℝ, 0 ≤ w → w ≤ 1 → sW1 (sLam N q) (sMu ρ) = ENNReal.ofReal w →
      |(∫ p, sKN κ N f p.1 p.2 ∂((sLam N q).prod (sLam N q)))
          - ∫ p, sKf f p.1 p.2 ∂((sMu ρ).prod (sMu ρ))|
        ≤ C * sSup (deriv f) * (Real.sqrt w + (N : ℝ) ^ (-(2 / 3 : ℝ)))
          + 2 * sSup (deriv (deriv f)) * w

theorem spec : Spec := fun κ Mρ hκ => QuantumNLS.EKernelBound.E_kernel_bound_exists κ Mρ hκ

end QuantumNLS.R2AF7Spec
