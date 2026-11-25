import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALFreeFields38

namespace NlsGge.ThirdConsultation.AL

open Filter Topology Set MeasureTheory
open NlsGge.AblowitzLadik NlsGge.Pilot NlsGge.SpectralFoundations

theorem al099_meshStep_cast (N : ℕ) :
    alMeshStep38 N = (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) := by
  simp [alMeshStep38]

/-- AL-099: compact spectral energy convergence with a fixed cutoff (wrapper over
`alCompactEnergy_tendsto38`; the `H¹` hypotheses are the ones of `alCompactConsistency38`). -/
theorem al099 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (uN : ℕ → PhysicalL2)
    (huN : ∀ N, SobolevSquareSummable 1 (physicalFourier (uN N)))
    (hPN : ∀ (N : ℕ) (k : ℤ), (N : ℤ) < |k| → physicalFourier (uN N) k = 0)
    (hconv : Tendsto (fun N => h1DistSq38 (uN N) u) atTop (𝓝 0))
    (W : ℝ → ℝ) (hW : Continuous W) (hWeven : ∀ x, W (-x) = W x)
    (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun N : ℕ => (2 / Real.pi) * ∫ lam in (-R)..R,
      W (2 * Real.sin (alMeshStep38 N * lam) / alMeshStep38 N) *
        alGapHeight38 (2 * N + 1) (h1Rep38 (uN N) (huN N)) lam)
      atTop (𝓝 ((2 / Real.pi) * ∫ lam in (-R)..R,
        W (2 * lam) * actualGapHeightE02_38 u lam)) := by
  have hUc : ContinuousOn (h1Rep38 u hu) (Icc (0 : ℝ) 2) :=
    (continuous_h1Rep38 u hu).continuousOn
  have hae := h1_cover_ae38 u hu
  have hU := (h1Rep_tendstoUniformly38 u hu uN huN hconv).mono (subset_univ (Icc (0 : ℝ) 1))
  simp only [al099_meshStep_cast]
  exact alCompactEnergy_tendsto38 u hUc hae hU hW hWeven R hR

end NlsGge.ThirdConsultation.AL
