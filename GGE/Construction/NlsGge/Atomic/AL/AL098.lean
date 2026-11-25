import NlsGge.Hierarchy.ALCompactConsistency38
import NlsGge.Hierarchy.ALFreeFields38
import NlsGge.Hierarchy.ALFullEnergy38

namespace NlsGge.ThirdConsultation.AL

open Filter Topology Set MeasureTheory
open NlsGge.AblowitzLadik NlsGge.Pilot NlsGge.SpectralFoundations

theorem al098_meshStep_cast (N : ℕ) :
    alMeshStep38 N = (1 : ℝ) / ((2 * N + 1 : ℕ) : ℝ) := by
  simp [alMeshStep38]

/-- AL-098: gap-height convergence including closed gaps (wrapper over
`alGapHeight38_eq_kappa` and `alGapHeight_tendstoUniformlyOn38`). -/
theorem al098 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (uN : ℕ → PhysicalL2)
    (huN : ∀ N, SobolevSquareSummable 1 (physicalFourier (uN N)))
    (hPN : ∀ (N : ℕ) (k : ℤ), (N : ℤ) < |k| → physicalFourier (uN N) k = 0)
    (hconv : Tendsto (fun N => h1DistSq38 (uN N) u) atTop (𝓝 0)) :
    (∀ N : ℕ, ∀ lam : ℝ,
      alGapHeight38 (2 * N + 1) (h1Rep38 (uN N) (huN N)) lam =
        alVh38 (alMeshStep38 N)
          (alSampleField38 (2 * N + 1) (h1Rep38 (uN N) (huN N))) lam) ∧
    ∀ R : ℝ, 0 ≤ R → TendstoUniformlyOn
      (fun N lam => alGapHeight38 (2 * N + 1) (h1Rep38 (uN N) (huN N)) lam)
      (fun lam => actualGapHeightE02_38 u (-lam)) atTop (Icc (-R) R) := by
  refine ⟨?_, ?_⟩
  · intro N lam
    have hL : (2 * N + 1 : ℕ) ≠ 0 := by omega
    unfold alVh38
    rw [alGapHeight38_eq_kappa hL, al098_meshStep_cast, inv_div, div_one]
  · have hUc : ContinuousOn (h1Rep38 u hu) (Icc (0 : ℝ) 2) :=
      (continuous_h1Rep38 u hu).continuousOn
    have hae := h1_cover_ae38 u hu
    have hU := (h1Rep_tendstoUniformly38 u hu uN huN hconv).mono (subset_univ (Icc (0 : ℝ) 1))
    intro R _hR
    exact alGapHeight_tendstoUniformlyOn38 u hUc hae hU R

end NlsGge.ThirdConsultation.AL
