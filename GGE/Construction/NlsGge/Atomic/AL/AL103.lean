import NlsGge.Hierarchy.ALPlaneConsistency38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38

namespace NlsGge.ThirdConsultation.AL

open Filter Topology Set MeasureTheory
open NlsGge.AblowitzLadik NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.Weights
open NlsGge.HierarchyRiccati.Core

/-- AL-103: the actual continuum gap and its reflected spectral energy (wrapper over
`actualGapHeight_planeWave38`, `planeEnergy_cont38` and `cont_change38`). -/
theorem al103 (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (K : ℕ) (k : ℤ) (hk : k.natAbs ≤ K) (t : ℝ) (ht : 0 ≤ t) :
    (∀ lam : ℝ,
      actualGapHeightE02_38 (planeL2 K (planeWaveCoeff38 K k t)) lam =
        planeGapCont38 t (lam + Real.pi * (k : ℝ))) ∧
    fullEnergy38 c K (planeWaveCoeff38 K k t) =
      (2 / Real.pi) * ∫ lam : ℝ,
        weight c.val (2 * lam) * planeGapCont38 t (lam + Real.pi * (k : ℝ)) ∧
    fullEnergy38 c K (planeWaveCoeff38 K k t) =
      (2 / Real.pi) * ∫ mu : ℝ,
        weight c.val (2 * Real.pi * (k : ℝ) + 2 * mu) * planeGapCont38 t mu := by
  have hE := planeEnergy_cont38 c K k hk t
  have hC := cont_change38 c k t
  refine ⟨fun lam => actualGapHeight_planeWave38 K k hk t lam, hE, ?_⟩
  have e : ∀ mu : ℝ, weight c.val (2 * Real.pi * (k : ℝ) + 2 * mu) =
      weight c.val (2 * (mu + Real.pi * (k : ℝ))) := fun mu => by
    congr 1; ring
  simp_rw [e]
  rw [hE, hC]

end NlsGge.ThirdConsultation.AL
