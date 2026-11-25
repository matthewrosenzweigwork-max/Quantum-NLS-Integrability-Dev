import NlsGge.Spectral.ActualEvenHalfTranslationProjectionV1
import NlsGge.Spectral.ActualNatTwoSmulComplexScalarCoherenceMinimumV1
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The actual odd-parity projection lands in the closed one-parity eigenspace. -/
theorem actualOddHalfTranslationProjection_mem (f : SpectralScalarL2) :
    ((2 : ℂ)⁻¹ • (f - halfTranslation f)) ∈ scalarParity (1 : ℤ) := by
  rw [mem_scalarParity]
  calc
    halfTranslation ((2 : ℂ)⁻¹ • (f - halfTranslation f)) =
        (2 : ℂ)⁻¹ • (halfTranslation f - f) := by
      rw [map_smul, map_sub, halfTranslation_involutive_actual_v2]
    _ = spectralSign (1 : ℤ) • ((2 : ℂ)⁻¹ • (f - halfTranslation f)) := by
      simp [spectralSign, smul_sub, smul_smul]
      module

/-- The two actual parity projections reconstruct every doubled-circle L² class. -/
theorem actualEvenOddHalfTranslationProjection_add (f : SpectralScalarL2) :
    ((2 : ℂ)⁻¹ • (f + halfTranslation f)) +
        ((2 : ℂ)⁻¹ • (f - halfTranslation f)) = f := by
  let a : ℂ := (2 : ℂ)⁻¹
  calc
    a • (f + halfTranslation f) + a • (f - halfTranslation f) =
        a • ((f + halfTranslation f) + (f - halfTranslation f)) := by
          rw [← smul_add]
    _ = a • (2 • f) := by congr 1 <;> abel
    _ = (a * (2 : ℂ)) • f := by
      exact actual_nat_two_smul_complex_scalar_coherence a f
    _ = f := by norm_num [a]

end NlsGge.Schur

end
