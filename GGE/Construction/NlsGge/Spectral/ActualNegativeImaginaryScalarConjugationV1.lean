import NlsGge.Spectral.ActualFullImaginaryFreeSourceResolventV3

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate

namespace NlsGge.Schur

/-- Every signed source mode is retained, including zero: this is the full
coefficient at the negative imaginary point, not the complementary resolvent. -/
def sourceFullNegativeImaginaryResolventCoeff {n : ℤ} (y : ℝ)
    (m : Sector n) : ℂ :=
  (-Complex.I * (y : ℂ) - spectralCenter m.val)⁻¹

theorem sourceFullNegativeImaginaryResolventCoeff_eq_conj
    {n : ℤ} (y : ℝ) (m : Sector n) :
    sourceFullNegativeImaginaryResolventCoeff y m =
      conj (sourceFullImaginaryResolventCoeff y m) := by
  simp [sourceFullNegativeImaginaryResolventCoeff,
    sourceFullImaginaryResolventCoeff, spectralCenter_eq_ofReal_pi_mul,
    map_inv₀, map_sub, map_mul]

theorem sourceFullNegativeImaginaryResolventCoeff_norm_le_one
    {n : ℤ} (y : ℝ) (hy : 1 ≤ y) (m : Sector n) :
    ‖sourceFullNegativeImaginaryResolventCoeff y m‖ ≤ 1 := by
  rw [sourceFullNegativeImaginaryResolventCoeff_eq_conj, Complex.norm_conj]
  exact sourceFullImaginaryResolventCoeff_norm_le_one y hy m

theorem sourceFullNegativeImaginaryResolvent_weightedCoeff_norm_le_one
    {n : ℤ} (y : ℝ) (hy : 0 < y) (m : Sector n) :
    ‖spectralCenter m.val * sourceFullNegativeImaginaryResolventCoeff y m‖ ≤ 1 := by
  have hconj : spectralCenter m.val * sourceFullNegativeImaginaryResolventCoeff y m =
      conj (spectralCenter m.val * sourceFullImaginaryResolventCoeff y m) := by
    rw [sourceFullNegativeImaginaryResolventCoeff_eq_conj]
    simp [map_mul, spectralCenter_eq_ofReal_pi_mul]
  rw [hconj, Complex.norm_conj]
  exact sourceFullImaginaryResolvent_weightedCoeff_norm_le_one y hy m

end NlsGge.Schur

