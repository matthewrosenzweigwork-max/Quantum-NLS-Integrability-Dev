import NlsGge.Schur.FreeResolventComplementaryInverseOnRangeActual

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Positivity of the actual absolute complementary inverse constant. This
small public fact isolates the scalar-constant obligation needed by later
quantitative Schur estimates. -/
theorem freeResolventComplementaryInverseUniformConstant22_posV2_31 :
    0 < freeResolventComplementaryInverseUniformConstant22 := by
  unfold freeResolventComplementaryInverseUniformConstant22
  have hM := NlsGge.Analysis.physicalH1MultiplierConstant_pos
  positivity

/-- The explicit continuous-linear-map norm estimate for the actual
composition order `row ∘ S ∘ V ∘ P`, provided the actual resonant vector is
fixed by `P`. This isolates the norm/composition dictionary step without
assuming any Schur-entry estimate or numerical bound. -/
theorem actualSchurDiagonalComposition_apply_norm_leV2_31
    {n : ℤ} (row S V P : ParityPair n →L[ℂ] ParityPair n)
    (e : ParityPair n) (hPe : P e = e) :
    ‖(row.comp (S.comp (V.comp P))) e‖ ≤
      ‖row‖ * (‖S‖ * (‖V‖ * ‖e‖)) := by
  change ‖row (S (V (P e)))‖ ≤ _
  rw [hPe]
  calc
    _ ≤ ‖row‖ * ‖S (V e)‖ := row.le_opNorm _
    _ ≤ ‖row‖ * (‖S‖ * ‖V e‖) :=
      mul_le_mul_of_nonneg_left (S.le_opNorm _) (norm_nonneg row)
    _ ≤ ‖row‖ * (‖S‖ * (‖V‖ * ‖e‖)) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg row)
      exact mul_le_mul_of_nonneg_left (V.le_opNorm e) (norm_nonneg S)

end NlsGge.Schur
