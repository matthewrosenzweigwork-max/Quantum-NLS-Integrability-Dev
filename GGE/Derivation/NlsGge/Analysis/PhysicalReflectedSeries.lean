import NlsGge.Analysis.PhysicalDoubleSeries

set_option autoImplicit false
noncomputable section
namespace NlsGge.Analysis
open NlsGge.Pilot

/-- Negation reindexes the second source block; it does not conjugate its independent field. -/
def reflectedPairIndex : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun rs := (-rs.1, -rs.2)
  invFun rs := (-rs.1, -rs.2)
  left_inv rs := by ext <;> dsimp <;> omega
  right_inv rs := by ext <;> dsimp <;> omega

theorem reflectedPairIndex_term (u : PhysicalL2) (n : ℤ) (rs : ℤ × ℤ) :
    ‖physicalFourier u (-n + (reflectedPairIndex rs).1 + (reflectedPairIndex rs).2)‖ ^ 2 *
        inverseSquare (reflectedPairIndex rs).1 * inverseSquare (reflectedPairIndex rs).2 =
      ‖physicalFourier u (-(n + rs.1 + rs.2))‖ ^ 2 * inverseSquare rs.1 * inverseSquare rs.2 := by
  change ‖physicalFourier u (-n + -rs.1 + -rs.2)‖ ^ 2 *
    inverseSquare (-rs.1) * inverseSquare (-rs.2) = _
  have hi : -n + -rs.1 + -rs.2 = -(n + rs.1 + rs.2) := by omega
  rw [hi, inverseSquare_neg, inverseSquare_neg]

theorem physicalH1_reflected_double_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    Summable (fun rs : ℤ × ℤ => ‖physicalFourier u (-(n + rs.1 + rs.2))‖ ^ 2 *
      inverseSquare rs.1 * inverseSquare rs.2) := by
  have hs := (physicalH1_source_double_summable u hu (-n)).comp_injective reflectedPairIndex.injective
  exact hs.congr (fun rs => reflectedPairIndex_term u n rs)

theorem physicalH1_reflected_double_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) :
    (∑' rs : ℤ × ℤ, ‖physicalFourier u (-(n + rs.1 + rs.2))‖ ^ 2 *
      inverseSquare rs.1 * inverseSquare rs.2) ≤
      (2 * uniformConvolutionConstant / (1 + (n : ℝ) ^ 2)) *
        ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs := physicalH1_reflected_double_summable u hu n
  have heq : (∑' rs : ℤ × ℤ, ‖physicalFourier u (-(n + rs.1 + rs.2))‖ ^ 2 *
      inverseSquare rs.1 * inverseSquare rs.2) =
      ∑' rs : ℤ × ℤ, ‖physicalFourier u (-n + rs.1 + rs.2)‖ ^ 2 *
        inverseSquare rs.1 * inverseSquare rs.2 := by
    calc
      _ = ∑' rs : ℤ × ℤ, ‖physicalFourier u (-n + (reflectedPairIndex rs).1 +
          (reflectedPairIndex rs).2)‖ ^ 2 * inverseSquare (reflectedPairIndex rs).1 *
          inverseSquare (reflectedPairIndex rs).2 :=
        tsum_congr (fun rs => (reflectedPairIndex_term u n rs).symm)
      _ = _ := reflectedPairIndex.tsum_eq
        (fun rs : ℤ × ℤ => ‖physicalFourier u (-n + rs.1 + rs.2)‖ ^ 2 *
          inverseSquare rs.1 * inverseSquare rs.2)
  rw [heq]
  simpa only [Int.cast_neg, neg_sq] using physicalH1_source_double_tsum_bound u hu (-n)

/-- Literal p≠n subtype negation preserves the nonresonant column. -/
def reflectedColumnIndex (n : ℤ) : {p : ℤ // p ≠ n} ≃ {p : ℤ // p ≠ -n} where
  toFun p := ⟨-p.val, by have h := p.property; omega⟩
  invFun p := ⟨-p.val, by have h := p.property; omega⟩
  left_inv p := by apply Subtype.ext; dsimp; omega
  right_inv p := by apply Subtype.ext; dsimp; omega

theorem reflectedColumnIndex_term (u : PhysicalL2) (n : ℤ) (p : {p : ℤ // p ≠ n}) :
    ‖physicalFourier u (reflectedColumnIndex n p).val‖ ^ 2 *
        inverseSquare (-n - (reflectedColumnIndex n p).val) =
      ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (n - p.val) := by
  change ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (-n - -p.val) = _
  have hi : -n - -p.val = -(n - p.val) := by omega
  rw [hi, inverseSquare_neg]

theorem physicalH1_reflected_column_summable (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) (hn : n ≠ 0) :
    Summable (fun p : {p : ℤ // p ≠ n} =>
      ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (n - p.val)) := by
  have hs := (summable_weighted_column_nonresonant (fun p => ‖physicalFourier u p‖ ^ 2)
    (fun p => sq_nonneg _) (physicalH1_weighted_summable u hu) (-n) (by omega)).comp_injective
    (reflectedColumnIndex n).injective
  exact hs.congr (fun p => reflectedColumnIndex_term u n p)

theorem physicalH1_reflected_column_tsum_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) (hn : n ≠ 0) :
    (∑' p : {p : ℤ // p ≠ n}, ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (n - p.val)) ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  have hs := physicalH1_reflected_column_summable u hu n hn
  have heq : (∑' p : {p : ℤ // p ≠ n}, ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (n - p.val)) =
      ∑' p : {p : ℤ // p ≠ -n}, ‖physicalFourier u p.val‖ ^ 2 * inverseSquare (-n - p.val) := by
    calc
      _ = ∑' p : {p : ℤ // p ≠ n}, ‖physicalFourier u (reflectedColumnIndex n p).val‖ ^ 2 *
          inverseSquare (-n - (reflectedColumnIndex n p).val) :=
        tsum_congr (fun p => (reflectedColumnIndex_term u n p).symm)
      _ = _ := (reflectedColumnIndex n).tsum_eq
        (fun p : {p : ℤ // p ≠ -n} => ‖physicalFourier u p.val‖ ^ 2 * inverseSquare (-n - p.val))
  rw [heq]
  simpa only [Int.cast_neg, neg_sq] using physicalH1_column_nonresonant_bound u hu (-n) (by omega)

end NlsGge.Analysis
