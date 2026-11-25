import NlsGge.GK38.AbelianFreeDerivative

/-! Source diagonal-minus2 input envelope, from the existing inverse-square convolution.
UNCOMPILED source preparation; all series below are proved summable before use. -/
set_option autoImplicit false
open Set Filter Topology Metric
namespace NlsGge.GK38
noncomputable section

def p3InputRowConvolution38 (s : Lib.L2Seq) (m : ℤ) : ℝ :=
  Lib.c3B 1 (fun n : ℤ => s n) (fun _ => 0) m

def p3InputRowEnvelope38 (s : Lib.L2Seq) (m : ℤ) : ℝ :=
  Real.sqrt (p3InputRowConvolution38 s m)

theorem p3InputRowConvolution_nonneg38 (s : Lib.L2Seq) (m : ℤ) :
    0 ≤ p3InputRowConvolution38 s m :=
  Lib.c3B_nonneg 1 (fun n : ℤ => s n) (fun _ => 0) m

theorem p3InputRowConvolution_terms38 (s : Lib.L2Seq) (m : ℤ) :
    Summable (fun n : ℤ => ‖s n‖ ^ 2 * Lib.c3w m n ^ 2) := by
  have hs : Summable (fun n : ℤ => ‖s n - (0 : ℂ)‖ ^ 2) := by
    simpa only [sub_zero] using (Lib.hasSum_sq_l2 s).summable
  simpa only [sub_zero] using Lib.summable_c3B_term hs m

theorem p3InputRowConvolution_bounds38 (s : Lib.L2Seq) :
    Summable (p3InputRowConvolution38 s) ∧
      (∑' m : ℤ, p3InputRowConvolution38 s m) ≤ ‖s‖ ^ 2 * Lib.invSqSum := by
  have hs : Summable (fun n : ℤ => ‖s n - (0 : ℂ)‖ ^ 2) := by
    simpa only [sub_zero] using (Lib.hasSum_sq_l2 s).summable
  have hb : (∑' n : ℤ, ‖s n - (0 : ℂ)‖ ^ 2) ≤ ‖s‖ ^ 2 := by
    simpa only [sub_zero, Lib.tsum_sq_l2] using (le_rfl : ‖s‖ ^ 2 ≤ ‖s‖ ^ 2)
  have hfin (T : Finset ℤ) :
      ∑ m ∈ T, p3InputRowConvolution38 s m ≤ ‖s‖ ^ 2 * Lib.invSqSum := by
    simpa only [p3InputRowConvolution38, one_pow, one_mul] using
      Lib.sum_c3B_le (c := 1) hs hb T
  exact ⟨summable_of_sum_le (p3InputRowConvolution_nonneg38 s) hfin,
    Real.tsum_le_of_sum_le (p3InputRowConvolution_nonneg38 s) hfin⟩

theorem p3InputRowEnvelope_sq38 (s : Lib.L2Seq) (m : ℤ) :
    p3InputRowEnvelope38 s m ^ 2 = p3InputRowConvolution38 s m :=
  Real.sq_sqrt (p3InputRowConvolution_nonneg38 s m)

theorem p3InputRowEnvelope_bounds38 (s : Lib.L2Seq) :
    Summable (fun m : ℤ => p3InputRowEnvelope38 s m ^ 2) ∧
      (∑' m : ℤ, p3InputRowEnvelope38 s m ^ 2) ≤ ‖s‖ ^ 2 * Lib.invSqSum := by
  simpa only [p3InputRowEnvelope_sq38] using p3InputRowConvolution_bounds38 s

/-- One current-point row sequence controls every signed excited index. -/
theorem p3InputRowEnvelope_point38 (s : Lib.L2Seq) (m n : ℤ) :
    ‖s n‖ * Lib.c3w m n ≤ p3InputRowEnvelope38 s m := by
  have ht := p3InputRowConvolution_terms38 s m
  have he : ‖s n‖ ^ 2 * Lib.c3w m n ^ 2 ≤ p3InputRowConvolution38 s m := by
    unfold p3InputRowConvolution38 Lib.c3B
    simp only [one_pow, one_mul, sub_zero]
    simpa only [Finset.sum_singleton] using
      ht.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => by positivity)
  have hsq := p3InputRowEnvelope_sq38 s m
  have hw := Lib.c3w_nonneg m n
  have hE := Real.sqrt_nonneg (p3InputRowConvolution38 s m)
  change 0 ≤ p3InputRowEnvelope38 s m at hE
  nlinarith [norm_nonneg (s n), mul_nonneg (norm_nonneg (s n)) hw]

theorem p3InputRowEnvelope_common_bound38 (s₀ : Lib.L2Seq) :
    ∃ V : Set Lib.L2Seq, V ∈ 𝓝 s₀ ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ s ∈ V, Summable (fun m : ℤ => p3InputRowEnvelope38 s m ^ 2) ∧
        (∑' m : ℤ, p3InputRowEnvelope38 s m ^ 2) ≤ B := by
  refine ⟨ball s₀ 1, ball_mem_nhds _ (by norm_num),
    (‖s₀‖ + 1) ^ 2 * Lib.invSqSum,
    mul_nonneg (sq_nonneg _) Lib.invSqSum_nonneg, ?_⟩
  intro s hs
  obtain ⟨hsum,hb⟩ := p3InputRowEnvelope_bounds38 s
  have hn : ‖s‖ ≤ ‖s₀‖ + 1 := by
    have hd : ‖s-s₀‖ < 1 := mem_ball_iff_norm.mp hs
    have htri := norm_le_norm_sub_add s s₀
    linarith
  refine ⟨hsum,hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ Lib.invSqSum_nonneg
  nlinarith [norm_nonneg s, norm_nonneg s₀]

end
end NlsGge.GK38
