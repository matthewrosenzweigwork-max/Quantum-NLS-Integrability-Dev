import QuantumNLS.TerraMultiRound85TranslationH1

/-! Strong continuity and group law for the H¹ translation multipliers,
needed for time-dependent Galilean transforms. -/
set_option autoImplicit false
noncomputable section
open scoped Topology
open Filter QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.LocalWellPosedness QuantumNLS.TerraMultiRound85TranslationH1 AddCircle
namespace QuantumNLS.TerraMultiRound85TranslationTime
variable {L : ℝ} [Fact (0 < L)]

/-- Translation multipliers form a one-parameter group. -/
theorem transPhase_add (y z : ℝ) (n : ℤ) :
    transPhase (L := L) (y+z) n = transPhase (L := L) y n * transPhase (L := L) z n := by
  unfold transPhase
  simp only [AddCircle.coe_add, fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

theorem translate_add (s y z : ℝ) (a : h04 L s) :
    QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y+z) a = QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s z a) := by
  apply WSeq.ext
  funext n
  change transPhase (L := L) (y+z) n * a.val n =
    transPhase (L := L) y n * (transPhase (L := L) z n * a.val n)
  rw [transPhase_add]
  ring

theorem norm_translate (s y : ℝ) (a : h04 L s) : ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y a‖ = ‖a‖ := by
  rw [norm_eq_sqrt, norm_eq_sqrt]
  change Real.sqrt (f04NormSq L s (translatedSeq (L := L) y a.val)) = Real.sqrt (f04NormSq L s a.val)
  rw [f04NormSq_translated]

theorem continuous_transPhase (n : ℤ) : Continuous (fun y : ℝ => transPhase (L := L) y n) := by
  unfold transPhase
  simp_rw [fourier_coe_apply]
  fun_prop

/-- The translation orbit is strongly continuous in the actual weighted norm. -/
theorem continuous_translate_apply (s : ℝ) (a : h04 L s) : Continuous fun y => QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y a := by
  rw [continuous_iff_continuousAt]
  intro y0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun y => ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y a - QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y0 a‖ ^ 2) (𝓝 y0) (𝓝 0) := by
    have e : ∀ y, ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y a - QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s y0 a‖ ^ 2 =
        ∑' n, (f04W L s).w n * ‖(transPhase (L := L) y n - transPhase (L := L) y0 n) * a.val n‖ ^ 2 := by
      intro y
      rw [norm_sq_eq_tsum]
      refine tsum_congr fun n => ?_
      simp [translatedSeq, sub_mul]
    simp_rw [e]
    have h0 : (0 : ℝ) = ∑' n : ℤ, (fun _ => (0 : ℝ)) n := by simp
    rw [h0]
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => 4 * ((f04W L s).w n *
      ‖a.val n‖ ^ 2)) (a.summable.mul_left 4) (fun n => ?_) (Eventually.of_forall fun y n => ?_)
    · have hc : Continuous fun y => (f04W L s).w n * ‖(transPhase (L := L) y n - transPhase (L := L) y0 n) * a.val n‖ ^ 2 :=
        continuous_const.mul ((((continuous_transPhase (L := L) n).sub continuous_const).mul continuous_const).norm.pow 2)
      have := hc.tendsto y0
      simpa using this
    · have hw := (f04W L s).pos n
      have h1 : ‖transPhase (L := L) y n - transPhase (L := L) y0 n‖ ≤ 2 := by
        calc _ ≤ ‖transPhase (L := L) y n‖ + ‖transPhase (L := L) y0 n‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_transPhase, norm_transPhase]; norm_num
      rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
      have h2 : ‖transPhase (L := L) y n - transPhase (L := L) y0 n‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (transPhase (L := L) y n - transPhase (L := L) y0 n)]
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖a.val n‖)
      nlinarith
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- Joint continuity along continuous time-dependent data and shifts. -/
theorem continuous_translate_curve (s : ℝ) {y : ℝ → ℝ} (hy : Continuous y)
    {a : ℝ → h04 L s} (ha : Continuous a) : Continuous fun t => QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t) := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun t => ‖a t - a t0‖ + ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t0) - QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t0) (a t0)‖)
      (𝓝 t0) (𝓝 (0 + 0)) := by
    refine Tendsto.add ?_ ?_
    · exact (tendsto_iff_norm_sub_tendsto_zero.mp (ha.tendsto t0))
    · exact (tendsto_iff_norm_sub_tendsto_zero.mp (((continuous_translate_apply s (a t0)).comp hy).tendsto t0))
  rw [add_zero] at h1
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) h1
  calc ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t) - QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t0) (a t0)‖
      = ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t - a t0) + (QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t0) - QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t0) (a t0))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t - a t0)‖ + ‖QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t) (a t0) - QuantumNLS.TerraMultiRound85TranslationH1.translate (L := L) s (y t0) (a t0)‖ := norm_add_le _ _
    _ = _ := by rw [norm_translate]

#print axioms transPhase_add
#print axioms translate_add
#print axioms continuous_translate_apply
#print axioms continuous_translate_curve
end QuantumNLS.TerraMultiRound85TranslationTime
