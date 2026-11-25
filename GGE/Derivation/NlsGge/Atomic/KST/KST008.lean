import NlsGge.Atomic.KST.KST005
import NlsGge.Atomic.KST.KST007

/-! # The far-output contribution in KST Lemma 2.2

Kappeler--Serier--Topalov (2009), printed2082.  The actual positive-product
kernel and full signed Fourier lattice are retained.  Energies are ENNReal;
actual square/absolute summability precedes every real series operation.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST007

namespace NlsGge.Atomic.KST008

/-- The source far-output contribution, retained as a nonnegative extended sum. -/
def hsSigma1 (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ,
    if (n.natAbs : ℝ) / 2 < ((j - n).natAbs : ℝ) then
      ∑' l : ℤ,
        ENNReal.ofReal
          (NlsGge.Atomic.KST007.positiveProductKernel φ n false l j ^ 2)
    else 0

private abbrev a (φ : PhysicalPairLp) (k : ℤ) : ℝ := majorantCoeff φ k
private abbrev A (φ : PhysicalPairLp) : ℝ := ‖majorantSequence φ‖
private abbrev d (n k : ℤ) : ℝ := reciprocalDistance n k

private lemma a_nonneg (φ : PhysicalPairLp) (k : ℤ) : 0 ≤ a φ k :=
  majorant_nonneg φ k

private lemma a_le (φ : PhysicalPairLp) (k : ℤ) : a φ k ≤ A φ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (majorantSequence φ) k
  simpa only [majorantSequence_apply, Real.norm_eq_abs,
    abs_of_nonneg (a_nonneg φ k)] using h

private lemma a_sq_summable (φ : PhysicalPairLp) :
    Summable (fun k : ℤ => a φ k ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, majorantSequence_apply,
    Real.norm_eq_abs, sq_abs] using
    (lp.memℓp (majorantSequence φ)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

private lemma a_sq_sum (φ : PhysicalPairLp) :
    (∑' k : ℤ, a φ k ^ 2) = A φ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, majorantSequence_apply,
    Real.norm_eq_abs, sq_abs] using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (majorantSequence φ)).symm

private lemma a_shift_sq_summable (φ : PhysicalPairLp) (c : ℤ) :
    Summable (fun k : ℤ => a φ (k + c) ^ 2) :=
  (a_sq_summable φ).comp_injective
    (i := fun k : ℤ => k + c) (by intro x y h; exact add_right_cancel h)

private lemma a_shift_sq_sum (φ : PhysicalPairLp) (c : ℤ) :
    (∑' k : ℤ, a φ (k + c) ^ 2) = A φ ^ 2 := by
  have h := (Equiv.addRight c).tsum_eq (fun k : ℤ => a φ k ^ 2)
  calc
    _ = ∑' k : ℤ, a φ k ^ 2 := by simpa only [Equiv.coe_addRight] using h
    _ = _ := a_sq_sum φ

private lemma d_eq (n k : ℤ) : d n k = 1 / ((k - n).natAbs : ℝ) := by
  by_cases h : k = n
  · simp [d, reciprocalDistance, h]
  · simp [d, reciprocalDistance, h, abs_sub_comm]

private lemma d_nonneg (n k : ℤ) : 0 ≤ d n k := by
  rw [d_eq]; positivity

private lemma d_sq_summable (n : ℤ) :
    Summable (fun k : ℤ => d n k ^ 2) := by
  have hbase0 : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hbase : Summable (fun k : ℤ => 1 / (k.natAbs : ℝ) ^ 2) := by
    convert hbase0 using 1 <;> simp [Nat.cast_natAbs, Int.cast_abs, abs_pow]
  have hshift := (Equiv.addRight (-n)).summable_iff.mpr hbase
  refine hshift.congr fun k => ?_
  simp [d_eq, sub_eq_add_neg, div_pow]

private lemma d_sq_sum_le (n : ℤ) : (∑' k : ℤ, d n k ^ 2) ≤ 4 := by
  have he : (fun k : ℤ => d n k ^ 2) =
      fun k : ℤ => 1 / ((k - n).natAbs : ℝ) ^ 2 := by
    funext k
    simp [d_eq, div_pow]
  rw [he]
  exact lattice_reciprocal_sq_bound n

private def distanceSeq (n : ℤ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨d n, memℓp_gen ((d_sq_summable n).congr fun k => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])⟩

private lemma distanceSeq_apply (n k : ℤ) : distanceSeq n k = d n k := rfl

private lemma distanceSeq_sqnorm (n : ℤ) :
    ‖distanceSeq n‖ ^ 2 = ∑' k : ℤ, d n k ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, distanceSeq_apply,
    Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (distanceSeq n)

private lemma distanceSeq_norm_le (n : ℤ) : ‖distanceSeq n‖ ≤ 2 := by
  have h := d_sq_sum_le n
  rw [← distanceSeq_sqnorm] at h
  nlinarith [norm_nonneg (distanceSeq n)]

private def row (φ : PhysicalPairLp) (n l j k : ℤ) : ℝ :=
  if k = n then 0 else a φ (l + k) * a φ (k + j)

private lemma row_nonneg (φ : PhysicalPairLp) (n l j k : ℤ) :
    0 ≤ row φ n l j k := by
  by_cases h : k = n
  · simp [row, h]
  · simp only [row, if_neg h]
    exact mul_nonneg (a_nonneg φ _) (a_nonneg φ _)

private lemma row_sq_le (φ : PhysicalPairLp) (n l j k : ℤ) :
    row φ n l j k ^ 2 ≤ A φ ^ 2 * a φ (k + j) ^ 2 := by
  by_cases h : k = n
  · simp only [row, if_pos h, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [row, if_neg h, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (a_nonneg φ _) (norm_nonneg _)).mpr (a_le φ _)) (sq_nonneg _)

private lemma row_sq_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => row φ n l j k ^ 2) :=
  Summable.of_nonneg_of_le (fun k => sq_nonneg _) (row_sq_le φ n l j)
    ((a_shift_sq_summable φ j).mul_left (A φ ^ 2))

private def rowSeq (φ : PhysicalPairLp) (n l j : ℤ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨row φ n l j, memℓp_gen ((row_sq_summable φ n l j).congr fun k => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])⟩

private lemma rowSeq_apply (φ : PhysicalPairLp) (n l j k : ℤ) :
    rowSeq φ n l j k = row φ n l j k := rfl

private lemma rowSeq_sqnorm (φ : PhysicalPairLp) (n l j : ℤ) :
    ‖rowSeq φ n l j‖ ^ 2 = ∑' k : ℤ, row φ n l j k ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, rowSeq_apply,
    Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (rowSeq φ n l j)

private lemma holder22 :
    (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
  rw [Real.holderConjugate_iff]; norm_num

private lemma row_inner_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => row φ n l j k * d n k) := by
  have h := lp.summable_mul holder22 (rowSeq φ n l j) (distanceSeq n)
  refine h.congr fun k => ?_
  change ‖row φ n l j k‖ * ‖d n k‖ = _
  simp only [Real.norm_eq_abs, abs_of_nonneg (row_nonneg φ n l j k),
    abs_of_nonneg (d_nonneg n k)]

private lemma row_inner_le (φ : PhysicalPairLp) (n l j : ℤ) :
    (∑' k : ℤ, row φ n l j k * d n k) ≤ 2 * ‖rowSeq φ n l j‖ := by
  have h := (lp.tsum_mul_le_mul_norm holder22 (rowSeq φ n l j) (distanceSeq n)).2
  have he : (fun k : ℤ => ‖rowSeq φ n l j k‖ * ‖distanceSeq n k‖) =
      fun k : ℤ => row φ n l j k * d n k := by
    funext k
    simp only [rowSeq_apply, distanceSeq_apply, Real.norm_eq_abs,
      abs_of_nonneg (row_nonneg φ n l j k), abs_of_nonneg (d_nonneg n k)]
  rw [he] at h
  calc
    _ ≤ ‖rowSeq φ n l j‖ * ‖distanceSeq n‖ := h
    _ ≤ ‖rowSeq φ n l j‖ * 2 :=
      mul_le_mul_of_nonneg_left (distanceSeq_norm_le n) (norm_nonneg _)
    _ = _ := by ring


private lemma row_inner_term (φ : PhysicalPairLp) (n l j k : ℤ) :
    row φ n l j k * d n k = a φ (l + k) * a φ (k + j) * d n k := by
  by_cases h : k = n
  · simp [row, h, d, reciprocalDistance]
  · simp only [row, if_neg h]

private lemma kernel_sq_le (φ : PhysicalPairLp) (n l j : ℤ) :
    positiveProductKernel φ n false l j ^ 2 ≤
      (4 * d n j ^ 2) * ∑' k : ℤ, row φ n l j k ^ 2 := by
  have he : (∑' k : ℤ, row φ n l j k * d n k) =
      ∑' k : ℤ, a φ (l + k) * a φ (k + j) * d n k :=
    tsum_congr (row_inner_term φ n l j)
  have hs0 : 0 ≤ ∑' k : ℤ, row φ n l j k * d n k :=
    tsum_nonneg (fun k => mul_nonneg (row_nonneg φ n l j k) (d_nonneg n k))
  have hs := row_inner_le φ n l j
  have hs2 := (sq_le_sq₀ hs0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (norm_nonneg (rowSeq φ n l j)))).mpr hs
  rw [positiveProductKernel_minus_plus]
  change (d n j * (∑' k : ℤ, a φ (l + k) * a φ (k + j) * d n k)) ^ 2 ≤ _
  rw [← he, mul_pow]
  calc
    _ ≤ d n j ^ 2 * (2 * ‖rowSeq φ n l j‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)
    _ = _ := by rw [← rowSeq_sqnorm]; ring

private lemma row_product_sq_le (φ : PhysicalPairLp) (n l j k : ℤ) :
    row φ n l j k ^ 2 ≤ a φ (l + k) ^ 2 * a φ (k + j) ^ 2 := by
  by_cases h : k = n
  · simp only [row, if_pos h, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · simp only [row, if_neg h, mul_pow, le_refl]

private lemma row_double_energy_le (φ : PhysicalPairLp) (n j : ℤ) :
    (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) ≤
      ENNReal.ofReal (A φ ^ 4) := by
  calc
    _ ≤ ∑' l : ℤ, ∑' k : ℤ,
        ENNReal.ofReal (a φ (l + k) ^ 2 * a φ (k + j) ^ 2) :=
      ENNReal.tsum_le_tsum (fun l => ENNReal.tsum_le_tsum
        (fun k => ENNReal.ofReal_le_ofReal (row_product_sq_le φ n l j k)))
    _ = ∑' k : ℤ, ∑' l : ℤ,
        ENNReal.ofReal (a φ (l + k) ^ 2 * a φ (k + j) ^ 2) := ENNReal.tsum_comm
    _ = ∑' k : ℤ, ENNReal.ofReal (A φ ^ 2) * ENNReal.ofReal (a φ (k + j) ^ 2) := by
      apply tsum_congr
      intro k
      simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
      rw [ENNReal.tsum_mul_right,
        ← ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg (a φ (l + k)))
          (a_shift_sq_summable φ k), a_shift_sq_sum]
    _ = ENNReal.ofReal (A φ ^ 2) * ENNReal.ofReal (A φ ^ 2) := by
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg (a φ (k + j)))
          (a_shift_sq_summable φ j), a_shift_sq_sum]
    _ = _ := by rw [← ENNReal.ofReal_mul (sq_nonneg _)]; congr 1; ring

private lemma column_energy_le (φ : PhysicalPairLp) (n j : ℤ) :
    (∑' l : ℤ, ENNReal.ofReal (positiveProductKernel φ n false l j ^ 2)) ≤
      ENNReal.ofReal (4 * A φ ^ 4 * d n j ^ 2) := by
  have hc : 0 ≤ 4 * d n j ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  calc
    _ ≤ ∑' l : ℤ, ENNReal.ofReal ((4 * d n j ^ 2) *
        ∑' k : ℤ, row φ n l j k ^ 2) :=
      ENNReal.tsum_le_tsum (fun l => ENNReal.ofReal_le_ofReal (kernel_sq_le φ n l j))
    _ = ENNReal.ofReal (4 * d n j ^ 2) *
        (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) := by
      simp_rw [ENNReal.ofReal_mul hc,
        ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg (row φ n _ j k))
          (row_sq_summable φ n _ j)]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (4 * d n j ^ 2) * ENNReal.ofReal (A φ ^ 4) :=
      mul_le_mul_right (row_double_energy_le φ n j) _
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring


private def farTail (n j : ℤ) : ℝ :=
  if (n.natAbs : ℝ) / 2 < ((j - n).natAbs : ℝ) then d n j ^ 2 else 0

private lemma farTail_nonneg (n j : ℤ) : 0 ≤ farTail n j := by
  unfold farTail
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

private lemma farTail_le (n j : ℤ) : farTail n j ≤ d n j ^ 2 := by
  unfold farTail
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

private lemma farTail_summable (n : ℤ) : Summable (farTail n) :=
  Summable.of_nonneg_of_le (farTail_nonneg n) (farTail_le n) (d_sq_summable n)

private lemma farTail_sum_le (n : ℤ) (hn : 5 ≤ n.natAbs) :
    (∑' j : ℤ, farTail n j) ≤ 5 / (n.natAbs : ℝ) := by
  simpa [farTail, d_eq] using lattice_reciprocal_sq_tail_contract hn

/-- The source far-output estimate, with the universal constant twenty. -/
theorem hs_far_output_le
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ)
    (hn : 5 ≤ n.natAbs) :
    hsSigma1 φ n ≤
      ENNReal.ofReal
        (20 * ‖NlsGge.Atomic.KST007.majorantSequence φ‖ ^ 4 /
          (n.natAbs : ℝ)) := by
  have hc : 0 ≤ 4 * A φ ^ 4 := mul_nonneg (by norm_num) (pow_nonneg (norm_nonneg _) _)
  calc
    hsSigma1 φ n ≤ ∑' j : ℤ,
        ENNReal.ofReal (4 * A φ ^ 4) * ENNReal.ofReal (farTail n j) := by
      unfold hsSigma1
      apply ENNReal.tsum_le_tsum
      intro j
      by_cases hfar : (n.natAbs : ℝ) / 2 < ((j - n).natAbs : ℝ)
      · rw [if_pos hfar]
        simpa only [farTail, if_pos hfar, ENNReal.ofReal_mul hc] using column_energy_le φ n j
      · simp only [if_neg hfar, farTail, ENNReal.ofReal_zero, mul_zero, le_refl]
    _ = ENNReal.ofReal (4 * A φ ^ 4) * ENNReal.ofReal (∑' j : ℤ, farTail n j) := by
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (farTail_nonneg n) (farTail_summable n)]
    _ ≤ ENNReal.ofReal (4 * A φ ^ 4) * ENNReal.ofReal (5 / (n.natAbs : ℝ)) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (farTail_sum_le n hn)) _
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; change _ = 20 * A φ ^ 4 / _; ring

end NlsGge.Atomic.KST008
