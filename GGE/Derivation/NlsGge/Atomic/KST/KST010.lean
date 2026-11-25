import NlsGge.Atomic.KST.KST005
import NlsGge.Atomic.KST.KST007

set_option autoImplicit false
noncomputable section
open scoped ENNReal
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST007

namespace NlsGge.Atomic.KST010

/-- The actual majorant Fourier remainder from source Eq(18). -/
def fourierTail (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) :
    lp (fun _ : ℤ => ℝ) 2 :=
  ⟨fun k : ℤ =>
      if n.natAbs ≤ k.natAbs then
        NlsGge.Atomic.KST007.majorantSequence φ k
      else 0,
    (lp.memℓp (NlsGge.Atomic.KST007.majorantSequence φ)).mono' (by
      intro k
      by_cases hk : n.natAbs ≤ k.natAbs
      · simp only [if_pos hk, le_refl]
      · simp only [if_neg hk, norm_zero]
        exact norm_nonneg _)⟩

/-- The source near-near contribution, as a nonnegative extended sum. -/
def hsSigma3 (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ,
    if (1 : ℝ) ≤ ((j - n).natAbs : ℝ) ∧
        ((j - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2 then
      ∑' l : ℤ,
        ENNReal.ofReal
          ((∑' k : ℤ,
            if (1 : ℝ) ≤ ((k - n).natAbs : ℝ) ∧
                ((k - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2 then
              NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
                NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j
            else 0) ^ 2)
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


private abbrev Near (n k : ℤ) : Prop :=
  (1 : ℝ) ≤ ((k - n).natAbs : ℝ) ∧
    ((k - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2

private def row (φ : PhysicalPairLp) (n l j k : ℤ) : ℝ :=
  if Near n k then a φ (l + k) * a φ (k + j) else 0

private lemma row_nonneg (φ : PhysicalPairLp) (n l j k : ℤ) :
    0 ≤ row φ n l j k := by
  by_cases h : Near n k
  · simp only [row, if_pos h]
    exact mul_nonneg (a_nonneg φ _) (a_nonneg φ _)
  · simp only [row, if_neg h, le_refl]

private lemma row_sq_le (φ : PhysicalPairLp) (n l j k : ℤ) :
    row φ n l j k ^ 2 ≤ A φ ^ 2 * a φ (k + j) ^ 2 := by
  by_cases h : Near n k
  · rw [row, if_pos h, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (a_nonneg φ _) (norm_nonneg _)).mpr (a_le φ _)) (sq_nonneg _)
  · simp only [row, if_neg h, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

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



private lemma tail_apply (φ : PhysicalPairLp) (n k : ℤ) :
    fourierTail φ n k = if n.natAbs ≤ k.natAbs then a φ k else 0 := by
  rfl

private lemma tail_nonneg (φ : PhysicalPairLp) (n k : ℤ) :
    0 ≤ fourierTail φ n k := by
  rw [tail_apply]
  split_ifs
  · exact a_nonneg φ k
  · exact le_rfl

private lemma tail_sq_summable (φ : PhysicalPairLp) (n : ℤ) :
    Summable (fun k : ℤ => fourierTail φ n k ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    (lp.memℓp (fourierTail φ n)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

private lemma tail_sq_sum (φ : PhysicalPairLp) (n : ℤ) :
    (∑' k : ℤ, fourierTail φ n k ^ 2) = ‖fourierTail φ n‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using
    (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (fourierTail φ n)).symm

private lemma tail_shift_sq_summable (φ : PhysicalPairLp) (n j : ℤ) :
    Summable (fun k : ℤ => fourierTail φ n (k + j) ^ 2) :=
  (tail_sq_summable φ n).comp_injective
    (i := fun k : ℤ => k + j) (by intro x y h; exact add_right_cancel h)

private lemma tail_shift_sq_sum (φ : PhysicalPairLp) (n j : ℤ) :
    (∑' k : ℤ, fourierTail φ n (k + j) ^ 2) = ‖fourierTail φ n‖ ^ 2 := by
  have h := (Equiv.addRight j).tsum_eq (fun k : ℤ => fourierTail φ n k ^ 2)
  calc
    _ = ∑' k : ℤ, fourierTail φ n k ^ 2 := by simpa only [Equiv.coe_addRight] using h
    _ = _ := tail_sq_sum φ n

private lemma near_forces_tail (n k j : ℤ) (hk : Near n k) (hj : Near n j) :
    n.natAbs ≤ (k + j).natAbs := by
  have hsub := Int.natAbs_sub_le (k + j) ((k - n) + (j - n))
  have hadd := Int.natAbs_add_le (k - n) (j - n)
  have hid : k + j - ((k - n) + (j - n)) = 2 * n := by ring
  rw [hid, Int.natAbs_mul] at hsub
  norm_num only [Int.natAbs_natCast] at hsub
  have htri : 2 * n.natAbs ≤ (k + j).natAbs + (k - n).natAbs + (j - n).natAbs := by
    omega
  have hreal : 2 * (n.natAbs : ℝ) ≤ ((k + j).natAbs : ℝ) +
      ((k - n).natAbs : ℝ) + ((j - n).natAbs : ℝ) := by exact_mod_cast htri
  have hbound : (n.natAbs : ℝ) ≤ ((k + j).natAbs : ℝ) := by
    linarith [hk.2, hj.2]
  exact_mod_cast hbound


private def nearProduct (φ : PhysicalPairLp) (n l j : ℤ) : ℝ :=
  ∑' k : ℤ, if Near n k then
    positiveKernel φ n false l (-k) * positiveKernel φ n true (-k) j else 0

private lemma source_term (φ : PhysicalPairLp) (n l j k : ℤ) :
    (if Near n k then
      positiveKernel φ n false l (-k) * positiveKernel φ n true (-k) j else 0) =
        d n j * (row φ n l j k * d n k) := by
  by_cases hk : Near n k
  · rw [if_pos hk, row, if_pos hk]
    simp only [positiveKernel, Bool.false_eq_true, ↓reduceIte, sub_neg_eq_add, neg_neg]
    change (a φ (l + k) * d n k) * (a φ (-k - j) * d n j) =
      d n j * (a φ (l + k) * a φ (k + j) * d n k)
    have he : a φ (-k - j) = a φ (k + j) := by
      change majorantCoeff φ (-k - j) = majorantCoeff φ (k + j)
      rw [show -k - j = -(k + j) by ring, majorant_even]
    rw [he]
    ring
  · simp only [if_neg hk, row, zero_mul, mul_zero]

private lemma nearProduct_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => if Near n k then
      positiveKernel φ n false l (-k) * positiveKernel φ n true (-k) j else 0) :=
  ((row_inner_summable φ n l j).mul_left (d n j)).congr
    (fun k => (source_term φ n l j k).symm)

private lemma nearProduct_eq (φ : PhysicalPairLp) (n l j : ℤ) :
    nearProduct φ n l j = d n j * ∑' k : ℤ, row φ n l j k * d n k := by
  unfold nearProduct
  calc
    _ = ∑' k : ℤ, d n j * (row φ n l j k * d n k) := tsum_congr (source_term φ n l j)
    _ = _ := (row_inner_summable φ n l j).tsum_mul_left _

private lemma nearProduct_sq_le (φ : PhysicalPairLp) (n l j : ℤ) :
    nearProduct φ n l j ^ 2 ≤ (4 * d n j ^ 2) * ∑' k : ℤ, row φ n l j k ^ 2 := by
  have hs0 : 0 ≤ ∑' k : ℤ, row φ n l j k * d n k :=
    tsum_nonneg (fun k => mul_nonneg (row_nonneg φ n l j k) (d_nonneg n k))
  have hs := row_inner_le φ n l j
  have hs2 := (sq_le_sq₀ hs0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (norm_nonneg (rowSeq φ n l j)))).mpr hs
  rw [nearProduct_eq, mul_pow]
  calc
    _ ≤ d n j ^ 2 * (2 * ‖rowSeq φ n l j‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hs2 (sq_nonneg _)
    _ = _ := by rw [← rowSeq_sqnorm]; ring

private lemma row_tail_sq_le (φ : PhysicalPairLp) (n l j k : ℤ) (hj : Near n j) :
    row φ n l j k ^ 2 ≤ a φ (l + k) ^ 2 * fourierTail φ n (k + j) ^ 2 := by
  by_cases hk : Near n k
  · rw [row, if_pos hk, tail_apply, if_pos (near_forces_tail n k j hk hj), mul_pow]
  · simp only [row, if_neg hk, zero_pow (by decide : 2 ≠ 0)]
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

private lemma row_double_energy_le (φ : PhysicalPairLp) (n j : ℤ) (hj : Near n j) :
    (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) ≤
      ENNReal.ofReal (A φ ^ 2 * ‖fourierTail φ n‖ ^ 2) := by
  calc
    _ ≤ ∑' l : ℤ, ∑' k : ℤ,
        ENNReal.ofReal (a φ (l + k) ^ 2 * fourierTail φ n (k + j) ^ 2) :=
      ENNReal.tsum_le_tsum (fun l => ENNReal.tsum_le_tsum
        (fun k => ENNReal.ofReal_le_ofReal (row_tail_sq_le φ n l j k hj)))
    _ = ∑' k : ℤ, ∑' l : ℤ,
        ENNReal.ofReal (a φ (l + k) ^ 2 * fourierTail φ n (k + j) ^ 2) := ENNReal.tsum_comm
    _ = ∑' k : ℤ, ENNReal.ofReal (A φ ^ 2) *
        ENNReal.ofReal (fourierTail φ n (k + j) ^ 2) := by
      apply tsum_congr
      intro k
      simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
      rw [ENNReal.tsum_mul_right,
        ← ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg (a φ (l + k)))
          (a_shift_sq_summable φ k), a_shift_sq_sum]
    _ = ENNReal.ofReal (A φ ^ 2) * ENNReal.ofReal (‖fourierTail φ n‖ ^ 2) := by
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg (fourierTail φ n (k + j)))
          (tail_shift_sq_summable φ n j), tail_shift_sq_sum]
    _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm

private lemma near_column_energy_le (φ : PhysicalPairLp) (n j : ℤ) (hj : Near n j) :
    (∑' l : ℤ, ENNReal.ofReal (nearProduct φ n l j ^ 2)) ≤
      ENNReal.ofReal (4 * A φ ^ 2 * ‖fourierTail φ n‖ ^ 2 * d n j ^ 2) := by
  have hc : 0 ≤ 4 * d n j ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  calc
    _ ≤ ∑' l : ℤ, ENNReal.ofReal ((4 * d n j ^ 2) *
        ∑' k : ℤ, row φ n l j k ^ 2) :=
      ENNReal.tsum_le_tsum (fun l => ENNReal.ofReal_le_ofReal (nearProduct_sq_le φ n l j))
    _ = ENNReal.ofReal (4 * d n j ^ 2) *
        (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) := by
      simp_rw [ENNReal.ofReal_mul hc,
        ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg (row φ n _ j k))
          (row_sq_summable φ n _ j)]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal (4 * d n j ^ 2) *
        ENNReal.ofReal (A φ ^ 2 * ‖fourierTail φ n‖ ^ 2) :=
      mul_le_mul_right (row_double_energy_le φ n j hj) _
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; ring

private def nearDistanceSq (n j : ℤ) : ℝ := if Near n j then d n j ^ 2 else 0

private lemma nearDistanceSq_nonneg (n j : ℤ) : 0 ≤ nearDistanceSq n j := by
  unfold nearDistanceSq
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

private lemma nearDistanceSq_le (n j : ℤ) : nearDistanceSq n j ≤ d n j ^ 2 := by
  unfold nearDistanceSq
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

private lemma nearDistanceSq_summable (n : ℤ) : Summable (nearDistanceSq n) :=
  Summable.of_nonneg_of_le (nearDistanceSq_nonneg n) (nearDistanceSq_le n) (d_sq_summable n)

private lemma nearDistanceSq_sum_le (n : ℤ) : (∑' j : ℤ, nearDistanceSq n j) ≤ 4 :=
  ((nearDistanceSq_summable n).tsum_le_tsum (nearDistanceSq_le n) (d_sq_summable n)).trans
    (d_sq_sum_le n)

/-- The source near-near estimate, retaining the full Fourier tail. -/
theorem hs_near_near_le
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) :
    hsSigma3 φ n ≤
      ENNReal.ofReal
        (16 * ‖NlsGge.Atomic.KST007.majorantSequence φ‖ ^ 2 *
          ‖fourierTail φ n‖ ^ 2) := by
  have hc : 0 ≤ 4 * A φ ^ 2 * ‖fourierTail φ n‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  calc
    hsSigma3 φ n ≤ ∑' j : ℤ,
        ENNReal.ofReal (4 * A φ ^ 2 * ‖fourierTail φ n‖ ^ 2) *
          ENNReal.ofReal (nearDistanceSq n j) := by
      change (∑' j : ℤ, if Near n j then
        ∑' l : ℤ, ENNReal.ofReal (nearProduct φ n l j ^ 2) else 0) ≤ _
      apply ENNReal.tsum_le_tsum
      intro j
      by_cases hj : Near n j
      · rw [if_pos hj]
        simpa only [nearDistanceSq, if_pos hj, ENNReal.ofReal_mul hc] using
          near_column_energy_le φ n j hj
      · simp only [if_neg hj, nearDistanceSq, ENNReal.ofReal_zero, mul_zero, le_refl]
    _ = ENNReal.ofReal (4 * A φ ^ 2 * ‖fourierTail φ n‖ ^ 2) *
        ENNReal.ofReal (∑' j : ℤ, nearDistanceSq n j) := by
      rw [ENNReal.tsum_mul_left,
        ← ENNReal.ofReal_tsum_of_nonneg (nearDistanceSq_nonneg n) (nearDistanceSq_summable n)]
    _ ≤ ENNReal.ofReal (4 * A φ ^ 2 * ‖fourierTail φ n‖ ^ 2) * ENNReal.ofReal 4 :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal (nearDistanceSq_sum_le n)) _
    _ = _ := by rw [← ENNReal.ofReal_mul hc]; congr 1; change _ = 16 * A φ ^ 2 * _; ring

end NlsGge.Atomic.KST010
