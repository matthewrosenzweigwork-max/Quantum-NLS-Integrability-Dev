import NlsGge.Atomic.KST.KST005
import NlsGge.Atomic.KST.KST007

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Atomic.KST009

/-- The far-intermediate contribution, expressed using the actual positive kernels. -/
def hsSigma2 (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ∑' l : ℤ,
    ENNReal.ofReal
      ((∑' k : ℤ,
          if (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ) then
            NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
              NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j
          else 0) ^ 2)

private lemma source_kernel_product
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n l j k : ℤ) :
    NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
        NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j =
      NlsGge.Atomic.KST007.majorantCoeff φ (l + k) *
        NlsGge.Atomic.KST007.majorantCoeff φ (k + j) *
          NlsGge.Atomic.KST007.reciprocalDistance n k *
            NlsGge.Atomic.KST007.reciprocalDistance n j := by
  simp [NlsGge.Atomic.KST007.positiveKernel]
  have h₂ : -k - j = -(k + j) := by omega
  rw [h₂, NlsGge.Atomic.KST007.majorant_even φ (k + j)]
  ring

open NlsGge.Atomic.KST002 NlsGge.Atomic.KST007

private abbrev a (φ : PhysicalPairLp) (k : ℤ) : ℝ := majorantCoeff φ k
private abbrev A (φ : PhysicalPairLp) : ℝ := ‖majorantSequence φ‖
private abbrev d (n k : ℤ) : ℝ := reciprocalDistance n k

private def far (n k : ℤ) : Prop :=
  (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ)

private lemma a_nonneg (φ : PhysicalPairLp) (k : ℤ) : 0 ≤ a φ k :=
  majorant_nonneg φ k

private lemma a_le (φ : PhysicalPairLp) (k : ℤ) : a φ k ≤ A φ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (majorantSequence φ) k
  simpa only [a, A, majorantSequence_apply, Real.norm_eq_abs,
    abs_of_nonneg (a_nonneg φ k)] using h

private lemma a_sq_summable (φ : PhysicalPairLp) :
    Summable (fun k : ℤ => a φ k ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, a, majorantSequence_apply,
    Real.norm_eq_abs, sq_abs] using
    (lp.memℓp (majorantSequence φ)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

private lemma a_sq_sum (φ : PhysicalPairLp) :
    (∑' k : ℤ, a φ k ^ 2) = A φ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, a, A,
    majorantSequence_apply, Real.norm_eq_abs, sq_abs] using
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

private lemma a_shift_sq_sum_ennreal (φ : PhysicalPairLp) (c : ℤ) :
    (∑' k : ℤ, ENNReal.ofReal (a φ (k + c) ^ 2)) =
      ENNReal.ofReal (A φ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
    (a_shift_sq_summable φ c)]
  rw [a_shift_sq_sum]

private lemma d_eq (n k : ℤ) : d n k = 1 / ((k - n).natAbs : ℝ) := by
  by_cases h : k = n
  · simp [d, reciprocalDistance, h]
  · simp [d, reciprocalDistance, h, abs_sub_comm]

private lemma d_nonneg (n k : ℤ) : 0 ≤ d n k := by
  rw [d_eq]
  positivity

private lemma d_sq_summable (n : ℤ) : Summable (fun k : ℤ => d n k ^ 2) := by
  have hbase0 : Summable (fun k : ℤ => 1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_int_pow (p := 2)).mpr (by norm_num)
  have hbase : Summable (fun k : ℤ => 1 / (k.natAbs : ℝ) ^ 2) := by
    refine hbase0.congr fun k => ?_
    simp [Nat.cast_natAbs, Int.cast_abs]
  have hshift := (Equiv.addRight (-n)).summable_iff.mpr hbase
  refine hshift.congr fun k => ?_
  simp [d_eq, sub_eq_add_neg]

private lemma d_sq_sum_le (n : ℤ) : (∑' k : ℤ, d n k ^ 2) ≤ 4 := by
  have he : (fun k : ℤ => d n k ^ 2) =
      fun k : ℤ => if k ≠ n then 1 / ((k - n).natAbs : ℝ) ^ 2 else 0 := by
    funext k
    by_cases h : k = n
    · simp [d, reciprocalDistance, h]
    · simp [d_eq, h]
  rw [he]
  exact lattice_reciprocal_sq_bound_contract n

private noncomputable def farDistance (n k : ℤ) : ℝ := by
  classical
  exact if far n k then d n k else 0

private lemma farDistance_nonneg (n k : ℤ) : 0 ≤ farDistance n k := by
  classical
  by_cases h : far n k <;> simp [farDistance, h, d_nonneg]

private lemma farDistance_sq_summable (n : ℤ) :
    Summable (fun k : ℤ => farDistance n k ^ 2) := by
  classical
  refine Summable.of_nonneg_of_le
    (f := fun k : ℤ => d n k ^ 2)
    (g := fun k : ℤ => farDistance n k ^ 2)
    (fun k => sq_nonneg _) ?_ (d_sq_summable n)
  intro k
  by_cases h : far n k
  · simp [farDistance, h]
  · simp [farDistance, h]
    exact sq_nonneg (d n k)

private lemma farDistance_sq_sum_le {n : ℤ} (hn : 5 ≤ n.natAbs) :
    (∑' k : ℤ, farDistance n k ^ 2) ≤ 5 / (n.natAbs : ℝ) := by
  classical
  have he : (fun k : ℤ => farDistance n k ^ 2) = fun k : ℤ =>
      if far n k then 1 / ((k - n).natAbs : ℝ) ^ 2 else 0 := by
    funext k
    simp [farDistance, far, d_eq]
  rw [he]
  exact lattice_reciprocal_sq_tail_contract hn

private noncomputable def row (φ : PhysicalPairLp) (n l j k : ℤ) : ℝ := by
  classical
  exact if far n k then a φ (l + k) * a φ (k + j) else 0

private lemma row_nonneg (φ : PhysicalPairLp) (n l j k : ℤ) :
    0 ≤ row φ n l j k := by
  classical
  by_cases h : far n k
  · simp [row, h]
    exact mul_nonneg (a_nonneg φ _) (a_nonneg φ _)
  · simp [row, h]

private lemma row_sq_le_product (φ : PhysicalPairLp) (n l j k : ℤ) :
    row φ n l j k ^ 2 ≤ a φ (l + k) ^ 2 * a φ (k + j) ^ 2 := by
  classical
  by_cases h : far n k
  · simp [row, h, mul_pow]
  · simp [row, h]
    positivity

private lemma row_energy_le (φ : PhysicalPairLp) (n j : ℤ) :
    (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) ≤
      ENNReal.ofReal (A φ ^ 4) := by
  calc
    (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) ≤
        ∑' l : ℤ, ∑' k : ℤ,
          ENNReal.ofReal (a φ (l + k) ^ 2) * ENNReal.ofReal (a φ (k + j) ^ 2) := by
      apply ENNReal.tsum_le_tsum
      intro l
      apply ENNReal.tsum_le_tsum
      intro k
      calc
        ENNReal.ofReal (row φ n l j k ^ 2) ≤
            ENNReal.ofReal (a φ (l + k) ^ 2 * a φ (k + j) ^ 2) :=
          ENNReal.ofReal_le_ofReal (row_sq_le_product φ n l j k)
        _ = ENNReal.ofReal (a φ (l + k) ^ 2) *
            ENNReal.ofReal (a φ (k + j) ^ 2) :=
          ENNReal.ofReal_mul (sq_nonneg _)
    _ = ∑' k : ℤ, ∑' l : ℤ,
          ENNReal.ofReal (a φ (l + k) ^ 2) * ENNReal.ofReal (a φ (k + j) ^ 2) :=
      ENNReal.tsum_comm
    _ = ∑' k : ℤ,
          ENNReal.ofReal (a φ (k + j) ^ 2) * ENNReal.ofReal (A φ ^ 2) := by
      congr 1
      funext k
      rw [ENNReal.tsum_mul_right, a_shift_sq_sum_ennreal]
      rw [mul_comm]
    _ = ENNReal.ofReal (A φ ^ 2) * ENNReal.ofReal (A φ ^ 2) := by
      rw [ENNReal.tsum_mul_right, a_shift_sq_sum_ennreal]
    _ = ENNReal.ofReal (A φ ^ 4) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg (A φ))]
      congr 1
      ring

private lemma row_sq_le (φ : PhysicalPairLp) (n l j k : ℤ) :
    row φ n l j k ^ 2 ≤ A φ ^ 2 * a φ (k + j) ^ 2 := by
  classical
  by_cases h : far n k
  · have hrow : row φ n l j k = a φ (l + k) * a φ (k + j) := by
      simp [row, h]
    rw [hrow, mul_pow]
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ (a_nonneg φ _) (norm_nonneg _)).mpr (a_le φ _))
      (sq_nonneg _)
  · simp [row, h]
    positivity

private lemma row_sq_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => row φ n l j k ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (row_sq_le φ n l j)
    ((a_shift_sq_summable φ j).mul_left (A φ ^ 2))

private def rowSeq (φ : PhysicalPairLp) (n l j : ℤ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨row φ n l j, memℓp_gen ((row_sq_summable φ n l j).congr fun k => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      abs_of_nonneg (row_nonneg φ n l j k)])⟩

private lemma rowSeq_apply (φ : PhysicalPairLp) (n l j k : ℤ) :
    rowSeq φ n l j k = row φ n l j k := rfl

private lemma rowSeq_sqnorm (φ : PhysicalPairLp) (n l j : ℤ) :
    ‖rowSeq φ n l j‖ ^ 2 = ∑' k : ℤ, row φ n l j k ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, rowSeq_apply,
    Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (rowSeq φ n l j)

private def farDistanceSeq (n : ℤ) : lp (fun _ : ℤ => ℝ) 2 :=
  ⟨farDistance n, memℓp_gen ((farDistance_sq_summable n).congr fun k => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])⟩

private lemma farDistanceSeq_apply (n k : ℤ) :
    farDistanceSeq n k = farDistance n k := rfl

private lemma farDistanceSeq_sqnorm (n : ℤ) :
    ‖farDistanceSeq n‖ ^ 2 = ∑' k : ℤ, farDistance n k ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, farDistanceSeq_apply,
    Real.norm_eq_abs, sq_abs] using
    lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (farDistanceSeq n)

private lemma farDistanceSeq_sqnorm_le {n : ℤ} (hn : 5 ≤ n.natAbs) :
    ‖farDistanceSeq n‖ ^ 2 ≤ 5 / (n.natAbs : ℝ) := by
  rw [farDistanceSeq_sqnorm]
  exact farDistance_sq_sum_le hn

private lemma holder22 :
    (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
  rw [Real.holderConjugate_iff]
  norm_num

private lemma row_inner_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => row φ n l j k * farDistance n k) := by
  classical
  have h := lp.summable_mul holder22 (rowSeq φ n l j) (farDistanceSeq n)
  refine h.congr fun k => ?_
  change ‖row φ n l j k‖ * ‖farDistance n k‖ = _
  simp only [Real.norm_eq_abs, abs_of_nonneg (row_nonneg φ n l j k),
    abs_of_nonneg (farDistance_nonneg n k)]

private lemma row_inner_le (φ : PhysicalPairLp) (n l j : ℤ) :
    (∑' k : ℤ, row φ n l j k * farDistance n k) ≤
      ‖rowSeq φ n l j‖ * ‖farDistanceSeq n‖ := by
  have h := (lp.tsum_mul_le_mul_norm holder22
    (rowSeq φ n l j) (farDistanceSeq n)).2
  have he : (fun k : ℤ =>
      ‖rowSeq φ n l j k‖ * ‖farDistanceSeq n k‖) =
      fun k : ℤ => row φ n l j k * farDistance n k := by
    funext k
    simp only [rowSeq_apply, farDistanceSeq_apply, Real.norm_eq_abs,
      abs_of_nonneg (row_nonneg φ n l j k),
      abs_of_nonneg (farDistance_nonneg n k)]
  rw [he] at h
  exact h

private lemma row_inner_nonneg (φ : PhysicalPairLp) (n l j : ℤ) :
    0 ≤ ∑' k : ℤ, row φ n l j k * farDistance n k :=
  tsum_nonneg fun k => mul_nonneg (row_nonneg φ n l j k)
    (farDistance_nonneg n k)

private noncomputable def farInner (φ : PhysicalPairLp) (n l j : ℤ) : ℝ := by
  classical
  exact ∑' k : ℤ,
    if far n k then
      NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
        NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j
    else 0

private lemma farInner_sq_le {φ : PhysicalPairLp} {n l j : ℤ}
    (hn : 5 ≤ n.natAbs) :
    (∑' k : ℤ, row φ n l j k * farDistance n k) ^ 2 ≤
      (∑' k : ℤ, row φ n l j k ^ 2) * (5 / (n.natAbs : ℝ)) := by
  have hinner := row_inner_nonneg φ n l j
  have hle := row_inner_le φ n l j
  have hfar := farDistanceSeq_sqnorm_le hn
  calc
    (∑' k : ℤ, row φ n l j k * farDistance n k) ^ 2 ≤
        (‖rowSeq φ n l j‖ * ‖farDistanceSeq n‖) ^ 2 :=
      (sq_le_sq₀ hinner (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hle
    _ = ‖rowSeq φ n l j‖ ^ 2 * ‖farDistanceSeq n‖ ^ 2 := by ring
    _ ≤ (∑' k : ℤ, row φ n l j k ^ 2) * (5 / (n.natAbs : ℝ)) := by
      rw [rowSeq_sqnorm]
      exact mul_le_mul_of_nonneg_left hfar (by positivity)

private lemma inner_sum_factor (φ : PhysicalPairLp) (n l j : ℤ) :
    farInner φ n l j =
      d n j * (∑' k : ℤ, row φ n l j k * farDistance n k) := by
  classical
  have hterm (k : ℤ) :
      (if far n k then
        NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
          NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j
      else 0) = d n j * (row φ n l j k * farDistance n k) := by
    rw [source_kernel_product]
    by_cases h : far n k
    · simp [h, row, farDistance]
      ring
    · simp [h, row, farDistance]
  have hmasked : Summable (fun k : ℤ =>
      if far n k then
        NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
          NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j
      else 0) :=
    ((row_inner_summable φ n l j).mul_left (d n j)).congr
      (fun k => (hterm k).symm)
  calc
    _ = ∑' k : ℤ, d n j * (row φ n l j k * farDistance n k) :=
      tsum_congr hterm
    _ = _ := (row_inner_summable φ n l j).tsum_mul_left (d n j)

private lemma column_energy_le {φ : PhysicalPairLp} {n j : ℤ}
    (hn : 5 ≤ n.natAbs) :
    (∑' l : ℤ, ENNReal.ofReal (farInner φ n l j ^ 2)) ≤
      ENNReal.ofReal
        (d n j ^ 2 * (5 / (n.natAbs : ℝ)) * A φ ^ 4) := by
  have hpoint (l : ℤ) :
      ENNReal.ofReal (farInner φ n l j ^ 2) ≤
        ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ))) *
          (∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) := by
    have hreal :
        (d n j * (∑' k : ℤ, row φ n l j k * farDistance n k)) ^ 2 ≤
          (d n j ^ 2 * (5 / (n.natAbs : ℝ))) *
            (∑' k : ℤ, row φ n l j k ^ 2) := by
      calc
        _ = d n j ^ 2 *
            (∑' k : ℤ, row φ n l j k * farDistance n k) ^ 2 := by ring
        _ ≤ d n j ^ 2 *
            ((∑' k : ℤ, row φ n l j k ^ 2) *
              (5 / (n.natAbs : ℝ))) :=
          mul_le_mul_of_nonneg_left (farInner_sq_le hn) (sq_nonneg _)
        _ = _ := by ring
    calc
      ENNReal.ofReal (farInner φ n l j ^ 2) ≤
          ENNReal.ofReal
            (d n j ^ 2 * (5 / (n.natAbs : ℝ)) *
              (∑' k : ℤ, row φ n l j k ^ 2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [inner_sum_factor]
        simpa [mul_assoc] using hreal
      _ = ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ))) *
          (∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
          (row_sq_summable φ n l j)]
  calc
    (∑' l : ℤ, ENNReal.ofReal (farInner φ n l j ^ 2)) ≤
        ∑' l : ℤ, ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ))) *
          (∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) :=
      ENNReal.tsum_le_tsum hpoint
    _ = ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ))) *
        (∑' l : ℤ, ∑' k : ℤ, ENNReal.ofReal (row φ n l j k ^ 2)) :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ))) *
        ENNReal.ofReal (A φ ^ 4) := by
      gcongr
      exact row_energy_le φ n j
    _ = ENNReal.ofReal
        (d n j ^ 2 * (5 / (n.natAbs : ℝ)) * A φ ^ 4) := by
      rw [← ENNReal.ofReal_mul' (by positivity)]

theorem hs_far_intermediate_le (φ : PhysicalPairLp) (n : ℤ)
    (hn : 5 ≤ n.natAbs) :
    hsSigma2 φ n ≤
      ENNReal.ofReal (20 * ‖majorantSequence φ‖ ^ 4 / (n.natAbs : ℝ)) := by
  classical
  have houter : hsSigma2 φ n ≤
      ∑' j : ℤ,
        ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ)) * A φ ^ 4) := by
    unfold hsSigma2
    apply ENNReal.tsum_le_tsum
    intro j
    calc
      (∑' l : ℤ, ENNReal.ofReal
          ((∑' k : ℤ,
            if (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ) then
              NlsGge.Atomic.KST007.positiveKernel φ n false l (-k) *
                NlsGge.Atomic.KST007.positiveKernel φ n true (-k) j
            else 0) ^ 2)) =
          ∑' l : ℤ, ENNReal.ofReal (farInner φ n l j ^ 2) := by
        congr 1
      _ ≤ ENNReal.ofReal
          (d n j ^ 2 * (5 / (n.natAbs : ℝ)) * A φ ^ 4) :=
        column_energy_le hn
  have hd :
      (∑' j : ℤ, ENNReal.ofReal (d n j ^ 2)) ≤ ENNReal.ofReal 4 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _)
      (d_sq_summable n)]
    exact ENNReal.ofReal_le_ofReal (d_sq_sum_le n)
  calc
    hsSigma2 φ n ≤
        ∑' j : ℤ,
          ENNReal.ofReal (d n j ^ 2 * (5 / (n.natAbs : ℝ)) * A φ ^ 4) := houter
    _ = (∑' j : ℤ, ENNReal.ofReal (d n j ^ 2)) *
        ENNReal.ofReal (5 / (n.natAbs : ℝ) * A φ ^ 4) := by
      calc
        _ = ∑' j : ℤ,
            ENNReal.ofReal (d n j ^ 2) *
              ENNReal.ofReal (5 / (n.natAbs : ℝ) * A φ ^ 4) := by
          congr 1
          funext j
          rw [show d n j ^ 2 * (5 / (n.natAbs : ℝ)) * A φ ^ 4 =
              d n j ^ 2 * ((5 / (n.natAbs : ℝ)) * A φ ^ 4) by ring]
          rw [ENNReal.ofReal_mul (sq_nonneg _)]
        _ = _ := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal 4 *
        ENNReal.ofReal (5 / (n.natAbs : ℝ) * A φ ^ 4) := by
      gcongr
    _ = ENNReal.ofReal
        (4 * (5 / (n.natAbs : ℝ) * A φ ^ 4)) := by
      rw [← ENNReal.ofReal_mul' (by positivity)]
    _ = ENNReal.ofReal
        (20 * ‖majorantSequence φ‖ ^ 4 / (n.natAbs : ℝ)) := by
      congr 1
      dsimp [A]
      field_simp
      ; ring

end NlsGge.Atomic.KST009
