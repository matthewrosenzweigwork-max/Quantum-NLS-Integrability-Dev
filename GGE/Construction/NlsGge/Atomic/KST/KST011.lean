import NlsGge.Atomic.KST.KST008
import NlsGge.Atomic.KST.KST009
import NlsGge.Atomic.KST.KST010

/-! # KST Lemma 2.2: decay of the actual square

The signed source matrix is partitioned before applying the lp2 triangle
inequality. All real inner series have genuine summability witnesses; finite
nonnegative matrix energy precedes real norms and Hilbert--Schmidt transfer.
-/
set_option autoImplicit false
noncomputable section
open scoped ENNReal InnerProduct InnerProductSpace
open NlsGge.Pilot NlsGge.Schur NlsGge.Atomic.KST002 NlsGge.Atomic.KST004
  NlsGge.Atomic.KST007

namespace NlsGge.Atomic.KST011

private abbrev A (φ : PhysicalPairLp) : ℝ := ‖majorantSequence φ‖
private abbrev T (φ : PhysicalPairLp) (n : ℤ) : ℝ := ‖KST010.fourierTail φ n‖
private abbrev Far (n k : ℤ) : Prop :=
  (n.natAbs : ℝ) / 2 < ((k - n).natAbs : ℝ)
private abbrev Near (n k : ℤ) : Prop :=
  (1 : ℝ) ≤ ((k - n).natAbs : ℝ) ∧
    ((k - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2

private def raw (φ : PhysicalPairLp) (n l j k : ℤ) : ℝ :=
  positiveKernel φ n false l (-k) * positiveKernel φ n true (-k) j

private lemma distance_nonneg (n k : ℤ) : 0 ≤ reciprocalDistance n k := by
  unfold reciprocalDistance
  split_ifs
  · exact le_rfl
  · positivity

private lemma kernel_nonneg (φ : PhysicalPairLp) (n : ℤ) (upper : Bool) (l j : ℤ) :
    0 ≤ positiveKernel φ n upper l j :=
  mul_nonneg (majorant_nonneg φ _) (distance_nonneg n _)

private lemma raw_nonneg (φ : PhysicalPairLp) (n l j k : ℤ) : 0 ≤ raw φ n l j k :=
  mul_nonneg (kernel_nonneg φ n false l (-k)) (kernel_nonneg φ n true (-k) j)

private lemma raw_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (raw φ n l j) := by
  change Summable (fun k : ℤ =>
    positiveKernel φ n false l (-k) * positiveKernel φ n true (-k) j)
  simpa only [Function.comp_def, Equiv.neg_apply, Bool.not_false] using
    (Equiv.neg ℤ).summable_iff.mpr (positiveProductKernel_summable φ n false l j)

private lemma product_eq_raw_sum (φ : PhysicalPairLp) (n l j : ℤ) :
    positiveProductKernel φ n false l j = ∑' k : ℤ, raw φ n l j k := by
  have h := (Equiv.neg ℤ).tsum_eq (fun q : ℤ =>
    positiveKernel φ n false l q * positiveKernel φ n true q j)
  simpa only [positiveProductKernel, Bool.not_false, raw, Equiv.neg_apply] using h.symm

private def farSum (φ : PhysicalPairLp) (n l j : ℤ) : ℝ :=
  ∑' k : ℤ, if Far n k then raw φ n l j k else 0

private def nearSum (φ : PhysicalPairLp) (n l j : ℤ) : ℝ :=
  ∑' k : ℤ, if Near n k then raw φ n l j k else 0

private lemma far_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => if Far n k then raw φ n l j k else 0) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (raw_summable φ n l j)
  · split_ifs
    · exact raw_nonneg φ n l j k
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact raw_nonneg φ n l j k

private lemma near_summable (φ : PhysicalPairLp) (n l j : ℤ) :
    Summable (fun k : ℤ => if Near n k then raw φ n l j k else 0) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (raw_summable φ n l j)
  · split_ifs
    · exact raw_nonneg φ n l j k
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact raw_nonneg φ n l j k

private lemma raw_k_resonance (φ : PhysicalPairLp) (n l j : ℤ) : raw φ n l j n = 0 := by
  simp [raw, positiveKernel, reciprocalDistance]

private lemma raw_j_resonance (φ : PhysicalPairLp) (n l k : ℤ) : raw φ n l n k = 0 := by
  simp [raw, positiveKernel, reciprocalDistance]

private lemma distance_one_le (n k : ℤ) (hk : k ≠ n) :
    (1 : ℝ) ≤ ((k - n).natAbs : ℝ) := by
  have hpos := Int.natAbs_pos.mpr (sub_ne_zero.mpr hk)
  exact_mod_cast (Nat.succ_le_of_lt hpos)

private lemma raw_partition (φ : PhysicalPairLp) (n l j k : ℤ) :
    raw φ n l j k = (if Far n k then raw φ n l j k else 0) +
      (if Near n k then raw φ n l j k else 0) := by
  by_cases hk : k = n
  · subst k
    simp [raw_k_resonance]
  · by_cases hf : Far n k
    · have hn : ¬ Near n k := fun h => (not_lt_of_ge h.2) hf
      simp only [if_pos hf, if_neg hn, add_zero]
    · have hn : Near n k := ⟨distance_one_le n k hk, le_of_not_gt hf⟩
      simp only [if_neg hf, if_pos hn, zero_add]

private lemma product_eq_far_add_near (φ : PhysicalPairLp) (n l j : ℤ) :
    positiveProductKernel φ n false l j = farSum φ n l j + nearSum φ n l j := by
  rw [product_eq_raw_sum]
  calc
    _ = ∑' k : ℤ, ((if Far n k then raw φ n l j k else 0) +
        (if Near n k then raw φ n l j k else 0)) := tsum_congr (raw_partition φ n l j)
    _ = _ := (far_summable φ n l j).tsum_add (near_summable φ n l j)

private lemma product_j_resonance (φ : PhysicalPairLp) (n l : ℤ) :
    positiveProductKernel φ n false l n = 0 := by
  rw [product_eq_raw_sum]
  simp only [raw_j_resonance, tsum_zero]

private lemma farSum_j_resonance (φ : PhysicalPairLp) (n l : ℤ) : farSum φ n l n = 0 := by
  simp only [farSum, raw_j_resonance, ite_self, tsum_zero]

private lemma nearSum_j_resonance (φ : PhysicalPairLp) (n l : ℤ) : nearSum φ n l n = 0 := by
  simp only [nearSum, raw_j_resonance, ite_self, tsum_zero]

private def farMatrix (φ : PhysicalPairLp) (n : ℤ) (p : ℤ × ℤ) : ℝ :=
  if Far n p.1 then positiveProductKernel φ n false p.2 p.1 else farSum φ n p.2 p.1

private def nearMatrix (φ : PhysicalPairLp) (n : ℤ) (p : ℤ × ℤ) : ℝ :=
  if Near n p.1 then nearSum φ n p.2 p.1 else 0

private lemma matrix_partition (φ : PhysicalPairLp) (n j l : ℤ) :
    positiveProductKernel φ n false l j = farMatrix φ n (j, l) + nearMatrix φ n (j, l) := by
  by_cases hj : j = n
  · subst j
    simp only [farMatrix, nearMatrix, Prod.fst, Prod.snd, product_j_resonance,
      farSum_j_resonance, nearSum_j_resonance, ite_self, add_zero]
  · by_cases hf : Far n j
    · have hn : ¬ Near n j := fun h => (not_lt_of_ge h.2) hf
      simp only [farMatrix, nearMatrix, Prod.fst, Prod.snd, if_pos hf, if_neg hn, add_zero]
    · have hn : Near n j := ⟨distance_one_le n j hj, le_of_not_gt hf⟩
      simp only [farMatrix, nearMatrix, Prod.fst, Prod.snd, if_neg hf, if_pos hn]
      exact product_eq_far_add_near φ n l j

private lemma far_matrix_energy_le (φ : PhysicalPairLp) (n : ℤ) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (farMatrix φ n p ^ 2)) ≤
      KST008.hsSigma1 φ n + KST009.hsSigma2 φ n := by
  calc
    _ ≤ ∑' p : ℤ × ℤ,
        ((if Far n p.1 then ENNReal.ofReal (positiveProductKernel φ n false p.2 p.1 ^ 2)
          else 0) + ENNReal.ofReal (farSum φ n p.2 p.1 ^ 2)) := by
      apply ENNReal.tsum_le_tsum
      intro p
      by_cases hp : Far n p.1
      · simp only [farMatrix, if_pos hp]
        exact le_add_right le_rfl
      · simp only [farMatrix, if_neg hp, zero_add, le_refl]
    _ = (∑' p : ℤ × ℤ,
        if Far n p.1 then ENNReal.ofReal (positiveProductKernel φ n false p.2 p.1 ^ 2)
          else 0) + ∑' p : ℤ × ℤ, ENNReal.ofReal (farSum φ n p.2 p.1 ^ 2) :=
      ENNReal.tsum_add
    _ = _ := by
      rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
      congr 1
      · change (∑' j : ℤ, ∑' l : ℤ, if Far n j then
            ENNReal.ofReal (positiveProductKernel φ n false l j ^ 2) else 0) =
          ∑' j : ℤ, if Far n j then
            ∑' l : ℤ, ENNReal.ofReal (positiveProductKernel φ n false l j ^ 2) else 0
        apply tsum_congr
        intro j
        by_cases hj : Far n j
        · simp only [if_pos hj]
        · simp only [if_neg hj, tsum_zero]

private lemma near_matrix_energy_eq (φ : PhysicalPairLp) (n : ℤ) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (nearMatrix φ n p ^ 2)) = KST010.hsSigma3 φ n := by
  rw [ENNReal.tsum_prod']
  change (∑' j : ℤ, ∑' l : ℤ,
    ENNReal.ofReal ((if Near n j then nearSum φ n l j else 0) ^ 2)) =
      ∑' j : ℤ, if Near n j then ∑' l : ℤ, ENNReal.ofReal (nearSum φ n l j ^ 2) else 0
  apply tsum_congr
  intro j
  by_cases hj : Near n j
  · simp only [if_pos hj]
  · simp only [if_neg hj, zero_pow (by decide : 2 ≠ 0), ENNReal.ofReal_zero, tsum_zero]

private lemma far_matrix_energy_bound (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (farMatrix φ n p ^ 2)) ≤
      ENNReal.ofReal (40 * A φ ^ 4 / (n.natAbs : ℝ)) := by
  have hc : 0 ≤ 20 * A φ ^ 4 / (n.natAbs : ℝ) := by positivity
  calc
    _ ≤ KST008.hsSigma1 φ n + KST009.hsSigma2 φ n := far_matrix_energy_le φ n
    _ ≤ ENNReal.ofReal (20 * A φ ^ 4 / (n.natAbs : ℝ)) +
        ENNReal.ofReal (20 * A φ ^ 4 / (n.natAbs : ℝ)) :=
      add_le_add (KST008.hs_far_output_le φ n hn) (KST009.hs_far_intermediate_le φ n hn)
    _ = _ := by rw [← ENNReal.ofReal_add hc hc]; congr 1; ring

private lemma near_matrix_energy_bound (φ : PhysicalPairLp) (n : ℤ) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (nearMatrix φ n p ^ 2)) ≤
      ENNReal.ofReal (16 * A φ ^ 2 * T φ n ^ 2) := by
  rw [near_matrix_energy_eq]
  exact KST010.hs_near_near_le φ n

private lemma far_matrix_sq_summable (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    Summable (fun p : ℤ × ℤ => farMatrix φ n p ^ 2) := by
  have hf : (∑' p : ℤ × ℤ, ENNReal.ofReal (farMatrix φ n p ^ 2)) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (far_matrix_energy_bound φ n hn) ENNReal.ofReal_lt_top)
  exact (ENNReal.summable_toReal hf).congr
    (fun p => ENNReal.toReal_ofReal (sq_nonneg (farMatrix φ n p)))

private lemma near_matrix_sq_summable (φ : PhysicalPairLp) (n : ℤ) :
    Summable (fun p : ℤ × ℤ => nearMatrix φ n p ^ 2) := by
  have hf : (∑' p : ℤ × ℤ, ENNReal.ofReal (nearMatrix φ n p ^ 2)) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (near_matrix_energy_bound φ n) ENNReal.ofReal_lt_top)
  exact (ENNReal.summable_toReal hf).congr
    (fun p => ENNReal.toReal_ofReal (sq_nonneg (nearMatrix φ n p)))

private def farVector (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    lp (fun _ : ℤ × ℤ => ℝ) 2 :=
  ⟨farMatrix φ n, memℓp_gen ((far_matrix_sq_summable φ n hn).congr fun p => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])⟩

private def nearVector (φ : PhysicalPairLp) (n : ℤ) : lp (fun _ : ℤ × ℤ => ℝ) 2 :=
  ⟨nearMatrix φ n, memℓp_gen ((near_matrix_sq_summable φ n).congr fun p => by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs])⟩

private lemma farVector_apply (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) (p : ℤ × ℤ) :
    farVector φ n hn p = farMatrix φ n p := rfl

private lemma nearVector_apply (φ : PhysicalPairLp) (n : ℤ) (p : ℤ × ℤ) :
    nearVector φ n p = nearMatrix φ n p := rfl

private lemma far_energy_eq_vector (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    ENNReal.ofReal (‖farVector φ n hn‖ ^ 2) =
      ∑' p : ℤ × ℤ, ENNReal.ofReal (farMatrix φ n p ^ 2) := by
  have he : ‖farVector φ n hn‖ ^ 2 = ∑' p : ℤ × ℤ, farMatrix φ n p ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, farVector_apply, Real.norm_eq_abs, sq_abs] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (farVector φ n hn)
  rw [he]
  exact ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) (far_matrix_sq_summable φ n hn)

private lemma near_energy_eq_vector (φ : PhysicalPairLp) (n : ℤ) :
    ENNReal.ofReal (‖nearVector φ n‖ ^ 2) =
      ∑' p : ℤ × ℤ, ENNReal.ofReal (nearMatrix φ n p ^ 2) := by
  have he : ‖nearVector φ n‖ ^ 2 = ∑' p : ℤ × ℤ, nearMatrix φ n p ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, nearVector_apply, Real.norm_eq_abs, sq_abs] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (nearVector φ n)
  rw [he]
  exact ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) (near_matrix_sq_summable φ n)

private lemma far_vector_sq_le (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    ‖farVector φ n hn‖ ^ 2 ≤ 40 * A φ ^ 4 / (n.natAbs : ℝ) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (far_matrix_energy_bound φ n hn)
  rw [← far_energy_eq_vector φ n hn, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at h
  exact h

private lemma near_vector_sq_le (φ : PhysicalPairLp) (n : ℤ) :
    ‖nearVector φ n‖ ^ 2 ≤ 16 * A φ ^ 2 * T φ n ^ 2 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (near_matrix_energy_bound φ n)
  rw [← near_energy_eq_vector φ n, ENNReal.toReal_ofReal (sq_nonneg _),
    ENNReal.toReal_ofReal (by positivity)] at h
  exact h

private lemma far_vector_norm_le (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    ‖farVector φ n hn‖ ≤ 7 * A φ ^ 2 / Real.sqrt (n.natAbs : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤
    7 * A φ ^ 2 / Real.sqrt (n.natAbs : ℝ))).mp
  calc
    _ ≤ 40 * A φ ^ 4 / (n.natAbs : ℝ) := far_vector_sq_le φ n hn
    _ ≤ 49 * A φ ^ 4 / (n.natAbs : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg (norm_nonneg _) 4))
        (Nat.cast_nonneg _)
    _ = _ := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring

private lemma near_vector_norm_le (φ : PhysicalPairLp) (n : ℤ) :
    ‖nearVector φ n‖ ≤ 4 * A φ * T φ n := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 4 * A φ * T φ n)).mp
  calc
    _ ≤ 16 * A φ ^ 2 * T φ n ^ 2 := near_vector_sq_le φ n
    _ = _ := by ring

private def matrixVector (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    lp (fun _ : ℤ × ℤ => ℝ) 2 := farVector φ n hn + nearVector φ n

private lemma matrixVector_apply (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) (p : ℤ × ℤ) :
    matrixVector φ n hn p = positiveProductKernel φ n false p.2 p.1 := by
  change farMatrix φ n p + nearMatrix φ n p = _
  exact (matrix_partition φ n p.1 p.2).symm

private lemma matrix_vector_norm_le (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    ‖matrixVector φ n hn‖ ≤
      7 * A φ * (A φ / Real.sqrt (n.natAbs : ℝ) + T φ n) := by
  have hAT : 0 ≤ A φ * T φ n := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  calc
    _ ≤ ‖farVector φ n hn‖ + ‖nearVector φ n‖ := norm_add_le _ _
    _ ≤ 7 * A φ ^ 2 / Real.sqrt (n.natAbs : ℝ) + 4 * A φ * T φ n :=
      add_le_add (far_vector_norm_le φ n hn) (near_vector_norm_le φ n)
    _ ≤ 7 * A φ ^ 2 / Real.sqrt (n.natAbs : ℝ) + 7 * A φ * T φ n := by nlinarith
    _ = _ := by ring

private def scalarBasis : HilbertBasis ℤ ℂ SpectralScalarL2 :=
  fourierBasis (T := (2 : ℝ))

private lemma scalarBasis_apply (k : ℤ) : scalarBasis k = spectralBasis k := by
  exact congrFun (coe_fourierBasis (T := (2 : ℝ))) k

private lemma scalarBasis_repr (f : SpectralScalarL2) (k : ℤ) :
    scalarBasis.repr f k = spectralCoeff f k := rfl

private lemma positive_energy_matrix (φ : PhysicalPairLp) (n : ℤ) :
    complexHilbertSchmidtEnergy
      ((positiveBlock φ n false).comp (positiveBlock φ n true)) =
      ∑' p : ℤ × ℤ, ENNReal.ofReal (positiveProductKernel φ n false p.2 p.1 ^ 2) := by
  rw [complexHilbertSchmidtEnergy_eq_matrix _ scalarBasis scalarBasis, ENNReal.tsum_prod']
  apply tsum_congr
  intro j
  apply tsum_congr
  intro l
  rw [← scalarBasis.repr_apply_apply]
  simp only [scalarBasis_repr, scalarBasis_apply]
  have hmatrix := positiveProduct_matrix φ n false l j
  simp only [Bool.not_false] at hmatrix
  rw [hmatrix, Complex.norm_real, Real.norm_eq_abs, sq_abs]

private lemma matrix_energy_eq_norm (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    (∑' p : ℤ × ℤ, ENNReal.ofReal (positiveProductKernel φ n false p.2 p.1 ^ 2)) =
      ENNReal.ofReal (‖matrixVector φ n hn‖ ^ 2) := by
  have hs : Summable (fun p : ℤ × ℤ => positiveProductKernel φ n false p.2 p.1 ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, matrixVector_apply,
      Real.norm_eq_abs, sq_abs] using (lp.memℓp (matrixVector φ n hn)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have he : ‖matrixVector φ n hn‖ ^ 2 =
      ∑' p : ℤ × ℤ, positiveProductKernel φ n false p.2 p.1 ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, matrixVector_apply,
      Real.norm_eq_abs, sq_abs] using
      lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (matrixVector φ n hn)
  rw [he]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun p => sq_nonneg _) hs).symm

private lemma positive_false_energy_le (φ : PhysicalPairLp) (n : ℤ) (hn : 5 ≤ n.natAbs) :
    complexHilbertSchmidtEnergy
      ((positiveBlock φ n false).comp (positiveBlock φ n true)) ≤
      ENNReal.ofReal ((7 * A φ * (A φ / Real.sqrt (n.natAbs : ℝ) + T φ n)) ^ 2) := by
  rw [positive_energy_matrix, matrix_energy_eq_norm φ n hn]
  apply ENNReal.ofReal_le_ofReal
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (matrix_vector_norm_le φ n hn)

private lemma center_mem_strip (n : ℤ) :
    ((n : ℂ) * (Real.pi : ℂ)) ∈ spectralStrip n := by
  change |(((n : ℂ) * (Real.pi : ℂ)).re - (n : ℝ) * Real.pi)| ≤ Real.pi / 2
  simpa only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, sub_self, abs_zero] using
    (div_nonneg Real.pi_pos.le (by norm_num : (0 : ℝ) ≤ 2))

theorem positive_product_hs_decay
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ)
    (hn : 5 ≤ n.natAbs) (upper : Bool) :
    NlsGge.Pilot.IsComplexHilbertSchmidt
        ((NlsGge.Atomic.KST007.positiveBlock φ n upper).comp
          (NlsGge.Atomic.KST007.positiveBlock φ n (!upper))) ∧
      NlsGge.Pilot.complexHilbertSchmidtNorm
          ((NlsGge.Atomic.KST007.positiveBlock φ n upper).comp
            (NlsGge.Atomic.KST007.positiveBlock φ n (!upper))) ≤
        7 * ‖NlsGge.Atomic.KST007.majorantSequence φ‖ *
          (‖NlsGge.Atomic.KST007.majorantSequence φ‖ /
              Real.sqrt (n.natAbs : ℝ) +
            ‖NlsGge.Atomic.KST010.fourierTail φ n‖) := by
  have he := positive_false_energy_le φ n hn
  have hfalse := complexHilbertSchmidtNorm_le_of_energy_le (by positivity) he
  have hfinite := (blockProduct_hs_comparison φ n
    ((n : ℂ) * (Real.pi : ℂ)) (center_mem_strip n) upper).1
  refine ⟨hfinite, ?_⟩
  cases upper
  · simpa only [Bool.not_false] using hfalse
  · simpa only [Bool.not_true] using (positiveProduct_hsNorm_eq φ n).symm.le.trans hfalse

theorem qOperator_sq_hs_decay
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) (n : ℤ)
    (hn : 5 ≤ n.natAbs) (z : ℂ)
    (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n) :
    NlsGge.Pilot.IsComplexHilbertSchmidt
        ((NlsGge.Atomic.KST006.qOperator φ n z hz).comp
          (NlsGge.Atomic.KST006.qOperator φ n z hz)) ∧
      NlsGge.Pilot.complexHilbertSchmidtNorm
          ((NlsGge.Atomic.KST006.qOperator φ n z hz).comp
            (NlsGge.Atomic.KST006.qOperator φ n z hz)) ≤
        14 * ‖NlsGge.Atomic.KST007.majorantSequence φ‖ *
          (‖NlsGge.Atomic.KST007.majorantSequence φ‖ /
              Real.sqrt (n.natAbs : ℝ) +
            ‖NlsGge.Atomic.KST010.fourierTail φ n‖) := by
  have h := qOperator_sq_hs_majorant φ n z hz
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ 2 * complexHilbertSchmidtNorm
        ((positiveBlock φ n false).comp (positiveBlock φ n true)) := h.2
    _ ≤ 2 * (7 * A φ * (A φ / Real.sqrt (n.natAbs : ℝ) + T φ n)) := by
      exact mul_le_mul_of_nonneg_left (positive_product_hs_decay φ n hn false).2 (by norm_num)
    _ = _ := by ring

private lemma tail_small (φ : PhysicalPairLp) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℤ, N ≤ n.natAbs → T φ n ≤ η := by
  have hsum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (majorantSequence φ)
  obtain ⟨s, hs⟩ := (Metric.tendsto_atTop.mp hsum) η hη
  refine ⟨s.sup Int.natAbs + 1, ?_⟩
  intro n hn
  have hres : ‖majorantSequence φ - ∑ k ∈ s, lp.single 2 k (majorantSequence φ k)‖ < η := by
    simpa only [dist_eq_norm, norm_sub_rev] using hs s le_rfl
  apply le_trans ?_ hres.le
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  by_cases hk : n.natAbs ≤ k.natAbs
  · have hks : k ∉ s := by
      intro hmem
      have hb : k.natAbs ≤ s.sup Int.natAbs := Finset.le_sup hmem
      omega
    simp only [KST010.fourierTail, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum,
      Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single, if_pos hk,
      if_neg hks, sub_zero, le_refl]
  · simp only [KST010.fourierTail, if_neg hk, norm_zero]
    exact norm_nonneg _

private lemma potentialCoeff_sub (ψ φ : PhysicalPairLp) (b : Bool) (k : ℤ) :
    potentialCoeff (ψ - φ) b k = potentialCoeff ψ b k - potentialCoeff φ b k := by
  calc
    _ = (fourierBasis (T := (2 : ℝ))).repr
        (NlsGge.Analysis.naturalPhysicalCoverL2 ((ψ - φ) b)) k :=
      (fourierBasis_repr _ _).symm
    _ = (fourierBasis (T := (2 : ℝ))).repr
          (NlsGge.Analysis.naturalPhysicalCoverL2 (ψ b)) k -
        (fourierBasis (T := (2 : ℝ))).repr
          (NlsGge.Analysis.naturalPhysicalCoverL2 (φ b)) k := by
      simp only [PiLp.sub_apply, map_sub]
      exact congrArg (fun u : lp (fun _ : ℤ => ℂ) 2 => u k)
        ((fourierBasis (T := (2 : ℝ))).repr.map_sub _ _)
    _ = _ := congrArg₂ (fun x y : ℂ => x - y)
      (fourierBasis_repr _ _) (fourierBasis_repr _ _)

private lemma coefficient_norm_diff (ψ φ : PhysicalPairLp) (b : Bool) (k : ℤ) :
    |‖potentialCoeff ψ b k‖ - ‖potentialCoeff φ b k‖| ≤ majorantCoeff (ψ - φ) k := by
  calc
    _ ≤ ‖potentialCoeff ψ b k - potentialCoeff φ b k‖ := abs_norm_sub_norm_le _ _
    _ = ‖potentialCoeff (ψ - φ) b k‖ := by rw [potentialCoeff_sub]
    _ ≤ _ := potentialCoeff_norm_le_majorant (ψ - φ) b k

private lemma majorant_point_diff (ψ φ : PhysicalPairLp) (k : ℤ) :
    |majorantCoeff ψ k - majorantCoeff φ k| ≤ majorantCoeff (ψ - φ) k := by
  have h (χ : PhysicalPairLp) (b : Bool) :
      ‖potentialCoeff χ b (-k)‖ ≤ majorantCoeff χ k := by
    exact (potentialCoeff_norm_le_majorant χ b (-k)).trans_eq (majorant_even χ k)
  have hu := abs_le.mp (coefficient_norm_diff ψ φ true k)
  have hu' := abs_le.mp (coefficient_norm_diff ψ φ true (-k))
  have hl := abs_le.mp (coefficient_norm_diff ψ φ false k)
  have hl' := abs_le.mp (coefficient_norm_diff ψ φ false (-k))
  rw [majorant_even (ψ - φ) k] at hu' hl'
  have hup : majorantCoeff ψ k ≤ majorantCoeff φ k + majorantCoeff (ψ - φ) k := by
    apply max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · linarith [potentialCoeff_norm_le_majorant φ true k]
    · linarith [h φ true]
    · linarith [potentialCoeff_norm_le_majorant φ false k]
    · linarith [h φ false]
  have hdown : majorantCoeff φ k ≤ majorantCoeff ψ k + majorantCoeff (ψ - φ) k := by
    apply max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · linarith [potentialCoeff_norm_le_majorant ψ true k]
    · linarith [h ψ true]
    · linarith [potentialCoeff_norm_le_majorant ψ false k]
    · linarith [h ψ false]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma majorant_norm_diff (ψ φ : PhysicalPairLp) :
    ‖majorantSequence ψ - majorantSequence φ‖ ≤ 2 * ‖ψ - φ‖ := by
  calc
    _ ≤ ‖majorantSequence (ψ - φ)‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro k
      simpa only [lp.coeFn_sub, Pi.sub_apply, majorantSequence_apply, Real.norm_eq_abs,
        abs_of_nonneg (majorant_nonneg (ψ - φ) k)] using majorant_point_diff ψ φ k
    _ ≤ _ := (majorant_norm_bounds (ψ - φ)).2

private lemma tail_norm_diff (ψ φ : PhysicalPairLp) (n : ℤ) :
    ‖KST010.fourierTail ψ n - KST010.fourierTail φ n‖ ≤ 2 * ‖ψ - φ‖ := by
  apply le_trans ?_ (majorant_norm_diff ψ φ)
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro k
  by_cases hk : n.natAbs ≤ k.natAbs
  · simp only [KST010.fourierTail, lp.coeFn_sub, Pi.sub_apply, if_pos hk, le_refl]
  · simp only [KST010.fourierTail, lp.coeFn_sub, Pi.sub_apply, if_neg hk, sub_self, norm_zero]
    exact norm_nonneg _

private lemma majorant_norm_perturb (ψ φ : PhysicalPairLp) :
    A ψ ≤ A φ + 2 * ‖ψ - φ‖ := by
  have h := norm_sub_norm_le (majorantSequence ψ) (majorantSequence φ)
  have hd := majorant_norm_diff ψ φ
  change ‖majorantSequence ψ‖ ≤ ‖majorantSequence φ‖ + _
  linarith

private lemma tail_norm_perturb (ψ φ : PhysicalPairLp) (n : ℤ) :
    T ψ n ≤ T φ n + 2 * ‖ψ - φ‖ := by
  have h := norm_sub_norm_le (KST010.fourierTail ψ n) (KST010.fourierTail φ n)
  have hd := tail_norm_diff ψ φ n
  change ‖KST010.fourierTail ψ n‖ ≤ ‖KST010.fourierTail φ n‖ + _
  linarith

theorem hs_qOperator_sq_decay
    (φ : NlsGge.Atomic.KST002.PhysicalPairLp) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N₀ : ℕ, 5 ≤ N₀ ∧
      ∀ ψ : NlsGge.Atomic.KST002.PhysicalPairLp, ‖ψ - φ‖ < ε →
        ∀ n : ℤ, N₀ ≤ n.natAbs →
          (∀ upper : Bool,
            NlsGge.Pilot.IsComplexHilbertSchmidt
                ((NlsGge.Atomic.KST007.positiveBlock ψ n upper).comp
                  (NlsGge.Atomic.KST007.positiveBlock ψ n (!upper))) ∧
              NlsGge.Pilot.complexHilbertSchmidtNorm
                  ((NlsGge.Atomic.KST007.positiveBlock ψ n upper).comp
                    (NlsGge.Atomic.KST007.positiveBlock ψ n (!upper))) ≤
                (1 / 4 : ℝ)) ∧
          (∀ (z : ℂ) (hz : z ∈ NlsGge.Atomic.KST004.spectralStrip n),
            NlsGge.Pilot.IsComplexHilbertSchmidt
                ((NlsGge.Atomic.KST006.qOperator ψ n z hz).comp
                  (NlsGge.Atomic.KST006.qOperator ψ n z hz)) ∧
              NlsGge.Pilot.complexHilbertSchmidtNorm
                  ((NlsGge.Atomic.KST006.qOperator ψ n z hz).comp
                    (NlsGge.Atomic.KST006.qOperator ψ n z hz)) ≤
                (1 / 2 : ℝ)) := by
  let B : ℝ := A φ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let ε : ℝ := min (1 / 2) (1 / (168 * B))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨Ntail, htail⟩ := tail_small φ (1 / (84 * B)) (by positivity)
  obtain ⟨Nden, hNden⟩ := exists_nat_gt ((84 * B ^ 2) ^ 2)
  let N₀ : ℕ := max 5 (max Ntail Nden)
  refine ⟨ε, hε, N₀, le_max_left _ _, ?_⟩
  intro ψ hψ n hn
  have hn5 : 5 ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hntail : Ntail ≤ n.natAbs :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnden : Nden ≤ n.natAbs :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hNpos : (0 : ℝ) < (n.natAbs : ℝ) := by exact_mod_cast (by omega : 0 < n.natAbs)
  have hsqrt : 0 < Real.sqrt (n.natAbs : ℝ) := Real.sqrt_pos.2 hNpos
  have hscale : 84 * B ^ 2 ≤ Real.sqrt (n.natAbs : ℝ) := by
    apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hNpos.le]
    exact hNden.le.trans (by exact_mod_cast hnden)
  have hden : B / Real.sqrt (n.natAbs : ℝ) ≤ 1 / (84 * B) := by
    apply (div_le_div_iff₀ hsqrt (by positivity)).mpr
    nlinarith
  have hdist_half : ‖ψ - φ‖ ≤ 1 / 2 :=
    hψ.le.trans (min_le_left _ _)
  have hdist_small : 2 * ‖ψ - φ‖ ≤ 1 / (84 * B) := by
    calc
      _ ≤ 2 * (1 / (168 * B)) :=
        mul_le_mul_of_nonneg_left (hψ.le.trans (min_le_right _ _)) (by norm_num)
      _ = _ := by field_simp; ring
  have hAψ : A ψ ≤ B := by
    have h := majorant_norm_perturb ψ φ
    dsimp [B]
    linarith
  have hTψ : T ψ n ≤ 2 / (84 * B) := by
    calc
      _ ≤ T φ n + 2 * ‖ψ - φ‖ := tail_norm_perturb ψ φ n
      _ ≤ 1 / (84 * B) + 1 / (84 * B) := add_le_add (htail n hntail) hdist_small
      _ = _ := by ring
  have hdivψ : A ψ / Real.sqrt (n.natAbs : ℝ) ≤ 1 / (84 * B) :=
    (div_le_div_of_nonneg_right hAψ hsqrt.le).trans hden
  have hsum : A ψ / Real.sqrt (n.natAbs : ℝ) + T ψ n ≤ 3 / (84 * B) := by
    calc
      _ ≤ 1 / (84 * B) + 2 / (84 * B) := add_le_add hdivψ hTψ
      _ = _ := by ring
  have hbound : 7 * A ψ * (A ψ / Real.sqrt (n.natAbs : ℝ) + T ψ n) ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ 7 * B * (A ψ / Real.sqrt (n.natAbs : ℝ) + T ψ n) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAψ (by norm_num))
          (by positivity)
      _ ≤ 7 * B * (3 / (84 * B)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by field_simp; ring
  have hprod (upper : Bool) :
      IsComplexHilbertSchmidt
          ((positiveBlock ψ n upper).comp (positiveBlock ψ n (!upper))) ∧
        complexHilbertSchmidtNorm
          ((positiveBlock ψ n upper).comp (positiveBlock ψ n (!upper))) ≤ (1 / 4 : ℝ) := by
    have h := positive_product_hs_decay ψ n hn5 upper
    exact ⟨h.1, h.2.trans hbound⟩
  refine ⟨hprod, ?_⟩
  intro z hz
  have h := qOperator_sq_hs_majorant ψ n z hz
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ 2 * complexHilbertSchmidtNorm
        ((positiveBlock ψ n false).comp (positiveBlock ψ n true)) := h.2
    _ ≤ 2 * (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left (hprod false).2 (by norm_num)
    _ = _ := by norm_num

end NlsGge.Atomic.KST011
