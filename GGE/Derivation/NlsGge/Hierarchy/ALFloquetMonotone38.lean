import NlsGge.Hierarchy.ALTransferDefs38
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Batch 38, E07: elementary `J`-form monotonicity for the exterior Floquet branch
(`|z| > 1`).  Recorded proof-route departure from v2's unitary/CMV picture. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped Matrix

lemma alTransfer38_mulVec_zero (a z : ℂ) (v : Fin 2 → ℂ) :
    (alTransfer38 a z).mulVec v 0 = ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)⁻¹) * (z * v 0 + a * v 1) := by
  simp [alTransfer38, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

lemma alTransfer38_mulVec_one (a z : ℂ) (v : Fin 2 → ℂ) :
    (alTransfer38 a z).mulVec v 1 =
      ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)⁻¹) * (star a * v 0 + z⁻¹ * v 1) := by
  simp [alTransfer38, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- Core real identity. -/
lemma alJForm_core38 (a z u w : ℂ) :
    (‖z * u‖ ^ 2 - ‖star a * u + (1 - ‖a‖ ^ 2 : ℝ) * w‖ ^ 2)
      - (1 - ‖a‖ ^ 2) * (‖u - a * w‖ ^ 2 - ‖z * w‖ ^ 2)
    = (‖z‖ ^ 2 - 1) * (‖u‖ ^ 2 + (1 - ‖a‖ ^ 2) * ‖w‖ ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma alJForm_transfer38 (a z : ℂ) (ha : ‖a‖ < 1) (hz : z ≠ 0) (v : Fin 2 → ℂ) :
    alJForm38 ((alTransfer38 a z).mulVec v) - alJForm38 v =
      (‖z‖ ^ 2 - 1) / (1 - ‖a‖ ^ 2) *
        (‖v 0 + a * v 1 / z‖ ^ 2 + (1 - ‖a‖ ^ 2) * ‖v 1‖ ^ 2 / ‖z‖ ^ 2) := by
  have ht : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  set w : ℂ := v 1 / z with hw
  set u : ℂ := v 0 + a * w with hu
  have hv1 : v 1 = z * w := by rw [hw]; field_simp
  have hv0 : v 0 = u - a * w := by rw [hu]; ring
  have e0 : z * v 0 + a * v 1 = z * u := by rw [hv0, hv1]; ring
  have hzw : z⁻¹ * (z * w) = w := by field_simp
  have hsa : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  have e1 : star a * v 0 + z⁻¹ * v 1
      = star a * u + ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * w := by
    rw [hv0, hv1]
    push_cast at hsa ⊢
    linear_combination (-w) * hsa + hzw
  have hs : (Real.sqrt (1 - ‖a‖ ^ 2)) ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt ht.le
  have hs0 : 0 < Real.sqrt (1 - ‖a‖ ^ 2) := Real.sqrt_pos.mpr ht
  have hN : ∀ X : ℂ, ‖((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)⁻¹) * X‖ ^ 2 = ‖X‖ ^ 2 / (1 - ‖a‖ ^ 2) := by
    intro X
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hs0.le, mul_pow, inv_pow, hs]
    ring
  have hw' : v 0 + a * v 1 / z = u := by
    rw [hv1, hu]; field_simp
  have hc := alJForm_core38 a z u w
  have hv1n : ‖v 1‖ ^ 2 = ‖z‖ ^ 2 * ‖w‖ ^ 2 := by rw [hv1, norm_mul, mul_pow]
  have hv0n : ‖v 0‖ ^ 2 = ‖u - a * w‖ ^ 2 := by rw [hv0]
  unfold alJForm38
  rw [alTransfer38_mulVec_zero, alTransfer38_mulVec_one, e0, e1, hN, hN, hw', hv1n, hv0n]
  have hz2 : ‖z * w‖ ^ 2 = ‖z‖ ^ 2 * ‖w‖ ^ 2 := by rw [norm_mul, mul_pow]
  have hzu : ‖z * u‖ ^ 2 = ‖z‖ ^ 2 * ‖u‖ ^ 2 := by rw [norm_mul, mul_pow]
  rw [hz2, hzu] at hc
  rw [hzu]
  have hz0 : ‖z‖ ^ 2 ≠ 0 := by positivity
  have ht0 : (1 - ‖a‖ ^ 2) ≠ 0 := ht.ne'
  generalize ‖star a * u + ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) * w‖ ^ 2 = B at hc ⊢
  generalize ‖u - a * w‖ ^ 2 = C at hc ⊢
  generalize ‖z‖ ^ 2 = Z at hc hz0 ⊢
  generalize ‖w‖ ^ 2 = W at hc ⊢
  generalize ‖u‖ ^ 2 = U at hc ⊢
  generalize 1 - ‖a‖ ^ 2 = t at hc ht0 ⊢
  field_simp
  linear_combination hc

lemma alTransfer38_det (a z : ℂ) (ha : ‖a‖ < 1) (hz : z ≠ 0) :
    Matrix.det (alTransfer38 a z) = 1 := by
  have ht : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hs : (Real.sqrt (1 - ‖a‖ ^ 2)) ^ 2 = 1 - ‖a‖ ^ 2 := Real.sq_sqrt ht.le
  have hs0 : (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  have hsa : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj']; push_cast; ring
  have hsC : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ^ 2 = 1 - ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hs]; push_cast; ring
  unfold alTransfer38
  rw [Matrix.det_smul, Matrix.det_fin_two_of]
  simp only [Fintype.card_fin]
  rw [inv_pow, hsC, hsa]
  have : (1 - ((‖a‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by rw [← hsC]; exact pow_ne_zero 2 hs0
  field_simp [hz]

lemma alTransfer38_mulVec_ne_zero (a z : ℂ) (ha : ‖a‖ < 1) (hz : z ≠ 0) (v : Fin 2 → ℂ)
    (hv : v ≠ 0) : (alTransfer38 a z).mulVec v ≠ 0 := by
  intro h
  exact hv (Matrix.eq_zero_of_mulVec_eq_zero (by rw [alTransfer38_det a z ha hz]; exact one_ne_zero) h)

lemma alJForm_transfer_gt38 (a z : ℂ) (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) (v : Fin 2 → ℂ)
    (hv : v ≠ 0) : alJForm38 v < alJForm38 ((alTransfer38 a z).mulVec v) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have ht : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hzp : 0 < ‖z‖ ^ 2 - 1 := by nlinarith
  have hzn : 0 < ‖z‖ := by linarith
  have hid := alJForm_transfer38 a z ha hz0 v
  have hpos : 0 < ‖v 0 + a * v 1 / z‖ ^ 2 + (1 - ‖a‖ ^ 2) * ‖v 1‖ ^ 2 / ‖z‖ ^ 2 := by
    by_cases h1 : v 1 = 0
    · have h0 : v 0 ≠ 0 := by
        intro h0; apply hv; ext i; fin_cases i <;> simp [h0, h1]
      rw [h1]; simp
      exact pow_pos (norm_pos_iff.mpr h0) 2
    · have : 0 < ‖v 1‖ := norm_pos_iff.mpr h1
      have : 0 < (1 - ‖a‖ ^ 2) * ‖v 1‖ ^ 2 / ‖z‖ ^ 2 := by positivity
      nlinarith [sq_nonneg ‖v 0 + a * v 1 / z‖]
  have : 0 < alJForm38 ((alTransfer38 a z).mulVec v) - alJForm38 v := by
    rw [hid]; positivity
  linarith

lemma alPartial38_mulVec_succ {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) (k : ℕ) (v : Fin 2 → ℂ) :
    (alPartial38 α z (k + 1)).mulVec v =
      (alTransfer38 (α (k : ZMod L)) z).mulVec ((alPartial38 α z k).mulVec v) := by
  rw [alPartial38, Matrix.mulVec_mulVec]

lemma alPartial38_ne_zero_ge {L : ℕ} (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ)
    (hz : 1 < ‖z‖) (v : Fin 2 → ℂ) (hv : v ≠ 0) (k : ℕ) :
    (alPartial38 α z k).mulVec v ≠ 0 ∧
      alJForm38 v ≤ alJForm38 ((alPartial38 α z k).mulVec v) := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
  induction k with
  | zero => simp [alPartial38, hv]
  | succ k ih =>
    rw [alPartial38_mulVec_succ]
    exact ⟨alTransfer38_mulVec_ne_zero _ _ (hα _) hz0 _ ih.1,
      ih.2.trans (alJForm_transfer_gt38 _ _ (hα _) hz _ ih.1).le⟩

lemma alPartial38_ne_zero {L : ℕ} (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ)
    (hz : 1 < ‖z‖) (v : Fin 2 → ℂ) (hv : v ≠ 0) (k : ℕ) :
    (alPartial38 α z k).mulVec v ≠ 0 := (alPartial38_ne_zero_ge α hα z hz v hv k).1

lemma alJForm_partial_strict38 {L : ℕ} (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ)
    (hz : 1 < ‖z‖) (v : Fin 2 → ℂ) (hv : v ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    alJForm38 v < alJForm38 ((alPartial38 α z k).mulVec v) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [alPartial38_mulVec_succ]
  have h := alPartial38_ne_zero_ge α hα z hz v hv m
  exact lt_of_le_of_lt h.2 (alJForm_transfer_gt38 _ _ (hα _) hz _ h.1)

lemma alJForm_smul38 (w : ℂ) (v : Fin 2 → ℂ) :
    alJForm38 (w • v) = ‖w‖ ^ 2 * alJForm38 v := by
  simp [alJForm38, mul_pow]; ring

theorem no_unimodular_multiplier38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (hα : IsALField38 α)
    (z : ℂ) (hz : 1 < ‖z‖) (w : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (h : (alMonodromy38 α z).mulVec v = w • v) : ‖w‖ ≠ 1 := by
  intro hw
  have := alJForm_partial_strict38 α hα z hz v hv L (NeZero.pos L)
  change alJForm38 v < alJForm38 ((alMonodromy38 α z).mulVec v) at this
  rw [h, alJForm_smul38, hw] at this
  simp at this

lemma alJForm_eigen_gt38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (hα : IsALField38 α)
    (z : ℂ) (hz : 1 < ‖z‖) (w : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (h : (alMonodromy38 α z).mulVec v = w • v) :
    alJForm38 v < ‖w‖ ^ 2 * alJForm38 v := by
  have := alJForm_partial_strict38 α hα z hz v hv L (NeZero.pos L)
  change alJForm38 v < alJForm38 ((alMonodromy38 α z).mulVec v) at this
  rwa [h, alJForm_smul38] at this

/-- Interior multiplier: negative `J`-form. -/
theorem alJForm_neg_of_norm_lt_one38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) (z : ℂ) (hz : 1 < ‖z‖) (w : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (h : (alMonodromy38 α z).mulVec v = w • v) (hw : ‖w‖ < 1) : alJForm38 v < 0 := by
  have := alJForm_eigen_gt38 α hα z hz w v hv h
  have hm : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hm.le) hx]

/-- Exterior multiplier: positive `J`-form. -/
theorem alJForm_pos_of_one_lt_norm38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) (z : ℂ) (hz : 1 < ‖z‖) (w : ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0)
    (h : (alMonodromy38 α z).mulVec v = w • v) (hw : 1 < ‖w‖) : 0 < alJForm38 v := by
  have := alJForm_eigen_gt38 α hα z hz w v hv h
  have hm : 1 < ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  by_contra hx; push Not at hx
  nlinarith [mul_nonneg (sub_nonneg.2 hm.le) (neg_nonneg.2 hx)]

/-- With `det M = 1` the multipliers are `w, w⁻¹`; they are separated by the unit circle. -/
theorem eigenvalues_separated38 {L : ℕ} [NeZero L] (α : ZMod L → ℂ) (hα : IsALField38 α)
    (z : ℂ) (hz : 1 < ‖z‖) (w w' : ℂ) (hww : w * w' = 1) (v v' : Fin 2 → ℂ)
    (hv : v ≠ 0) (hv' : v' ≠ 0)
    (h : (alMonodromy38 α z).mulVec v = w • v)
    (h' : (alMonodromy38 α z).mulVec v' = w' • v') :
    (‖w‖ < 1 ∧ 1 < ‖w'‖ ∧ alJForm38 v < 0 ∧ 0 < alJForm38 v') ∨
      (1 < ‖w‖ ∧ ‖w'‖ < 1 ∧ 0 < alJForm38 v ∧ alJForm38 v' < 0) := by
  have h1 := no_unimodular_multiplier38 α hα z hz w v hv h
  have h2 := no_unimodular_multiplier38 α hα z hz w' v' hv' h'
  have hn : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, hww, norm_one]
  rcases lt_or_gt_of_ne h1 with a | a
  · left
    have : 1 < ‖w'‖ := by
      by_contra hc; push Not at hc
      nlinarith [norm_nonneg w, norm_nonneg w']
    exact ⟨a, this, alJForm_neg_of_norm_lt_one38 α hα z hz w v hv h a,
      alJForm_pos_of_one_lt_norm38 α hα z hz w' v' hv' h' this⟩
  · right
    have : ‖w'‖ < 1 := by
      by_contra hc; push Not at hc
      nlinarith [norm_nonneg w, norm_nonneg w']
    exact ⟨a, this, alJForm_pos_of_one_lt_norm38 α hα z hz w v hv h a,
      alJForm_neg_of_norm_lt_one38 α hα z hz w' v' hv' h' this⟩

end NlsGge.AblowitzLadik

end
