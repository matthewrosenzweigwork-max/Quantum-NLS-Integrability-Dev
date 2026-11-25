                                                                                                                                                                                                                                                                                      
import Mathlib
import NlsGge.Hierarchy.ALTransferDefs38

                                                                                                                   
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open NlsGge.AblowitzLadik

namespace NlsGge.ThirdConsultation.AL

local notation "JJ" => (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ)

namespace AL004Aux

theorem det_transfer (a z : ℂ) (ha : ‖a‖ < 1) (hz : z ≠ 0) : (alTransfer38 a z).det = 1 := by
  have h1 : (0 : ℝ) < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hs : (0 : ℝ) < Real.sqrt (1 - ‖a‖ ^ 2) := Real.sqrt_pos.2 h1
  have hs2 : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ^ 2 = ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt h1.le]
  have hsne : ((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hne : (1 - ‖a‖ ^ 2 : ℂ) ≠ 0 := by
    have : ((1 - ‖a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
    simpa using this
  have haa : a * star a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold alTransfer38
  rw [Matrix.det_smul, Matrix.det_fin_two_of]
  simp only [Fintype.card_fin]
  have : z * z⁻¹ - a * star a = 1 - ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [haa, mul_inv_cancel₀ hz]
  rw [this]
  field_simp
  rw [hs2]
  push_cast
  ring

theorem det_alPartial {L : ℕ} (α : ZMod L → ℂ) (hα : IsALField38 α) (z : ℂ) (hz : z ≠ 0) (n : ℕ) :
    (alPartial38 α z n).det = 1 := by
  induction n with
  | zero => simp [alPartial38]
  | succ n ih => rw [alPartial38, Matrix.det_mul, ih, det_transfer _ z (hα _) hz, one_mul]

theorem tele {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) (n : ℕ) :
    (alPartial38 α z n)ᴴ * JJ * alPartial38 α z n - JJ =
      ∑ j ∈ Finset.range n, (alPartial38 α z j)ᴴ *
        ((alTransfer38 (α (j : ZMod L)) z)ᴴ * JJ * alTransfer38 (α (j : ZMod L)) z - JJ) *
        alPartial38 α z j := by
  induction n with
  | zero => simp [alPartial38]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, alPartial38, Matrix.conjTranspose_mul]
    noncomm_ring

theorem quad_pos (a z w0 w1 : ℂ) (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) (hw : w0 ≠ 0 ∨ w1 ≠ 0) :
    0 < (1 - ‖a‖ ^ 2)⁻¹ * (Complex.normSq (z * w0 + a * w1) - Complex.normSq (starRingEnd ℂ a * w0 + w1 / z))
      - (Complex.normSq w0 - Complex.normSq w1) := by
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hr : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  set y : ℂ := w1 / z with hy
  have hw1 : w1 = z * y := by rw [hy]; field_simp
  have hxy : w0 ≠ 0 ∨ y ≠ 0 := by
    rcases hw with h | h
    · exact Or.inl h
    · right; rw [hy]; exact div_ne_zero h hz0
  have hZ : 1 < Complex.normSq z := by
    rw [← Complex.sq_norm]; nlinarith [norm_nonneg z]
  have hra : ‖a‖ ^ 2 = Complex.normSq a := Complex.sq_norm a
  rw [hw1, show z * w0 + a * (z * y) = z * (w0 + a * y) by ring]
  have hr' : 1 - Complex.normSq a ≠ 0 := by rw [← hra]; exact hr.ne'
  have key : (1 - ‖a‖ ^ 2)⁻¹ * (Complex.normSq (z * (w0 + a * y)) -
        Complex.normSq (starRingEnd ℂ a * w0 + y)) - (Complex.normSq w0 - Complex.normSq (z * y)) =
      (Complex.normSq z - 1) * (Complex.normSq w0 + Complex.normSq y +
        2 * (starRingEnd ℂ a * w0 * starRingEnd ℂ y).re) / (1 - ‖a‖ ^ 2) := by
    rw [hra]
    field_simp
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [key]
  apply div_pos _ hr
  apply mul_pos (sub_pos.2 hZ)
  have hC : -(‖a‖ * ‖w0‖ * ‖y‖) ≤ (starRingEnd ℂ a * w0 * starRingEnd ℂ y).re := by
    have := Complex.abs_re_le_norm (starRingEnd ℂ a * w0 * starRingEnd ℂ y)
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj] at this
    linarith [neg_abs_le ((starRingEnd ℂ a * w0 * starRingEnd ℂ y).re)]
  have hpos : 0 < ‖w0‖ ^ 2 + ‖y‖ ^ 2 := by
    rcases hxy with h | h
    · have := norm_pos_iff.2 h; positivity
    · have := norm_pos_iff.2 h; positivity
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [sq_nonneg (‖w0‖ - ‖y‖), norm_nonneg a, norm_nonneg w0, norm_nonneg y,
    mul_nonneg (norm_nonneg a) (sq_nonneg (‖w0‖ - ‖y‖))]

theorem form_pos (a z : ℂ) (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) (w : Fin 2 → ℂ) (hw : w ≠ 0) :
    0 < (dotProduct (star w)
      (((alTransfer38 a z)ᴴ * JJ * alTransfer38 a z - JJ) *ᵥ w)).re := by
  set A := alTransfer38 a z with hA
  have hJ : ∀ x : Fin 2 → ℂ, dotProduct (star x) (JJ *ᵥ x) =
      ((Complex.normSq (x 0) - Complex.normSq (x 1) : ℝ) : ℂ) := by
    intro x
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.star_def, mul_comm, Complex.mul_conj]
    ring
  have e1 : dotProduct (star w) ((Aᴴ * JJ * A) *ᵥ w) = dotProduct (star (A *ᵥ w)) (JJ *ᵥ (A *ᵥ w)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  have e2 : dotProduct (star w) ((Aᴴ * JJ * A - JJ) *ᵥ w) =
      ((Complex.normSq ((A *ᵥ w) 0) - Complex.normSq ((A *ᵥ w) 1) : ℝ) : ℂ) -
        ((Complex.normSq (w 0) - Complex.normSq (w 1) : ℝ) : ℂ) := by
    rw [Matrix.sub_mulVec, dotProduct_sub, e1, hJ, hJ]
  rw [e2, ← Complex.ofReal_sub, Complex.ofReal_re]
  have h1 : (A *ᵥ w) 0 = ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ))⁻¹ * (z * w 0 + a * w 1) := by
    simp [hA, alTransfer38, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have h2 : (A *ᵥ w) 1 = ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ))⁻¹ *
      (starRingEnd ℂ a * w 0 + w 1 / z) := by
    simp [hA, alTransfer38, Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
    ring
  have hc : Complex.normSq (((Real.sqrt (1 - ‖a‖ ^ 2) : ℝ) : ℂ))⁻¹ = (1 - ‖a‖ ^ 2)⁻¹ := by
    have h1' : (0 : ℝ) ≤ 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
    rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt h1']
  rw [h1, h2, map_mul, map_mul, hc]
  have hq := quad_pos a z (w 0) (w 1) ha hz (by
    by_contra hcon
    push_neg at hcon
    apply hw
    ext i; fin_cases i
    · exact hcon.1
    · exact hcon.2)
  nlinarith [hq]

end AL004Aux

theorem al004 {L : ℕ} [NeZero L] (α : ZMod L → ℂ)
    (hα : IsALField38 α) (z : ℂ) (hz : 1 < ‖z‖) :
  let J : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]
  (alMonodromy38 α z).conjTranspose * J * alMonodromy38 α z - J =
    ∑ j ∈ Finset.range L,
      (alPartial38 α z j).conjTranspose *
        ((alTransfer38 (α (j : ZMod L)) z).conjTranspose * J *
          alTransfer38 (α (j : ZMod L)) z - J) * alPartial38 α z j ∧
  (∀ j : ℕ, j ≤ L → IsUnit (alPartial38 α z j)) ∧
  ∀ v : Fin 2 → ℂ, v ≠ 0 →
    0 < (dotProduct (fun i => star (v i))
      (((alMonodromy38 α z).conjTranspose * J * alMonodromy38 α z - J).mulVec v)).re := by
  intro J
  have hz0 : z ≠ 0 := norm_pos_iff.1 (by linarith)
  have hunit : ∀ j : ℕ, IsUnit (alPartial38 α z j) := fun j =>
    (Matrix.isUnit_iff_isUnit_det _).2 (by rw [AL004Aux.det_alPartial α hα z hz0 j]; exact isUnit_one)
  have hT := AL004Aux.tele α z L
  refine ⟨hT, fun j _ => hunit j, ?_⟩
  intro v hv
  change 0 < (dotProduct (star v) ((((alMonodromy38 α z)ᴴ * JJ * alMonodromy38 α z) - JJ) *ᵥ v)).re
  rw [show alMonodromy38 α z = alPartial38 α z L from rfl, hT, Matrix.sum_mulVec, dotProduct_sum,
    Complex.re_sum]
  apply Finset.sum_pos _ (Finset.nonempty_range_iff.2 (NeZero.ne L))
  intro j _
  have hPv : alPartial38 α z j *ᵥ v ≠ 0 := by
    intro h
    apply hv
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (hunit j)
    have := (Matrix.mulVec_injective_iff_isUnit.2 (hunit j))
    exact this (by simpa using h)
  have key := AL004Aux.form_pos (α (j : ZMod L)) z (hα _) hz _ hPv
  have e : dotProduct (star v) (((alPartial38 α z j)ᴴ *
        ((alTransfer38 (α (j : ZMod L)) z)ᴴ * JJ * alTransfer38 (α (j : ZMod L)) z -
          JJ) * alPartial38 α z j) *ᵥ v) =
      dotProduct (star (alPartial38 α z j *ᵥ v))
        (((alTransfer38 (α (j : ZMod L)) z)ᴴ * JJ * alTransfer38 (α (j : ZMod L)) z -
          JJ) *ᵥ (alPartial38 α z j *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rw [e]
  exact key

end NlsGge.ThirdConsultation.AL
