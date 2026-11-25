import NlsGge.Hierarchy.ALTransferDefs38
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Batch 38, E07 algebra of the AL monodromy (paper/v2.tex l.1870-1905, `D:sec:ALdefinition`):
determinant one, unit-circle `[[a,b],[b̄,ā]]` form (real trace), parity under `z ↦ -z`,
and the Laurent form `tr M(z) = Σ_{k=0}^{L} c_k z^{L-2k}` with `c_0 = exp(M_d/2)`. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open scoped Matrix
open Polynomial Filter Topology

/-! ### Determinant -/

theorem det_alTransfer38 (a z : ℂ) (ha : ‖a‖ < 1) (hz : z ≠ 0) :
    (alTransfer38 a z).det = 1 := by
  have hpos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith [norm_nonneg a]
  have hr0 : (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
  have hr2 : (Real.sqrt (1 - ‖a‖ ^ 2) : ℂ) ^ 2 = 1 - (‖a‖ : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hpos.le]; push_cast; ring
  have hmul : a * star a = (‖a‖ : ℂ) ^ 2 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold alTransfer38
  rw [Matrix.det_smul, Matrix.det_fin_two_of]
  simp only [Fintype.card_fin]
  rw [mul_inv_cancel₀ hz, hmul, inv_pow, hr2]
  have : (1 - (‖a‖ : ℂ) ^ 2) ≠ 0 := by rw [← hr2]; exact pow_ne_zero 2 hr0
  field_simp

theorem det_alPartial38 {L : ℕ} {α : ZMod L → ℂ} (hα : IsALField38 α) {z : ℂ} (hz : z ≠ 0)
    (k : ℕ) : (alPartial38 α z k).det = 1 := by
  induction k with
  | zero => simp [alPartial38]
  | succ k ih =>
    simp only [alPartial38, Matrix.det_mul, ih, det_alTransfer38 _ _ (hα _) hz, one_mul]

theorem det_alMonodromy38 {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) {z : ℂ}
    (hz : z ≠ 0) : (alMonodromy38 α z).det = 1 :=
  det_alPartial38 hα hz L

/-! ### Unit-circle form -/

/-- The form `[[a, b], [b̄, ā]]`. -/
def IsCircleForm38 (M : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ a b : ℂ, M = !![a, b; star b, star a]

theorem isCircleForm38_one : IsCircleForm38 1 :=
  ⟨1, 0, by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

theorem isCircleForm38_mul {M N : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsCircleForm38 M)
    (hN : IsCircleForm38 N) : IsCircleForm38 (M * N) := by
  obtain ⟨a, b, rfl⟩ := hM
  obtain ⟨c, d, rfl⟩ := hN
  refine ⟨a * c + b * star d, a * d + b * star c, ?_⟩
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm]

theorem alTransfer38_isCircleForm (a z : ℂ) (hz : ‖z‖ = 1) :
    IsCircleForm38 (alTransfer38 a z) := by
  have hzi : z⁻¹ = star z := by
    rw [Complex.inv_def, Complex.star_def, Complex.normSq_eq_norm_sq, hz]; simp
  set c : ℂ := ((Real.sqrt (1 - ‖a‖ ^ 2) : ℂ)⁻¹) with hc
  have hcs : star c = c := by
    rw [hc, star_inv₀, Complex.star_def, Complex.conj_ofReal]
  refine ⟨c * z, c * a, ?_⟩
  unfold alTransfer38
  rw [← hc, hzi]
  ext i j; fin_cases i <;> fin_cases j <;> simp [star_mul', hcs]

theorem alPartial38_isCircleForm {L : ℕ} (α : ZMod L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) :
    IsCircleForm38 (alPartial38 α z k) := by
  induction k with
  | zero => exact isCircleForm38_one
  | succ k ih => exact isCircleForm38_mul (alTransfer38_isCircleForm _ _ hz) ih

theorem alMonodromy38_circleForm {L : ℕ} (α : ZMod L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ∃ a b : ℂ, alMonodromy38 α z = !![a, b; star b, star a] :=
  alPartial38_isCircleForm α hz L

theorem alMonodromy38_trace_im {L : ℕ} (α : ZMod L → ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    (Matrix.trace (alMonodromy38 α z)).im = 0 := by
  obtain ⟨a, b, h⟩ := alMonodromy38_circleForm α hz
  rw [h, Matrix.trace_fin_two]
  simp

/-! ### Parity -/

theorem alTransfer38_neg (a z : ℂ) :
    alTransfer38 a (-z) =
      -(!![(1 : ℂ), 0; 0, -1] * alTransfer38 a z * !![(1 : ℂ), 0; 0, -1]) := by
  unfold alTransfer38
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [inv_neg]

private theorem sigConj38 (M : Matrix (Fin 2) (Fin 2) ℂ) :
    !![(1 : ℂ), 0; 0, -1] * M * !![(1 : ℂ), 0; 0, -1] =
      !![M 0 0, -M 0 1; -M 1 0, M 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] <;>
    simp

theorem alPartial38_neg {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) (k : ℕ) :
    alPartial38 α (-z) k =
      ((-1 : ℂ) ^ k) • (!![(1 : ℂ), 0; 0, -1] * alPartial38 α z k * !![(1 : ℂ), 0; 0, -1]) := by
  induction k with
  | zero =>
    have h := sigConj38 1
    rw [Matrix.mul_one] at h
    simp only [alPartial38, pow_zero, one_smul, Matrix.mul_one]
    rw [h]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    simp only [alPartial38]
    rw [alTransfer38_neg, ih, sigConj38, sigConj38, sigConj38]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

theorem alMonodromy38_neg {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) :
    alMonodromy38 α (-z) =
      ((-1 : ℂ) ^ L) •
        (!![(1 : ℂ), 0; 0, -1] * alMonodromy38 α z * !![(1 : ℂ), 0; 0, -1]) :=
  alPartial38_neg α z L

theorem trace_alMonodromy38_neg {L : ℕ} (α : ZMod L → ℂ) (z : ℂ) :
    Matrix.trace (alMonodromy38 α (-z)) = ((-1 : ℂ) ^ L) * Matrix.trace (alMonodromy38 α z) := by
  rw [alMonodromy38_neg, sigConj38]
  simp [Matrix.trace_fin_two]
  ring

theorem trace_alMonodromy38_neg_odd {L : ℕ} (hL : Odd L) (α : ZMod L → ℂ) (z : ℂ) :
    Matrix.trace (alMonodromy38 α (-z)) = -Matrix.trace (alMonodromy38 α z) := by
  rw [trace_alMonodromy38_neg, hL.neg_one_pow]; ring

/-! ### Laurent form -/

/-- normalisation constant of the `j`-th transfer matrix -/
def alScale38 {L : ℕ} (α : ZMod L → ℂ) (j : ℕ) : ℂ :=
  ((Real.sqrt (1 - ‖α (j : ZMod L)‖ ^ 2) : ℂ)⁻¹)

private theorem natDegree_step_le (a : ℂ) (p q : ℂ[X]) (k : ℕ) (hp : p.natDegree ≤ k)
    (hq : q.natDegree ≤ k) : (p + C a * X * q).natDegree ≤ k + 1 := by
  refine natDegree_add_le_of_degree_le (hp.trans (Nat.le_succ k)) ?_
  have h1 : (C a * X : ℂ[X]).natDegree ≤ 0 + 1 :=
    natDegree_mul_le_of_le (natDegree_C a).le (natDegree_X_le (R := ℂ))
  exact (natDegree_mul_le_of_le h1 hq).trans (by omega)

private theorem natDegree_step_le' (p q : ℂ[X]) (k : ℕ) (hp : p.natDegree ≤ k)
    (hq : q.natDegree ≤ k) : (p + q).natDegree ≤ k + 1 :=
  natDegree_add_le_of_degree_le (hp.trans (Nat.le_succ k)) (hq.trans (Nat.le_succ k))

private theorem natDegree_Xmul_le (p : ℂ[X]) (k : ℕ) (hp : p.natDegree ≤ k) :
    (X * p).natDegree ≤ k + 1 := by
  have := natDegree_mul_le_of_le (natDegree_X_le (R := ℂ)) hp
  omega

private theorem natDegree_Cmul_le' (c : ℂ) (p : ℂ[X]) (n : ℕ) (hp : p.natDegree ≤ n) :
    (C c * p).natDegree ≤ n := (natDegree_C_mul_le c p).trans hp

theorem alPartial_laurent38 {L : ℕ} {α : ZMod L → ℂ} (k : ℕ) :
    ∃ p00 p01 p10 p11 : ℂ[X],
      p00.natDegree ≤ k ∧ p01.natDegree ≤ k ∧ p10.natDegree ≤ k ∧ p11.natDegree ≤ k ∧
      p00.coeff 0 = ∏ j ∈ Finset.range k, alScale38 α j ∧
      p11.coeff 0 = (if k = 0 then 1 else 0) ∧
      ∀ z : ℂ, z ≠ 0 → alPartial38 α z k =
        !![z ^ (k : ℤ) * p00.eval ((z ^ 2)⁻¹), z ^ ((k : ℤ) - 1) * p01.eval ((z ^ 2)⁻¹);
           z ^ ((k : ℤ) - 1) * p10.eval ((z ^ 2)⁻¹), z ^ (k : ℤ) * p11.eval ((z ^ 2)⁻¹)] := by
  induction k with
  | zero =>
    refine ⟨1, 0, 0, 1, by simp, by simp, by simp, by simp, by simp, by simp, ?_⟩
    intro z hz
    ext i j; fin_cases i <;> fin_cases j <;> simp [alPartial38]
  | succ k ih =>
    obtain ⟨p00, p01, p10, p11, d00, d01, d10, d11, c00, c11, h⟩ := ih
    set s := alScale38 α k with hs
    set a := α (k : ZMod L) with ha
    refine ⟨C s * (p00 + C a * X * p10), C s * (p01 + C a * p11),
      C s * (C (star a) * p00 + X * p10), C s * (C (star a) * (X * p01) + X * p11),
      natDegree_Cmul_le' _ _ _ (natDegree_step_le a _ _ k d00 d10),
      natDegree_Cmul_le' _ _ _ (natDegree_step_le' _ _ k d01
        ((natDegree_Cmul_le' _ _ _ d11))),
      natDegree_Cmul_le' _ _ _ (natDegree_add_le_of_degree_le
        ((natDegree_Cmul_le' _ _ _ d00).trans (Nat.le_succ k)) (natDegree_Xmul_le _ _ d10)),
      natDegree_Cmul_le' _ _ _ (natDegree_add_le_of_degree_le
        (natDegree_Cmul_le' _ _ _ (natDegree_Xmul_le _ _ d01)) (natDegree_Xmul_le _ _ d11)),
      ?_, ?_, ?_⟩
    · rw [coeff_C_mul, coeff_add, c00, Finset.prod_range_succ, mul_comm]
      simp [coeff_zero_eq_eval_zero]
      exact Or.inl hs
    · simp [coeff_zero_eq_eval_zero]
    · intro z hz
      have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz
      have hg : z ^ ((k : ℤ) + 1 - 1) = z ^ (k : ℤ) := by simp
      have e1 : z ^ (((k + 1 : ℕ) : ℤ)) = z ^ (k : ℤ) * z := by
        rw [Nat.cast_succ, zpow_add_one₀ hz]
      have e2 : z ^ ((k : ℤ) - 1) = z ^ (k : ℤ) * z⁻¹ := by
        rw [zpow_sub_one₀ hz]
      have e0 : z ^ (k : ℤ) ≠ 0 := zpow_ne_zero _ hz
      have hA : alTransfer38 (α (k : ZMod L)) z = s • !![z, a; star a, z⁻¹] := rfl
      simp only [alPartial38]
      rw [hA, h z hz]
      have e3 : z ^ (((k + 1 : ℕ) : ℤ) - 1) = z ^ (k : ℤ) := by simp
      rw [e3, e1]
      rw [e2]
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, eval_add, eval_mul] <;>
        field_simp

private theorem pow_cast_eq (z : ℂ) (hz : z ≠ 0) (L m : ℕ) :
    z ^ (L : ℤ) * ((z ^ 2)⁻¹) ^ m = z ^ ((L : ℤ) - 2 * m) := by
  rw [zpow_sub₀ hz, zpow_mul]
  simp [inv_pow, div_eq_mul_inv]

/-- `∏ (1-r_j)^{-1/2} = exp(M_d/2)`. -/
theorem alScale38_prod {L : ℕ} [NeZero L] {α : ZMod L → ℂ} (hα : IsALField38 α) :
    ∏ j ∈ Finset.range L, alScale38 α j = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by have := NeZero.ne L; omega⟩
  have hpos : ∀ j : ZMod (n + 1), 0 < 1 - ‖α j‖ ^ 2 := fun j => by
    have := hα j; nlinarith [norm_nonneg (α j)]
  have hs : ∀ j : ZMod (n + 1),
      Real.exp (-Real.log (1 - ‖α j‖ ^ 2) / 2) = (Real.sqrt (1 - ‖α j‖ ^ 2))⁻¹ := by
    intro j
    rw [neg_div, Real.exp_neg, Real.exp_half, Real.exp_log (hpos j)]
  have hsum : ∏ j ∈ Finset.range (n + 1), alScale38 α j
      = ∏ j : ZMod (n + 1), ((Real.sqrt (1 - ‖α j‖ ^ 2))⁻¹ : ℝ) := by
    rw [← Fin.prod_univ_eq_prod_range (fun j => alScale38 α j) (n + 1)]
    rw [Complex.ofReal_prod]
    refine Finset.prod_congr rfl ?_
    intro j _
    simp only [alScale38]
    have hj : (((j : ℕ) : ZMod (n + 1))) = (show ZMod (n + 1) from j) :=
      Fin.cast_val_eq_self j
    rw [hj]
    push_cast; rfl
  rw [hsum]
  have : alMass38 (n + 1) α / 2 = ∑ j : ZMod (n + 1), (-Real.log (1 - ‖α j‖ ^ 2) / 2) := by
    unfold alMass38
    simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]
  rw [this, Real.exp_sum]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => (hs j).symm)

theorem alMonodromy38_trace_laurent {L : ℕ} [NeZero L] {α : ZMod L → ℂ}
    (hα : IsALField38 α) :
    ∃ c : ℕ → ℂ,
      (∀ z : ℂ, z ≠ 0 → Matrix.trace (alMonodromy38 α z) =
        ∑ k ∈ Finset.range (L + 1), c k * z ^ ((L : ℤ) - 2 * k)) ∧
      c 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
  obtain ⟨p00, p01, p10, p11, d00, d01, d10, d11, c00, c11, h⟩ :=
    alPartial_laurent38 (α := α) L
  have hL : L ≠ 0 := NeZero.ne L
  refine ⟨fun m => (p00 + p11).coeff m, ?_, ?_⟩
  · intro z hz
    unfold alMonodromy38
    rw [h z hz, Matrix.trace_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have hd : (p00 + p11).natDegree < L + 1 :=
      Nat.lt_succ_of_le (natDegree_add_le_of_degree_le d00 d11)
    rw [← mul_add, ← eval_add, eval_eq_sum_range' hd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [← pow_cast_eq z hz L m]; ring
  · simp [coeff_add, c00, c11, hL, alScale38_prod hα]

theorem alMonodromy38_trace_tendsto {L : ℕ} [NeZero L] {α : ZMod L → ℂ}
    (hα : IsALField38 α) :
    Tendsto (fun z : ℂ => z ^ (-(L : ℤ)) * Matrix.trace (alMonodromy38 α z)) (cocompact ℂ)
      (𝓝 ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ)) := by
  obtain ⟨p00, p01, p10, p11, d00, d01, d10, d11, c00, c11, h⟩ :=
    alPartial_laurent38 (α := α) L
  have hL : L ≠ 0 := NeZero.ne L
  have hw : Tendsto (fun z : ℂ => (z ^ 2)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : Tendsto (fun z : ℂ => ‖z‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun z : ℂ => ‖z‖ ^ 2) (cocompact ℂ) atTop :=
      (tendsto_pow_atTop (by norm_num)).comp h1
    have h3 := h2.inv_tendsto_atTop
    simp only [norm_inv, norm_pow]
    exact h3
  have hp := ((p00 + p11).continuous.tendsto 0).comp hw
  have hval : (p00 + p11).eval 0 = ((Real.exp (alMass38 L α / 2) : ℝ) : ℂ) := by
    rw [← coeff_zero_eq_eval_zero, coeff_add, c00, c11]
    simp [hL, alScale38_prod hα]
  rw [hval] at hp
  refine hp.congr' ?_
  have hev : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
    have := (tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop 0
    filter_upwards [this] with z hz
    exact norm_pos_iff.mp hz
  filter_upwards [hev] with z hz
  unfold alMonodromy38
  rw [h z hz, Matrix.trace_fin_two]
  simp only [Function.comp, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, eval_add]
  rw [mul_add, ← mul_assoc, ← mul_assoc, ← zpow_add₀ hz]
  simp

end NlsGge.AblowitzLadik

end
