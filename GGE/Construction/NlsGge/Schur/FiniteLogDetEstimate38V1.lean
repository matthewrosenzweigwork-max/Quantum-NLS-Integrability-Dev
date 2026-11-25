import Mathlib

/-!
# Finite-dimensional log-determinant estimate (`F:eq:logdet`, `F:eq:Jacbound`)

For a real square matrix `B` over a finite index type with `‖B‖ ≤ 1/2` (operator norm of the
Euclidean / `ℓ²` structure, `Matrix.Norms.L2Operator`), `0 < det (1 + B)` and
`|log det (1 + B) - tr B| ≤ HS` with `HS = ∑ i j, B i j ^ 2` (hence also `≤ 2 * HS`).
Proof by Jacobi's formula along `t ↦ det (1 + t B)`.
-/

set_option linter.unusedSectionVars false

namespace NlsGge.Schur

open Matrix Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Euclidean norm of a coordinate vector. -/
noncomputable def eN (v : ι → ℝ) : ℝ := ‖(EuclideanSpace.equiv ι ℝ).symm v‖

lemma eN_sq (v : ι → ℝ) : eN v ^ 2 = ∑ i, v i ^ 2 := by
  unfold eN
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

lemma eN_add (v w : ι → ℝ) : eN (v + w) ≤ eN v + eN w := by
  unfold eN
  rw [map_add]
  exact norm_add_le _ _

lemma eN_smul (c : ℝ) (v : ι → ℝ) : eN (c • v) = |c| * eN v := by
  unfold eN
  rw [map_smul, norm_smul, Real.norm_eq_abs]

lemma eN_nonneg (v : ι → ℝ) : 0 ≤ eN v := norm_nonneg _

lemma eN_eq_zero {v : ι → ℝ} (h : eN v = 0) : v = 0 := by
  unfold eN at h
  have := norm_eq_zero.mp h
  simpa using this

lemma abs_dot_le (u v : ι → ℝ) : |∑ i, u i * v i| ≤ eN u * eN v := by
  unfold eN
  have := abs_real_inner_le_norm ((EuclideanSpace.equiv ι ℝ).symm u)
    ((EuclideanSpace.equiv ι ℝ).symm v)
  convert this using 2
  simp [PiLp.inner_apply, mul_comm]

/-- Operator-norm hypothesis in coordinates. -/
def OpBound (B : Matrix ι ι ℝ) (c : ℝ) : Prop := ∀ v : ι → ℝ, eN (B *ᵥ v) ≤ c * eN v

open scoped Matrix.Norms.L2Operator in
lemma opBound_of_norm (B : Matrix ι ι ℝ) :
    OpBound B (‖B‖) := by
  intro v
  have := Matrix.l2_opNorm_mulVec (𝕜 := ℝ) B ((EuclideanSpace.equiv ι ℝ).symm v)
  simpa [eN] using this

lemma lower_bound (B : Matrix ι ι ℝ) (hB : OpBound B (1/2)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (w : ι → ℝ) : eN w ≤ 2 * eN ((1 + t • B) *ᵥ w) := by
  have h1 : w = (1 + t • B) *ᵥ w + (-t) • (B *ᵥ w) := by
    ext i; simp [add_mulVec, smul_mulVec]
  have h2 := eN_add ((1 + t • B) *ᵥ w) ((-t) • (B *ᵥ w))
  rw [← h1, eN_smul, abs_neg, abs_of_nonneg ht0] at h2
  have h3 := hB w
  have h4 : t * eN (B *ᵥ w) ≤ 1/2 * eN w := by
    calc t * eN (B *ᵥ w) ≤ 1 * eN (B *ᵥ w) := by
          exact mul_le_mul_of_nonneg_right ht1 (eN_nonneg _)
      _ ≤ 1/2 * eN w := by linarith
  linarith

lemma det_ne_zero (B : Matrix ι ι ℝ) (hB : OpBound B (1/2)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t • B).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  have := lower_bound B hB ht0 ht1 v
  rw [hv0] at this
  have h0 : eN (0 : ι → ℝ) = 0 := by simp [eN]
  rw [h0] at this
  exact hv (eN_eq_zero (le_antisymm (by linarith) (eN_nonneg _)))

lemma inv_bound (B : Matrix ι ι ℝ) (hB : OpBound B (1/2)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : ι → ℝ) : eN ((1 + t • B)⁻¹ *ᵥ x) ≤ 2 * eN x := by
  have hd := det_ne_zero B hB ht0 ht1
  have := lower_bound B hB ht0 ht1 ((1 + t • B)⁻¹ *ᵥ x)
  rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.one_mulVec] at this

/-- `|tr (B C B)| ≤ 2 HS` for any `C` of norm bound 2. -/
lemma trace_bound (B C : Matrix ι ι ℝ) (hC : OpBound C 2) :
    |trace (B * (C * B))| ≤ 2 * ∑ i, ∑ j, B i j ^ 2 := by
  have key : ∀ j, |∑ k, B j k * (C * B) k j| ≤
      (∑ k, B j k ^ 2) + ∑ k, B k j ^ 2 := by
    intro j
    have h1 : ∑ k, B j k * (C * B) k j = ∑ k, B j k * (C *ᵥ (fun k => B k j)) k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1]
    refine (abs_dot_le _ _).trans ?_
    have h2 := hC (fun k => B k j)
    have h3 : eN (B j) * eN (C *ᵥ fun k => B k j) ≤ eN (B j) * (2 * eN (fun k => B k j)) :=
      mul_le_mul_of_nonneg_left h2 (eN_nonneg _)
    have h4 := eN_sq (B j)
    have h5 := eN_sq (fun k => B k j)
    nlinarith [sq_nonneg (eN (B j) - eN (fun k => B k j))]
  have : |trace (B * (C * B))| ≤ ∑ j, ((∑ k, B j k ^ 2) + ∑ k, B k j ^ 2) := by
    rw [Matrix.trace]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    simpa [Matrix.diag, Matrix.mul_apply] using key j
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun j k => B k j ^ 2)] at this
  linarith

/-- Jacobi's formula at a point where `1 + tB` is invertible. -/
lemma hasDerivAt_det (B : Matrix ι ι ℝ) (t : ℝ) (hd : (1 + t • B).det ≠ 0) :
    HasDerivAt (fun s : ℝ => (1 + s • B).det)
      ((1 + t • B).det * trace ((1 + t • B)⁻¹ * B)) t := by
  set A : Matrix ι ι ℝ := 1 + t • B with hA
  have hAC : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd)
  set M : Matrix ι ι ℝ := A⁻¹ * B with hM
  set P : ℝ[X] := (det (1 + (X : ℝ[X]) • M.map C)).divX.divX with hP
  have hfun : (fun s : ℝ => (1 + s • B).det) = fun s : ℝ =>
      A.det * (1 + trace M * (s - t) + P.eval (s - t) * (s - t) ^ 2) := by
    funext s
    have : (1 : Matrix ι ι ℝ) + s • B = A * (1 + (s - t) • M) := by
      rw [mul_add, mul_one, mul_smul_comm, hM, ← Matrix.mul_assoc, hAC, Matrix.one_mul, hA,
        sub_smul]
      abel
    have hs := Matrix.det_one_add_smul (s - t) M
    rw [this, Matrix.det_mul, hs]
  rw [hfun]
  have h1 : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have h2 : HasDerivAt (fun s : ℝ => P.eval (s - t)) (P.derivative.eval (t - t) * 1) t := by
    have hh : HasDerivAt (fun x : ℝ => P.eval x) (P.derivative.eval (t - t))
        ((fun s : ℝ => s - t) t) := P.hasDerivAt (t - t)
    have := HasDerivAt.comp (𝕜 := ℝ) (h := fun s : ℝ => s - t) t hh h1
    exact this
  have h3 : HasDerivAt (fun s : ℝ => (s - t) ^ 2) (2 * (t - t) ^ 1 * 1) t := by
    convert h1.fun_pow 2 using 1
  have h4 := (((h1.const_mul (trace M)).const_add 1).add (h2.mul h3)).const_mul A.det
  convert h4 using 1
  simp

lemma det_pos_of_opBound (B : Matrix ι ι ℝ) (hB : OpBound B (1/2)) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) : 0 < (1 + t • B).det := by
  have hcont : ContinuousOn (fun s : ℝ => (1 + s • B).det) (Set.Icc 0 1) := fun s hs =>
    (hasDerivAt_det B s (det_ne_zero B hB hs.1 hs.2)).continuousAt.continuousWithinAt
  by_contra hneg
  push_neg at hneg
  have hsub : Set.Icc (0:ℝ) t ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc_right h1
  have := intermediate_value_Icc' (a := 0) (b := t) h0 (hcont.mono hsub)
    (show (0:ℝ) ∈ Set.Icc ((1 + t • B).det) ((1 + (0:ℝ) • B).det) from
      ⟨hneg, by simp⟩)
  obtain ⟨c, hc, hc0⟩ := this
  exact det_ne_zero B hB hc.1 (hc.2.trans h1) hc0

/-- Trace deviation along the path. -/
lemma trace_dev (B : Matrix ι ι ℝ) (hB : OpBound B (1/2)) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |trace ((1 + t • B)⁻¹ * B) - trace B| ≤ 2 * t * ∑ i, ∑ j, B i j ^ 2 := by
  have hd := det_ne_zero B hB h0 h1
  have hCA : (1 + t • B)⁻¹ * (1 + t • B) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd)
  set C := (1 + t • B)⁻¹ with hC
  have h2 : C * B = B - t • (C * B * B) := by
    have : C * (1 + t • B) * B = B := by rw [hCA, Matrix.one_mul]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul] at this
    rw [eq_sub_iff_add_eq]; exact this
  have h3 : trace (C * B) - trace B = - (t * trace (B * (C * B))) := by
    have := congrArg trace h2
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_mul_comm (C * B) B] at this
    simp only [smul_eq_mul] at this
    linarith
  rw [h3, abs_neg, abs_mul, abs_of_nonneg h0]
  have := trace_bound B C (inv_bound B hB h0 h1 |> fun h x => by simpa [hC] using h x)
  nlinarith

theorem logdet_abs_sub_trace_le_HS (B : Matrix ι ι ℝ) (hB : OpBound B (1/2)) :
    |Real.log (1 + B).det - trace B| ≤ ∑ i, ∑ j, B i j ^ 2 := by
  set HS : ℝ := ∑ i, ∑ j, B i j ^ 2 with hHS
  have hHS0 : 0 ≤ HS := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  set F : ℝ → ℝ := fun s => (1 + s • B).det with hF
  have hpos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < F s := fun s hs => det_pos_of_opBound B hB hs.1 hs.2
  have hder : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun r => Real.log (F r))
      (trace ((1 + s • B)⁻¹ * B)) s := by
    intro s hs
    have h := (hasDerivAt_det B s (hpos s hs).ne').log (hpos s hs).ne'
    convert h using 1
    exact (mul_div_cancel_left₀ _ (hpos s hs).ne').symm
  have hint : interior (Set.Icc (0:ℝ) 1) = Set.Ioo 0 1 := interior_Icc
  have hcont : ContinuousOn (fun r => Real.log (F r)) (Set.Icc 0 1) := fun s hs =>
    (hder s hs).continuousAt.continuousWithinAt
  have hF0 : F 0 = 1 := by simp [hF]
  have hF1 : F 1 = (1 + B).det := by simp [hF]
  have hdev := fun s (hs : s ∈ Set.Icc (0:ℝ) 1) => trace_dev B hB hs.1 hs.2
  -- upper bound
  have hup : AntitoneOn (fun r => Real.log (F r) - r * trace B - r ^ 2 * HS) (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (f' := fun s => trace ((1 + s • B)⁻¹ * B) - trace B - 2 * s * HS) ?_ ?_ ?_
    · exact (hcont.sub (by fun_prop)).sub (by fun_prop)
    · intro s hs
      rw [hint] at hs
      have hs' : s ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hs
      have := (((hder s hs').sub ((hasDerivAt_id s).mul_const (trace B))).sub
        ((hasDerivAt_pow 2 s).mul_const HS))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp
    · intro s hs
      rw [hint] at hs
      have := hdev s (Set.Ioo_subset_Icc_self hs)
      have := (abs_le.mp this).2
      linarith
  have hlo : MonotoneOn (fun r => Real.log (F r) - r * trace B + r ^ 2 * HS) (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun s => trace ((1 + s • B)⁻¹ * B) - trace B + 2 * s * HS) ?_ ?_ ?_
    · exact (hcont.sub (by fun_prop)).add (by fun_prop)
    · intro s hs
      rw [hint] at hs
      have hs' : s ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hs
      have := (((hder s hs').sub ((hasDerivAt_id s).mul_const (trace B))).add
        ((hasDerivAt_pow 2 s).mul_const HS))
      refine (this.congr_deriv ?_).hasDerivWithinAt
      simp
    · intro s hs
      rw [hint] at hs
      have := hdev s (Set.Ioo_subset_Icc_self hs)
      have := (abs_le.mp this).1
      linarith
  have h01 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have u := hup h01 h11 zero_le_one
  have l := hlo h01 h11 zero_le_one
  simp only [hF0, hF1, Real.log_one] at u l
  rw [abs_le]
  constructor <;> nlinarith

open scoped Matrix.Norms.L2Operator in
/-- `‖B‖ ≤ 1/2` (L2 operator norm) gives positivity of the determinant. -/
theorem det_one_add_pos (B : Matrix ι ι ℝ) (hB : ‖B‖ ≤ 1/2) : 0 < (1 + B).det := by
  have := det_pos_of_opBound B (fun v => (opBound_of_norm B v).trans
    (mul_le_mul_of_nonneg_right hB (eN_nonneg _))) (t := 1) zero_le_one le_rfl
  simpa using this

open scoped Matrix.Norms.L2Operator in
/-- `F:eq:logdet` with explicit constant `2` (the proof gives constant `1`). -/
theorem logDet_sub_trace_le (B : Matrix ι ι ℝ) (hB : ‖B‖ ≤ 1/2) :
    |Real.log (1 + B).det - trace B| ≤ 2 * ∑ i, ∑ j, B i j ^ 2 := by
  have h := logdet_abs_sub_trace_le_HS B (fun v => (opBound_of_norm B v).trans
    (mul_le_mul_of_nonneg_right hB (eN_nonneg _)))
  have : 0 ≤ ∑ i, ∑ j, B i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

open scoped Matrix.Norms.L2Operator in
/-- `F:eq:Jacbound`: `|tr B| ≤ 1/4` and `HS ≤ 1/8` give `1/2 ≤ det (1+B) ≤ 2`. -/
theorem det_one_add_mem_Icc (B : Matrix ι ι ℝ) (hB : ‖B‖ ≤ 1/2)
    (htr : |trace B| ≤ 1/4) (hHS : 2 * ∑ i, ∑ j, B i j ^ 2 ≤ 1/4) :
    1/2 ≤ (1 + B).det ∧ (1 + B).det ≤ 2 := by
  have hp := det_one_add_pos B hB
  have hl := abs_le.mp (logDet_sub_trace_le B hB)
  have ht := abs_le.mp htr
  have hlog1 : Real.log (1/2) ≤ Real.log (1 + B).det := by
    have : Real.log (1/2) < -(1/2) := by
      have := Real.log_two_gt_d9
      rw [one_div, Real.log_inv]; linarith
    linarith [hl.1, ht.1]
  have hlog2 : Real.log (1 + B).det ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith [hl.2, ht.2]
  exact ⟨(Real.log_le_log_iff (by norm_num) hp).mp hlog1,
    (Real.log_le_log_iff hp (by norm_num)).mp hlog2⟩

end NlsGge.Schur
