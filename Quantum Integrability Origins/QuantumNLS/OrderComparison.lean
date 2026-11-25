import QuantumNLS.GaudinResponse

/-!
# CC:F01:comparison (R-C54DBD49): order comparison

Source: `source/chapters/root_response/F01.tex`, standing assumptions (lines 4-18: `L, c > 0`,
the map `T` of `CC:F01:smooth` and its Jacobian `CC:F01:jacobian`), Lemma `CC:F01:comparison`
(lines 20-27) and its proof (lines 28-38):

"For any `x, y ∈ ℝ^N`, define `B = ∫_0^1 DT(x + t(y − x)) dt`. Then `B` is symmetric positive
definite, `B^{-1}` has nonnegative entries, and every row and column of `B^{-1}` sums to `1/L`.
In particular, `T(x) ≤ T(y)` componentwise implies `x ≤ y` componentwise."

Lean indices are zero based (`Fin N`). `T` is `GaudinResponse.Tsmooth` (DEF-051, realized) and
`DT` its Fréchet derivative.

Realization: `avgJac L c x y` is the accepted entrywise average `RootContraction.Bavg` along the
segment; `avgJac_entry` identifies each entry literally with `∫_0^1 (DT(x + t(y−x)) e_k)_i dt`.
Printed proof steps: `avgJac_quadratic` (`vᵀBv = L Σ v_i² + Σ_{i<j} w_ij (v_i − v_j)²`,
`w_ij = w_ji > 0`), `avgJac_posDef`, `avgJac_isUnit_det`, the minimum principle
`avgJac_nonneg_of_nonneg`, `avgJac_inv_nonneg`, `B1 = L1` and symmetry for the row/column sums,
`avgJac_response` (`T(y) − T(x) = B(y − x)`), and `comparison`.

Deviation (does not change the statement): the matrix integral is entrywise (interval integrals of
the entries), as in the accepted `RootContraction`; no Bochner integral of matrices is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Finset

namespace QuantumNLS.OrderComparison

open QuantumNLS.GaudinResponse QuantumNLS.RootContraction QuantumNLS.OrderedResponse

variable {N : ℕ}

/-- `B = ∫_0^1 DT(x + t(y − x)) dt` (entrywise). -/
def avgJac (L c : ℝ) (x y : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Bavg L c x (fun j => y j - x j)

/-- Each entry is literally `∫_0^1 (DT(x + t(y − x)) e_k)_i dt`. -/
theorem avgJac_entry (L : ℝ) {c : ℝ} (hc : 0 < c) (x y : Fin N → ℝ) (i k : Fin N) :
    avgJac L c x y i k =
      ∫ t in (0 : ℝ)..1, fderiv ℝ (Tsmooth L c) (x + t • (y - x)) (Pi.single k 1) i := by
  unfold avgJac Bavg
  simp only [Matrix.of_apply]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have hz : (x + t • (y - x)) = fun j => x j + t * (y j - x j) := by
    funext j; simp [smul_eq_mul]
  rw [(hasFDerivAt_Tsmooth L hc _).fderiv, hz]
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

/-- The printed weights `w_ij` are positive and symmetric. -/
theorem weights_pos_symm {c : ℝ} (hc : 0 < c) (x y : Fin N → ℝ) (i j : Fin N) :
    0 < wAvg c x (fun l => y l - x l) i j ∧
      wAvg c x (fun l => y l - x l) i j = wAvg c x (fun l => y l - x l) j i :=
  ⟨wAvg_pos hc _ _ i j, wAvg_symm c _ _ i j⟩

/-- `(Bv)_i = L v_i + Σ_{j≠i} w_ij (v_i − v_j)`. -/
theorem avgJac_mulVec {L c : ℝ} (hc : 0 < c) (x y v : Fin N → ℝ) (i : Fin N) :
    (avgJac L c x y *ᵥ v) i =
      L * v i + ∑ j ∈ univ.erase i, wAvg c x (fun l => y l - x l) i j * (v i - v j) :=
  Bavg_mulVec hc _ _ v i

/-- **The quadratic form** `vᵀBv = L Σ_i v_i² + Σ_{i<j} w_ij (v_i − v_j)²`. -/
theorem avgJac_quadratic {L c : ℝ} (hc : 0 < c) (x y v : Fin N → ℝ) :
    v ⬝ᵥ (avgJac L c x y *ᵥ v) = L * ∑ i, v i ^ 2 +
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        wAvg c x (fun l => y l - x l) i j * (v i - v j) ^ 2 := by
  set w := wAvg c x (fun l => y l - x l)
  have hw : ∀ i j, w i j = w j i := fun i j => wAvg_symm c _ _ i j
  have h1 : ∀ i, v i * (avgJac L c x y *ᵥ v) i =
      L * v i ^ 2 + ∑ j, w i j * (v i * (v i - v j)) := by
    intro i
    rw [avgJac_mulVec hc, mul_add, Finset.mul_sum]
    rw [← Finset.sum_erase (s := univ) (a := i) (f := fun j => w i j * (v i * (v i - v j)))
      (by simp)]
    congr 1
    · ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  have hpair : 2 * ∑ i, ∑ j, w i j * (v i * (v i - v j)) =
      ∑ i, ∑ j, w i j * (v i - v j) ^ 2 := by
    have hS : ∑ i, ∑ j, w i j * (v i * (v i - v j)) = ∑ i, ∑ j, w i j * (v j * (v j - v i)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
        rw [hw j i]
    rw [two_mul]
    nth_rewrite 2 [hS]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlt := sum_sum_eq_two_mul_lt (fun i j => w i j * (v i - v j) ^ 2)
    (fun i j => by
      show w i j * (v i - v j) ^ 2 = w j i * (v j - v i) ^ 2
      rw [hw i j]; ring) (fun i => by simp)
  unfold dotProduct
  simp_rw [h1]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  linarith

/-- **`B` is symmetric.** -/
theorem avgJac_transpose {L c : ℝ} (hc : 0 < c) (x y : Fin N → ℝ) :
    (avgJac L c x y)ᵀ = avgJac L c x y := Bavg_transpose hc _ _

/-- **`B` is positive definite** (`L, c > 0`). -/
theorem avgJac_posDef {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y : Fin N → ℝ) :
    (avgJac L c x y).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact avgJac_transpose hc x y
  · have h := Bavg_quad (L := L) hc x (fun j => y j - x j) v
    have hpos : 0 < ∑ i, v i ^ 2 := by
      obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
        by_contra h'; push Not at h'; exact hv (funext h')
      exact lt_of_lt_of_le (pow_pos (abs_pos.mpr hi) 2 |>.trans_eq (sq_abs _))
        (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (mem_univ i))
    simp only [star_trivial]
    unfold dotProduct avgJac
    nlinarith

/-- **`B` is invertible.** -/
theorem avgJac_isUnit_det {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y : Fin N → ℝ) :
    IsUnit (avgJac L c x y).det := Bavg_isUnit_det hL hc _ _

/-- **Minimum principle**: `Bv = f ≥ 0` implies `v ≥ 0`. -/
theorem avgJac_nonneg_of_nonneg {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y v : Fin N → ℝ)
    (hf : ∀ i, 0 ≤ (avgJac L c x y *ᵥ v) i) : ∀ i, 0 ≤ v i :=
  Bavg_nonneg_of_nonneg hL hc _ _ v hf

/-- **`B^{-1}` has nonnegative entries.** -/
theorem avgJac_inv_nonneg {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y : Fin N → ℝ) (i k : Fin N) :
    0 ≤ (avgJac L c x y)⁻¹ i k := Bavg_inv_nonneg hL hc _ _ i k

/-- `B 1 = L 1`. -/
theorem avgJac_mulVec_one {L c : ℝ} (hc : 0 < c) (x y : Fin N → ℝ) :
    avgJac L c x y *ᵥ (fun _ => (1 : ℝ)) = fun _ => L := Bavg_mulVec_one hc _ _

/-- **Every row of `B^{-1}` sums to `1/L`.** -/
theorem avgJac_inv_row_sum {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y : Fin N → ℝ) (i : Fin N) :
    ∑ k, (avgJac L c x y)⁻¹ i k = 1 / L := Bavg_inv_row_sum hL hc _ _ i

/-- **Every column of `B^{-1}` sums to `1/L`.** -/
theorem avgJac_inv_col_sum {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y : Fin N → ℝ) (k : Fin N) :
    ∑ i, (avgJac L c x y)⁻¹ i k = 1 / L := Bavg_inv_col_sum hL hc _ _ k

/-- **`T(y) − T(x) = B(y − x)`.** -/
theorem avgJac_response {L c : ℝ} (hc : 0 < c) (x y : Fin N → ℝ) (i : Fin N) :
    (avgJac L c x y *ᵥ (y - x)) i = Tsmooth L c y i - Tsmooth L c x i := by
  have h := Bavg_response (L := L) hc x (fun j => y j - x j) i
  have e : (fun j => x j + (y j - x j)) = y := by funext j; ring
  rw [e] at h
  exact h

/-- **Order comparison**: `T(x) ≤ T(y)` componentwise implies `x ≤ y` componentwise. -/
theorem comparison {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {x y : Fin N → ℝ}
    (hT : ∀ i, Tsmooth L c x i ≤ Tsmooth L c y i) : ∀ i, x i ≤ y i := by
  have h := avgJac_nonneg_of_nonneg hL hc x y (y - x) (fun i => by
    rw [avgJac_response hc]; linarith [hT i])
  intro i
  have := h i
  simp only [Pi.sub_apply] at this
  linarith

/-- **CC:F01:comparison**, all printed clauses together. -/
theorem order_comparison {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (x y : Fin N → ℝ) :
    (avgJac L c x y)ᵀ = avgJac L c x y ∧ (avgJac L c x y).PosDef ∧
    (∀ i k, 0 ≤ (avgJac L c x y)⁻¹ i k) ∧
    (∀ i, ∑ k, (avgJac L c x y)⁻¹ i k = 1 / L) ∧
    (∀ k, ∑ i, (avgJac L c x y)⁻¹ i k = 1 / L) ∧
    ((∀ i, Tsmooth L c x i ≤ Tsmooth L c y i) → ∀ i, x i ≤ y i) :=
  ⟨avgJac_transpose hc x y, avgJac_posDef hL hc x y, avgJac_inv_nonneg hL hc x y,
    avgJac_inv_row_sum hL hc x y, avgJac_inv_col_sum hL hc x y, comparison hL hc⟩

/-! Kernel axiom audit (checkpoint OC1). -/
#print axioms avgJac_entry
#print axioms weights_pos_symm
#print axioms avgJac_mulVec
#print axioms avgJac_quadratic
#print axioms avgJac_transpose
#print axioms avgJac_posDef
#print axioms avgJac_isUnit_det
#print axioms avgJac_nonneg_of_nonneg
#print axioms avgJac_inv_nonneg
#print axioms avgJac_mulVec_one
#print axioms avgJac_inv_row_sum
#print axioms avgJac_inv_col_sum
#print axioms avgJac_response
#print axioms comparison
#print axioms order_comparison

end QuantumNLS.OrderComparison
