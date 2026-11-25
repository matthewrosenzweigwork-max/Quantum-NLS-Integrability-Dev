import Mathlib
import QuantumNLS.BetheCompressedKernel
import QuantumNLS.NormalizedTransfer

/-!
# R-F611926F `QG:prop:haar-kernel-factorization` (stage 1): determinant form of the actual DEF-048 kernels
(`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:293`)

> `K_{r,z} = (1 − ρ_r e^{izL})/r! · A_r^* (∧^r R_z^{ρ_r}) A_r`, `ρ_r = (−1)^{r−1}`, with the resolvent kernel
> `R_z^ρ(x,y) = e^{iz(x−y)}/(1−q) (1_{x>y} + q 1_{x<y})`, `q = ρ e^{izL}`.

## This module
The proof's kernel-level content, against the ACTUAL DEF-048 kernels (`BetheTransferKernelAdjoint.rawPlus/rawMinus`
and the explicit double average `BetheCompressedKernel.averagedRaw`, whose `m!`-averages over output and input
permutations are the symmetrizers `P_r`):
* Part I: the chamber determinant `det (1_{y_j<x_i} + q 1_{y_j>x_i})` of strictly decreasing tuples equals
  `(1−q)^{r−1}` on the pattern `x_1>y_1>…>x_r>y_r`, `(−1)^{r−1}q(1−q)^{r−1}` on `y_1>x_1>…>y_r>x_r`, `0` otherwise
  (`det_Mq_formula`; elementary row operations and a transposition/complement symmetry, no external input).
* Part II: `(1−q) det R(x_i,y_j) = rawKernel L z x y` for strictly decreasing `x,y` in `(0,L)` without ties
  (`rawKernel_eq_det`), and the full averaged kernel `averagedRaw L r z X Y = (1−q)/(r!)² · sgn(X) sgn(Y) · det R(X_i,Y_j)`
  for tuples with distinct coordinates in `(0,L)` (`averagedRaw_eq`; `sgn` = sign of the permutation sorting the tuple
  into decreasing order), which is the exact factorization at kernel level (`(1−q)/r! · (1/r!) det` with ordering signs).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Matrix Finset
open scoped BigOperators Classical

namespace QuantumNLS.HaarKernelFactorization

/-! ### Part I: the chamber determinant -/

/-- The 0/1-valued staircase matrix `M_{ij} = 1` if `y_j < x_i`, else `q`. -/
def Mq (q : ℂ) {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if y j < x i then 1 else q

/-- Strict cyclic interlacing `x_1 > y_1 > x_2 > y_2 > …`. -/
def Il {n : ℕ} (x y : Fin n → ℝ) : Prop := (∀ j, y j < x j) ∧ ∀ i j, i < j → x j < y i

/-- No coincidences between the `x`- and `y`-coordinates. -/
def NoTie {n : ℕ} (x y : Fin n → ℝ) : Prop := ∀ i j, x i ≠ y j

theorem Il_succ {n : ℕ} (x y : Fin (n + 1) → ℝ) :
    Il x y ↔ y 0 < x 0 ∧ (∀ i : Fin n, x i.succ < y 0) ∧
      Il (fun i : Fin n => x i.succ) (fun i : Fin n => y i.succ) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0, fun i => h2 0 i.succ (Fin.succ_pos i),
      fun j => h1 j.succ, fun i j hij => h2 i.succ j.succ (Fin.succ_lt_succ_iff.2 hij)⟩
  · rintro ⟨h0, hc, h1, h2⟩
    refine ⟨fun j => ?_, fun i j hij => ?_⟩
    · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
      · exact h0
      · exact h1 j
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact absurd hij (lt_irrefl _)
        · exact hc j
      · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j, rfl⟩
        · exact absurd hij (by simp [Fin.lt_def])
        · exact h2 i j (Fin.succ_lt_succ_iff.1 hij)

theorem Il_one (x y : Fin 1 → ℝ) : Il x y ↔ y 0 < x 0 := by
  constructor
  · exact fun h => h.1 0
  · intro h
    refine ⟨fun j => ?_, fun i j hij => ?_⟩
    · rw [Subsingleton.elim j 0]; exact h
    · exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl _)

/-- Transposition/complement symmetry: `M_q(x,y) = q · M_{q⁻¹}(y,x)ᵀ` (no ties). -/
theorem Mq_transpose {n : ℕ} (q : ℂ) (hq : q ≠ 0) (x y : Fin n → ℝ) (h : NoTie x y) :
    Mq q x y = q • (Mq q⁻¹ y x).transpose := by
  ext i j
  simp only [Mq, Matrix.of_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rcases lt_or_gt_of_ne (h i j) with hlt | hgt
  · rw [if_neg (not_lt.2 hlt.le), if_pos hlt, mul_one]
  · rw [if_pos hgt, if_neg (not_lt.2 hgt.le), mul_inv_cancel₀ hq]

/-- Rows `0` and `i+1` coincide (both all ones) when `y_0 < x_{i+1}` and `y_0 < x_0`. -/
theorem det_Mq_caseA0 {n : ℕ} (q : ℂ) (x y : Fin (n + 2) → ℝ) (hy : ∀ j, y j ≤ y 0)
    (h0 : y 0 < x 0) (i : Fin (n + 1)) (hi : y 0 < x i.succ) : (Mq q x y).det = 0 := by
  refine Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm ?_
  funext j
  simp only [Mq, Matrix.of_apply]
  rw [if_pos (lt_of_le_of_lt (hy j) h0), if_pos (lt_of_le_of_lt (hy j) hi)]

/-- Row reduction when `y_0 < x_0` and all other `x_i < y_0`: the determinant reduces to the tails at `q = 0`. -/
theorem det_Mq_caseA {n : ℕ} (q : ℂ) (x y : Fin (n + 2) → ℝ) (hy : ∀ j, y j ≤ y 0)
    (h0 : y 0 < x 0) (h1 : ∀ i : Fin (n + 1), x i.succ < y 0) :
    (Mq q x y).det = (1 - q) ^ (n + 1) *
      (Mq (0 : ℂ) (fun i : Fin (n + 1) => x i.succ) (fun i : Fin (n + 1) => y i.succ)).det := by
  set M := Mq q x y with hM
  have hrow0 : ∀ j, M 0 j = 1 := fun j => by
    simp only [hM, Mq, Matrix.of_apply]
    rw [if_pos (lt_of_le_of_lt (hy j) h0)]
  have hcol0 : ∀ i : Fin (n + 1), M i.succ 0 = q := fun i => by
    simp only [hM, Mq, Matrix.of_apply]
    rw [if_neg (not_lt.2 (h1 i).le)]
  let L : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    Matrix.of fun i k => if i = k then 1 else if k = 0 then q else 0
  let N : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
    Matrix.of fun i j => if i = 0 then M 0 j else M i j - q * M 0 j
  have hLN : M = L * N := by
    ext i j
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · have h0s : ∀ k : Fin (n + 1), (0 : Fin (n + 2)) ≠ k.succ := fun k => (Fin.succ_ne_zero k).symm
      simp [Matrix.mul_apply, Fin.sum_univ_succ, L, N, Fin.succ_ne_zero, h0s]
    · simp [Matrix.mul_apply, Fin.sum_univ_succ, L, N, Fin.succ_ne_zero, Fin.succ_inj]
  have hlow : L.IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    have h1' : i ≠ j := ne_of_lt hij'
    have h2' : j ≠ 0 := by
      intro h; subst h; exact absurd hij' (by simp [Fin.lt_def])
    simp [L, h1', h2']
  have hLdet : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L hlow]
    simp [L]
  have hNdet : N.det = (1 - q) ^ (n + 1) * (Mq (0 : ℂ) (fun i : Fin (n + 1) => x i.succ)
      (fun i : Fin (n + 1) => y i.succ)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∀ i : Fin (n + 1), (-1 : ℂ) ^ ((i.succ : Fin (n + 2)) : ℕ) * N i.succ 0 *
        det (N.submatrix i.succ.succAbove Fin.succ) = 0 := by
      intro i
      have : N i.succ 0 = 0 := by
        simp only [N, Matrix.of_apply, Fin.succ_ne_zero, if_false]
        rw [hcol0 i, hrow0 0]; ring
      rw [this]; ring
    rw [Finset.sum_eq_zero (fun i _ => hz i), add_zero]
    have h00 : N 0 0 = 1 := by simp [N, hrow0]
    have hsub : N.submatrix (Fin.succAbove (0 : Fin (n + 2))) Fin.succ =
        (1 - q) • Mq (0 : ℂ) (fun i : Fin (n + 1) => x i.succ) (fun i : Fin (n + 1) => y i.succ) := by
      ext i j
      simp only [N, Mq, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_ne_zero, if_false,
        Fin.succAbove_zero, Matrix.smul_apply, smul_eq_mul, hM]
      rw [if_pos (lt_of_le_of_lt (hy j.succ) h0)]
      by_cases hc : y j.succ < x i.succ
      · simp [hc]
      · simp [hc]
    simp only [Fin.val_zero, pow_zero, one_mul, h00]
    rw [hsub, Matrix.det_smul]
    simp
  rw [hLN, Matrix.det_mul, hLdet, hNdet, one_mul]

/-- **The chamber determinant.**  For strictly decreasing `x, y : Fin (n+1) → ℝ` without ties,
`det(1_{y_j<x_i} + q 1_{y_j>x_i}) = (1−q)^n ([x_1>y_1>…] + (−1)^n q [y_1>x_1>…])`. -/
theorem det_Mq_formula : ∀ (n : ℕ) (q : ℂ) (x y : Fin (n + 1) → ℝ), StrictAnti x → StrictAnti y →
    NoTie x y → (Mq q x y).det = (1 - q) ^ n *
      ((if Il x y then 1 else 0) + (-1) ^ n * q * (if Il y x then 1 else 0)) := by
  intro n
  induction n with
  | zero =>
    intro q x y hx hy hnt
    rw [Matrix.det_fin_one]
    simp only [Mq, Matrix.of_apply, Il_one, pow_zero, one_mul]
    rcases lt_or_gt_of_ne (hnt 0 0) with hlt | hgt
    · rw [if_neg (not_lt.2 hlt.le), if_neg (not_lt.2 hlt.le), if_pos hlt]; ring
    · rw [if_pos hgt, if_pos hgt, if_neg (not_lt.2 hgt.le)]; ring
  | succ n ih =>
    intro q x y hx hy hnt
    have hx' : StrictAnti (fun i : Fin (n + 1) => x i.succ) := hx.comp_strictMono Fin.strictMono_succ
    have hy' : StrictAnti (fun i : Fin (n + 1) => y i.succ) := hy.comp_strictMono Fin.strictMono_succ
    have hnt' : NoTie (fun i : Fin (n + 1) => x i.succ) (fun i : Fin (n + 1) => y i.succ) :=
      fun i j => hnt i.succ j.succ
    have hy0 : ∀ j, y j ≤ y 0 := fun j => hy.antitone (Fin.zero_le _)
    have hx0 : ∀ j, x j ≤ x 0 := fun j => hx.antitone (Fin.zero_le _)
    have ih0 : ∀ (x y : Fin (n + 1) → ℝ), StrictAnti x → StrictAnti y → NoTie x y →
        (Mq (0 : ℂ) x y).det = if Il x y then 1 else 0 := by
      intro x y hx hy hnt
      rw [ih 0 x y hx hy hnt]; simp
    -- Case A in full generality
    have caseA : ∀ (q : ℂ) (x y : Fin (n + 2) → ℝ), StrictAnti x → StrictAnti y → NoTie x y →
        y 0 < x 0 → (Mq q x y).det = (1 - q) ^ (n + 1) * (if Il x y then 1 else 0) := by
      intro q x y hx hy hnt hA
      have hx' : StrictAnti (fun i : Fin (n + 1) => x i.succ) :=
        hx.comp_strictMono Fin.strictMono_succ
      have hy' : StrictAnti (fun i : Fin (n + 1) => y i.succ) :=
        hy.comp_strictMono Fin.strictMono_succ
      have hnt' : NoTie (fun i : Fin (n + 1) => x i.succ) (fun i : Fin (n + 1) => y i.succ) :=
        fun i j => hnt i.succ j.succ
      have hy0 : ∀ j, y j ≤ y 0 := fun j => hy.antitone (Fin.zero_le _)
      by_cases hall : ∀ i : Fin (n + 1), x i.succ < y 0
      · rw [det_Mq_caseA q x y hy0 hA hall, ih0 _ _ hx' hy' hnt']
        have : Il x y ↔ Il (fun i : Fin (n + 1) => x i.succ) (fun i : Fin (n + 1) => y i.succ) := by
          rw [Il_succ]; exact ⟨fun h => h.2.2, fun h => ⟨hA, hall, h⟩⟩
        simp only [this]
      · push_neg at hall
        obtain ⟨i, hi⟩ := hall
        have hi' : y 0 < x i.succ := lt_of_le_of_ne hi (hnt i.succ 0).symm
        rw [det_Mq_caseA0 q x y hy0 hA i hi']
        have : ¬ Il x y := by
          rw [Il_succ]; rintro ⟨_, h, _⟩; exact absurd (h i) (not_lt.2 hi)
        simp [this]
    rcases lt_or_gt_of_ne (hnt 0 0) with hB | hA
    · -- Case B : x 0 < y 0
      have hnIl : ¬ Il x y := fun h => absurd (h.1 0) (not_lt.2 hB.le)
      by_cases hq : q = 0
      · subst hq
        rw [Matrix.det_eq_zero_of_column_eq_zero 0 (fun i => by
          simp only [Mq, Matrix.of_apply]
          rw [if_neg (not_lt.2 (lt_of_le_of_lt (hx0 i) hB).le)])]
        simp [hnIl]
      · have hnt'' : NoTie y x := fun i j => (hnt j i).symm
        rw [Mq_transpose q hq x y hnt, Matrix.det_smul, Matrix.det_transpose,
          caseA q⁻¹ y x hy hx hnt'' hB]
        simp only [Fintype.card_fin, hnIl, if_false, zero_add]
        have hq1 : q ^ (n + 2) * (1 - q⁻¹) ^ (n + 1) = q * (q - 1) ^ (n + 1) := by
          have : (1 - q⁻¹) = (q - 1) / q := by field_simp
          rw [this, div_pow]; field_simp; ring
        have h2 : (q - 1) ^ (n + 1) = (-1) ^ (n + 1) * (1 - q) ^ (n + 1) := by
          rw [← neg_sub, neg_pow]
        calc q ^ (n + 2) * ((1 - q⁻¹) ^ (n + 1) * (if Il y x then 1 else 0))
            = (q ^ (n + 2) * (1 - q⁻¹) ^ (n + 1)) * (if Il y x then 1 else 0) := by ring
          _ = _ := by rw [hq1, h2]; ring
    · -- Case A : y 0 < x 0
      have hnIl' : ¬ Il y x := fun h => absurd (h.1 0) (not_lt.2 hA.le)
      rw [caseA q x y hx hy hnt hA]
      simp [hnIl']

#print axioms det_Mq_formula

/-! ### Part II: the actual DEF-048 averaged kernel as a determinant -/

section Kernel

open QuantumNLS.BetheTransferKernelAdjoint QuantumNLS.BetheCompressedKernel

/-- The resolvent kernel `R_z^ρ(a,b) = e^{iz(a−b)}/(1−q) (1_{a>b} + q 1_{a<b})` of the source (`q = ρ e^{izL}`). -/
def Rk (q z : ℂ) (a b : ℝ) : ℂ :=
  Complex.exp (Complex.I * z * ((a - b : ℝ) : ℂ)) / (1 - q) *
    (if b < a then 1 else if a < b then q else 0)

/-- The matrix `(R_z^ρ(x_i, y_j))_{i,j}`. -/
def RkMat (q z : ℂ) {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => Rk q z (x i) (y j)

/-- `det R(x_i,y_j) = e^{izΣ(x−y)}/(1−q)^n · det M_q(x,y)` (no ties). -/
theorem det_RkMat {n : ℕ} (q z : ℂ) (x y : Fin n → ℝ) (h : NoTie x y) :
    (RkMat q z x y).det = (1 - q)⁻¹ ^ n *
      Complex.exp (Complex.I * z * ((∑ i, (x i - y i) : ℝ) : ℂ)) * (Mq q x y).det := by
  have hentry : RkMat q z x y = Matrix.of fun i j =>
      Complex.exp (Complex.I * z * (x i : ℂ)) *
        (Complex.exp (-(Complex.I * z * (y j : ℂ))) * ((1 - q)⁻¹ * (Mq q x y) i j)) := by
    ext i j
    simp only [RkMat, Rk, Mq, Matrix.of_apply]
    rcases lt_or_gt_of_ne (h i j) with hlt | hgt
    · rw [if_neg (not_lt.2 hlt.le), if_pos hlt, if_neg (not_lt.2 hlt.le)]
      rw [div_eq_inv_mul, ← mul_assoc, ← mul_assoc]
      have : Complex.exp (Complex.I * z * ((x i - y j : ℝ) : ℂ)) =
          Complex.exp (Complex.I * z * (x i : ℂ)) * Complex.exp (-(Complex.I * z * (y j : ℂ))) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
    · rw [if_pos hgt, if_pos hgt]
      have : Complex.exp (Complex.I * z * ((x i - y j : ℝ) : ℂ)) =
          Complex.exp (Complex.I * z * (x i : ℂ)) * Complex.exp (-(Complex.I * z * (y j : ℂ))) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [this]; ring
  rw [hentry]
  have h1 : (Matrix.of fun i j => Complex.exp (Complex.I * z * (x i : ℂ)) *
        (Complex.exp (-(Complex.I * z * (y j : ℂ))) * ((1 - q)⁻¹ * (Mq q x y) i j))).det =
      (∏ i, Complex.exp (Complex.I * z * (x i : ℂ))) *
        (Matrix.of fun i j => Complex.exp (-(Complex.I * z * (y j : ℂ))) *
          ((1 - q)⁻¹ * (Mq q x y) i j)).det :=
    Matrix.det_mul_column (fun i => Complex.exp (Complex.I * z * (x i : ℂ)))
      (Matrix.of fun i j => Complex.exp (-(Complex.I * z * (y j : ℂ))) * ((1 - q)⁻¹ * (Mq q x y) i j))
  have h2 : (Matrix.of fun i j => Complex.exp (-(Complex.I * z * (y j : ℂ))) *
          ((1 - q)⁻¹ * (Mq q x y) i j)).det =
      (∏ j, Complex.exp (-(Complex.I * z * (y j : ℂ)))) *
        (Matrix.of fun i j => (1 - q)⁻¹ * (Mq q x y) i j).det :=
    Matrix.det_mul_row (fun j => Complex.exp (-(Complex.I * z * (y j : ℂ))))
      (Matrix.of fun i j => (1 - q)⁻¹ * (Mq q x y) i j)
  rw [h1, h2]
  have hc : (Matrix.of fun i j => (1 - q)⁻¹ * (Mq q x y) i j) = (1 - q)⁻¹ • Mq q x y := by
    ext i j; simp
  rw [hc, Matrix.det_smul, Fintype.card_fin]
  have hexp : (∏ i, Complex.exp (Complex.I * z * (x i : ℂ))) *
      (∏ j, Complex.exp (-(Complex.I * z * (y j : ℂ)))) =
      Complex.exp (Complex.I * z * ((∑ i, (x i - y i) : ℝ) : ℂ)) := by
    have e : ∀ i, Complex.exp (Complex.I * z * (x i : ℂ)) * Complex.exp (-(Complex.I * z * (y i : ℂ))) =
        Complex.exp (Complex.I * z * ((x i - y i : ℝ) : ℂ)) := fun i => by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => e i), ← Complex.exp_sum,
      ← Finset.mul_sum, ← Complex.ofReal_sum]
  calc _ = ((∏ i, Complex.exp (Complex.I * z * (x i : ℂ))) *
      (∏ j, Complex.exp (-(Complex.I * z * (y j : ℂ))))) * ((1 - q)⁻¹ ^ n * (Mq q x y).det) := by ring
    _ = _ := by rw [hexp]; ring

theorem plusOrder_strictAnti {L : ℝ} {m : ℕ} {a b : Fin m → ℝ} (h : PlusOrder L a b) :
    StrictAnti a ∧ StrictAnti b := by
  constructor
  · intro i j hij; exact lt_trans (h.2 i j hij) (h.1 i).2.1
  · intro i j hij; exact lt_trans (h.1 j).2.1 (h.2 i j hij)

theorem plusOrder_iff_Il {L : ℝ} {m : ℕ} {a b : Fin m → ℝ} (ha : ∀ i, 0 < a i ∧ a i < L)
    (hb : ∀ i, 0 < b i ∧ b i < L) : PlusOrder L a b ↔ Il a b :=
  ⟨fun h => ⟨fun j => (h.1 j).2.1, h.2⟩,
    fun h => ⟨fun j => ⟨(hb j).1, h.1 j, (ha j).2⟩, h.2⟩⟩

theorem rawKernel_ne_zero {L : ℝ} {m : ℕ} (z : ℂ) {a b : Fin m → ℝ}
    (h : rawKernel L z a b ≠ 0) : StrictAnti a ∧ StrictAnti b := by
  by_contra hn
  apply h
  have h1 : ¬ PlusOrder L a b := fun hp => hn (plusOrder_strictAnti hp)
  have h2 : ¬ MinusOrder L a b := fun hp => hn (plusOrder_strictAnti hp).symm
  unfold rawKernel rawPlus rawMinus
  rw [if_neg h1, if_neg h2, add_zero]

/-- **Sorted tuples**: `rawKernel L z a b = (1−q) det R_z^ρ(a_i,b_j)` for `a, b` strictly decreasing in `(0,L)`,
no ties, `q = (−1)^n e^{izL} ≠ 1` (`r = n+1`, `ρ_r = (−1)^{r−1} = (−1)^n`). -/
theorem rawKernel_eq_det (L : ℝ) (z : ℂ) (n : ℕ) (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (a b : Fin (n + 1) → ℝ) (ha : StrictAnti a) (hb : StrictAnti b) (hnt : NoTie a b)
    (hab : ∀ i, 0 < a i ∧ a i < L) (hbb : ∀ i, 0 < b i ∧ b i < L) :
    rawKernel L z a b = (1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) *
      (RkMat ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z a b).det := by
  set q : ℂ := (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) with hqdef
  have hq1 : (1 - q) ≠ 0 := sub_ne_zero.2 (Ne.symm hq)
  rw [det_RkMat q z a b hnt, det_Mq_formula n q a b ha hb hnt]
  have hP : PlusOrder L a b ↔ Il a b := plusOrder_iff_Il hab hbb
  have hM : MinusOrder L a b ↔ Il b a := plusOrder_iff_Il hbb hab
  have hqq : (-1 : ℂ) ^ n * q = Complex.exp (Complex.I * z * L) := by
    rw [hqdef, ← mul_assoc, ← mul_pow]; simp
  have hd : Complex.exp (Complex.I * z * L - Complex.I * z * ((∑ j, (b j - a j) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * z * L) * Complex.exp (Complex.I * z * ((∑ i, (a i - b i) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]; congr 1
    have : ((∑ j, (b j - a j) : ℝ) : ℂ) = -((∑ i, (a i - b i) : ℝ) : ℂ) := by
      push_cast; rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [this]; ring
  unfold rawKernel rawPlus rawMinus
  have e1 : (if PlusOrder L a b then Complex.exp (Complex.I * z * (displacement a b : ℝ)) else 0) =
      (if Il a b then Complex.exp (Complex.I * z * ((∑ i, (a i - b i) : ℝ) : ℂ)) else 0) := by
    by_cases h : Il a b
    · rw [if_pos (hP.2 h), if_pos h]; rfl
    · rw [if_neg (fun hh => h (hP.1 hh)), if_neg h]
  have e2 : (if MinusOrder L a b then Complex.exp (Complex.I * z * L - Complex.I * z *
        ((∑ j, (b j - a j) : ℝ) : ℂ)) else 0) =
      (if Il b a then Complex.exp (Complex.I * z * L) *
        Complex.exp (Complex.I * z * ((∑ i, (a i - b i) : ℝ) : ℂ)) else 0) := by
    by_cases h : Il b a
    · rw [if_pos (hM.2 h), if_pos h, hd]
    · rw [if_neg (fun hh => h (hM.1 hh)), if_neg h]
  rw [e1, e2]
  have hpow : (1 - q) ^ n * (1 - q)⁻¹ ^ (n + 1) = (1 - q)⁻¹ := by
    calc (1 - q) ^ n * (1 - q)⁻¹ ^ (n + 1) = (1 - q) ^ n * ((1 - q)⁻¹ ^ n * (1 - q)⁻¹) := by
          rw [pow_succ]
      _ = ((1 - q) * (1 - q)⁻¹) ^ n * (1 - q)⁻¹ := by rw [mul_pow]; ring
      _ = (1 - q)⁻¹ := by rw [mul_inv_cancel₀ hq1, one_pow, one_mul]
  have key : ∀ E S : ℂ, (1 - q) * ((1 - q)⁻¹ ^ (n + 1) * E * ((1 - q) ^ n * S)) = E * S := by
    intro E S
    calc (1 - q) * ((1 - q)⁻¹ ^ (n + 1) * E * ((1 - q) ^ n * S))
        = E * S * ((1 - q) * ((1 - q) ^ n * (1 - q)⁻¹ ^ (n + 1))) := by ring
      _ = E * S := by rw [hpow, mul_inv_cancel₀ hq1, mul_one]
  rw [key]
  by_cases h1 : Il a b <;> by_cases h2 : Il b a
  · simp only [if_pos h1, if_pos h2]
    rw [← hqq]; ring
  · simp only [if_pos h1, if_neg h2]; ring
  · simp only [if_neg h1, if_pos h2]
    rw [← hqq]; ring
  · simp only [if_neg h1, if_neg h2]; simp

/-! #### Sorting permutations -/

/-- The permutation sorting `X` into strictly decreasing order. -/
def sortPerm {m : ℕ} (X : Fin m → ℝ) : Equiv.Perm (Fin m) := Tuple.sort (fun i => -X i)

/-- The ordering sign `sgn(X)`: sign of the permutation which puts the coordinates in decreasing order. -/
def sgnDec {m : ℕ} (X : Fin m → ℝ) : ℂ := ((Equiv.Perm.sign (sortPerm X) : ℤˣ) : ℂ)

theorem sortPerm_strictAnti {m : ℕ} {X : Fin m → ℝ} (hX : Function.Injective X) :
    StrictAnti (X ∘ sortPerm X) := by
  have hmono := Tuple.monotone_sort (fun i => -X i)
  have hanti : Antitone (X ∘ sortPerm X) := fun i j hij => by
    have := hmono hij
    simp only [Function.comp_apply] at this
    show X (sortPerm X j) ≤ X (sortPerm X i)
    unfold sortPerm
    linarith
  exact hanti.strictAnti_of_injective (hX.comp (sortPerm X).injective)

theorem eq_sortPerm {m : ℕ} {X : Fin m → ℝ} {σ : Equiv.Perm (Fin m)} (h : StrictAnti (X ∘ σ)) :
    σ = sortPerm X := by
  unfold sortPerm
  rw [Tuple.eq_sort_iff]
  refine ⟨fun i j hij => ?_, fun i j hij heq => ?_⟩
  · have := h.antitone hij
    simp only [Function.comp_apply] at this ⊢
    linarith
  · have := h hij
    simp only [Function.comp_apply] at this
    linarith

/-- **Exact kernel factorization against the actual DEF-048 averaged kernel.**  For tuples `X, Y` with distinct
coordinates in `(0,L)` and no ties,
`averagedRaw L r z X Y = (1−q)/(r!)² · sgn(X) sgn(Y) · det R_z^ρ(X_i,Y_j)`, i.e. `(1−q)/r!` times the kernel
`sgn(X) sgn(Y) (1/r!) det R(X_i,Y_j)` of `A_r^*(∧^r R) A_r`; `q = ρ_r e^{izL}`, `ρ_r = (−1)^{r−1}`, `r = n+1`. -/
theorem averagedRaw_eq (L : ℝ) [Fact (0 < L)] (n : ℕ) (z : ℂ)
    (hq : (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) ≠ 1)
    (X Y : Fin (n + 1) → ℝ) (hX : Function.Injective X) (hY : Function.Injective Y) (hnt : NoTie X Y)
    (hXb : ∀ i, 0 < X i ∧ X i < L) (hYb : ∀ i, 0 < Y i ∧ Y i < L) :
    averagedRaw L (n + 1) z X Y =
      (((n + 1).factorial : ℂ)⁻¹) ^ 2 * (1 - (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) *
        sgnDec X * sgnDec Y *
        (RkMat ((-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L)) z X Y).det := by
  set q : ℂ := (-1 : ℂ) ^ n * Complex.exp (Complex.I * z * L) with hqdef
  set σX := sortPerm X with hσX
  set σY := sortPerm Y with hσY
  have hXs : StrictAnti (X ∘ σX) := sortPerm_strictAnti hX
  have hYs : StrictAnti (Y ∘ σY) := sortPerm_strictAnti hY
  unfold averagedRaw
  have hout : (∑ σ : Equiv.Perm (Fin (n + 1)), (((n + 1).factorial : ℂ)⁻¹ *
      ∑ τ : Equiv.Perm (Fin (n + 1)), rawKernel L z (X ∘ σ) (Y ∘ τ.symm))) =
      ((n + 1).factorial : ℂ)⁻¹ * ∑ τ : Equiv.Perm (Fin (n + 1)), rawKernel L z (X ∘ σX) (Y ∘ τ.symm) := by
    refine Finset.sum_eq_single σX (fun σ _ hσ => ?_) (fun h => absurd (Finset.mem_univ _) h)
    rw [Finset.sum_eq_zero (fun τ _ => ?_), mul_zero]
    by_contra hne
    exact hσ (eq_sortPerm (rawKernel_ne_zero z hne).1)
  have hin : (∑ τ : Equiv.Perm (Fin (n + 1)), rawKernel L z (X ∘ σX) (Y ∘ τ.symm)) =
      rawKernel L z (X ∘ σX) (Y ∘ σY) := by
    refine Finset.sum_eq_single σY.symm (fun τ _ hτ => ?_) (fun h => absurd (Finset.mem_univ _) h) |>.trans ?_
    · by_contra hne
      have := eq_sortPerm (rawKernel_ne_zero z hne).2
      exact hτ (by rw [← Equiv.symm_symm τ, this, ← hσY])
    · simp
  rw [hout, hin]
  have hdet : (RkMat q z (X ∘ σX) (Y ∘ σY)).det =
      (Equiv.Perm.sign σX : ℂ) * (Equiv.Perm.sign σY : ℂ) * (RkMat q z X Y).det := by
    have : RkMat q z (X ∘ σX) (Y ∘ σY) = ((RkMat q z X Y).submatrix σX id).submatrix id σY := by
      ext i j; simp [RkMat]
    rw [this, Matrix.det_permute', Matrix.det_permute]; ring
  rw [rawKernel_eq_det L z n hq (X ∘ σX) (Y ∘ σY) hXs hYs
    (fun i j => hnt _ _) (fun i => hXb _) (fun i => hYb _), hdet]
  unfold sgnDec
  ring

#print axioms averagedRaw_eq

end Kernel

end QuantumNLS.HaarKernelFactorization
