import Mathlib
import QuantumNLS.CorrelationLatticeBound

/-!
# REG-006 stage (b), item 3: the constrained sum (`CC:G04:correlation`), checkpoint for `q = 2`

Source: `source/chapters/regularity/integer_moments.tex`, lines 176--188 (the Hölder estimate that bounds
the uniform derivative sums). Stage (b) item 3 of the split REG-006 work.

Statement proved here (q = 2, constant 1): with `W(n) = 1 + |n|`, `k ≥ 1`, `α : Fin 2 → ℕ`, `|α| ≤ 2k` and
coefficient families `a_j : ℤ → ℂ` with `Σ_n W(n)^{2k} |a_j(n)|² < ∞`, the family
`n ↦ ∏_j |n_j|^{α_j} ∏_j |a_j(n_j)|` indexed by the constraint set `{n : Σ_j n_j = 0}` is summable, and

  `Σ_{Σn=0} ∏_j |n_j|^{α_j} ∏_j |a_j(n_j)| ≤ N_0 · N_1`,  `N_j = (Σ_n W(n)^{2k}|a_j(n)|²)^{1/2}`.

General `q`: step (i) of the route is proved as `prod_pow_le_sum_Wt_pow`. The full general-`q` statement is
NOT proved here; the exact remaining lemmas are stated at the end of the module docstring.

Route for `q = 2`: the constraint `n_0 + n_1 = 0` is the bijection `x ↦ (x, −x)` with `ℤ`. Then
`∏_j |n_j|^{α_j} ≤ W(x)^{2k}` (because `|α| ≤ 2k`), `W^{2k} = W^k W^k` splits the weight onto the two
factors, and Hölder (`p = q = 2`, Mathlib's tsum Hölder) with the reflection `x ↦ −x` gives the bound.
Nothing else is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.CorrelationConstrainedSum

open QuantumNLS.CorrelationLatticeBound

theorem abs_cast_neg (x : ℤ) : |((-x : ℤ) : ℝ)| = |((x : ℤ) : ℝ)| := by
  push_cast
  exact abs_neg _

theorem Wt_neg (x : ℤ) : Wt (-x) = Wt x := by
  unfold Wt
  rw [abs_cast_neg]

theorem Wt_pow_split (k : ℕ) (x : ℤ) : Wt x ^ (2 * k) = Wt x ^ k * Wt x ^ k := by
  rw [← pow_add]
  congr 1
  ring

/-- `|x|^s · |−x|^t ≤ W(x)^{2k}` whenever `s + t ≤ 2k`. -/
theorem abs_pow_mul_le {k : ℕ} (s t : ℕ) (hst : s + t ≤ 2 * k) (x : ℤ) :
    |((x : ℤ) : ℝ)| ^ s * |((-x : ℤ) : ℝ)| ^ t ≤ Wt x ^ (2 * k) := by
  rw [abs_cast_neg]
  have hu0 : 0 ≤ |((x : ℤ) : ℝ)| := abs_nonneg _
  rw [← pow_add ( |((x : ℤ) : ℝ)| ) s t]
  unfold Wt
  calc |((x : ℤ) : ℝ)| ^ (s + t) ≤ (1 + |((x : ℤ) : ℝ)|) ^ (s + t) :=
        pow_le_pow_left₀ hu0 (by linarith) _
    _ ≤ (1 + |((x : ℤ) : ℝ)|) ^ (2 * k) := pow_le_pow_right₀ (by linarith) hst

/-- The constraint set `{n : Fin 2 → ℤ | n_0 + n_1 = 0}` is in bijection with `ℤ`, `x ↦ (x, −x)`. -/
def sumZeroEquiv : ℤ ≃ {n : Fin 2 → ℤ // ∑ j, n j = 0} where
  toFun x := ⟨![x, -x], by simp [Fin.sum_univ_two]⟩
  invFun n := n.1 0
  left_inv x := by simp
  right_inv n := by
    apply Subtype.ext
    have h := n.2
    rw [Fin.sum_univ_two] at h
    show (![n.1 0, -n.1 0] : Fin 2 → ℤ) = n.1
    funext i
    fin_cases i
    · simp
    · have h1 : n.1 1 = -n.1 0 := by linarith
      simp [h1]

/-- **Constrained sum, `q = 2`.** For `k ≥ 1`, `|α| ≤ 2k`, and coefficient families with finite weighted
ℓ² norms, the constrained family is summable and bounded by the product of the two ℓ² norms. -/
theorem constrained_bound_two {k : ℕ} (hk : 1 ≤ k) (α : Fin 2 → ℕ) (hα : ∑ j, α j ≤ 2 * k)
    (a : Fin 2 → ℤ → ℂ) (ha : ∀ j, Summable fun x : ℤ => Wt x ^ (2 * k) * ‖a j x‖ ^ 2) :
    Summable (fun n : {n : Fin 2 → ℤ // ∑ j, n j = 0} =>
        (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖) ∧
      ∑' n : {n : Fin 2 → ℤ // ∑ j, n j = 0},
          (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖ ≤
        Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖a 0 x‖ ^ 2) *
          Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖a 1 x‖ ^ 2) := by
  have hα2 : α 0 + α 1 ≤ 2 * k := by
    have := hα
    rw [Fin.sum_univ_two] at this
    exact this
  set f : ℤ → ℝ := fun x => Wt x ^ k * ‖a 0 x‖ with hf
  set g : ℤ → ℝ := fun x => Wt x ^ k * ‖a 1 (-x)‖ with hg
  have hf0 : ∀ x, 0 ≤ f x := fun x => mul_nonneg (pow_nonneg (Wt_pos x).le _) (norm_nonneg _)
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (pow_nonneg (Wt_pos x).le _) (norm_nonneg _)
  have hfsq : ∀ x, f x ^ (2 : ℝ) = Wt x ^ (2 * k) * ‖a 0 x‖ ^ 2 := by
    intro x
    rw [Real.rpow_two]
    simp only [hf]
    rw [mul_pow, ← pow_mul, mul_comm k 2]
  have hgsq : ∀ x, g x ^ (2 : ℝ) = Wt (-x) ^ (2 * k) * ‖a 1 (-x)‖ ^ 2 := by
    intro x
    rw [Real.rpow_two, Wt_neg]
    simp only [hg]
    rw [mul_pow, ← pow_mul, mul_comm k 2]
  have hfs : Summable fun x => f x ^ (2 : ℝ) := by
    refine (ha 0).congr (fun x => ?_)
    exact (hfsq x).symm
  have hgs : Summable fun x => g x ^ (2 : ℝ) := by
    have h1 : Summable fun x : ℤ => Wt (-x) ^ (2 * k) * ‖a 1 (-x)‖ ^ 2 :=
      (Equiv.neg ℤ).summable_iff.2 (ha 1)
    exact h1.congr (fun x => (hgsq x).symm)
  obtain ⟨hsumfg, hineq⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two hf0 hg0 hfs hgs
  have e1 : ∑' x, f x ^ (2 : ℝ) = ∑' x : ℤ, Wt x ^ (2 * k) * ‖a 0 x‖ ^ 2 :=
    tsum_congr hfsq
  have e2 : ∑' x, g x ^ (2 : ℝ) = ∑' x : ℤ, Wt x ^ (2 * k) * ‖a 1 x‖ ^ 2 := by
    rw [tsum_congr hgsq]
    exact (Equiv.neg ℤ).tsum_eq (fun y : ℤ => Wt y ^ (2 * k) * ‖a 1 y‖ ^ 2)
  -- the summand on the constraint set, pulled back to `ℤ`
  set F : {n : Fin 2 → ℤ // ∑ j, n j = 0} → ℝ := fun n =>
    (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖ with hF
  have hFnn : ∀ n, 0 ≤ F n := fun n =>
    mul_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (abs_nonneg _) _)
      (Finset.prod_nonneg fun j _ => norm_nonneg _)
  have hFe : ∀ x : ℤ, F (sumZeroEquiv x) ≤ f x * g x := by
    intro x
    simp only [hF, sumZeroEquiv, Equiv.coe_fn_mk, Fin.prod_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    have hm := abs_pow_mul_le (k := k) (α 0) (α 1) hα2 x
    have hC : 0 ≤ ‖a 0 x‖ * ‖a 1 (-x)‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hAB : 0 ≤ |((x : ℤ) : ℝ)| ^ α 0 * |((-x : ℤ) : ℝ)| ^ α 1 :=
      mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _)
    calc |((x : ℤ) : ℝ)| ^ α 0 * |((-x : ℤ) : ℝ)| ^ α 1 * (‖a 0 x‖ * ‖a 1 (-x)‖)
        ≤ Wt x ^ (2 * k) * (‖a 0 x‖ * ‖a 1 (-x)‖) := mul_le_mul_of_nonneg_right hm hC
      _ = f x * g x := by
          simp only [hf, hg]
          rw [Wt_pow_split]
          ring
  have hsumFe : Summable fun x : ℤ => F (sumZeroEquiv x) :=
    Summable.of_nonneg_of_le (fun x => hFnn _) hFe hsumfg
  have hsumF : Summable F := (sumZeroEquiv.summable_iff).1 hsumFe
  refine ⟨hsumF, ?_⟩
  rw [← sumZeroEquiv.tsum_eq F]
  calc ∑' x : ℤ, F (sumZeroEquiv x) ≤ ∑' x : ℤ, f x * g x :=
        Summable.tsum_le_tsum hFe hsumFe hsumfg
    _ ≤ (∑' x, f x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑' x, g x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hineq
    _ = Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖a 0 x‖ ^ 2) *
          Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖a 1 x‖ ^ 2) := by
          rw [e1, e2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Step (i), general `q`.** For `|α| ≤ 2k` and `q ≥ 1`: `∏_j |n_j|^{α_j} ≤ Σ_i W(n_i)^{2k}`.
The largest coordinate dominates the product, and `W(max)^{2k}` is one of the summands. -/
theorem prod_pow_le_sum_Wt_pow {q k : ℕ} (hq : 0 < q) (α : Fin q → ℕ) (hα : ∑ j, α j ≤ 2 * k)
    (n : Fin q → ℤ) :
    ∏ j, |((n j : ℤ) : ℝ)| ^ α j ≤ ∑ i, Wt (n i) ^ (2 * k) := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => |((n j : ℤ) : ℝ)|)
    ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  set M : ℝ := |((n i0 : ℤ) : ℝ)| with hM
  have hM0 : 0 ≤ M := abs_nonneg _
  have hle : ∀ j, |((n j : ℤ) : ℝ)| ≤ M := fun j => hi0 j (Finset.mem_univ j)
  have h1 : ∏ j, |((n j : ℤ) : ℝ)| ^ α j ≤ ∏ j, M ^ α j := by
    gcongr with j _
    exact hle j
  have h2 : ∏ j, M ^ α j = M ^ (∑ j, α j) := Finset.prod_pow_eq_pow_sum _ _ _
  have h3 : M ^ (∑ j, α j) ≤ (1 + M) ^ (2 * k) :=
    calc M ^ (∑ j, α j) ≤ (1 + M) ^ (∑ j, α j) := pow_le_pow_left₀ hM0 (by linarith) _
      _ ≤ (1 + M) ^ (2 * k) := pow_le_pow_right₀ (by linarith) hα
  have h4 : (1 + M) ^ (2 * k) = Wt (n i0) ^ (2 * k) := by
    unfold Wt
    rw [hM]
  have h5 : Wt (n i0) ^ (2 * k) ≤ ∑ i, Wt (n i) ^ (2 * k) :=
    Finset.single_le_sum (f := fun i => Wt (n i) ^ (2 * k))
      (fun i _ => pow_nonneg (Wt_pos _).le _) (Finset.mem_univ i0)
  calc ∏ j, |((n j : ℤ) : ℝ)| ^ α j ≤ ∏ j, M ^ α j := h1
    _ = M ^ (∑ j, α j) := h2
    _ ≤ (1 + M) ^ (2 * k) := h3
    _ = Wt (n i0) ^ (2 * k) := h4
    _ ≤ ∑ i, Wt (n i) ^ (2 * k) := h5

end QuantumNLS.CorrelationConstrainedSum

/-! Axiom audit (every declaration of the checkpoint). -/
#print axioms QuantumNLS.CorrelationConstrainedSum.constrained_bound_two
#print axioms QuantumNLS.CorrelationConstrainedSum.prod_pow_le_sum_Wt_pow
#print axioms QuantumNLS.CorrelationConstrainedSum.abs_pow_mul_le
#print axioms QuantumNLS.CorrelationConstrainedSum.sumZeroEquiv
#print axioms QuantumNLS.CorrelationConstrainedSum.Wt_neg
#print axioms QuantumNLS.CorrelationConstrainedSum.Wt_pow_split
#print axioms QuantumNLS.CorrelationConstrainedSum.abs_cast_neg
