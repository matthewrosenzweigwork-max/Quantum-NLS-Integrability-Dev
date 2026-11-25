import Mathlib
import QuantumNLS.CorrelationConstrainedSum

/-!
# REG-006 stage (b), item 3, general `q`: the constrained sum (`CC:G04:correlation`)

Source: `source/chapters/regularity/integer_moments.tex`, lines 176--188. Stage (b) item 3 of the split
REG-006 work, extending the `q = 2` checkpoint `QuantumNLS.CorrelationConstrainedSum` (read-only import).

Target (general `q = m + 2 ≥ 2`, `k ≥ 1`, `|α| ≤ 2k`, `W(n) = 1 + |n|`, `b_j(x) = ‖a_j(x)‖`), with
`N_j = (Σ_x W(x)^{2k} b_j(x)²)^{1/2}` and `C_k = (Σ_x W(x)^{-2k})^{1/2}`:

  `Σ_{Σn = 0} ∏_j |n_j|^{α_j} ∏_j b_j(n_j) ≤ (2^k)^m · (q(q−1)) · C_k^q · ∏_j N_j`, summable.

Route (all steps proved in this file):
1. `prod_pow_le_sum_Wt_pow` (imported): `∏_j |n_j|^{α_j} ≤ Σ_i W(n_i)^{2k}`.
2. Peetre on the constraint (`Wt_sum_pow_le`, `Wt_constraint_pow_le`): `W(n_i)^k ≤ (2^k)^m Σ_l W(n_{i∘succAbove l})^k`.
   Hence `W(n_i)^{2k} ∏_j b_j ≤ (2^k)^m Σ_l W(n_i)^k W(n_{i'})^k ∏_j b_j`, `i' = i.succAbove l`.
3. Each pair term is a product `∏_j g_j(n_j)` with weight `W^k` on the two coordinates `i, i'` (ℓ²) and
   plain `b_j` elsewhere (ℓ¹). The pair bound (`pair_bound`) uses the q-fold Fubini identity
   (`prod_real_aux`, from the frozen `CorrelationFourierBridge.prod_tsum_aux`), the parametrisation
   `cEquiv` of the constraint set by `(ρ, x)`, and the shift Cauchy estimate `shift_cauchy`:
   `Σ_x f(x) g(−x − s) ≤ ‖f‖₂ ‖g‖₂` uniformly in `s`.
4. Permutations (`perm_tsum_all`, `exists_perm_pair`) move an arbitrary pair `(i, i')` to `(0, 1)`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.CorrelationConstrainedSumGen

open QuantumNLS.CorrelationLatticeBound QuantumNLS.CorrelationConstrainedSum

/-- Peetre-type inequality for a finite sum: `W(Σ_j x_j)^k ≤ (2^k)^m Σ_j W(x_j)^k` on `Fin (m+1)`. -/
theorem Wt_sum_pow_le (k : ℕ) : ∀ (m : ℕ) (x : Fin (m + 1) → ℤ),
    Wt (∑ j, x j) ^ k ≤ ((2 : ℝ) ^ k) ^ m * ∑ j, Wt (x j) ^ k
  | 0, x => by simp
  | m + 1, x => by
    have ih : Wt (∑ j : Fin (m + 1), x j.succ) ^ k ≤
        ((2 : ℝ) ^ k) ^ m * ∑ j : Fin (m + 1), Wt (x j.succ) ^ k :=
      Wt_sum_pow_le k m (fun j => x j.succ)
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ (fun j => Wt (x j) ^ k)]
    have h1 := Wt_pow_le k (x 0 + ∑ j : Fin (m + 1), x j.succ) (x 0)
    rw [add_sub_cancel_left] at h1
    have hA : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    have hB : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ (m + 1) := le_self_pow₀ hA (Nat.succ_ne_zero m)
    have hW0 : 0 ≤ Wt (x 0) ^ k := pow_nonneg (Wt_pos _).le _
    have hpow : (2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ m = ((2 : ℝ) ^ k) ^ (m + 1) := (pow_succ' _ _).symm
    calc Wt (x 0 + ∑ j : Fin (m + 1), x j.succ) ^ k
        ≤ (2 : ℝ) ^ k * (Wt (x 0) ^ k + Wt (∑ j : Fin (m + 1), x j.succ) ^ k) := h1
      _ ≤ (2 : ℝ) ^ k * (Wt (x 0) ^ k + ((2 : ℝ) ^ k) ^ m * ∑ j : Fin (m + 1), Wt (x j.succ) ^ k) := by
          gcongr
      _ = (2 : ℝ) ^ k * Wt (x 0) ^ k + ((2 : ℝ) ^ k * ((2 : ℝ) ^ k) ^ m) *
            ∑ j : Fin (m + 1), Wt (x j.succ) ^ k := by ring
      _ ≤ ((2 : ℝ) ^ k) ^ (m + 1) * Wt (x 0) ^ k + ((2 : ℝ) ^ k) ^ (m + 1) *
            ∑ j : Fin (m + 1), Wt (x j.succ) ^ k := by
          rw [hpow]
          exact add_le_add (mul_le_mul_of_nonneg_right hB hW0) le_rfl
      _ = ((2 : ℝ) ^ k) ^ (m + 1) * (Wt (x 0) ^ k + ∑ j : Fin (m + 1), Wt (x j.succ) ^ k) := by ring

/-- Peetre on the constraint: if `Σ_j x_j = 0` on `Fin (m+2)`, then
`W(x_i)^k ≤ (2^k)^m Σ_{l} W(x_{i.succAbove l})^k` for every `i`. -/
theorem Wt_constraint_pow_le {m k : ℕ} (x : Fin (m + 2) → ℤ) (hx : ∑ j, x j = 0) (i : Fin (m + 2)) :
    Wt (x i) ^ k ≤ ((2 : ℝ) ^ k) ^ m * ∑ l : Fin (m + 1), Wt (x (i.succAbove l)) ^ k := by
  have hsplit : ∑ j, x j = x i + ∑ l : Fin (m + 1), x (i.succAbove l) :=
    Fin.sum_univ_succAbove x i
  have hneg : x i = -∑ l : Fin (m + 1), x (i.succAbove l) := by linarith
  have h : Wt (∑ l : Fin (m + 1), x (i.succAbove l)) ^ k ≤
      ((2 : ℝ) ^ k) ^ m * ∑ l : Fin (m + 1), Wt (x (i.succAbove l)) ^ k :=
    Wt_sum_pow_le k m (fun l => x (i.succAbove l))
  rw [hneg, Wt_neg]
  exact h

/-- Real-valued Fubini for a product over `Fin m → ℤ` of nonnegative summable families. -/
theorem prod_real_aux (m : ℕ) (g : Fin m → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (hgs : ∀ j, Summable (g j)) :
    Summable (fun ρ : Fin m → ℤ => ∏ j, g j (ρ j)) ∧
      ∏ j, (∑' x, g j x) = ∑' ρ : Fin m → ℤ, ∏ j, g j (ρ j) := by
  cases m with
  | zero =>
    refine ⟨Summable.of_finite, ?_⟩
    simp [tsum_fintype]
  | succ m' =>
    have hu : ∀ j, Summable fun n => ‖(fun j n => ((g j n : ℝ) : ℂ)) j n‖ := by
      intro j
      exact (hgs j).congr (fun n => by simp [Complex.norm_real, Real.norm_of_nonneg (hg0 j n)])
    obtain ⟨h1, h2⟩ := QuantumNLS.CorrelationFourierBridge.prod_tsum_aux m'
      (fun j n => ((g j n : ℝ) : ℂ)) hu
    have hnorm : ∀ ρ : Fin (m' + 1) → ℤ, ‖∏ j, ((g j (ρ j) : ℝ) : ℂ)‖ = ∏ j, g j (ρ j) := by
      intro ρ
      rw [norm_prod]
      exact Finset.prod_congr rfl (fun j _ => by
        rw [Complex.norm_real, Real.norm_of_nonneg (hg0 j _)])
    refine ⟨h1.congr (fun ρ => hnorm ρ), ?_⟩
    apply Complex.ofReal_injective
    rw [Complex.ofReal_prod, Complex.ofReal_tsum]
    simp only [Complex.ofReal_tsum, Complex.ofReal_prod]
    exact h2

/-- The shift `x ↦ -x - s` as an involution of `ℤ`. -/
def shiftEquiv (s : ℤ) : ℤ ≃ ℤ where
  toFun x := -x - s
  invFun y := -y - s
  left_inv x := by show -(-x - s) - s = x; ring
  right_inv y := by show -(-y - s) - s = y; ring

/-- Shift Cauchy estimate: `Σ_x f(x) g(−x − s) ≤ (Σ f²)^{1/2} (Σ g²)^{1/2}`, uniformly in `s`. -/
theorem shift_cauchy (f g : ℤ → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfs : Summable fun x => f x ^ 2) (hgs : Summable fun x => g x ^ 2) (s : ℤ) :
    Summable (fun x => f x * g (-x - s)) ∧
      ∑' x, f x * g (-x - s) ≤ Real.sqrt (∑' x, f x ^ 2) * Real.sqrt (∑' x, g x ^ 2) := by
  have hgE : Summable fun x => g (-x - s) ^ 2 :=
    ((shiftEquiv s).summable_iff).2 hgs
  have hfs' : Summable fun x => f x ^ (2 : ℝ) := by simpa only [Real.rpow_two] using hfs
  have hgs' : Summable fun x => (fun x => g (-x - s)) x ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using hgE
  obtain ⟨hsum, hineq⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two hf0
    (fun x => hg0 (-x - s)) hfs' hgs'
  have e1 : ∑' x, f x ^ (2 : ℝ) = ∑' x, f x ^ 2 := tsum_congr (fun x => Real.rpow_two _)
  have e2 : ∑' x, (fun x => g (-x - s)) x ^ (2 : ℝ) = ∑' x, g x ^ 2 := by
    rw [tsum_congr (fun x => Real.rpow_two ((fun x => g (-x - s)) x))]
    exact (shiftEquiv s).tsum_eq (fun y => g y ^ 2)
  refine ⟨hsum, ?_⟩
  calc ∑' x, f x * g (-x - s) ≤ (∑' x, f x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
        (∑' x, (fun x => g (-x - s)) x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := hineq
    _ = Real.sqrt (∑' x, f x ^ 2) * Real.sqrt (∑' x, g x ^ 2) := by
          rw [e1, e2, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- Parametrisation of the constraint set `{n : Fin (m+2) → ℤ | Σ n = 0}` by the free coordinates
`(ρ, x) ↦ n` with `n_0 = x`, `n_1 = −x − Σ_j ρ_j`, `n_{j+2} = ρ_j`. -/
def cEquiv (m : ℕ) : (Fin m → ℤ) × ℤ ≃ {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} where
  toFun p := ⟨(Fin.cons (α := fun _ : Fin (m + 2) => ℤ) p.2
      (Fin.cons (α := fun _ : Fin (m + 1) => ℤ) (-p.2 - ∑ j, p.1 j) p.1) : Fin (m + 2) → ℤ), by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    ring⟩
  invFun n := (fun j => n.1 j.succ.succ, n.1 0)
  left_inv p := by
    simp
  right_inv n := by
    apply Subtype.ext
    have h := n.2
    simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one] at h
    dsimp only
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp
    · refine Fin.cases ?_ (fun j => ?_) i'
      · rw [Fin.cons_succ, Fin.cons_zero, Fin.succ_zero_eq_one]
        linarith
      · simp

/-- The summand on the parametrised constraint set: `(ρ, x) ↦ P(ρ) · g_0(x) · g_1(−x − Σρ)`, where
`P(ρ) = ∏_{j} g_{j+2}(ρ_j)`. -/
def pairTerm {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (p : (Fin m → ℤ) × ℤ) : ℝ :=
  (∏ j : Fin m, g j.succ.succ (p.1 j)) * (g 0 p.2 * g 1 (-p.2 - ∑ j, p.1 j))

theorem cEquiv_pair {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (p : (Fin m → ℤ) × ℤ) :
    ∏ j, g j ((cEquiv m p).1 j) = pairTerm g p := by
  unfold pairTerm
  show ∏ j, g j ((Fin.cons (α := fun _ : Fin (m + 2) => ℤ) p.2
    (Fin.cons (α := fun _ : Fin (m + 1) => ℤ) (-p.2 - ∑ j, p.1 j) p.1) : Fin (m + 2) → ℤ) j) = _
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.succ_zero_eq_one]
  ring

theorem pairTerm_nonneg {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (p : (Fin m → ℤ) × ℤ) : 0 ≤ pairTerm g p :=
  mul_nonneg (Finset.prod_nonneg fun j _ => hg0 _ _) (mul_nonneg (hg0 _ _) (hg0 _ _))

theorem pairTerm_inner {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (ρ : Fin m → ℤ) :
    ∑' x, pairTerm g (ρ, x) =
      (∏ j : Fin m, g j.succ.succ (ρ j)) * ∑' x, g 0 x * g 1 (-x - ∑ j, ρ j) := by
  simp only [pairTerm]
  exact tsum_mul_left

theorem pairTerm_inner_summable {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (h0 : Summable fun x => g 0 x ^ 2) (h1 : Summable fun x => g 1 x ^ 2) (ρ : Fin m → ℤ) :
    Summable fun x => pairTerm g (ρ, x) := by
  have h := (shift_cauchy (g 0) (g 1) (fun x => hg0 0 x) (fun x => hg0 1 x) h0 h1
    (∑ j, ρ j)).1.mul_left (∏ j : Fin m, g j.succ.succ (ρ j))
  simp only [pairTerm]
  exact h

theorem pairTerm_inner_le {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (h0 : Summable fun x => g 0 x ^ 2) (h1 : Summable fun x => g 1 x ^ 2) (ρ : Fin m → ℤ) :
    ∑' x, pairTerm g (ρ, x) ≤
      (∏ j : Fin m, g j.succ.succ (ρ j)) *
        (Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2)) := by
  rw [pairTerm_inner]
  exact mul_le_mul_of_nonneg_left
    (shift_cauchy (g 0) (g 1) (fun x => hg0 0 x) (fun x => hg0 1 x) h0 h1 (∑ j, ρ j)).2
    (Finset.prod_nonneg fun j _ => hg0 _ _)

theorem pairTerm_outer_summable {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (h0 : Summable fun x => g 0 x ^ 2) (h1 : Summable fun x => g 1 x ^ 2)
    (hr : ∀ j : Fin m, Summable (g j.succ.succ)) :
    Summable fun ρ : Fin m → ℤ => ∑' x, pairTerm g (ρ, x) := by
  obtain ⟨hPs, -⟩ := prod_real_aux m (fun j => g j.succ.succ) (fun j x => hg0 _ x) hr
  have hPs' : Summable (fun ρ : Fin m → ℤ => ∏ j : Fin m, g j.succ.succ (ρ j)) := hPs
  refine Summable.of_nonneg_of_le (fun ρ => tsum_nonneg fun x => pairTerm_nonneg g hg0 _)
    (fun ρ => pairTerm_inner_le g hg0 h0 h1 ρ)
    (hPs'.mul_right (Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2)))

theorem pairTerm_summable {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (h0 : Summable fun x => g 0 x ^ 2) (h1 : Summable fun x => g 1 x ^ 2)
    (hr : ∀ j : Fin m, Summable (g j.succ.succ)) :
    Summable (pairTerm g) :=
  (summable_prod_of_nonneg (f := pairTerm g) (fun p => pairTerm_nonneg g hg0 p)).2
    ⟨fun ρ => pairTerm_inner_summable g hg0 h0 h1 ρ,
      pairTerm_outer_summable g hg0 h0 h1 hr⟩

theorem pairTerm_tsum_bound {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (h0 : Summable fun x => g 0 x ^ 2) (h1 : Summable fun x => g 1 x ^ 2)
    (hr : ∀ j : Fin m, Summable (g j.succ.succ)) :
    ∑' p, pairTerm g p ≤
      Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2) *
        ∏ j : Fin m, ∑' x, g j.succ.succ x := by
  obtain ⟨hPs, hPsum⟩ := prod_real_aux m (fun j => g j.succ.succ) (fun j x => hg0 _ x) hr
  have hPs' : Summable (fun ρ : Fin m → ℤ => ∏ j : Fin m, g j.succ.succ (ρ j)) := hPs
  have hPsum' : ∏ j : Fin m, ∑' x, g j.succ.succ x =
      ∑' ρ : Fin m → ℤ, ∏ j : Fin m, g j.succ.succ (ρ j) := hPsum
  calc ∑' p, pairTerm g p
      = ∑' ρ : Fin m → ℤ, ∑' x, pairTerm g (ρ, x) :=
        (pairTerm_summable g hg0 h0 h1 hr).tsum_prod'
          (fun ρ => pairTerm_inner_summable g hg0 h0 h1 ρ)
    _ ≤ ∑' ρ : Fin m → ℤ, (∏ j : Fin m, g j.succ.succ (ρ j)) *
          (Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2)) :=
        Summable.tsum_le_tsum (fun ρ => pairTerm_inner_le g hg0 h0 h1 ρ)
          (pairTerm_outer_summable g hg0 h0 h1 hr)
          (hPs'.mul_right _)
    _ = (∑' ρ : Fin m → ℤ, ∏ j : Fin m, g j.succ.succ (ρ j)) *
          (Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2)) := tsum_mul_right
    _ = Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2) *
          ∏ j : Fin m, ∑' x, g j.succ.succ x := by
        rw [hPsum']
        ring

/-- Two `ℓ²` coordinates (positions `0`, `1`) and `ℓ¹` coordinates (positions `j.succ.succ`) on the
constraint set: the Fubini/Cauchy estimate. -/
theorem two_l2_bound (m : ℕ) (g : Fin (m + 2) → ℤ → ℝ) (hg0 : ∀ j x, 0 ≤ g j x)
    (h0 : Summable fun x => g 0 x ^ 2) (h1 : Summable fun x => g 1 x ^ 2)
    (hr : ∀ j : Fin m, Summable (g j.succ.succ)) :
    Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j)) ∧
      ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, g j (n.1 j) ≤
        Real.sqrt (∑' x, g 0 x ^ 2) * Real.sqrt (∑' x, g 1 x ^ 2) *
          ∏ j : Fin m, ∑' x, g j.succ.succ x := by
  have hsumG : Summable (pairTerm g) := pairTerm_summable g hg0 h0 h1 hr
  have hEq : ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, g j (n.1 j) =
      ∑' p, pairTerm g p := by
    rw [← (cEquiv m).tsum_eq (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j))]
    exact tsum_congr fun p => cEquiv_pair g p
  have hSumF : Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j)) := by
    refine (cEquiv m).summable_iff.1 ?_
    exact hsumG.congr fun p => (cEquiv_pair g p).symm
  refine ⟨hSumF, ?_⟩
  rw [hEq]
  exact pairTerm_tsum_bound g hg0 h0 h1 hr

/-- Coordinate permutation of the constraint set `{n | Σ n = 0}`. -/
def permC {q : ℕ} (σ : Equiv.Perm (Fin q)) :
    {n : Fin q → ℤ // ∑ j, n j = 0} ≃ {n : Fin q → ℤ // ∑ j, n j = 0} where
  toFun n := ⟨fun j => n.1 (σ j), by
    show ∑ j, n.1 (σ j) = 0
    rw [Equiv.sum_comp σ n.1]
    exact n.2⟩
  invFun n := ⟨fun j => n.1 (σ.symm j), by
    show ∑ j, n.1 (σ.symm j) = 0
    rw [Equiv.sum_comp σ.symm n.1]
    exact n.2⟩
  left_inv n := by
    apply Subtype.ext
    funext j
    simp
  right_inv n := by
    apply Subtype.ext
    funext j
    simp

theorem perm_prod {q : ℕ} (σ : Equiv.Perm (Fin q)) (g : Fin q → ℤ → ℝ) (n : Fin q → ℤ) :
    ∏ j, g j (n (σ j)) = ∏ j, g (σ.symm j) (n j) := by
  have h := Equiv.prod_comp σ (fun j => g (σ.symm j) (n j))
  simp only [Equiv.symm_apply_apply] at h
  exact h

/-- Permuting the families on the constraint set: summability and the sum are invariant. -/
theorem perm_tsum_all {q : ℕ} (τ : Equiv.Perm (Fin q)) (g : Fin q → ℤ → ℝ) :
    (Summable (fun n : {n : Fin q → ℤ // ∑ j, n j = 0} => ∏ j, g (τ j) (n.1 j)) ↔
      Summable (fun n : {n : Fin q → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j))) ∧
    ∑' n : {n : Fin q → ℤ // ∑ j, n j = 0}, ∏ j, g (τ j) (n.1 j) =
      ∑' n : {n : Fin q → ℤ // ∑ j, n j = 0}, ∏ j, g j (n.1 j) := by
  have key : (fun n : {n : Fin q → ℤ // ∑ j, n j = 0} => ∏ j, g (τ j) (n.1 j)) =
      (fun n : {n : Fin q → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j)) ∘ (permC τ.symm) := by
    funext n
    show ∏ j, g (τ j) (n.1 j) = ∏ j, g j (n.1 (τ.symm j))
    exact (perm_prod τ.symm g n.1).symm
  rw [key]
  exact ⟨(permC τ.symm).summable_iff,
    (permC τ.symm).tsum_eq (fun n : {n : Fin q → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j))⟩

/-- Every ordered pair of distinct indices is moved to `(0, 1)` by a permutation. -/
theorem exists_perm_pair {m : ℕ} (i i' : Fin (m + 2)) (hne : i ≠ i') :
    ∃ τ : Equiv.Perm (Fin (m + 2)), τ 0 = i ∧ τ 1 = i' := by
  have hl0 : Equiv.swap (0 : Fin (m + 2)) i i' ≠ 0 := by
    intro h
    apply hne
    have h2 := congrArg (Equiv.swap (0 : Fin (m + 2)) i) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h2
    exact h2.symm
  refine ⟨Equiv.swap (0 : Fin (m + 2)) i *
    Equiv.swap (1 : Fin (m + 2)) (Equiv.swap 0 i i'), ?_, ?_⟩
  · show Equiv.swap (0 : Fin (m + 2)) i (Equiv.swap (1 : Fin (m + 2)) (Equiv.swap 0 i i') 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne zero_ne_one (Ne.symm hl0), Equiv.swap_apply_left]
  · show Equiv.swap (0 : Fin (m + 2)) i (Equiv.swap (1 : Fin (m + 2)) (Equiv.swap 0 i i') 1) = i'
    rw [Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Pair bound: for distinct `i ≠ i'`, the family with `ℓ²` coordinates at `i, i'` and `ℓ¹` coordinates
elsewhere satisfies the bound `∏_j D_j` on the constraint set. -/
theorem pair_bound {m : ℕ} (g : Fin (m + 2) → ℤ → ℝ) (D : Fin (m + 2) → ℝ)
    (hg0 : ∀ j x, 0 ≤ g j x) (hD : ∀ j, 0 ≤ D j) (i i' : Fin (m + 2)) (hne : i ≠ i')
    (hi : Summable fun x => g i x ^ 2) (hi' : Summable fun x => g i' x ^ 2)
    (hli : Real.sqrt (∑' x, g i x ^ 2) ≤ D i) (hli' : Real.sqrt (∑' x, g i' x ^ 2) ≤ D i')
    (hl : ∀ j, j ≠ i → j ≠ i' → Summable (g j))
    (hlb : ∀ j, j ≠ i → j ≠ i' → ∑' x, g j x ≤ D j) :
    Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} => ∏ j, g j (n.1 j)) ∧
      ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, g j (n.1 j) ≤ ∏ j, D j := by
  obtain ⟨τ, hτ0, hτ1⟩ := exists_perm_pair i i' hne
  have hss0 : ∀ j : Fin m, (j.succ.succ : Fin (m + 2)) ≠ 0 := fun j => Fin.succ_ne_zero _
  have hss1 : ∀ j : Fin m, (j.succ.succ : Fin (m + 2)) ≠ 1 := fun j => Fin.succ_succ_ne_one j
  have hτi : ∀ j : Fin m, τ j.succ.succ ≠ i := by
    intro j h
    apply hss0 j
    apply τ.injective
    rw [h, hτ0]
  have hτi' : ∀ j : Fin m, τ j.succ.succ ≠ i' := by
    intro j h
    apply hss1 j
    apply τ.injective
    rw [h, hτ1]
  have h0' : Summable fun x => (fun j => g (τ j)) 0 x ^ 2 := by
    show Summable fun x => g (τ 0) x ^ 2
    rw [hτ0]
    exact hi
  have h1' : Summable fun x => (fun j => g (τ j)) 1 x ^ 2 := by
    show Summable fun x => g (τ 1) x ^ 2
    rw [hτ1]
    exact hi'
  have hr' : ∀ j : Fin m, Summable ((fun j => g (τ j)) j.succ.succ) := fun j =>
    hl _ (hτi j) (hτi' j)
  obtain ⟨hS, hB⟩ := two_l2_bound m (fun j => g (τ j)) (fun j x => hg0 _ x) h0' h1' hr'
  obtain ⟨hPs, hPt⟩ := perm_tsum_all τ g
  refine ⟨hPs.1 hS, ?_⟩
  have hA : Real.sqrt (∑' x, (fun j => g (τ j)) 0 x ^ 2) ≤ D i := by
    show Real.sqrt (∑' x, g (τ 0) x ^ 2) ≤ D i
    rw [hτ0]
    exact hli
  have hA' : Real.sqrt (∑' x, (fun j => g (τ j)) 1 x ^ 2) ≤ D i' := by
    show Real.sqrt (∑' x, g (τ 1) x ^ 2) ≤ D i'
    rw [hτ1]
    exact hli'
  have hprod : ∏ j : Fin m, ∑' x, (fun j => g (τ j)) j.succ.succ x ≤
      ∏ j : Fin m, D (τ j.succ.succ) :=
    Finset.prod_le_prod₀ (fun j _ => tsum_nonneg fun x => hg0 _ x)
      (fun j _ => hlb _ (hτi j) (hτi' j))
  have hfin := mul_le_mul (mul_le_mul hA hA' (Real.sqrt_nonneg _) (hD i)) hprod
    (Finset.prod_nonneg fun j _ => tsum_nonneg fun x => hg0 _ x) (mul_nonneg (hD i) (hD i'))
  have hD' : ∏ j, D j = D i * (D i' * ∏ j : Fin m, D (τ j.succ.succ)) := by
    rw [← Equiv.prod_comp τ D, Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.succ_zero_eq_one,
      hτ0, hτ1]
  calc ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, g j (n.1 j)
      = ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, g (τ j) (n.1 j) := hPt.symm
    _ ≤ Real.sqrt (∑' x, (fun j => g (τ j)) 0 x ^ 2) * Real.sqrt (∑' x, (fun j => g (τ j)) 1 x ^ 2) *
          ∏ j : Fin m, ∑' x, (fun j => g (τ j)) j.succ.succ x := hB
    _ ≤ D i * D i' * ∏ j : Fin m, D (τ j.succ.succ) := hfin
    _ = ∏ j, D j := by rw [hD']; ring

/-- The constant `C_k = (Σ_x W(x)^{-2k})^{1/2}`. -/
def Ckc (k : ℕ) : ℝ := Real.sqrt (∑' x : ℤ, (Wt x ^ (2 * k))⁻¹)

/-- The weighted norm `N_j = (Σ_x W(x)^{2k} ‖a_j(x)‖²)^{1/2}`. -/
def Nc {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) (j : Fin q) : ℝ :=
  Real.sqrt (∑' x : ℤ, Wt x ^ (2 * k) * ‖a j x‖ ^ 2)

theorem Ckc_ge_one {k : ℕ} (hk : 1 ≤ k) : 1 ≤ Ckc k := by
  unfold Ckc
  rw [Real.one_le_sqrt]
  have hle := (Wt_inv_summable hk).le_tsum 0
    (fun j _ => inv_nonneg.2 (pow_nonneg (Wt_pos j).le _))
  have h0 : (Wt 0 ^ (2 * k))⁻¹ = 1 := by simp [Wt]
  linarith

/-- Weighted family of an ordered pair: `‖a_j(x)‖ · W(x)^k` for `j ∈ {i, i'}`, else `‖a_j(x)‖`. -/
def vfam {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) (i i' j : Fin q) (x : ℤ) : ℝ :=
  ‖a j x‖ * (if j = i ∨ j = i' then Wt x ^ k else 1)

theorem vfam_nonneg {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) (i i' j : Fin q) (x : ℤ) :
    0 ≤ vfam a k i i' j x := by
  unfold vfam
  have h : (0 : ℝ) ≤ (if j = i ∨ j = i' then Wt x ^ k else 1) := by
    split_ifs
    · exact pow_nonneg (Wt_pos x).le k
    · norm_num
  exact mul_nonneg (norm_nonneg _) h

theorem vfam_of_mem {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) {i i' j : Fin q} (h : j = i ∨ j = i')
    (x : ℤ) : vfam a k i i' j x = ‖a j x‖ * Wt x ^ k := by
  unfold vfam
  rw [if_pos h]

theorem vfam_of_not_mem {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) {i i' j : Fin q}
    (h : ¬(j = i ∨ j = i')) (x : ℤ) : vfam a k i i' j x = ‖a j x‖ := by
  unfold vfam
  rw [if_neg h, mul_one]

theorem vfam_sq_eq {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) {i i' j : Fin q} (h : j = i ∨ j = i')
    (x : ℤ) : vfam a k i i' j x ^ 2 = Wt x ^ (2 * k) * ‖a j x‖ ^ 2 := by
  rw [vfam_of_mem a k h x, mul_pow, ← pow_mul, mul_comm k 2]
  ring

theorem prod_ite_pair {q : ℕ} (i i' : Fin q) (hne : i ≠ i') (h : Fin q → ℝ) :
    ∏ j, (if j = i ∨ j = i' then h j else 1) = h i * h i' := by
  have hsub : ∏ j ∈ ({i, i'} : Finset (Fin q)), (if j = i ∨ j = i' then h j else 1) =
      ∏ j, (if j = i ∨ j = i' then h j else 1) := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hj
    have hj' : ¬(j = i ∨ j = i') := by
      intro h'
      apply hj
      rcases h' with h' | h' <;> simp [h']
    exact if_neg hj'
  rw [← hsub, Finset.prod_pair hne]
  simp

theorem vfam_prod {q : ℕ} (a : Fin q → ℤ → ℂ) (k : ℕ) {i i' : Fin q} (hne : i ≠ i')
    (n : Fin q → ℤ) :
    ∏ j, vfam a k i i' j (n j) = (∏ j, ‖a j (n j)‖) * (Wt (n i) ^ k * Wt (n i') ^ k) := by
  have h : ∀ j, vfam a k i i' j (n j) =
      ‖a j (n j)‖ * (if j = i ∨ j = i' then Wt (n j) ^ k else 1) := fun j => rfl
  rw [Finset.prod_congr rfl (fun j _ => h j), Finset.prod_mul_distrib,
    prod_ite_pair i i' hne (fun j => Wt (n j) ^ k)]

theorem ne_succAbove_of {m : ℕ} (i : Fin (m + 2)) (l : Fin (m + 1)) : i ≠ i.succAbove l :=
  (Fin.succAbove_ne i l).symm

/-- **Constrained sum, general `q = m + 2`.** For `k ≥ 1`, `Σ_j α_j ≤ 2k`, and coefficient families with
finite weighted ℓ² norms, the constrained family is summable and bounded by
`(2^k)^m · (m+2)(m+1) · C_k^{m+2} · ∏_j N_j`. -/
theorem constrained_bound {m k : ℕ} (hk : 1 ≤ k) (α : Fin (m + 2) → ℕ) (hα : ∑ j, α j ≤ 2 * k)
    (a : Fin (m + 2) → ℤ → ℂ) (ha : ∀ j, Summable fun x : ℤ => Wt x ^ (2 * k) * ‖a j x‖ ^ 2) :
    Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} =>
        (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖) ∧
      ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
          (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖ ≤
        ((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2) *
          ∏ j, Nc a k j := by
  have hCk1 : 1 ≤ Ckc k := Ckc_ge_one hk
  have hN0 : ∀ j, 0 ≤ Nc a k j := fun j => Real.sqrt_nonneg _
  have hl1 : ∀ j, Summable (fun x : ℤ => ‖a j x‖) ∧ ∑' x : ℤ, ‖a j x‖ ≤ Ckc k * Nc a k j :=
    fun j => l1_bound hk (fun n => norm_nonneg _) (ha j)
  have hD0 : ∀ j, 0 ≤ Ckc k * Nc a k j := fun j => mul_nonneg (zero_le_one.trans hCk1) (hN0 j)
  have hsq : ∀ i i' j : Fin (m + 2), j = i ∨ j = i' →
      Summable (fun x : ℤ => vfam a k i i' j x ^ 2) :=
    fun i i' j h => (ha j).congr (fun x => (vfam_sq_eq a k h x).symm)
  have hsq_tsum : ∀ i i' j : Fin (m + 2), j = i ∨ j = i' →
      ∑' x : ℤ, vfam a k i i' j x ^ 2 = ∑' x : ℤ, Wt x ^ (2 * k) * ‖a j x‖ ^ 2 :=
    fun i i' j h => tsum_congr (fun x => vfam_sq_eq a k h x)
  have hli : ∀ i i' j : Fin (m + 2), j = i ∨ j = i' →
      Real.sqrt (∑' x : ℤ, vfam a k i i' j x ^ 2) ≤ Ckc k * Nc a k j := by
    intro i i' j h
    rw [hsq_tsum i i' j h]
    exact le_mul_of_one_le_left (hN0 j) hCk1
  have hl : ∀ i i' j : Fin (m + 2), j ≠ i → j ≠ i' → Summable (vfam a k i i' j) := by
    intro i i' j h1 h2
    refine (hl1 j).1.congr (fun x => ?_)
    exact (vfam_of_not_mem a k (not_or.2 ⟨h1, h2⟩) x).symm
  have hlb : ∀ i i' j : Fin (m + 2), j ≠ i → j ≠ i' →
      ∑' x : ℤ, vfam a k i i' j x ≤ Ckc k * Nc a k j := by
    intro i i' j h1 h2
    rw [tsum_congr (fun x => vfam_of_not_mem a k (not_or.2 ⟨h1, h2⟩) x)]
    exact (hl1 j).2
  have hpair : ∀ i i' : Fin (m + 2), i ≠ i' →
      Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} => ∏ j, vfam a k i i' j (n.1 j)) ∧
        ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, vfam a k i i' j (n.1 j) ≤
          ∏ j, (Ckc k * Nc a k j) := by
    intro i i' hne
    exact pair_bound (vfam a k i i') (fun j => Ckc k * Nc a k j)
      (fun j x => vfam_nonneg a k i i' j x) hD0 i i' hne
      (hsq i i' i (Or.inl rfl)) (hsq i i' i' (Or.inr rfl))
      (hli i i' i (Or.inl rfl)) (hli i i' i' (Or.inr rfl))
      (fun j h1 h2 => hl i i' j h1 h2) (fun j h1 h2 => hlb i i' j h1 h2)
  have hF : ∀ n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
      (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖ ≤
        ((2 : ℝ) ^ k) ^ m * ∑ i, ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) := by
    intro n
    have hP0 : 0 ≤ ∏ j, ‖a j (n.1 j)‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
    have step1 := prod_pow_le_sum_Wt_pow (k := k) (by omega : 0 < m + 2) α hα n.1
    have step2 : ∀ i : Fin (m + 2), Wt (n.1 i) ^ (2 * k) * ∏ j, ‖a j (n.1 j)‖ ≤
        ((2 : ℝ) ^ k) ^ m * ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) := by
      intro i
      have hc := Wt_constraint_pow_le (k := k) n.1 n.2 i
      have hsumP : ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) =
          ∑ l : Fin (m + 1), (∏ j, ‖a j (n.1 j)‖) *
            (Wt (n.1 i) ^ k * Wt (n.1 (i.succAbove l)) ^ k) :=
        Finset.sum_congr rfl (fun l _ => vfam_prod a k (ne_succAbove_of i l) n.1)
      rw [hsumP, Wt_pow_split]
      calc Wt (n.1 i) ^ k * Wt (n.1 i) ^ k * ∏ j, ‖a j (n.1 j)‖
          ≤ Wt (n.1 i) ^ k * (((2 : ℝ) ^ k) ^ m * ∑ l : Fin (m + 1), Wt (n.1 (i.succAbove l)) ^ k) *
              ∏ j, ‖a j (n.1 j)‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (pow_nonneg (Wt_pos _).le _)) hP0
        _ = ((2 : ℝ) ^ k) ^ m * ∑ l : Fin (m + 1),
              (∏ j, ‖a j (n.1 j)‖) * (Wt (n.1 i) ^ k * Wt (n.1 (i.succAbove l)) ^ k) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l _
          ring
    calc (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖
        ≤ (∑ i, Wt (n.1 i) ^ (2 * k)) * ∏ j, ‖a j (n.1 j)‖ :=
          mul_le_mul_of_nonneg_right step1 hP0
      _ = ∑ i, Wt (n.1 i) ^ (2 * k) * ∏ j, ‖a j (n.1 j)‖ := Finset.sum_mul _ _ _
      _ ≤ ∑ i, ((2 : ℝ) ^ k) ^ m * ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) :=
          Finset.sum_le_sum fun i _ => step2 i
      _ = ((2 : ℝ) ^ k) ^ m * ∑ i, ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) := by
          rw [Finset.mul_sum]
  have hΨsum : Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} =>
      ∑ i, ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j)) :=
    summable_sum fun i _ => summable_sum fun l _ =>
      (hpair i (i.succAbove l) (ne_succAbove_of i l)).1
  have hFnn : ∀ n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
      0 ≤ (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖ :=
    fun n => mul_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (abs_nonneg _) _)
      (Finset.prod_nonneg fun j _ => norm_nonneg _)
  have hsumF : Summable (fun n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0} =>
      (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖) :=
    Summable.of_nonneg_of_le hFnn hF (hΨsum.mul_left _)
  refine ⟨hsumF, ?_⟩
  have hsplit : ∀ i : Fin (m + 2),
      ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∑ l : Fin (m + 1),
          ∏ j, vfam a k i (i.succAbove l) j (n.1 j) =
        ∑ l : Fin (m + 1), ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
          ∏ j, vfam a k i (i.succAbove l) j (n.1 j) :=
    fun i => Summable.tsum_finsetSum (fun l _ => (hpair i (i.succAbove l) (ne_succAbove_of i l)).1)
  calc ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
          (∏ j, |((n.1 j : ℤ) : ℝ)| ^ α j) * ∏ j, ‖a j (n.1 j)‖
      ≤ ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
          ((2 : ℝ) ^ k) ^ m * ∑ i, ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) :=
        Summable.tsum_le_tsum hF hsumF (hΨsum.mul_left _)
    _ = ((2 : ℝ) ^ k) ^ m * ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0},
          ∑ i, ∑ l : Fin (m + 1), ∏ j, vfam a k i (i.succAbove l) j (n.1 j) := tsum_mul_left
    _ = ((2 : ℝ) ^ k) ^ m * ∑ i, ∑ l : Fin (m + 1),
          ∑' n : {n : Fin (m + 2) → ℤ // ∑ j, n j = 0}, ∏ j, vfam a k i (i.succAbove l) j (n.1 j) := by
        rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun l _ =>
          (hpair i (i.succAbove l) (ne_succAbove_of i l)).1)]
        congr 1
        exact Finset.sum_congr rfl (fun i _ => hsplit i)
    _ ≤ ((2 : ℝ) ^ k) ^ m * ∑ i : Fin (m + 2), ∑ l : Fin (m + 1), ∏ j, (Ckc k * Nc a k j) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun l _ =>
            (hpair i (i.succAbove l) (ne_succAbove_of i l)).2)
          (pow_nonneg (by norm_num) _)
    _ = ((2 : ℝ) ^ k) ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (Ckc k) ^ (m + 2) *
          ∏ j, Nc a k j := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.prod_mul_distrib, Finset.prod_const]
        push_cast
        ring

end QuantumNLS.CorrelationConstrainedSumGen

/-! Axiom audit (constrained sum, general `q`). -/
#print axioms QuantumNLS.CorrelationConstrainedSumGen.Ckc_ge_one
#print axioms QuantumNLS.CorrelationConstrainedSumGen.prod_ite_pair
#print axioms QuantumNLS.CorrelationConstrainedSumGen.vfam_prod
#print axioms QuantumNLS.CorrelationConstrainedSumGen.constrained_bound
#print axioms QuantumNLS.CorrelationConstrainedSumGen.Wt_sum_pow_le
#print axioms QuantumNLS.CorrelationConstrainedSumGen.Wt_constraint_pow_le
#print axioms QuantumNLS.CorrelationConstrainedSumGen.prod_real_aux
#print axioms QuantumNLS.CorrelationConstrainedSumGen.shift_cauchy
#print axioms QuantumNLS.CorrelationConstrainedSumGen.cEquiv
#print axioms QuantumNLS.CorrelationConstrainedSumGen.cEquiv_pair
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_nonneg
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_inner
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_inner_summable
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_inner_le
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_outer_summable
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_summable
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_tsum_bound
#print axioms QuantumNLS.CorrelationConstrainedSumGen.two_l2_bound
#print axioms QuantumNLS.CorrelationConstrainedSumGen.perm_prod
#print axioms QuantumNLS.CorrelationConstrainedSumGen.perm_tsum_all
#print axioms QuantumNLS.CorrelationConstrainedSumGen.exists_perm_pair
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pair_bound
#print axioms QuantumNLS.CorrelationConstrainedSumGen.vfam_nonneg
#print axioms QuantumNLS.CorrelationConstrainedSumGen.vfam_of_mem
#print axioms QuantumNLS.CorrelationConstrainedSumGen.vfam_of_not_mem
#print axioms QuantumNLS.CorrelationConstrainedSumGen.vfam_sq_eq
#print axioms QuantumNLS.CorrelationConstrainedSumGen.ne_succAbove_of

/-! Axiom audit (chunk 2). -/
#print axioms QuantumNLS.CorrelationConstrainedSumGen.Wt_sum_pow_le
#print axioms QuantumNLS.CorrelationConstrainedSumGen.Wt_constraint_pow_le
#print axioms QuantumNLS.CorrelationConstrainedSumGen.prod_real_aux
#print axioms QuantumNLS.CorrelationConstrainedSumGen.shift_cauchy
#print axioms QuantumNLS.CorrelationConstrainedSumGen.cEquiv
#print axioms QuantumNLS.CorrelationConstrainedSumGen.cEquiv_pair
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_summable
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pairTerm_tsum_bound
#print axioms QuantumNLS.CorrelationConstrainedSumGen.two_l2_bound
#print axioms QuantumNLS.CorrelationConstrainedSumGen.perm_tsum_all
#print axioms QuantumNLS.CorrelationConstrainedSumGen.exists_perm_pair
#print axioms QuantumNLS.CorrelationConstrainedSumGen.pair_bound
