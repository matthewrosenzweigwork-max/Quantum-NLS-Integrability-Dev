import Mathlib
import QuantumNLS.OrderedResponse

/-!
# R-0662E607 `adj:lem:inverse-decay`: entrywise decay of the inverse Gaudin matrix

Source: `source/chapters/quantitative/fixed_moments.tex`, lines 4–40 (lemma `adj:lem:inverse-decay`
with its printed proof). No graph prerequisites.

Statement. For `N ≥ 2`, `c, L > 0` and arbitrary reals `q_1,…,q_N`, let
`w_jk = 2c/(c²+(q_j−q_k)²)` for `j ≠ k`, `G = L Id + 𝓛_w` with `(𝓛_w f)_j = Σ_{k≠j} w_jk (f_j − f_k)`,
`d = L + 2(N−1)/c`, `τ = 1 − L/d`, `B = (2c/d²)(1+4τ+τ²)/(1−τ)⁴`. Then
`0 ≤ (G⁻¹)_jk ≤ (L⁻¹ + B)/(1 + (q_j − q_k)²)` for all `j, k`.

Matrix link. `G` is `QuantumNLS.OrderedResponse.Bmat L c q` (frozen module 5467eeae, imported read-only).
Its diagonal is `G_jj = L + Σ_{k≠j} w_jk`, its off-diagonal entries are `G_jk = −w_jk`, and its action is
`(G u)_j = L u_j + Σ_{k≠j} w_jk (u_j − u_k)` (`OrderedResponse.mulVec_Bmat_eq`). This is `L Id + 𝓛_w`.
The lemma `ig_G_action` restates this action with the weight written out as `2c/(c²+(q_j−q_k)²)`.

Route (printed proof, with the weighted estimates made explicit).
* `P = Id − G/d` has nonnegative entries, and every row and column sums to `τ ∈ (0,1)`.
* `Σ_{ℓ<n} P^ℓ → d·G⁻¹` entrywise, since `G·Σ_{ℓ<n}P^ℓ = d(Id − P^n)` and `(P^n)_jk ≤ τ^n`.
* Path union bound: for `R = |q_j−q_k| > 0` and `ℓ ≥ 1`, `(P^ℓ)_jk ≤ 2cℓ³τ^{ℓ−1}/(dR²)`. The proof splits
  `P^ℓ = S^ℓ + Σ_i S^i Q P^{ℓ−1−i}` where `S` keeps the short jumps (`|q_u−q_v| < R/ℓ`) and `Q` the long
  jumps. `S^ℓ_jk = 0` because a path of `ℓ` short steps has total displacement `< R`.
* `Σ_{m<n}(m+1)³τ^m ≤ (1+4τ+τ²)/(1−τ)⁴`, from a closed form with a nonnegative remainder.
  Hence `(G⁻¹)_jk·R² ≤ B`.
* `G⁻¹·1 = L⁻¹·1` and nonnegativity give `(G⁻¹)_jk ≤ L⁻¹`.
* Combining, `(G⁻¹)_jk·(1+R²) ≤ L⁻¹ + B`.

No `sorry`, `admit`, `native_decide`, or added axioms.
-/

noncomputable section
open scoped BigOperators
open Finset Matrix Filter Topology
open QuantumNLS.OrderedResponse

namespace QuantumNLS.InverseGaudinDecay

/-! ## A. Generic facts for nonnegative matrices with constant row sums -/

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ig_pow_nonneg {P : Matrix ι ι ℝ} (hnn : ∀ i k, 0 ≤ P i k) :
    ∀ m : ℕ, ∀ i k, 0 ≤ (P ^ m) i k := by
  intro m
  induction m with
  | zero =>
    intro i k
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    intro i k
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (ih i j) (hnn j k)

lemma ig_pow_row_sum {P : Matrix ι ι ℝ} {τ : ℝ} (hrow : ∀ i, ∑ k, P i k = τ) :
    ∀ m : ℕ, ∀ i, ∑ k, (P ^ m) i k = τ ^ m := by
  intro m
  induction m with
  | zero =>
    intro i
    simp [Matrix.one_apply]
  | succ m ih =>
    intro i
    have h : ∑ k, (P ^ (m + 1)) i k = ∑ j, (P ^ m) i j * τ := by
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.mul_sum, hrow j]
    rw [h, ← Finset.sum_mul, ih i, pow_succ]

lemma ig_pow_col_sum {P : Matrix ι ι ℝ} {τ : ℝ} (hrow : ∀ i, ∑ k, P i k = τ)
    (hsym : ∀ i k, P i k = P k i) (m : ℕ) (k : ι) :
    ∑ v, (P ^ m) v k = τ ^ m := by
  have hT : Pᵀ = P := Matrix.ext fun i j => hsym j i
  have hPm : (P ^ m)ᵀ = P ^ m := by rw [Matrix.transpose_pow, hT]
  have key : ∀ v, (P ^ m) v k = (P ^ m) k v := fun v => congrFun (congrFun hPm k) v
  rw [Finset.sum_congr rfl fun v _ => key v]
  exact ig_pow_row_sum hrow m k

lemma ig_pow_le {P : Matrix ι ι ℝ} {τ : ℝ} (hnn : ∀ i k, 0 ≤ P i k)
    (hrow : ∀ i, ∑ k, P i k = τ) (m : ℕ) (i k : ι) : (P ^ m) i k ≤ τ ^ m := by
  rw [← ig_pow_row_sum hrow m i]
  exact Finset.single_le_sum (fun j _ => ig_pow_nonneg hnn m i j) (Finset.mem_univ k)

lemma ig_pow_mono {A B : Matrix ι ι ℝ} (hA : ∀ i k, 0 ≤ A i k) (hB : ∀ i k, 0 ≤ B i k)
    (hAB : ∀ i k, A i k ≤ B i k) : ∀ m : ℕ, ∀ i k, (A ^ m) i k ≤ (B ^ m) i k := by
  intro m
  induction m with
  | zero =>
    intro i k
    simp
  | succ m ih =>
    intro i k
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_le_sum fun j _ =>
      mul_le_mul (ih i j) (hAB j k) (hA j k) (ig_pow_nonneg hB m i j)

/-- Tail identity for the telescoping split of powers. -/
lemma ig_tail_succ (S Q P : Matrix ι ι ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), S ^ i * Q * P ^ (m + 1 - 1 - i)
      = Q * P ^ m + S * ∑ i ∈ range m, S ^ i * Q * P ^ (m - 1 - i) := by
  rw [Finset.sum_range_succ', Finset.mul_sum, add_comm (Q * P ^ m)]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi' : m + 1 - 1 - (i + 1) = m - 1 - i := by omega
    rw [hi', pow_succ']
    simp only [mul_assoc]
  · simp

/-- Telescoping split `P^m = S^m + Σ_{i<m} S^i Q P^{m-1-i}` when `P = S + Q`. -/
lemma ig_pow_split (S Q P : Matrix ι ι ℝ) (hPSQ : P = S + Q) :
    ∀ m : ℕ, P ^ m = S ^ m + ∑ i ∈ range m, S ^ i * Q * P ^ (m - 1 - i)
  | 0 => by simp
  | m + 1 => by
    have ih := ig_pow_split S Q P hPSQ m
    have e1 : P ^ (m + 1) = (S + Q) * P ^ m := by
      rw [← hPSQ, pow_succ']
    rw [ig_tail_succ S Q P m, e1, add_mul, ih]
    simp only [mul_add, add_mul]
    rw [← pow_succ']
    abel

/-- Short-jump part of `P` at threshold `r`: entries with `|x_i − x_k| < r`. -/
def igS (x : ι → ℝ) (r : ℝ) (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i k => if |x i - x k| < r then P i k else 0

/-- Long-jump part of `P` at threshold `r`: entries with `r ≤ |x_i − x_k|`. -/
def igQ (x : ι → ℝ) (r : ℝ) (P : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i k => if r ≤ |x i - x k| then P i k else 0

lemma ig_split_PQ (x : ι → ℝ) (r : ℝ) (P : Matrix ι ι ℝ) : P = igS x r P + igQ x r P := by
  ext i k
  by_cases h : |x i - x k| < r
  · have h' : ¬ r ≤ |x i - x k| := not_le.mpr h
    simp [igS, igQ, h, h']
  · have h' : r ≤ |x i - x k| := not_lt.mp h
    simp [igS, igQ, h, h']

lemma ig_igS_nonneg {x : ι → ℝ} {r : ℝ} {P : Matrix ι ι ℝ} (hP : ∀ i k, 0 ≤ P i k) :
    ∀ i k, 0 ≤ igS x r P i k := by
  intro i k
  unfold igS
  rw [Matrix.of_apply]
  split_ifs
  · exact hP i k
  · exact le_rfl

lemma ig_igS_le {x : ι → ℝ} {r : ℝ} {P : Matrix ι ι ℝ} (hP : ∀ i k, 0 ≤ P i k) :
    ∀ i k, igS x r P i k ≤ P i k := by
  intro i k
  unfold igS
  rw [Matrix.of_apply]
  split_ifs
  · exact le_rfl
  · exact hP i k

lemma ig_igQ_nonneg {x : ι → ℝ} {r : ℝ} {P : Matrix ι ι ℝ} (hP : ∀ i k, 0 ≤ P i k) :
    ∀ i k, 0 ≤ igQ x r P i k := by
  intro i k
  unfold igQ
  rw [Matrix.of_apply]
  split_ifs
  · exact hP i k
  · exact le_rfl

lemma ig_igQ_le {x : ι → ℝ} {r M : ℝ} {P : Matrix ι ι ℝ} (hM : 0 ≤ M)
    (hbig : ∀ u v, r ≤ |x u - x v| → P u v ≤ M) : ∀ i k, igQ x r P i k ≤ M := by
  intro i k
  unfold igQ
  rw [Matrix.of_apply]
  split_ifs with h
  · exact hbig i k h
  · exact hM

lemma ig_igS_ne_zero_lt {x : ι → ℝ} {r : ℝ} {P : Matrix ι ι ℝ} {i k : ι}
    (h : igS x r P i k ≠ 0) : |x i - x k| < r := by
  by_contra hc
  apply h
  simp [igS, hc]

/-- A product of `m+1` short steps has total displacement `< (m+1) r`. -/
lemma ig_igS_pow_far (x : ι → ℝ) (r : ℝ) (P : Matrix ι ι ℝ) :
    ∀ m : ℕ, ∀ i k, (igS x r P ^ (m + 1)) i k ≠ 0 → |x i - x k| < ((m : ℝ) + 1) * r := by
  intro m
  induction m with
  | zero =>
    intro i k h
    simp only [zero_add, pow_one] at h
    have := ig_igS_ne_zero_lt h
    simpa using this
  | succ m ih =>
    intro i k h
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨w, _, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hw
    have hA := ih i w h1
    have hB := ig_igS_ne_zero_lt h2
    have htri := abs_sub_le (x i) (x w) (x k)
    have hcast : (((m + 1 : ℕ) : ℝ) + 1) * r = ((m : ℝ) + 1) * r + r := by
      push_cast
      ring
    rw [hcast]
    linarith

/-- Exchange of a double sum with a scalar factor and a product of sums. -/
lemma ig_sum_swap_mul (A B : ι → ℝ) (M : ℝ) :
    ∑ v, ∑ u, (A u * M) * B v = M * (∑ u, A u) * (∑ v, B v) := by
  have h : ∀ v, ∑ u, (A u * M) * B v = (M * ∑ u, A u) * B v := by
    intro v
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => by ring
  simp only [h]
  rw [← Finset.mul_sum]

/-- Entrywise bound for one block `S^i Q P^p`. -/
lemma ig_term_bound {S Q P : Matrix ι ι ℝ} {τ M : ℝ}
    (hS0 : ∀ i k, 0 ≤ S i k) (hSP : ∀ i k, S i k ≤ P i k) (hP0 : ∀ i k, 0 ≤ P i k)
    (hrow : ∀ i, ∑ k, P i k = τ) (hsym : ∀ i k, P i k = P k i) (hτ : 0 ≤ τ)
    (hQM : ∀ i k, Q i k ≤ M) (hM : 0 ≤ M) (i p : ℕ) (j k : ι) :
    (S ^ i * Q * P ^ p) j k ≤ M * τ ^ i * τ ^ p := by
  have hA : ∀ u, 0 ≤ (S ^ i) j u := fun u => ig_pow_nonneg hS0 i j u
  have hB : ∀ v, 0 ≤ (P ^ p) v k := fun v => ig_pow_nonneg hP0 p v k
  have hSum1 : ∑ u, (S ^ i) j u ≤ τ ^ i := by
    calc ∑ u, (S ^ i) j u ≤ ∑ u, (P ^ i) j u :=
          Finset.sum_le_sum fun u _ => ig_pow_mono hS0 hP0 hSP i j u
      _ = τ ^ i := ig_pow_row_sum hrow i j
  have hSum2 : ∑ v, (P ^ p) v k = τ ^ p := ig_pow_col_sum hrow hsym p k
  have expand : (S ^ i * Q * P ^ p) j k = ∑ v, ∑ u, ((S ^ i) j u * Q u v) * (P ^ p) v k := by
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
  calc (S ^ i * Q * P ^ p) j k = ∑ v, ∑ u, ((S ^ i) j u * Q u v) * (P ^ p) v k := expand
    _ ≤ ∑ v, ∑ u, ((S ^ i) j u * M) * (P ^ p) v k := by
        refine Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun u _ => ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hQM u v) (hA u)) (hB v)
    _ = M * (∑ u, (S ^ i) j u) * (∑ v, (P ^ p) v k) :=
        ig_sum_swap_mul (fun u => (S ^ i) j u) (fun v => (P ^ p) v k) M
    _ ≤ M * τ ^ i * τ ^ p := by
        rw [hSum2]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hSum1 hM) (pow_nonneg hτ p)

/-- Path union bound: if the long jumps are at most `M` and `|x_j − x_k| = (m+1) r`, then
`(P^{m+1})_jk ≤ (m+1) M τ^m`. -/
lemma ig_path_bound {P : Matrix ι ι ℝ} {τ : ℝ} (hP0 : ∀ i k, 0 ≤ P i k)
    (hrow : ∀ i, ∑ k, P i k = τ) (hsym : ∀ i k, P i k = P k i) (hτ : 0 ≤ τ)
    {M : ℝ} (hM : 0 ≤ M) {x : ι → ℝ} {r : ℝ}
    (hbig : ∀ u v, r ≤ |x u - x v| → P u v ≤ M) (m : ℕ) (j k : ι)
    (hjk : |x j - x k| = ((m : ℝ) + 1) * r) :
    (P ^ (m + 1)) j k ≤ ((m : ℝ) + 1) * M * τ ^ m := by
  have hPSQ := ig_split_PQ x r P
  set S := igS x r P with hSdef
  set Q := igQ x r P with hQdef
  have hS0 : ∀ i k, 0 ≤ S i k := ig_igS_nonneg hP0
  have hSP : ∀ i k, S i k ≤ P i k := ig_igS_le hP0
  have hQM : ∀ i k, Q i k ≤ M := ig_igQ_le hM hbig
  have hz : (S ^ (m + 1)) j k = 0 := by
    by_contra h
    have h' := ig_igS_pow_far x r P m j k h
    rw [hjk] at h'
    exact lt_irrefl _ h'
  have hterm : ∀ i ∈ range (m + 1), (S ^ i * Q * P ^ (m + 1 - 1 - i)) j k ≤ M * τ ^ m := by
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    have hidx : i + (m + 1 - 1 - i) = m := by omega
    calc (S ^ i * Q * P ^ (m + 1 - 1 - i)) j k
        ≤ M * τ ^ i * τ ^ (m + 1 - 1 - i) :=
          ig_term_bound hS0 hSP hP0 hrow hsym hτ hQM hM i (m + 1 - 1 - i) j k
      _ = M * τ ^ m := by rw [mul_assoc, ← pow_add, hidx]
  rw [ig_pow_split S Q P hPSQ (m + 1), Matrix.add_apply, hz, zero_add, Matrix.sum_apply]
  calc ∑ i ∈ range (m + 1), (S ^ i * Q * P ^ (m + 1 - 1 - i)) j k
      ≤ ∑ _i ∈ range (m + 1), M * τ ^ m := Finset.sum_le_sum hterm
    _ = ((m : ℝ) + 1) * M * τ ^ m := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Generic

/-! ## B. The partial geometric-type sum `Σ (m+1)³ x^m` -/

/-- Closed form of `Σ_{k≥0} (t+k)³ x^k` for `0 ≤ x < 1`. -/
def igTailT (x t : ℝ) : ℝ :=
  t ^ 3 / (1 - x) + 3 * t ^ 2 * x / (1 - x) ^ 2 + 3 * t * (x * (1 + x)) / (1 - x) ^ 3
    + x * (1 + 4 * x + x ^ 2) / (1 - x) ^ 4

lemma ig_tailT_rec {x : ℝ} (hx : x < 1) (t : ℝ) :
    igTailT x t = t ^ 3 + x * igTailT x (t + 1) := by
  have h1 : (1 - x) ≠ 0 := (by linarith : (0 : ℝ) < 1 - x).ne'
  unfold igTailT
  field_simp
  ring

lemma ig_tailT_one {x : ℝ} (hx : x < 1) :
    igTailT x 1 = (1 + 4 * x + x ^ 2) / (1 - x) ^ 4 := by
  have h1 : (1 - x) ≠ 0 := (by linarith : (0 : ℝ) < 1 - x).ne'
  unfold igTailT
  field_simp
  ring

lemma ig_partial_closed {x : ℝ} (hx : x < 1) (n : ℕ) :
    ∑ m ∈ range n, ((m : ℝ) + 1) ^ 3 * x ^ m
      = (1 + 4 * x + x ^ 2) / (1 - x) ^ 4 - x ^ n * igTailT x ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [ig_tailT_one hx]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h := ig_tailT_rec hx ((n : ℝ) + 1)
    push_cast
    rw [h]
    ring

lemma ig_tailT_nonneg {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (ht : 0 ≤ t) :
    0 ≤ igTailT x t := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 0 ≤ 1 + x := by linarith
  have h3 : 0 ≤ 1 + 4 * x + x ^ 2 := by nlinarith [sq_nonneg x]
  unfold igTailT
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact div_nonneg (pow_nonneg ht 3) h1.le
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht 2)) hx0)
      (pow_nonneg h1.le 2)
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht) (mul_nonneg hx0 h2))
      (pow_nonneg h1.le 3)
  · exact div_nonneg (mul_nonneg hx0 h3) (pow_nonneg h1.le 4)

/-- The printed series bound `Σ_{m≥0} (m+1)³ x^m = (1+4x+x²)/(1−x)⁴`, in partial-sum form. -/
lemma ig_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    ∑ m ∈ range n, ((m : ℝ) + 1) ^ 3 * x ^ m ≤ (1 + 4 * x + x ^ 2) / (1 - x) ^ 4 := by
  rw [ig_partial_closed hx1 n]
  have := mul_nonneg (pow_nonneg hx0 n)
    (ig_tailT_nonneg hx0 hx1 (t := (n : ℝ) + 1) (by positivity))
  linarith

/-! ## C. The Gaudin matrix `G = Bmat` and its substochastic companion `P = Id − G/d` -/

section Gaudin

variable {N : ℕ} {L c : ℝ}

/-- Graph-Laplacian action of `G = Bmat`: `(G u)_j = L u_j + Σ_{k≠j} w_jk (u_j − u_k)` with
`w_jk = 2c/(c²+(q_j−q_k)²)`. This is the action of `L Id + 𝓛_w`. -/
lemma ig_G_action (q u : Fin N → ℝ) (j : Fin N) :
    (Bmat L c q *ᵥ u) j
      = L * u j + ∑ k ∈ univ.erase j, 2 * c / (c ^ 2 + (q j - q k) ^ 2) * (u j - u k) :=
  mulVec_Bmat_eq L c q u j

lemma ig_G_apply_ne (q : Fin N → ℝ) {j k : Fin N} (h : j ≠ k) :
    Bmat L c q j k = -wt c (q j) (q k) := by
  simp [Bmat, h]

lemma ig_G_apply_self (q : Fin N → ℝ) (j : Fin N) :
    Bmat L c q j j = L + ∑ k ∈ univ.erase j, wt c (q j) (q k) := by
  simp [Bmat]

lemma ig_G_symm (q : Fin N → ℝ) (j k : Fin N) : Bmat L c q j k = Bmat L c q k j := by
  by_cases h : j = k
  · rw [h]
  · rw [ig_G_apply_ne q h, ig_G_apply_ne q (Ne.symm h), wt_comm]

lemma ig_G_row_sum (q : Fin N → ℝ) (j : Fin N) : ∑ k, Bmat L c q j k = L := by
  have h := mulVec_Bmat_eq L c q (fun _ => (1 : ℝ)) j
  simp only [mul_one, sub_self, mul_zero, Finset.sum_const_zero, add_zero] at h
  simpa [Matrix.mulVec, dotProduct] using h

lemma ig_wt_le (hc : 0 < c) (x y : ℝ) : wt c x y ≤ 2 / c := by
  unfold wt
  rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg _)) hc]
  nlinarith [sq_nonneg (x - y)]

lemma ig_wt_sum_le (hN : 2 ≤ N) (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) :
    ∑ l ∈ univ.erase j, wt c (q j) (q l) ≤ ((N : ℝ) - 1) * (2 / c) := by
  calc ∑ l ∈ univ.erase j, wt c (q j) (q l) ≤ ∑ _l ∈ univ.erase j, (2 / c) :=
        Finset.sum_le_sum fun l _ => ig_wt_le hc _ _
    _ = ((N : ℝ) - 1) * (2 / c) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]

lemma ig_P_apply (d : ℝ) (q : Fin N → ℝ) (j k : Fin N) :
    ((1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q) j k
      = (if j = k then 1 else 0) - d⁻¹ * Bmat L c q j k := by
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]

lemma ig_P_nonneg (hN : 2 ≤ N) (hc : 0 < c) {d : ℝ} (hdpos : 0 < d)
    (hd : d = L + 2 * ((N : ℝ) - 1) / c) (q : Fin N → ℝ) (j k : Fin N) :
    0 ≤ ((1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q) j k := by
  rw [ig_P_apply]
  by_cases h : j = k
  · subst h
    rw [if_pos rfl, ig_G_apply_self]
    have hs := ig_wt_sum_le hN hc q j
    have e : ((N : ℝ) - 1) * (2 / c) = 2 * ((N : ℝ) - 1) / c := by ring
    have hX : L + ∑ l ∈ univ.erase j, wt c (q j) (q l) ≤ d := by
      rw [hd]
      linarith
    have hinv : d⁻¹ * (L + ∑ l ∈ univ.erase j, wt c (q j) (q l)) ≤ 1 := by
      rw [inv_mul_le_iff₀ hdpos, mul_one]
      exact hX
    linarith
  · rw [if_neg h, ig_G_apply_ne q h, mul_neg, zero_sub, neg_neg]
    exact mul_nonneg (inv_nonneg.mpr hdpos.le) (wt_pos hc (q j) (q k)).le

lemma ig_P_row_sum (q : Fin N → ℝ) (d : ℝ) (j : Fin N) :
    ∑ k, ((1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q) j k = 1 - d⁻¹ * L := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ig_G_row_sum]
  simp [Matrix.one_apply]

lemma ig_P_symm (q : Fin N → ℝ) (d : ℝ) (j k : Fin N) :
    ((1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q) j k
      = ((1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q) k j := by
  rw [ig_P_apply, ig_P_apply, ig_G_symm q j k]
  congr 1
  by_cases h : j = k
  · rw [h]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- Long-jump entry bound: if `R/n ≤ |q_j − q_k|` then `P_jk ≤ 2c n²/(d R²)`. -/
lemma ig_P_long_le {d R n : ℝ} (hc : 0 < c) (hd : 0 < d) (q : Fin N → ℝ) (hR : 0 < R)
    (hn : 0 < n) (j k : Fin N) (h : R / n ≤ |q j - q k|) :
    ((1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q) j k ≤ 2 * c * n ^ 2 / (d * R ^ 2) := by
  have hjk : j ≠ k := by
    rintro rfl
    have hpos : 0 < R / n := div_pos hR hn
    rw [sub_self, abs_zero] at h
    linarith
  have hd0 : d ≠ 0 := hd.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hc2 : (0 : ℝ) ≤ 2 * c := by linarith
  rw [ig_P_apply, if_neg hjk, ig_G_apply_ne q hjk, mul_neg, zero_sub, neg_neg]
  have hle : R ≤ |q j - q k| * n := (div_le_iff₀ hn).mp h
  have h0 : R ^ 2 ≤ (|q j - q k| * n) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hle hle hR.le (le_trans hR.le hle)
  have h1 : (|q j - q k| * n) ^ 2 = (q j - q k) ^ 2 * n ^ 2 := by
    rw [mul_pow, sq_abs]
  have hsq : R ^ 2 ≤ (q j - q k) ^ 2 * n ^ 2 := by
    rw [← h1]
    exact h0
  have hw : wt c (q j) (q k) ≤ 2 * c * n ^ 2 / R ^ 2 := by
    unfold wt
    rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg _)) (pow_pos hR 2)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hc2,
      mul_nonneg (mul_nonneg hc2 (sq_nonneg n)) (sq_nonneg c)]
  calc d⁻¹ * wt c (q j) (q k) ≤ d⁻¹ * (2 * c * n ^ 2 / R ^ 2) :=
        mul_le_mul_of_nonneg_left hw (inv_nonneg.mpr hd.le)
    _ = 2 * c * n ^ 2 / (d * R ^ 2) := by
        field_simp

end Gaudin

/-! ## D. The inverse-decay theorem -/

/-- **R-0662E607 `adj:lem:inverse-decay`.** For `N ≥ 2`, `c, L > 0`, and arbitrary reals `q`,
with `G = Bmat L c q = L Id + 𝓛_w`, `d = L + 2(N−1)/c`, `τ = 1 − L/d`, and
`B = (2c/d²)(1+4τ+τ²)/(1−τ)⁴`, every entry satisfies `0 ≤ (G⁻¹)_jk ≤ (L⁻¹ + B)/(1+(q_j−q_k)²)`. -/
theorem inverse_gaudin_decay {N : ℕ} (hN : 2 ≤ N) {L c : ℝ} (hL : 0 < L) (hc : 0 < c)
    (q : Fin N → ℝ) (d τ B : ℝ)
    (hd : d = L + 2 * ((N : ℝ) - 1) / c)
    (hτ : τ = 1 - L / d)
    (hB : B = 2 * c / d ^ 2 * (1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4) (j k : Fin N) :
    0 ≤ (Bmat L c q)⁻¹ j k ∧ (Bmat L c q)⁻¹ j k ≤ (L⁻¹ + B) / (1 + (q j - q k) ^ 2) := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcost : 0 < 2 * ((N : ℝ) - 1) / c := div_pos (by linarith) hc
  have hdL : L < d := by
    rw [hd]
    linarith
  have hdpos : 0 < d := by linarith
  have hd0 : d ≠ 0 := hdpos.ne'
  have hc2 : 0 < 2 * c := by linarith
  have hLd : 0 < L / d := div_pos hL hdpos
  have hτ0 : 0 ≤ τ := by
    rw [hτ]
    have : L / d ≤ 1 := (div_le_one hdpos).mpr hdL.le
    linarith
  have hτ1 : τ < 1 := by
    rw [hτ]
    linarith
  have h1τ : (1 - τ) ≠ 0 := (by linarith : (0 : ℝ) < 1 - τ).ne'
  have hB0 : 0 ≤ B := by
    rw [hB]
    apply div_nonneg
    · apply mul_nonneg
      · exact div_nonneg hc2.le (sq_nonneg d)
      · nlinarith [sq_nonneg τ]
    · positivity
  obtain ⟨P, hPdef⟩ : ∃ P : Matrix (Fin N) (Fin N) ℝ,
      P = (1 : Matrix (Fin N) (Fin N) ℝ) - d⁻¹ • Bmat L c q := ⟨_, rfl⟩
  have hPnn : ∀ i l, 0 ≤ P i l := fun i l => by
    rw [hPdef]
    exact ig_P_nonneg hN hc hdpos hd q i l
  have hProw : ∀ i, ∑ l, P i l = τ := fun i => by
    rw [hPdef, ig_P_row_sum, hτ]
    ring
  have hPsym : ∀ i l, P i l = P l i := fun i l => by
    rw [hPdef]
    exact ig_P_symm q d i l
  -- invertibility of G, from the frozen OrderedResponse module
  have hunit : IsUnit (Bmat L c q).det := Bmat_isUnit_det hL hc q
  have hinv : (Bmat L c q)⁻¹ * Bmat L c q = 1 := Matrix.nonsing_inv_mul _ hunit
  -- G = d (Id − P)
  have hG_eq : Bmat L c q = d • (1 - P) := by
    rw [hPdef, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hd0, one_smul]
  -- Neumann partial sums: G · Σ_{ℓ<n} P^ℓ = d (Id − P^n)
  have hSG : ∀ n : ℕ, Bmat L c q * (∑ l ∈ range n, P ^ l) = d • (1 - P ^ n) := by
    intro n
    rw [hG_eq, smul_mul_assoc, mul_neg_geom_sum]
  have hkey : ∀ n : ℕ, ∑ l ∈ range n, P ^ l = d • ((Bmat L c q)⁻¹ - (Bmat L c q)⁻¹ * P ^ n) := by
    intro n
    have h1 : (Bmat L c q)⁻¹ * (Bmat L c q * ∑ l ∈ range n, P ^ l)
        = ∑ l ∈ range n, P ^ l := by
      rw [← mul_assoc, hinv, one_mul]
    rw [← h1, hSG n, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one]
  -- limits of the partial sums
  have hlim : ∀ i l : Fin N,
      Tendsto (fun n : ℕ => (∑ m ∈ range n, P ^ m) i l) atTop
        (𝓝 (d * (Bmat L c q)⁻¹ i l)) := by
    intro i l
    have hPn : ∀ m l' : Fin N, Tendsto (fun n : ℕ => (P ^ n) m l') atTop (𝓝 0) := by
      intro m l'
      exact squeeze_zero (fun n => ig_pow_nonneg hPnn n m l')
        (fun n => ig_pow_le hPnn hProw n m l')
        (tendsto_pow_atTop_nhds_zero_of_lt_one hτ0 hτ1)
    have hE : Tendsto (fun n : ℕ => ∑ m, (Bmat L c q)⁻¹ i m * (P ^ n) m l) atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ : Finset (Fin N))
        (fun m _ => (hPn m l).const_mul ((Bmat L c q)⁻¹ i m))
      simpa using this
    have h2 := (tendsto_const_nhds (x := d * (Bmat L c q)⁻¹ i l)).sub (hE.const_mul d)
    rw [mul_zero, sub_zero] at h2
    refine h2.congr fun n => ?_
    rw [hkey n, Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_apply, smul_eq_mul, mul_sub]
  -- nonnegativity of G⁻¹
  have hnn : ∀ i l : Fin N, 0 ≤ (Bmat L c q)⁻¹ i l := by
    intro i l
    have hS : 0 ≤ d * (Bmat L c q)⁻¹ i l :=
      ge_of_tendsto' (hlim i l) fun n => by
        rw [Matrix.sum_apply]
        exact Finset.sum_nonneg fun m _ => ig_pow_nonneg hPnn m i l
    by_contra hneg
    have hneg' : (Bmat L c q)⁻¹ i l < 0 := lt_of_not_ge hneg
    have := mul_neg_of_pos_of_neg hdpos hneg'
    linarith
  -- row sums of G⁻¹ equal L⁻¹ (since G·1 = L·1)
  have hGi_row : ∀ i, ∑ m, (Bmat L c q)⁻¹ i m = L⁻¹ := by
    intro i
    have hGo : Bmat L c q *ᵥ (fun _ => (1 : ℝ)) = L • (fun _ => (1 : ℝ)) := by
      funext l
      rw [mulVec_Bmat_eq]
      simp
    have h1 : (Bmat L c q)⁻¹ *ᵥ (Bmat L c q *ᵥ (fun _ => (1 : ℝ))) = fun _ => (1 : ℝ) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    rw [hGo, Matrix.mulVec_smul] at h1
    have h2 := congrFun h1 i
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : ∑ m, (Bmat L c q)⁻¹ i m = ((Bmat L c q)⁻¹ *ᵥ (fun _ => (1 : ℝ))) i := by
      simp [Matrix.mulVec, dotProduct]
    rw [h3]
    have hLne : L ≠ 0 := hL.ne'
    calc ((Bmat L c q)⁻¹ *ᵥ (fun _ => (1 : ℝ))) i
        = L⁻¹ * (L * ((Bmat L c q)⁻¹ *ᵥ (fun _ => (1 : ℝ))) i) := by
          rw [← mul_assoc, inv_mul_cancel₀ hLne, one_mul]
      _ = L⁻¹ := by rw [h2, mul_one]
  have hGi_le : ∀ i l, (Bmat L c q)⁻¹ i l ≤ L⁻¹ := by
    intro i l
    rw [← hGi_row i]
    exact Finset.single_le_sum (fun m _ => hnn i m) (Finset.mem_univ l)
  -- the weighted bound (G⁻¹)_jk · R² ≤ B
  have hbound : (Bmat L c q)⁻¹ j k * (q j - q k) ^ 2 ≤ B := by
    by_cases hjk0 : q j - q k = 0
    · rw [hjk0]
      simpa using hB0
    · have hRpos0 : 0 < |q j - q k| := abs_pos.mpr hjk0
      have hjne : j ≠ k := by
        rintro rfl
        simp at hjk0
      have hR2 : (q j - q k) ^ 2 = |q j - q k| ^ 2 := (sq_abs _).symm
      rw [hR2, hB]
      set R := |q j - q k| with hRdef
      have hRpos : 0 < R := hRpos0
      have hR0 : R ≠ 0 := hRpos.ne'
      have hK : 0 ≤ 2 * c / (d * R ^ 2) :=
        div_nonneg hc2.le (mul_nonneg hdpos.le (sq_nonneg _))
      have hPk : ∀ m : ℕ, (P ^ (m + 1)) j k ≤ 2 * c / (d * R ^ 2) * (((m : ℝ) + 1) ^ 3 * τ ^ m) := by
        intro m
        have hn : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        have hn0 : (m : ℝ) + 1 ≠ 0 := hn.ne'
        have hM : 0 ≤ 2 * c * ((m : ℝ) + 1) ^ 2 / (d * R ^ 2) :=
          div_nonneg (mul_nonneg hc2.le (sq_nonneg _)) (mul_nonneg hdpos.le (sq_nonneg _))
        have hpb := ig_path_bound hPnn hProw hPsym hτ0 hM (x := q) (r := R / ((m : ℝ) + 1))
          (fun u v huv => by
            rw [hPdef]
            exact ig_P_long_le hc hdpos q hRpos hn u v huv) m j k
          (by
            field_simp
            exact hRdef.symm)
        calc (P ^ (m + 1)) j k
            ≤ ((m : ℝ) + 1) * (2 * c * ((m : ℝ) + 1) ^ 2 / (d * R ^ 2)) * τ ^ m := hpb
          _ = 2 * c / (d * R ^ 2) * (((m : ℝ) + 1) ^ 3 * τ ^ m) := by ring
      have h0 : (P ^ 0) j k = 0 := by
        rw [pow_zero, Matrix.one_apply_ne hjne]
      have hpart : ∀ n : ℕ, (∑ m ∈ range (n + 1), P ^ m) j k
          ≤ 2 * c / (d * R ^ 2) * ((1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4) := by
        intro n
        rw [Matrix.sum_apply, Finset.sum_range_succ', h0, add_zero]
        calc ∑ m ∈ range n, (P ^ (m + 1)) j k
            ≤ ∑ m ∈ range n, 2 * c / (d * R ^ 2) * (((m : ℝ) + 1) ^ 3 * τ ^ m) :=
              Finset.sum_le_sum fun m _ => hPk m
          _ = 2 * c / (d * R ^ 2) * ∑ m ∈ range n, ((m : ℝ) + 1) ^ 3 * τ ^ m := by
              rw [Finset.mul_sum]
          _ ≤ 2 * c / (d * R ^ 2) * ((1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4) :=
              mul_le_mul_of_nonneg_left (ig_partial_le hτ0 hτ1 n) hK
      have hlim' : Tendsto (fun n : ℕ => (∑ m ∈ range (n + 1), P ^ m) j k) atTop
          (𝓝 (d * (Bmat L c q)⁻¹ j k)) :=
        (hlim j k).comp (tendsto_add_atTop_nat 1)
      have hle := le_of_tendsto' hlim' hpart
      have hkey2 : (2 * c / (d * R ^ 2) * ((1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4)) * (R ^ 2 / d)
          = 2 * c / d ^ 2 * (1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4 := by
        field_simp
      calc (Bmat L c q)⁻¹ j k * R ^ 2 = (d * (Bmat L c q)⁻¹ j k) * (R ^ 2 / d) := by
            field_simp
        _ ≤ (2 * c / (d * R ^ 2) * ((1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4)) * (R ^ 2 / d) :=
            mul_le_mul_of_nonneg_right hle (div_nonneg (sq_nonneg _) hdpos.le)
        _ = 2 * c / d ^ 2 * (1 + 4 * τ + τ ^ 2) / (1 - τ) ^ 4 := hkey2
  refine ⟨hnn j k, ?_⟩
  rw [le_div_iff₀ (by positivity), mul_add, mul_one]
  linarith [hGi_le j k, hbound]

#print axioms QuantumNLS.InverseGaudinDecay.ig_pow_nonneg
#print axioms QuantumNLS.InverseGaudinDecay.ig_pow_row_sum
#print axioms QuantumNLS.InverseGaudinDecay.ig_pow_col_sum
#print axioms QuantumNLS.InverseGaudinDecay.ig_pow_le
#print axioms QuantumNLS.InverseGaudinDecay.ig_pow_mono
#print axioms QuantumNLS.InverseGaudinDecay.ig_tail_succ
#print axioms QuantumNLS.InverseGaudinDecay.ig_pow_split
#print axioms QuantumNLS.InverseGaudinDecay.ig_split_PQ
#print axioms QuantumNLS.InverseGaudinDecay.ig_igS_nonneg
#print axioms QuantumNLS.InverseGaudinDecay.ig_igS_le
#print axioms QuantumNLS.InverseGaudinDecay.ig_igQ_nonneg
#print axioms QuantumNLS.InverseGaudinDecay.ig_igQ_le
#print axioms QuantumNLS.InverseGaudinDecay.ig_igS_ne_zero_lt
#print axioms QuantumNLS.InverseGaudinDecay.ig_igS_pow_far
#print axioms QuantumNLS.InverseGaudinDecay.ig_sum_swap_mul
#print axioms QuantumNLS.InverseGaudinDecay.ig_term_bound
#print axioms QuantumNLS.InverseGaudinDecay.ig_path_bound
#print axioms QuantumNLS.InverseGaudinDecay.ig_tailT_rec
#print axioms QuantumNLS.InverseGaudinDecay.ig_tailT_one
#print axioms QuantumNLS.InverseGaudinDecay.ig_partial_closed
#print axioms QuantumNLS.InverseGaudinDecay.ig_tailT_nonneg
#print axioms QuantumNLS.InverseGaudinDecay.ig_partial_le
#print axioms QuantumNLS.InverseGaudinDecay.ig_G_action
#print axioms QuantumNLS.InverseGaudinDecay.ig_G_apply_ne
#print axioms QuantumNLS.InverseGaudinDecay.ig_G_apply_self
#print axioms QuantumNLS.InverseGaudinDecay.ig_G_symm
#print axioms QuantumNLS.InverseGaudinDecay.ig_G_row_sum
#print axioms QuantumNLS.InverseGaudinDecay.ig_wt_le
#print axioms QuantumNLS.InverseGaudinDecay.ig_wt_sum_le
#print axioms QuantumNLS.InverseGaudinDecay.ig_P_apply
#print axioms QuantumNLS.InverseGaudinDecay.ig_P_nonneg
#print axioms QuantumNLS.InverseGaudinDecay.ig_P_row_sum
#print axioms QuantumNLS.InverseGaudinDecay.ig_P_symm
#print axioms QuantumNLS.InverseGaudinDecay.ig_P_long_le
#print axioms QuantumNLS.InverseGaudinDecay.inverse_gaudin_decay

end QuantumNLS.InverseGaudinDecay
