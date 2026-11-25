import Mathlib
import QuantumNLS.OrderedResponse

/-!
# R-E36CF4CB `adj:lem:cubic-gaudin-identity`: the cubic Gaudin identity

Source: `source/chapters/quantitative/fourth_moments.tex`, lemma `adj:lem:cubic-gaudin-identity`
(starts at line 10) with its printed proof. No graph prerequisites.

Objects (Lean indices are zero-based; `q : Fin N → ℝ`, `N ≥ 1` is implicit in `Fin N` and
stated as `1 ≤ N` where a sum over all indices needs it):
* `wgt c q j k = w_jk = 2c/(c²+(q_j−q_k)²)`;
* `lapW c q f j = (𝓛_w f)_j = Σ_{k≠j} w_jk (f_j − f_k)`;
* `Gop L c q f j = (G f)_j = L f_j + (𝓛_w f)_j`, that is `G = L Id + 𝓛_w`;
* `mom q = P = Σ_j q_j`, `dsum c q j = d_j = Σ_{k≠j} w_jk`,
  `bsum c q j = b_j = Σ_{k≠j} w_jk (q_j − q_k)`.

Clauses formalized literally:
1. `cubic_gaudin_identity`: the displayed identity
   `(G q³)_j = L q_j³ + 3q_j² b_j + (−4cN+6c) q_j + 3c² q_j d_j − 2cP − c² b_j`, for every `j`.
2. `cubic_coefficients`: `|b_j| ≤ N−1` and `0 ≤ d_j ≤ 2(N−1)/c`, for every `j`.
3. `cubic_response_remainder`: for `v = G⁻¹ δ`, with `δ` supported where `|q_j| ≤ Q` and
   `Σ_j (1+q_j²)|v_j| ≤ W`, the bound
   `|Σ_j q_j³ v_j − (2c/L)(Σ_j v_j) P| ≤ (1/L)[Q³‖δ‖₁ + (3(N−1)+|4cN−6c|+6c(N−1)+c²(N−1))W]`.

Matrix identification: `G` is `QuantumNLS.OrderedResponse.Bmat L c q` (frozen module 5467eeae,
imported read-only). `Gop_eq_mulVec`, `Gmat_eq_Bmat` and `G_identified` prove this. Invertibility of
`G` is `OrderedResponse.Bmat_isUnit_det`.

Route: the printed proof (per-term identity `w(q_j³−q_k³) = 3q_j²(wh) − 3q_j(wh²) + wh³` with
`h = q_j − q_k`, the identities `wh² = 2c − c²w` and `wh³ = 2ch − c²wh` from `w(c²+h²) = 2c`,
and the symmetric pairing of the identity with `v`).

No `sorry`, `admit`, `native_decide`, `axiom`, or added axioms.
-/

noncomputable section
open scoped BigOperators
open Finset Matrix
open QuantumNLS.OrderedResponse

namespace QuantumNLS.CubicGaudinIdentity

variable {N : ℕ}

/-! ## A. Literal objects of the lemma -/

/-- Pair weight `w_jk = 2c/(c²+(q_j−q_k)²)`. -/
def wgt (c : ℝ) (q : Fin N → ℝ) (j k : Fin N) : ℝ := 2 * c / (c ^ 2 + (q j - q k) ^ 2)

/-- Graph Laplacian `(𝓛_w f)_j = Σ_{k≠j} w_jk (f_j − f_k)`. -/
def lapW (c : ℝ) (q f : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ k ∈ univ.erase j, wgt c q j k * (f j - f k)

/-- `G = L Id + 𝓛_w` acting on vectors: `(G f)_j = L f_j + (𝓛_w f)_j`. -/
def Gop (L c : ℝ) (q f : Fin N → ℝ) (j : Fin N) : ℝ := L * f j + lapW c q f j

/-- The total momentum `P = Σ_j q_j`. -/
def mom (q : Fin N → ℝ) : ℝ := ∑ j, q j

/-- `d_j = Σ_{k≠j} w_jk`. -/
def dsum (c : ℝ) (q : Fin N → ℝ) (j : Fin N) : ℝ := ∑ k ∈ univ.erase j, wgt c q j k

/-- `b_j = Σ_{k≠j} w_jk (q_j − q_k)`. -/
def bsum (c : ℝ) (q : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ k ∈ univ.erase j, wgt c q j k * (q j - q k)

/-! ## B. Pointwise facts about the weight -/

lemma wgt_pos {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j k : Fin N) : 0 < wgt c q j k := by
  unfold wgt
  have h0 : 0 < c ^ 2 + (q j - q k) ^ 2 := by
    nlinarith [sq_nonneg (q j - q k), mul_pos hc hc]
  exact div_pos (by linarith) h0

lemma wgt_nonneg {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j k : Fin N) : 0 ≤ wgt c q j k :=
  (wgt_pos hc q j k).le

/-- `w_jk (c² + (q_j−q_k)²) = 2c`. -/
lemma wgt_mul_sq {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j k : Fin N) :
    wgt c q j k * (c ^ 2 + (q j - q k) ^ 2) = 2 * c := by
  unfold wgt
  have h0 : c ^ 2 + (q j - q k) ^ 2 ≠ 0 := by
    have : 0 < c ^ 2 + (q j - q k) ^ 2 := by
      nlinarith [sq_nonneg (q j - q k), mul_pos hc hc]
    exact this.ne'
  exact div_mul_cancel₀ _ h0

/-- `w_jk ≤ 2/c`, since `c² ≤ c² + (q_j−q_k)²`. -/
lemma wgt_le_two_div {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j k : Fin N) :
    wgt c q j k ≤ 2 / c := by
  unfold wgt
  have h0 : 0 < c ^ 2 + (q j - q k) ^ 2 := by
    nlinarith [sq_nonneg (q j - q k), mul_pos hc hc]
  rw [div_le_div_iff₀ h0 hc]
  nlinarith [sq_nonneg (q j - q k)]

/-- `w_jk |q_j − q_k| ≤ 1`, from `2c|h| ≤ c² + h²`. -/
lemma wgt_abs_mul_le_one {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j k : Fin N) :
    wgt c q j k * |q j - q k| ≤ 1 := by
  unfold wgt
  have h0 : 0 < c ^ 2 + (q j - q k) ^ 2 := by
    nlinarith [sq_nonneg (q j - q k), mul_pos hc hc]
  rw [div_mul_eq_mul_div, div_le_one h0]
  nlinarith [sq_abs (q j - q k), sq_nonneg (|q j - q k| - c)]

/-- `|x| ≤ 1 + x²`. -/
lemma absq_le (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  nlinarith [sq_abs x, sq_nonneg (|x| - 1 / 2)]

/-! ## C. Sum-level facts -/

lemma card_erase_real (j : Fin N) : ((univ.erase j).card : ℝ) = (N : ℝ) - 1 := by
  have h1 : 1 ≤ N := j.pos
  rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    Nat.cast_sub h1, Nat.cast_one]

/-- `Σ_{k≠j} (q_j − q_k) = N q_j − P`. -/
lemma sum_erase_sub (q : Fin N → ℝ) (j : Fin N) :
    ∑ k ∈ univ.erase j, (q j - q k) = (N : ℝ) * q j - mom q := by
  have hE : ∑ k ∈ univ.erase j, q k = mom q - q j := by
    have := Finset.add_sum_erase univ q (Finset.mem_univ j)
    unfold mom
    linarith
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, card_erase_real, hE]
  ring

/-- `Σ_{k≠j} w_jk (q_j−q_k)² = 2c(N−1) − c² d_j`. -/
lemma hsum_wh2 {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) :
    ∑ k ∈ univ.erase j, wgt c q j k * (q j - q k) ^ 2
      = 2 * c * ((N : ℝ) - 1) - c ^ 2 * dsum c q j := by
  have h : ∀ k ∈ univ.erase j, wgt c q j k * (q j - q k) ^ 2 = 2 * c - c ^ 2 * wgt c q j k := by
    intro k _
    linear_combination wgt_mul_sq hc q j k
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
    nsmul_eq_mul, card_erase_real]
  unfold dsum
  ring

/-- `Σ_{k≠j} w_jk (q_j−q_k)³ = 2c(N q_j − P) − c² b_j`. -/
lemma hsum_wh3 {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) :
    ∑ k ∈ univ.erase j, wgt c q j k * (q j - q k) ^ 3
      = 2 * c * ((N : ℝ) * q j - mom q) - c ^ 2 * bsum c q j := by
  have h : ∀ k ∈ univ.erase j, wgt c q j k * (q j - q k) ^ 3
      = 2 * c * (q j - q k) - c ^ 2 * (wgt c q j k * (q j - q k)) := by
    intro k _
    linear_combination (q j - q k) * wgt_mul_sq hc q j k
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_erase_sub]
  unfold bsum
  ring

/-! ## D. The cubic Gaudin identity (printed display after "one has exactly") -/

/-- **R-E36CF4CB, displayed identity.** For `c, L > 0` and real `q`, for every `j`:
`(G q³)_j = L q_j³ + 3q_j² b_j + (−4cN+6c) q_j + 3c² q_j d_j − 2cP − c² b_j`. -/
theorem cubic_gaudin_identity {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) :
    Gop L c q (fun i => q i ^ 3) j
      = L * q j ^ 3 + 3 * q j ^ 2 * bsum c q j + (-4 * c * (N : ℝ) + 6 * c) * q j
        + 3 * c ^ 2 * q j * dsum c q j - 2 * c * mom q - c ^ 2 * bsum c q j := by
  have hsplit : ∑ k ∈ univ.erase j, wgt c q j k * (q j ^ 3 - q k ^ 3)
      = 3 * q j ^ 2 * bsum c q j
        - 3 * q j * (∑ k ∈ univ.erase j, wgt c q j k * (q j - q k) ^ 2)
        + ∑ k ∈ univ.erase j, wgt c q j k * (q j - q k) ^ 3 := by
    unfold bsum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  dsimp only [Gop, lapW]
  rw [hsplit, hsum_wh2 hc q j, hsum_wh3 hc q j]
  ring

/-- **R-E36CF4CB, coefficient bounds.** For `c > 0` and every `j`: `|b_j| ≤ N−1`, `0 ≤ d_j`, and
`d_j ≤ 2(N−1)/c`. -/
theorem cubic_coefficients {c : ℝ} (hc : 0 < c) (q : Fin N → ℝ) (j : Fin N) :
    |bsum c q j| ≤ (N : ℝ) - 1 ∧ 0 ≤ dsum c q j ∧ dsum c q j ≤ 2 * ((N : ℝ) - 1) / c := by
  refine ⟨?_, ?_, ?_⟩
  · unfold bsum
    calc |∑ k ∈ univ.erase j, wgt c q j k * (q j - q k)|
        ≤ ∑ k ∈ univ.erase j, |wgt c q j k * (q j - q k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ univ.erase j, (1 : ℝ) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul, abs_of_nonneg (wgt_nonneg hc q j k)]
          exact wgt_abs_mul_le_one hc q j k
      _ = (N : ℝ) - 1 := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_erase_real]
  · unfold dsum
    exact Finset.sum_nonneg fun k _ => wgt_nonneg hc q j k
  · unfold dsum
    calc ∑ k ∈ univ.erase j, wgt c q j k
        ≤ ∑ _k ∈ univ.erase j, (2 / c) := Finset.sum_le_sum fun k _ => wgt_le_two_div hc q j k
      _ = 2 * ((N : ℝ) - 1) / c := by
          rw [Finset.sum_const, nsmul_eq_mul, card_erase_real]
          ring

/-! ## E. Matrix identification `G = OrderedResponse.Bmat` -/

/-- `Bmat` is symmetric. -/
lemma Bmat_transpose (L c : ℝ) (q : Fin N → ℝ) : (Bmat L c q)ᵀ = Bmat L c q := by
  ext j k
  rw [Matrix.transpose_apply]
  unfold Bmat
  by_cases h : j = k
  · subst h
    rfl
  · rw [Matrix.of_apply, Matrix.of_apply, if_neg h, if_neg (Ne.symm h),
      wt_comm c (q k) (q j)]

/-- The operator `G = L Id + 𝓛_w` is the matrix `OrderedResponse.Bmat L c q` (action form). -/
theorem Gop_eq_mulVec (L c : ℝ) (q f : Fin N → ℝ) :
    Gop L c q f = Bmat L c q *ᵥ f := by
  funext j
  rw [mulVec_Bmat_eq]
  rfl

/-- The matrix of `G` (its `k`-th column is `G e_k`) equals `OrderedResponse.Bmat L c q`. -/
theorem Gmat_eq_Bmat (L c : ℝ) (q : Fin N → ℝ) :
    Matrix.of (fun j k => Gop L c q (Pi.single k 1) j) = Bmat L c q := by
  ext j k
  rw [Matrix.of_apply, Gop_eq_mulVec, Matrix.mulVec_single_one]
  rfl

/-- Combined identification: the matrix of `G` is `Bmat`, and `G f = Bmat f` for all `f`. -/
theorem G_identified (L c : ℝ) (q : Fin N → ℝ) :
    Matrix.of (fun j k => Gop L c q (Pi.single k 1) j) = Bmat L c q ∧
      ∀ f : Fin N → ℝ, Gop L c q f = Bmat L c q *ᵥ f :=
  ⟨Gmat_eq_Bmat L c q, Gop_eq_mulVec L c q⟩

/-- Symmetry of `G`: `Σ_j g_j (G f)_j = Σ_j f_j (G g)_j`. -/
lemma pair_symm (L c : ℝ) (q g f : Fin N → ℝ) :
    ∑ j, g j * Gop L c q f j = ∑ j, f j * Gop L c q g j := by
  have hA : ∀ x : Fin N → ℝ, x ᵥ* Bmat L c q = Bmat L c q *ᵥ x := fun x => by
    rw [← Matrix.vecMul_transpose, Bmat_transpose]
  calc ∑ j, g j * Gop L c q f j = g ⬝ᵥ (Bmat L c q *ᵥ f) := by
        rw [Gop_eq_mulVec]
        rfl
    _ = (g ᵥ* Bmat L c q) ⬝ᵥ f := (Matrix.dotProduct_mulVec _ _ _)
    _ = (Bmat L c q *ᵥ g) ⬝ᵥ f := by rw [hA]
    _ = f ⬝ᵥ (Bmat L c q *ᵥ g) := dotProduct_comm _ _
    _ = ∑ j, f j * Gop L c q g j := by
        rw [Gop_eq_mulVec]
        rfl

/-! ## F. The remainder bound (printed second display) -/

/-- **R-E36CF4CB, remainder bound.** Let `N ≥ 1`, `L, c > 0`, `v = G⁻¹ δ` (with `G` identified
with `Bmat`), `δ` supported where `|q_j| ≤ Q`, and `Σ_j (1+q_j²)|v_j| ≤ W`. Then
`|Σ_j q_j³ v_j − (2c/L)(Σ_j v_j) P| ≤ (1/L)[Q³‖δ‖₁ + (3(N−1)+|4cN−6c|+6c(N−1)+c²(N−1))W]`. -/
theorem cubic_response_remainder {L c : ℝ} (hN : 1 ≤ N) (hL : 0 < L) (hc : 0 < c)
    (q δ v : Fin N → ℝ) (Q W : ℝ)
    (hv : v = (Bmat L c q)⁻¹ *ᵥ δ)
    (hsupp : ∀ j, δ j ≠ 0 → |q j| ≤ Q)
    (hW : ∑ j, (1 + q j ^ 2) * |v j| ≤ W) :
    |∑ j, q j ^ 3 * v j - 2 * c / L * (∑ j, v j) * mom q|
      ≤ 1 / L * (Q ^ 3 * ∑ j, |δ j|
          + (3 * ((N : ℝ) - 1) + |4 * c * (N : ℝ) - 6 * c| + 6 * c * ((N : ℝ) - 1)
              + c ^ 2 * ((N : ℝ) - 1)) * W) := by
  have hN1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hL0 : L ≠ 0 := hL.ne'
  have hc0 : c ≠ 0 := hc.ne'
  -- (1) `G v = δ`, from `v = G⁻¹ δ` and the identification `G = Bmat`.
  have hGv : ∀ j, Gop L c q v j = δ j := by
    have h1 : Gop L c q v = δ := by
      rw [Gop_eq_mulVec, hv, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (Bmat_isUnit_det hL hc q), Matrix.one_mulVec]
    intro j
    exact congrFun h1 j
  -- (2) pairing the identity with `v`, by symmetry of `G`.
  have hpair : ∑ j, v j * Gop L c q (fun i => q i ^ 3) j = ∑ j, q j ^ 3 * δ j := by
    rw [pair_symm L c q v (fun i => q i ^ 3)]
    simp only [hGv]
  have hexp : ∑ j, v j * Gop L c q (fun i => q i ^ 3) j
      = L * ∑ j, q j ^ 3 * v j + 3 * ∑ j, q j ^ 2 * bsum c q j * v j
        + (-4 * c * (N : ℝ) + 6 * c) * ∑ j, q j * v j
        + 3 * c ^ 2 * ∑ j, q j * dsum c q j * v j
        - 2 * c * mom q * ∑ j, v j - c ^ 2 * ∑ j, bsum c q j * v j := by
    have hterm : ∀ j, v j * Gop L c q (fun i => q i ^ 3) j
        = L * (q j ^ 3 * v j) + 3 * (q j ^ 2 * bsum c q j * v j)
          + (-4 * c * (N : ℝ) + 6 * c) * (q j * v j)
          + 3 * c ^ 2 * (q j * dsum c q j * v j)
          - 2 * c * mom q * v j - c ^ 2 * (bsum c q j * v j) := by
      intro j
      rw [cubic_gaudin_identity hL hc q j]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have key : L * ∑ j, q j ^ 3 * v j - 2 * c * mom q * ∑ j, v j
      = ∑ j, q j ^ 3 * δ j - 3 * ∑ j, q j ^ 2 * bsum c q j * v j
        - (-4 * c * (N : ℝ) + 6 * c) * ∑ j, q j * v j
        - 3 * c ^ 2 * ∑ j, q j * dsum c q j * v j + c ^ 2 * ∑ j, bsum c q j * v j := by
    linear_combination hpair - hexp
  -- (3) bounds on the five sums, from the coefficient bounds and `Σ(1+q²)|v| ≤ W`.
  have hsumK : ∀ (K : ℝ) (f : Fin N → ℝ), 0 ≤ K →
      (∀ j, |f j| ≤ K * ((1 + q j ^ 2) * |v j|)) → |∑ j, f j| ≤ K * W := by
    intro K f hK hf
    calc |∑ j, f j| ≤ ∑ j, |f j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, K * ((1 + q j ^ 2) * |v j|) := Finset.sum_le_sum fun j _ => hf j
      _ = K * ∑ j, (1 + q j ^ 2) * |v j| := by rw [Finset.mul_sum]
      _ ≤ K * W := mul_le_mul_of_nonneg_left hW hK
  have hS2 : |∑ j, q j ^ 2 * bsum c q j * v j| ≤ ((N : ℝ) - 1) * W := by
    refine hsumK ((N : ℝ) - 1) (fun j => q j ^ 2 * bsum c q j * v j) hN1 (fun j => ?_)
    obtain ⟨hb, -, -⟩ := cubic_coefficients hc q j
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (q j))]
    have h1 : q j ^ 2 * |bsum c q j| ≤ q j ^ 2 * ((N : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right h1 (abs_nonneg (v j))
    nlinarith [mul_nonneg hN1 (abs_nonneg (v j))]
  have hS3 : |∑ j, q j ^ 3 * δ j| ≤ Q ^ 3 * ∑ j, |δ j| := by
    calc |∑ j, q j ^ 3 * δ j| ≤ ∑ j, |q j ^ 3 * δ j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, Q ^ 3 * |δ j| := by
          refine Finset.sum_le_sum fun j _ => ?_
          by_cases hd : δ j = 0
          · simp [hd]
          · rw [abs_mul, abs_pow]
            have h3 : |q j| ^ 3 ≤ Q ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hsupp j hd) 3
            exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      _ = Q ^ 3 * ∑ j, |δ j| := by rw [Finset.mul_sum]
  have hS3' : |∑ j, q j * v j| ≤ W := by
    have h := hsumK 1 (fun j => q j * v j) zero_le_one (fun j => by
      rw [abs_mul, one_mul]
      exact mul_le_mul_of_nonneg_right (absq_le _) (abs_nonneg _))
    simpa only [one_mul] using h
  have hS4 : |∑ j, q j * dsum c q j * v j| ≤ (2 * ((N : ℝ) - 1) / c) * W := by
    refine hsumK (2 * ((N : ℝ) - 1) / c) (fun j => q j * dsum c q j * v j)
      (div_nonneg (by linarith) hc.le) (fun j => ?_)
    obtain ⟨hd0, hdle⟩ := (cubic_coefficients hc q j).2
    rw [abs_mul, abs_mul, abs_of_nonneg hd0]
    have h1 : |q j| * dsum c q j ≤ (1 + q j ^ 2) * (2 * ((N : ℝ) - 1) / c) :=
      mul_le_mul (absq_le _) hdle hd0 (by positivity)
    calc |q j| * dsum c q j * |v j|
        ≤ (1 + q j ^ 2) * (2 * ((N : ℝ) - 1) / c) * |v j| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = (2 * ((N : ℝ) - 1) / c) * ((1 + q j ^ 2) * |v j|) := by ring
  have hS6 : |∑ j, bsum c q j * v j| ≤ ((N : ℝ) - 1) * W := by
    refine hsumK ((N : ℝ) - 1) (fun j => bsum c q j * v j) hN1 (fun j => ?_)
    obtain ⟨hb, -, -⟩ := cubic_coefficients hc q j
    rw [abs_mul]
    have h1 := mul_le_mul_of_nonneg_right hb (abs_nonneg (v j))
    nlinarith [mul_nonneg (mul_nonneg hN1 (sq_nonneg (q j))) (abs_nonneg (v j))]
  -- (4) the coefficient-weighted bounds.
  have h2 : |3 * ∑ j, q j ^ 2 * bsum c q j * v j| ≤ 3 * (((N : ℝ) - 1) * W) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul_of_nonneg_left hS2 (by norm_num)
  have h3 : |(-4 * c * (N : ℝ) + 6 * c) * ∑ j, q j * v j|
      ≤ |4 * c * (N : ℝ) - 6 * c| * W := by
    have hk : |-4 * c * (N : ℝ) + 6 * c| = |4 * c * (N : ℝ) - 6 * c| := by
      rw [show -4 * c * (N : ℝ) + 6 * c = -(4 * c * (N : ℝ) - 6 * c) by ring, abs_neg]
    rw [abs_mul, hk]
    exact mul_le_mul_of_nonneg_left hS3' (abs_nonneg _)
  have h4 : |3 * c ^ 2 * ∑ j, q j * dsum c q j * v j| ≤ 6 * c * ((N : ℝ) - 1) * W := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 3 * c ^ 2)]
    calc 3 * c ^ 2 * |∑ j, q j * dsum c q j * v j|
        ≤ 3 * c ^ 2 * ((2 * ((N : ℝ) - 1) / c) * W) :=
          mul_le_mul_of_nonneg_left hS4 (by positivity)
      _ = 6 * c * ((N : ℝ) - 1) * W := by field_simp; ring
  have h6 : |c ^ 2 * ∑ j, bsum c q j * v j| ≤ c ^ 2 * (((N : ℝ) - 1) * W) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg c)]
    exact mul_le_mul_of_nonneg_left hS6 (sq_nonneg c)
  -- (5) assemble: `X = (1/L) E` with `E` the right side of `key`.
  have hX : ∑ j, q j ^ 3 * v j - 2 * c / L * (∑ j, v j) * mom q
      = 1 / L * (∑ j, q j ^ 3 * δ j - 3 * ∑ j, q j ^ 2 * bsum c q j * v j
        - (-4 * c * (N : ℝ) + 6 * c) * ∑ j, q j * v j
        - 3 * c ^ 2 * ∑ j, q j * dsum c q j * v j + c ^ 2 * ∑ j, bsum c q j * v j) := by
    rw [← key]
    field_simp
  rw [hX, abs_mul, abs_of_pos (one_div_pos.2 hL)]
  refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.2 hL).le
  obtain ⟨a1, a2⟩ := abs_le.1 hS3
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  obtain ⟨d1, d2⟩ := abs_le.1 h3
  obtain ⟨e1, e2⟩ := abs_le.1 h4
  obtain ⟨f1, f2⟩ := abs_le.1 h6
  rw [abs_le]
  constructor <;> linarith

end QuantumNLS.CubicGaudinIdentity

/-! ## G. Axiom audit (`#print axioms`) -/

#print axioms QuantumNLS.CubicGaudinIdentity.wgt
#print axioms QuantumNLS.CubicGaudinIdentity.lapW
#print axioms QuantumNLS.CubicGaudinIdentity.Gop
#print axioms QuantumNLS.CubicGaudinIdentity.mom
#print axioms QuantumNLS.CubicGaudinIdentity.dsum
#print axioms QuantumNLS.CubicGaudinIdentity.bsum
#print axioms QuantumNLS.CubicGaudinIdentity.wgt_pos
#print axioms QuantumNLS.CubicGaudinIdentity.wgt_nonneg
#print axioms QuantumNLS.CubicGaudinIdentity.wgt_mul_sq
#print axioms QuantumNLS.CubicGaudinIdentity.wgt_le_two_div
#print axioms QuantumNLS.CubicGaudinIdentity.wgt_abs_mul_le_one
#print axioms QuantumNLS.CubicGaudinIdentity.absq_le
#print axioms QuantumNLS.CubicGaudinIdentity.card_erase_real
#print axioms QuantumNLS.CubicGaudinIdentity.sum_erase_sub
#print axioms QuantumNLS.CubicGaudinIdentity.hsum_wh2
#print axioms QuantumNLS.CubicGaudinIdentity.hsum_wh3
#print axioms QuantumNLS.CubicGaudinIdentity.cubic_gaudin_identity
#print axioms QuantumNLS.CubicGaudinIdentity.cubic_coefficients
#print axioms QuantumNLS.CubicGaudinIdentity.Bmat_transpose
#print axioms QuantumNLS.CubicGaudinIdentity.Gop_eq_mulVec
#print axioms QuantumNLS.CubicGaudinIdentity.Gmat_eq_Bmat
#print axioms QuantumNLS.CubicGaudinIdentity.G_identified
#print axioms QuantumNLS.CubicGaudinIdentity.pair_symm
#print axioms QuantumNLS.CubicGaudinIdentity.cubic_response_remainder
