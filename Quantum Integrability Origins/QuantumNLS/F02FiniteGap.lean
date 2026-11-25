import Mathlib
import QuantumNLS.AdjacentResponse
import QuantumNLS.F02Round6
import QuantumNLS.IndividualRootBound
import QuantumNLS.OrderedResponse
import QuantumNLS.RootDisplacement

/-!
# CC:F02:finite-gap (R-9E63B373): exact interpolation and active-block bounds

Source: `source-text/chapters/root_response/F02.tex`, Proposition `CC:F02:finite-gap` (line 118) and its proof.

Data: `L > 0`, `c > 0`, an occupation `η : MArr N` with `η_b ≥ 1` (`hb`), integers `a > b` (`hab`), `m = η − e_b + e_a = transfer η hb a`.
`C_k = Ccum η k` (a one-based rank; the zero-based Lean index `i` has `i + 1 = C_k`), labels `n_i = labs η i`, `ñ_i = labs m i`, `ν_i(s) = (1−s) n_i + s ñ_i`
(`nuPath`), `q(s,c) = root L (realLabelForce ν(s)) c` (`qPath`; the unique ordered solution of (CC:F02:real-labels), `F02Round6Derivative.coupling_derivative`),
`B(s,c) = Bmat L c q(s,c)`, `[B^{-1} q]_i = responseVec L c q i` (DEF-051), `Q_2(η) = Σ_i q_i²` with `q = arrRoots L c η`, `p_n = 2πn/L`, `D_N(c) = 2√(c(N−1)/L)`.

`finite_gap` proves the three printed conclusions:
* (gap-integral) `Q_2(m) − Q_2(η) = 4π Σ_{k=b}^{a−1} ∫_0^1 [B(s,c)^{-1} q(s,c)]_{C_k} ds`;
* (gap-coupling) `= (4π/L) Σ_k ∫_0^1 [q − c ∂_c q]_{C_k} ds` (`∂_c` at fixed `ν(s)`);
* (forced-bound) for every `s ∈ [0,1]` and every forced rank `i = C_k`, the two-sided bound with `p_b − D_N − √(cN(N−1)/(4Lη_b))` and `p_a + D_N + √(cN(N−1)/(4Lm_a))`, `m_a = η_a + 1`.
Repeated ranks `C_k` are kept with their multiplicity (the sum is over `k`).

Route as printed: `RootDisplacement` (`deriv_eq_Bmat_inv`, the fractional label path), `AdjacentResponse` (`label_shift`, `rankVec_eq`, `Ccum_transfer`, `Ccum_jump`),
symmetry of `B^{-1}`, the derivative identity (`root_scaled_deriv_eq`), the individual root bound (REG-002 `individual_root_bound`, for real labels through the arctan inversion identity),
ordered response (`OrderedResponse.ordered_response`) and the quadratic bound (`coupling_derivative`), with the donor block / receiver block counting argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators Matrix ContDiff
open Finset

namespace QuantumNLS.F02FiniteGap

open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.AdjacentResponse
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.RootDisplacement
open QuantumNLS.OrderedResponse QuantumNLS.RootContraction
open QuantumNLS.Ext025A6 (realLabelForce f02_roots_joint_analyticAt f02_roots_solve)
open QuantumNLS.RootDisplacementEstimate (pair_identity count_erase)

variable {N : ℕ}

/-! ## 1. Two abstract block estimates -/

/-- Lower bound from a block: all indices of the block lie below `i`, have `f ≤ f_i` and `q ≥ P`. -/
theorem block_lower {L K P : ℝ} (hL : 0 < L) (q f : Fin N → ℝ) (i : Fin N)
    (hz : ∑ j, (q j - L * f j) ^ 2 ≤ K) (S : Finset (Fin N)) (m : ℕ) (hm : 1 ≤ m)
    (hcard : m ≤ S.card) (hS : ∀ j ∈ S, f j ≤ f i ∧ P ≤ q j) :
    P - Real.sqrt (K / m) ≤ L * f i := by
  by_cases hX : P - L * f i ≤ 0
  · have := Real.sqrt_nonneg (K / m)
    linarith
  · push_neg at hX
    have hz' : ∀ j ∈ S, (P - L * f i) ^ 2 ≤ (q j - L * f j) ^ 2 := by
      intro j hj
      obtain ⟨h1, h2⟩ := hS j hj
      have : P - L * f i ≤ q j - L * f j := by nlinarith
      exact pow_le_pow_left₀ hX.le this 2
    have hsum : (S.card : ℝ) * (P - L * f i) ^ 2 ≤ K := by
      calc (S.card : ℝ) * (P - L * f i) ^ 2 = ∑ j ∈ S, (P - L * f i) ^ 2 := by simp
        _ ≤ ∑ j ∈ S, (q j - L * f j) ^ 2 := sum_le_sum hz'
        _ ≤ ∑ j, (q j - L * f j) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => sq_nonneg _)
        _ ≤ K := hz
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm' : (m : ℝ) * (P - L * f i) ^ 2 ≤ K :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)) hsum
    have h2 : (P - L * f i) ^ 2 ≤ K / m := by
      rw [le_div_iff₀ hm0]; nlinarith
    have : P - L * f i ≤ Real.sqrt (K / m) := (le_abs_self _).trans (Real.abs_le_sqrt h2)
    linarith

/-- Upper bound from a block: all indices of the block lie above `i`, have `f_i ≤ f` and `q ≤ P`. -/
theorem block_upper {L K P : ℝ} (hL : 0 < L) (q f : Fin N → ℝ) (i : Fin N)
    (hz : ∑ j, (q j - L * f j) ^ 2 ≤ K) (S : Finset (Fin N)) (m : ℕ) (hm : 1 ≤ m)
    (hcard : m ≤ S.card) (hS : ∀ j ∈ S, f i ≤ f j ∧ q j ≤ P) :
    L * f i ≤ P + Real.sqrt (K / m) := by
  by_cases hY : 0 ≤ P - L * f i
  · have := Real.sqrt_nonneg (K / m)
    linarith
  · push_neg at hY
    have hz' : ∀ j ∈ S, (L * f i - P) ^ 2 ≤ (q j - L * f j) ^ 2 := by
      intro j hj
      obtain ⟨h1, h2⟩ := hS j hj
      have h3 : q j - L * f j ≤ P - L * f i := by nlinarith
      have h4 : L * f i - P ≤ L * f j - q j := by linarith
      exact (pow_le_pow_left₀ (by linarith) h4 2).trans_eq (by ring)
    have hsum : (S.card : ℝ) * (L * f i - P) ^ 2 ≤ K := by
      calc (S.card : ℝ) * (L * f i - P) ^ 2 = ∑ j ∈ S, (L * f i - P) ^ 2 := by simp
        _ ≤ ∑ j ∈ S, (q j - L * f j) ^ 2 := sum_le_sum hz'
        _ ≤ ∑ j, (q j - L * f j) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ S) (fun _ _ _ => sq_nonneg _)
        _ ≤ K := hz
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm' : (m : ℝ) * (L * f i - P) ^ 2 ≤ K :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)) hsum
    have h2 : (L * f i - P) ^ 2 ≤ K / m := by
      rw [le_div_iff₀ hm0]; nlinarith
    have : L * f i - P ≤ Real.sqrt (K / m) := (le_abs_self _).trans (Real.abs_le_sqrt h2)
    linarith

theorem card_block (lo hi : ℕ) (h : hi ≤ N) :
    (univ.filter fun j : Fin N => lo ≤ j.val ∧ j.val < hi).card = hi - lo := by
  have himg : (univ.filter fun j : Fin N => lo ≤ j.val ∧ j.val < hi).image Fin.val =
      Finset.Ico lo hi := by
    ext k
    simp only [mem_image, mem_filter, mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hk
      exact ⟨⟨k, by omega⟩, hk, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Nat.card_Ico]

/-! ## 2. The individual root bound for real labels -/

/-- REG-002 for the real-label roots: `|q_j − 2πν_j/L| ≤ 2√(c(N−1)/L)` for monotone real labels `ν`. -/
theorem real_label_root_bound (hN : 1 ≤ N) {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {ν : Fin N → ℝ}
    (hν : Monotone ν) (j : Fin N) :
    |root L (realLabelForce ν) c j - 2 * Real.pi * ν j / L| ≤
      2 * Real.sqrt (c * ((N : ℝ) - 1) / L) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hd := QuantumNLS.F02Round6Derivative.coupling_derivative hL hc hν
  dsimp only at hd
  obtain ⟨hq, -⟩ := hd
  set q := root L (realLabelForce ν) c with hqdef
  have hE : ∀ i : Fin (M + 1), L * (q i - 2 * Real.pi * ν i / L) =
      2 * ∑ k ∈ Finset.univ.erase i, Real.arctan (c / (q i - q k)) := by
    intro i
    have hpair : ∀ k ∈ Finset.univ.erase i,
        2 * Real.arctan ((q i - q k) / c) + 2 * Real.arctan (c / (q i - q k)) =
          if k < i then Real.pi else -Real.pi := by
      intro k hk
      have hne : k ≠ i := Finset.ne_of_mem_erase hk
      have hx : q i - q k ≠ 0 := by
        intro e
        exact hne (hq.injective (sub_eq_zero.1 e)).symm
      rw [pair_identity hc hx]
      simp only [sub_pos, hq.lt_iff_lt]
    have hsplit : ∑ k ∈ Finset.univ.erase i,
        (2 * Real.arctan ((q i - q k) / c) + 2 * Real.arctan (c / (q i - q k))) =
          ∑ k ∈ Finset.univ.erase i, (if k < i then Real.pi else -Real.pi) :=
      Finset.sum_congr rfl hpair
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, count_erase] at hsplit
    have h1 := f02_roots_solve hL hc ν i
    rw [← hqdef] at h1
    have : L * (q i - 2 * Real.pi * ν i / L) = L * q i - 2 * Real.pi * ν i := by
      field_simp
    rw [this]
    push_cast at h1 hsplit
    linarith
  have hp : Monotone (fun i => 2 * Real.pi * ν i / L) := by
    intro i k hik
    have := hν hik
    have hpi := Real.pi_pos
    simp only
    gcongr
  exact QuantumNLS.IndividualRootBound.individual_root_bound (Nat.succ_pos M) hL hc q
    (fun i => 2 * Real.pi * ν i / L) hq hp hE j

/-! ## 3. The interpolation data -/

variable {L c : ℝ}

/-- The real interpolated labels `ν(s) = (1−s) n + s ñ`. -/
def nuPath (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (s : ℝ) : Fin N → ℝ :=
  fun i => (1 - s) * (labs η i : ℝ) + s * (labs (transfer η hb a) i : ℝ)

/-- The roots `q(s,c)` of the real labels `ν(s)`. -/
def qPath (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (s : ℝ) : Fin N → ℝ :=
  root L (realLabelForce (nuPath η hb a s)) c

/-- `[v]_{C_k}`: the coordinate at the rank `C_k` (zero-based index `i` with `i + 1 = C_k`). -/
def atRank (η : MArr N) (k : ℤ) (v : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, if (i.val : ℤ) + 1 = Ccum η k then v i else 0

theorem nuPath_monotone (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) {s : ℝ} (h0 : 0 ≤ s)
    (h1 : s ≤ 1) : Monotone (nuPath η hb a s) := by
  intro i j hij
  have e1 : (labs η i : ℝ) ≤ labs η j := by exact_mod_cast labs_mono η hij
  have e2 : (labs (transfer η hb a) i : ℝ) ≤ labs (transfer η hb a) j := by
    exact_mod_cast labs_mono _ hij
  unfold nuPath
  nlinarith

theorem qPath_eq_frac (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    qPath L c η hb a = fracRoots L c (realLabels (labs η)) (labelIncrement (labs η) (labs (transfer η hb a))) := by
  funext s
  unfold qPath fracRoots
  congr 1
  funext i
  simp only [forcingPath, labelAt, logLabel, realLabels, labelIncrement, realLabelForce, nuPath]
  ring

theorem qPath_zero (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    qPath L c η hb a 0 = arrRoots L c η := by
  rw [qPath_eq_frac, fracRoots_zero]
  rfl

theorem qPath_one (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    qPath L c η hb a 1 = arrRoots L c (transfer η hb a) := by
  rw [qPath_eq_frac, fracRoots_one]
  rfl

/-- `responseVec = (gaudin)⁻¹ q`. -/
theorem responseVec_eq_inverse (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    responseVec L c q = (gaudin L c q).inverse q := by
  have h : gaudin L c q (responseVec L c q) = q := by
    rw [gaudin_eq_Bmat]
    exact gaudin_responseVec hL hc q
  have h2 := (gaudin_isInvertible hL hc q).inverse_apply_self (responseVec L c q)
  rw [h] at h2
  exact h2.symm

/-- `[B^{-1} q] = (q − z)/L` for `z = c ∂_c q`, valid for every real forcing. -/
theorem responseVec_eq_sub (hL : 0 < L) (hc : 0 < c) (b : Fin N → ℝ) (i : Fin N) :
    responseVec L c (root L b c) i =
      (root L b c i - c * deriv (root L b) c i) / L := by
  have h := congrFun (root_scaled_deriv_eq hL hc b) i
  rw [responseVec_eq_inverse hL hc]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h
  field_simp
  linarith

/-! ## 4. Continuity of the integrands -/

theorem continuous_nuPath (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    Continuous (nuPath η hb a) :=
  continuous_pi fun i => by unfold nuPath; fun_prop

theorem analyticAt_qPath (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ)
    (s : ℝ) : AnalyticAt ℝ (qPath L c η hb a) s := by
  have hcoord : ∀ i, AnalyticAt ℝ (fun t : ℝ => nuPath η hb a t i) s := fun i => by
    unfold nuPath
    exact ((analyticAt_const.sub analyticAt_id).mul analyticAt_const).add
      (analyticAt_id.mul analyticAt_const)
  have hp : AnalyticAt ℝ (fun t : ℝ => (c, nuPath η hb a t)) s :=
    analyticAt_const.prod (AnalyticAt.pi hcoord)
  exact (f02_roots_joint_analyticAt hL hc (nuPath η hb a s)).comp
    (f := fun t : ℝ => (c, nuPath η hb a t)) hp

theorem continuous_qPath (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    Continuous (qPath L c η hb a) :=
  continuous_iff_continuousAt.2 fun s => (analyticAt_qPath hL hc η hb a s).continuousAt

/-- `s ↦ c ∂_c q(s,c)` is continuous (joint analyticity of the roots in `(c, ν)`). -/
theorem continuous_dc (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) :
    Continuous fun s => deriv (root L (realLabelForce (nuPath η hb a s))) c := by
  let Fm : ℝ × (Fin N → ℝ) → (Fin N → ℝ) := fun p => root L (realLabelForce p.2) p.1
  have hdc : ∀ s, deriv (root L (realLabelForce (nuPath η hb a s))) c =
      fderiv ℝ Fm (c, nuPath η hb a s) (1, 0) := by
    intro s
    have hF : DifferentiableAt ℝ Fm (c, nuPath η hb a s) :=
      (f02_roots_joint_analyticAt hL hc (nuPath η hb a s)).differentiableAt
    have hpath : HasDerivAt (fun d : ℝ => (d, nuPath η hb a s)) ((1 : ℝ), (0 : Fin N → ℝ)) c :=
      (hasDerivAt_id c).prodMk (hasDerivAt_const c _)
    exact (hF.hasFDerivAt.comp_hasDerivAt c hpath).deriv
  have : (fun s => deriv (root L (realLabelForce (nuPath η hb a s))) c) =
      fun s => fderiv ℝ Fm (c, nuPath η hb a s) (1, 0) := funext hdc
  rw [this]
  refine continuous_iff_continuousAt.2 fun s => ?_
  have hcd : ContDiffAt ℝ ∞ Fm (c, nuPath η hb a s) :=
    (f02_roots_joint_analyticAt hL hc (nuPath η hb a s)).contDiffAt
  have hfd : ContDiffAt ℝ 0 (fderiv ℝ Fm) (c, nuPath η hb a s) :=
    hcd.fderiv_right (by simp)
  have hpc : ContinuousAt (fun t : ℝ => (c, nuPath η hb a t)) s :=
    (continuous_const.prodMk (continuous_nuPath η hb a)).continuousAt
  exact (ContinuousAt.comp (f := fun t : ℝ => (c, nuPath η hb a t)) hfd.continuousAt hpc).clm_apply
    continuousAt_const

theorem continuous_responseVec (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b)
    (a : ℤ) (i : Fin N) :
    Continuous fun s => responseVec L c (qPath L c η hb a s) i := by
  have h : (fun s => responseVec L c (qPath L c η hb a s) i) =
      fun s => (qPath L c η hb a s i - c * deriv (root L (realLabelForce (nuPath η hb a s))) c i) / L :=
    funext fun s => responseVec_eq_sub hL hc _ i
  rw [h]
  refine Continuous.div_const (Continuous.sub ((continuous_apply i).comp (continuous_qPath hL hc η hb a))
    (continuous_const.mul ((continuous_apply i).comp (continuous_dc hL hc η hb a)))) L

theorem continuous_atRank {η : MArr N} (k : ℤ) {v : ℝ → Fin N → ℝ} (hv : ∀ i, Continuous fun s => v s i) :
    Continuous fun s => atRank η k (v s) := by
  unfold atRank
  refine continuous_finset_sum _ fun i _ => ?_
  by_cases h : (i.val : ℤ) + 1 = Ccum η k
  · simpa [h] using hv i
  · simp only [h, if_false]
    exact continuous_const

/-! ## 5. The energy identity -/

theorem hasDerivAt_energy (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) (s : ℝ) :
    HasDerivAt (fun t => ∑ i, qPath L c η hb a t i ^ 2)
      (4 * Real.pi * ∑ k ∈ Finset.Ico b a, atRank η k (responseVec L c (qPath L c η hb a s))) s := by
  rw [qPath_eq_frac]
  set x := realLabels (labs η)
  set δ := labelIncrement (labs η) (labs (transfer η hb a)) with hδ
  have hcoord : ∀ i, HasDerivAt (fun t => fracRoots L c x δ t i)
      (deriv (fracRoots L c x δ) s i) s := fun i => fracRoots_coord_hasDerivAt hL hc x δ s i
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin N)))
    (fun i _ => (hcoord i).pow 2)
  have hd := deriv_eq_Bmat_inv hL hc x δ s
  have hδr : δ = rankVec η b a := by
    funext i; rw [rankVec_eq η hb hab i]; rfl
  set q := fracRoots L c x δ s with hq
  have hsym : ((Bmat L c q)⁻¹)ᵀ = (Bmat L c q)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, jacobian_symm]
  have hrw : responseVec L c q = (Bmat L c q)⁻¹ *ᵥ q := rfl
  have key : ∑ i, 2 * q i * deriv (fracRoots L c x δ) s i =
      4 * Real.pi * ∑ k ∈ Finset.Ico b a, atRank η k (responseVec L c q) := by
    have h1 : ∑ i, 2 * q i * deriv (fracRoots L c x δ) s i =
        2 * (q ⬝ᵥ deriv (fracRoots L c x δ) s) := by
      unfold dotProduct
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hd, hδr]
    have h2 : (fun i => 2 * Real.pi * rankVec η b a i) = (2 * Real.pi) • rankVec η b a := by
      funext i; simp
    rw [h2, Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hsym, ← hrw, smul_eq_mul]
    have h3 : responseVec L c q ⬝ᵥ rankVec η b a =
        ∑ k ∈ Finset.Ico b a, atRank η k (responseVec L c q) := by
      unfold dotProduct rankVec atRank
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> ring
    rw [h3]; ring
  refine HasDerivAt.congr_deriv hsum ?_
  rw [← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  norm_num

theorem gap_integral (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) :
    ∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      4 * Real.pi * ∑ k ∈ Finset.Ico b a,
        ∫ s in (0 : ℝ)..1, atRank η k (responseVec L c (qPath L c η hb a s)) := by
  have hint : ∀ k, IntervalIntegrable (fun s => atRank η k (responseVec L c (qPath L c η hb a s)))
      MeasureTheory.volume 0 1 := fun k =>
    (continuous_atRank k (continuous_responseVec hL hc η hb a)).intervalIntegrable _ _
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t => ∑ i, qPath L c η hb a t i ^ 2)
      (4 * Real.pi * ∑ k ∈ Finset.Ico b a,
        atRank η k (responseVec L c (qPath L c η hb a s))) s :=
    fun s _ => hasDerivAt_energy hL hc η hb hab s
  have hI : IntervalIntegrable (fun s => 4 * Real.pi * ∑ k ∈ Finset.Ico b a,
      atRank η k (responseVec L c (qPath L c η hb a s))) MeasureTheory.volume 0 1 := by
    have : Continuous (fun s => 4 * Real.pi * ∑ k ∈ Finset.Ico b a,
        atRank η k (responseVec L c (qPath L c η hb a s))) :=
      continuous_const.mul (continuous_finset_sum _ fun k _ =>
        continuous_atRank k (continuous_responseVec hL hc η hb a))
    exact this.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hI
  simp only [qPath_one, qPath_zero] at hFTC
  rw [← hFTC, intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum]
  intro k _
  exact hint k

theorem atRank_div (η : MArr N) (k : ℤ) (v : Fin N → ℝ) (L : ℝ) :
    atRank η k (fun i => v i / L) = atRank η k v / L := by
  unfold atRank
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem gap_coupling (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) :
    ∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      (4 * Real.pi / L) * ∑ k ∈ Finset.Ico b a, ∫ s in (0 : ℝ)..1,
        atRank η k (fun i => qPath L c η hb a s i -
          c * deriv (root L (realLabelForce (nuPath η hb a s))) c i) := by
  have e : ∀ k : ℤ, ∫ s in (0 : ℝ)..1, atRank η k (responseVec L c (qPath L c η hb a s)) =
      (∫ s in (0 : ℝ)..1, atRank η k (fun i => qPath L c η hb a s i -
          c * deriv (root L (realLabelForce (nuPath η hb a s))) c i)) / L := by
    intro k
    rw [← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show atRank η k (responseVec L c (qPath L c η hb a s)) = _
    have : responseVec L c (qPath L c η hb a s) = fun i => (qPath L c η hb a s i -
        c * deriv (root L (realLabelForce (nuPath η hb a s))) c i) / L :=
      funext fun i => responseVec_eq_sub hL hc _ i
    rw [this, atRank_div]
  rw [gap_integral hL hc η hb hab, Finset.sum_congr rfl (fun k _ => e k), ← Finset.sum_div]
  ring

/-! ## 6. Block combinatorics -/

theorem donor_facts (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) {i : Fin N} (hi : (i.val : ℤ) + 1 = Ccum η k) (j : Fin N)
    (hj : Ccum η (b - 1) ≤ j.val ∧ j.val < Ccum η b) :
    j ≤ i ∧ b ≤ labs η j ∧ b ≤ labs (transfer η hb a) j := by
  obtain ⟨hbk, hka⟩ := Finset.mem_Ico.mp hk
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Ccum_mono η hbk
    rw [Fin.le_def]
    omega
  · by_contra hcon
    push_neg at hcon
    have h1 : labs η j ≤ b - 1 := by omega
    have h2 := (labs_le_iff η j (b - 1)).1 h1
    omega
  · by_contra hcon
    push_neg at hcon
    have hle : labs (transfer η hb a) j ≤ b - 1 := by omega
    have h2 := (labs_le_iff (transfer η hb a) j (b - 1)).1 hle
    have h3 := Ccum_transfer η hb a (b - 1)
    rw [if_neg (by omega), if_neg (by omega)] at h3
    omega

theorem receiver_facts (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) {i : Fin N} (hi : (i.val : ℤ) + 1 = Ccum η k) (j : Fin N)
    (hj : Ccum (transfer η hb a) (a - 1) ≤ j.val ∧ j.val < Ccum (transfer η hb a) a) :
    i ≤ j ∧ labs η j ≤ a ∧ labs (transfer η hb a) j ≤ a := by
  obtain ⟨hbk, hka⟩ := Finset.mem_Ico.mp hk
  have h3 := Ccum_transfer η hb a (a - 1)
  rw [if_pos (by omega), if_neg (by omega)] at h3
  have h4 := Ccum_transfer η hb a a
  rw [if_pos (by omega), if_pos le_rfl] at h4
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Ccum_mono η (show k ≤ a - 1 by omega)
    rw [Fin.le_def]
    omega
  · rw [labs_le_iff]
    omega
  · rw [labs_le_iff]
    omega

/-! ## 7. The forced-rank bounds -/

theorem forced_bound (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) {k : ℤ} (hk : k ∈ Finset.Ico b a)
    {i : Fin N} (hi : (i.val : ℤ) + 1 = Ccum η k) :
    (2 * Real.pi * b / L - 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) -
        Real.sqrt (c * N * ((N : ℝ) - 1) / (4 * L * (η.1 b : ℝ)))) / L ≤
      responseVec L c (qPath L c η hb a s) i ∧
    responseVec L c (qPath L c η hb a s) i ≤
      (2 * Real.pi * a / L + 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) +
        Real.sqrt (c * N * ((N : ℝ) - 1) / (4 * L * ((η.1 a : ℝ) + 1)))) / L := by
  have hN : 1 ≤ N := Fin.pos_iff_nonempty.2 ⟨i⟩
  have hν := nuPath_monotone η hb a h0 h1
  have hd := QuantumNLS.F02Round6Derivative.coupling_derivative hL hc hν
  dsimp only at hd
  obtain ⟨hord, -, -, -, -, -, hinv, -, hquad⟩ := hd
  set q := qPath L c η hb a s with hqdef
  set f := responseVec L c q with hfdef
  have hf : ∀ j, L * f j = q j - c * deriv (root L (realLabelForce (nuPath η hb a s))) c j := by
    intro j
    have := responseVec_eq_sub hL hc (realLabelForce (nuPath η hb a s)) j
    rw [hfdef, hqdef]
    unfold qPath
    rw [this]
    field_simp
  have hz2 : ∑ j, (q j - L * f j) ^ 2 ≤ c * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) := by
    have := hquad
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have e : ∀ j, q j - L * f j = c * deriv (root L (realLabelForce (nuPath η hb a s))) c j := by
      intro j; rw [hf j]; ring
    simp_rw [e]
    exact this
  have hfmono : Monotone f := by
    by_cases hN1 : 1 < N
    · exact (ordered_response hL hc hN1 q hord).monotone
    · intro x y hxy
      have : x = y := by
        apply Fin.ext
        have := x.2; have := y.2; omega
      rw [this]
  have hroot : ∀ j, |q j - 2 * Real.pi * nuPath η hb a s j / L| ≤
      2 * Real.sqrt (c * ((N : ℝ) - 1) / L) := fun j => real_label_root_bound hN hL hc hν j
  constructor
  · -- donor block
    set S := univ.filter (fun j : Fin N => Ccum η (b - 1) ≤ j.val ∧ j.val < Ccum η b) with hS
    have hcardS : S.card = Ccum η b - Ccum η (b - 1) := card_block _ _ (Ccum_le_N η b)
    have hjump := Ccum_jump η (le_refl b)
    have hcard : (η.1 b) ≤ S.card := by omega
    have hmem : ∀ j ∈ S, f j ≤ f i ∧ 2 * Real.pi * b / L - 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) ≤ q j := by
      intro j hj
      rw [hS, mem_filter] at hj
      obtain ⟨hji, hbj, hbj'⟩ := donor_facts η hb hab hk hi j hj.2
      refine ⟨hfmono hji, ?_⟩
      have hnu : (b : ℝ) ≤ nuPath η hb a s j := by
        have e1 : (b : ℝ) ≤ labs η j := by exact_mod_cast hbj
        have e2 : (b : ℝ) ≤ labs (transfer η hb a) j := by exact_mod_cast hbj'
        unfold nuPath
        nlinarith
      have hr := (abs_le.1 (hroot j)).1
      have : 2 * Real.pi * b / L ≤ 2 * Real.pi * nuPath η hb a s j / L := by
        gcongr
      linarith
    have hm1 : 1 ≤ η.1 b := by exact_mod_cast hb
    have hb' := block_lower hL q f i hz2 S (η.1 b) hm1 hcard hmem
    have hKm : c * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) / (η.1 b : ℝ) =
        c * N * ((N : ℝ) - 1) / (4 * L * (η.1 b : ℝ)) := by
      rw [div_div]
    rw [hKm] at hb'
    rw [div_le_iff₀ hL]
    linarith
  · -- receiver block
    set m := transfer η hb a with hm
    set S := univ.filter (fun j : Fin N => Ccum m (a - 1) ≤ j.val ∧ j.val < Ccum m a) with hS
    have hcardS : S.card = Ccum m a - Ccum m (a - 1) := card_block _ _ (Ccum_le_N m a)
    have hjump := Ccum_jump m (le_refl a)
    have hma : ((m.1 a : ℕ) : ℤ) = η.1 a + 1 := by
      have := transfer_apply η hb a a
      rw [if_neg (by omega), if_pos rfl] at this
      simpa using this
    have hcard : η.1 a + 1 ≤ S.card := by omega
    have hmem : ∀ j ∈ S, f i ≤ f j ∧ q j ≤ 2 * Real.pi * a / L + 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) := by
      intro j hj
      rw [hS, mem_filter] at hj
      obtain ⟨hij, haj, haj'⟩ := receiver_facts η hb hab hk hi j hj.2
      refine ⟨hfmono hij, ?_⟩
      have hnu : nuPath η hb a s j ≤ (a : ℝ) := by
        have e1 : (labs η j : ℝ) ≤ a := by exact_mod_cast haj
        have e2 : (labs (transfer η hb a) j : ℝ) ≤ a := by exact_mod_cast haj'
        unfold nuPath
        nlinarith
      have hr := (abs_le.1 (hroot j)).2
      have : 2 * Real.pi * nuPath η hb a s j / L ≤ 2 * Real.pi * a / L := by
        gcongr
      linarith
    have hm1 : 1 ≤ η.1 a + 1 := by omega
    have hb' := block_upper hL q f i hz2 S (η.1 a + 1) hm1 hcard hmem
    have hKm : c * (N : ℝ) * ((N : ℝ) - 1) / (4 * L) / (((η.1 a + 1 : ℕ)) : ℝ) =
        c * N * ((N : ℝ) - 1) / (4 * L * ((η.1 a : ℝ) + 1)) := by
      rw [div_div]; push_cast; rfl
    rw [hKm] at hb'
    rw [le_div_iff₀ hL]
    linarith

/-! ## 8. The proposition -/

/-- **`CC:F02:finite-gap`** (R-9E63B373). -/
theorem finite_gap (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) :
    (∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      4 * Real.pi * ∑ k ∈ Finset.Ico b a,
        ∫ s in (0 : ℝ)..1, atRank η k (responseVec L c (qPath L c η hb a s))) ∧
    (∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      (4 * Real.pi / L) * ∑ k ∈ Finset.Ico b a, ∫ s in (0 : ℝ)..1,
        atRank η k (fun i => qPath L c η hb a s i -
          c * deriv (root L (realLabelForce (nuPath η hb a s))) c i)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ k ∈ Finset.Ico b a, ∀ i : Fin N, (i.val : ℤ) + 1 = Ccum η k →
      (2 * Real.pi * b / L - 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) -
          Real.sqrt (c * N * ((N : ℝ) - 1) / (4 * L * (η.1 b : ℝ)))) / L ≤
        responseVec L c (qPath L c η hb a s) i ∧
      responseVec L c (qPath L c η hb a s) i ≤
        (2 * Real.pi * a / L + 2 * Real.sqrt (c * ((N : ℝ) - 1) / L) +
          Real.sqrt (c * N * ((N : ℝ) - 1) / (4 * L * ((η.1 a : ℝ) + 1)))) / L) :=
  ⟨gap_integral hL hc η hb hab, gap_coupling hL hc η hb hab,
    fun _ hs _ hk _ hi => forced_bound hL hc η hb hab hs.1 hs.2 hk hi⟩

end QuantumNLS.F02FiniteGap

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.F02FiniteGap.real_label_root_bound
#print axioms QuantumNLS.F02FiniteGap.gap_integral
#print axioms QuantumNLS.F02FiniteGap.gap_coupling
#print axioms QuantumNLS.F02FiniteGap.forced_bound
#print axioms QuantumNLS.F02FiniteGap.finite_gap
