import Mathlib
import QuantumNLS.CorrelationFourierBridge

/-!
# REG-006 stage (b): weighted lattice estimates (`CC:G04:correlation`), checkpoint

Source: `source/chapters/regularity/integer_moments.tex`, lines 176--188 (the Hölder/Sobolev estimate used
for the uniform derivative bounds). Stage (b) of the split REG-006 work.

Proved here (all with standard axioms only):
1. `Wt_pow_le` (Peetre-type): `W(m)^k ≤ 2^k (W(n)^k + W(m−n)^k)` for `W(n) = 1 + |n|`, `k : ℕ`.
2. `Wt_inv_summable`: `Σ_{n ∈ ℤ} W(n)^{−2k} < ∞` for `k ≥ 1`.
3. `l1_bound`: the ℓ¹ bound by the weighted ℓ²: `Σ|b_n| ≤ (Σ W^{−2k})^{1/2} (Σ W^{2k}|b_n|²)^{1/2}`, with the
   explicit constant `C_k = (Σ W^{−2k})^{1/2}`.
4. `coef_weighted_bound`: the realized coefficients of `f ∈ H^k` satisfy
   `(min(1, 2π/L))^k · (Σ W^{2k}|û_f(n)|²)^{1/2} ≤ ‖f‖_{H^k}`, proved from the realized DEF-002 norm
   (`WField.norm_sq_eq_tsum` with `sobolevWeight`), not assumed.

NOT proved here: the Young/convolution bound `‖W^k(u*v)‖₂ ≤ C‖W^k u‖₂‖v‖₁` and the constrained-sum bound
`Σ_{Σn_j=0} ∏|2πn_j/L|^{α_j} ∏|a_j(n_j)| ≤ C ∏ N_j` (item 3 of the task). See the review record.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle Filter
open scoped BigOperators ENNReal

namespace QuantumNLS.CorrelationLatticeBound

open QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.TranslatedCorrelation
  QuantumNLS.CorrelationFourierBridge

/-- The lattice weight `W(n) = 1 + |n|`. -/
def Wt (n : ℤ) : ℝ := 1 + |(n : ℝ)|

theorem one_le_Wt (n : ℤ) : 1 ≤ Wt n := by
  unfold Wt
  linarith [abs_nonneg (n : ℝ)]

theorem Wt_pos (n : ℤ) : 0 < Wt n := by linarith [one_le_Wt n]

theorem Wt_sub_le (m n : ℤ) : Wt m ≤ Wt n + Wt (m - n) := by
  unfold Wt
  have h1 : |(m : ℝ)| ≤ |(n : ℝ)| + |((m - n : ℤ) : ℝ)| := by
    have e : (m : ℝ) = (n : ℝ) + ((m - n : ℤ) : ℝ) := by push_cast; ring
    rw [e]
    exact abs_add_le _ _
  linarith

/-- Peetre-type inequality: `W(m)^k ≤ 2^k (W(n)^k + W(m−n)^k)`. -/
theorem Wt_pow_le (k : ℕ) (m n : ℤ) :
    Wt m ^ k ≤ 2 ^ k * (Wt n ^ k + Wt (m - n) ^ k) := by
  have hx := Wt_pos n
  have hy := Wt_pos (m - n)
  have hsum : (Wt n + Wt (m - n)) ^ k ≤ 2 ^ k * (Wt n ^ k + Wt (m - n) ^ k) := by
    rcases le_total (Wt n) (Wt (m - n)) with h | h
    · have h2 : Wt n + Wt (m - n) ≤ 2 * Wt (m - n) := by linarith
      calc (Wt n + Wt (m - n)) ^ k ≤ (2 * Wt (m - n)) ^ k :=
            pow_le_pow_left₀ (by linarith) h2 k
        _ = 2 ^ k * Wt (m - n) ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * (Wt n ^ k + Wt (m - n) ^ k) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have := pow_nonneg hx.le k
            linarith
    · have h2 : Wt n + Wt (m - n) ≤ 2 * Wt n := by linarith
      calc (Wt n + Wt (m - n)) ^ k ≤ (2 * Wt n) ^ k :=
            pow_le_pow_left₀ (by linarith) h2 k
        _ = 2 ^ k * Wt n ^ k := mul_pow _ _ _
        _ ≤ 2 ^ k * (Wt n ^ k + Wt (m - n) ^ k) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            have := pow_nonneg hy.le k
            linarith
  calc Wt m ^ k ≤ (Wt n + Wt (m - n)) ^ k := pow_le_pow_left₀ (Wt_pos m).le (Wt_sub_le m n) k
    _ ≤ 2 ^ k * (Wt n ^ k + Wt (m - n) ^ k) := hsum

/-- `Σ_{n ∈ ℤ} (W(n)^{2k})^{-1} < ∞` for `k ≥ 1`. -/
theorem Wt_inv_summable {k : ℕ} (hk : 1 ≤ k) : Summable fun n : ℤ => (Wt n ^ (2 * k))⁻¹ := by
  have hnat : Summable fun n : ℕ => (Wt (n : ℤ) ^ 2)⁻¹ := by
    have h0 : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.2 (by norm_num)
    have h1 := (summable_nat_add_iff 1).2 h0
    refine h1.congr (fun n => ?_)
    unfold Wt
    have hn : |((n : ℤ) : ℝ)| = (n : ℝ) := by
      rw [Int.cast_natCast]
      exact abs_of_nonneg (Nat.cast_nonneg n)
    rw [hn]
    push_cast
    rw [one_div]
    congr 1
    ring
  have hall : Summable fun n : ℤ => (Wt n ^ 2)⁻¹ := by
    refine Summable.of_nat_of_neg hnat ?_
    refine hnat.congr (fun n => ?_)
    unfold Wt
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hall
  · exact inv_nonneg.2 (pow_nonneg (Wt_pos n).le _)
  · have h1 : Wt n ^ 2 ≤ Wt n ^ (2 * k) := pow_le_pow_right₀ (one_le_Wt n) (by omega)
    exact inv_anti₀ (pow_pos (Wt_pos n) 2) h1

/-- **ℓ¹ bound by the weighted ℓ² norm** (Hölder with `p = q = 2`):
`Σ_n b_n ≤ (Σ_n W^{-2k})^{1/2} (Σ_n W^{2k} b_n²)^{1/2}` for nonnegative `b`. -/
theorem l1_bound {k : ℕ} (hk : 1 ≤ k) {b : ℤ → ℝ} (hb0 : ∀ n, 0 ≤ b n)
    (hb : Summable fun n => Wt n ^ (2 * k) * b n ^ 2) :
    Summable b ∧
      ∑' n, b n ≤ Real.sqrt (∑' n, (Wt n ^ (2 * k))⁻¹) * Real.sqrt (∑' n, Wt n ^ (2 * k) * b n ^ 2) := by
  set f : ℤ → ℝ := fun n => (Wt n ^ k)⁻¹ with hf
  set g : ℤ → ℝ := fun n => Wt n ^ k * b n with hg
  have hfg : ∀ n, f n * g n = b n := by
    intro n
    have hk0 : Wt n ^ k ≠ 0 := (pow_pos (Wt_pos n) k).ne'
    simp only [hf, hg]
    field_simp
  have hf0 : ∀ n, 0 ≤ f n := fun n => inv_nonneg.2 (pow_nonneg (Wt_pos n).le _)
  have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (pow_nonneg (Wt_pos n).le _) (hb0 n)
  have hfsq : ∀ n, f n ^ (2 : ℝ) = (Wt n ^ (2 * k))⁻¹ := by
    intro n
    rw [Real.rpow_two]
    simp only [hf]
    rw [inv_pow, ← pow_mul, mul_comm]
  have hgsq : ∀ n, g n ^ (2 : ℝ) = Wt n ^ (2 * k) * b n ^ 2 := by
    intro n
    rw [Real.rpow_two]
    simp only [hg]
    rw [mul_pow, ← pow_mul, mul_comm 2 k]
  have hfs : Summable fun i => f i ^ (2 : ℝ) := by
    refine (Wt_inv_summable hk).congr (fun n => ?_)
    exact (hfsq n).symm
  have hgs : Summable fun i => g i ^ (2 : ℝ) := by
    refine hb.congr (fun n => ?_)
    exact (hgsq n).symm
  obtain ⟨hsumfg, hineq⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two hf0 hg0 hfs hgs
  have e1 : ∑' i, f i ^ (2 : ℝ) = ∑' n, (Wt n ^ (2 * k))⁻¹ := tsum_congr hfsq
  have e2 : ∑' i, g i ^ (2 : ℝ) = ∑' n, Wt n ^ (2 * k) * b n ^ 2 := tsum_congr hgsq
  have hbeq : (fun n => b n) = fun n => f n * g n := funext fun n => (hfg n).symm
  refine ⟨?_, ?_⟩
  · exact hsumfg.congr hfg
  · have hsum_b : ∑' n, b n = ∑' i, f i * g i := tsum_congr (fun n => (hfg n).symm)
    rw [hsum_b, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    rw [e1, e2] at hineq
    exact hineq

variable {L : ℝ} [Fact (0 < L)]

/-- The realized coefficients `coefH hk f` are the Fourier coefficients of the `L²` class of `f`. -/
theorem coefH_eq_fourierL2 {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) (n : ℤ) :
    coefH hk f n = fourierL2 L f.val n := by
  unfold coefH
  rw [toF1_val]

/-- Comparison of the realized DEF-002 weight with the lattice weight: with `a = 2π/L`,
`min(1,a)^{2k} W(n)^{2k} ≤ sobolevWeight L k n ≤ max(1,a)^{2k} W(n)^{2k}`. -/
theorem sobolev_weight_comp (L : ℝ) (hL : 0 < L) (k : ℕ) (n : ℤ) :
    (min 1 (2 * Real.pi / L)) ^ (2 * k) * Wt n ^ (2 * k) ≤ sobolevWeight L (k : ℝ) n ∧
      sobolevWeight L (k : ℝ) n ≤ (max 1 (2 * Real.pi / L)) ^ (2 * k) * Wt n ^ (2 * k) := by
  have ha0 : 0 < 2 * Real.pi / L := div_pos (by positivity) hL
  have harg : 2 * Real.pi * (n : ℝ) / L = (2 * Real.pi / L) * (n : ℝ) := by ring
  have habs : |(2 * Real.pi / L) * (n : ℝ)| = (2 * Real.pi / L) * |(n : ℝ)| := by
    rw [abs_mul, abs_of_pos ha0]
  have hbase : sobolevWeight L (k : ℝ) n = (1 + (2 * Real.pi / L) * |(n : ℝ)|) ^ (2 * k) := by
    unfold sobolevWeight
    rw [harg, habs, show 2 * (k : ℝ) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  rw [hbase]
  have hm1 : min 1 (2 * Real.pi / L) ≤ 1 := min_le_left _ _
  have hma : min 1 (2 * Real.pi / L) ≤ 2 * Real.pi / L := min_le_right _ _
  have hM1 : 1 ≤ max 1 (2 * Real.pi / L) := le_max_left _ _
  have hMa : 2 * Real.pi / L ≤ max 1 (2 * Real.pi / L) := le_max_right _ _
  have hm0 : 0 < min 1 (2 * Real.pi / L) := lt_min one_pos ha0
  have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hlow : min 1 (2 * Real.pi / L) * Wt n ≤ 1 + (2 * Real.pi / L) * |(n : ℝ)| := by
    unfold Wt
    nlinarith [mul_le_mul_of_nonneg_right hma hn0]
  have hup : 1 + (2 * Real.pi / L) * |(n : ℝ)| ≤ max 1 (2 * Real.pi / L) * Wt n := by
    unfold Wt
    nlinarith [mul_le_mul_of_nonneg_right hMa hn0]
  have hnn : 0 ≤ 1 + (2 * Real.pi / L) * |(n : ℝ)| := by
    have := mul_nonneg ha0.le hn0
    linarith
  constructor
  · have h := pow_le_pow_left₀ (mul_nonneg hm0.le (Wt_pos n).le) hlow (2 * k)
    rw [mul_pow] at h
    exact h
  · have h := pow_le_pow_left₀ hnn hup (2 * k)
    rw [mul_pow] at h
    exact h

/-- **Coefficient comparison (item 4).** For `f ∈ H^k` (realized DEF-002 space), with `a = 2π/L`:
the weighted ℓ² sum of its realized coefficients is summable and
`min(1,a)^k · (Σ_n W(n)^{2k}|û_f(n)|²)^{1/2} ≤ ‖f‖_{H^k}`. -/
theorem coef_weighted_bound {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) :
    Summable (fun n : ℤ => Wt n ^ (2 * k) * ‖coefH hk f n‖ ^ 2) ∧
      (min 1 (2 * Real.pi / L)) ^ k * Real.sqrt (∑' n : ℤ, Wt n ^ (2 * k) * ‖coefH hk f n‖ ^ 2) ≤
        ‖f‖ := by
  have hL : 0 < L := Fact.out
  have hc : ∀ n, ‖coefH hk f n‖ = ‖fourierL2 L f.val n‖ := fun n => by
    rw [coefH_eq_fourierL2 hk f n]
  simp only [hc]
  set m := min 1 (2 * Real.pi / L) with hm
  have hm0 : 0 < m := lt_min one_pos (div_pos (by positivity) hL)
  have hnorm : ‖f‖ ^ 2 = ∑' n, sobolevWeight L (k : ℝ) n * ‖fourierL2 L f.val n‖ ^ 2 :=
    WField.norm_sq_eq_tsum L f
  have hsumS : Summable (fun n => sobolevWeight L (k : ℝ) n * ‖fourierL2 L f.val n‖ ^ 2) :=
    f.summable
  have hsumW : Summable (fun n => Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (pow_nonneg (Wt_pos n).le _) (sq_nonneg _)) (fun n => ?_)
      (hsumS.mul_left ((m ^ (2 * k))⁻¹))
    have h1 := (sobolev_weight_comp L hL k n).1
    rw [← hm] at h1
    have hc2 : 0 ≤ ‖fourierL2 L f.val n‖ ^ 2 := sq_nonneg _
    have hmk : 0 < m ^ (2 * k) := pow_pos hm0 _
    calc Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2
        = (m ^ (2 * k))⁻¹ * (m ^ (2 * k) * Wt n ^ (2 * k)) * ‖fourierL2 L f.val n‖ ^ 2 := by
          field_simp
      _ ≤ (m ^ (2 * k))⁻¹ * sobolevWeight L (k : ℝ) n * ‖fourierL2 L f.val n‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hc2
          exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hmk.le)
      _ = (m ^ (2 * k))⁻¹ * (sobolevWeight L (k : ℝ) n * ‖fourierL2 L f.val n‖ ^ 2) := by ring
  -- the weighted sum is bounded by the H^k norm
  have hbound : m ^ (2 * k) * ∑' n, Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [← tsum_mul_left, hnorm]
    apply Summable.tsum_le_tsum _ (hsumW.mul_left (m ^ (2 * k))) hsumS
    intro n
    have h1 := (sobolev_weight_comp L hL k n).1
    rw [← hm] at h1
    have hc2 : 0 ≤ ‖fourierL2 L f.val n‖ ^ 2 := sq_nonneg _
    calc m ^ (2 * k) * (Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2)
        = (m ^ (2 * k) * Wt n ^ (2 * k)) * ‖fourierL2 L f.val n‖ ^ 2 := by ring
      _ ≤ sobolevWeight L (k : ℝ) n * ‖fourierL2 L f.val n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 hc2
  refine ⟨hsumW, ?_⟩
  have hsq : m ^ k * Real.sqrt (∑' n, Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2) =
      Real.sqrt (m ^ (2 * k) * ∑' n, Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2) := by
    rw [show m ^ (2 * k) = (m ^ k) ^ 2 by rw [← pow_mul, mul_comm], Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (pow_nonneg hm0.le k)]
  rw [hsq]
  calc Real.sqrt (m ^ (2 * k) * ∑' n, Wt n ^ (2 * k) * ‖fourierL2 L f.val n‖ ^ 2)
      ≤ Real.sqrt (‖f‖ ^ 2) := Real.sqrt_le_sqrt hbound
    _ = ‖f‖ := Real.sqrt_sq (norm_nonneg _)

end QuantumNLS.CorrelationLatticeBound

/-! Axiom audit (every declaration of the checkpoint). -/
#print axioms QuantumNLS.CorrelationLatticeBound.Wt_pow_le
#print axioms QuantumNLS.CorrelationLatticeBound.Wt_inv_summable
#print axioms QuantumNLS.CorrelationLatticeBound.l1_bound
#print axioms QuantumNLS.CorrelationLatticeBound.sobolev_weight_comp
#print axioms QuantumNLS.CorrelationLatticeBound.coef_weighted_bound
#print axioms QuantumNLS.CorrelationLatticeBound.coefH_eq_fourierL2
#print axioms QuantumNLS.CorrelationLatticeBound.Wt_sub_le
#print axioms QuantumNLS.CorrelationLatticeBound.one_le_Wt
#print axioms QuantumNLS.CorrelationLatticeBound.Wt_pos
