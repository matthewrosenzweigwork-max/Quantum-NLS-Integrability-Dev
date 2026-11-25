import Mathlib
import QuantumNLS.SmoothJ
import QuantumNLS.StepIntegrals
import QuantumNLS.FiniteResponse

/-!
# CC:F04:deterministic-gap (R-C455C541), step 1: the row identity and the strong `L²` limit of the bounded kernel tests

Source: `F04.tex`, Proposition `CC:F04:deterministic-gap` (line 315), proof: the exact row equation (CC:F04:row)
`f_{i} = (x_N + (2κ/N) Σ_{j≠i} f_j/(c_N² + (x_N − q_j)²)) / (L + (2κ/N) Σ_{j≠i} 1/(c_N² + (x_N − q_j)²))`
and "Choose a bounded continuous extension of `(x(λ) − y)^{-2}` that vanishes in a small neighborhood of `x(λ)` ... Composing with the empirical quantiles gives strong `L²` convergence of these bounded kernel tests."

* `row_identity`: for `B f = q` (`FiniteResponse.Bop`), `f_i (L + Σ_{j≠i} w_ij) = q_i + Σ_{j≠i} w_ij f_j`, `w_ij = 2c/(c² + (q_i − q_j)²)`;
* `kk c ε s = 1/(c² + max(s², ε²))`: the bounded extension (equal to `1/(c² + s²)` for `|s| ≥ ε`), `kk_diff` its uniform Lipschitz bound in `(s, c²)`;
* `kernel_L2_tendsto`: if the step quantiles `stepL2 (q_N) → Q` in `L²(0,1)`, `z_N → x`, `c_N → 0`, then the step functions of `kk c_N ε (z_N − q_{j,N})` converge strongly to `kk 0 ε (x − Q(t))` in `L²(0,1)`.
No truncation is needed because `kk` is globally Lipschitz and bounded.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set Finset
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.DetGapRow

open QuantumNLS.FiniteResponse (Bop wt L2N)
open QuantumNLS.StepIntegrals (stepL2 stepF stepL2_ae measurable_stepF norm_sq_step stepL2_sub)
open QuantumNLS.SmoothJ (compL2 compL2_ae norm_compL2_sub_le stepL2_comp)
open QuantumNLS.BulkResponseForm (L2Unit)
open QuantumNLS.QuantileForm (uI)

/-! ## 1. The row identity -/

theorem row_identity {n : ℕ} {L c : ℝ} (q f : Fin n → ℝ) (hf : Bop L c q f = q) (i : Fin n) :
    f i * (L + ∑ j ∈ univ.erase i, wt c (q i) (q j)) =
      q i + ∑ j ∈ univ.erase i, wt c (q i) (q j) * f j := by
  have h := congrFun hf i
  rw [QuantumNLS.FiniteResponse.Bop_eq_erase] at h
  have e : ∑ j ∈ univ.erase i, wt c (q i) (q j) * (f i - f j) =
      f i * ∑ j ∈ univ.erase i, wt c (q i) (q j) - ∑ j ∈ univ.erase i, wt c (q i) (q j) * f j := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e] at h
  linarith

/-! ## 2. The bounded kernel -/

/-- `kk c ε s = 1/(c² + max(s², ε²))`: the bounded extension of `1/(c² + s²)`. -/
def kk (c ε s : ℝ) : ℝ := 1 / (c ^ 2 + max (s ^ 2) (ε ^ 2))

theorem kk_eq {c ε s : ℝ} (h : ε ≤ |s|) (hε : 0 < ε) : kk c ε s = 1 / (c ^ 2 + s ^ 2) := by
  unfold kk
  have h2 : ε ^ 2 ≤ s ^ 2 := by
    rw [← sq_abs s]; exact pow_le_pow_left₀ hε.le h 2
  rw [max_eq_left h2]

theorem kk_pos {c ε : ℝ} (hε : 0 < ε) (s : ℝ) : 0 < kk c ε s := by
  unfold kk
  have : 0 < c ^ 2 + max (s ^ 2) (ε ^ 2) :=
    add_pos_of_nonneg_of_pos (sq_nonneg c) (lt_of_lt_of_le (by positivity) (le_max_right _ _))
  positivity

theorem kk_le {c ε : ℝ} (hε : 0 < ε) (s : ℝ) : kk c ε s ≤ 1 / ε ^ 2 := by
  unfold kk
  have h1 : ε ^ 2 ≤ c ^ 2 + max (s ^ 2) (ε ^ 2) :=
    (le_max_right _ _).trans (by nlinarith [sq_nonneg c])
  exact one_div_le_one_div_of_le (by positivity) h1

theorem phi_ge {ε : ℝ} (hε : 0 < ε) (s : ℝ) : ε * |s| ≤ max (s ^ 2) (ε ^ 2) := by
  rcases le_total |s| ε with h | h
  · calc ε * |s| ≤ ε * ε := mul_le_mul_of_nonneg_left h hε.le
      _ = ε ^ 2 := by ring
      _ ≤ _ := le_max_right _ _
  · calc ε * |s| ≤ |s| * |s| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
      _ = s ^ 2 := by rw [← sq, sq_abs]
      _ ≤ _ := le_max_left _ _

theorem kk_diff {c c' ε s s' : ℝ} (hε : 0 < ε) :
    |kk c ε s - kk c' ε s'| ≤ 2 * |s - s'| / ε ^ 3 + |c ^ 2 - c' ^ 2| / ε ^ 4 := by
  set φ := max (s ^ 2) (ε ^ 2) with hφ
  set φ' := max (s' ^ 2) (ε ^ 2) with hφ'
  have hφ2 : ε ^ 2 ≤ φ := le_max_right _ _
  have hφ2' : ε ^ 2 ≤ φ' := le_max_right _ _
  have hφp : 0 < φ := lt_of_lt_of_le (by positivity) hφ2
  have hφp' : 0 < φ' := lt_of_lt_of_le (by positivity) hφ2'
  have hs1 := phi_ge hε s
  have hs2 := phi_ge hε s'
  have hd1 : 0 < c ^ 2 + φ := by positivity
  have hd2 : 0 < c' ^ 2 + φ' := by positivity
  unfold kk
  rw [← hφ, ← hφ']
  have e : 1 / (c ^ 2 + φ) - 1 / (c' ^ 2 + φ') = ((c' ^ 2 + φ') - (c ^ 2 + φ)) / ((c ^ 2 + φ) * (c' ^ 2 + φ')) := by
    field_simp
  rw [e, abs_div, abs_of_pos (mul_pos hd1 hd2)]
  have hden : φ * φ' ≤ (c ^ 2 + φ) * (c' ^ 2 + φ') := by nlinarith [sq_nonneg c, sq_nonneg c']
  have hnum : |(c' ^ 2 + φ') - (c ^ 2 + φ)| ≤ |φ' - φ| + |c ^ 2 - c' ^ 2| := by
    have := abs_add_le (φ' - φ) (c' ^ 2 - c ^ 2)
    rw [abs_sub_comm (c ^ 2) (c' ^ 2)]
    calc |(c' ^ 2 + φ') - (c ^ 2 + φ)| = |(φ' - φ) + (c' ^ 2 - c ^ 2)| := by ring_nf
      _ ≤ _ := this
  have hφd : |φ' - φ| ≤ |s' - s| * (|s'| + |s|) := by
    have h1 : |φ' - φ| ≤ |s' ^ 2 - s ^ 2| := by
      simpa [hφ, hφ'] using abs_max_sub_max_le_abs (s' ^ 2) (s ^ 2) (ε ^ 2)
    refine h1.trans ?_
    have : s' ^ 2 - s ^ 2 = (s' - s) * (s' + s) := by ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
  have hq : (|s'| + |s|) / (φ * φ') ≤ 2 / ε ^ 3 := by
    have a1 : |s'| / (φ * φ') ≤ 1 / ε ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : ε * |s'| ≤ φ' := hs2
      nlinarith [abs_nonneg s', hφ2, hφp, mul_pos hφp hφp']
    have a2 : |s| / (φ * φ') ≤ 1 / ε ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : ε * |s| ≤ φ := hs1
      nlinarith [abs_nonneg s, hφ2', hφp', mul_pos hφp hφp']
    have : (|s'| + |s|) / (φ * φ') = |s'| / (φ * φ') + |s| / (φ * φ') := by ring
    rw [this]
    have : (2 : ℝ) / ε ^ 3 = 1 / ε ^ 3 + 1 / ε ^ 3 := by ring
    rw [this]
    exact add_le_add a1 a2
  calc |(c' ^ 2 + φ') - (c ^ 2 + φ)| / ((c ^ 2 + φ) * (c' ^ 2 + φ'))
      ≤ (|φ' - φ| + |c ^ 2 - c' ^ 2|) / (φ * φ') := by
        calc _ ≤ |(c' ^ 2 + φ') - (c ^ 2 + φ)| / (φ * φ') :=
              div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hφp hφp') hden
          _ ≤ _ := div_le_div_of_nonneg_right hnum (mul_pos hφp hφp').le
    _ = |φ' - φ| / (φ * φ') + |c ^ 2 - c' ^ 2| / (φ * φ') := by ring
    _ ≤ 2 * |s - s'| / ε ^ 3 + |c ^ 2 - c' ^ 2| / ε ^ 4 := by
        have t1 : |φ' - φ| / (φ * φ') ≤ 2 * |s - s'| / ε ^ 3 := by
          calc |φ' - φ| / (φ * φ') ≤ (|s' - s| * (|s'| + |s|)) / (φ * φ') :=
                div_le_div_of_nonneg_right hφd (mul_pos hφp hφp').le
            _ = |s' - s| * ((|s'| + |s|) / (φ * φ')) := by ring
            _ ≤ |s' - s| * (2 / ε ^ 3) := mul_le_mul_of_nonneg_left hq (abs_nonneg _)
            _ = 2 * |s - s'| / ε ^ 3 := by rw [abs_sub_comm s' s]; ring
        have t2 : |c ^ 2 - c' ^ 2| / (φ * φ') ≤ |c ^ 2 - c' ^ 2| / ε ^ 4 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
          nlinarith [hφ2, hφ2']
        linarith

/-- The kernel test as a function of the root: `y ↦ 1/(x−y)²` cut off at scale `ε`. -/
def hker (x ε y : ℝ) : ℝ := kk 0 ε (x - y)

theorem hker_bdd {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ∀ y, |hker x ε y| ≤ 1 / ε ^ 2 := fun y => by
  unfold hker
  rw [abs_of_pos (kk_pos hε _)]; exact kk_le hε _

theorem hker_lip {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    LipschitzWith ⟨2 / ε ^ 3, by positivity⟩ (hker x ε) := by
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  have h := kk_diff (c := 0) (c' := 0) (ε := ε) (s := x - y) (s' := x - y') hε
  simp only [sub_self, abs_zero, zero_div, add_zero] at h
  simp only [Real.dist_eq]
  show |hker x ε y - hker x ε y'| ≤ 2 / ε ^ 3 * |y - y'|
  have e : |x - y - (x - y')| = |y - y'| := by
    rw [show x - y - (x - y') = -(y - y') by ring, abs_neg]
  rw [e] at h
  calc |hker x ε y - hker x ε y'| ≤ 2 * |y - y'| / ε ^ 3 := h
    _ = 2 / ε ^ 3 * |y - y'| := by ring

/-! ## 3. Strong `L²` convergence of the kernel tests -/

theorem norm_stepL2_le {n : ℕ} (v : Fin (n + 1) → ℝ) {e : ℝ} (he : 0 ≤ e) (hv : ∀ j, |v j| ≤ e) :
    ‖stepL2 v‖ ≤ e := by
  have h := norm_sq_step (Nat.succ_pos n) v
  have h2 : L2N (n + 1) v ≤ e ^ 2 := by
    unfold L2N
    have hs : ∑ j, v j ^ 2 ≤ ∑ _j : Fin (n + 1), e ^ 2 :=
      Finset.sum_le_sum fun j _ => by
        have := hv j
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    calc 1 / ((n + 1 : ℕ) : ℝ) * ∑ j, v j ^ 2 ≤ 1 / ((n + 1 : ℕ) : ℝ) * ∑ _j : Fin (n + 1), e ^ 2 :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = e ^ 2 := by simp; field_simp
  have : ‖stepL2 v‖ ^ 2 ≤ e ^ 2 := by rw [h]; exact h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) he (by norm_num)).1 this

theorem kernel_L2_tendsto {x ε : ℝ} (hε : 0 < ε) {q : (n : ℕ) → Fin (n + 1) → ℝ} {z c : ℕ → ℝ}
    {Q : ℝ → ℝ} (hQm : Measurable Q) {Q0 : L2Unit} (hQ0 : (Q0 : ℝ → ℝ) =ᵐ[uI] Q)
    (hq : Tendsto (fun n => ‖stepL2 (q n) - Q0‖) atTop (𝓝 0))
    (hz : Tendsto z atTop (𝓝 x)) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun n => ‖stepL2 (fun j => kk (c n) ε (z n - q n j)) -
      compL2 (hker_lip hε x).continuous.measurable (hker_bdd hε x) hQm‖) atTop (𝓝 0) := by
  set K : ℝ := 2 / ε ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity
  have hmeasQ := (hker_lip hε x).continuous.measurable
  set e : ℕ → ℝ := fun n => 2 * |z n - x| / ε ^ 3 + (c n) ^ 2 / ε ^ 4 with he
  have he0 : ∀ n, 0 ≤ e n := fun n => by positivity
  have hen : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => |z n - x|) atTop (𝓝 0) := by
      simpa using (hz.sub_const x).abs
    have h2 : Tendsto (fun n => (c n) ^ 2) atTop (𝓝 0) := by simpa using hc.pow 2
    have := ((h1.const_mul 2).div_const (ε ^ 3)).add (h2.div_const (ε ^ 4))
    simpa using this
  have hb := hq.const_mul K
  rw [mul_zero] at hb
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hen.add hb)
  have hN : 0 < n + 1 := Nat.succ_pos n
  have hstep : stepL2 (fun j => hker x ε (q n j)) =
      compL2 hmeasQ (hker_bdd hε x) (measurable_stepF (q n)) := stepL2_comp hN hmeasQ (hker_bdd hε x) _
  have h1 : ‖stepL2 (fun j => kk (c n) ε (z n - q n j)) - stepL2 (fun j => hker x ε (q n j))‖ ≤ e n := by
    rw [← stepL2_sub]
    refine norm_stepL2_le _ (he0 n) fun j => ?_
    have := kk_diff (c := c n) (c' := 0) (ε := ε) (s := z n - q n j) (s' := x - q n j) hε
    have e1 : |z n - q n j - (x - q n j)| = |z n - x| := by
      rw [show z n - q n j - (x - q n j) = z n - x by ring]
    rw [e1] at this
    simp only [Pi.sub_apply]
    unfold hker
    simpa [he] using this
  have h2 : ‖compL2 hmeasQ (hker_bdd hε x) (measurable_stepF (q n)) -
      compL2 hmeasQ (hker_bdd hε x) hQm‖ ≤ K * ‖stepL2 (q n) - Q0‖ :=
    norm_compL2_sub_le (hker_lip hε x) (hker_bdd hε x) (measurable_stepF (q n)) hQm (stepL2_ae (q n)) hQ0
  calc ‖stepL2 (fun j => kk (c n) ε (z n - q n j)) - compL2 hmeasQ (hker_bdd hε x) hQm‖
      = ‖(stepL2 (fun j => kk (c n) ε (z n - q n j)) - stepL2 (fun j => hker x ε (q n j))) +
          (compL2 hmeasQ (hker_bdd hε x) (measurable_stepF (q n)) -
            compL2 hmeasQ (hker_bdd hε x) hQm)‖ := by rw [hstep]; congr 1; abel
    _ ≤ ‖stepL2 (fun j => kk (c n) ε (z n - q n j)) - stepL2 (fun j => hker x ε (q n j))‖ +
          ‖compL2 hmeasQ (hker_bdd hε x) (measurable_stepF (q n)) -
            compL2 hmeasQ (hker_bdd hε x) hQm‖ := norm_add_le _ _
    _ ≤ e n + K * ‖stepL2 (q n) - Q0‖ := add_le_add h1 h2

end QuantumNLS.DetGapRow

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.DetGapRow.row_identity
#print axioms QuantumNLS.DetGapRow.kk_diff
#print axioms QuantumNLS.DetGapRow.kernel_L2_tendsto
