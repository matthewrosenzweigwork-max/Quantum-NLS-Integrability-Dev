import Mathlib
import QuantumNLS.F02FiniteGap
import QuantumNLS.EmpiricalRapidity
import QuantumNLS.BulkResponseActual

/-!
# CC:F02:tightness (R-E22E10B6): original-law boundedness of active adjacent gaps

Source: `source-text/chapters/root_response/F02.tex`, Theorem `CC:F02:tightness` (line 219) and its proof (lines 253-279).

Data (printed): `L, κ > 0`, `N ≥ 1`, `c_N = κ/N`, distinct integers `a ≠ b`, the occupation law `P` on `𝓜_N = MArr N` (for the actual Bethe product law this is
`bornMeasure (physBasis L hκ N) u hu`, `tightness_born`), the limiting indexed masses `I_n = I_n^{(κ)}(u)` with `I_a, I_b > 0`, `r = ½ min{I_a, I_b}`,
`e_N = E ‖m/N − I‖_{ℓ¹}` (`eN`, in `[0,∞]`), the event `A_N = {m_a/N ≥ r, m_b/N ≥ r}`, and for `m_a ≥ 1` the gap `G_N^{ab}(m) = Q_2(m) − Q_2(m − e_a + e_b)` with `Q_2(m) = Σ q_i²`
(`gap`, roots `arrRoots L (κ/N) m`); `K_{ab}(r) = (4π|a−b|/L)(max{|p_a|,|p_b|} + 2√(κ/L) + √(κ/(4Lr)))`.

Proved (`tightness`): (good-bound) `|G_N^{ab}(m)| ≤ K_ab(r)` for `m ∈ A_N`; (good-probability) `P(A_N^c) ≤ e_N/r`; (tail-probability) `P{m_a ≥ 1, |G| > K_ab} ≤ e_N/r`.
`tightness_tendsto`: if `e_N → 0` these probabilities tend to `0`.

Scope (recorded): the identity of `I` with `I^{(κ)}(u)` (DEF-014 / R-950BFB30) and the convergence `e_N → 0` ("the full occupation theorem", R-E6DFC650) are not used in the inequalities:
`I` is an arbitrary real sequence and `e_N → 0` is the explicit hypothesis of `tightness_tendsto`; the inequalities hold for every probability law `P` on `MArr N`.

Route as printed: `CC:F02:finite-gap` (`F02FiniteGap.gap_integral`, `forced_bound`) for the active-block bounds with the donor count `η_b = m_b + 1`, receiver count `m_a` (case `a > b`, `η = m − e_a + e_b`)
or donor `m_a`, receiver `m_b + 1` (case `a < b`, forward transfer), then Markov's inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal

noncomputable section

namespace QuantumNLS.F02Tightness

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.GaudinResponse
open QuantumNLS.F02FiniteGap

/-- `Q_2(m) = Σ_i q_i²` at coupling `c`. -/
def Q2 {N : ℕ} (L c : ℝ) (m : MArr N) : ℝ := ∑ i, arrRoots L c m i ^ 2

/-- `G_N^{ab}(m) = Q_2(m) − Q_2(m − e_a + e_b)` (set to `0` when `m_a = 0`). -/
def gap {N : ℕ} (L κ : ℝ) (a b : ℤ) (m : MArr N) : ℝ :=
  if h : 1 ≤ m.1 a then Q2 L (κ / N) m - Q2 L (κ / N) (transfer m h b) else 0

/-- The constant `B = max{|p_a|,|p_b|} + 2√(κ/L) + √(κ/(4Lr))`; `K_{ab}(r) = 4π|a−b|/L · B`. -/
def Bconst (L κ r : ℝ) (a b : ℤ) : ℝ :=
  max |2 * Real.pi * a / L| |2 * Real.pi * b / L| + 2 * Real.sqrt (κ / L) + Real.sqrt (κ / (4 * L * r))

def Kab (L κ r : ℝ) (a b : ℤ) : ℝ :=
  4 * Real.pi * |((a : ℝ) - b)| / L * Bconst L κ r a b

/-- `‖m/N − I‖_{ℓ¹}`, in `[0,∞]`. -/
def ellOne {N : ℕ} (I : ℤ → ℝ) (m : MArr N) : ℝ≥0∞ :=
  ∑' n : ℤ, ENNReal.ofReal |((m.1 n : ℕ) : ℝ) / N - I n|

/-- `e_N = E ‖m/N − I‖_{ℓ¹}` under the law `P`. -/
def eN {N : ℕ} (P : Measure (MArr N)) (I : ℤ → ℝ) : ℝ≥0∞ := ∫⁻ m, ellOne I m ∂P

/-- `A_N = {m_a/N ≥ r, m_b/N ≥ r}`. -/
def AN (N : ℕ) (a b : ℤ) (r : ℝ) : Set (MArr N) :=
  {m | r ≤ ((m.1 a : ℕ) : ℝ) / N ∧ r ≤ ((m.1 b : ℕ) : ℝ) / N}

/-! ## 1. The deterministic bound -/

theorem atRank_eq {N : ℕ} (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {k : ℤ} (hk : b ≤ k) :
    ∃ i : Fin N, (i.val : ℤ) + 1 = Ccum η k ∧ ∀ v : Fin N → ℝ, atRank η k v = v i := by
  have h1 := Ccum_jump η hk
  have h2 := Ccum_le_N η k
  have hpos : 1 ≤ Ccum η k := by omega
  refine ⟨⟨Ccum η k - 1, by omega⟩, by simp only [Fin.val_mk]; omega, fun v => ?_⟩
  unfold atRank
  rw [Finset.sum_eq_single (⟨Ccum η k - 1, by omega⟩ : Fin N)]
  · rw [if_pos (by simp only [Fin.val_mk]; omega)]
  · intro j _ hj
    have : ¬ ((j.val : ℤ) + 1 = Ccum η k) := by
      intro h
      apply hj
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    simp [this]
  · simp

theorem sqrt_term_le {L κ r m : ℝ} {N : ℕ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) (hr : 0 < r)
    (hm : r * N ≤ m) :
    Real.sqrt (κ / N * N * ((N : ℝ) - 1) / (4 * L * m)) ≤ Real.sqrt (κ / (4 * L * r)) := by
  apply Real.sqrt_le_sqrt
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hm0 : 0 < m := lt_of_lt_of_le (by positivity) hm
  have hcN : κ / N * N = κ := by field_simp
  rw [hcN, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : ((N : ℝ) - 1) * r ≤ m := by nlinarith
  nlinarith [mul_pos hκ hL]

theorem D_term_le {L κ : ℝ} {N : ℕ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) :
    2 * Real.sqrt (κ / N * ((N : ℝ) - 1) / L) ≤ 2 * Real.sqrt (κ / L) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have : κ / N * ((N : ℝ) - 1) / L ≤ κ / L := by
    rw [div_le_div_iff_of_pos_right hL]
    rw [div_mul_eq_mul_div, div_le_iff₀ hN']
    nlinarith
  linarith [Real.sqrt_le_sqrt this]

theorem Bconst_comm (L κ r : ℝ) (a b : ℤ) : Bconst L κ r a b = Bconst L κ r b a := by
  unfold Bconst; rw [max_comm]

theorem Bconst_nonneg {L κ r : ℝ} (a b : ℤ) : 0 ≤ Bconst L κ r a b := by
  unfold Bconst
  have := le_max_left |2 * Real.pi * (a : ℝ) / L| |2 * Real.pi * (b : ℝ) / L|
  have := abs_nonneg (2 * Real.pi * (a : ℝ) / L)
  have := Real.sqrt_nonneg (κ / L)
  have := Real.sqrt_nonneg (κ / (4 * L * r))
  linarith

/-- Active-block bound: `|Q_2(η_{b→a}) − Q_2(η)| ≤ 4π(a−b)/L · B` when both block counts are `≥ rN`. -/
theorem abs_gap_le {N : ℕ} {L κ r : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) (hr : 0 < r)
    (η : MArr N) {b a : ℤ} (hb : 1 ≤ η.1 b) (hab : b < a)
    (hrb : r * N ≤ η.1 b) (hra : r * N ≤ (η.1 a : ℝ) + 1) :
    |Q2 L (κ / N) (transfer η hb a) - Q2 L (κ / N) η| ≤
      4 * Real.pi * ((a : ℝ) - b) / L * Bconst L κ r a b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < κ / (N : ℝ) := by positivity
  have hgap := gap_integral hL hc η hb hab
  have hQ : Q2 L (κ / N) (transfer η hb a) - Q2 L (κ / N) η =
      ∑ i, arrRoots L (κ / N) (transfer η hb a) i ^ 2 - ∑ i, arrRoots L (κ / N) η i ^ 2 := rfl
  rw [hQ, hgap]
  have hBpos := Bconst_nonneg (L := L) (κ := κ) (r := r) a b
  have hBdef : Bconst L κ r a b = max |2 * Real.pi * (a : ℝ) / L| |2 * Real.pi * (b : ℝ) / L| +
      2 * Real.sqrt (κ / L) + Real.sqrt (κ / (4 * L * r)) := rfl
  have hpt : ∀ k ∈ Finset.Ico b a, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |atRank η k (responseVec L (κ / N) (qPath L (κ / N) η hb a s))| ≤ Bconst L κ r a b / L := by
    intro k hk s hs
    obtain ⟨i, hi, hv⟩ := atRank_eq η hb (Finset.mem_Ico.1 hk).1
    rw [hv]
    obtain ⟨hlow, hup⟩ := forced_bound hL hc η hb hab hs.1 hs.2 hk hi
    have hD := D_term_le hL hκ hN
    have hSb := sqrt_term_le (L := L) (κ := κ) hL hκ hN hr hrb
    have hSa := sqrt_term_le (L := L) (κ := κ) hL hκ hN hr hra
    have hMa : 2 * Real.pi * (a : ℝ) / L ≤ max |2 * Real.pi * (a : ℝ) / L| |2 * Real.pi * (b : ℝ) / L| :=
      (le_abs_self _).trans (le_max_left _ _)
    have hMb : -(max |2 * Real.pi * (a : ℝ) / L| |2 * Real.pi * (b : ℝ) / L|) ≤
        2 * Real.pi * (b : ℝ) / L :=
      (neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)
    rw [abs_le]
    constructor
    · have hnum : -(Bconst L κ r a b) ≤ 2 * Real.pi * b / L -
          2 * Real.sqrt (κ / N * ((N : ℝ) - 1) / L) -
          Real.sqrt (κ / N * N * ((N : ℝ) - 1) / (4 * L * (η.1 b : ℝ))) := by
        rw [hBdef]; linarith
      have := div_le_div_of_nonneg_right hnum hL.le
      rw [neg_div] at this
      exact this.trans hlow
    · have hnum : 2 * Real.pi * a / L + 2 * Real.sqrt (κ / N * ((N : ℝ) - 1) / L) +
          Real.sqrt (κ / N * N * ((N : ℝ) - 1) / (4 * L * ((η.1 a : ℝ) + 1))) ≤ Bconst L κ r a b := by
        rw [hBdef]; linarith
      exact hup.trans (div_le_div_of_nonneg_right hnum hL.le)
  have hint : ∀ k ∈ Finset.Ico b a, |∫ s in (0 : ℝ)..1,
      atRank η k (responseVec L (κ / N) (qPath L (κ / N) η hb a s))| ≤ Bconst L κ r a b / L := by
    intro k hk
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := Bconst L κ r a b / L)
      (f := fun s => atRank η k (responseVec L (κ / N) (qPath L (κ / N) η hb a s)))
      (fun s hs => by
        rw [Set.uIoc_of_le zero_le_one] at hs
        rw [Real.norm_eq_abs]
        exact hpt k hk s ⟨hs.1.le, hs.2⟩)
    simpa using this
  have hcard : ((Finset.Ico b a).card : ℝ) = (a : ℝ) - b := by
    rw [Int.card_Ico]
    rw [show (((a - b).toNat : ℕ) : ℝ) = (((a - b : ℤ)) : ℝ) from by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ a - b)]
    push_cast; ring
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi)]
  calc 4 * Real.pi * |∑ k ∈ Finset.Ico b a, ∫ s in (0 : ℝ)..1,
        atRank η k (responseVec L (κ / N) (qPath L (κ / N) η hb a s))|
      ≤ 4 * Real.pi * ∑ k ∈ Finset.Ico b a, |∫ s in (0 : ℝ)..1,
        atRank η k (responseVec L (κ / N) (qPath L (κ / N) η hb a s))| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 4 * Real.pi * ((Finset.Ico b a).card • (Bconst L κ r a b / L)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_card_nsmul _ _ _ hint) (by positivity)
    _ = 4 * Real.pi * ((a : ℝ) - b) / L * Bconst L κ r a b := by
        rw [nsmul_eq_mul, hcard]; ring

theorem tcount_recv {N : ℕ} (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (hab : a ≠ b) :
    (((transfer η hb a).1 a : ℕ) : ℝ) = (η.1 a : ℝ) + 1 := by
  have := transfer_apply η hb a a
  simp only [hab, ↓reduceIte] at this
  have h : (((transfer η hb a).1 a : ℕ) : ℤ) = (η.1 a : ℤ) + 1 := by omega
  exact_mod_cast h

theorem tcount_donor {N : ℕ} (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (hab : a ≠ b) :
    (η.1 b : ℝ) = (((transfer η hb a).1 b : ℕ) : ℝ) + 1 := by
  have := transfer_apply η hb a b
  simp only [Ne.symm hab, ↓reduceIte] at this
  have h : (η.1 b : ℤ) = (((transfer η hb a).1 b : ℕ) : ℤ) + 1 := by omega
  exact_mod_cast h

/-- **Good bound** (`CC:F02:good-bound`): `|G_N^{ab}(m)| ≤ K_{ab}(r)` on `A_N`. -/
theorem good_bound {N : ℕ} {L κ r : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) (hr : 0 < r)
    {a b : ℤ} (hab : a ≠ b) {m : MArr N} (hm : m ∈ AN N a b r) :
    |gap L κ a b m| ≤ Kab L κ r a b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hma, hmb⟩ := hm
  have hma' : r * N ≤ (m.1 a : ℝ) := by rwa [le_div_iff₀ hN'] at hma
  have hmb' : r * N ≤ (m.1 b : ℝ) := by rwa [le_div_iff₀ hN'] at hmb
  have hpos : (0 : ℝ) < m.1 a := lt_of_lt_of_le (by positivity) hma'
  have ha1 : 1 ≤ m.1 a := by exact_mod_cast hpos
  unfold gap
  rw [dif_pos ha1]
  unfold Kab
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b: forward transfer from m, donor a, receiver b
    have h := abs_gap_le hL hκ hN hr m ha1 hlt (by simpa using hma') (by linarith)
    rw [abs_sub_comm, Bconst_comm L κ r a b]
    rw [abs_of_neg (by linarith [(Int.cast_lt (R := ℝ)).2 hlt] : (a : ℝ) - b < 0)]
    convert h using 2
    ring
  · -- b < a: η = m − e_a + e_b, donor b (count m_b + 1), receiver a (count m_a)
    have hne : b ≠ a := Ne.symm hab
    have hηb : 1 ≤ (transfer m ha1 b).1 b := transfer_receiver m ha1 hne
    have e1 := tcount_recv m ha1 b hne
    have e2 := tcount_donor m ha1 b hne
    have h := abs_gap_le hL hκ hN hr (transfer m ha1 b) hηb hgt (by linarith) (by linarith)
    rw [transfer_transfer m ha1 hne] at h
    rw [abs_of_pos (by linarith [(Int.cast_lt (R := ℝ)).2 hgt] : (0 : ℝ) < (a : ℝ) - b)]
    exact h

/-! ## 2. The probability bounds -/

theorem compl_subset {N : ℕ} {r : ℝ} (hr : 0 < r) {I : ℤ → ℝ} {a b : ℤ} (hIa : 2 * r ≤ I a)
    (hIb : 2 * r ≤ I b) :
    (AN N a b r)ᶜ ⊆ {m : MArr N | ENNReal.ofReal r ≤ ellOne I m} := by
  intro m hm
  simp only [AN, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_le] at hm
  have key : ∀ c : ℤ, 2 * r ≤ I c → ((m.1 c : ℕ) : ℝ) / N < r →
      ENNReal.ofReal r ≤ ellOne I m := by
    intro c hc hlt
    unfold ellOne
    have h1 : ENNReal.ofReal r ≤ ENNReal.ofReal |((m.1 c : ℕ) : ℝ) / N - I c| :=
      ENNReal.ofReal_le_ofReal (by rw [le_abs]; right; linarith)
    exact h1.trans (ENNReal.le_tsum (f := fun n : ℤ => ENNReal.ofReal |((m.1 n : ℕ) : ℝ) / N - I n|) c)
  rcases hm with h | h
  · exact key a hIa h
  · exact key b hIb h

theorem prob_compl_le {N : ℕ} (P : Measure (MArr N)) {r : ℝ} (hr : 0 < r) {I : ℤ → ℝ} {a b : ℤ}
    (hIa : 2 * r ≤ I a) (hIb : 2 * r ≤ I b) :
    P (AN N a b r)ᶜ ≤ eN P I / ENNReal.ofReal r := by
  calc P (AN N a b r)ᶜ ≤ P {m : MArr N | ENNReal.ofReal r ≤ ellOne I m} :=
        measure_mono (compl_subset hr hIa hIb)
    _ ≤ (∫⁻ m, ellOne I m ∂P) / ENNReal.ofReal r :=
        meas_ge_le_lintegral_div Measurable.of_discrete.aemeasurable
          (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top

/-- **`CC:F02:tightness`** (R-E22E10B6): the good bound, the good probability bound and the tail-probability bound.
`r = ½ min{I_a, I_b}`, `I_a, I_b > 0`; `e_N` is the printed `E ‖m/N − I‖_{ℓ¹}` under the law `P`. -/
theorem tightness {N : ℕ} {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hN : 0 < N) {a b : ℤ} (hab : a ≠ b)
    {I : ℤ → ℝ} (hIa : 0 < I a) (hIb : 0 < I b) (P : Measure (MArr N)) :
    (∀ m ∈ AN N a b (min (I a) (I b) / 2), |gap L κ a b m| ≤ Kab L κ (min (I a) (I b) / 2) a b) ∧
    P (AN N a b (min (I a) (I b) / 2))ᶜ ≤ eN P I / ENNReal.ofReal (min (I a) (I b) / 2) ∧
    P {m : MArr N | 1 ≤ m.1 a ∧ Kab L κ (min (I a) (I b) / 2) a b < |gap L κ a b m|} ≤
      eN P I / ENNReal.ofReal (min (I a) (I b) / 2) := by
  have hr : 0 < min (I a) (I b) / 2 := by positivity
  have h2a : 2 * (min (I a) (I b) / 2) ≤ I a := by linarith [min_le_left (I a) (I b)]
  have h2b : 2 * (min (I a) (I b) / 2) ≤ I b := by linarith [min_le_right (I a) (I b)]
  have hgood : ∀ m ∈ AN N a b (min (I a) (I b) / 2),
      |gap L κ a b m| ≤ Kab L κ (min (I a) (I b) / 2) a b := fun m hm =>
    good_bound hL hκ hN hr hab hm
  refine ⟨hgood, prob_compl_le P hr h2a h2b, ?_⟩
  refine le_trans (measure_mono ?_) (prob_compl_le P hr h2a h2b)
  intro m hm
  simp only [Set.mem_setOf_eq] at hm
  intro hmA
  exact absurd (hgood m hmA) (not_le.2 hm.2)

/-- If `e_N → 0` (the full occupation theorem), both probabilities tend to `0`. -/
theorem tightness_tendsto {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {a b : ℤ} (hab : a ≠ b)
    {I : ℤ → ℝ} (hIa : 0 < I a) (hIb : 0 < I b) (P : ∀ N : ℕ, Measure (MArr N))
    (he : Tendsto (fun N : ℕ => eN (P N) I) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => P N (AN N a b (min (I a) (I b) / 2))ᶜ) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => P N {m : MArr N | 1 ≤ m.1 a ∧
      Kab L κ (min (I a) (I b) / 2) a b < |gap L κ a b m|}) atTop (𝓝 0) := by
  have hr : 0 < min (I a) (I b) / 2 := by positivity
  have hlim : Tendsto (fun N : ℕ => eN (P N) I / ENNReal.ofReal (min (I a) (I b) / 2)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const he (Or.inr (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hr).ne'))
    rw [zero_mul] at this
    exact this.congr fun N => (div_eq_mul_inv _ _).symm
  have hev : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N => bot_le) ?_
    filter_upwards [hev] with N hN
    exact (tightness hL hκ hN hab hIa hIb (P N)).2.1
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun N => bot_le) ?_
    filter_upwards [hev] with N hN
    exact (tightness hL hκ hN hab hIa hIb (P N)).2.2

/-- The statement for the actual Bethe product law `P_{N,u}` (the Born law of the physical basis). -/
theorem tightness_born {L : ℝ} [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (u : QuantumNLS.PhysicalTensor.L2T L) (hu : ‖u‖ = 1) {a b : ℤ} (hab : a ≠ b)
    {I : ℤ → ℝ} (hIa : 0 < I a) (hIb : 0 < I b) :
    (∀ m ∈ AN N a b (min (I a) (I b) / 2), |gap L κ a b m| ≤ Kab L κ (min (I a) (I b) / 2) a b) ∧
    QuantumNLS.EmpiricalRapidity.bornMeasure (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu
        (AN N a b (min (I a) (I b) / 2))ᶜ ≤
      eN (QuantumNLS.EmpiricalRapidity.bornMeasure (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu) I /
        ENNReal.ofReal (min (I a) (I b) / 2) :=
  by
  have := tightness (Fact.out : 0 < L) hκ hN hab hIa hIb
    (QuantumNLS.EmpiricalRapidity.bornMeasure (QuantumNLS.BulkResponseActual.physBasis L hκ N) u hu)
  exact ⟨this.1, this.2.1⟩

end QuantumNLS.F02Tightness

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.F02Tightness.atRank_eq
#print axioms QuantumNLS.F02Tightness.abs_gap_le
#print axioms QuantumNLS.F02Tightness.good_bound
#print axioms QuantumNLS.F02Tightness.tightness
#print axioms QuantumNLS.F02Tightness.tightness_tendsto
#print axioms QuantumNLS.F02Tightness.tightness_born
