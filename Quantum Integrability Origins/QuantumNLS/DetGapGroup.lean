import Mathlib
import QuantumNLS.F02FiniteGap
import QuantumNLS.F04SelSetup

/-!
# CC:F04:deterministic-gap (R-C455C541), step 3: grouping equal ranks into the `λ ∈ [b,a]` integral

Source: `F04.tex` line 315, proof of Proposition `CC:F04:deterministic-gap`: "Group equal ranks in this sum. For any distinct
forced rank, its set of thresholds is a consecutive integer interval `d, d+1, …, e−1`; its old and new labels are exactly
`d, e`, by the adjacent-label identity. Its contribution, including its multiplicity, is
`(e−d) ∫₀¹ f_{i,N}(s) ds = ∫_d^e f_{i,N}((λ−d)/(e−d)) dλ`. These intervals partition `[b,a]`. Therefore the exact identity becomes
`Q₂(m^{(N)}) − Q₂(η^{(N)}) = 4π ∫_b^a f_{i_N(λ),N}(s_N(λ)) dλ` (CC:F04:label-integral).  No absent intermediate label is discarded."

* `Phi L c η hb a λ = Σ_i 1_{(d_i, e_i]}(λ) f_{i,N}((λ−d_i)/(e_i−d_i))` with `d_i = labs η i`, `e_i = labs (transfer η hb a) i`
  (the integrand `f_{i_N(λ),N}(s_N(λ))`; the value at the integers is immaterial);
* `Phi_eq_rank`: for `k ∈ [b,a)`, `λ ∈ (k,k+1)`: `Phi λ = f_{rk,N}(s_N(λ))` (the printed `i_N`, `s_N`, from `F04SelSetup`);
* `label_integral`: `Σ q̃² − Σ q² = 4π ∫_b^a Phi` (uses `F02FiniteGap.gap_integral` exactly).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.DetGapGroup

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.F04SelSetup

variable {N : ℕ}

/-- `f_{i}(s) = [B(s)^{-1} q(s)]_i`. -/
def gP (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (i : Fin N) (s : ℝ) : ℝ :=
  responseVec L c (qPath L c η hb a s) i

/-- `f_{i}((λ−d_i)/(e_i−d_i))`. -/
def Gl (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (i : Fin N) (lam : ℝ) : ℝ :=
  gP L c η hb a i ((lam - (labs η i : ℝ)) / ((labs (transfer η hb a) i : ℝ) - labs η i))

/-- The integrand `λ ↦ f_{i_N(λ),N}(s_N(λ))`. -/
def Phi (L c : ℝ) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (lam : ℝ) : ℝ :=
  ∑ i, (Set.Ioc (labs η i : ℝ) (labs (transfer η hb a) i : ℝ)).indicator (Gl L c η hb a i) lam

theorem continuous_gP {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b)
    (a : ℤ) (i : Fin N) : Continuous (gP L c η hb a i) :=
  continuous_responseVec hL hc η hb a i

theorem continuous_Gl {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b)
    (a : ℤ) (i : Fin N) : Continuous (Gl L c η hb a i) :=
  (continuous_gP hL hc η hb a i).comp ((continuous_id.sub continuous_const).div_const _)

theorem measurable_Phi {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b)
    (a : ℤ) : Measurable (Phi L c η hb a) := by
  unfold Phi
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (continuous_Gl hL hc η hb a i).measurable.indicator measurableSet_Ioc

/-- Regrouping the thresholds by rank. -/
theorem sum_atRank_integral {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b)
    (a : ℤ) :
    ∑ k ∈ Finset.Ico b a, ∫ s in (0 : ℝ)..1, atRank η k (responseVec L c (qPath L c η hb a s)) =
      ∑ i, rankVec η b a i * ∫ s in (0 : ℝ)..1, gP L c η hb a i s := by
  have hint : ∀ i : Fin N, IntervalIntegrable (gP L c η hb a i) volume 0 1 := fun i =>
    (continuous_gP hL hc η hb a i).intervalIntegrable _ _
  have h1 : ∀ k : ℤ, ∫ s in (0 : ℝ)..1, atRank η k (responseVec L c (qPath L c η hb a s)) =
      ∑ i : Fin N, if (i.val : ℤ) + 1 = Ccum η k then ∫ s in (0 : ℝ)..1, gP L c η hb a i s else 0 := by
    intro k
    unfold atRank
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : (i.val : ℤ) + 1 = Ccum η k
      · simp [h, gP]
      · simp [h]
    · intro i _
      by_cases h : (i.val : ℤ) + 1 = Ccum η k
      · simp only [h, if_true]; exact hint i
      · simp [h]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold rankVec
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-- The substitution `λ = d + (e−d) s`. -/
theorem integral_Gl {L c : ℝ} (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) (i : Fin N)
    {d e : ℝ} (hd : d = (labs η i : ℝ)) (he : e = (labs (transfer η hb a) i : ℝ)) (hde : d < e) :
    ∫ lam in d..e, Gl L c η hb a i lam = (e - d) * ∫ s in (0 : ℝ)..1, gP L c η hb a i s := by
  have hm : e - d ≠ 0 := (sub_pos.2 hde).ne'
  have h1 : ∀ lam, Gl L c η hb a i lam = (fun y => gP L c η hb a i (y / (e - d))) (lam - d) := by
    intro lam; simp only [Gl, hd, he]
  simp_rw [h1]
  rw [intervalIntegral.integral_comp_sub_right (fun y => gP L c η hb a i (y / (e - d))) d,
    intervalIntegral.integral_comp_div (fun y => gP L c η hb a i y) hm]
  simp [hm]

theorem integral_Phi {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ}
    (hab : b < a) :
    ∫ lam in (b : ℝ)..(a : ℝ), Phi L c η hb a lam =
      ∑ i, rankVec η b a i * ∫ s in (0 : ℝ)..1, gP L c η hb a i s := by
  have hba : (b : ℝ) ≤ a := by exact_mod_cast hab.le
  have hI : ∀ i : Fin N, IntervalIntegrable
      ((Set.Ioc (labs η i : ℝ) (labs (transfer η hb a) i : ℝ)).indicator (Gl L c η hb a i)) volume
      (b : ℝ) a := by
    intro i
    have h := (continuous_Gl hL hc η hb a i).integrableOn_Icc (μ := volume) (a := (labs η i : ℝ)) (b := (labs (transfer η hb a) i : ℝ))
    have h2 : IntegrableOn (Gl L c η hb a i) (Set.Ioc (labs η i : ℝ) (labs (transfer η hb a) i : ℝ)) volume :=
      h.mono_set Set.Ioc_subset_Icc_self
    exact (h2.integrable_indicator measurableSet_Ioc).intervalIntegrable
  unfold Phi
  rw [intervalIntegral.integral_finset_sum (fun i _ => hI i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hrk := rankVec_eq η hb hab i
  have hle : (labs η i : ℝ) ≤ labs (transfer η hb a) i := by
    exact_mod_cast labs_le_transfer η hb hab i
  rcases hle.eq_or_lt with heq | hlt
  · have : rankVec η b a i = 0 := by rw [hrk, ← heq]; ring
    rw [this, zero_mul, ← heq]
    simp
  · -- some threshold has rank `i`
    have hpos : 0 < rankVec η b a i := by rw [hrk]; linarith
    have hex : ∃ k ∈ Finset.Ico b a, (i.val : ℤ) + 1 = Ccum η k := by
      by_contra hno
      push Not at hno
      have : rankVec η b a i = 0 := by
        unfold rankVec
        exact Finset.sum_eq_zero fun k hk => by simp [hno k hk]
      linarith
    obtain ⟨k, hk, hik⟩ := hex
    obtain ⟨h1, h2, h3, h4⟩ := rank_labels η hb hab hk i hik
    have hbd : (b : ℝ) ≤ labs η i := by exact_mod_cast h1
    have hea : (labs (transfer η hb a) i : ℝ) ≤ a := by exact_mod_cast h4
    rw [intervalIntegral.integral_of_le hba, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 (Set.Ioc_subset_Ioc hbd hea), ← intervalIntegral.integral_of_le hlt.le,
      integral_Gl η hb a i rfl rfl hlt, hrk]

theorem Phi_eq_rank {L c : ℝ} (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {k : ℤ}
    (hk : k ∈ Finset.Ico b a) {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    Phi L c η hb a lam =
      responseVec L c (qPath L c η hb a (sParam η hb (a := a) (Finset.mem_Ico.1 hk).1 lam))
        (rk η hb (Finset.mem_Ico.1 hk).1) := by
  obtain ⟨hbk, hka⟩ := Finset.mem_Ico.1 hk
  have hv := rk_val η hb hbk
  obtain ⟨r1, r2, r3, r4⟩ := rk_labels η hb hab hk
  unfold Phi
  rw [Finset.sum_eq_single (rk η hb hbk)]
  · have hmem : lam ∈ Set.Ioc (labs η (rk η hb hbk) : ℝ) (labs (transfer η hb a) (rk η hb hbk) : ℝ) := by
      constructor
      · have : (labs η (rk η hb hbk) : ℝ) ≤ k := by exact_mod_cast r2
        linarith
      · have : ((k : ℝ) + 1) ≤ labs (transfer η hb a) (rk η hb hbk) := by exact_mod_cast r3
        linarith
    rw [Set.indicator_of_mem hmem]
    rfl
  · intro i _ hne
    have hC := Ccum_transfer η hb a k
    rw [if_pos hbk, if_neg (by omega)] at hC
    rw [Set.indicator_of_notMem]
    intro hmem
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hij : (i.val : ℤ) < (rk η hb hbk).val := by exact_mod_cast hlt
      have : labs (transfer η hb a) i ≤ k := (labs_le_iff _ i k).2 (by omega)
      have : (labs (transfer η hb a) i : ℝ) ≤ k := by exact_mod_cast this
      linarith [hmem.2]
    · have hij : (rk η hb hbk).val < (i.val : ℤ) := by exact_mod_cast hgt
      have : k + 1 ≤ labs η i := by
        by_contra hcon
        have := (labs_le_iff η i k).1 (by omega)
        omega
      have : ((k : ℝ) + 1) ≤ labs η i := by exact_mod_cast this
      linarith [hmem.1]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`CC:F04:label-integral`.** -/
theorem label_integral {L c : ℝ} (hL : 0 < L) (hc : 0 < c) (η : MArr N) {b : ℤ} (hb : 1 ≤ η.1 b)
    {a : ℤ} (hab : b < a) :
    ∑ i, arrRoots L c (transfer η hb a) i ^ 2 - ∑ i, arrRoots L c η i ^ 2 =
      4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), Phi L c η hb a lam := by
  rw [gap_integral hL hc η hb hab, sum_atRank_integral hL hc η hb a, integral_Phi hL hc η hb hab]

end QuantumNLS.DetGapGroup

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.DetGapGroup.measurable_Phi
#print axioms QuantumNLS.DetGapGroup.integral_Phi
#print axioms QuantumNLS.DetGapGroup.Phi_eq_rank
#print axioms QuantumNLS.DetGapGroup.label_integral
