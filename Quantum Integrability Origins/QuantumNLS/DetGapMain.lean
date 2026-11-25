import Mathlib
import QuantumNLS.DetGapRow
import QuantumNLS.DetGapRowLim
import QuantumNLS.DetGapGroup
import QuantumNLS.DetGapW2
import QuantumNLS.F04SelBand
import QuantumNLS.StrongLimitBulk

/-!
# CC:F04:deterministic-gap (R-C455C541), step 5: the transfer limit `ω_ab = 4π ∫_b^a f_ext(x(λ)) dλ`

Source: `F04.tex` line 315, Proposition `CC:F04:deterministic-gap` and its proof.  Assembly of
`DetGapGroup` (CC:F04:label-integral), `DetGapW2` (quantile convergence from `W₂`), `StrongLimitBulk.strong_limit_bulk`
(`CC:F03:deterministic`), `DetGapRowLim.row_limit` (CC:F04:row-limit) and `F02FiniteGap.forced_bound` (CC:F04:row-domination),
with dominated convergence.  The selection clause `CC:F04:selection` (R-F4C3E5BE) is carried as an explicit hypothesis `hsel`
with exactly the statement of `F04Selection.selection` (sonnet_fourier's assembly of `F04SelConv.selection_conv` and
`F04SelSeparation.selection_separation`); it is bound to that theorem in `DetGapFinal`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Matrix

namespace QuantumNLS.DetGapMain

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
open QuantumNLS.LocalHeight QuantumNLS.DetGapGroup QuantumNLS.DetGapRowLim QuantumNLS.DetGapW2
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData BulkMeasure)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.QuantileTransport (qm empirical W2)
open QuantumNLS.StepIntegrals (stepL2)
open QuantumNLS.StrongLimitBulk (Q2 strong_limit_bulk)
open PhysicalTensor (L2T)

/-! ## 1. Algebra: `Bop = B` and the uniform row bound -/

theorem bop_eq_gaudin {N : ℕ} (L c : ℝ) (q v : Fin N → ℝ) :
    QuantumNLS.FiniteResponse.Bop L c q v = gaudinMatrix L c q *ᵥ v := by
  funext i
  rw [QuantumNLS.FiniteResponse.Bop_eq_erase, gaudinMatrix_mulVec]
  congr 1
  all_goals (try (refine Finset.sum_congr rfl fun j _ => ?_))
  all_goals (try (simp only [QuantumNLS.FiniteResponse.wt, div_eq_mul_inv]))

theorem E_bound {L κ r N c m : ℝ} (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hN : 0 < N)
    (hcN : c * N = κ) (hm : r * N ≤ m) :
    Real.sqrt (c * N * (N - 1) / (4 * L * m)) ≤ Real.sqrt (κ / (4 * L * r)) := by
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity) hm
  apply Real.sqrt_le_sqrt
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : c * N * (N - 1) * (4 * L * r) = κ * (4 * L) * (r * (N - 1)) := by
    rw [hcN]; ring
  rw [h1]
  have h2 : r * (N - 1) ≤ m := by nlinarith
  calc κ * (4 * L) * (r * (N - 1)) ≤ κ * (4 * L) * m :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

/-- The printed uniform bound `CC:F04:row-domination`. -/
def Cb (L κ r : ℝ) (a b : ℤ) : ℝ :=
  (|2 * Real.pi * (b : ℝ) / L| + |2 * Real.pi * (a : ℝ) / L| + 2 * Real.sqrt (κ / L) +
    Real.sqrt (κ / (4 * L * r))) / L

theorem row_bound {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {n : ℕ} (η : MArr (n + 1)) {b : ℤ}
    (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {r : ℝ} (hr : 0 < r)
    (hrb : r * ((n : ℝ) + 1) ≤ (η.1 b : ℝ)) (hra : r * ((n : ℝ) + 1) ≤ (η.1 a : ℝ))
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) {k : ℤ} (hk : k ∈ Finset.Ico b a) {i : Fin (n + 1)}
    (hi : (i.val : ℤ) + 1 = Ccum η k) :
    |responseVec L (κ / ((n : ℝ) + 1)) (qPath L (κ / ((n : ℝ) + 1)) η hb a s) i| ≤
      Cb L κ r a b := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hc : 0 < κ / ((n : ℝ) + 1) := by positivity
  obtain ⟨hlo, hup⟩ := forced_bound hL hc η hb hab h0 h1 hk hi
  have hNc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hNc] at hlo hup
  have hcN : κ / ((n : ℝ) + 1) * ((n : ℝ) + 1) = κ := div_mul_cancel₀ _ hN.ne'
  set c := κ / ((n : ℝ) + 1) with hcdef
  have hD : Real.sqrt (c * (((n : ℝ) + 1) - 1) / L) ≤ Real.sqrt (κ / L) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith
  have hE1 := E_bound hL hκ hr hN hcN hrb
  have hE2 := E_bound hL hκ hr hN hcN (m := (η.1 a : ℝ) + 1) (by linarith)
  set P := Real.sqrt (κ / L)
  set T := Real.sqrt (κ / (4 * L * r))
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hb0 := abs_nonneg (2 * Real.pi * (b : ℝ) / L)
  have ha0 := abs_nonneg (2 * Real.pi * (a : ℝ) / L)
  have hbb := le_abs_self (2 * Real.pi * (b : ℝ) / L)
  have hbb' := neg_abs_le (2 * Real.pi * (b : ℝ) / L)
  have haa := le_abs_self (2 * Real.pi * (a : ℝ) / L)
  rw [abs_le]
  unfold Cb
  constructor
  · have : -((|2 * Real.pi * (b : ℝ) / L| + |2 * Real.pi * (a : ℝ) / L| + 2 * P + T) / L) ≤
        (2 * Real.pi * (b : ℝ) / L - 2 * Real.sqrt (c * (((n : ℝ) + 1) - 1) / L) -
          Real.sqrt (c * ((n : ℝ) + 1) * (((n : ℝ) + 1) - 1) / (4 * L * (η.1 b : ℝ)))) / L := by
      rw [← neg_div]
      apply div_le_div_of_nonneg_right _ hL.le
      linarith
    exact this.trans hlo
  · refine hup.trans ?_
    apply div_le_div_of_nonneg_right _ hL.le
    linarith

/-! ## 2. The occupations converge coordinatewise -/

theorem occ_tendsto {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (η : (n : ℕ) → MArr (n + 1))
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0)) (m : ℤ) :
    Tendsto (fun n : ℕ => (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 (II hκ u m)) := by
  have hI : Summable (fun m => II hκ u m) :=
    (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.1
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hη
  have hs1 : Summable (fun m : ℤ => (((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1)) := by
    apply summable_of_ne_finset_zero (s := (η n).1.support)
    intro m hm
    rw [Finsupp.notMem_support_iff.1 hm]
    simp
  have hab : Summable (fun m : ℤ => |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|) :=
    (hs1.sub hI).abs
  rw [Real.norm_eq_abs]
  exact hab.le_tsum m (fun j _ => abs_nonneg _)

/-! ## 3. The transfer limit -/

/-- **`CC:F04:deterministic-gap`** (R-C455C541), the selection clause `CC:F04:selection` being the hypothesis `hsel`. -/
theorem deterministic_gap_of_selection {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) (hbulk : BulkMeasure (Mu hκ u))
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hW2 : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (κ / ((n : ℝ) + 1)) (η n)))
      (Mu hκ u)) atTop (𝓝 0))
    (hsel : ∀ {k : ℤ} (hbk : b ≤ k) (hka : k < a) {lam : ℝ} (h1 : (k : ℝ) < lam)
      (h2 : lam < (k : ℝ) + 1),
      (∃ x, th hκ u x = lam * Real.pi) ∧
      (∀ x, th hκ u x = lam * Real.pi →
        Tendsto (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
          (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x)) ∧
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ n : ℕ in atTop, ∀ j : Fin (n + 1), j ≠ rk (η n) (hηb n) hbk →
        c₀ ≤ |qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
            (sParam (η n) (hηb n) (a := a) hbk lam) j -
          qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
            (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)|)
    {F : L2Unit} (hF : (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).IsResponse F)
    {f : ℝ → ℝ} (hfm : Measurable f) (hFf : (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm (Mu hκ u) t))
    (xl : ℝ → ℝ)
    (hxl : ∀ k : ℤ, b ≤ k → k < a → ∀ lam : ℝ, (k : ℝ) < lam → lam < (k : ℝ) + 1 →
      th hκ u (xl lam) = lam * Real.pi) :
    IntervalIntegrable (fun lam => fext L κ (Mu hκ u) f (xl lam)) volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
        ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (η n) i ^ 2) atTop
      (𝓝 (4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) := by
  haveI hprob := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hu0 : u ≠ 0 := ne_zero_of_II_pos hκ hb
  set D : BulkResponseData := ⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ with hD
  have hc : ∀ n : ℕ, 0 < κ / ((n : ℝ) + 1) := fun n => by positivity
  have hba : (b : ℝ) ≤ a := by exact_mod_cast hab.le
  -- the finite identity
  have hid : ∀ n : ℕ, ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
      ∑ i, arrRoots L (κ / ((n : ℝ) + 1)) (η n) i ^ 2 =
      4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam :=
    fun n => label_integral hL (hc n) (η n) (hηb n) hab
  -- uniform occupation lower bounds
  set r : ℝ := min (II hκ u a) (II hκ u b) / 2 with hrdef
  have hr : 0 < r := by
    have := lt_min ha hb
    simp only [hrdef]; positivity
  have hrlt_b : r < II hκ u b := by
    have := min_le_right (II hκ u a) (II hκ u b)
    simp only [hrdef]; linarith [lt_min ha hb]
  have hrlt_a : r < II hκ u a := by
    have := min_le_left (II hκ u a) (II hκ u b)
    simp only [hrdef]; linarith [lt_min ha hb]
  have hocc : ∀ m : ℤ, r < II hκ u m → ∀ᶠ n : ℕ in atTop, r * ((n : ℝ) + 1) ≤ (((η n).1 m : ℕ) : ℝ) := by
    intro m hm
    have := (occ_tendsto hκ u η hη m).eventually (lt_mem_nhds hm)
    filter_upwards [this] with n hn
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [lt_div_iff₀ hN] at hn
    exact hn.le
  have hunif : ∀ᶠ n : ℕ in atTop, ∀ lam : ℝ, lam ∈ Ioc (b : ℝ) a → lam ∉ range (Int.cast : ℤ → ℝ) →
      |Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam| ≤ Cb L κ r a b := by
    filter_upwards [hocc b hrlt_b, hocc a hrlt_a] with n hnb hna lam hlam hnon
    have hk0 : b ≤ ⌊lam⌋ := Int.le_floor.2 hlam.1.le
    have hlt : lam < a := by
      refine lt_of_le_of_ne hlam.2 fun h => hnon ⟨a, h.symm⟩
    have hk1 : ⌊lam⌋ < a := Int.floor_lt.2 hlt
    have hkl : (⌊lam⌋ : ℝ) < lam := by
      refine lt_of_le_of_ne (Int.floor_le lam) fun h => hnon ⟨⌊lam⌋, h⟩
    have hku : lam < (⌊lam⌋ : ℝ) + 1 := Int.lt_floor_add_one lam
    have hk : ⌊lam⌋ ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hk0, hk1⟩
    rw [Phi_eq_rank (η n) (hηb n) hab hk hkl hku]
    have hs := sParam_spec (η n) (hηb n) hab hk hkl hku
    exact row_bound hL hκ (η n) (hηb n) hab hr hnb hna hs.1.le hs.2.1.le hk (rk_val (η n) (hηb n) hk0)
  -- the pointwise limit
  have hlim : ∀ lam : ℝ, lam ∈ Ioc (b : ℝ) a → lam ∉ range (Int.cast : ℤ → ℝ) →
      Tendsto (fun n : ℕ => Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam) atTop
        (𝓝 (fext L κ (Mu hκ u) f (xl lam))) := by
    intro lam hlam hnon
    have hk0 : b ≤ ⌊lam⌋ := Int.le_floor.2 hlam.1.le
    have hlt : lam < a := lt_of_le_of_ne hlam.2 fun h => hnon ⟨a, h.symm⟩
    have hk1 : ⌊lam⌋ < a := Int.floor_lt.2 hlt
    have h1 : (⌊lam⌋ : ℝ) < lam := lt_of_le_of_ne (Int.floor_le lam) fun h => hnon ⟨⌊lam⌋, h⟩
    have h2 : lam < (⌊lam⌋ : ℝ) + 1 := Int.lt_floor_add_one lam
    set k := ⌊lam⌋ with hkdef
    have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hk0, hk1⟩
    obtain ⟨-, hconv, c₀, hc₀, hsep⟩ := hsel hk0 hk1 h1 h2
    have hx := hxl k hk0 hk1 lam h1 h2
    set x := xl lam with hxdef
    obtain ⟨j, ℓ, r', l, -, hjk, hkl, -, hrl, hnull, hrth, hlth, -, -⟩ :=
      band_data hκ u hu hb ha hk0 hk1
    obtain ⟨-, hxs⟩ := xlam_data hκ u hu hjk hkl hrth hlth hrl hu0 h1 h2
    have hxI : x ∈ Ioo r' l := (hxs x hx).1
    set ε := min c₀ (min (x - r') (l - x)) with hεdef
    have hε : 0 < ε := lt_min hc₀ (lt_min (by linarith [hxI.1]) (by linarith [hxI.2]))
    have hε1 : ε ≤ c₀ := min_le_left _ _
    have hε2 : ε ≤ x - r' := (min_le_right _ _).trans (min_le_left _ _)
    have hε3 : ε ≤ l - x := (min_le_right _ _).trans (min_le_right _ _)
    -- data
    set q : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
      (sParam (η n) (hηb n) (a := a) hk0 lam) with hqdef
    set Fv : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => responseVec L (κ / ((n : ℝ) + 1)) (q n) with hFvdef
    have hFv : ∀ n : ℕ, QuantumNLS.FiniteResponse.Bop D.L (D.κ / ((n + 1 : ℕ) : ℝ)) (q n) (Fv n) = q n := by
      intro n
      show QuantumNLS.FiniteResponse.Bop L (κ / ((n + 1 : ℕ) : ℝ)) (q n) (Fv n) = q n
      rw [Nat.cast_succ, bop_eq_gaudin]
      exact gaudin_responseVec hL (hc n) (q n)
    -- the step quantiles
    have hq0eq : ∀ n : ℕ, qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a 0 =
        arrRoots L (κ / ((n : ℝ) + 1)) (η n) := fun n => qPath_zero L _ (η n) (hηb n) a
    have hq0 : ∀ n : ℕ, Monotone (arrRoots L (κ / ((n : ℝ) + 1)) (η n)) := by
      intro n
      rw [← hq0eq n]
      exact (qPath_realBethe hL hκ (η n) (hηb n) a le_rfl zero_le_one).sorted.monotone
    have hs01 : ∀ n : ℕ, 0 < sParam (η n) (hηb n) (a := a) hk0 lam ∧
        sParam (η n) (hηb n) (a := a) hk0 lam < 1 := fun n =>
      ⟨(sParam_spec (η n) (hηb n) hab hk h1 h2).1, (sParam_spec (η n) (hηb n) hab hk h1 h2).2.1⟩
    have hC : ∀ n : ℕ, ∑ j, |q n j - arrRoots L (κ / ((n : ℝ) + 1)) (η n) j| ≤
        2 * Real.pi * ((a : ℝ) - b) / L := by
      intro n
      have hpl := path_l1 hL (hc n) (η n) (hηb n) hab (s := 0) le_rfl zero_le_one
      rw [sub_zero, mul_one] at hpl
      rw [← hpl]
      refine Finset.sum_le_sum fun j _ => ?_
      have hm := path_mono hL (hc n) (η n) (hηb n) hab (hs01 n).1.le (hs01 n).2.le j
      rw [← hq0eq n]
      simp only [hqdef]
      rw [abs_of_nonneg (by linarith [hm.1]), abs_of_nonpos (by linarith [hm.1, hm.2])]
      linarith [hm.1, hm.2]
    have hQc : Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0) :=
      quantile_conv_of_W2 D hq0 hW2 hC
    have hFc : Tendsto (fun n : ℕ => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) :=
      (strong_limit_bulk D hF (N := fun n => n + 1) (fun n => Nat.succ_pos n)
        (tendsto_add_atTop_nat 1) q Fv hFv hQc).1
    have hrow := row_limit D hfm hFf q Fv hFv hQc hFc (fun n => rk (η n) (hηb n) hk0) hε
      (hconv x hx)
      (by
        filter_upwards [hsep] with n hn j hj
        rw [abs_sub_comm]
        exact hε1.trans (hn j hj))
      (measure_mono_null (Ioo_subset_Ioo (by linarith) (by linarith)) hnull)
      (M := Cb L κ r a b)
      (by
        filter_upwards [hocc b hrlt_b, hocc a hrlt_a] with n hnb hna
        exact row_bound hL hκ (η n) (hηb n) hab hr hnb hna (hs01 n).1.le (hs01 n).2.le hk
          (rk_val (η n) (hηb n) hk0))
    refine hrow.congr fun n => ?_
    exact (Phi_eq_rank (η n) (hηb n) hab hk h1 h2).symm
  -- dominated convergence
  have hae : ∀ᵐ lam ∂(volume : Measure ℝ), lam ∉ range (Int.cast : ℤ → ℝ) :=
    (Set.countable_range (Int.cast : ℤ → ℝ)).ae_notMem volume
  have hae' : ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)), lam ∈ Ioc (b : ℝ) a ∧
      lam ∉ range (Int.cast : ℤ → ℝ) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with lam h1 h2
    exact ⟨h2, h1⟩
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a)
      (volume.restrict (Ioc (b : ℝ) a)) := fun n =>
    (measurable_Phi hL (hc n) (η n) (hηb n) a).aestronglyMeasurable
  have hbd : ∀ᶠ n : ℕ in atTop, ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)),
      ‖Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam‖ ≤ Cb L κ r a b := by
    filter_upwards [hunif] with n hn
    filter_upwards [hae'] with lam hl
    rw [Real.norm_eq_abs]
    exact hn lam hl.1 hl.2
  have hlimae : ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)),
      Tendsto (fun n : ℕ => Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam) atTop
        (𝓝 (fext L κ (Mu hκ u) f (xl lam))) := by
    filter_upwards [hae'] with lam hl
    exact hlim lam hl.1 hl.2
  have hDC := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioc (b : ℝ) a))
    (l := atTop) (fun _ => Cb L κ r a b) (Eventually.of_forall hmeas) hbd
    (integrable_const _) hlimae
  have hψm : AEStronglyMeasurable (fun lam => fext L κ (Mu hκ u) f (xl lam))
      (volume.restrict (Ioc (b : ℝ) a)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hlimae
  have hψb : ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)),
      ‖fext L κ (Mu hκ u) f (xl lam)‖ ≤ Cb L κ r a b := by
    filter_upwards [hae'] with lam hl
    have hev : ∀ᶠ n : ℕ in atTop,
        ‖Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam‖ ≤ Cb L κ r a b := by
      filter_upwards [hunif] with n hn
      rw [Real.norm_eq_abs]
      exact hn lam hl.1 hl.2
    exact le_of_tendsto (hlim lam hl.1 hl.2).norm hev
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hba]
    exact Integrable.mono' (integrable_const (Cb L κ r a b)) hψm hψb
  · have h2 : Tendsto (fun n : ℕ => ∫ lam in (b : ℝ)..(a : ℝ),
        Phi L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a lam) atTop
        (𝓝 (∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) := by
      simpa only [intervalIntegral.integral_of_le hba] using hDC
    refine (h2.const_mul (4 * Real.pi)).congr fun n => ?_
    exact (hid n).symm

end QuantumNLS.DetGapMain

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.DetGapMain.row_bound
#print axioms QuantumNLS.DetGapMain.occ_tendsto
#print axioms QuantumNLS.DetGapMain.deterministic_gap_of_selection
