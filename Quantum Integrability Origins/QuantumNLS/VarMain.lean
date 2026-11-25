import Mathlib
import QuantumNLS.DetGapMain
import QuantumNLS.VarSelection
import QuantumNLS.VarStrong
import QuantumNLS.VarRowLim

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 8: the energy-gap limit at contact `c_N = κ_N/N`, `κ_N → κ`

Source: `F04.tex` line 412, Proposition `CC:F04:variable-coupling` and its proof (last paragraph): "Finally the exact real-label identity (CC:F04:label-integral) holds at every `c_N > 0`, and (CC:F04:row-domination) holds with `κ_+` in place of `κ`. Dominated convergence proves the asserted energy gap limit with the limiting coupling `κ`."

`variable_coupling_core` follows `DetGapMain.deterministic_gap_of_selection` (read-only) with: the exact identity `DetGapGroup.label_integral` at `c_N = κs N/(N+1)`; the row domination `row_boundV` (`κ_+`); selection/separation `VarSelection.selectionV`; strong bulk response `VarStrong.strong_response_V`; the row limit `VarRowLim.row_limitV`.  Here `κs N > 0` for all `N` (the statement in `VarFinal` removes this normalization).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Matrix

namespace QuantumNLS.VarMain

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
open QuantumNLS.LocalHeight QuantumNLS.DetGapGroup QuantumNLS.DetGapRowLim QuantumNLS.DetGapW2
open QuantumNLS.DetGapMain (Cb row_bound occ_tendsto)
open QuantumNLS.VarCoupling QuantumNLS.VarSelection QuantumNLS.VarStrong QuantumNLS.VarRowLim
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData BulkMeasure)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.QuantileTransport (qm empirical W2)
open QuantumNLS.StepIntegrals (stepL2)
open QuantumNLS.StrongLimitBulk (Q2)
open PhysicalTensor (L2T)

/-- `CC:F04:row-domination` with `κ_+` in place of `κ`. -/
theorem row_boundV {L κp : ℝ} {κs : ℕ → ℝ} (hL : 0 < L) (hpos : ∀ N, 0 < κs N) {n : ℕ}
    (hκp : κs n ≤ κp) (η : MArr (n + 1)) {b : ℤ}
    (hb : 1 ≤ η.1 b) {a : ℤ} (hab : b < a) {r : ℝ} (hr : 0 < r)
    (hrb : r * ((n : ℝ) + 1) ≤ (η.1 b : ℝ)) (hra : r * ((n : ℝ) + 1) ≤ (η.1 a : ℝ))
    {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) {k : ℤ} (hk : k ∈ Finset.Ico b a) {i : Fin (n + 1)}
    (hi : (i.val : ℤ) + 1 = Ccum η k) :
    |responseVec L (κs n / ((n : ℝ) + 1)) (qPath L (κs n / ((n : ℝ) + 1)) η hb a s) i| ≤
      Cb L κp r a b := by
  have h := row_bound hL (hpos n) η hb hab hr hrb hra h0 h1 hk hi
  refine h.trans ?_
  unfold Cb
  have hκ0 := hpos n
  apply div_le_div_of_nonneg_right _ hL.le
  have s1 : Real.sqrt (κs n / L) ≤ Real.sqrt (κp / L) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hκp hL.le)
  have s2 : Real.sqrt (κs n / (4 * L * r)) ≤ Real.sqrt (κp / (4 * L * r)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hκp (by positivity))
  linarith

theorem variable_coupling_core {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) {κs : ℕ → ℝ}
    (hκs : Tendsto κs atTop (𝓝 κ)) (hpos : ∀ N, 0 < κs N) {κp : ℝ}
    (hκp : ∀ᶠ N : ℕ in atTop, κs N ≤ κp) (u : L2T L)
    (hu : ‖u‖ = 1) (hbulk : BulkMeasure (Mu hκ u))
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κs n / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    (hQ0 : ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n ∧ s n ≤ 1) →
      Tendsto (fun n : ℕ => ‖stepL2 (qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a (s n)) -
        Q2 (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData)‖) atTop (𝓝 0))
    {F : L2Unit} (hF : (⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ : BulkResponseData).IsResponse F)
    {f : ℝ → ℝ} (hfm : Measurable f) (hFf : (F : ℝ → ℝ) =ᵐ[uI] fun t => f (qm (Mu hκ u) t))
    (xl : ℝ → ℝ)
    (hxl : ∀ k : ℤ, b ≤ k → k < a → ∀ lam : ℝ, (k : ℝ) < lam → lam < (k : ℝ) + 1 →
      th hκ u (xl lam) = lam * Real.pi) :
    IntervalIntegrable (fun lam => fext L κ (Mu hκ u) f (xl lam)) volume (b : ℝ) a ∧
    Tendsto (fun n : ℕ => ∑ i, arrRoots L (κs n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
        ∑ i, arrRoots L (κs n / ((n : ℝ) + 1)) (η n) i ^ 2) atTop
      (𝓝 (4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) := by
  haveI hprob := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hu0 : u ≠ 0 := ne_zero_of_II_pos hκ hb
  set D : BulkResponseData := ⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ with hD
  have hc : ∀ n : ℕ, 0 < κs n / ((n : ℝ) + 1) := fun n => div_pos (hpos n) (by positivity)
  have hba : (b : ℝ) ≤ a := by exact_mod_cast hab.le
  -- the exact identity at every `c_N > 0`
  have hid : ∀ n : ℕ, ∑ i, arrRoots L (κs n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) i ^ 2 -
      ∑ i, arrRoots L (κs n / ((n : ℝ) + 1)) (η n) i ^ 2 =
      4 * Real.pi * ∫ lam in (b : ℝ)..(a : ℝ),
        Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam :=
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
  have hocc : ∀ m : ℤ, r < II hκ u m → ∀ᶠ n : ℕ in atTop,
      r * ((n : ℝ) + 1) ≤ (((η n).1 m : ℕ) : ℝ) := by
    intro m hm
    have := (occ_tendsto hκ u η hη m).eventually (lt_mem_nhds hm)
    filter_upwards [this] with n hn
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [lt_div_iff₀ hN] at hn
    exact hn.le
  have hunif : ∀ᶠ n : ℕ in atTop, ∀ lam : ℝ, lam ∈ Ioc (b : ℝ) a →
      lam ∉ range (Int.cast : ℤ → ℝ) →
      |Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam| ≤ Cb L κp r a b := by
    filter_upwards [hocc b hrlt_b, hocc a hrlt_a, hκp] with n hnb hna hκn lam hlam hnon
    have hk0 : b ≤ ⌊lam⌋ := Int.le_floor.2 hlam.1.le
    have hlt : lam < a := lt_of_le_of_ne hlam.2 fun h => hnon ⟨a, h.symm⟩
    have hk1 : ⌊lam⌋ < a := Int.floor_lt.2 hlt
    have hkl : (⌊lam⌋ : ℝ) < lam := lt_of_le_of_ne (Int.floor_le lam) fun h => hnon ⟨⌊lam⌋, h⟩
    have hku : lam < (⌊lam⌋ : ℝ) + 1 := Int.lt_floor_add_one lam
    have hk : ⌊lam⌋ ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hk0, hk1⟩
    rw [Phi_eq_rank (η n) (hηb n) hab hk hkl hku]
    have hs := sParam_spec (η n) (hηb n) hab hk hkl hku
    exact row_boundV hL hpos hκn (η n) (hηb n) hab hr hnb hna hs.1.le hs.2.1.le hk
      (rk_val (η n) (hηb n) hk0)
  -- the pointwise limit
  have hlim : ∀ lam : ℝ, lam ∈ Ioc (b : ℝ) a → lam ∉ range (Int.cast : ℤ → ℝ) →
      Tendsto (fun n : ℕ => Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam) atTop
        (𝓝 (fext L κ (Mu hκ u) f (xl lam))) := by
    intro lam hlam hnon
    have hk0 : b ≤ ⌊lam⌋ := Int.le_floor.2 hlam.1.le
    have hlt : lam < a := lt_of_le_of_ne hlam.2 fun h => hnon ⟨a, h.symm⟩
    have hk1 : ⌊lam⌋ < a := Int.floor_lt.2 hlt
    have h1 : (⌊lam⌋ : ℝ) < lam := lt_of_le_of_ne (Int.floor_le lam) fun h => hnon ⟨⌊lam⌋, h⟩
    have h2 : lam < (⌊lam⌋ : ℝ) + 1 := Int.lt_floor_add_one lam
    set k := ⌊lam⌋ with hkdef
    have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hk0, hk1⟩
    obtain ⟨-, hconv, c₀, hc₀, hsep⟩ :=
      selectionV hκ hκs hpos u hu hk0 hk1 hb ha η hηb hη hend h1 h2
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
    set q : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a
      (sParam (η n) (hηb n) (a := a) hk0 lam) with hqdef
    set Fv : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => responseVec L (κs n / ((n : ℝ) + 1)) (q n)
      with hFvdef
    have hFv : ∀ n : ℕ, QuantumNLS.FiniteResponse.Bop D.L (κs n / ((n + 1 : ℕ) : ℝ)) (q n) (Fv n) =
        q n := by
      intro n
      show QuantumNLS.FiniteResponse.Bop L (κs n / ((n + 1 : ℕ) : ℝ)) (q n) (Fv n) = q n
      rw [Nat.cast_succ, bop_eq_gaudin']
      exact gaudin_responseVec hL (hc n) (q n)
    -- the step quantiles (uniform in `s`: the printed "empirical quantiles tend to `Q` in `L²`, uniformly in `s`")
    have hs01 : ∀ n : ℕ, 0 < sParam (η n) (hηb n) (a := a) hk0 lam ∧
        sParam (η n) (hηb n) (a := a) hk0 lam < 1 := fun n =>
      ⟨(sParam_spec (η n) (hηb n) hab hk h1 h2).1, (sParam_spec (η n) (hηb n) hab hk h1 h2).2.1⟩
    have hQc : Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D‖) atTop (𝓝 0) :=
      hQ0 (fun n => sParam (η n) (hηb n) (a := a) hk0 lam)
        (fun n => ⟨(hs01 n).1.le, (hs01 n).2.le⟩)
    have hFc : Tendsto (fun n : ℕ => ‖stepL2 (Fv n) - F‖) atTop (𝓝 0) :=
      strong_response_V D hF hκs hpos q Fv hFv hQc
    have hrow := row_limitV D hκs hpos hfm hFf q Fv hFv hQc hFc
      (fun n => rk (η n) (hηb n) hk0) hε
      (hconv x hx)
      (by
        filter_upwards [hsep] with n hn j hj
        rw [abs_sub_comm]
        exact hε1.trans (hn j hj))
      (measure_mono_null (Ioo_subset_Ioo (by linarith) (by linarith)) hnull)
      (M := Cb L κp r a b)
      (by
        filter_upwards [hocc b hrlt_b, hocc a hrlt_a, hκp] with n hnb hna hκn
        exact row_boundV hL hpos hκn (η n) (hηb n) hab hr hnb hna (hs01 n).1.le (hs01 n).2.le hk
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
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a) (volume.restrict (Ioc (b : ℝ) a)) :=
    fun n => (measurable_Phi hL (hc n) (η n) (hηb n) a).aestronglyMeasurable
  have hbd : ∀ᶠ n : ℕ in atTop, ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)),
      ‖Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam‖ ≤ Cb L κp r a b := by
    filter_upwards [hunif] with n hn
    filter_upwards [hae'] with lam hl
    rw [Real.norm_eq_abs]
    exact hn lam hl.1 hl.2
  have hlimae : ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)),
      Tendsto (fun n : ℕ => Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam) atTop
        (𝓝 (fext L κ (Mu hκ u) f (xl lam))) := by
    filter_upwards [hae'] with lam hl
    exact hlim lam hl.1 hl.2
  have hDC := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc (b : ℝ) a)) (l := atTop) (fun _ => Cb L κp r a b)
    (Eventually.of_forall hmeas) hbd (integrable_const _) hlimae
  have hψm : AEStronglyMeasurable (fun lam => fext L κ (Mu hκ u) f (xl lam))
      (volume.restrict (Ioc (b : ℝ) a)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hmeas hlimae
  have hψb : ∀ᵐ lam ∂(volume.restrict (Ioc (b : ℝ) a)),
      ‖fext L κ (Mu hκ u) f (xl lam)‖ ≤ Cb L κp r a b := by
    filter_upwards [hae'] with lam hl
    have hev : ∀ᶠ n : ℕ in atTop,
        ‖Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam‖ ≤ Cb L κp r a b := by
      filter_upwards [hunif] with n hn
      rw [Real.norm_eq_abs]
      exact hn lam hl.1 hl.2
    exact le_of_tendsto (hlim lam hl.1 hl.2).norm hev
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hba]
    exact Integrable.mono' (integrable_const (Cb L κp r a b)) hψm hψb
  · have h2 : Tendsto (fun n : ℕ => ∫ lam in (b : ℝ)..(a : ℝ),
        Phi L (κs n / ((n : ℝ) + 1)) (η n) (hηb n) a lam) atTop
        (𝓝 (∫ lam in (b : ℝ)..(a : ℝ), fext L κ (Mu hκ u) f (xl lam))) := by
      simpa only [intervalIntegral.integral_of_le hba] using hDC
    refine (h2.const_mul (4 * Real.pi)).congr fun n => ?_
    exact (hid n).symm

end QuantumNLS.VarMain

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarMain.row_boundV
#print axioms QuantumNLS.VarMain.variable_coupling_core
