import QuantumNLS.F04SelBand
import QuantumNLS.F04SelSetup
import QuantumNLS.SelectionBand

/-! R-F4C3E5BE CC:F04:selection (root_response/F04.tex:202), stage S4a: the convergence clause
`q_{i_N,N}(s_N(lambda)) -> x(lambda)` of the printed selection proposition, assembled from
* `F04SelBand` (physical band data `r < l`, `mu(r,l) = 0`, cumulative-mass brackets, `x(lambda)`),
* `F04SelRank` (rank bracketing `rank_lower`, `rank_upper`),
* `F04SelSetup` (forced rank, parameter `s_N(lambda)`, path roots solve the real-label Bethe
  equations, empirical-measure limit independent of `s`),
* `SelectionBand.selection_core` (review record, S3, read-only).
The separation clause is the other half of the printed proposition. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
namespace QuantumNLS.F04SelConv

open QuantumNLS.BetheLabels QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.LocalHeight QuantumNLS.F04SelRank QuantumNLS.F04SelSetup QuantumNLS.F04SelBand
open PhysicalTensor (L2T)

/-- The empirical measures along `s_N in [0,1]` have the weak limit of the `s = 0` endpoint
(the roots of the old arrays). -/
theorem path_weak0 {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {a b : ℤ} (hab : b < a) (η : (n : ℕ) → MArr (n + 1)) (hb : ∀ n, 1 ≤ (η n).1 b)
    (hend : EmpiricalWeakConv (fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hb n) a 0) μ)
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1) :
    EmpiricalWeakConv (fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hb n) a (s n)) μ := by
  refine weakConv_of_l1 hend ?_
  have hC : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * (2 * Real.pi * ((a : ℝ) - b) / L)) atTop
      (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (2 * Real.pi * ((a : ℝ) - b) / L)
    simpa using this
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hC
  have hc : 0 < κ / ((N : ℝ) + 1) := by positivity
  have h0 := path_l1 hL hc (η N) (hb N) hab (le_refl (0 : ℝ)) zero_le_one
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ j, |qPath L (κ / ((N : ℝ) + 1)) (η N) (hb N) a (s N) j -
        qPath L (κ / ((N : ℝ) + 1)) (η N) (hb N) a 0 j|
      ≤ ∑ j, |qPath L (κ / ((N : ℝ) + 1)) (η N) (hb N) a 0 j -
        qPath L (κ / ((N : ℝ) + 1)) (η N) (hb N) a 1 j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        obtain ⟨m1, m2⟩ := path_mono hL hc (η N) (hb N) hab (hs0 N) (hs1 N) j
        have m3 := (path_mono hL hc (η N) (hb N) hab (le_refl (0 : ℝ)) zero_le_one j).2
        rw [abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
    _ = 2 * Real.pi * ((a : ℝ) - b) / L := by rw [h0]; ring

/-- **Convergence clause of `CC:F04:selection`** (R-F4C3E5BE): for `lambda in (k, k+1)`, `b <= k < a`,
the solutions `x` of `theta_u(x) = pi lambda` exist, and the selected root at the printed parameter
`s_N(lambda)` converges to each of them. -/
theorem selection_conv {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1)
    {b a k : ℤ} (hbk : b ≤ k) (hka : k < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n)) (Mu hκ u))
    {lam : ℝ} (h1 : (k : ℝ) < lam) (h2 : lam < (k : ℝ) + 1) :
    (∃ x, th hκ u x = lam * Real.pi) ∧ ∀ x, th hκ u x = lam * Real.pi →
      Tendsto (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a
        (sParam (η n) (hηb n) (a := a) hbk lam) (rk (η n) (hηb n) hbk)) atTop (𝓝 x) := by
  haveI := Mu_prob hκ u hu
  have hL : 0 < L := Fact.out
  have hu0 := ne_zero_of_II_pos hκ hb
  have hab : b < a := lt_of_le_of_lt hbk hka
  have hk : k ∈ Finset.Ico b a := Finset.mem_Ico.2 ⟨hbk, hka⟩
  obtain ⟨j, ℓ, r, l, hbj, hjk, hkl, hla, hrl, hnull, hrth, hlth, hlow, hup⟩ :=
    band_data hκ u hu hb ha hbk hka
  obtain ⟨hex, hall⟩ := xlam_data hκ u hu hjk hkl hrth hlth hrl hu0 h1 h2
  refine ⟨?_, fun x hx => ?_⟩
  · obtain ⟨x, -, hx⟩ := hex
    exact ⟨x, hx⟩
  set s : ℕ → ℝ := fun n => sParam (η n) (hηb n) (a := a) hbk lam with hs
  have hs01 : ∀ n, 0 < s n ∧ s n < 1 ∧
      nuPath (η n) (hηb n) a (s n) (rk (η n) (hηb n) hbk) = lam :=
    fun n => sParam_spec (η n) (hηb n) hab hk h1 h2
  have hend0 : EmpiricalWeakConv (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a 0)
      (Mu hκ u) := by
    have : (fun n : ℕ => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a 0) =
        fun n : ℕ => arrRoots L (κ / ((n : ℝ) + 1)) (η n) := by
      funext n
      exact qPath_zero L _ (η n) (hηb n) a
    rw [this]
    exact hend
  have hw : EmpiricalWeakConv (fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a (s n))
      (Mu hκ u) :=
    path_weak0 hL hκ hab η hηb hend0 s (fun n => (hs01 n).1.le) (fun n => (hs01 n).2.1.le)
  have hB : ∀ n : ℕ, RealBethe L κ n (qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a (s n))
      (nuPath (η n) (hηb n) a (s n)) := fun n =>
    qPath_realBethe hL hκ (η n) (hηb n) a (hs01 n).1.le (hs01 n).2.1.le
  set q : (n : ℕ) → Fin (n + 1) → ℝ := fun n => qPath L (κ / ((n : ℝ) + 1)) (η n) (hηb n) a (s n)
    with hq
  set i : (n : ℕ) → Fin (n + 1) := fun n => rk (η n) (hηb n) hbk with hi
  have hna : ∀ y, Mu hκ u {y} = 0 := Mu_singleton hκ u
  have hmono : ∀ n, Monotone (q n) := fun n => (hB n).sorted.monotone
  have hfrac : Tendsto (fun n : ℕ => (((i n : ℕ) : ℝ) + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (∑' m : ℤ, (if m ≤ k then II hκ u m else 0))) := by
    refine (Ccum_tendsto hκ u (b := b) η hη k).congr fun n => ?_
    have := rk_val (η n) (hηb n) hbk
    have h' : (((rk (η n) (hηb n) hbk).val : ℕ) : ℝ) + 1 = ((Ccum (η n) k : ℕ) : ℝ) := by
      exact_mod_cast this
    simp only [hi]
    rw [h']
  have hloc : ∀ h : ℝ, 0 < h → ∀ᶠ n : ℕ in atTop, q n (i n) ∈ Ioo (r - h) (l + h) := by
    intro h hh
    filter_upwards [rank_lower (hna) hmono hw hfrac (hlow (r - h) (by linarith)),
      rank_upper (hna) hmono hw hfrac (hup (l + h) (by linarith))] with n hn1 hn2
    exact ⟨hn1, hn2⟩
  have hlab : Tendsto (fun n : ℕ => nuPath (η n) (hηb n) a (s n) (i n)) atTop (𝓝 lam) := by
    have : (fun n : ℕ => nuPath (η n) (hηb n) a (s n) (i n)) = fun _ => lam :=
      funext fun n => (hs01 n).2.2
    rw [this]
    exact tendsto_const_nhds
  obtain ⟨hxm, hxθ⟩ := hall x hx
  have hθ : theta L κ (Mu hκ u) x = Real.pi * lam := by rw [hxθ]; ring
  exact SelectionBand.selection_core hL hκ hna hrl hnull hB hw i hloc hlab hxm hθ

end QuantumNLS.F04SelConv
#print axioms QuantumNLS.F04SelConv.path_weak0
#print axioms QuantumNLS.F04SelConv.selection_conv
