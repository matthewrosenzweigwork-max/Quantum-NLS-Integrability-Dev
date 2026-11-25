import Mathlib
import QuantumNLS.VarMain
import QuantumNLS.VarW2Weak

/-!
# CC:F04:variable-coupling (R-C88B5D59) as one named theorem

Source: `F04.tex` line 412, Proposition `CC:F04:variable-coupling` (`\\ReportID{R-C88B5D59}`):

  *Fix the limiting data `μ, I` at coupling `κ > 0` as above.  Let `κ_N → κ`, with `0 < κ_- ≤ κ_N ≤ κ_+ < ∞` for all sufficiently large `N`, and replace the finite contact parameter by `c_N = κ_N/N`.  Suppose that `a > b`, `I_a, I_b > 0`, the old occupations satisfy `η_b^{(N)} ≥ 1` and `η^{(N)}/N → I` in `ℓ¹`, and one endpoint empirical root measure for the transfer `η ↦ η − e_b + e_a` converges to `μ` in quadratic Wasserstein distance.  Using Theorem CC:F03:deterministic at fixed `κ` and the finite-`c` identities in Proposition CC:F02:finite-gap, the selection, separation, row limit and deterministic energy-gap limit above all hold.  The limiting `θ`, `x(λ)`, `F`, `f_ext` and `ω_ab` are those at `κ`.*

* hypotheses exactly as printed: `κs → κ`, `κ_- ≤ κs N ≤ κ_+` eventually (`hbd`), `a > b`, `I_a, I_b > 0`, `η_b ≥ 1`, `η/N → I` in `ℓ¹` (`hη`), and **one** endpoint (the old array `η`, or the transferred array `m = η − e_b + e_a`) with `W₂(μ_N, μ) → 0` (`hW2`, a disjunction); the weak convergence of the endpoint measure used by the selection proposition is derived from it (`VarW2Weak.weak_of_W2`, `weak_shift`);
* `hbulk`: `μ = M_u` satisfies the standing hypotheses of `CC:F03:section` (including `∫ x² dμ < ∞`), exactly as in `DetGapFinal`;
* `F` the response at `κ`, `f` with `f(Q) = F` a.e., `x(λ)` any solution of `θ(x) = πλ` (non-integer `λ`);
* conclusions: (selection, separation, row limit) `VarSelection.selectionV`; (energy gap) integrability of `f_ext(x(λ))` on `[b,a]` and `Q₂(m^{(N)}) − Q₂(η^{(N)}) → 4π ∫_b^a f_ext(x(λ)) dλ` (limiting coupling `κ`), where `Q₂` is computed from the roots at contact `κ_N/N`.
The proof passes to `κs' = κs` eventually (and `= κ` otherwise) so that `κs' > 0` everywhere (the printed bounds are only for large `N`); the statements are about limits, so this changes nothing.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.VarFinal

open QuantumNLS.BetheLabels QuantumNLS.F02FiniteGap QuantumNLS.AdjacentResponse QuantumNLS.BetheRoots
open QuantumNLS.F04SelSetup QuantumNLS.F04SelBand QuantumNLS.LocalHeight QuantumNLS.DetGapRowLim
open QuantumNLS.VarCoupling QuantumNLS.VarMain QuantumNLS.VarW2Weak
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData BulkMeasure)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.QuantileTransport (qm empirical W2)
open QuantumNLS.StepIntegrals (stepL2)
open QuantumNLS.StrongLimitBulk (Q2)
open PhysicalTensor (L2T)

/-- **`CC:F04:variable-coupling`** (R-C88B5D59): the energy-gap limit. -/
theorem variable_coupling {L κ : ℝ} [Fact (0 < L)] (hκ : 0 < κ) (u : L2T L)
    (hu : ‖u‖ = 1) (hbulk : BulkMeasure (Mu hκ u))
    {κs : ℕ → ℝ} (hκs : Tendsto κs atTop (𝓝 κ)) {κm κp : ℝ} (hκm : 0 < κm)
    (hbd : ∀ᶠ N : ℕ in atTop, κm ≤ κs N ∧ κs N ≤ κp)
    {b a : ℤ} (hab : b < a) (hb : 0 < II hκ u b) (ha : 0 < II hκ u a)
    (η : (n : ℕ) → MArr (n + 1)) (hηb : ∀ n, 1 ≤ (η n).1 b)
    (hη : Tendsto (fun n : ℕ => ∑' m : ℤ, |(((η n).1 m : ℕ) : ℝ) / ((n : ℝ) + 1) - II hκ u m|)
      atTop (𝓝 0))
    (hW2 : Tendsto (fun n : ℕ => W2 (empirical (n + 1) (arrRoots L (κs n / ((n : ℝ) + 1)) (η n)))
        (Mu hκ u)) atTop (𝓝 0) ∨
      Tendsto (fun n : ℕ => W2 (empirical (n + 1)
        (arrRoots L (κs n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a))) (Mu hκ u)) atTop (𝓝 0))
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
  have hab' : (0 : ℝ) ≤ (a : ℝ) - b := by
    have : (b : ℝ) < a := by exact_mod_cast hab
    linarith
  -- positivity normalization
  obtain ⟨κs', hκs'⟩ : ∃ κs' : ℕ → ℝ, κs' = fun n => if 0 < κs n then κs n else κ := ⟨_, rfl⟩
  have hev : ∀ᶠ n : ℕ in atTop, κs' n = κs n := by
    filter_upwards [hbd] with n hn
    rw [hκs']
    simp only [if_pos (lt_of_lt_of_le hκm hn.1)]
  have hpos : ∀ n, 0 < κs' n := by
    intro n
    rw [hκs']
    by_cases h : 0 < κs n
    · simp [h]
    · simp [h, hκ]
  have hκs'T : Tendsto κs' atTop (𝓝 κ) := hκs.congr' (hev.mono fun n hn => hn.symm)
  have hκp : ∀ᶠ n : ℕ in atTop, κs' n ≤ κp := by
    filter_upwards [hbd, hev] with n hn hn'
    rw [hn']; exact hn.2
  set D : BulkResponseData := ⟨L, κ, Fact.out, hκ, Mu hκ u, hbulk⟩ with hD
  have hcs : ∀ n : ℕ, 0 < κs' n / ((n : ℝ) + 1) := fun n => div_pos (hpos n) (by positivity)
  -- monotone endpoints
  have hq0m : ∀ n : ℕ, Monotone (arrRoots L (κs' n / ((n : ℝ) + 1)) (η n)) := by
    intro n
    rw [← qPath_zero L _ (η n) (hηb n) a]
    exact (qPath_realBetheV hL hpos (η n) (hηb n) a le_rfl zero_le_one).sorted.monotone
  have hq1m : ∀ n : ℕ, Monotone (arrRoots L (κs' n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a)) := by
    intro n
    rw [← qPath_one L _ (η n) (hηb n) a]
    exact (qPath_realBetheV hL hpos (η n) (hηb n) a zero_le_one le_rfl).sorted.monotone
  -- the Wasserstein hypothesis, on the `κs'` arrays
  have hW2' : Tendsto (fun n : ℕ => W2 (empirical (n + 1)
        (arrRoots L (κs' n / ((n : ℝ) + 1)) (η n))) (Mu hκ u)) atTop (𝓝 0) ∨
      Tendsto (fun n : ℕ => W2 (empirical (n + 1)
        (arrRoots L (κs' n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a))) (Mu hκ u)) atTop (𝓝 0) := by
    rcases hW2 with h | h
    · left
      exact h.congr' (hev.mono fun n hn => by simp only [hn])
    · right
      exact h.congr' (hev.mono fun n hn => by simp only [hn])
  -- the old-endpoint weak convergence
  have hend : EmpiricalWeakConv (fun n : ℕ => arrRoots L (κs' n / ((n : ℝ) + 1)) (η n)) (Mu hκ u) := by
    rcases hW2' with h | h
    · exact weak_of_W2 D hq0m h
    · have h1 := weak_of_W2 D hq1m h
      have h1' : EmpiricalWeakConv (fun n : ℕ => qPath L (κs' n / ((n : ℝ) + 1)) (η n) (hηb n) a 1)
          (Mu hκ u) := by
        have : (fun n : ℕ => qPath L (κs' n / ((n : ℝ) + 1)) (η n) (hηb n) a 1) =
            fun n : ℕ => arrRoots L (κs' n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a) := by
          funext n; exact qPath_one L _ (η n) (hηb n) a
        rw [this]; exact h1
      have h0 := weak_shift hL hcs hab η hηb h1'
      have : (fun n : ℕ => qPath L (κs' n / ((n : ℝ) + 1)) (η n) (hηb n) a 0) =
          fun n : ℕ => arrRoots L (κs' n / ((n : ℝ) + 1)) (η n) := by
        funext n; exact qPath_zero L _ (η n) (hηb n) a
      rw [this] at h0; exact h0
  -- quantile convergence uniformly in `s`
  have hQ0 : ∀ s : ℕ → ℝ, (∀ n, 0 ≤ s n ∧ s n ≤ 1) →
      Tendsto (fun n : ℕ => ‖stepL2 (qPath L (κs' n / ((n : ℝ) + 1)) (η n) (hηb n) a (s n)) -
        Q2 D‖) atTop (𝓝 0) := by
    intro s hs
    rcases hW2' with h | h
    · refine QuantumNLS.DetGapW2.quantile_conv_of_W2 D (q0 := fun n =>
        arrRoots L (κs' n / ((n : ℝ) + 1)) (η n)) hq0m h (C := 2 * Real.pi * ((a : ℝ) - b) / L) ?_
      intro n
      have hpl := path_l1 hL (hcs n) (η n) (hηb n) hab (s := 0) le_rfl zero_le_one
      rw [sub_zero, mul_one] at hpl
      rw [← hpl]
      refine Finset.sum_le_sum fun j _ => ?_
      have hm := path_mono hL (hcs n) (η n) (hηb n) hab (hs n).1 (hs n).2 j
      rw [← qPath_zero L _ (η n) (hηb n) a]
      rw [abs_of_nonneg (by linarith [hm.1]), abs_of_nonpos (by linarith [hm.1, hm.2])]
      linarith [hm.1, hm.2]
    · refine QuantumNLS.DetGapW2.quantile_conv_of_W2 D (q0 := fun n =>
        arrRoots L (κs' n / ((n : ℝ) + 1)) (transfer (η n) (hηb n) a)) hq1m h
        (C := 2 * Real.pi * ((a : ℝ) - b) / L) ?_
      intro n
      have hpl := path_l1 hL (hcs n) (η n) (hηb n) hab (hs n).1 (hs n).2
      rw [← qPath_one L _ (η n) (hηb n) a, hpl]
      have : 0 ≤ 2 * Real.pi * ((a : ℝ) - b) / L := by positivity
      have h2 : 2 * Real.pi * ((a : ℝ) - b) * (1 - s n) / L ≤ 2 * Real.pi * ((a : ℝ) - b) / L := by
        apply div_le_div_of_nonneg_right _ hL.le
        have := (hs n).1
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hab']
      exact h2
  have hcore := variable_coupling_core hκ hκs'T hpos hκp u hu hbulk hab hb ha η hηb hη hend hQ0 hF
    hfm hFf xl hxl
  refine ⟨hcore.1, ?_⟩
  exact hcore.2.congr' (hev.mono fun n hn => by simp only [hn])

end QuantumNLS.VarFinal

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarFinal.variable_coupling
