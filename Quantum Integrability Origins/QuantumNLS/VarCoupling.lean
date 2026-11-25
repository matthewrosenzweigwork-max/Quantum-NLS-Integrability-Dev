import Mathlib
import QuantumNLS.F04SelSetup

/-!
# CC:F04:variable-coupling (R-C88B5D59), step 1: the real-label equations and path measures at contact `c_N = κ_N/N`

Source: `F04.tex` line 412, Proposition `CC:F04:variable-coupling`: "replace the finite contact parameter by `c_N = κ_N/N` ... The path-distance identity (CC:F04:path-distance) is independent of the contact parameter, so its quadratic-Wasserstein estimate and uniformity in the interpolation parameter remain valid. ... the exact real-label identity holds at every `c_N > 0`".

Generalizations of `F04SelSetup.qPath_realBethe` and `F04SelConv.path_weak0` (both read-only, stated with the fixed `c = κ/(n+1)`) to a coupling sequence `κs : ℕ → ℝ`, `κs N > 0`:
* `RealBetheV L κs N q ν`: the printed real-label Bethe equations (CC:F04:real-bethe) with `c_N = κs N/(N+1)`;
* `qPath_realBetheV`: the interpolated roots `q_N(s)` solve them with labels `ν(s)`;
* `path_weak0V`: weak limit along `s_N ∈ [0,1]` equals that of the `s = 0` endpoint (the l1 path-distance bound is independent of `c`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace QuantumNLS.VarCoupling

open QuantumNLS.BetheLabels QuantumNLS.BetheSmooth QuantumNLS.AdjacentResponse QuantumNLS.F02FiniteGap
open QuantumNLS.BetheRoots QuantumNLS.GaudinResponse QuantumNLS.RootDisplacement
open QuantumNLS.OrderedResponse QuantumNLS.RootContraction
open QuantumNLS.Ext025A6 (realLabelForce f02_roots_joint_analyticAt f02_roots_solve)
open QuantumNLS.RootDisplacementEstimate (pair_identity count_erase)
open QuantumNLS.LocalHeight QuantumNLS.F04SelSetup

/-- `CC:F04:real-bethe` at particle number `N + 1` and contact `c_N = κs N/(N+1)`. -/
structure RealBetheV (L : ℝ) (κs : ℕ → ℝ) (N : ℕ) (q ν : Fin (N + 1) → ℝ) : Prop where
  sorted : StrictMono q
  labels : Monotone ν
  eqn : ∀ i, L * q i - 2 * ∑ j ∈ Finset.univ.erase i,
      Real.arctan (κs N / ((N : ℝ) + 1) / (q i - q j)) = 2 * Real.pi * ν i

theorem qPath_realBetheV {L : ℝ} {κs : ℕ → ℝ} (hL : 0 < L) (hpos : ∀ N, 0 < κs N) {n : ℕ}
    (η : MArr (n + 1)) {b : ℤ} (hb : 1 ≤ η.1 b) (a : ℤ) {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    RealBetheV L κs n (qPath L (κs n / ((n : ℝ) + 1)) η hb a s) (nuPath η hb a s) := by
  have hc : 0 < κs n / ((n : ℝ) + 1) := div_pos (hpos n) (by positivity)
  have hν := nuPath_monotone η hb a h0 h1
  have hd := QuantumNLS.F02Round6Derivative.coupling_derivative hL hc hν
  dsimp only at hd
  obtain ⟨hq, -⟩ := hd
  set c := κs n / ((n : ℝ) + 1) with hcdef
  set q := root L (realLabelForce (nuPath η hb a s)) c with hqdef
  refine ⟨hq, hν, fun i => ?_⟩
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
  have h1' := f02_roots_solve hL hc (nuPath η hb a s) i
  rw [← hqdef] at h1'
  push_cast at h1' hsplit
  change L * q i - 2 * ∑ j ∈ Finset.univ.erase i, Real.arctan (c / (q i - q j)) =
    2 * Real.pi * nuPath η hb a s i
  linarith

/-- The weak limit of the empirical measures of the path roots `q_N(s_N)` at contact `κs N/(N+1)`
is that of the `s = 0` endpoint. -/
theorem path_weak0V {L : ℝ} {κs : ℕ → ℝ} (hL : 0 < L) (hpos : ∀ N, 0 < κs N) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {a b : ℤ} (hab : b < a) (η : (n : ℕ) → MArr (n + 1))
    (hb : ∀ n, 1 ≤ (η n).1 b)
    (hend : EmpiricalWeakConv (fun n => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hb n) a 0) μ)
    (s : ℕ → ℝ) (hs0 : ∀ n, 0 ≤ s n) (hs1 : ∀ n, s n ≤ 1) :
    EmpiricalWeakConv (fun n => qPath L (κs n / ((n : ℝ) + 1)) (η n) (hb n) a (s n)) μ := by
  refine weakConv_of_l1 hend ?_
  have hC : Tendsto (fun N : ℕ => (1 / ((N : ℝ) + 1)) * (2 * Real.pi * ((a : ℝ) - b) / L)) atTop
      (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const
      (2 * Real.pi * ((a : ℝ) - b) / L)
    simpa using this
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hC
  have hc : 0 < κs N / ((N : ℝ) + 1) := div_pos (hpos N) (by positivity)
  have h0 := path_l1 hL hc (η N) (hb N) hab (le_refl (0 : ℝ)) zero_le_one
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc ∑ j, |qPath L (κs N / ((N : ℝ) + 1)) (η N) (hb N) a (s N) j -
        qPath L (κs N / ((N : ℝ) + 1)) (η N) (hb N) a 0 j|
      ≤ ∑ j, |qPath L (κs N / ((N : ℝ) + 1)) (η N) (hb N) a 0 j -
        qPath L (κs N / ((N : ℝ) + 1)) (η N) (hb N) a 1 j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        obtain ⟨m1, m2⟩ := path_mono hL hc (η N) (hb N) hab (hs0 N) (hs1 N) j
        have m3 := (path_mono hL hc (η N) (hb N) hab (le_refl (0 : ℝ)) zero_le_one j).2
        rw [abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
    _ = 2 * Real.pi * ((a : ℝ) - b) / L := by rw [h0]; ring

end QuantumNLS.VarCoupling

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.VarCoupling.qPath_realBetheV
#print axioms QuantumNLS.VarCoupling.path_weak0V
