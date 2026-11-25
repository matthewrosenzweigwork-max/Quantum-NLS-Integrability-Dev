import Mathlib
import QuantumNLS.BornConvergence

/-!
# R-BB7EDFF3 (`CC:F03:actual`), probabilistic ingredients on varying probability spaces

Source: `source-text/chapters/root_response/F03.tex`, proof of `CC:F03:actual` (lines 342-371 of the
source text).  Two elementary measure-theoretic steps of that proof, over the varying probability
spaces `(Ω n, P n)` of `BornConvergence.TendstoInProbability`:

* `inProb_of_L1`: `L¹` convergence of a random variable to a constant is convergence in probability
  (Markov); this turns "`E_N → E_*` in `L¹(P_{N,u})`" into convergence in probability;
* `tendsto_lintegral_of_dom`: a nonnegative random variable `X_n` that tends to `0` in probability and
  satisfies `X_n ≤ a E_n + b` with `E_n → E_*` in `L¹` has `E X_n → 0` (the "uniform integrability from
  `L¹` convergence of the dominating energy" step: `‖Q_N−Q‖² ≤ 2E_N+2E_*` and
  `‖F_N−F‖² ≤ 2E_N/L²+2‖F‖²`).

No hypothesis beyond those named is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.F03ActualProb

open QuantumNLS.BornConvergence (TendstoInProbability)

universe u

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

/-- `L¹` convergence to a constant implies convergence in probability (Markov). -/
theorem inProb_of_L1 (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ) (x : ℝ) (hint : ∀ n, Integrable (fun ω => X n ω - x) (P n))
    (h : Tendsto (fun n => ∫ ω, |X n ω - x| ∂P n) atTop (𝓝 0)) :
    TendstoInProbability P X x := by
  intro ε hε
  have hε' : (ENNReal.ofReal ε) ≠ 0 := (ENNReal.ofReal_pos.2 hε).ne'
  have hbound : ∀ n, P n {ω | ε < dist (X n ω) x} ≤
      ENNReal.ofReal (∫ ω, |X n ω - x| ∂P n) / ENNReal.ofReal ε := by
    intro n
    have hi : Integrable (fun ω => |X n ω - x|) (P n) := (hint n).abs
    have hae : AEMeasurable (fun ω => ENNReal.ofReal |X n ω - x|) (P n) :=
      hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    have h1 := meas_ge_le_lintegral_div hae hε' ENNReal.ofReal_ne_top
    have h2 : (∫⁻ ω, ENNReal.ofReal |X n ω - x| ∂P n) =
        ENNReal.ofReal (∫ ω, |X n ω - x| ∂P n) :=
      (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => abs_nonneg _))).symm
    rw [h2] at h1
    refine le_trans (measure_mono ?_) h1
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [Real.dist_eq] at hω
    exact ENNReal.ofReal_le_ofReal hω.le
  have hlim : Tendsto (fun n => ENNReal.ofReal (∫ ω, |X n ω - x| ∂P n) / ENNReal.ofReal ε)
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun n => ENNReal.ofReal (∫ ω, |X n ω - x| ∂P n)) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_ofReal h)
      simpa using this
    have := ENNReal.Tendsto.mul_const h0 (Or.inr (ENNReal.inv_ne_top.2 hε'))
    simpa [div_eq_mul_inv] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
    hbound

/-- A nonnegative random variable dominated by `a E_n + b`, with `E_n → E_*` in `L¹`, which tends to
`0` in probability, has expectation tending to `0`. -/
theorem tendsto_lintegral_of_dom (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X E : ∀ n, Ω n → ℝ) (hXm : ∀ n, Measurable (X n)) (hEm : ∀ n, Measurable (E n))
    (a b Es : ℝ) (ha : 0 ≤ a)
    (hdom : ∀ n ω, X n ω ≤ a * E n ω + b)
    (hEint : ∀ n, Integrable (E n) (P n))
    (hE : Tendsto (fun n => ∫ ω, |E n ω - Es| ∂P n) atTop (𝓝 0))
    (hX : TendstoInProbability P X 0) :
    Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal (X n ω) ∂P n) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  by_cases hηtop : η = ⊤
  · exact Eventually.of_forall fun _ => hηtop ▸ le_top
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  set ε : ℝ := η.toReal / 2 with hεdef
  have hε : 0 < ε := by positivity
  set c : ℝ := a * Es + b with hc
  -- the exceptional sets
  set A : ∀ n, Set (Ω n) := fun n => {ω | ε < dist (X n ω) 0} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by
    have : A n = {ω | ε < |X n ω|} := by
      ext ω; simp [hA, ]
    rw [this]
    exact measurableSet_lt measurable_const (hXm n).abs
  -- pointwise bound
  have hpt : ∀ n ω, ENNReal.ofReal (X n ω) ≤ ENNReal.ofReal ε +
      (ENNReal.ofReal (a * |E n ω - Es|) + (A n).indicator (fun _ => ENNReal.ofReal c) ω) := by
    intro n ω
    by_cases hω : ω ∈ A n
    · rw [Set.indicator_of_mem hω]
      have h1 : X n ω ≤ a * |E n ω - Es| + c := by
        have h2 : E n ω ≤ |E n ω - Es| + Es := by
          have := le_abs_self (E n ω - Es); linarith
        have := hdom n ω
        have h3 : a * E n ω ≤ a * (|E n ω - Es| + Es) := mul_le_mul_of_nonneg_left h2 ha
        rw [hc]; nlinarith
      calc ENNReal.ofReal (X n ω) ≤ ENNReal.ofReal (a * |E n ω - Es| + c) :=
            ENNReal.ofReal_le_ofReal h1
        _ ≤ ENNReal.ofReal (a * |E n ω - Es|) + ENNReal.ofReal c := ENNReal.ofReal_add_le
        _ ≤ _ := by
          rw [add_comm (ENNReal.ofReal ε)]
          exact le_self_add
    · have h1 : X n ω ≤ ε := by
        simp only [hA, Set.mem_ofPred_eq, not_lt, Real.dist_eq, sub_zero] at hω
        exact (le_abs_self _).trans hω
      calc ENNReal.ofReal (X n ω) ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal h1
        _ ≤ _ := le_self_add
  -- integral of the bound
  have hint : ∀ n, ∫⁻ ω, ENNReal.ofReal (X n ω) ∂P n ≤ ENNReal.ofReal ε +
      (ENNReal.ofReal a * ENNReal.ofReal (∫ ω, |E n ω - Es| ∂P n) +
        ENNReal.ofReal c * P n (A n)) := by
    intro n
    have hg1m : Measurable fun ω => ENNReal.ofReal (a * |E n ω - Es|) :=
      (((hEm n).sub_const Es).abs.const_mul a).ennreal_ofReal
    have hg2m : Measurable ((A n).indicator fun _ : Ω n => ENNReal.ofReal c) :=
      measurable_const.indicator (hAm n)
    have hEi : Integrable (fun ω => |E n ω - Es|) (P n) :=
      ((hEint n).sub (integrable_const Es)).abs
    have h1 : (∫⁻ ω, ENNReal.ofReal (a * |E n ω - Es|) ∂P n) =
        ENNReal.ofReal a * ENNReal.ofReal (∫ ω, |E n ω - Es| ∂P n) := by
      have : ∀ ω, ENNReal.ofReal (a * |E n ω - Es|) =
          ENNReal.ofReal a * ENNReal.ofReal |E n ω - Es| := fun ω => ENNReal.ofReal_mul ha
      simp_rw [this]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ofReal_integral_eq_lintegral_ofReal hEi (ae_of_all _ (fun _ => abs_nonneg _))]
    calc ∫⁻ ω, ENNReal.ofReal (X n ω) ∂P n
        ≤ ∫⁻ ω, (ENNReal.ofReal ε + (ENNReal.ofReal (a * |E n ω - Es|) +
            (A n).indicator (fun _ => ENNReal.ofReal c) ω)) ∂P n := lintegral_mono (hpt n)
      _ = ENNReal.ofReal ε + (∫⁻ ω, ENNReal.ofReal (a * |E n ω - Es|) ∂P n +
            ∫⁻ ω, (A n).indicator (fun _ => ENNReal.ofReal c) ω ∂P n) := by
          rw [lintegral_add_left measurable_const, lintegral_add_left hg1m, lintegral_const,
            measure_univ, mul_one]
      _ = _ := by
          rw [h1, lintegral_indicator_const (hAm n)]
  have ht1 : Tendsto (fun n => ENNReal.ofReal (∫ ω, |E n ω - Es| ∂P n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hE
  have ht2 : Tendsto (fun n => P n (A n)) atTop (𝓝 0) := hX ε hε
  have hlim : Tendsto (fun n => ENNReal.ofReal ε +
      (ENNReal.ofReal a * ENNReal.ofReal (∫ ω, |E n ω - Es| ∂P n) +
        ENNReal.ofReal c * P n (A n))) atTop
      (𝓝 (ENNReal.ofReal ε + (ENNReal.ofReal a * 0 + ENNReal.ofReal c * 0))) :=
    tendsto_const_nhds.add
      ((ENNReal.Tendsto.const_mul ht1 (Or.inr ENNReal.ofReal_ne_top)).add
        (ENNReal.Tendsto.const_mul ht2 (Or.inr ENNReal.ofReal_ne_top)))
  have hlt : ENNReal.ofReal ε + (ENNReal.ofReal a * 0 + ENNReal.ofReal c * 0) < η := by
    simp only [mul_zero, add_zero]
    calc ENNReal.ofReal ε < ENNReal.ofReal η.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hηr).2 (by rw [hεdef]; linarith)
      _ = η := ENNReal.ofReal_toReal hηtop
  filter_upwards [hlim.eventually (gt_mem_nhds hlt)] with n hn
  exact (hint n).trans hn.le

end QuantumNLS.F03ActualProb

#print axioms QuantumNLS.F03ActualProb.inProb_of_L1
#print axioms QuantumNLS.F03ActualProb.tendsto_lintegral_of_dom
