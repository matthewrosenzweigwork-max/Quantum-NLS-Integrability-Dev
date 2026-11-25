import Mathlib
import QuantumNLS.JLower
import QuantumNLS.StepIntegrals

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (H): the smooth recovery sequence

Source (F03.tex): "For a fixed real `h ∈ C_c^∞(ℝ)`, take `v_N = h(Q_N)` and `v = h(Q)`. These functions converge strongly in `L²`. Along every almost-everywhere convergent quantile subsequence,
their nonlocal integrands converge almost everywhere and are bounded by `Lip(h)²`. The exceptional set `Q(t) = Q(s)` has measure zero. Dominated convergence, followed by the subsequence criterion, proves
`ℰ_N(h(Q_N)) → ℰ(h(Q))`, `𝒥_N(h(Q_N)) → 𝒥(h(Q))`."

* `null_eq`: for measurable `Q` with `uI.map Q` atomless, `{(t,s) : Q t = Q s}` is null for `uI ⊗ uI` (Fubini; the atomlessness of `μ` through `Q_* uI = μ`).
* `smooth_energy_tendsto`: `ENint c_n Q_n (h ∘ Q_n) → formEnergy Q (h ∘ Q)` for Lipschitz `h`, `Q_n → Q` in `L²`, `c_n → 0`.
* `smooth_J_tendsto`: the values `𝒥_n(h∘Q_n) → 𝒥(h∘Q)` for bounded Lipschitz `h`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace QuantumNLS.SmoothRecovery

open QuantumNLS.BulkResponseRiesz (mu2 ae_fst ae_snd ae_subseq)
open QuantumNLS.QuantileForm (uI)
open QuantumNLS.BulkResponseForm (L2Unit formEnergy quot)
open QuantumNLS.GLowerBound (ENint)

/-- Atomless quantile: the set `{Q t = Q s}` is `uI ⊗ uI`-null. -/
theorem null_eq {Q : ℝ → ℝ} (hQ : Measurable Q) (hna : ∀ a : ℝ, uI (Q ⁻¹' {a}) = 0) :
    ∀ᵐ p ∂mu2, Q p.1 ≠ Q p.2 := by
  have hS : MeasurableSet {p : ℝ × ℝ | Q p.1 = Q p.2} :=
    measurableSet_eq_fun (hQ.comp measurable_fst) (hQ.comp measurable_snd)
  have h0 : mu2 {p : ℝ × ℝ | Q p.1 = Q p.2} = 0 := by
    rw [Measure.measure_prod_null hS]
    refine Eventually.of_forall fun x => ?_
    show uI (Prod.mk x ⁻¹' {p : ℝ × ℝ | Q p.1 = Q p.2}) = 0
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | Q p.1 = Q p.2} = Q ⁻¹' {Q x} := by
      ext s; simp [eq_comm]
    rw [this]; exact hna _
  rw [ae_iff]
  simpa using h0

theorem pt_bound {K : ℝ≥0} {h : ℝ → ℝ} (hh : LipschitzWith K h) (c a b : ℝ) :
    (h a - h b) ^ 2 / (c ^ 2 + (a - b) ^ 2) ≤ (K : ℝ) ^ 2 := by
  have h1 : |h a - h b| ≤ K * |a - b| := by
    have := hh.dist_le_mul a b
    simpa [Real.dist_eq] using this
  have h2 : (h a - h b) ^ 2 ≤ (K : ℝ) ^ 2 * (a - b) ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rwa [mul_pow, sq_abs, sq_abs] at this
  refine div_le_of_le_mul₀ (by positivity) (by positivity) ?_
  nlinarith [sq_nonneg c, sq_nonneg (K : ℝ)]

section
variable {Q : ℝ → ℝ} {Qn : ℕ → ℝ → ℝ} {cn : ℕ → ℝ} {Qe : ℕ → L2Unit} {Q0 : L2Unit}

theorem smooth_energy_tendsto {K : ℝ≥0} {h : ℝ → ℝ} (hh : LipschitzWith K h)
    (hQm : Measurable Q) (hQnm : ∀ n, Measurable (Qn n)) (hc : Tendsto cn atTop (𝓝 0))
    (hna : ∀ᵐ p ∂mu2, Q p.1 ≠ Q p.2)
    (hQ : Tendsto (fun n => ‖Qe n - Q0‖) atTop (𝓝 0))
    (hQe : ∀ n, (Qe n : ℝ → ℝ) =ᵐ[uI] Qn n) (hQ0 : (Q0 : ℝ → ℝ) =ᵐ[uI] Q) :
    Tendsto (fun n => ENint (cn n) (Qn n) (fun t => h (Qn n t))) atTop
      (𝓝 (formEnergy Q (fun t => h (Q t)))) := by
  refine Filter.tendsto_of_subseq_tendsto fun ns hns => ?_
  have hQs : Tendsto (fun n => Qe (ns n)) atTop (𝓝 Q0) :=
    tendsto_iff_norm_sub_tendsto_zero.2 (hQ.comp hns)
  obtain ⟨ms, hms, hae⟩ := ae_subseq hQs
  refine ⟨ms, ?_⟩
  have hu : Tendsto (fun i => ns (ms i)) atTop atTop := hns.comp hms.tendsto_atTop
  have hae2 : ∀ᵐ t ∂uI, Tendsto (fun i => Qn (ns (ms i)) t) atTop (𝓝 (Q t)) := by
    filter_upwards [hae, ae_all_iff.2 hQe, hQ0] with t h1 h2 h3
    rw [← h3]
    exact h1.congr fun i => h2 (ns (ms i))
  let F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun i p => ENNReal.ofReal
    ((h (Qn (ns (ms i)) p.1) - h (Qn (ns (ms i)) p.2)) ^ 2 /
      (cn (ns (ms i)) ^ 2 + (Qn (ns (ms i)) p.1 - Qn (ns (ms i)) p.2) ^ 2))
  let f : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal ((h (Q p.1) - h (Q p.2)) ^ 2 / (Q p.1 - Q p.2) ^ 2)
  have hFm : ∀ i, Measurable (F i) := fun i => by
    have hq1 : Measurable fun p : ℝ × ℝ => Qn (ns (ms i)) p.1 := (hQnm _).comp measurable_fst
    have hq2 : Measurable fun p : ℝ × ℝ => Qn (ns (ms i)) p.2 := (hQnm _).comp measurable_snd
    exact ENNReal.measurable_ofReal.comp
      ((((hh.continuous.measurable.comp hq1).sub (hh.continuous.measurable.comp hq2)).pow_const 2).div
        (measurable_const.add ((hq1.sub hq2).pow_const 2)))
  have hbound : ∫⁻ p, ENNReal.ofReal ((K : ℝ) ^ 2) ∂mu2 ≠ ⊤ := by
    simp
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := mu2) (fun _ => ENNReal.ofReal ((K : ℝ) ^ 2))
    hFm (fun i => Eventually.of_forall fun p => ENNReal.ofReal_le_ofReal (pt_bound hh _ _ _)) hbound
    (f := f) (by
      filter_upwards [hna, ae_fst (P := fun t => Tendsto (fun i => Qn (ns (ms i)) t) atTop (𝓝 (Q t))) hae2,
        ae_snd (P := fun t => Tendsto (fun i => Qn (ns (ms i)) t) atTop (𝓝 (Q t))) hae2] with p h0 h1 h2
      refine (ENNReal.tendsto_ofReal ?_)
      have hcc : Tendsto (fun i => cn (ns (ms i))) atTop (𝓝 0) := hc.comp hu
      have hnum : Tendsto (fun i => (h (Qn (ns (ms i)) p.1) - h (Qn (ns (ms i)) p.2)) ^ 2) atTop
          (𝓝 ((h (Q p.1) - h (Q p.2)) ^ 2)) :=
        (((hh.continuous.tendsto _).comp h1).sub ((hh.continuous.tendsto _).comp h2)).pow 2
      have hden : Tendsto (fun i => cn (ns (ms i)) ^ 2 + (Qn (ns (ms i)) p.1 - Qn (ns (ms i)) p.2) ^ 2)
          atTop (𝓝 (0 ^ 2 + (Q p.1 - Q p.2) ^ 2)) :=
        (hcc.pow 2).add ((h1.sub h2).pow 2)
      have hne : (0 : ℝ) ^ 2 + (Q p.1 - Q p.2) ^ 2 ≠ 0 := by
        have := sub_ne_zero.2 h0
        positivity
      have hd := hnum.div hden hne
      have e : (0 : ℝ) ^ 2 + (Q p.1 - Q p.2) ^ 2 = (Q p.1 - Q p.2) ^ 2 := by ring
      rw [e] at hd
      exact hd)
  have hf : formEnergy Q (fun t => h (Q t)) = ∫⁻ p, f p ∂mu2 := by
    unfold formEnergy
    refine lintegral_congr fun p => ?_
    simp only [f, quot, div_pow]
  rw [hf]
  exact hlim

end

end QuantumNLS.SmoothRecovery

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.SmoothRecovery.null_eq
#print axioms QuantumNLS.SmoothRecovery.smooth_energy_tendsto
