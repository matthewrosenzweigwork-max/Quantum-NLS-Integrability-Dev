import Mathlib
import QuantumNLS.BornConvergence
import QuantumNLS.QuantileTransport
import QuantumNLS.StrongLimitBulk
import QuantumNLS.GaudinResponse
import QuantumNLS.FiniteResponse
import QuantumNLS.DetGapW2

/-!
# R-BB7EDFF3 (`CC:F03:actual`), the deterministic ingredients and their in-probability forms

Source: `source-text/chapters/root_response/F03.tex`, the quantile criterion (lines 305-317) and the
proof of `CC:F03:actual` (lines 342-371).

* `w2_nbhd`: the printed neighbourhood form of the quantile criterion.  For every `ε > 0` there is a
  neighbourhood of `(μ, ∫x²dμ)` in the product of the Lévy-Prokhorov metric and the second-moment value
  on which `W₂(ν, μ) < ε`; otherwise a deterministic sequence would violate
  `QuantileTransport.tendsto_W2_of_weak_of_moment` (weak convergence plus convergence of second moments
  gives `W₂ → 0`; F05 clause 3, the ordered quantile coupling).
* `quantile_inProb`: weak convergence in probability plus second-moment convergence in probability give
  `W₂(ν_N, μ) → 0` in probability, over the varying probability spaces.
* `response_local_uniform`: the printed sequential local uniformity of the deterministic response theorem
  (`StrongLimitBulk.strong_limit_bulk`): for every `ε > 0` there are `δ > 0` and `N₀` with
  `‖stepL2 q − Q‖ < δ ⟹ ‖stepL2 (B_N⁻¹ q) − F‖ < ε` for every `N ≥ N₀` and every real array `q`.
* `response_norm_sq_le`: the printed bound `L² ‖F_N‖² ≤ ‖Q_N‖²` for `F_N = stepL2 (B_N⁻¹ q)`.

`B_N⁻¹ q` is `GaudinResponse.responseVec` (DEF-051), converted to the printed operator `Bop` of
`StrongLimitBulk.strong_limit_bulk` by `bop_eq_gaudin`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Matrix

noncomputable section

namespace QuantumNLS.F03ActualQuantile

open QuantumNLS.BornConvergence (TendstoInProbability)
open QuantumNLS.QuantileTransport (W2 HasFiniteSecondMoment WeakConv weakConv_of_tendsto
  tendsto_W2_of_weak_of_moment empirical)
open QuantumNLS.BulkResponseForm (L2Unit BulkResponseData)
open QuantumNLS.StepIntegrals (stepL2 norm_sq_step)
open QuantumNLS.StrongLimitBulk (Q2 strong_limit_bulk)
open QuantumNLS.FiniteResponse (Bop L2N response_bounds)
open QuantumNLS.GaudinResponse (gaudinMatrix responseVec gaudin_responseVec gaudinMatrix_mulVec)

/-! ### The quantile criterion in neighbourhood form -/

theorem w2_nbhd (μ : MeasureTheory.ProbabilityMeasure ℝ) (hμ : HasFiniteSecondMoment (μ : Measure ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ν : MeasureTheory.ProbabilityMeasure ℝ, HasFiniteSecondMoment (ν : Measure ℝ) →
      levyProkhorovDist (ν : Measure ℝ) (μ : Measure ℝ) < δ →
      |(∫ x, x ^ 2 ∂(ν : Measure ℝ)) - ∫ x, x ^ 2 ∂(μ : Measure ℝ)| < δ →
      (W2 (ν : Measure ℝ) (μ : Measure ℝ)).toReal < ε := by
  by_contra hcon
  push Not at hcon
  have H : ∀ j : ℕ, ∃ ν : MeasureTheory.ProbabilityMeasure ℝ, HasFiniteSecondMoment (ν : Measure ℝ) ∧
      levyProkhorovDist (ν : Measure ℝ) (μ : Measure ℝ) < 1 / ((j : ℝ) + 1) ∧
      |(∫ x, x ^ 2 ∂(ν : Measure ℝ)) - ∫ x, x ^ 2 ∂(μ : Measure ℝ)| < 1 / ((j : ℝ) + 1) ∧
      ε ≤ (W2 (ν : Measure ℝ) (μ : Measure ℝ)).toReal :=
    fun j => hcon (1 / ((j : ℝ) + 1)) (by positivity)
  choose ν hν1 hν2 hν3 hν4 using H
  have hsmall : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- Lévy-Prokhorov convergence
  have hLP : Tendsto (fun j => levyProkhorovDist (ν j : Measure ℝ) (μ : Measure ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun j => by unfold levyProkhorovDist; exact ENNReal.toReal_nonneg) (fun j => (hν2 j).le) hsmall
  have hLP' : Tendsto (fun j => (LevyProkhorov.ofMeasure (ν j) :
      LevyProkhorov (MeasureTheory.ProbabilityMeasure ℝ))) atTop
      (𝓝 (LevyProkhorov.ofMeasure μ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact hLP
  have hweak : Tendsto ν atTop (𝓝 μ) :=
    (LevyProkhorov.continuous_toMeasure_probabilityMeasure.tendsto
      (LevyProkhorov.ofMeasure μ)).comp hLP'
  have hw := weakConv_of_tendsto ν μ hweak
  have hmom : Tendsto (fun j => ∫ x, x ^ 2 ∂(ν j : Measure ℝ)) atTop
      (𝓝 (∫ x, x ^ 2 ∂(μ : Measure ℝ))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun j => dist_nonneg) (fun j => by rw [Real.dist_eq]; exact (hν3 j).le) hsmall
  have hW := tendsto_W2_of_weak_of_moment hν1 hμ hw hmom
  have hW' : Tendsto (fun j => (W2 (ν j : Measure ℝ) (μ : Measure ℝ)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
    rw [ENNReal.toReal_zero] at this
    exact this
  obtain ⟨j, hj⟩ := (hW'.eventually (gt_mem_nhds hε)).exists
  exact absurd (hν4 j) (not_le.2 hj)

/-- Weak convergence in probability and convergence of the second moments in probability give
`W₂(ν_N, μ) → 0` in probability, over varying probability spaces. -/
theorem quantile_inProb {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (ν : ∀ n, Ω n → MeasureTheory.ProbabilityMeasure ℝ) (μ : MeasureTheory.ProbabilityMeasure ℝ)
    (hfin : ∀ n ω, HasFiniteSecondMoment (ν n ω : Measure ℝ))
    (hμ : HasFiniteSecondMoment (μ : Measure ℝ))
    (hw : TendstoInProbability P (fun n ω => LevyProkhorov.ofMeasure (ν n ω))
      (LevyProkhorov.ofMeasure μ))
    (hm : TendstoInProbability P (fun n ω => ∫ x, x ^ 2 ∂(ν n ω : Measure ℝ))
      (∫ x, x ^ 2 ∂(μ : Measure ℝ))) :
    TendstoInProbability P (fun n ω => (W2 (ν n ω : Measure ℝ) (μ : Measure ℝ)).toReal) 0 := by
  intro ε hε
  obtain ⟨δ, hδ, hnb⟩ := w2_nbhd μ hμ hε
  have h1 := hw (δ / 2) (by positivity)
  have h2 := hm (δ / 2) (by positivity)
  have hs := h1.add h2
  rw [add_zero] at hs
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
    (fun n => zero_le) (fun n => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hLP : levyProkhorovDist (ν n ω : Measure ℝ) (μ : Measure ℝ) < δ := by
    have : dist (LevyProkhorov.ofMeasure (ν n ω)) (LevyProkhorov.ofMeasure μ) =
        levyProkhorovDist (ν n ω : Measure ℝ) (μ : Measure ℝ) := rfl
    rw [← this]; linarith
  have hMom : |(∫ x, x ^ 2 ∂(ν n ω : Measure ℝ)) - ∫ x, x ^ 2 ∂(μ : Measure ℝ)| < δ := by
    rw [Real.dist_eq] at hc2; linarith
  have := hnb (ν n ω) (hfin n ω) hLP hMom
  rw [Real.dist_eq, sub_zero] at hω
  have h0 : 0 ≤ (W2 (ν n ω : Measure ℝ) (μ : Measure ℝ)).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg h0] at hω
  exact absurd hω (not_lt.2 this.le)

/-! ### The response: conversion `Bop = B` and local uniformity -/

theorem bop_eq_gaudin {N : ℕ} (L c : ℝ) (q v : Fin N → ℝ) :
    Bop L c q v = gaudinMatrix L c q *ᵥ v := by
  funext i
  rw [QuantumNLS.FiniteResponse.Bop_eq_erase, gaudinMatrix_mulVec]
  congr 1

theorem bop_responseVec {L c : ℝ} (hL : 0 < L) (hc : 0 < c) {N : ℕ} (q : Fin N → ℝ) :
    Bop L c q (responseVec L c q) = q := by
  rw [bop_eq_gaudin]
  exact gaudin_responseVec hL hc q

/-- **The printed bound** `L² ‖F_N‖² ≤ ‖Q_N‖²` for the step response of an arbitrary real array. -/
theorem response_norm_sq_le {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)
    (q : Fin N → ℝ) :
    L ^ 2 * ‖stepL2 (responseVec L (κ / N) q)‖ ^ 2 ≤ ‖stepL2 q‖ ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < κ / (N : ℝ) := by positivity
  have h := (response_bounds hL hκ hN (bop_responseVec hL hc q)).1
  rw [norm_sq_step hN, norm_sq_step hN]
  exact h

/-- **The printed sequential local uniformity** of the deterministic response theorem
(`CC:F03:deterministic`, `StrongLimitBulk.strong_limit_bulk`). -/
theorem response_local_uniform (D : BulkResponseData) {F : L2Unit} (hF : D.IsResponse F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q : Fin N → ℝ,
      ‖stepL2 q - Q2 D‖ < δ → ‖stepL2 (responseVec D.L (D.κ / N) q) - F‖ < ε := by
  by_contra hcon
  push Not at hcon
  have H : ∀ j : ℕ, ∃ N : ℕ, j + 1 ≤ N ∧ ∃ q : Fin N → ℝ, ‖stepL2 q - Q2 D‖ < 1 / ((j : ℝ) + 1) ∧
      ε ≤ ‖stepL2 (responseVec D.L (D.κ / N) q) - F‖ := by
    intro j
    obtain ⟨N, hN, q, hq1, hq2⟩ := hcon (1 / ((j : ℝ) + 1)) (by positivity) (j + 1) (Nat.succ_pos j)
    exact ⟨N, hN, q, hq1, hq2⟩
  choose N hN q hq1 hq2 using H
  have hNpos : ∀ j, 0 < N j := fun j => lt_of_lt_of_le (Nat.succ_pos j) (hN j)
  have hNt : Tendsto N atTop atTop :=
    tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hN j)) tendsto_id
  have hsmall : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hQc : Tendsto (fun j => ‖stepL2 (q j) - Q2 D‖) atTop (𝓝 0) :=
    squeeze_zero (fun j => norm_nonneg _) (fun j => (hq1 j).le) hsmall
  have hFv : ∀ j, Bop D.L (D.κ / N j) (q j) (responseVec D.L (D.κ / N j) (q j)) = q j := by
    intro j
    have hN' : (0 : ℝ) < N j := by exact_mod_cast hNpos j
    exact bop_responseVec D.hL (by have := D.hκ; positivity) (q j)
  have hlim := (strong_limit_bulk D hF hNpos hNt q (fun j => responseVec D.L (D.κ / N j) (q j))
    hFv hQc).1
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact absurd (hq2 j) (not_le.2 hj)

end QuantumNLS.F03ActualQuantile

#print axioms QuantumNLS.F03ActualQuantile.w2_nbhd
#print axioms QuantumNLS.F03ActualQuantile.quantile_inProb
#print axioms QuantumNLS.F03ActualQuantile.bop_responseVec
#print axioms QuantumNLS.F03ActualQuantile.response_norm_sq_le
#print axioms QuantumNLS.F03ActualQuantile.response_local_uniform
