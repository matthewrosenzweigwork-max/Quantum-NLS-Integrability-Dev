/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams

Adapted selected index, discreteness, integral algebra and norm-bound proofs from
https://github.com/bjbraams/lean-CA, commit333a684877588d3667c7a0d37e5074aaa2e5b7b7:
ComplexAnalysis/CurveIndex.lean, ComplexAnalysis/LogDerivIntegral.lean,
ComplexAnalysis/CurveIndex/Continuity.lean, ComplexAnalysis/Cycle.lean.
Finite structural leaf proofs replace globally-C1 generator hypotheses. The
far-field proof constructs the actual convex-ball primitive using pinned Mathlib.
-/

import NlsGge.Atomic.Support.ContourChain
import NlsGge.Atomic.Support.ContourKernelParameter
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-! Literal normalized indices for actual finite C1 chains and cycles.

Open chains retain their endpoint-ratio/continuity statements; integer values and
far-field zero require closed outer endpoints. All analytic integral uses prove
actual leaf integrability. This module asserts no Cauchy theorem, Jordan index-one,
source orientation, nested deformation, or Riesz idempotence result.
-/

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology unitInterval

namespace NlsGge.Atomic.ContourChain

namespace Chain

/-- The actual finite kernel integral with exactly the Riesz normalization. -/
def index {a b : ℂ} (c : Chain a b) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹))

lemma integrable_toSpanSingleton_of_continuousOn
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {a b : ℂ} (c : Chain a b) {U : Set ℂ} {f : ℂ → F}
    (hf : ContinuousOn f U) (hcU : c.trace ⊆ U) :
    c.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) :=
  Chain.integrable_of_continuousOn
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hf)
    (fun t => hcU (c.path_mem_trace t))

lemma integrable_sub_inv {a b : ℂ} (c : Chain a b) {w : ℂ} (hw : w ∉ c.trace) :
    c.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) :=
  c.integrable_toSpanSingleton_of_continuousOn
    ((continuousOn_id.sub continuousOn_const).inv₀
      (fun _ hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))) subset_rfl

lemma integral_sub_inv_eq_two_pi_I_mul_index {a b : ℂ} (c : Chain a b) (w : ℂ) :
    c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) =
      (2 * (Real.pi : ℂ) * Complex.I) * c.index w := by
  rw [index, ← mul_assoc, mul_inv_cancel₀ Complex.two_pi_I_ne_zero, one_mul]

/-- Only true off-trace scalar integrals are identified with the literal path integral. -/
lemma index_eq_arcIndex {a b : ℂ} (c : Chain a b) {w : ℂ} (hw : w ∉ c.trace) :
    c.index w = ContourKernelParameter.arcIndex c.path w := by
  rw [index, ContourKernelParameter.arcIndex,
    integral_eq_curveIntegral (c.integrable_sub_inv hw)]

lemma index_reverse {a b : ℂ} (c : Chain a b) {w : ℂ} (hw : w ∉ c.trace) :
    c.reverse.index w = -c.index w := by
  rw [index, index, integral_reverse (c.integrable_sub_inv hw), mul_neg]

/-- The leaf endpoint ratios telescope with actual middle-endpoint avoidance. -/
theorem exp_integral_sub_inv {a b : ℂ} (c : Chain a b) {w : ℂ} (hw : w ∉ c.trace) :
    Complex.exp (c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹))) =
      (b - w) / (a - w) := by
  induction c with
  | leaf γ hc =>
      have hi := (leaf γ hc).integrable_sub_inv hw
      exact ContourKernelParameter.exp_curveIntegral_sub_inv γ hc
        (fun t he => hw (he ▸ mem_range_self t))
  | @join a b d p q hp hq =>
      have hwp : w ∉ p.trace := fun hz => hw (by rw [trace_join]; exact Or.inl hz)
      have hwq : w ∉ q.trace := fun hz => hw (by rw [trace_join]; exact Or.inr hz)
      have hiP := p.integrable_sub_inv hwp
      have hiQ := q.integrable_sub_inv hwq
      have ha : a - w ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem p.source_mem_trace hwp)
      have hb : b - w ≠ 0 := sub_ne_zero.mpr (ne_of_mem_of_not_mem p.target_mem_trace hwp)
      change Complex.exp (p.integral _ + q.integral _) = _
      rw [Complex.exp_add, hp hwp, hq hwq]
      field_simp [ha, hb]

/-- Integer multiples require genuinely closed outer endpoints, not closed leaves. -/
theorem exists_int_integral_sub_inv {a : ℂ} (c : Chain a a) {w : ℂ} (hw : w ∉ c.trace) :
    ∃ n : ℤ, c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
  have hi := c.integrable_sub_inv hw
  apply Complex.exp_eq_one_iff.mp
  rw [c.exp_integral_sub_inv hw,
    div_self (sub_ne_zero.mpr (ne_of_mem_of_not_mem c.source_mem_trace hw))]

theorem exists_int_index {a : ℂ} (c : Chain a a) {w : ℂ} (hw : w ∉ c.trace) :
    ∃ n : ℤ, c.index w = (n : ℂ) := by
  obtain ⟨n, hn⟩ := c.exists_int_integral_sub_inv hw
  refine ⟨n, ?_⟩
  rw [index, hn, mul_comm (n : ℂ), ← mul_assoc,
    inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul]


/-- Open chains have continuous indices off their traces; no integer claim is made. -/
theorem continuousOn_index {a b : ℂ} (c : Chain a b) :
    ContinuousOn c.index c.traceᶜ := by
  induction c with
  | leaf γ hc => exact ContourKernelParameter.continuousOn_arcIndex γ hc
  | join p q hp hq =>
      have hp' : ContinuousOn p.index (join p q).traceᶜ :=
        hp.mono (by rw [trace_join]; exact compl_subset_compl.mpr subset_union_left)
      have hq' : ContinuousOn q.index (join p q).traceᶜ :=
        hq.mono (by rw [trace_join]; exact compl_subset_compl.mpr subset_union_right)
      refine (hp'.add hq').congr (fun w _ => ?_)
      change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * (p.integral _ + q.integral _) =
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * p.integral _ +
          (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * q.integral _
      exact mul_add _ _ _


/-- The zero far-field conclusion is restricted to genuinely closed chains. -/
theorem index_eq_zero_of_notMem_ball {a : ℂ} (c : Chain a a)
    {z₀ w : ℂ} {R : ℝ} (hball : c.trace ⊆ ball z₀ R) (hw : w ∉ ball z₀ R) :
    c.index w = 0 := by
  have hf : DifferentiableOn ℂ (fun z => (z - w)⁻¹) (ball z₀ R) :=
    (differentiableOn_id.sub_const w).inv
      (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hw))
  obtain ⟨P, hP⟩ := (convex_ball z₀ R).exists_forall_hasDerivWithinAt hf
  have hP' : ∀ z ∈ ball z₀ R, HasDerivAt P ((z - w)⁻¹) z :=
    fun z hz => (hP z hz).hasDerivAt (isOpen_ball.mem_nhds hz)
  obtain ⟨hi, he⟩ := c.integral_eq_sub_of_hasDerivAt hf.continuousOn hP' hball
  rw [index, he, sub_self, mul_zero]

section IntegralAlgebra
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {a b : ℂ}

lemma integral_sub (c : Chain a b) {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F}
    (h₁ : c.Integrable ω₁) (h₂ : c.Integrable ω₂) :
    c.integral (ω₁ - ω₂) = c.integral ω₁ - c.integral ω₂ := by
  induction c with
  | leaf γ hc => exact curveIntegral_sub h₁ h₂
  | join p q hp hq =>
      change p.integral (ω₁ - ω₂) + q.integral (ω₁ - ω₂) = _
      rw [hp h₁.1 h₂.1, hq h₁.2 h₂.2]
      change _ = (p.integral ω₁ + q.integral ω₁) - (p.integral ω₂ + q.integral ω₂)
      abel

lemma integral_congr (c : Chain a b) {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F}
    (h : EqOn ω₁ ω₂ c.trace) : c.integral ω₁ = c.integral ω₂ := by
  induction c with
  | leaf γ hc =>
      change curveIntegral ω₁ γ = curveIntegral ω₂ γ
      simp only [curveIntegral_def]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [curveIntegralFun_def]
      exact congrArg (fun T : ℂ →L[ℂ] F => T (derivWithin γ.extend I t))
        (h ((leaf γ hc).extend_mem_trace t))
  | join p q hp hq =>
      have hp' : EqOn ω₁ ω₂ p.trace := fun z hz => h (by rw [trace_join]; exact Or.inl hz)
      have hq' : EqOn ω₁ ω₂ q.trace := fun z hz => h (by rw [trace_join]; exact Or.inr hz)
      exact congrArg₂ (· + ·) (hp hp') (hq hq')

lemma integral_smul_const [CompleteSpace F] (c : Chain a b) {g : ℂ → ℂ} (v : F)
    (hint : c.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z))) :
    c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z • v)) =
      c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z)) • v := by
  induction c with
  | leaf γ hc =>
      change curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z • v)) γ =
        curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z)) γ • v
      simp only [curveIntegral_def, curveIntegralFun_def,
        ContinuousLinearMap.toSpanSingleton_apply, smul_smul, smul_eq_mul]
      exact intervalIntegral.integral_smul_const _ v
  | join p q hp hq =>
      change p.integral _ + q.integral _ = (p.integral _ + q.integral _) • v
      rw [hp hint.1, hq hint.2, add_smul]

/-- A genuine finite derivative bound, chosen before the function and scalar bound.
This inequality does not assert integrability of an arbitrary bounded function. -/
theorem exists_norm_integral_le (c : Chain a b) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (f : ℂ → F) (M : ℝ),
      (∀ z ∈ c.trace, ‖f z‖ ≤ M) →
      ‖c.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ ≤ L * M := by
  induction c with
  | leaf γ hc =>
      obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
        (hc.continuousOn_derivWithin uniqueDiffOn_Icc_zero_one le_rfl)
      refine ⟨max L 0, le_max_right _ _, fun f M hM => ?_⟩
      change ‖curveIntegral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ‖ ≤ _
      rw [curveIntegral_def]
      have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
          ‖curveIntegralFun (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) γ t‖ ≤
            max L 0 * M := by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        rw [curveIntegralFun_def, ContinuousLinearMap.toSpanSingleton_apply, norm_smul]
        exact mul_le_mul ((hL t (Ioc_subset_Icc_self ht)).trans (le_max_left _ _))
          (hM _ ((leaf γ hc).extend_mem_trace t)) (norm_nonneg _) (le_max_right _ _)
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
  | join p q hp hq =>
      obtain ⟨Lp, hLp, hp⟩ := hp
      obtain ⟨Lq, hLq, hq⟩ := hq
      refine ⟨Lp + Lq, add_nonneg hLp hLq, fun f M hM => ?_⟩
      have hpM : ∀ z ∈ p.trace, ‖f z‖ ≤ M := fun z hz => hM z (by rw [trace_join]; exact Or.inl hz)
      have hqM : ∀ z ∈ q.trace, ‖f z‖ ≤ M := fun z hz => hM z (by rw [trace_join]; exact Or.inr hz)
      calc
        ‖p.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) +
            q.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ ≤
          ‖p.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ +
            ‖q.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ := norm_add_le _ _
        _ ≤ Lp * M + Lq * M := add_le_add (hp f M hpM) (hq f M hqM)
        _ = (Lp + Lq) * M := by ring

end IntegralAlgebra

end Chain

namespace Cycle

/-- The actual finite sum of the normalized closed-chain indices. -/
def index (Γ : Cycle) (w : ℂ) : ℂ := ∑ i, (Γ.chain i).2.index w

lemma integrable_sub_inv (Γ : Cycle) {w : ℂ} (hw : w ∉ Γ.range) :
    Γ.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) :=
  fun i => (Γ.chain i).2.integrable_sub_inv (fun hz => hw (mem_iUnion.mpr ⟨i, hz⟩))

lemma integral_sub_inv_eq_two_pi_I_mul_index (Γ : Cycle) (w : ℂ) :
    Γ.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) =
      (2 * (Real.pi : ℂ) * Complex.I) * Γ.index w := by
  simp only [integral, index, Chain.integral_sub_inv_eq_two_pi_I_mul_index, Finset.mul_sum]

theorem exists_int_index (Γ : Cycle) {w : ℂ} (hw : w ∉ Γ.range) :
    ∃ n : ℤ, Γ.index w = (n : ℂ) := by
  classical
  have h (i : Fin Γ.n) : ∃ n : ℤ, (Γ.chain i).2.index w = (n : ℂ) :=
    (Γ.chain i).2.exists_int_index (fun hz => hw (mem_iUnion.mpr ⟨i, hz⟩))
  choose n hn using h
  exact ⟨∑ i, n i, by simp [index, hn]⟩

@[simp] lemma index_empty (w : ℂ) : empty.index w = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  exact Fin.elim0 i

lemma index_append (Γ Δ : Cycle) (w : ℂ) :
    (Γ.append Δ).index w = Γ.index w + Δ.index w := by
  change (∑ i : Fin (Γ.n + Δ.n), ((Γ.append Δ).chain i).2.index w) = _
  rw [Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [append_chain_castAdd])
  · exact Finset.sum_congr rfl (fun i _ => by rw [append_chain_natAdd])

lemma index_reverse (Γ : Cycle) {w : ℂ} (hw : w ∉ Γ.range) :
    Γ.reverse.index w = -Γ.index w := by
  change (∑ i, (Γ.chain i).2.reverse.index w) = -(∑ i, (Γ.chain i).2.index w)
  simp only [Chain.index_reverse _ (fun hz => hw (mem_iUnion.mpr ⟨_, hz⟩)), Finset.sum_neg_distrib]


theorem continuousOn_index (Γ : Cycle) : ContinuousOn Γ.index Γ.rangeᶜ :=
  continuousOn_finsetSum _ fun i _ => ((Γ.chain i).2.continuousOn_index).mono
    (compl_subset_compl.mpr (subset_iUnion (fun j => (Γ.chain j).2.trace) i))

/-- Discreteness is applied to the actual whole-cycle integer-valued function. -/
theorem index_eq_of_isPreconnected (Γ : Cycle) {U : Set ℂ} (hU : IsPreconnected U)
    (hUΓ : U ⊆ Γ.rangeᶜ) {v w : ℂ} (hv : v ∈ U) (hw : w ∈ U) :
    Γ.index v = Γ.index w := by
  apply hU.constant_of_mapsTo Complex.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range
    (Γ.continuousOn_index.mono hUΓ) _ hv hw
  intro z hz
  obtain ⟨n, hn⟩ := Γ.exists_int_index (hUΓ hz)
  exact ⟨n, hn.symm⟩

theorem exists_ball_index_eq (Γ : Cycle) {w : ℂ} (hw : w ∉ Γ.range) :
    ∃ r > 0, ball w r ⊆ Γ.rangeᶜ ∧ ∀ z ∈ ball w r, Γ.index z = Γ.index w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Γ.isOpen_compl_range w hw
  exact ⟨r, hr, hball, fun z hz => Γ.index_eq_of_isPreconnected
    (convex_ball w r).isPreconnected hball hz (mem_ball_self hr)⟩

theorem isOpen_setOf_index_eq (Γ : Cycle) (v : ℂ) :
    IsOpen {w | w ∉ Γ.range ∧ Γ.index w = v} := by
  rw [Metric.isOpen_iff]
  rintro w ⟨hw, hv⟩
  obtain ⟨r, hr, hball, heq⟩ := Γ.exists_ball_index_eq hw
  exact ⟨r, hr, fun z hz => ⟨hball hz, (heq z hz).trans hv⟩⟩


theorem index_eq_zero_of_notMem_ball (Γ : Cycle) {z₀ w : ℂ} {R : ℝ}
    (hball : Γ.range ⊆ ball z₀ R) (hw : w ∉ ball z₀ R) : Γ.index w = 0 :=
  Finset.sum_eq_zero fun i _ => (Γ.chain i).2.index_eq_zero_of_notMem_ball
    (fun _ hz => hball (mem_iUnion.mpr ⟨i, hz⟩)) hw

theorem exists_pos_index_eq_zero_outside_ball (Γ : Cycle) (z₀ : ℂ) :
    ∃ R > 0, Γ.range ⊆ ball z₀ R ∧ ∀ w, w ∉ ball z₀ R → Γ.index w = 0 := by
  obtain ⟨R, hR, hball⟩ := Γ.isBounded_range.subset_ball_lt 0 z₀
  exact ⟨R, hR, hball, fun w hw => Γ.index_eq_zero_of_notMem_ball hball hw⟩

section IntegralAlgebra
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma integrable_toSpanSingleton_of_continuousOn (Γ : Cycle) {U : Set ℂ} {f : ℂ → F}
    (hf : ContinuousOn f U) (hΓU : Γ.range ⊆ U) :
    Γ.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z)) :=
  Cycle.integrable_of_continuousOn
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ F).continuous.comp_continuousOn hf) hΓU

lemma integral_sub (Γ : Cycle) {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F}
    (h₁ : Γ.Integrable ω₁) (h₂ : Γ.Integrable ω₂) :
    Γ.integral (ω₁ - ω₂) = Γ.integral ω₁ - Γ.integral ω₂ := by
  unfold integral
  calc
    (∑ i, (Γ.chain i).2.integral (ω₁ - ω₂)) =
        ∑ i, ((Γ.chain i).2.integral ω₁ - (Γ.chain i).2.integral ω₂) :=
      Finset.sum_congr rfl (fun i _ => Chain.integral_sub _ (h₁ i) (h₂ i))
    _ = _ := by rw [Finset.sum_sub_distrib]

lemma integral_congr (Γ : Cycle) {ω₁ ω₂ : ℂ → ℂ →L[ℂ] F}
    (h : EqOn ω₁ ω₂ Γ.range) : Γ.integral ω₁ = Γ.integral ω₂ := by
  unfold integral
  exact Finset.sum_congr rfl (fun i _ => Chain.integral_congr _
    (fun _ hz => h (mem_iUnion.mpr ⟨i, hz⟩)))

lemma integral_smul_const [CompleteSpace F] (Γ : Cycle) {g : ℂ → ℂ} (v : F)
    (hint : Γ.Integrable (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z))) :
    Γ.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z • v)) =
      Γ.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z)) • v := by
  unfold integral
  calc
    (∑ i, (Γ.chain i).2.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z • v))) =
        ∑ i, (Γ.chain i).2.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (g z)) • v :=
      Finset.sum_congr rfl (fun i _ => Chain.integral_smul_const _ v (hint i))
    _ = _ := by rw [Finset.sum_smul]

/-- The finite length constant depends on the actual C1 leaves, before f and M. -/
theorem exists_norm_integral_le (Γ : Cycle) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (f : ℂ → F) (M : ℝ),
      (∀ z ∈ Γ.range, ‖f z‖ ≤ M) →
      ‖Γ.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ ≤ L * M := by
  classical
  have hchain (i : Fin Γ.n) := (Γ.chain i).2.exists_norm_integral_le (F := F)
  choose L hL0 hL using hchain
  refine ⟨∑ i, L i, Finset.sum_nonneg (fun i _ => hL0 i), fun f M hM => ?_⟩
  calc
    ‖Γ.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ ≤
        ∑ i, ‖(Γ.chain i).2.integral (fun z => ContinuousLinearMap.toSpanSingleton ℂ (f z))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, L i * M := Finset.sum_le_sum (fun i _ => hL i f M
      (fun z hz => hM z (mem_iUnion.mpr ⟨i, hz⟩)))
    _ = (∑ i, L i) * M := by rw [Finset.sum_mul]

end IntegralAlgebra

end Cycle
end NlsGge.Atomic.ContourChain
