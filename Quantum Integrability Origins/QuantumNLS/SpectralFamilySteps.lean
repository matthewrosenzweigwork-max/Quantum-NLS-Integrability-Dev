import QuantumNLS.CompactSpectralHelpers

/-!
# Level-`y` continuity steps for antitone compact resolvent families (EXT-001 helpers only)

Authorized scope (VERIFIED SCOPED OWNER APPROVAL, `implementation/ops/STATUS.md`, S2): compact
spectral HELPER lemmas. This module states and proves NO continuity principle, NO
`AbstractContinuity`, and NO density/completeness claim; it gives per-level (finite-rank) steps.

Setting (`Hyp`): a family `R t` (`t ≥ 0`) of bounded symmetric operators on a complex Hilbert space
with `‖R t x‖² ≤ Re⟨R t x, x⟩` (as for the inverse of an operator `≥ 1`), antitone in form order,
strongly right continuous, `R 0` compact; and a family of continuous, nonzero, linearly independent
eigenvectors `R t (v t i) = μ t i • v t i` (`μ` real).

* `Hyp.compact`, `Hyp.pos`, `Hyp.norm_apply_le`: every `R t` is compact and positive, `‖R t‖ ≤ 1`;
* `Hyp.mu_eq`, `Hyp.mu_rcont`: `μ t i` is a Rayleigh quotient and is right continuous in `t`;
* `Hyp.right_step`: if the level-`y` spanning property `FullAt` holds at `τ`, then for all `s ≥ τ`
  close to `τ` it holds at `s`, with the same set of indices above level `y`;
* `Hyp.left_le`: left lower semicontinuity of the branch values `μ · i` (only downward jumps).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal Topology
open Filter

namespace QuantumNLS.SpectralFamilySteps

open QuantumNLS.CompactSpectralHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {ι : Type*}

/-- Hypotheses on a resolvent-type family and an eigenvector family. -/
structure Hyp (R : ℝ≥0 → E →L[ℂ] E) (v : ℝ≥0 → ι → E) (μ : ℝ≥0 → ι → ℝ) : Prop where
  symm : ∀ t, (R t : E →ₗ[ℂ] E).IsSymmetric
  dom : ∀ t x, ‖R t x‖ ^ 2 ≤ RCLike.re ⟪R t x, x⟫_ℂ
  anti : ∀ s t, s ≤ t → ∀ x, RCLike.re ⟪R t x, x⟫_ℂ ≤ RCLike.re ⟪R s x, x⟫_ℂ
  compact0 : IsCompactOperator (R 0)
  rcont : ∀ t f, Tendsto (fun s => R s f) (𝓝[≥] t) (𝓝 (R t f))
  vcont : ∀ i, Continuous fun t => v t i
  vne : ∀ t i, v t i ≠ 0
  indep : ∀ t, LinearIndependent ℂ (v t)
  eig : ∀ t i, R t (v t i) = (μ t i : ℂ) • v t i

variable {R : ℝ≥0 → E →L[ℂ] E} {v : ℝ≥0 → ι → E} {μ : ℝ≥0 → ι → ℝ}

namespace Hyp

variable (H : Hyp R v μ)
include H

lemma pos (t : ℝ≥0) (x : E) : 0 ≤ RCLike.re ⟪R t x, x⟫_ℂ := (sq_nonneg _).trans (H.dom t x)

lemma compact (t : ℝ≥0) : IsCompactOperator (R t) :=
  isCompactOperator_of_dom H.compact0 fun x => (H.dom t x).trans (H.anti 0 t bot_le x)

lemma norm_apply_le (t : ℝ≥0) (x : E) : ‖R t x‖ ≤ ‖x‖ := by
  have h1 := H.dom t x
  have h2 : RCLike.re ⟪R t x, x⟫_ℂ ≤ ‖R t x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h3 := norm_nonneg (R t x)
  have h4 := norm_nonneg x
  nlinarith

lemma re_eig (t : ℝ≥0) (i : ι) :
    RCLike.re ⟪R t (v t i), v t i⟫_ℂ = μ t i * ‖v t i‖ ^ 2 := by
  rw [H.eig t i, re_inner_real_smul]

lemma mu_eq (t : ℝ≥0) (i : ι) :
    μ t i = RCLike.re ⟪R t (v t i), v t i⟫_ℂ / ‖v t i‖ ^ 2 := by
  have hv : 0 < ‖v t i‖ ^ 2 := by have := norm_pos_iff.2 (H.vne t i); positivity
  rw [H.re_eig, mul_div_assoc, div_self hv.ne', mul_one]

/-- `R s (v s i) → R t (v t i)` as `s ↓ t`. -/
lemma tendsto_apply_v (t : ℝ≥0) (i : ι) :
    Tendsto (fun s => R s (v s i)) (𝓝[≥] t) (𝓝 (R t (v t i))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hv : Tendsto (fun s => ‖v s i - v t i‖) (𝓝[≥] t) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 ((H.vcont i).tendsto t)).mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun s => ‖R s (v t i) - R t (v t i)‖) (𝓝[≥] t) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (H.rcont t (v t i))
  have h0 := hv.add hR
  rw [add_zero] at h0
  refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) h0
  calc ‖R s (v s i) - R t (v t i)‖ = ‖R s (v s i - v t i) + (R s (v t i) - R t (v t i))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖R s (v s i - v t i)‖ + ‖R s (v t i) - R t (v t i)‖ := norm_add_le _ _
    _ ≤ ‖v s i - v t i‖ + ‖R s (v t i) - R t (v t i)‖ := by
        gcongr; exact H.norm_apply_le s _

/-- **Right continuity of the branch values** `t ↦ μ t i`. -/
lemma mu_rcont (t : ℝ≥0) (i : ι) : Tendsto (fun s => μ s i) (𝓝[≥] t) (𝓝 (μ t i)) := by
  have hvt : Tendsto (fun s => v s i) (𝓝[≥] t) (𝓝 (v t i)) :=
    ((H.vcont i).tendsto t).mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun s => RCLike.re ⟪R s (v s i), v s i⟫_ℂ) (𝓝[≥] t)
      (𝓝 (RCLike.re ⟪R t (v t i), v t i⟫_ℂ)) :=
    (RCLike.continuous_re.tendsto _).comp ((H.tendsto_apply_v t i).inner hvt)
  have hden : Tendsto (fun s => ‖v s i‖ ^ 2) (𝓝[≥] t) (𝓝 (‖v t i‖ ^ 2)) :=
    (hvt.norm).pow 2
  have hne : ‖v t i‖ ^ 2 ≠ 0 := by have := norm_pos_iff.2 (H.vne t i); positivity
  have := hnum.div hden hne
  rw [← H.mu_eq t i] at this
  exact this.congr fun s => (H.mu_eq s i).symm

/-- **Right step at level `y`.** -/
theorem right_step {y : ℝ} (hy : 0 < y) {τ : ℝ≥0} (hfull : FullAt (v τ) (μ τ) (R τ) y) :
    ∀ᶠ s in 𝓝[≥] τ, FullAt (v s) (μ s) (R s) y ∧ {i | y < μ s i} = {i | y < μ τ i} := by
  have hcount := (fullAt_iff_count (v τ) (μ τ) (H.compact τ) (H.symm τ) (H.indep τ) (H.eig τ) hy).1
    hfull
  have := finiteDimensional_eigUp (H.compact τ) (H.symm τ) hy
  obtain ⟨hJf, -, -⟩ := count_in_subspace (eigUp (R τ) y) (v τ) (H.indep τ) {i | y < μ τ i}
    (fun i hi => mem_eigUp hi (H.eig τ i))
  have hev : ∀ᶠ s in 𝓝[≥] τ, ∀ i ∈ {i | y < μ τ i}, y < μ s i :=
    (hJf.eventually_all).2 fun i hi => (H.mu_rcont τ i).eventually (lt_mem_nhds hi)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hsτ
  have := finiteDimensional_eigUp (H.compact s) (H.symm s) hy
  obtain ⟨hJs, hles, -⟩ := count_in_subspace (eigUp (R s) y) (v s) (H.indep s) {i | y < μ s i}
    (fun i hi => mem_eigUp hi (H.eig s i))
  have hmono := finrank_eigUp_mono (H.compact s) (H.symm s) (H.compact τ) (H.symm τ) (H.pos τ)
    (H.anti τ s hsτ) hy
  have hsub : {i | y < μ τ i} ⊆ {i | y < μ s i} := fun i hi => hs i hi
  have hcard : {i | y < μ s i}.ncard ≤ {i | y < μ τ i}.ncard := by
    omega
  have heq : {i | y < μ τ i} = {i | y < μ s i} := Set.eq_of_subset_of_ncard_le hsub hcard hJs
  refine ⟨(fullAt_iff_count (v s) (μ s) (H.compact s) (H.symm s) (H.indep s) (H.eig s) hy).2 ?_,
    heq.symm⟩
  have h1 := Set.ncard_le_ncard hsub hJs
  omega

/-- **Left lower semicontinuity of the branch values**: if `μ s i ≤ y` for all `s ∈ [a, τ)`
(`a < τ`), then `μ τ i ≤ y` (the branch values can only jump down from the left). -/
theorem left_le {y : ℝ} {a τ : ℝ≥0} (haτ : a < τ) (i : ι) (h : ∀ s, a ≤ s → s < τ → μ s i ≤ y) :
    μ τ i ≤ y := by
  have hne : (𝓝[<] τ).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_Iio' ⟨a, haτ⟩]; exact Set.mem_Iic.2 le_rfl)
  have hg : Continuous fun s => RCLike.re ⟪R τ (v s i), v s i⟫_ℂ - y * ‖v s i‖ ^ 2 :=
    ((RCLike.continuous_re.comp (((R τ).continuous.comp (H.vcont i)).inner (H.vcont i))).sub
      (continuous_const.mul ((H.vcont i).norm.pow 2)))
  have hlim : Tendsto (fun s => RCLike.re ⟪R τ (v s i), v s i⟫_ℂ - y * ‖v s i‖ ^ 2) (𝓝[<] τ)
      (𝓝 (RCLike.re ⟪R τ (v τ i), v τ i⟫_ℂ - y * ‖v τ i‖ ^ 2)) :=
    (hg.tendsto τ).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[<] τ, RCLike.re ⟪R τ (v s i), v s i⟫_ℂ - y * ‖v s i‖ ^ 2 ≤ 0 := by
    filter_upwards [Ioo_mem_nhdsLT haτ] with s hs
    have h1 := H.anti s τ hs.2.le (v s i)
    have h2 := H.re_eig s i
    have h3 := h s hs.1.le hs.2
    have h4 := sq_nonneg ‖v s i‖
    nlinarith
  have hle := le_of_tendsto hlim hev
  rw [H.re_eig] at hle
  have hv : 0 < ‖v τ i‖ ^ 2 := by have := norm_pos_iff.2 (H.vne τ i); positivity
  nlinarith

/-- **No entry above a level while the level-`y` spanning property holds**: on `[a, b]`, a
branch value at most `y` at `a` stays at most `y` at `b`. -/
theorem no_entry {y : ℝ} (hy : 0 < y) {a b : ℝ≥0} (hab : a ≤ b)
    (hfull : ∀ s, a ≤ s → s ≤ b → FullAt (v s) (μ s) (R s) y) (i : ι) (ha : μ a i ≤ y) :
    μ b i ≤ y := by
  by_contra hb
  push Not at hb
  set S := {s : ℝ≥0 | a ≤ s ∧ s ≤ b ∧ y < μ s i}
  have hSne : S.Nonempty := ⟨b, hab, le_rfl, hb⟩
  have hbdd : BddBelow S := OrderBot.bddBelow S
  set τ := sInf S
  have haτ : a ≤ τ := le_csInf hSne fun s hs => hs.1
  have hτb : τ ≤ b := csInf_le hbdd ⟨hab, le_rfl, hb⟩
  have hμτ : μ τ i ≤ y := by
    rcases haτ.lt_or_eq with hlt | heq
    · refine H.left_le hlt i fun s hs1 hs2 => ?_
      by_contra hc
      push Not at hc
      have : τ ≤ s := csInf_le hbdd ⟨hs1, hs2.le.trans hτb, hc⟩
      exact absurd hs2 (not_lt.2 this)
    · rw [← heq]; exact ha
  have hR := H.right_step hy (hfull τ haτ hτb)
  have hev : ∀ᶠ s in 𝓝[≥] τ, μ s i ≤ y := by
    filter_upwards [hR] with s hs
    by_contra hc
    push Not at hc
    have : i ∈ {i | y < μ s i} := hc
    rw [hs.2] at this
    exact absurd this (not_lt.2 hμτ)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.1 hev
  obtain ⟨s, hsS, hsu⟩ := exists_lt_of_csInf_lt hSne hu
  have hτs : τ ≤ s := csInf_le hbdd hsS
  exact absurd (hsub ⟨hτs, hsu⟩) (not_le.2 hsS.2.2)

end Hyp

#print axioms Hyp.no_entry
#print axioms Hyp.compact
#print axioms Hyp.mu_rcont
#print axioms Hyp.right_step
#print axioms Hyp.left_le

end QuantumNLS.SpectralFamilySteps
