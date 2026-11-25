/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams

Finite-leaf Banach-valued cycle Cauchy proofs are adapted from
https://github.com/bjbraams/lean-CA, commit333a684877588d3667c7a0d37e5074aaa2e5b7b7,
ComplexAnalysis/Cycle/Cauchy.lean:75-265. Actual finite C1-leaf induction replaces
the globally-C1 loop-generator premise; the checked arbitrary-endpoint leaf
kernel theorem is reused. The applicable license is listed in the third-party notices.

-/

import NlsGge.Atomic.Support.ContourChain
import NlsGge.Atomic.Support.ContourKernelParameter
import NlsGge.Atomic.Support.ContourCycleIndex
import Mathlib.Analysis.Complex.Liouville

/-! Actual finite-leaf Banach cycle Cauchy by Dixon's entire-function argument.
The index is the checked literal normalized scalar integral. Vanishing off the
open domain is an explicit analytical premise on the whole actual cycle.
No Jordan, orientation, index-one, nested realization or Riesz idempotence is asserted.
-/

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter ContinuousLinearMap
open scoped unitInterval Topology

namespace NlsGge.Atomic.ContourChain

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace Chain

/-- Kernel holomorphy follows from the actual C1 leaves and finite addition. -/
theorem differentiableOn_integral_kernel
    {a b : ℂ} (c : Chain a b)
    {U : Set ℂ} (hU : IsOpen U)
    {V : Set ℂ} (hcV : c.trace ⊆ V)
    {K : ℂ → ℂ → F}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (U ×ˢ V))
    (hd : ∀ w ∈ V, DifferentiableOn ℂ (fun z => K z w) U) :
    DifferentiableOn ℂ
      (fun z => c.integral (fun w => toSpanSingleton ℂ (K z w))) U := by
  induction c with
  | leaf γ hc =>
      exact ContourKernelParameter.differentiableOn_curveIntegral_kernel hU hc
        (fun t => hcV (mem_range_self t)) hK hd
  | join p q hp hq =>
      have him : p.trace ∪ q.trace ⊆ V := by
        rw [← trace_join]
        exact hcV
      exact (hp (fun z hz => him (Or.inl hz))).add
        (hq (fun z hz => him (Or.inr hz)))

end Chain

namespace Cycle

/-- Actual finite-family kernel integrals are holomorphic in their parameter. -/
theorem differentiableOn_integral_kernel
    (Γ : Cycle)
    {U : Set ℂ} (hU : IsOpen U)
    {V : Set ℂ} (hΓV : Γ.range ⊆ V)
    {K : ℂ → ℂ → F}
    (hK : ContinuousOn (fun p : ℂ × ℂ => K p.1 p.2) (U ×ˢ V))
    (hd : ∀ w ∈ V, DifferentiableOn ℂ (fun z => K z w) U) :
    DifferentiableOn ℂ
      (fun z => Γ.integral (fun w => toSpanSingleton ℂ (K z w))) U := by
  unfold Cycle.integral
  refine (DifferentiableOn.sum (u := Finset.univ) fun i _ =>
    Chain.differentiableOn_integral_kernel (Γ.chain i).2 hU
      (fun z hz => hΓV (mem_iUnion.mpr ⟨i, hz⟩)) hK hd).congr fun z _ => ?_
  simp [Finset.sum_apply]

/-- Off the cycle, the integral of the divided slope is the Cauchy integral minus the index
term. Only continuity of the function on a set containing the cycle is used. -/
theorem integral_dslope_eq_sub (Γ : Cycle) {U : Set ℂ} (hΓU : Γ.range ⊆ U)
    {f : ℂ → F} (hf : ContinuousOn f U) {z : ℂ} (hz : z ∉ Γ.range) :
    Γ.integral (fun w => toSpanSingleton ℂ (dslope f w z)) =
      Γ.integral (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) -
        (2 * (Real.pi : ℂ) * Complex.I * Γ.index z) • f z := by
  have hne : ∀ w ∈ Γ.range, w - z ≠ 0 := fun w hw h => hz (sub_eq_zero.mp h ▸ hw)
  have hker : ContinuousOn (fun w => (w - z)⁻¹) Γ.range :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  have hint₁ : Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn (hker.smul (hf.mono hΓU)) subset_rfl
  have hint₂ : Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn hker subset_rfl
  have hint₃ : Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f z)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn (hker.smul continuousOn_const) subset_rfl
  have hcongr : EqOn (fun w => toSpanSingleton ℂ (dslope f w z))
      ((fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) -
        fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f z)) Γ.range := by
    intro w hw
    have hwz : z ≠ w := fun h => hz (h ▸ hw)
    have key : dslope f w z = (w - z)⁻¹ • f w - (w - z)⁻¹ • f z := by
      rw [dslope_of_ne _ hwz, slope_def_module, ← neg_sub w z, inv_neg, neg_smul, smul_sub,
        neg_sub]
    refine ContinuousLinearMap.ext fun v => ?_
    simp [key, smul_sub]
  rw [Γ.integral_congr hcongr, Γ.integral_sub hint₁ hint₃, Γ.integral_smul_const (f z) hint₂,
    Γ.integral_sub_inv_eq_two_pi_I_mul_index]


set_option maxHeartbeats 800000 in
/-- **Dixon's lemma.** For a `C¹` cycle in an open set `U` whose index vanishes outside `U`,
and a Banach-valued function holomorphic on `U`, the integral over the cycle of the divided
slope at any point of `U` vanishes. -/
theorem integral_dslope_eq_zero (Γ : Cycle) {U : Set ℂ} (hU : IsOpen U) (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) :
    Γ.integral (fun w => toSpanSingleton ℂ (dslope f w z)) = 0 := by
  classical
  set h : ℂ → F := fun z => Γ.integral (fun w => toSpanSingleton ℂ (dslope f w z)) with hh_def
  set h₁ : ℂ → F := fun z => Γ.integral (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w))
    with hh₁_def
  have hh : DifferentiableOn ℂ h U := by
    refine Γ.differentiableOn_integral_kernel hU (V := U) hΓU
      (K := fun z w => dslope f w z) ?_ ?_
    · exact (ContourKernelParameter.continuousOn_dslope_prod_of_differentiableOn hU hf).comp
        (f := fun p : ℂ × ℂ => (p.2, p.1)) (by fun_prop) fun p hp => ⟨hp.2, hp.1⟩
    · intro w hw
      exact (Complex.differentiableOn_dslope (hU.mem_nhds hw)).mpr hf
  have hh₁ : DifferentiableOn ℂ h₁ Γ.rangeᶜ := by
    refine Γ.differentiableOn_integral_kernel Γ.isOpen_compl_range (V := Γ.range) subset_rfl
      (K := fun z w => (w - z)⁻¹ • f w) ?_ ?_
    · refine ContinuousOn.smul ?_ (hf.continuousOn.comp continuous_snd.continuousOn
        fun p hp => hΓU hp.2)
      refine ContinuousOn.inv₀ (continuous_snd.continuousOn.sub continuous_fst.continuousOn) ?_
      rintro ⟨z, w⟩ ⟨hz, hw⟩
      exact sub_ne_zero.mpr fun h => (hz : z ∉ Γ.range) (h ▸ hw)
    · intro w hw
      exact (((differentiableOn_const w).sub differentiableOn_id).inv
        fun z hz => sub_ne_zero.mpr fun h => (hz : z ∉ Γ.range)
          ((show w = z from h) ▸ hw)).smul_const (f w)
  have hint_h : ∀ z ∈ U,
      Γ.Integrable (fun w => toSpanSingleton ℂ (dslope f w z)) := by
    intro z hz
    refine Γ.integrable_toSpanSingleton_of_continuousOn ?_ hΓU
    exact (ContourKernelParameter.continuousOn_dslope_prod_of_differentiableOn hU hf).comp
      (f := fun w : ℂ => (w, z)) (continuous_id.continuousOn.prodMk continuousOn_const) (fun w hw => ⟨hw, hz⟩)
  have hint_h₁ : ∀ z ∉ Γ.range,
      Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) := by
    intro z hz
    refine Γ.integrable_toSpanSingleton_of_continuousOn ?_ subset_rfl
    exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz))).smul
      (hf.continuousOn.mono hΓU)
  have hagree : ∀ z, z ∉ Γ.range → Γ.index z = 0 → z ∈ U → h z = h₁ z := by
    intro z hzΓ hzi _
    simp only [hh_def, hh₁_def]
    rw [Γ.integral_dslope_eq_sub hΓU hf.continuousOn hzΓ, hzi, mul_zero, zero_smul,
      sub_zero]
  have hV : IsOpen {w | w ∉ Γ.range ∧ Γ.index w = 0} := Γ.isOpen_setOf_index_eq 0
  let H : ℂ → F := fun z => if z ∈ U then h z else h₁ z
  have hHU : ∀ z ∈ U, H z = h z := fun z hz => by simp [H, hz]
  have hHV : ∀ z, z ∉ Γ.range → Γ.index z = 0 → H z = h₁ z := by
    intro z hzΓ hzi
    by_cases hzU : z ∈ U
    · simp [H, hzU, hagree z hzΓ hzi hzU]
    · simp [H, hzU]
  have hHdiff : Differentiable ℂ H := by
    intro z₀
    by_cases hz₀ : z₀ ∈ U
    · have heq : H =ᶠ[𝓝 z₀] h := by
        filter_upwards [hU.mem_nhds hz₀] with z hz
        exact hHU z hz
      exact heq.differentiableAt_iff.mpr (hh.differentiableAt (hU.mem_nhds hz₀))
    · have hz₀Γ : z₀ ∉ Γ.range := fun hm => hz₀ (hΓU hm)
      have heq : H =ᶠ[𝓝 z₀] h₁ := by
        filter_upwards [hV.mem_nhds ⟨hz₀Γ, hind z₀ hz₀⟩] with z hzV
        exact hHV z hzV.1 hzV.2
      exact heq.differentiableAt_iff.mpr
        (hh₁.differentiableAt (Γ.isOpen_compl_range.mem_nhds hz₀Γ))
  obtain ⟨R, hR, hball, hRind⟩ := Γ.exists_pos_index_eq_zero_outside_ball 0
  obtain ⟨L, hL0, hL⟩ := Γ.exists_norm_integral_le (F := F)
  obtain ⟨M₀, hM₀⟩ := Γ.isCompact_range.exists_bound_of_continuousOn (hf.continuousOn.mono hΓU)
  set M := max M₀ 0 with hM_def
  have hM : ∀ w ∈ Γ.range, ‖f w‖ ≤ M := fun w hw => (hM₀ w hw).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hdecay : ∀ z : ℂ, R < ‖z‖ → ‖H z‖ ≤ L * (M / (‖z‖ - R)) := by
    intro z hzR
    have hzb : z ∉ ball 0 R := by simpa using hzR.le
    have hzΓ : z ∉ Γ.range := fun hm => hzb (hball hm)
    have hint := hint_h₁ z hzΓ
    rw [hHV z hzΓ (hRind z hzb)]
    refine hL _ _ fun w hw => ?_
    have hwR : ‖w‖ < R := by simpa using hball hw
    have hpos : 0 < ‖z‖ - R := by linarith
    have hwz : ‖z‖ - R ≤ ‖w - z‖ := by
      calc ‖z‖ - R ≤ ‖z‖ - ‖w‖ := by linarith
        _ ≤ ‖w - z‖ := by rw [norm_sub_rev]; exact norm_sub_norm_le z w
    rw [norm_smul, norm_inv, div_eq_inv_mul]
    exact mul_le_mul (inv_anti₀ hpos hwz) (hM w hw) (norm_nonneg _) (inv_nonneg.mpr hpos.le)
  have hbdd : Bornology.IsBounded (Set.range H) := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) (R + 1)).exists_bound_of_continuousOn
      hHdiff.continuous.continuousOn
    refine isBounded_iff_forall_norm_le.mpr ⟨max C (L * M), ?_⟩
    rintro _ ⟨z, rfl⟩
    by_cases hz : ‖z‖ ≤ R + 1
    · exact (hC z (by simpa using hz)).trans (le_max_left _ _)
    · have hz' := not_le.mp hz
      refine (hdecay z (by linarith)).trans (le_trans ?_ (le_max_right _ _))
      have h1 : 1 ≤ ‖z‖ - R := by linarith
      calc L * (M / (‖z‖ - R)) ≤ L * (M / 1) := by
            gcongr
        _ = L * M := by rw [div_one]
  have hconst : ∀ z w, H z = H w := fun z w => hHdiff.apply_eq_apply_of_bounded hbdd z w
  have hzero : ∀ z, H z = 0 := by
    intro z
    have hlim : Tendsto (fun t : ℝ => L * (M / (t - R))) atTop (𝓝 0) := by
      have ht : Tendsto (fun t : ℝ => t - R) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      have := (ht.inv_tendsto_atTop.const_mul M).const_mul L
      simpa [div_eq_mul_inv] using this
    have hle : ∀ᶠ t : ℝ in atTop, ‖H z‖ ≤ L * (M / (t - R)) := by
      filter_upwards [eventually_gt_atTop R] with t ht
      rw [hconst z (t : ℂ)]
      have hnorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hR.trans ht)]
      have := hdecay (t : ℂ) (by rwa [hnorm])
      rwa [hnorm] at this
    exact norm_le_zero_iff.mp (ge_of_tendsto hlim hle)
  have hint := hint_h z hz
  have := hzero z
  rwa [hHU z hz] at this


/-- **Cauchy's integral formula for cycles.** For a `C¹` cycle in an open set `U` whose index
vanishes outside `U`, and a Banach-valued function holomorphic on `U`, the Cauchy integral at a
point of `U` off the cycle is the index times the value. -/
theorem integral_sub_inv_smul_eq_index_smul (Γ : Cycle) {U : Set ℂ} (hU : IsOpen U) (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) {z : ℂ} (hz : z ∈ U) (hzΓ : z ∉ Γ.range) :
    Γ.integral (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) =
      (2 * (Real.pi : ℂ) * Complex.I * Γ.index z) • f z := by
  have hint : Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn
      (((continuousOn_id.sub continuousOn_const).inv₀
        (fun w hw => sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hzΓ))).smul
        (hf.continuousOn.mono hΓU)) subset_rfl
  have h := Γ.integral_dslope_eq_sub hΓU hf.continuousOn hzΓ
  rw [Γ.integral_dslope_eq_zero hU hΓU hind hf hz] at h
  exact (sub_eq_zero.mp h.symm)

/-- **Cauchy's theorem for cycles.** For a `C¹` cycle in an open set `U` whose index vanishes
outside `U`, the integral of every Banach-valued function holomorphic on `U` vanishes. -/
theorem integral_eq_zero (Γ : Cycle) {U : Set ℂ} (hU : IsOpen U) (hΓU : Γ.range ⊆ U) (hind : ∀ w, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) :
    Γ.integral (fun w => toSpanSingleton ℂ (f w)) = 0 := by
  have hint := Γ.integrable_toSpanSingleton_of_continuousOn hf.continuousOn hΓU
  rcases isEmpty_or_nonempty (Fin Γ.n) with hn | hne
  · simp [Cycle.integral]
  · obtain ⟨i⟩ := hne
    set z₀ := (Γ.chain i).1 with hz₀_def
    have hz₀ : z₀ ∈ U := by
      have := hΓU (Γ.chain_mem_range i 0)
      simpa only [Chain.path_source] using this
    have hg : DifferentiableOn ℂ (fun w => (w - z₀) • f w) U :=
      (differentiableOn_id.sub_const z₀).smul hf
    have key := Γ.integral_dslope_eq_zero hU hΓU hind hg hz₀
    rw [← key]
    refine Γ.integral_congr fun w hw => ?_
    congr 1
    by_cases hwz : w = z₀
    · rw [hwz, dslope_same]
      have hd := ((hasDerivAt_id z₀).sub_const z₀).smul
        (hf.differentiableAt (hU.mem_nhds hz₀)).hasDerivAt
      have hd' : HasDerivAt (fun w => (w - z₀) • f w)
          ((id z₀ - z₀) • deriv f z₀ + (1 : ℂ) • f z₀) z₀ := hd
      rw [hd'.deriv]
      simp
    · rw [dslope_of_ne _ (Ne.symm hwz), slope_def_module, sub_self, zero_smul, zero_sub,
        smul_neg, smul_smul]
      have hmul : (z₀ - w)⁻¹ * (w - z₀) = -1 := by
        rw [← neg_sub z₀ w, mul_neg, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hwz))]
      rw [hmul, neg_one_smul, neg_neg]


/-- The actual Cauchy formula together with actual recursive leaf integrability. -/
theorem integrable_and_integral_sub_inv_smul_eq_index_smul
    (Γ : Cycle) {U : Set ℂ} (hU : IsOpen U) (hΓU : Γ.range ⊆ U)
    (hind : ∀ w : ℂ, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U)
    {z : ℂ} (hz : z ∈ U) (hzΓ : z ∉ Γ.range) :
    Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) ∧
      Γ.integral (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) =
        (2 * (Real.pi : ℂ) * Complex.I * Γ.index z) • f z := by
  have hint : Γ.Integrable (fun w => toSpanSingleton ℂ ((w - z)⁻¹ • f w)) :=
    Γ.integrable_toSpanSingleton_of_continuousOn
      (((continuousOn_id.sub continuousOn_const).inv₀
        (fun w hw => sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hzΓ))).smul
        (hf.continuousOn.mono hΓU)) subset_rfl
  exact ⟨hint, Γ.integral_sub_inv_smul_eq_index_smul hU hΓU hind hf hz hzΓ⟩

/-- The actual Cauchy theorem together with actual recursive leaf integrability. -/
theorem integrable_and_integral_eq_zero
    (Γ : Cycle) {U : Set ℂ} (hU : IsOpen U) (hΓU : Γ.range ⊆ U)
    (hind : ∀ w : ℂ, w ∉ U → Γ.index w = 0)
    {f : ℂ → F} (hf : DifferentiableOn ℂ f U) :
    Γ.Integrable (fun w => toSpanSingleton ℂ (f w)) ∧
      Γ.integral (fun w => toSpanSingleton ℂ (f w)) = 0 := by
  have hint := Γ.integrable_toSpanSingleton_of_continuousOn hf.continuousOn hΓU
  exact ⟨hint, Γ.integral_eq_zero hU hΓU hind hf⟩

end Cycle
end NlsGge.Atomic.ContourChain
