import QuantumNLS.Prop010RectangleDifferentialR17

/-!
# R-52CF5DA1 stage 1: the fixed-rectangle action differential on a full open neighborhood

`prop:audit-finite-count-propagation` (GAUGE_RETARGETING.tex:101), proof paragraph "Use the resulting joint
quantum spectral projection ... a fixed open neighborhood of `u_*` gives ... fixed cutoff neighborhoods, and a
positive contour lower bound on `|D_v|` for every unit `v` in that neighborhood", and the identity of
`lem:audit-scalar-period` (R-620D5517, accepted) used at the nearby centers.

For a rough center `u` and a label `n`, the rectangle `Γ_n = ∂([b_{n-1}(u), b_n(u)] × [-h,h])` is FIXED (it is
the rectangle of the accepted PROP-010).  We prove that there is ONE open set `W ∋ u` such that at EVERY
`v ∈ W` (not only at the center):
* every point of `Γ_n` is regular for `v`;
* the transported Cauchy period identity `∮_{Γ_n} G_v = 2πi I_n(v)` holds;
* the full real differential is `dI_n(v)[k] = -(2πκ)⁻¹ Re ∮_{Γ_n} ∂_v s(z;v)[k] / D_v(z) dz`, with
  `D_v = Df L κ G_v` the denominator of `v` itself.

The proof is the accepted PROP-010 argument (`Prop010RectangleDifferentialR17`) relocated to the points of a
fixed open set: the analytic germ of `v ↦ G_v|_{Γ_n}` is produced at every point of `W` by the accepted
`RootScalarDifferentialR10.exists_analytic_regular_path`, whose hypotheses hold on the open set
`W = {v | the gap / mass / regularity / period conditions hold near v}`.
No hypothesis is added; all inherited modules are read-only.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped BigOperators

namespace QuantumNLS.R52CFDeriv

open Prop010RectangleTransportR17 Prop010RectangleDifferentialR17 PeriodReconstruction
open PhysicalTensor (L2T)
open RootCauchyFullBracketR8 (G)
open RootCauchyJointR9 (Regular)
open RootMassInvolutionR8 (mass)
open RootScalarPeriodR8 (cut)
open LabelExactPeriod (rectIntegral)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The conditions at one input `v` for the fixed rectangle of the center `u`. -/
def Good (hκ : 0 < κ) (u : L2T L) (n : ℤ) (h δ M : ℝ) (v : L2T L) : Prop :=
  (∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ v),
      δ ≤ |q - cut hκ u (n-1)| ∧ δ ≤ |q - cut hκ u n|) ∧
    (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ M ∧
    (∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h, Regular κ (v, z)) ∧
    rectIntegral (fun z => G hκ z v) (cut hκ u (n-1)) (cut hκ u n) h =
      (2 * (Real.pi : ℂ) * I) * (mass hκ n v : ℂ)

theorem cut_lt (hκ : 0 < κ) (u : L2T L) (n : ℤ) : cut hκ u (n-1) < cut hκ u n :=
  (DEF014Phase.facts ((⟨κ, hκ⟩, u) : DEF014Phase.Param L)).phase.separator_strictMono (by omega)

theorem eventually_good (hκ : 0 < κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0 < h) :
    ∃ δ > 0, ∀ᶠ v : L2T L in 𝓝 u, Good hκ u n h δ ((‖u‖ + 1) ^ 2) v := by
  obtain ⟨δ, hδ, hg⟩ := endpoint_gaps hκ u n
  refine ⟨δ, hδ, ?_⟩
  have hm : ∀ᶠ v : L2T L in 𝓝 u,
      (PhysicalQuantumMeasure.measure hκ v univ).toReal ≤ (‖u‖ + 1) ^ 2 := by
    have hn : ∀ᶠ v : L2T L in 𝓝 u, ‖v‖ < ‖u‖ + 1 :=
      continuous_norm.continuousAt.eventually (gt_mem_nhds (by linarith))
    filter_upwards [hn] with v hv
    rw [PhysicalQuantumMeasure.measure_univ, ENNReal.toReal_ofReal (sq_nonneg _)]
    nlinarith [norm_nonneg v, norm_nonneg u]
  have hr : ∀ᶠ v : L2T L in 𝓝 u, ∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h, Regular κ (v, z) := by
    apply (isCompact_Gam _ _ _).eventually_forall_of_forall_eventually
    intro z hz
    exact (RootCauchyJointR9.isOpen_regular κ).mem_nhds
      (Prop010CutoffExistenceR11.rectangle_regular L hκ u n hh hz)
  filter_upwards [hg, hm, hr, eventually_rectangle_period hκ u n hh] with v h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The analytic germ of `v ↦ G_v|_{Γ_n}` at every point where the conditions hold nearby. -/
theorem analytic_path_at (hκ : 0 < κ) (u : L2T L) (n : ℤ) {h δ M : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hM : 0 ≤ M) (v : L2T L) (hv : ∀ᶠ w : L2T L in 𝓝 v, Good hκ u n h δ M w) :
    ∃ H : L2T L → C(Boundary (cut hκ u (n-1)) (cut hκ u n) h, ℂ),
      AnalyticAt ℝ H v ∧ ∀ᶠ w : L2T L in 𝓝 v, ∀ z, H w z = G hκ z.1 w := by
  let a := cut hκ u (n-1)
  let b := cut hκ u n
  let Z : C(Boundary a b h, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩
  have hZ : LipschitzWith 1 Z := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simp only [NNReal.coe_one, one_mul]
    exact le_rfl
  have hgap : ∀ᶠ w : L2T L in 𝓝 v,
      ∀ᵐ q : ℝ ∂(PhysicalQuantumMeasure.measure hκ w), ∀ z : Boundary a b h, min δ h ≤ ‖Z z - (q : ℂ)‖ := by
    filter_upwards [hv] with w hw
    filter_upwards [hw.1] with q hq z
    exact Gam_dist hh hq.1 hq.2 z.2
  have hm : ∀ᶠ w : L2T L in 𝓝 v, (PhysicalQuantumMeasure.measure hκ w univ).toReal ≤ M := by
    filter_upwards [hv] with w hw
    exact hw.2.1
  have hr : ∀ᶠ w : L2T L in 𝓝 v, ∀ z : Boundary a b h, Regular κ (w, Z z) := by
    filter_upwards [hv] with w hw z
    exact hw.2.2.1 z.1 z.2
  exact RootScalarDifferentialR10.exists_analytic_regular_path hκ Z hZ v
    (lt_min hδ hh) hM hgap hm hr

/-- Differentiation of the transported period at a point `v` near which the conditions hold. -/
theorem mass_differential_at (hκ : 0 < κ) (u : L2T L) (n : ℤ) {h δ M : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hM : 0 ≤ M) (v : L2T L) (hv : ∀ᶠ w : L2T L in 𝓝 v, Good hκ u n h δ M w) (k : L2T L) :
    (fderiv ℝ (mass hκ n) v k : ℂ) = (2 * (Real.pi : ℂ) * I)⁻¹ *
      rectIntegral (fun z => fderiv ℝ (G hκ z) v k) (cut hκ u (n-1)) (cut hκ u n) h := by
  obtain ⟨H, hH, hHe⟩ := analytic_path_at hκ u n hh hδ hM v hv
  have hab : cut hκ u (n-1) ≤ cut hκ u n := (cut_lt hκ u n).le
  let T := boundaryIntegral hab hh.le
  let J : L2T L → ℂ := fun w => T (H w)
  have hJ := T.hasFDerivAt.comp v hH.differentiableAt.hasFDerivAt
  change HasFDerivAt J _ v at hJ
  have hDH : ∀ z : Boundary (cut hκ u (n-1)) (cut hκ u n) h,
      (fderiv ℝ H v k) z = fderiv ℝ (G hκ z.1) v k := by
    intro z
    have hd := (ContinuousMap.evalCLM ℝ z).hasFDerivAt.comp v hH.differentiableAt.hasFDerivAt
    have heq : (fun w => H w z) =ᶠ[𝓝 v] G hκ z.1 := hHe.mono fun w hw => hw z
    have hhd := (hd.congr_of_eventuallyEq heq.symm).fderiv
    simpa using (congrArg (fun A : L2T L →L[ℝ] ℂ => A k) hhd).symm
  have heq : J =ᶠ[𝓝 v] fun w => rectIntegral (fun z => G hκ z w)
      (cut hκ u (n-1)) (cut hκ u n) h := by
    filter_upwards [hHe] with w hw
    exact boundaryIntegral_eq hab hh.le _ _ hw
  have hmass : (fun w => (mass hκ n w : ℂ)) =ᶠ[𝓝 v]
      fun w => (2 * (Real.pi : ℂ) * I)⁻¹ * J w := by
    filter_upwards [heq, hv] with w hw hp
    rw [hw, hp.2.2.2]
    field_simp
  have hdM := Complex.ofRealCLM.hasFDerivAt.comp v
    (DEF014MassAnalytic.analyticAt_physical_coordinate hκ n v).differentiableAt.hasFDerivAt
  have hhM := (hdM.congr_of_eventuallyEq hmass.symm).fderiv
  have he := congrArg (fun A : L2T L →L[ℝ] ℂ => A k)
    (hhM.symm.trans (hJ.const_mul (2 * (Real.pi : ℂ) * I)⁻¹).fderiv)
  change (fderiv ℝ (mass hκ n) v k : ℂ) = (2 * (Real.pi : ℂ) * I)⁻¹ * (T (fderiv ℝ H v k)) at he
  rw [boundaryIntegral_eq hab hh.le _ (fun z => fderiv ℝ (G hκ z) v k) hDH] at he
  exact he

/-- The action differential with the denominator of `v` itself, on the fixed rectangle of `u`. -/
theorem action_differential_at (hκ : 0 < κ) (u : L2T L) (n : ℤ) {h δ M : ℝ} (hh : 0 < h) (hδ : 0 < δ)
    (hM : 0 ≤ M) (v : L2T L) (hv : ∀ᶠ w : L2T L in 𝓝 v, Good hκ u n h δ M w) (k : L2T L) :
    fderiv ℝ (mass hκ n) v k = -(2 * Real.pi * κ)⁻¹ *
      (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k /
        PeriodReconstructionCore.Df L κ (fun z => G hκ z v) z)
        (cut hκ u (n-1)) (cut hκ u n) h).re := by
  let J := rectIntegral (fun z => fderiv ℝ (G hκ z) v k) (cut hκ u (n-1)) (cut hκ u n) h
  have hm := mass_differential_at hκ u n hh hδ hM v hv k
  have hj : J = (2 * (Real.pi : ℂ) * I) * (fderiv ℝ (mass hκ n) v k : ℂ) := by
    change (fderiv ℝ (mass hκ n) v k : ℂ) = (2 * (Real.pi : ℂ) * I)⁻¹ * J at hm
    rw [hm]; field_simp
  have hreg := hv.self_of_nhds.2.2.1
  have hp (z : ℂ) (hz : z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h) :
      fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k /
        PeriodReconstructionCore.Df L κ (fun z => G hκ z v) z =
        (I * (κ : ℂ)) * fderiv ℝ (G hκ z) v k := by
    have he := Prop010ClassicalR10.exponent_differential hκ v k z (hreg z hz)
    simpa only [PeriodReconstructionCore.Df, PeriodReconstructionCore.Af,
      ScalarLogBranchR10.difference, RootScalarPeriodR10.exponent,
      ← Prop010CutoffExistenceR11.ef_exp] using he.symm
  have hab : cut hκ u (n-1) ≤ cut hκ u n := (cut_lt hκ u n).le
  have he : rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k /
      PeriodReconstructionCore.Df L κ (fun z => G hκ z v) z) (cut hκ u (n-1)) (cut hκ u n) h =
      rectIntegral (fun z => (I * (κ : ℂ)) * fderiv ℝ (G hκ z) v k)
        (cut hκ u (n-1)) (cut hκ u n) h := by
    apply LabelExactPeriod.rectIntegral_congr
    · exact fun x hx => hp _ (PeriodTwoTerm.bot_mem hab hx)
    · exact fun x hx => hp _ (PeriodTwoTerm.top_mem hab hx)
    · exact fun y hy => hp _ (PeriodTwoTerm.right_mem hh.le hy)
    · exact fun y hy => hp _ (PeriodTwoTerm.left_mem hh.le hy)
  rw [he, PeriodTwoTerm.rectIntegral_const_mul]
  change _ = -(2 * Real.pi * κ)⁻¹ * ((I * (κ : ℂ)) * J).re
  rw [hj]
  simp only [mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im]
  norm_num
  field_simp

/-- **Stage 1 headline.**  One open neighborhood `W` of the center `u` on which, at every point `v`, the fixed
rectangle of `u` is regular, carries the transported period, and gives the full differential of `I_n` with the
denominator `D_v`. -/
theorem fixed_rectangle_neighborhood (hκ : 0 < κ) (u : L2T L) (n : ℤ) {h : ℝ} (hh : 0 < h) :
    ∃ W : Set (L2T L), IsOpen W ∧ u ∈ W ∧ ∀ v ∈ W,
      (∀ z ∈ Gam (cut hκ u (n-1)) (cut hκ u n) h, Regular κ (v, z)) ∧
      rectIntegral (fun z => G hκ z v) (cut hκ u (n-1)) (cut hκ u n) h =
        (2 * (Real.pi : ℂ) * I) * (mass hκ n v : ℂ) ∧
      ∀ k : L2T L, fderiv ℝ (mass hκ n) v k = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) v k /
          PeriodReconstructionCore.Df L κ (fun z => G hκ z v) z)
          (cut hκ u (n-1)) (cut hκ u n) h).re := by
  obtain ⟨δ, hδ, hg⟩ := eventually_good hκ u n hh
  refine ⟨{v | ∀ᶠ w : L2T L in 𝓝 v, Good hκ u n h δ ((‖u‖ + 1) ^ 2) w}, isOpen_setOf_eventually_nhds,
    hg, ?_⟩
  intro v hv
  exact ⟨hv.self_of_nhds.2.2.1, hv.self_of_nhds.2.2.2,
    action_differential_at hκ u n hh hδ (sq_nonneg _) v hv⟩

end QuantumNLS.R52CFDeriv

#print axioms QuantumNLS.R52CFDeriv.fixed_rectangle_neighborhood
