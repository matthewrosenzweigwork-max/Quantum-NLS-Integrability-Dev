import Mathlib
import QuantumNLS.Prop009ProbeDev
import QuantumNLS.PeriodTwoTerm
import QuantumNLS.MPFixedContour

/-!
# PROP-009 `lem:B4-finite-probes` (`spectral_calculus.tex:141-154`), the branch clause

The printed lemma also asserts that, for a configuration obeying the finitely many probe bounds, "all roots have a common positive distance from a fixed
neighborhood of `Γ`, and the local branches used in `thm:B3-period-reconstruction` are well defined there ... The branch neighborhoods may be prescribed
sufficiently small before selecting these probes."  `Prop009FiniteProbes.finite_probes` (a9d14725) proves the block identification, the root distance from `Γ`
and the `O(N^-2)` remainder; this NEW module adds the branch clause, with everything combined in one probe set (frozen modules are not edited).

* `nb Γ r = {z | ∃ w ∈ Γ, ‖z − w‖ ≤ r}` is the closed `r`-neighbourhood of the fixed contour `Γ = Gam xm xp h` (compact).
* `nbhd_background` (sequence-free): the background `A, A⁻¹, e, D` keeps its bounds (`2M`, `η/2`) on a neighbourhood of `Γ`, with `G` differentiable there.
* `branch_regular` (pointwise): from the five numerical conditions of `PeriodTwoTerm.eventual_props` at a point `w` (roots `2|c|` away, `‖W‖ ≤ 1/2`,
  `‖a_N‖ ≥ 1/(2M)`, `‖D_N‖ ≥ 3η/4`, `‖a_N − A‖ ≤ 1/(2M)`) it follows that `1+W`, `a_N/A` and every `1 + ic/(w − q_j)` lie in the slit plane (so the Taylor
  square-root and principal logarithm branches are defined) and that `a_N`, `log a_N` and `ℓ_N` are analytic at `w`.
* `branch_eventually`: along any weakly convergent sequence with `N → ∞` these hold eventually, uniformly on `nb Γ r`.
* **`finite_probes_branch`**: constants `M, η, δ` and a radius `r0` (all fixed before the probes); for every `0 < r ≤ r0` finitely many high probes,
  `ε`, `N₀`, `C` such that every on-shell configuration obeying the probe bounds has the exact block, the `C N^{-2}` remainder on `Γ`, and `BranchGood` (the
  conditions above, with the constants `2M`, `η/2`) at every point of `nb Γ r`.
Routing: `Prop009ProbeDev.probes_generic` (Cauchy-limit criterion, no EXT-025 contract) + `PeriodTwoTerm.eventual_props` + accepted PROP-004/006 outputs.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Set Filter Topology Complex Metric
open scoped ENNReal

namespace QuantumNLS.Prop009Branch

open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodReconstructionBigO QuantumNLS.PeriodReconstruction
open QuantumNLS.LabelJointLimit QuantumNLS.LabelJointWeak QuantumNLS.LabelBlock
open QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts
open QuantumNLS.RootMeasureComplex (HighHalf)
open QuantumNLS.PeriodTwoTerm (eventual_props)
open QuantumNLS.Prop009ProbeDev (probes_generic gam_supp_dist)
open QuantumNLS.MPFixedContour (gam_background)
open QuantumNLS.EmpiricalRapidity (cauchyTransform)

/-! ### 1. The closed neighbourhood of a compact contour -/

/-- The closed `r`-neighbourhood of `Γ`. -/
def nb (Γ : Set ℂ) (r : ℝ) : Set ℂ := {z | ∃ w ∈ Γ, ‖z - w‖ ≤ r}

theorem isCompact_nb {Γ : Set ℂ} (hΓ : IsCompact Γ) (r : ℝ) : IsCompact (nb Γ r) := by
  have : nb Γ r = (fun p : ℂ × ℂ => p.1 + p.2) '' (Γ ×ˢ closedBall (0 : ℂ) r) := by
    ext z
    constructor
    · rintro ⟨w, hw, hz⟩
      exact ⟨(w, z - w), ⟨hw, by simpa using hz⟩, by simp⟩
    · rintro ⟨⟨w, y⟩, ⟨hw, hy⟩, rfl⟩
      exact ⟨w, hw, by simpa using hy⟩
  rw [this]
  exact (hΓ.prod (isCompact_closedBall 0 r)).image continuous_add

theorem nb_subset_cthickening {Γ : Set ℂ} {r : ℝ} : nb Γ r ⊆ cthickening r Γ := by
  rintro z ⟨w, hw, hz⟩
  exact Metric.mem_cthickening_of_dist_le z w r Γ hw (by rwa [dist_eq_norm])

theorem nb_mono {Γ : Set ℂ} {r r' : ℝ} (h : r ≤ r') : nb Γ r ⊆ nb Γ r' :=
  fun z ⟨w, hw, hz⟩ => ⟨w, hw, hz.trans h⟩

/-! ### 2. The background on a neighbourhood -/

theorem nbhd_background {L κ : ℝ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {Γ : Set ℂ} (hΓ : IsCompact Γ)
    {d0 η M : ℝ} (hd0 : 0 < d0) (hM : 1 ≤ M)
    (hsupp : ∀ z ∈ Γ, ∀ t ∈ μ.support, d0 ≤ ‖z - t‖)
    (hb : ∀ z ∈ Γ, η ≤ ‖Df L κ (cauchyTransform μ) z‖ ∧ ‖Af κ (cauchyTransform μ) z‖ ≤ M ∧
      ‖(Af κ (cauchyTransform μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M) (hη : 0 < η) :
    ∃ r0 > 0, ∀ z ∈ nb Γ r0, (∀ t ∈ μ.support, d0 / 2 ≤ ‖z - t‖) ∧
      (∀ᶠ w in 𝓝 z, η / 2 ≤ ‖Df L κ (cauchyTransform μ) w‖) ∧ ‖Af κ (cauchyTransform μ) z‖ ≤ 2 * M ∧
      ‖(Af κ (cauchyTransform μ) z)⁻¹‖ ≤ 2 * M ∧ ‖ef L z‖ ≤ 2 * M := by
  set G := cauchyTransform μ with hG
  let Pp : ℂ → Prop := fun z => (∀ t ∈ μ.support, d0 / 2 ≤ ‖z - t‖) ∧ η / 2 < ‖Df L κ G z‖ ∧
    ‖Af κ G z‖ < 2 * M ∧ ‖(Af κ G z)⁻¹‖ < 2 * M ∧ ‖ef L z‖ < 2 * M
  have hev : ∀ z0 ∈ Γ, ∀ᶠ z in 𝓝 z0, Pp z := by
    intro z0 hz0
    obtain ⟨hD0, hA0', hAi0, he0⟩ := hb z0 hz0
    have hGd : DifferentiableAt ℂ G z0 := differentiableAt_cauchy μ hd0 (hsupp z0 hz0)
    have hGc : ContinuousAt G z0 := hGd.continuousAt
    have hAc : ContinuousAt (Af κ G) z0 := (hGc.const_mul (I * κ)).cexp
    have hec : ContinuousAt (ef L) z0 := (hasDerivAt_ef L z0).continuousAt
    have hAne : Af κ G z0 ≠ 0 := exp_ne_zero _
    have hDc : ContinuousAt (Df L κ G) z0 := hAc.sub (hec.div hAc hAne)
    have hAic : ContinuousAt (fun z => (Af κ G z)⁻¹) z0 := hAc.inv₀ hAne
    have hM0 : 0 < M := by linarith
    filter_upwards [Metric.ball_mem_nhds z0 (show 0 < d0 / 2 by positivity),
      hDc.norm.eventually (lt_mem_nhds (show η / 2 < ‖Df L κ G z0‖ by linarith)),
      hAc.norm.eventually (gt_mem_nhds (show ‖Af κ G z0‖ < 2 * M by linarith)),
      hAic.norm.eventually (gt_mem_nhds (show ‖(Af κ G z0)⁻¹‖ < 2 * M by linarith)),
      hec.norm.eventually (gt_mem_nhds (show ‖ef L z0‖ < 2 * M by linarith))]
      with z hz h1 h2 h3 h4
    refine ⟨fun t ht => ?_, h1, h2, h3, h4⟩
    have hz' : ‖z - z0‖ < d0 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have := hsupp z0 hz0 t ht
    have h5 := norm_sub_norm_le (z0 - t) (z0 - z)
    rw [sub_sub_sub_cancel_left, norm_sub_rev z0 z] at h5
    linarith
  have hsub : Γ ⊆ interior {z | Pp z} := fun z0 hz0 => mem_interior_iff_mem_nhds.2 (hev z0 hz0)
  obtain ⟨δ, hδ, hcth⟩ := hΓ.exists_cthickening_subset_open isOpen_interior hsub
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hzi : z ∈ interior {z | Pp z} := hcth (nb_subset_cthickening hz)
  have hnh : {z | Pp z} ∈ 𝓝 z := mem_interior_iff_mem_nhds.1 hzi
  have hP := mem_of_mem_nhds hnh
  refine ⟨hP.1, ?_, hP.2.2.1.le, hP.2.2.2.1.le, hP.2.2.2.2.le⟩
  filter_upwards [hnh] with w hw using hw.2.1.le

/-! ### 3. Branch regularity at a point -/

/-- The branch conditions at a point. -/
def BranchGood (L κ c M η : ℝ) (G : ℂ → ℂ) {N : ℕ} (q : Fin N → ℝ) (w : ℂ) : Prop :=
  (∀ j, 2 * |c| < ‖w - q j‖) ∧ ‖Wf L κ c G q w‖ ≤ 1 / 2 ∧ 1 / (2 * M) ≤ ‖aNf L κ c G q w‖ ∧
    3 * η / 4 ≤ ‖DNf L κ c G q w‖ ∧ ‖aNf L κ c G q w - Af κ G w‖ ≤ 1 / (2 * M) ∧
    1 + Wf L κ c G q w ∈ slitPlane ∧ aNf L κ c G q w / Af κ G w ∈ slitPlane ∧
    (∀ j, 1 + I * c / (w - q j) ∈ slitPlane) ∧
    AnalyticAt ℂ (aNf L κ c G q) w ∧ AnalyticAt ℂ (logaNf L κ c G q) w ∧ AnalyticAt ℂ (ellf c q) w

theorem branch_regular {L κ c : ℝ} (μ : Measure ℝ) [IsProbabilityMeasure μ] {N : ℕ}
    {q : Fin N → ℝ} {z : ℂ} {d0 M η : ℝ} (hd0 : 0 < d0) (hM : 0 < M) (hη : 0 < η)
    (hS : ∀ t ∈ μ.support, d0 ≤ ‖z - t‖) (hR : ∀ j, 2 * |c| < ‖z - q j‖)
    (hDz : Df L κ (cauchyTransform μ) z ≠ 0)
    (hW : ‖Wf L κ c (cauchyTransform μ) q z‖ ≤ 1 / 2)
    (ha : 1 / (2 * M) ≤ ‖aNf L κ c (cauchyTransform μ) q z‖)
    (hDN : 3 * η / 4 ≤ ‖DNf L κ c (cauchyTransform μ) q z‖)
    (haA : ‖aNf L κ c (cauchyTransform μ) q z - Af κ (cauchyTransform μ) z‖ ≤ 1 / (2 * M))
    (hAi : ‖(Af κ (cauchyTransform μ) z)⁻¹‖ ≤ M) :
    BranchGood L κ c M η (cauchyTransform μ) q z := by
  set G := cauchyTransform μ
  have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ G w := by
    filter_upwards [Metric.ball_mem_nhds z (show 0 < d0 / 2 by positivity)] with w hw
    refine differentiableAt_cauchy μ (show 0 < d0 / 2 by positivity) fun t ht => ?_
    have h1 := hS t ht
    have h2 : ‖w - z‖ < d0 / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
    have := norm_sub_norm_le (z - t) (z - w)
    rw [sub_sub_sub_cancel_left, norm_sub_rev z w] at this
    linarith
  have hGc : ContinuousAt G z := hGnear.self_of_nhds.continuousAt
  have hAc : ContinuousAt (Af κ G) z := (hGc.const_mul (I * κ)).cexp
  have hec : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
  have hA0 : Af κ G z ≠ 0 := exp_ne_zero _
  have hsc : ContinuousAt (sf L κ G) z := hAc.add (hec.div hAc hA0)
  have hDc : ContinuousAt (Df L κ G) z := hAc.sub (hec.div hAc hA0)
  have hsNc : ContinuousAt (sNf L c q) z := (hasDerivAt_sN L hR).continuousAt
  have hWc : ContinuousAt (Wf L κ c G q) z :=
    ((hsNc.pow 2).sub (hsc.pow 2)).div (hDc.pow 2) (pow_ne_zero 2 hDz)
  have hslitW : 1 + Wf L κ c G q z ∈ slitPlane := by
    refine Or.inl ?_
    have := Complex.abs_re_le_norm (Wf L κ c G q z)
    simp only [add_re, one_re]
    linarith [neg_abs_le (Wf L κ c G q z).re]
  have hWnear : ∀ᶠ w in 𝓝 z, 1 + Wf L κ c G q w ∈ slitPlane := by
    filter_upwards [hWc.norm.eventually (gt_mem_nhds (show ‖Wf L κ c G q z‖ < 1 by linarith))]
      with w hw
    refine Or.inl ?_
    have := Complex.abs_re_le_norm (Wf L κ c G q w)
    simp only [add_re, one_re]
    linarith [neg_abs_le (Wf L κ c G q w).re]
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (aNf L κ c G q) w := by
    filter_upwards [hGnear, hDc.eventually_ne hDz, ev_dist hR, hWnear] with w h1 h2 h3 h4
    exact differentiableAt_aN L κ c h1 h2 h3 h4
  obtain ⟨s, hs, hsd⟩ := hdiff.exists_mem
  have han : AnalyticAt ℂ (aNf L κ c G q) z :=
    DifferentiableOn.analyticAt (fun w hw => (hsd w hw).differentiableWithinAt) hs
  obtain ⟨s2, hs2, hsd2⟩ := hGnear.exists_mem
  have hGan : AnalyticAt ℂ G z :=
    DifferentiableOn.analyticAt (fun w hw => (hsd2 w hw).differentiableWithinAt) hs2
  have hAan : AnalyticAt ℂ (Af κ G) z := ((analyticAt_const (𝕜 := ℂ) (v := I * (κ : ℂ))).mul hGan).cexp
  have ha0 : aNf L κ c G q z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at ha; linarith [show 0 < 1 / (2 * M) by positivity]
  have hslit : aNf L κ c G q z / Af κ G z ∈ slitPlane := by
    refine Or.inl ?_
    have e : aNf L κ c G q z / Af κ G z - 1 = (aNf L κ c G q z - Af κ G z) * (Af κ G z)⁻¹ := by
      field_simp
    have hb : ‖aNf L κ c G q z / Af κ G z - 1‖ ≤ 1 / 2 := by
      rw [e, norm_mul]
      calc _ ≤ 1 / (2 * M) * M := mul_le_mul haA hAi (norm_nonneg _) (by positivity)
        _ = 1 / 2 := by field_simp
    have := Complex.abs_re_le_norm (aNf L κ c G q z / Af κ G z - 1)
    have e2 : (aNf L κ c G q z / Af κ G z).re = 1 + (aNf L κ c G q z / Af κ G z - 1).re := by
      simp
    rw [e2]
    linarith [neg_abs_le (aNf L κ c G q z / Af κ G z - 1).re]
  have hterm : ∀ j, 1 + I * c / (z - q j) ∈ slitPlane := by
    intro j
    refine Or.inl ?_
    have hw : z - q j ≠ 0 := by
      intro h0; have := hR j; rw [h0, norm_zero] at this; linarith [abs_nonneg c]
    have hnw : 0 < ‖z - q j‖ := norm_pos_iff.2 hw
    have hu : ‖I * c / (z - q j)‖ < 1 / 2 := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        div_lt_iff₀ hnw]; linarith [hR j]
    have := Complex.abs_re_le_norm (I * c / (z - q j))
    simp only [add_re, one_re]
    linarith [neg_abs_le (I * c / (z - q j)).re]
  have hell : AnalyticAt ℂ (ellf c q) z := by
    have : ellf c q = fun w => ∑ j, log (1 + I * c / (w - q j)) := rfl
    rw [this]
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) (f := fun (j : Fin N) (w : ℂ) => log (1 + I * c / (w - q j))) (c := z)
      Finset.univ (fun j _ => ?_)
    have hw : z - q j ≠ 0 := by
      intro h0; have := hR j; rw [h0, norm_zero] at this; linarith [abs_nonneg c]
    exact ((analyticAt_const (𝕜 := ℂ) (v := (1 : ℂ))).add ((analyticAt_const (𝕜 := ℂ) (v := I * (c : ℂ))).div
      ((analyticAt_id (𝕜 := ℂ)).sub (analyticAt_const (𝕜 := ℂ) (v := ((q j : ℝ) : ℂ)))) hw)).clog (hterm j)
  have hlog : AnalyticAt ℂ (logaNf L κ c G q) z := by
    have : logaNf L κ c G q = fun w => I * κ * G w + log (aNf L κ c G q w / Af κ G w) := rfl
    rw [this]
    exact ((analyticAt_const (𝕜 := ℂ) (v := I * (κ : ℂ))).mul hGan).add ((han.div hAan hA0).clog hslit)
  exact ⟨hR, hW, ha, hDN, haA, hslitW, hslit, hterm, han, hlog, hell⟩

/-! ### 4. Eventual branch conditions along a weakly convergent sequence -/

theorem branch_eventually {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) = S.μ) {N : ℕ → ℕ} {hN : ∀ k, 0 < N k} {B : ∀ k, OnShellBethe L κ (N k)}
    (hconv : Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ)) (hNtop : Tendsto N atTop atTop)
    {xm xp h δ r d0 η M r0 : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hd0 : 0 < d0) (hη : 0 < η) (hM : 1 ≤ M)
    (hr : 0 < r) (hr0 : r ≤ r0) (hrδ : r ≤ min δ h / 2)
    (hsupp : ∀ z ∈ Gam xm xp h, ∀ t ∈ S.μ.support, d0 ≤ ‖z - t‖)
    (hroot : ∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h, ∀ j, min δ h ≤ ‖z - (B k).q j‖)
    (hbg : ∀ z ∈ nb (Gam xm xp h) r0, (∀ t ∈ S.μ.support, d0 / 2 ≤ ‖z - t‖) ∧
      (∀ᶠ w in 𝓝 z, η / 2 ≤ ‖Df L κ (cauchyTransform S.μ) w‖) ∧
      ‖Af κ (cauchyTransform S.μ) z‖ ≤ 2 * M ∧ ‖(Af κ (cauchyTransform S.μ) z)⁻¹‖ ≤ 2 * M ∧ ‖ef L z‖ ≤ 2 * M) :
    ∀ᶠ k in atTop, ∀ w ∈ nb (Gam xm xp h) r,
      BranchGood L κ (κ / N k) (2 * M) (η / 2) (cauchyTransform S.μ) (B k).q w := by
  have hL := S.hL
  have hκ := S.hκ
  haveI : IsProbabilityMeasure S.μ := S.isProb
  set G := cauchyTransform S.μ with hG
  set Γ := Gam xm xp h with hΓ
  set K := nb Γ r with hK
  have hKc : IsCompact K := isCompact_nb (isCompact_Gam xm xp h) r
  have hKb : ∀ z ∈ K, z ∈ nb Γ r0 := fun z hz => nb_mono hr0 hz
  have hmh : 0 < min δ h / 2 := by positivity
  have hrootK : ∀ᶠ k in atTop, ∀ z ∈ K, ∀ j, min δ h / 2 ≤ ‖z - (B k).q j‖ := by
    filter_upwards [hroot] with k hk z ⟨w, hw, hzw⟩ j
    have h1 := hk w hw j
    have h2 := norm_sub_norm_le (w - (B k).q j) (w - z)
    rw [sub_sub_sub_cancel_left, norm_sub_rev w z] at h2
    linarith
  have hsuppK : ∀ z ∈ K, ∀ t ∈ S.μ.support, d0 / 2 ≤ ‖z - t‖ := fun z hz t ht => (hbg z (hKb z hz)).1 t ht
  set d1 := min (min δ h / 2) (d0 / 2) with hd1
  have hd1pos : 0 < d1 := by positivity
  have hU0 := unif_conv hconv hKc hd1pos (fun z hz t ht => by
      rw [hμ] at ht; exact (min_le_right _ _).trans (hsuppK z hz t ht))
    (hrootK.mono fun k hk z hz j => (min_le_left _ _).trans (hk z hz j))
  rw [hμ] at hU0
  have hU : Tendsto (fun p : ℕ × ℂ => (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) -
      I * κ * G p.2) (atTop ×ˢ 𝓟 K) (𝓝 0) := by
    have := hU0.const_mul (I * κ)
    rw [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun p => ?_)
    show I * κ * (((N p.1 : ℝ)⁻¹ : ℂ) * ∑ j, (p.2 - ((B p.1).q j : ℂ))⁻¹ - G p.2) =
      (∑ j, I * ((κ / N p.1 : ℝ) : ℂ) / (p.2 - ((B p.1).q j : ℂ))) - I * κ * G p.2
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  have hGd : ∀ z ∈ K, DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_cauchy S.μ (show 0 < d0 / 2 by positivity) (hsuppK z hz)
  have hDev : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, Df L κ G w ≠ 0 := fun z hz => by
    filter_upwards [(hbg z (hKb z hz)).2.1] with w hw
    intro h0; rw [h0, norm_zero] at hw; linarith
  have hMK : ∀ z ∈ K, ‖Af κ G z‖ ≤ 2 * M ∧ ‖(Af κ G z)⁻¹‖ ≤ 2 * M ∧ ‖ef L z‖ ≤ 2 * M ∧
      η / 2 ≤ ‖Df L κ G z‖ := fun z hz => by
    obtain ⟨-, hD, hA, hAi, he⟩ := hbg z (hKb z hz)
    exact ⟨hA, hAi, he, hD.self_of_nhds⟩
  have hev := eventual_props (q := fun k => (B k).q) (G := G) (Γ := K) (L := L) hκ hN hNtop hmh hrootK hU hGd hDev
    (M := 2 * M) (η := η / 2) (by linarith) (by positivity) hMK
  have hevk := Filter.eventually_prod_principal_iff.1 hev
  filter_upwards [hevk] with k hk w hw
  obtain ⟨hR, hW, ha, hDN, haA⟩ := hk w hw
  have hMpos : 0 < 2 * M := by linarith
  have hDz : Df L κ G w ≠ 0 := by
    have := (hMK w hw).2.2.2
    intro h0; rw [h0, norm_zero] at this; linarith
  exact branch_regular S.μ (d0 := d0 / 2) (η := η / 2) (show 0 < d0 / 2 by positivity) hMpos (by positivity)
    (hsuppK w hw) hR hDz hW ha hDN haA (hMK w hw).2.1

/-! ### 5. The finite-probe lemma with the branch clause -/

/-- **PROP-009 `lem:B4-finite-probes` with the branch clause.** -/
theorem finite_probes_branch {L κ : ℝ} (S : IndexedScalarMeasureCuts L κ) {n : ℤ} {xm xp h : ℝ}
    (hxm : xm ∈ S.cuts) (hxp : xp ∈ S.cuts) (hlt : xm < xp) (hh : 0 < h)
    (h1 : 2 * Real.pi * (n - 1) < exteriorForce L κ S.μ xm)
    (h2 : exteriorForce L κ S.μ xm < 2 * Real.pi * n)
    (h3 : 2 * Real.pi * n < exteriorForce L κ S.μ xp)
    (h4 : exteriorForce L κ S.μ xp < 2 * Real.pi * (n + 1)) :
    ∃ M η : ℝ, 1 ≤ M ∧ 0 < η ∧ ∃ δ > 0, ∃ r0 > 0, r0 ≤ min δ h / 2 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      ∃ m : ℕ, ∃ z : Fin m → ℂ, (∀ j, HighHalf L κ (z j)) ∧ ∃ ε > 0, ∃ N₀ : ℕ, ∃ C : ℝ,
        ∀ (N : ℕ) (hN : 0 < N), N₀ ≤ N → ∀ B : OnShellBethe L κ N,
          (∀ j, ‖sNf L (κ / N) B.q (z j) - sf L κ (cauchyTransform S.μ) (z j)‖ < ε) →
          BlockConclusion B n xm xp δ ∧
          (∀ w ∈ Gam xm xp h, ‖remf κ L (fun _ => N) (fun _ => B.q) (cauchyTransform S.μ) (0, w)‖ ≤
            C * ((N : ℝ)⁻¹) ^ 2) ∧
          ∀ w ∈ nb (Gam xm xp h) r, BranchGood L κ (κ / N) (2 * M) (η / 2) (cauchyTransform S.μ) B.q w := by
  have hL := S.hL
  have hκ := S.hκ
  haveI : IsProbabilityMeasure S.μ := S.isProb
  obtain ⟨η, M, Gb, hη, hM, hGb, hbg⟩ := gam_background S hxm hxp hlt hh h1 h2 h3 h4
  obtain ⟨d0, hd0, hsupp⟩ := gam_supp_dist S hxm hxp hh
  obtain ⟨r0b, hr0b, hnb⟩ := nbhd_background (L := L) (κ := κ) S.μ (isCompact_Gam xm xp h) hd0 hM hsupp
    (fun z hz => ⟨(hbg z hz).2.1, (hbg z hz).2.2.1, (hbg z hz).2.2.2.1, (hbg z hz).2.2.2.2.1⟩) hη
  set μ : ProbabilityMeasure ℝ := ⟨S.μ, S.isProb⟩ with hμdef
  obtain ⟨δ, hδ, U, hU, N₁, hN₁⟩ := label_block_uniform S (μ := μ) rfl hxm hxp hlt h1 h2 h3 h4
  refine ⟨M, η, hM, hη, δ, hδ, min r0b (min δ h / 2), by positivity, min_le_right _ _, ?_⟩
  intro r hr hrle
  have hr0 : r ≤ r0b := hrle.trans (min_le_left _ _)
  have hrδ : r ≤ min δ h / 2 := hrle.trans (min_le_right _ _)
  let P : ℕ → ∀ N : ℕ, OnShellBethe L κ N → Prop := fun t N B =>
    BlockConclusion B n xm xp δ ∧
    (∀ w ∈ Gam xm xp h, ‖remf κ L (fun _ => N) (fun _ => B.q) (cauchyTransform S.μ) (0, w)‖ ≤
      (t : ℝ) * ((N : ℝ)⁻¹) ^ 2) ∧
    ∀ w ∈ nb (Gam xm xp h) r, BranchGood L κ (κ / N) (2 * M) (η / 2) (cauchyTransform S.μ) B.q w
  have hmono : ∀ t t' N (B : OnShellBethe L κ N), t ≤ t' → P t N B → P t' N B := by
    intro t t' N B htt hP
    refine ⟨hP.1, fun w hw => (hP.2.1 w hw).trans ?_, hP.2.2⟩
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast htt) (sq_nonneg _)
  have hseq : ∀ (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (B : ∀ k, OnShellBethe L κ (N k)),
      Tendsto (fun k => rootP (B k) (hN k)) atTop (𝓝 μ) →
      Tendsto N atTop atTop → ∃ t, ∀ᶠ k in atTop, P t (N k) (B k) := by
    intro N hN B hconv hNtop
    have hblock : ∀ᶠ k in atTop, BlockConclusion (B k) n xm xp δ := by
      filter_upwards [hconv.eventually (mem_of_superset hU subset_rfl),
        hNtop.eventually (eventually_ge_atTop N₁)] with k hk1 hk2
      exact hN₁ (N k) (hN k) hk2 (B k) hk1
    have hroot : ∀ᶠ k in atTop, ∀ z ∈ Gam xm xp h, ∀ j, min δ h ≤ ‖z - ((B k).q j : ℝ)‖ :=
      hblock.mono fun k hk z hz j => Gam_dist hh (hk j).2.1 (hk j).2.2 hz
    obtain ⟨C₁, hC₁⟩ := log_reconstruction S (μ := μ) rfl hconv hNtop hxm hxp hlt hh h1 h2 h3 h4
    have hbr := branch_eventually S (μ := μ) rfl hconv hNtop (r0 := r0b) hh hδ hd0 hη hM hr hr0 hrδ hsupp hroot hnb
    refine ⟨⌈C₁⌉₊, ?_⟩
    filter_upwards [hblock, hC₁, hbr] with k hk hCk hbk
    refine ⟨hk, fun w hw => (hCk w hw).trans ?_, hbk⟩
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil C₁) (sq_nonneg _)
  obtain ⟨m, z, hz, ε, hε, N₀, t, ht⟩ := probes_generic S P hmono hseq
  exact ⟨m, z, hz, ε, hε, N₀, (t : ℝ), fun N hN hN0 B hB => ht N hN hN0 B hB⟩

end QuantumNLS.Prop009Branch

#print axioms QuantumNLS.Prop009Branch.nbhd_background
#print axioms QuantumNLS.Prop009Branch.branch_regular
#print axioms QuantumNLS.Prop009Branch.branch_eventually
#print axioms QuantumNLS.Prop009Branch.finite_probes_branch
