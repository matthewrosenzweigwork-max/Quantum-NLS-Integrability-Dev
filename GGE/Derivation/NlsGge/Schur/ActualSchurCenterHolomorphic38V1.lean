import NlsGge.Schur.ActualSchurCenterContraction38V1
import NlsGge.Schur.ActualSchurCoefficientJointAnalyticV2_31
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Holomorphy of the moving gap center in the potential pair (NEW-F03.05)

Source: `paper/v2.tex` lines 1118-1127.  For `R ≥ 1` and `|n| ≥ C R^3` the
center `σ_n(p)` of the closed disk `|σ - nπ| ≤ 1/2` solving
`σ = nπ + α_n(σ; p)` (unique by `actualSchurCenter_existsUnique38V1`) depends
complex-differentiably on the independent complex H¹ pair `p` in the open balls
`‖p.1‖ < R`, `‖p.2‖ < R`.

Route: the implicit-function theorem in its inverse-function form.  The map
`Φ(w, p) = (w - nπ - α(w, p), p)` is strictly differentiable at `(σ(p₀), p₀)`
(joint analyticity of the actual coefficient on the original spectral disk times
the closed balls), its derivative is invertible because `|∂_w α| ≤ 1/4`, and
the local inverse branch is identified with the unique fixed point.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace NNReal Topology
open Filter
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- Abstract implicit-function step: if `α` is strictly differentiable at a
fixed point `(w₀, p₀)` of `w = c + α(w, p₀)` with `∂_w α ≠ 1`, then there is a
function `s`, differentiable at `p₀`, with `s p₀ = w₀` and
`s q = c + α (s q, q)` near `p₀`. -/
theorem strictFixedPoint_differentiableAt38V1 {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H]
    (α : ℂ × H → ℂ) (c w0 : ℂ) (p0 : H) (α' : ℂ × H →L[ℂ] ℂ)
    (hα : HasStrictFDerivAt α α' (w0, p0)) (ha : α' (1, 0) ≠ 1)
    (hfix : w0 = c + α (w0, p0)) :
    ∃ s : H → ℂ, DifferentiableAt ℂ s p0 ∧ s p0 = w0 ∧
      ∀ᶠ q in 𝓝 p0, s q = c + α (s q, q) := by
  set a : ℂ := α' (1, 0) with ha_def
  have h1a : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  let Bq : H →L[ℂ] ℂ := α'.comp (ContinuousLinearMap.inr ℂ ℂ H)
  have hα' : ∀ x : ℂ × H, α' x = x.1 * a + Bq x.2 := by
    intro x
    have hx : x = x.1 • ((1 : ℂ), (0 : H)) + ((0 : ℂ), x.2) := by
      ext <;> simp
    conv_lhs => rw [hx]
    simp only [map_add, map_smul, smul_eq_mul, ← ha_def]
    rfl
  let Φ : ℂ × H → ℂ × H := fun x => (x.1 - c - α x, x.2)
  let Φ' : ℂ × H →L[ℂ] ℂ × H :=
    ((ContinuousLinearMap.fst ℂ ℂ H) - α').prod (ContinuousLinearMap.snd ℂ ℂ H)
  let Ψ' : ℂ × H →L[ℂ] ℂ × H :=
    (((1 - a)⁻¹) • ((ContinuousLinearMap.fst ℂ ℂ H) +
      Bq.comp (ContinuousLinearMap.snd ℂ ℂ H))).prod (ContinuousLinearMap.snd ℂ ℂ H)
  have hl : Function.LeftInverse Ψ' Φ' := by
    intro x
    ext
    · simp [Ψ', Φ', hα']
      field_simp
      ring
    · simp [Ψ', Φ']
  have hr : Function.RightInverse Ψ' Φ' := by
    intro x
    ext
    · simp [Ψ', Φ', hα']
      field_simp
      ring
    · simp [Ψ', Φ']
  let e : (ℂ × H) ≃L[ℂ] (ℂ × H) := ContinuousLinearEquiv.equivOfInverse Φ' Ψ' hl hr
  have hΦ0 : HasStrictFDerivAt Φ Φ' (w0, p0) := by
    have := ((hasStrictFDerivAt_fst (𝕜 := ℂ) (E := ℂ) (F := H) (p := (w0, p0))).sub_const c).sub hα
    exact this.prodMk (hasStrictFDerivAt_snd (𝕜 := ℂ) (E := ℂ) (F := H) (p := (w0, p0)))
  have hΦ : HasStrictFDerivAt Φ ((e : (ℂ × H) →L[ℂ] (ℂ × H))) (w0, p0) := hΦ0
  have hpt : Φ (w0, p0) = (0, p0) := by
    simp only [Φ]
    rw [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    rw [sub_sub, sub_eq_zero]
    exact hfix
  let g : ℂ × H → ℂ × H := hΦ.localInverse Φ _ _
  have hgd : HasStrictFDerivAt g (e.symm : (ℂ × H) →L[ℂ] (ℂ × H)) (0, p0) := by
    have := hΦ.to_localInverse
    rwa [hpt] at this
  have hcurve : HasStrictFDerivAt (fun q : H => ((0 : ℂ), q))
      (ContinuousLinearMap.inr ℂ ℂ H) p0 :=
    (hasStrictFDerivAt_const (0 : ℂ) p0).prodMk (hasStrictFDerivAt_id p0)
  have hcomp := (hgd.comp p0 hcurve)
  refine ⟨fun q => (g (0, q)).1, ?_, ?_, ?_⟩
  · have := (hasStrictFDerivAt_fst (𝕜 := ℂ) (E := ℂ) (F := H) (p := g (0, p0))).comp p0 hcomp
    exact this.hasFDerivAt.differentiableAt
  · have := hΦ.localInverse_apply_image
    rw [hpt] at this
    exact congrArg Prod.fst this
  · have hev := hΦ.eventually_right_inverse
    rw [hpt] at hev
    have hev2 : ∀ᶠ q in 𝓝 p0, Φ (g (0, q)) = (0, q) :=
      (hcurve.hasFDerivAt.continuousAt.tendsto.eventually hev)
    filter_upwards [hev2] with q hq
    have h1 := congrArg Prod.fst hq
    have h2 := congrArg Prod.snd hq
    simp only [Φ] at h1 h2
    have h3 : α (g (0, q)) = α ((g (0, q)).1, q) := congrArg α (Prod.ext rfl h2)
    show (g (0, q)).1 = c + α ((g (0, q)).1, q)
    rw [← h3]
    linear_combination h1

open scoped Classical in
/-- The moving gap center `σ_n(p)`: for `1 ≤ R`, `C R^3 ≤ |n|` and a pair in the
closed radius-`R` balls it is the unique solution in `|σ - nπ| ≤ 1/2` of
`σ = nπ + α_n(σ; p)`; outside this range it is the junk value `nπ`. -/
def actualSchurCenter38 (R : ℝ) (n : ℤ) (p : ActualSchurEffectiveH1PairV3_30) : ℂ :=
  if h : 1 ≤ R ∧ actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| ∧
      ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R then
    Classical.choose (actualSchurCenter_existsUnique38V1 R h.1 n h.2.1 p h.2.2.1
      h.2.2.2).exists
  else spectralCenter n

/-- Specification of `actualSchurCenter38` in the source range. -/
theorem actualSchurCenter38_spec
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) :
    actualSchurCenter38 R n p ∈ Metric.closedBall (spectralCenter n) (1 / 2) ∧
      actualSchurCenter38 R n p =
        spectralCenter n + actualSchurAlpha38 n p (actualSchurCenter38 R n p) := by
  have h : 1 ≤ R ∧ actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)| ∧
      ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := ⟨hR, hthr, hp₁, hp₂⟩
  unfold actualSchurCenter38
  split_ifs with h'
  · exact Classical.choose_spec (actualSchurCenter_existsUnique38V1 R h'.1 n h'.2.1 p h'.2.2.1
      h'.2.2.2).exists
  · exact absurd h h'

/-- Any solution of the center equation in the closed half disk is
`actualSchurCenter38`. -/
theorem actualSchurCenter38_eq_of_fixed
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ ≤ R) (hp₂ : ‖p.2‖ ≤ R) (σ : ℂ)
    (hσ : σ ∈ Metric.closedBall (spectralCenter n) (1 / 2))
    (hfix : σ = spectralCenter n + actualSchurAlpha38 n p σ) :
    actualSchurCenter38 R n p = σ :=
  (actualSchurCenter_existsUnique38V1 R hR n hthr p hp₁ hp₂).unique
    (actualSchurCenter38_spec R hR n hthr p hp₁ hp₂) ⟨hσ, hfix⟩

set_option backward.isDefEq.respectTransparency false in
/-- F:eq:center holomorphy: on the open balls `‖p.1‖ < R`, `‖p.2‖ < R` the center
`σ_n(p)` is complex-differentiable in the independent complex H¹ pair. -/
theorem actualSchurCenter38_differentiableAt
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R) :
    DifferentiableAt ℂ (actualSchurCenter38 R n) p := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  obtain ⟨hmaps, -⟩ :=
    actualSchurCenterMap38_mapsTo_and_lipschitz R hR n hthr p hp₁.le hp₂.le
  obtain ⟨hσball, hσfix⟩ := actualSchurCenter38_spec R hR n hthr p hp₁.le hp₂.le
  set σ0 := actualSchurCenter38 R n p with hσ0
  have hσD : σ0 ∈ spectralDisk n := closedBall_half_subset_spectralDisk38 n hσball
  have hσ18 : ‖σ0 - spectralCenter n‖ ≤ 1 / 8 := by
    have := hmaps σ0 hσball
    rwa [← hσfix] at this
  -- joint analyticity at `(σ0, p)`
  have hAn := (actualSchurCoefficientsJointAnalyticV2_31 R hR n hn hlarge).1
  have hmem : ((σ0, p) : ℂ × ActualSchurEffectiveH1PairV3_30) ∈
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} :=
    ⟨hσD, hp₁.le, hp₂.le⟩
  have hα := (hAn _ hmem).hasStrictFDerivAt
  set α' := fderiv ℂ (actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (true, resonantIndex n)) (σ0, p) with hα'
  -- the partial derivative in the spectral variable is the Green derivative
  have hpart : HasDerivAt (actualSchurAlpha38 n p) (α' (1, 0)) σ0 := by
    have h1 : HasFDerivAt (fun w : ℂ => ((w, p) : ℂ × ActualSchurEffectiveH1PairV3_30))
        (ContinuousLinearMap.inl ℂ ℂ ActualSchurEffectiveH1PairV3_30) σ0 :=
      (hasFDerivAt_id σ0).prodMk (hasFDerivAt_const p σ0)
    have h2 := hα.hasFDerivAt.comp σ0 h1
    have h3 := h2.hasDerivAt
    exact h3
  have hbd := actualSchurAlpha38_deriv_bound R hR n hn hlarge p σ0 hσD hp₁.le hp₂.le
  have hder := actualSchurAlpha38_hasDerivAt R hR n hn hlarge p σ0 hσD hp₁.le hp₂.le
  have hval := hpart.unique hder
  have hne : α' (1, 0) ≠ 1 := by
    intro h1
    have h14 := (actualSchurCenterThresholdConstant38_consequences R hR n hthr).2.2.2
    rw [hval] at h1
    have := le_trans hbd h14
    rw [h1] at this
    norm_num at this
  obtain ⟨s, hs, hs0, hsfix⟩ :=
    strictFixedPoint_differentiableAt38V1
      (actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n))
      (spectralCenter n) σ0 p α' hα hne hσfix
  have hscont : ContinuousAt s p := hs.continuousAt
  have hnear : ∀ᶠ q in 𝓝 p, dist (s q) σ0 < 1 / 8 := by
    have := hscont.eventually (Metric.ball_mem_nhds (s p) (show (0 : ℝ) < 1 / 8 by norm_num))
    filter_upwards [this] with q hq
    rw [hs0] at hq
    exact hq
  have hq1 : ∀ᶠ q in 𝓝 p, ‖q.1‖ < R :=
    (continuous_norm.comp continuous_fst).continuousAt.eventually (gt_mem_nhds hp₁)
  have hq2 : ∀ᶠ q in 𝓝 p, ‖q.2‖ < R :=
    (continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds hp₂)
  have hEq : actualSchurCenter38 R n =ᶠ[𝓝 p] s := by
    filter_upwards [hsfix, hnear, hq1, hq2] with q hqfix hqn hq1' hq2'
    refine actualSchurCenter38_eq_of_fixed R hR n hthr q hq1'.le hq2'.le (s q) ?_ hqfix
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [dist_eq_norm] at hqn
    calc ‖s q - spectralCenter n‖ = ‖(s q - σ0) + (σ0 - spectralCenter n)‖ := by
          congr 1; ring
      _ ≤ ‖s q - σ0‖ + ‖σ0 - spectralCenter n‖ := norm_add_le _ _
      _ ≤ 1 / 2 := by linarith
  exact hs.congr_of_eventuallyEq hEq

end NlsGge.Schur
