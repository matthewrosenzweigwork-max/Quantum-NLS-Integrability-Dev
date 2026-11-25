import NlsGge.Schur.ActualSchurQnRealDerivative38V1
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Constructions

/-!
# Real/complex analyticity of the Schur center and of `q_n` (NEW-F03.05/06, review note N1)

Source: `paper/v2.tex` lines 1118-1129 ("`σ_n` and `q_n` are analytic on a
neighbourhood of the ball").  The earlier files prove only
`DifferentiableAt`.  Pinned mathlib has no "complex differentiable on an open
subset of a Banach space implies analytic", so analyticity is obtained from the
analytic inverse function theorem `OpenPartialHomeomorph.analyticAt_symm` applied
to `Φ(w, p) = (w - nπ - α(w, p), p)`, using the joint analyticity of the actual
coefficient (`actualSchurCoefficientsJointAnalyticV2_31`).

* (a) `actualSchurCenter38_analyticAt`: the center is `ℂ`-analytic at every
  `p` in the open balls;
* (b) `actualSchurQn38_analyticAt`: so is `q_n`;
* (c) `actualSchurQnRealRemainder38_analyticAt`: the real-type remainder
  `v ↦ q_n(v, v̄) - v_n` is `ℝ`-analytic on the open H¹ ball.
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace NNReal Topology ENNReal
open Filter
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

local notation "H1" => WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-- Analytic implicit-function step: if `α` is analytic at a fixed point
`(w₀, p₀)` of `w = c + α(w, p₀)` with `∂_w α ≠ 1`, then there is a function `s`,
analytic at `p₀`, with `s p₀ = w₀` and `s q = c + α (s q, q)` near `p₀`. -/
theorem strictFixedPoint_analyticAt38V1 {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [CompleteSpace H]
    (α : ℂ × H → ℂ) (c w0 : ℂ) (p0 : H)
    (hα : AnalyticAt ℂ α (w0, p0))
    (ha : fderiv ℂ α (w0, p0) (1, 0) ≠ 1)
    (hfix : w0 = c + α (w0, p0)) :
    ∃ s : H → ℂ, AnalyticAt ℂ s p0 ∧ s p0 = w0 ∧
      ∀ᶠ q in 𝓝 p0, s q = c + α (s q, q) := by
  set α' : ℂ × H →L[ℂ] ℂ := fderiv ℂ α (w0, p0) with hα'def
  have hαs : HasStrictFDerivAt α α' (w0, p0) := hα.hasStrictFDerivAt
  set a : ℂ := α' (1, 0) with ha_def
  have h1a : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  let Bq : H →L[ℂ] ℂ := α'.comp (ContinuousLinearMap.inr ℂ ℂ H)
  have hα'x : ∀ x : ℂ × H, α' x = x.1 * a + Bq x.2 := by
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
    · simp [Ψ', Φ', hα'x]
      field_simp
      ring
    · simp [Ψ', Φ']
  have hr : Function.RightInverse Ψ' Φ' := by
    intro x
    ext
    · simp [Ψ', Φ', hα'x]
      field_simp
      ring
    · simp [Ψ', Φ']
  let e : (ℂ × H) ≃L[ℂ] (ℂ × H) := ContinuousLinearEquiv.equivOfInverse Φ' Ψ' hl hr
  have hΦ0 : HasStrictFDerivAt Φ Φ' (w0, p0) := by
    have := ((hasStrictFDerivAt_fst (𝕜 := ℂ) (E := ℂ) (F := H) (p := (w0, p0))).sub_const c).sub
      hαs
    exact this.prodMk (hasStrictFDerivAt_snd (𝕜 := ℂ) (E := ℂ) (F := H) (p := (w0, p0)))
  have hΦ : HasStrictFDerivAt Φ ((e : (ℂ × H) →L[ℂ] (ℂ × H))) (w0, p0) := hΦ0
  have hpt : Φ (w0, p0) = (0, p0) := by
    simp only [Φ]
    rw [Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    rw [sub_sub, sub_eq_zero]
    exact hfix
  -- analyticity of `Φ` at `(w0, p0)`
  have hΦan : AnalyticAt ℂ Φ (w0, p0) := by
    have h1 : AnalyticAt ℂ (fun x : ℂ × H => x.1 - c - α x) (w0, p0) := by
      have hfst : AnalyticAt ℂ (fun x : ℂ × H => x.1) (w0, p0) :=
        (ContinuousLinearMap.fst ℂ ℂ H).analyticAt _
      exact (hfst.sub analyticAt_const).sub hα
    have h2 : AnalyticAt ℂ (fun x : ℂ × H => x.2) (w0, p0) :=
      (ContinuousLinearMap.snd ℂ ℂ H).analyticAt _
    exact h1.prod h2
  let Φ0 : OpenPartialHomeomorph (ℂ × H) (ℂ × H) := hΦ.toOpenPartialHomeomorph Φ
  have hΦ0coe : (Φ0 : ℂ × H → ℂ × H) = Φ := rfl
  have hsrc : (w0, p0) ∈ Φ0.source := hΦ.mem_toOpenPartialHomeomorph_source
  have htgt : (0, p0) ∈ Φ0.target := by
    have := hΦ.image_mem_toOpenPartialHomeomorph_target
    rwa [hpt] at this
  have hsymm : Φ0.symm (0, p0) = (w0, p0) := by
    have := Φ0.left_inv hsrc
    rw [hΦ0coe, hpt] at this
    exact this
  have hAn : AnalyticAt ℂ Φ0 (Φ0.symm (0, p0)) := by
    rw [hsymm]; exact hΦan
  have hder : fderiv ℂ Φ0 (Φ0.symm (0, p0)) = (e : ℂ × H →L[ℂ] ℂ × H) := by
    rw [hsymm]; exact hΦ.hasFDerivAt.fderiv
  have hsymAn : AnalyticAt ℂ Φ0.symm (0, p0) :=
    Φ0.analyticAt_symm (i := e) htgt hAn hder
  have hcurve : AnalyticAt ℂ (fun q : H => ((0 : ℂ), q)) p0 :=
    analyticAt_const.prod analyticAt_id
  have hfstA : AnalyticAt ℂ (fun x : ℂ × H => x.1) (Φ0.symm (0, p0)) :=
    (ContinuousLinearMap.fst ℂ ℂ H).analyticAt _
  refine ⟨fun q => (Φ0.symm (0, q)).1, ?_, ?_, ?_⟩
  · exact (hfstA.comp hsymAn).comp hcurve
  · show (Φ0.symm (0, p0)).1 = w0
    rw [hsymm]
  · have hev : ∀ᶠ y in 𝓝 ((0 : ℂ), p0), y ∈ Φ0.target := Φ0.open_target.mem_nhds htgt
    have hev2 : ∀ᶠ q in 𝓝 p0, ((0 : ℂ), q) ∈ Φ0.target :=
      hcurve.continuousAt.tendsto.eventually hev
    filter_upwards [hev2] with q hq
    have hq' := Φ0.right_inv hq
    rw [hΦ0coe] at hq'
    have h1 := congrArg Prod.fst hq'
    have h2 := congrArg Prod.snd hq'
    simp only [Φ] at h1 h2
    have h3 : α (Φ0.symm (0, q)) = α ((Φ0.symm (0, q)).1, q) :=
      congrArg α (Prod.ext rfl h2)
    show (Φ0.symm (0, q)).1 = c + α ((Φ0.symm (0, q)).1, q)
    rw [← h3]
    linear_combination h1

set_option backward.isDefEq.respectTransparency false in
/-- (a) F:eq:center analyticity: on the open balls `‖p.1‖ < R`, `‖p.2‖ < R` the
center `σ_n(p)` is complex-analytic at every point of the independent complex H¹
pair space. -/
theorem actualSchurCenter38_analyticAt
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R) :
    AnalyticAt ℂ (actualSchurCenter38 R n) p := by
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
  have hAn := (actualSchurCoefficientsJointAnalyticV2_31 R hR n hn hlarge).1
  have hmem : ((σ0, p) : ℂ × ActualSchurEffectiveH1PairV3_30) ∈
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} :=
    ⟨hσD, hp₁.le, hp₂.le⟩
  have hαan := hAn _ hmem
  have hα := hαan.hasStrictFDerivAt
  set α' := fderiv ℂ (actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (true, resonantIndex n)) (σ0, p) with hα'
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
    strictFixedPoint_analyticAt38V1
      (actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (true, resonantIndex n))
      (spectralCenter n) σ0 p hαan hne hσfix
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
  exact hs.congr hEq.symm

set_option backward.isDefEq.respectTransparency false in
/-- (b) `q_n(p) = b_n(σ_n(p); p)` is complex-analytic at every point of the open
balls `‖p.1‖ < R`, `‖p.2‖ < R`. -/
theorem actualSchurQn38_analyticAt
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (p : ActualSchurEffectiveH1PairV3_30)
    (hp₁ : ‖p.1‖ < R) (hp₂ : ‖p.2‖ < R) :
    AnalyticAt ℂ (actualSchurQn38 R n) p := by
  obtain ⟨hn, hlarge, -, -⟩ :=
    actualSchurCenterThresholdConstant38_consequences R hR n hthr
  obtain ⟨hσ, -⟩ := actualSchurCenter38_spec R hR n hthr p hp₁.le hp₂.le
  have hAn := (actualSchurCoefficientsJointAnalyticV2_31 R hR n hn hlarge).2.1
  have hmem : ((actualSchurCenter38 R n p, p) : ℂ × ActualSchurEffectiveH1PairV3_30) ∈
      {x : ℂ × ActualSchurEffectiveH1PairV3_30 |
        x.1 ∈ spectralDisk n ∧ ‖x.2.1‖ ≤ R ∧ ‖x.2.2‖ ≤ R} :=
    ⟨closedBall_half_subset_spectralDisk38 n hσ, hp₁.le, hp₂.le⟩
  have hb := hAn _ hmem
  have hσa := actualSchurCenter38_analyticAt R hR n hthr p hp₁ hp₂
  have hpair : AnalyticAt ℂ (fun q : ActualSchurEffectiveH1PairV3_30 =>
      (actualSchurCenter38 R n q, q)) p := hσa.prod analyticAt_id
  exact AnalyticAt.comp (g := actualSchurCoefficientAfterDext31 n
    (true, resonantIndex n) (false, resonantIndex n))
    (f := fun q : ActualSchurEffectiveH1PairV3_30 => (actualSchurCenter38 R n q, q)) hb hpair

set_option backward.isDefEq.respectTransparency false in
/-- (c) The real-type remainder `v ↦ q_n(v, v̄) - v_n` is real-analytic at every
`u` of the open H¹ ball `‖u‖ < R` (real structure on the complex H¹ carrier by
restriction of scalars). -/
theorem actualSchurQnRealRemainder38_analyticAt
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (u : H1) (hu : ‖u‖ < R) :
    AnalyticAt ℝ (actualSchurQnRealRemainder38 R n) u := by
  have hq := actualSchurQn38_analyticAt R hR n hthr (u, actualH1Conj38 u) hu
    (by rw [actualH1Conj38_norm]; exact hu)
  have hqR : AnalyticAt ℝ (actualSchurQn38 R n) (actualRealTypeEmbedding38 u) :=
    hq.restrictScalars (𝕜 := ℝ)
  have hι : AnalyticAt ℝ (fun v : H1 => actualRealTypeEmbedding38 v) u :=
    actualRealTypeEmbedding38.analyticAt u
  have h1 : AnalyticAt ℝ
      (fun v : H1 => actualSchurQn38 R n (actualRealTypeEmbedding38 v)) u :=
    AnalyticAt.comp (g := actualSchurQn38 R n)
      (f := fun v : H1 => actualRealTypeEmbedding38 v) hqR hι
  have h2 : AnalyticAt ℝ (fun v : H1 => actualH1CoordinateCLM38 n v) u :=
    ((actualH1CoordinateCLM38 n).restrictScalars ℝ).analyticAt u
  have h := h1.sub h2
  convert h using 1
  funext v
  simp only [actualSchurQnRealRemainder38, actualRealTypeEmbedding38_apply,
    actualH1CoordinateCLM38_apply]
  rfl

end NlsGge.Schur
