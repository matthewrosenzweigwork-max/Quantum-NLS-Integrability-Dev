import NlsGge.Atomic.G4.G4004
import NlsGge.Atomic.LIB.LIB010
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

set_option autoImplicit false

open Metric Set Filter Topology MeasureTheory
open TopologicalSpace

namespace NlsGge.Atomic.G4

noncomputable section

private theorem affineLine_analyticAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (x h : E) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => x + w • h) z := by
  haveI : IsScalarTower ℂ ℂ E := ⟨fun a b w => by simpa using (mul_smul a b w)⟩
  have hsmul : AnalyticAt ℂ (fun w : ℂ => w • h) z := by
    convert analyticAt_id.smul (analyticAt_const (v := h) (x := z)) using 1
    · ext w
      rfl
    · exact this
  exact analyticAt_const.add hsmul

/-- Countably many parameterwise exceptional sets can be synchronized on one
separable affine complex disk.  The exceptional set obtained here is local to
this disk; no separability assumption on the Banach parameter space is used. -/
private theorem ae_bound_on_affine_disk
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {μ : Measure α} {U : Set E} {a : α → E → F}
    {u h : E} {r R : ℝ} {g : α → ℝ}
    (ha : ∀ᵐ t ∂μ, AnalyticOnNhd ℂ (a t) U)
    (hballU : ball u r ⊆ U)
    (hdom : ∀ v ∈ ball u r, ∀ᵐ t ∂μ, ‖a t v‖ ≤ g t)
    (hmap : ∀ z : ℂ, ‖z‖ ≤ R → u + z • h ∈ ball u r) :
    ∀ᵐ t ∂μ, ∀ z : ℂ, ‖z‖ ≤ R → ‖a t (u + z • h)‖ ≤ |g t| := by
  classical
  let S : Type := {z : ℂ // z ∈ closedBall (0 : ℂ) R}
  have hsepSet : IsSeparable (closedBall (0 : ℂ) R) :=
    TopologicalSpace.IsSeparable.of_separableSpace (closedBall (0 : ℂ) R)
  letI : SeparableSpace S := hsepSet.separableSpace
  obtain ⟨D, hDcount, hDdense⟩ := (exists_countable_dense S)
  haveI : Countable D := hDcount.to_subtype
  let line : ℂ → E := fun z => u + z • h
  have hAE : ∀ᵐ t ∂μ, ∀ z : D, ‖a t (u + (z.1.1) • h)‖ ≤ |g t| :=
    ae_all_iff.2 fun z => by
      have hz : ‖(z.1.1 : ℂ)‖ ≤ R := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using z.1.2
      have hzmap := hmap z.1.1 hz
      exact (hdom (u + z.1.1 • h) hzmap).mono fun t ht => ht.trans (le_abs_self _)
  filter_upwards [ha, hAE] with t htAnalytic htDense
  have hlineContinuous : Continuous (fun z : S => a t (u + (z.1 : ℂ) • h)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hz : ‖(z.1 : ℂ)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using z.2
    have hpoint : u + (z.1 : ℂ) • h ∈ U := hballU (hmap z.1 hz)
    have ha_cont : ContinuousAt (a t) (u + (z.1 : ℂ) • h) :=
      (htAnalytic (u + (z.1 : ℂ) • h) hpoint).continuousAt
    have hinner : ContinuousAt (fun w : S => u + (w.1 : ℂ) • h) z := by
      fun_prop
    exact ContinuousAt.comp
      (f := fun w : S => u + (w.1 : ℂ) • h) (g := a t) ha_cont hinner
  let B : Set S := {z | ‖a t (u + (z.1 : ℂ) • h)‖ ≤ |g t|}
  have hBclosed : IsClosed B := isClosed_Iic.preimage hlineContinuous.norm
  have hDsubset : D ⊆ B := by
    intro z hz
    exact htDense ⟨z, hz⟩
  have hclosure : closure D ⊆ B := closure_minimal hDsubset hBclosed
  have hall : ∀ z : S, ‖a t (u + (z.1 : ℂ) • h)‖ ≤ |g t| := by
    intro z
    have hzcl : z ∈ closure D := by
      rw [hDdense.closure_eq]
      simp
    exact hclosure hzcl
  intro z hz
  have hzS : ‖(z : ℂ)‖ ≤ R := hz
  simpa using hall ⟨z, by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzS⟩

private theorem scalar_integral_line_hasDerivAt
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {μ : Measure α} {U : Set E} {a : α → E → F}
    (ha : ∀ᵐ t ∂μ, AnalyticOnNhd ℂ (a t) U)
    (hmeas : ∀ v ∈ U, AEStronglyMeasurable (fun t => a t v) μ)
    {u h : E} (hu : u ∈ U)
    {r : ℝ} (hr : 0 < r) (hballU : ball u r ⊆ U)
    {g : α → ℝ} (hg : Integrable g μ)
    (hdom : ∀ v ∈ ball u r, ∀ᵐ t ∂μ, ‖a t v‖ ≤ g t)
    (L : F →L[ℂ] ℂ) :
    ∃ δ : ℝ, 0 < δ ∧
      HasDerivAt
        (fun z : ℂ => L (∫ t, a t (u + z • h) ∂μ))
        (∫ t, deriv (fun w : ℂ => L (a t (u + w • h))) 0 ∂μ) 0 := by
  let δ : ℝ := r / (4 * (‖h‖ + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hmap : ∀ z : ℂ, ‖z‖ ≤ 2 * δ → u + z • h ∈ ball u r := by
    intro z hz
    rw [mem_ball_iff_norm]
    have hz' : ‖z‖ ≤ r / (2 * (‖h‖ + 1)) := by
      calc
        ‖z‖ ≤ 2 * δ := hz
        _ = r / (2 * (‖h‖ + 1)) := by dsimp [δ]; field_simp; norm_num
    have hratio : ‖h‖ / (‖h‖ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [norm_nonneg h]
    calc
      ‖u + z • h - u‖ = ‖z • h‖ := by congr 1 <;> abel
      _ = ‖z‖ * ‖h‖ := norm_smul _ _
      _ ≤ (r / (2 * (‖h‖ + 1))) * ‖h‖ :=
        mul_le_mul_of_nonneg_right hz' (norm_nonneg h)
      _ = r / 2 * (‖h‖ / (‖h‖ + 1)) := by field_simp
      _ = (‖h‖ / (‖h‖ + 1)) * (r / 2) := by ring
      _ ≤ 1 * (r / 2) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = r / 2 := by ring
      _ < r := by linarith
  have hAEdisk := ae_bound_on_affine_disk ha hballU hdom hmap
  let Fline : ℂ → α → ℂ := fun z t => L (a t (u + z • h))
  let Fderiv : ℂ → α → ℂ := fun z t => deriv (fun w : ℂ => L (a t (u + w • h))) z
  have hLineAnalytic (t : α) (ht : AnalyticOnNhd ℂ (a t) U) :
      AnalyticOnNhd ℂ (fun z : ℂ => L (a t (u + z • h))) (closedBall 0 (2 * δ)) := by
    intro z hz
    have hz' : ‖z‖ ≤ 2 * δ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz
    have hu' : u + z • h ∈ U := hballU (hmap z hz')
    have hfa : AnalyticAt ℂ (a t) (u + z • h) := ht _ hu'
    have hline : AnalyticAt ℂ (fun w : ℂ => u + w • h) z := affineLine_analyticAt u h z
    exact AnalyticAt.comp (g := fun y : E => L (a t y)) (f := fun w : ℂ => u + w • h)
      (AnalyticAt.comp (g := fun y : F => L y) (f := a t) (L.analyticAt _) hfa) hline
  have hFmeas (z : ℂ) (hz : z ∈ ball (0 : ℂ) δ) : AEStronglyMeasurable (Fline z) μ := by
    dsimp [Fline]
    have hz0 : ‖z‖ < δ := by simpa [mem_ball_iff_norm] using hz
    have hz' : ‖z‖ ≤ 2 * δ := by linarith
    exact L.continuous.comp_aestronglyMeasurable
      (hmeas (u + z • h) (hballU (hmap z hz')))
  have hFint0 : Integrable (Fline 0) μ := by
    have hbound0 := hdom u (mem_ball_self hr)
    have hvec : Integrable (fun t => a t u) μ := (hg.mono' (hmeas u hu) hbound0)
    have hmeasL : AEStronglyMeasurable (fun t => L (a t u)) μ :=
      L.continuous.comp_aestronglyMeasurable (hmeas u hu)
    have hnorm : ∀ᵐ t ∂μ, ‖L (a t u)‖ ≤ ‖L‖ * ‖a t u‖ :=
      Filter.Eventually.of_forall fun t => L.le_opNorm _
    have hLint : Integrable (fun t => L (a t u)) μ := by
      apply (hvec.norm.const_mul ‖L‖).mono' hmeasL
      filter_upwards [hnorm] with t ht
      simpa [mul_comm] using ht
    simpa [Fline] using hLint
  have hFprime_meas : AEStronglyMeasurable (Fderiv 0) μ := by
    classical
    obtain ⟨q, hq, hqne⟩ : ∃ q : ℕ → ℂ,
        Tendsto q atTop (𝓝 0) ∧ ∀ᶠ n in atTop, q n ≠ 0 := by
      simpa only [tendsto_nhdsWithin_iff] using!
        (exists_seq_tendsto (𝓝[≠] (0 : ℂ)))
    have hqball : ∀ᶠ n in atTop, q n ∈ ball (0 : ℂ) δ :=
      hq.eventually (ball_mem_nhds 0 hδ)
    let q' : ℕ → ℂ := fun n =>
      if h : q n ∈ ball (0 : ℂ) δ then q n else (δ / 2 : ℝ)
    have hq'ball : ∀ n, q' n ∈ ball (0 : ℂ) δ := by
      intro n
      dsimp [q']
      split_ifs with hn
      · exact hn
      · have hhalf : δ / 2 < δ := by linarith
        simpa only [mem_ball_iff_norm, sub_zero, Complex.norm_real,
          Real.norm_of_nonneg (by positivity : 0 ≤ δ / 2)] using hhalf
    have hq'ne : ∀ᶠ n in atTop, q' n ≠ 0 := by
      filter_upwards [hqball, hqne] with n hn hnn
      have hval : q' n = q n := by dsimp [q']; simp [hn]
      rw [hval]
      exact hnn
    have hq'eq : q' =ᶠ[atTop] q := by
      filter_upwards [hqball] with n hn
      have hval : q' n = q n := by dsimp [q']; simp [hn]
      exact hval
    have hq' : Tendsto q' atTop (𝓝[≠] (0 : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hq.congr' hq'eq.symm, hq'ne⟩
    have hquotMeas (n : ℕ) :
        AEStronglyMeasurable (fun t => (q' n)⁻¹ • (Fline (q' n) t - Fline 0 t)) μ := by
      have hqmeas := hFmeas (q' n) (hq'ball n)
      have hzero := hFmeas 0 (by simp [hδ])
      have hsub : Continuous (fun p : ℂ × ℂ => p.1 - p.2) := continuous_fst.sub continuous_snd
      have hsmul : Continuous (fun z : ℂ => (q' n)⁻¹ • z) := continuous_const_smul _
      have hcombine : Continuous (fun p : ℂ × ℂ => (q' n)⁻¹ • (p.1 - p.2)) := hsmul.comp hsub
      exact hcombine.comp_aestronglyMeasurable (hqmeas.prodMk hzero)
    have hquotLimit : ∀ᵐ t ∂μ,
        Tendsto (fun n => (q' n)⁻¹ • (Fline (q' n) t - Fline 0 t)) atTop
          (𝓝 (Fderiv 0 t)) := by
      filter_upwards [ha] with t ht
      have hz0 : ‖(0 : ℂ)‖ ≤ 2 * δ := by norm_num; positivity
      have hlineAt : AnalyticAt ℂ (fun z : ℂ => L (a t (u + z • h))) 0 :=
        hLineAnalytic t ht 0 (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz0)
      have hderiv := hlineAt.differentiableAt.hasDerivAt
      have hslope := hderiv.tendsto_slope_zero.comp hq'
      simpa [Fline, Fderiv, Function.comp_def] using hslope
    exact aestronglyMeasurable_of_tendsto_ae atTop hquotMeas hquotLimit
  let bound : α → ℝ := fun t => (‖L‖ / δ) * |g t|
  have hboundInt : Integrable bound μ := by
    dsimp [bound]
    exact hg.abs.const_mul (‖L‖ / δ)
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ ball (0 : ℂ) δ, ‖Fderiv z t‖ ≤ bound t := by
    filter_upwards [ha, hAEdisk] with t ht hdisk
    intro z hz
    have hclosed :
        AnalyticOnNhd ℂ (fun w : ℂ => L (a t (u + w • h))) (closedBall z δ) := by
      intro w hw
      apply hLineAnalytic t ht w
      have hwz : ‖w - z‖ ≤ δ := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
      have hz0 : ‖z‖ < δ := by simpa [mem_ball_iff_norm] using hz
      have hw0 : ‖w‖ ≤ 2 * δ := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by congr 1 <;> abel
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ δ + δ := add_le_add hwz hz0.le
          _ = 2 * δ := by ring
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hw0
    have hcircle : ∀ w ∈ sphere z δ,
        ‖L (a t (u + w • h))‖ ≤ ‖L‖ * |g t| := by
      intro w hw
      have hwd : w ∈ closedBall z δ := sphere_subset_closedBall hw
      have hwz : ‖w - z‖ ≤ δ := by
        simpa only [Metric.mem_closedBall, dist_eq_norm] using hwd
      have hz0 : ‖z‖ < δ := by simpa [mem_ball_iff_norm] using hz
      have hw0 : ‖w‖ ≤ 2 * δ := by
        calc
          ‖w‖ = ‖(w - z) + z‖ := by congr 1 <;> abel
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ δ + δ := add_le_add hwz hz0.le
          _ = 2 * δ := by ring
      calc
        ‖L (a t (u + w • h))‖ ≤ ‖L‖ * ‖a t (u + w • h)‖ := L.le_opNorm _
        _ ≤ ‖L‖ * |g t| := mul_le_mul_of_nonneg_left (hdisk w hw0) (norm_nonneg _)
    have hcauchy := NlsGge.Atomic.LIB.cauchy_iterated_deriv_bound 1 hδ hclosed hcircle
    have hcauchy' :
        ‖deriv (fun w : ℂ => L (a t (u + w • h))) z‖ ≤ ‖L‖ * |g t| / δ := by
      simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, pow_one, one_mul] using hcauchy
    dsimp [Fderiv, bound]
    calc
      ‖deriv (fun w : ℂ => L (a t (u + w • h))) z‖ ≤ ‖L‖ * |g t| / δ := hcauchy'
      _ = (‖L‖ / δ) * |g t| := by ring
  have hdiff : ∀ᵐ t ∂μ, ∀ z ∈ ball (0 : ℂ) δ,
      HasDerivAt (Fline · t) (Fderiv z t) z := by
    filter_upwards [ha] with t ht
    intro z hz
    have hz0 : ‖z‖ < δ := by simpa [mem_ball_iff_norm] using hz
    have hz' : ‖z‖ ≤ 2 * δ := by linarith
    have hline := hLineAnalytic t ht z
      (by simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hz')
    simpa [Fline, Fderiv] using hline.differentiableAt.hasDerivAt
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Fline) (F' := Fderiv) (μ := μ) (s := ball (0 : ℂ) δ) (x₀ := 0)
    (bound := bound)
    (ball_mem_nhds 0 hδ)
    (by
      filter_upwards [ball_mem_nhds 0 hδ] with z hz
      exact hFmeas z hz)
    hFint0 hFprime_meas hbound hboundInt hdiff
  have heq :
      (fun z : ℂ => L (∫ t, a t (u + z • h) ∂μ)) =ᶠ[𝓝 0]
      (fun z => ∫ t, Fline z t ∂μ) := by
    filter_upwards [ball_mem_nhds 0 hδ] with z hz
    have hz0 : ‖z‖ < δ := by simpa [mem_ball_iff_norm] using hz
    have hz' : ‖z‖ ≤ 2 * δ := by linarith
    have hvec : Integrable (fun t => a t (u + z • h)) μ :=
      hg.mono' (hmeas (u + z • h) (hballU (hmap z hz')))
        (hdom (u + z • h) (hmap z hz'))
    rw [ContinuousLinearMap.integral_comp_comm L hvec]
  refine ⟨δ, hδ, ?_⟩
  exact hparam.2.congr_of_eventuallyEq heq

/-- A parameter integral with a locally integrable majorant is analytic.  The
exceptional set in the bound may depend on each individual parameter value;
the proof only synchronizes it on each separable affine complex disk. -/
theorem analyticOn_integral_of_locally_dominated
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {μ : Measure α} {U : Set E} {a : α → E → F}
    (hU : IsOpen U)
    (ha : ∀ᵐ t ∂μ, AnalyticOnNhd ℂ (a t) U)
    (hmeas : ∀ u ∈ U, AEStronglyMeasurable (fun t => a t u) μ)
    (hdom : ∀ u ∈ U, ∃ r > 0, ball u r ⊆ U ∧
      ∃ g : α → ℝ, Integrable g μ ∧
        ∀ v ∈ ball u r, ∀ᵐ t ∂μ, ‖a t v‖ ≤ g t) :
    AnalyticOnNhd ℂ (fun u => ∫ t, a t u ∂μ) U := by
  let f : E → F := fun u => ∫ t, a t u ∂μ
  have hweak : NlsGge.GK38.Lib.WeaklyAnalyticOn f U := by
    intro x hx h L
    let line : ℂ → E := fun z => x + z • h
    let V : Set ℂ := {z | line z ∈ U}
    have hlineC : Continuous line := by fun_prop
    have hVopen : IsOpen V := hU.preimage hlineC
    let q : ℂ → ℂ := fun z => L (f (line z))
    have hdiff : DifferentiableOn ℂ q V := by
      intro ζ hζ
      have hy : line ζ ∈ U := hζ
      rcases hdom (line ζ) hy with ⟨r, hr, hballU, g, hg, hlocal⟩
      obtain ⟨δ, hδ, hD⟩ := scalar_integral_line_hasDerivAt
        (u := line ζ) (h := h)
        ha hmeas hy hr hballU hg hlocal L
      let qshift : ℂ → ℂ := fun w =>
        L (f ((line ζ) + (w - ζ) • h))
      have harg (w : ℂ) : line w = (line ζ) + (w - ζ) • h := by
        dsimp [line]
        calc
          x + w • h = x + (ζ + (w - ζ)) • h := by congr 2 <;> ring
          _ = (x + ζ • h) + (w - ζ) • h := by rw [add_smul]; abel
      have hD' : HasDerivAt
          (fun z : ℂ => L (∫ t, a t (line ζ + z • h) ∂μ))
          (∫ t, deriv (fun w : ℂ => L (a t (line ζ + w • h))) 0 ∂μ) (ζ - ζ) := by
        simpa using hD
      have hshift : HasDerivAt qshift
          (∫ t, deriv (fun w : ℂ => L (a t ((line ζ) + w • h))) 0 ∂μ) ζ := by
        simpa [qshift, f] using hD'.comp_sub_const ζ ζ
      have heq : q =ᶠ[𝓝 ζ] qshift := by
        filter_upwards with w
        change L (f (line w)) = L (f ((line ζ) + (w - ζ) • h))
        rw [harg w]
      exact (hshift.congr_of_eventuallyEq heq).differentiableAt.differentiableWithinAt
    have hqanalytic : AnalyticOnNhd ℂ q V :=
      (Complex.analyticOnNhd_iff_differentiableOn hVopen).2 hdiff
    have hzero : (0 : ℂ) ∈ V := by simpa [V, line] using hx
    simpa [q, f, line] using hqanalytic 0 hzero
  have hlocbdd : NlsGge.GK38.Lib.LocBdd U f := by
    intro u hu
    rcases hdom u hu with ⟨r, hr, hballU, g, hg, hlocal⟩
    refine ⟨r, hr, ∫ t, |g t| ∂μ, ?_⟩
    intro v hv
    have hbound : ∀ᵐ t ∂μ, ‖a t v‖ ≤ |g t| :=
      (hlocal v hv).mono fun t ht => ht.trans (le_abs_self _)
    have hvec : Integrable (fun t => a t v) μ :=
      (hg.abs).mono' (hmeas v (hballU hv)) hbound
    have hnorm : ‖∫ t, a t v ∂μ‖ ≤ ∫ t, |g t| ∂μ := by
      calc
        ‖∫ t, a t v ∂μ‖ ≤ ∫ t, ‖a t v‖ ∂μ := norm_integral_le_integral_norm _
        _ ≤ ∫ t, |g t| ∂μ := integral_mono_ae hvec.norm hg.abs hbound
    simpa [f] using hnorm
  exact analyticOnNhd_of_weakAnalytic_locallyBounded hU hweak hlocbdd

/-- The global-majorant formulation from the packet follows from the local
theorem by shrinking a parameter ball inside the open domain. -/
theorem analyticOn_integral_of_dominated
    {α E F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {μ : Measure α} {U : Set E} {a : α → E → F} {g : α → ℝ}
    (hU : IsOpen U)
    (ha : ∀ᵐ t ∂μ, AnalyticOnNhd ℂ (a t) U)
    (hg : Integrable g μ)
    (hdom : ∀ u ∈ U, ∀ᵐ t ∂μ, ‖a t u‖ ≤ g t)
    (hmeas : ∀ u ∈ U, AEStronglyMeasurable (fun t => a t u) μ) :
    AnalyticOnNhd ℂ (fun u => ∫ t, a t u ∂μ) U := by
  apply analyticOn_integral_of_locally_dominated hU ha hmeas
  intro u hu
  rcases Metric.mem_nhds_iff.mp (hU.mem_nhds hu) with ⟨r, hr, hball⟩
  exact ⟨r, hr, hball, g, hg, fun v hv => hdom v (hball hv)⟩

/-- The local majorant `C t^(-1/2)` is integrable on `(0,1)`, so the same
analyticity result applies to the endpoint-singular spectral weight. -/
theorem analyticOn_integral_of_rpow_half_locally_dominated
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set E} {a : ℝ → E → F} (C : ℝ) (hC : 0 ≤ C)
    (hU : IsOpen U)
    (ha : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)), AnalyticOnNhd ℂ (a t) U)
    (hmeas : ∀ u ∈ U,
      AEStronglyMeasurable (fun t => a t u) (volume.restrict (Ioo (0 : ℝ) 1)))
    (hdom : ∀ u ∈ U, ∃ r > 0, ball u r ⊆ U ∧
      ∀ v ∈ ball u r, ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
        ‖a t v‖ ≤ C * Real.rpow t (-1 / 2)) :
    AnalyticOnNhd ℂ (fun u => ∫ t, a t u ∂(volume.restrict (Ioo (0 : ℝ) 1))) U := by
  have hpow : Integrable (fun t : ℝ => Real.rpow t (-1 / 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    change IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioo (0 : ℝ) 1) volume
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 / 2 : ℝ)) (t := 1) (by norm_num)]
    norm_num
  have hg : Integrable (fun t : ℝ => C * Real.rpow t (-1 / 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hCeq : C = |C| := (abs_of_nonneg hC).symm
    rw [hCeq]
    exact hpow.const_mul |C|
  apply analyticOn_integral_of_locally_dominated hU ha hmeas
  intro u hu
  rcases hdom u hu with ⟨r, hr, hballU, hlocal⟩
  exact ⟨r, hr, hballU, (fun t : ℝ => C * Real.rpow t (-1 / 2)), hg, hlocal⟩

end

end NlsGge.Atomic.G4
