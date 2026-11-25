import QuantumNLS.L1TransferParameter

/-! Entire parameter dependence of the actual measurable-coefficient Volterra
series. Cauchy's estimate supplies an integrable derivative majorant; no
continuous representative or trace identity is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory Filter Topology Set
namespace QuantumNLS.L1TransferHolomorphic

variable {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace α] {μ : Measure α}

omit [CompleteSpace E] in
/-- Measurability of the parameter derivative, obtained as a sequential
limit of measurable difference quotients. -/
theorem measurable_parameter_deriv (F : ℂ → α → E)
    (hm : ∀ z, AEStronglyMeasurable (F z) μ)
    (hd : ∀ᵐ t ∂μ, Differentiable ℂ (fun z => F z t)) (z₀ : ℂ) :
    AEStronglyMeasurable (fun t => deriv (fun z => F z t) z₀) μ := by
  let h : ℕ → ℂ := fun n => ((n : ℂ) + 1)⁻¹
  have ht : Tendsto h atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
          Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0))
      simpa [h, one_div, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hh
    · exact Filter.Eventually.of_forall (fun n => by simp [h]; exact_mod_cast (by omega : n + 1 ≠ 0))
  apply aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun n t => (h n)⁻¹ • (F (z₀ + h n) t - F z₀ t))
  · intro n
    exact ((hm _).sub (hm _)).const_smul _
  · filter_upwards [hd] with t ht'
    exact (ht' z₀).hasDerivAt.tendsto_slope_zero.comp ht

omit [CompleteSpace E] in
/-- Local domination of entire integrands suffices for differentiating an
integral. The radius-two bound yields a radius-one derivative bound. -/
theorem differentiableAt_integral (F : ℂ → α → E) (z₀ : ℂ) (g : α → ℝ)
    (hm : ∀ z, AEStronglyMeasurable (F z) μ)
    (hi : Integrable (F z₀) μ) (hg : Integrable g μ)
    (hd : ∀ᵐ t ∂μ, Differentiable ℂ (fun z => F z t))
    (hb : ∀ᵐ t ∂μ, ∀ z ∈ Metric.closedBall z₀ 2, ‖F z t‖ ≤ g t) :
    DifferentiableAt ℂ (fun z => ∫ t, F z t ∂μ) z₀ := by
  have hbound : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball z₀ 1,
      ‖deriv (fun w => F w t) z‖ ≤ g t := by
    filter_upwards [hd, hb] with t ht hbt
    intro z hz
    have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (by norm_num : (0 : ℝ) < 1) ht.diffContOnCl (C := g t) (c := z) (fun w hw => by
        apply hbt w
        change dist w z₀ ≤ 2
        have hw' : dist w z = 1 := hw
        have hz' : dist z z₀ < 1 := hz
        linarith [dist_triangle w z z₀])
    simpa using hh
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall hm) hi (measurable_parameter_deriv F hm hd z₀)
    hbound hg (by
      filter_upwards [hd] with t ht
      exact fun z _ => (ht z).hasDerivAt)).2.differentiableAt

section Algebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
  [CompleteSpace 𝔸]
local instance : NormedAlgebra ℝ 𝔸 := NormedAlgebra.restrictScalars ℝ ℂ 𝔸
variable {A : ℂ → ℝ → 𝔸} {L : ℝ}
open QuantumNLS.LinearFundamental QuantumNLS.L1SpatialTransfer

/-- Entirety of each Volterra term under locally uniform L1 domination. -/
theorem differentiable_dyson (hL : 0 ≤ L)
    (hA : ∀ z, IntervalIntegrable (A z) volume 0 L)
    (hd : ∀ t ∈ Icc 0 L, Differentiable ℂ (fun z => A z t))
    (hb : ∀ z₀ : ℂ, ∃ g : ℝ → ℝ, IntervalIntegrable g volume 0 L ∧
      ∀ z ∈ Metric.closedBall z₀ 2, ∀ t ∈ Icc 0 L, ‖A z t‖ ≤ g t) :
    ∀ n, ∀ x ∈ Icc 0 L, Differentiable ℂ (fun z => dyson (A z) n x) := by
  intro n
  induction n with
  | zero => intro x hx; exact differentiable_const _
  | succ n ih =>
    intro x hx z₀
    obtain ⟨g, hg, hbg⟩ := hb z₀
    let C := ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..L, g t) ^ n / (n.factorial : ℝ)
    have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) L := by
      rw [uIcc_of_le hx.1, uIcc_of_le hL]
      exact Icc_subset_Icc_right hx.2
    have hi : ∀ z, Integrable (fun t => A z t * dyson (A z) n t)
        (volume.restrict (Ioc 0 x)) := fun z =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mp
        ((integrable_dyson_product (hA z) n).mono_set hsub)
    have hgi : Integrable (fun t => g t * C) (volume.restrict (Ioc 0 x)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mp
        ((hg.mono_set hsub).mul_const C)
    have hh := differentiableAt_integral
      (fun z t => A z t * dyson (A z) n t) z₀ (fun t => g t * C)
      (fun z => (hi z).aestronglyMeasurable) (hi z₀) hgi (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have htL : t ∈ Icc 0 L := ⟨ht.1.le, ht.2.trans hx.2⟩
        exact (hd t htL).mul (ih t htL)) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have htL : t ∈ Icc 0 L := ⟨ht.1.le, ht.2.trans hx.2⟩
        intro z hz
        exact (norm_mul_le _ _).trans (mul_le_mul
          (hbg z hz t htL)
          (L1TransferParameter.norm_dyson_le hL (fun z _ => hA z) hg hbg hz n htL)
          (norm_nonneg _) ((norm_nonneg _).trans (hbg z hz t htL))))
    simpa only [dyson, intervalIntegral.integral_of_le hx.1] using hh

/-- Entirety of the summed measurable-coefficient transfer. Only the
original factorial bound is needed to sum the holomorphic terms. -/
theorem differentiable_transfer (hL : 0 ≤ L)
    (hA : ∀ z, IntervalIntegrable (A z) volume 0 L)
    (hd : ∀ t ∈ Icc 0 L, Differentiable ℂ (fun z => A z t))
    (hb : ∀ z₀ : ℂ, ∃ g : ℝ → ℝ, IntervalIntegrable g volume 0 L ∧
      ∀ z ∈ Metric.closedBall z₀ 2, ∀ t ∈ Icc 0 L, ‖A z t‖ ≤ g t)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    Differentiable ℂ (fun z => transfer (A z) x) := by
  intro z₀
  obtain ⟨g, hg, hbg⟩ := hb z₀
  have hs : Summable (fun n : ℕ =>
      ‖(1 : 𝔸)‖ * (∫ t in (0 : ℝ)..L, g t) ^ n / (n.factorial : ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (∫ t in (0 : ℝ)..L, g t)).mul_left ‖(1 : 𝔸)‖
  have hh := Complex.differentiableOn_tsum_of_summable_norm hs
    (fun n => (differentiable_dyson hL hA hd hb n x hx).differentiableOn
      (s := Metric.ball z₀ 2)) Metric.isOpen_ball (fun n z hz =>
        L1TransferParameter.norm_dyson_le hL (fun z _ => hA z) hg hbg
          (Metric.ball_subset_closedBall hz) n hx)
  exact hh.differentiableAt (Metric.ball_mem_nhds z₀ (by norm_num : (0 : ℝ) < 2))
end Algebra

end QuantumNLS.L1TransferHolomorphic

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.L1TransferHolomorphic.measurable_parameter_deriv
#print axioms QuantumNLS.L1TransferHolomorphic.differentiableAt_integral
#print axioms QuantumNLS.L1TransferHolomorphic.differentiable_dyson
#print axioms QuantumNLS.L1TransferHolomorphic.differentiable_transfer

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.L1TransferHolomorphic." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
