import Mathlib

/-!
# R-F611926F (R1), real-variable analysis: integration by parts for `L¹` primitives

The one analytic tool for the identification `R_z^ρ = (D_ρ − iz)^{-1}`: for `u ∈ L¹(0,x)` and `c ∈ ℂ`
```
∫₀ˣ c e^{ct} (∫₀ᵗ u) dt = ∫₀ˣ u(s) (e^{cx} − e^{cs}) ds,
```
(Fubini on the triangle), hence `e^{cx} ∫₀ˣ u = ∫₀ˣ (c e^{ct} ∫₀ᵗ u + e^{ct} u(t)) dt` (`ibp`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace QuantumNLS.HaarResolventAnalysis

theorem hasDerivAt_cexp_mul (c : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (c * Complex.exp (c * t)) t := by
  have h : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
  have := h.cexp
  simpa [mul_comm] using this

theorem integral_cexp_mul (c : ℂ) {a b : ℝ} :
    ∫ t in a..b, c * Complex.exp (c * t) = Complex.exp (c * b) - Complex.exp (c * a) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_cexp_mul c t) ?_
  exact (Continuous.intervalIntegrable (by fun_prop) _ _)

theorem ibp_swap (c : ℂ) {u : ℝ → ℂ} {x : ℝ} (hx : 0 ≤ x) (hu : IntervalIntegrable u volume 0 x) :
    ∫ t in (0 : ℝ)..x, c * Complex.exp (c * t) * ∫ s in (0 : ℝ)..t, u s =
      ∫ s in (0 : ℝ)..x, u s * (Complex.exp (c * x) - Complex.exp (c * s)) := by
  have hu' : IntegrableOn u (Ioc 0 x) := (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 hu
  set μ : Measure ℝ := volume.restrict (Ioc 0 x) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ]; exact ⟨by simp [Real.volume_Ioc]⟩
  let K : ℝ → ℝ → ℂ := fun t s => if s < t then c * Complex.exp (c * t) * u s else 0
  have hKint : Integrable (Function.uncurry K) (μ.prod μ) := by
    have hmeas : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => c * Complex.exp (c * p.1) * u p.2)
          (μ.prod μ) := by
        refine AEStronglyMeasurable.mul ?_
          (hu'.aestronglyMeasurable.comp_quasiMeasurePreserving
            (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)))
        exact (Measurable.aestronglyMeasurable (by fun_prop))
      have h2 := h1.indicator (s := {p : ℝ × ℝ | p.2 < p.1})
        (measurableSet_lt measurable_snd measurable_fst)
      refine h2.congr (Eventually.of_forall (fun p => ?_))
      by_cases hp : p.2 < p.1 <;> simp [K, Function.uncurry, hp, Set.indicator]
    set M : ℝ := ‖c‖ * Real.exp (‖c‖ * x) with hM
    have hg : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * (M * ‖u p.2‖)) (μ.prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod (hu'.norm.const_mul M)
    refine hg.mono' hmeas ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae
      (ae_restrict_mem measurableSet_Ioc : ∀ᵐ t ∂μ, t ∈ Ioc 0 x)] with p hp
    obtain ⟨t, s⟩ := p
    have ht : t ∈ Ioc 0 x := hp
    simp only [Function.uncurry, K]
    by_cases hts : s < t
    · rw [if_pos hts, norm_mul, norm_mul, one_mul]
      have hexp : ‖Complex.exp (c * t)‖ ≤ Real.exp (‖c‖ * x) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        calc (c * (t : ℂ)).re ≤ ‖c * (t : ℂ)‖ := Complex.re_le_norm _
          _ = ‖c‖ * |t| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          _ ≤ ‖c‖ * x := by
            rw [abs_of_pos ht.1]; exact mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
      rw [hM]
      calc ‖c‖ * ‖Complex.exp (c * t)‖ * ‖u s‖
          ≤ ‖c‖ * Real.exp (‖c‖ * x) * ‖u s‖ := by gcongr
        _ = _ := by ring
    · rw [if_neg hts, norm_zero, one_mul]
      positivity
  -- inner integrals
  have hin : ∀ t ∈ Ioc (0 : ℝ) x, ∫ s, K t s ∂μ =
      c * Complex.exp (c * t) * ∫ s in (0 : ℝ)..t, u s := by
    intro t ht
    have hK : ∀ s, K t s = c * Complex.exp (c * t) * (Iio t).indicator u s := fun s => by
      by_cases h : s < t <;> simp [K, Set.indicator, h]
    simp only [hK]
    rw [integral_const_mul, integral_indicator measurableSet_Iio, hμ,
      Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio t ∩ Ioc 0 x = Ioo 0 t := by
      ext s; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans ht.2⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le ht.1.le]
  have hout : ∀ s ∈ Ioc (0 : ℝ) x, ∫ t, K t s ∂μ =
      u s * (Complex.exp (c * x) - Complex.exp (c * s)) := by
    intro s hs
    have hK : ∀ t, K t s = u s * (Ioi s).indicator (fun t : ℝ => c * Complex.exp (c * t)) t :=
      fun t => by
        by_cases h : s < t <;> simp [K, Set.indicator, h, mul_comm, mul_left_comm]
    simp only [hK]
    rw [integral_const_mul, integral_indicator measurableSet_Ioi, hμ,
      Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi s ∩ Ioc 0 x = Ioc s x := by
      ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hs.1.trans h1, h2⟩
    rw [hset, ← intervalIntegral.integral_of_le hs.2, integral_cexp_mul]
  have hfub := integral_integral_swap hKint
  have hL : ∫ t in (0 : ℝ)..x, c * Complex.exp (c * t) * ∫ s in (0 : ℝ)..t, u s =
      ∫ t, ∫ s, K t s ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hx]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hin t ht).symm
  have hR : ∫ s in (0 : ℝ)..x, u s * (Complex.exp (c * x) - Complex.exp (c * s)) =
      ∫ s, ∫ t, K t s ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hx]
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact (hout s hs).symm
  rw [hL, hR]
  exact hfub

/-- Integration by parts for an `L¹` primitive: `e^{cx} ∫₀ˣ u = ∫₀ˣ (c e^{ct} ∫₀ᵗ u + e^{ct} u(t)) dt`. -/
theorem ibp (c : ℂ) {u : ℝ → ℂ} {x : ℝ} (hx : 0 ≤ x) (hu : IntervalIntegrable u volume 0 x) :
    Complex.exp (c * x) * ∫ s in (0 : ℝ)..x, u s =
      ∫ t in (0 : ℝ)..x, (c * Complex.exp (c * t) * (∫ s in (0 : ℝ)..t, u s) +
        Complex.exp (c * t) * u t) := by
  have h1 := ibp_swap c hx hu
  have hcont : Continuous (fun t : ℝ => c * Complex.exp (c * t)) := by fun_prop
  have hint2 : IntervalIntegrable (fun t : ℝ => Complex.exp (c * t) * u t) volume 0 x := by
    have : Continuous (fun t : ℝ => Complex.exp (c * t)) := by fun_prop
    exact hu.continuousOn_mul this.continuousOn
  have hint1 : IntervalIntegrable (fun t : ℝ => c * Complex.exp (c * t) * ∫ s in (0 : ℝ)..t, u s)
      volume 0 x := by
    have hprim : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, u s) (Set.uIcc 0 x) :=
      intervalIntegral.continuousOn_primitive_interval' hu (by simp [hx])
    exact (hcont.continuousOn.mul hprim).intervalIntegrable
  rw [intervalIntegral.integral_add hint1 hint2, h1]
  have h3 : ∫ s in (0 : ℝ)..x, u s * (Complex.exp (c * x) - Complex.exp (c * s)) =
      Complex.exp (c * x) * (∫ s in (0 : ℝ)..x, u s) - (∫ s in (0 : ℝ)..x, Complex.exp (c * s) * u s) := by
    have hA : IntervalIntegrable (fun s : ℝ => u s * Complex.exp (c * x)) volume 0 x :=
      hu.mul_const _
    rw [show (fun s : ℝ => u s * (Complex.exp (c * x) - Complex.exp (c * s))) =
      fun s => u s * Complex.exp (c * x) - Complex.exp (c * s) * u s from
        funext fun s => by ring]
    rw [intervalIntegral.integral_sub hA hint2, intervalIntegral.integral_mul_const]
    ring
  rw [h3]; ring

#print axioms ibp

end QuantumNLS.HaarResolventAnalysis
