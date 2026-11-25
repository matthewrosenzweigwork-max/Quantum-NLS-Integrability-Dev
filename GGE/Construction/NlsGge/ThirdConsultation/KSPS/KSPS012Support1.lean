import Mathlib

                                                                                                                    
                                                                                                       
                                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter

namespace NlsGge.ThirdConsultation.KSPS012Support1

theorem fubini_tri {f g : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) :
    ∫ t in (0 : ℝ)..1, f t * ∫ s in t..1, g s =
      ∫ s in (0 : ℝ)..1, g s * ∫ t in (0 : ℝ)..s, f t := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hμ
  have hfi : Integrable f μ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hf; exact hf
  have hgi : Integrable g μ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hg; exact hg
  let G : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun p => f p.1 * g p.2)
  have hGint : Integrable G (μ.prod μ) :=
    (hfi.mul_prod hgi).indicator (measurableSet_lt measurable_fst measurable_snd)
  have hswap := integral_integral_swap (μ := μ) (ν := μ) (f := fun t s => G (t, s)) hGint
  have hL : ∀ t ∈ Ioc (0 : ℝ) 1, ∫ s, G (t, s) ∂μ = f t * ∫ s in t..1, g s := by
    intro t ht
    have hfun : (fun s => G (t, s)) = Set.indicator (Ioi t) (fun s => f t * g s) := by
      funext s
      simp only [G, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioi]
    rw [hfun, integral_indicator measurableSet_Ioi, hμ, Measure.restrict_restrict measurableSet_Ioi]
    have hset : Ioi t ∩ Ioc (0 : ℝ) 1 = Ioc t 1 := by
      ext s; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, by linarith [ht.1], h3⟩
    rw [hset, ← intervalIntegral.integral_of_le ht.2, intervalIntegral.integral_const_mul]
  have hR : ∀ s ∈ Ioc (0 : ℝ) 1, ∫ t, G (t, s) ∂μ = g s * ∫ t in (0 : ℝ)..s, f t := by
    intro s hs
    have hfun : (fun t => G (t, s)) = Set.indicator (Iio s) (fun t => f t * g s) := by
      funext t
      simp only [G, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Iio]
    rw [hfun, integral_indicator measurableSet_Iio, hμ, Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio s ∩ Ioc (0 : ℝ) 1 = Ioo 0 s := by
      ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [hs.2]⟩
    rw [hset, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.1.le,
      intervalIntegral.integral_mul_const, mul_comm]
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_fun measurableSet_Ioc (fun t ht => (hL t ht).symm),
    setIntegral_congr_fun measurableSet_Ioc (fun s hs => (hR s hs).symm)]
  exact hswap

/-- Weighted Cauchy-Schwarz: `(∫ a k)^2 ≤ (∫ a)(∫ a k^2)` for nonnegative `a`. -/
theorem weighted_cs {a k : ℝ → ℝ} (ha0 : ∀ t, 0 ≤ a t)
    (ha : IntervalIntegrable a volume 0 1)
    (hak : IntervalIntegrable (fun t => a t * k t) volume 0 1)
    (hak2 : IntervalIntegrable (fun t => a t * k t ^ 2) volume 0 1) :
    (∫ t in (0 : ℝ)..1, a t * k t) ^ 2 ≤
      (∫ t in (0 : ℝ)..1, a t) * ∫ t in (0 : ℝ)..1, a t * k t ^ 2 := by
  set A := ∫ t in (0 : ℝ)..1, a t with hA
  set B := ∫ t in (0 : ℝ)..1, a t * k t with hB
  set C := ∫ t in (0 : ℝ)..1, a t * k t ^ 2 with hC
  have hq : ∀ x : ℝ, 0 ≤ A * (x * x) + (-2 * B) * x + C := by
    intro x
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, a t * (x - k t) ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one (fun t _ => mul_nonneg (ha0 t) (sq_nonneg _))
    have h1 : ∫ t in (0 : ℝ)..1, a t * (x - k t) ^ 2 =
        x ^ 2 * A - 2 * x * B + C := by
      have : ∀ t : ℝ, a t * (x - k t) ^ 2 =
          x ^ 2 * a t - 2 * x * (a t * k t) + a t * k t ^ 2 := fun t => by ring
      simp_rw [this]
      rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      · exact (ha.const_mul _)
      · exact (hak.const_mul _)
      · exact (ha.const_mul _).sub (hak.const_mul _)
      · exact hak2
    nlinarith [h0, h1]
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

end NlsGge.ThirdConsultation.KSPS012Support1
