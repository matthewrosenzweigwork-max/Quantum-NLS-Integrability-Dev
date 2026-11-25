import Mathlib

                                                                                         
                                                             
                                                                                                 
                                                                                                      
                                                                                                                      
               

set_option autoImplicit false

namespace NlsGge.Atomic.T.T019

open MeasureTheory

theorem clause2 (r : ℕ) (c : Fin r → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ C : ℝ, ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) → ∏ i, x i ≤ C * Real.exp (∑ i, c i * x i) := by
  refine ⟨∏ i, (c i)⁻¹, fun x hx => ?_⟩
  have hle : ∀ i, x i ≤ (c i)⁻¹ * Real.exp (c i * x i) := by
    intro i
    have h1 : c i * x i ≤ Real.exp (c i * x i) := by
      have := Real.add_one_le_exp (c i * x i)
      linarith
    calc x i = (c i)⁻¹ * (c i * x i) := by
          rw [← mul_assoc, inv_mul_cancel₀ (hc i).ne', one_mul]
      _ ≤ (c i)⁻¹ * Real.exp (c i * x i) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (hc i).le)
  calc ∏ i, x i ≤ ∏ i, ((c i)⁻¹ * Real.exp (c i * x i)) :=
        Finset.prod_le_prod₀ (fun i _ => hx i) (fun i _ => hle i)
    _ = (∏ i, (c i)⁻¹) * Real.exp (∑ i, c i * x i) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]

theorem clause1 (k : ℕ) (a C : ℝ) (ha : 0 < a) :
    ∃ ε : ℝ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
        (q : Ω → ℝ), Measurable q → (∀ x, 0 ≤ q x) →
        MeasureTheory.Integrable (fun x => Real.exp (a * q x)) μ →
        ∫ x, Real.exp (a * q x) ∂μ ≤ C →
        ∀ R : ℝ, ∫⁻ x, ENNReal.ofReal (q x ^ k * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x) ∂μ ≤
          ENNReal.ofReal (ε R) := by
  have ha' : a ≠ 0 := ha.ne'
  set K : ℝ := (k.factorial : ℝ) * (4 / a) ^ k with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨fun R => K * Real.exp (-(a * R) / 4) * ((C + 1) / 2), ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun R : ℝ => a * R / 4) Filter.atTop Filter.atTop :=
      (Filter.tendsto_id.const_mul_atTop ha).atTop_div_const (by norm_num)
    have h2 : Filter.Tendsto (fun R : ℝ => Real.exp (-(a * R / 4))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
    have h3 := ((h2.const_mul K).mul_const ((C + 1) / 2))
    rw [mul_zero, zero_mul] at h3
    refine h3.congr (fun R => ?_)
    congr 2
    ring
  · intro Ω _ μ _ q hq hq0 hint hC R
    have hpow : ∀ x, q x ^ k ≤ K * Real.exp (a * q x / 4) := by
      intro x
      have hx0 : 0 ≤ a * q x / 4 := by
        have := hq0 x
        positivity
      have h1 : (a * q x / 4) ^ k / (k.factorial : ℝ) ≤ Real.exp (a * q x / 4) :=
        Real.pow_div_factorial_le_exp (a * q x / 4) hx0 k
      have h2 : q x ^ k = K * ((a * q x / 4) ^ k / (k.factorial : ℝ)) := by
        have hsimp : (4 / a) * (a * q x / 4) = q x := by field_simp
        have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
        rw [hK]
        calc q x ^ k = ((4 / a) * (a * q x / 4)) ^ k := by rw [hsimp]
          _ = (4 / a) ^ k * (a * q x / 4) ^ k := mul_pow _ _ _
          _ = (k.factorial : ℝ) * (4 / a) ^ k * ((a * q x / 4) ^ k / (k.factorial : ℝ)) := by
              field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hK0
    have hI0 : ∀ x, 0 ≤ Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : R < q x
      · rw [Set.indicator_of_mem (show x ∈ {x | R < q x} from hx)]
        norm_num
      · rw [Set.indicator_of_notMem (show x ∉ {x | R < q x} from hx)]
    have hind : ∀ x, Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x ≤
        Real.exp (a * (q x - R) / 4) := by
      intro x
      by_cases hx : R < q x
      · rw [Set.indicator_of_mem (show x ∈ {x | R < q x} from hx)]
        have h0 : 0 ≤ a * (q x - R) / 4 := by
          have := sub_pos.2 hx
          have : 0 ≤ a * (q x - R) := mul_nonneg ha.le this.le
          linarith
        simpa using Real.one_le_exp h0
      · rw [Set.indicator_of_notMem (show x ∉ {x | R < q x} from hx)]
        exact (Real.exp_pos _).le
    have hE : ∀ x, Real.exp (a * q x / 4) * Real.exp (a * (q x - R) / 4) =
        Real.exp (-(a * R) / 4) * Real.exp (a * q x / 2) := by
      intro x
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hAM : ∀ x, Real.exp (a * q x / 2) ≤ (Real.exp (a * q x) + 1) / 2 := by
      intro x
      have hsq : Real.exp (a * q x) = Real.exp (a * q x / 2) * Real.exp (a * q x / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      nlinarith [sq_nonneg (Real.exp (a * q x / 2) - 1)]
    set h : Ω → ℝ := fun x => K * Real.exp (-(a * R) / 4) * ((Real.exp (a * q x) + 1) / 2) with hh
    have hdom : ∀ x, q x ^ k * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x ≤ h x := by
      intro x
      have hstep1 : q x ^ k * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x ≤
          (K * Real.exp (a * q x / 4)) * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x :=
        mul_le_mul_of_nonneg_right (hpow x) (hI0 x)
      have hstep2 : (K * Real.exp (a * q x / 4)) * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x ≤
          (K * Real.exp (a * q x / 4)) * Real.exp (a * (q x - R) / 4) :=
        mul_le_mul_of_nonneg_left (hind x) (mul_nonneg hK0 (Real.exp_pos _).le)
      have hstep3 : (K * Real.exp (a * q x / 4)) * Real.exp (a * (q x - R) / 4) =
          K * (Real.exp (-(a * R) / 4) * Real.exp (a * q x / 2)) := by
        rw [← hE x]
        ring
      have hstep4 : K * (Real.exp (-(a * R) / 4) * Real.exp (a * q x / 2)) ≤
          K * (Real.exp (-(a * R) / 4) * ((Real.exp (a * q x) + 1) / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hAM x) (Real.exp_pos _).le) hK0
      have hstep5 : K * (Real.exp (-(a * R) / 4) * ((Real.exp (a * q x) + 1) / 2)) = h x := by
        rw [hh]
        ring
      linarith
    have hfun : h = fun x => (K * Real.exp (-(a * R) / 4) / 2) * Real.exp (a * q x) +
        (K * Real.exp (-(a * R) / 4) / 2) := by
      funext x
      rw [hh]
      ring
    have hhint : MeasureTheory.Integrable h μ := by
      rw [hfun]
      exact (hint.const_mul _).add (MeasureTheory.integrable_const _)
    have hhnn : 0 ≤ h := by
      intro x
      have h1 : 0 ≤ K * Real.exp (-(a * R) / 4) := mul_nonneg hK0 (Real.exp_pos _).le
      have h2 : 0 ≤ (Real.exp (a * q x) + 1) / 2 := by
        have := Real.exp_pos (a * q x)
        linarith
      exact mul_nonneg h1 h2
    have hle : ∫⁻ x, ENNReal.ofReal (q x ^ k * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x) ∂μ ≤
        ∫⁻ x, ENNReal.ofReal (h x) ∂μ :=
      MeasureTheory.lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hdom x))
    have hhnn' : 0 ≤ᵐ[μ] h := Filter.Eventually.of_forall hhnn
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hhint hhnn'] at hle
    refine hle.trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : ∫ x, h x ∂μ = K * Real.exp (-(a * R) / 4) * ((∫ x, Real.exp (a * q x) ∂μ + 1) / 2) := by
      rw [hfun, MeasureTheory.integral_add (hint.const_mul _) (MeasureTheory.integrable_const _),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
      simp only [MeasureTheory.probReal_univ, smul_eq_mul, mul_one]
      ring
    rw [hI]
    have hK' : 0 ≤ K * Real.exp (-(a * R) / 4) := mul_nonneg hK0 (Real.exp_pos _).le
    have hC' : (∫ x, Real.exp (a * q x) ∂μ + 1) / 2 ≤ (C + 1) / 2 := by linarith
    exact mul_le_mul_of_nonneg_left hC' hK'

theorem T019_helper : ((
  (∀ (k : ℕ) (a C : ℝ), 0 < a → ∃ ε : ℝ → ℝ, Filter.Tendsto ε Filter.atTop (nhds 0) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
      (q : Ω → ℝ), Measurable q → (∀ x, 0 ≤ q x) →
      MeasureTheory.Integrable (fun x => Real.exp (a * q x)) μ →
      ∫ x, Real.exp (a * q x) ∂μ ≤ C →
      ∀ R : ℝ, ∫⁻ x, ENNReal.ofReal (q x ^ k * Set.indicator {x | R < q x} (fun _ => (1 : ℝ)) x) ∂μ ≤
        ENNReal.ofReal (ε R)) ∧
  (∀ (r : ℕ) (c : Fin r → ℝ), (∀ i, 0 < c i) →
    ∃ C : ℝ, ∀ x : Fin r → ℝ, (∀ i, 0 ≤ x i) → ∏ i, x i ≤ C * Real.exp (∑ i, c i * x i))
  : Prop)) := by
  exact ⟨fun k a C ha => clause1 k a C ha, fun r c hc => clause2 r c hc⟩

end NlsGge.Atomic.T.T019
