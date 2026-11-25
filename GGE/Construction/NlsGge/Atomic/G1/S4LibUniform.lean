import Mathlib
import NlsGge.Atomic.G1.S4LibCauchy

                                                                                               
                                                                                               
                                                                                    
                                                                                               
                                                                                                  
                                                                                   
set_option autoImplicit false
open Metric Set Filter Topology
open scoped ENNReal NNReal

namespace NlsGge.S4Lib

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- The Taylor coefficient series `n ↦ (n!)⁻¹ • D^n f(a)` as a formal multilinear series. -/
noncomputable def taylorSeries (f : E → F) (a : E) : FormalMultilinearSeries ℂ E F :=
  fun n => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n f a

theorem taylorSeries_radius_ge {f : E → F} {a : E} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hM : ∀ z ∈ ball a R, ‖f z‖ ≤ M) :
    ENNReal.ofReal (R / Real.exp 1) ≤ (taylorSeries f a).radius := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hρ : 0 < R / Real.exp 1 := div_pos hR he
  have hr : (((R / Real.exp 1).toNNReal : ℝ≥0) : ℝ) = R / Real.exp 1 :=
    Real.coe_toNNReal _ hρ.le
  have h := (taylorSeries f a).le_radius_of_bound M (r := (R / Real.exp 1).toNNReal) (fun n => by
    rw [hr]
    have h1 := norm_inv_factorial_smul_iteratedFDeriv_le n hR hf hM
    have hMa : 0 ≤ M := (norm_nonneg _).trans (hM a (mem_ball_self hR))
    calc ‖taylorSeries f a n‖ * (R / Real.exp 1) ^ n
        ≤ (M * (Real.exp 1 / R) ^ n) * (R / Real.exp 1) ^ n := by
          gcongr
          exact h1
      _ = M := by
          rw [mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm (Real.exp 1) R,
            div_self (by positivity), one_pow, mul_one])
  exact h

/-- (b1) Taylor expansion on the ball of radius `R / e`. -/
theorem hasFPowerSeriesOnBall_taylorSeries {f : E → F} {a : E} {R M : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball a R)) (hM : ∀ z ∈ ball a R, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (taylorSeries f a) a (ENNReal.ofReal (R / Real.exp 1)) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  set ρ : ℝ := R / Real.exp 1 with hρdef
  have hρ : 0 < ρ := div_pos hR he
  have hρR : ρ < R := by
    rw [hρdef, div_lt_iff₀ he]; nlinarith
  set p := taylorSeries f a with hp
  have hrad : ENNReal.ofReal ρ ≤ p.radius := taylorSeries_radius_ge hR hf hM
  have hradpos : 0 < p.radius := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ) hrad
  obtain ⟨p0, r0, h0⟩ := hf a (mem_ball_self hR)
  have hloc : ∀ y ∈ Metric.eball (0 : E) r0, HasSum (fun n => p n fun _ => y) (f (a + y)) :=
    fun y hy => h0.hasSum_iteratedFDeriv hy
  have hball := p.hasFPowerSeriesOnBall hradpos
  have hg : AnalyticOnNhd ℂ p.sum (ball (0 : E) ρ) := by
    refine hball.analyticOnNhd.mono ?_
    rw [← Metric.eball_ofReal]
    exact Metric.eball_subset_eball hrad
  have hf1 : AnalyticOnNhd ℂ (fun y => f (a + y)) (ball (0 : E) ρ) := by
    intro y hy
    have hy' : a + y ∈ ball a R := by
      rw [mem_ball, dist_eq_norm] at hy ⊢
      have : a + y - a = y := by abel
      rw [this]; rw [sub_zero] at hy; linarith
    exact AnalyticAt.comp (g := f) (f := fun z : E => a + z) (hf (a + y) hy')
      (analyticAt_const.add analyticAt_id)
  have hev : (fun y => f (a + y)) =ᶠ[𝓝 (0 : E)] p.sum := by
    filter_upwards [Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self h0.r_pos)] with y hy
    exact ((hloc y hy).tsum_eq).symm
  have heq := hf1.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball (0 : E) ρ).isPreconnected
    (mem_ball_self hρ) hev
  refine ⟨hrad, ENNReal.ofReal_pos.mpr hρ, fun {y} hy => ?_⟩
  rw [Metric.eball_ofReal] at hy
  have h3 : f (a + y) = p.sum y := heq hy
  have hy2 : y ∈ Metric.eball (0 : E) p.radius := by
    rw [← Metric.eball_ofReal] at hy
    exact Metric.eball_subset_eball hrad hy
  rw [h3]
  exact p.hasSum hy2

/-- (b2) Local form: the limit has a power series on the ball of radius `R / e`. -/
theorem exists_hasFPowerSeriesOnBall_of_tendstoUniformlyOn {f : ℕ → E → F} {g : E → F} {a : E}
    {R M : ℝ} (hR : 0 < R) (hf : ∀ k, AnalyticOnNhd ℂ (f k) (ball a R))
    (hM : ∀ k, ∀ z ∈ ball a R, ‖f k z‖ ≤ M)
    (hlim : TendstoUniformlyOn f g atTop (ball a R)) :
    ∃ q : FormalMultilinearSeries ℂ E F,
      HasFPowerSeriesOnBall g q a (ENNReal.ofReal (R / Real.exp 1)) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  set c : ℝ := Real.exp 1 / R with hc
  have hcpos : 0 < c := div_pos he hR
  have hMa : 0 ≤ M := (norm_nonneg _).trans (hM 0 a (mem_ball_self hR))
  have hp := fun k => hasFPowerSeriesOnBall_taylorSeries hR (hf k) (hM k)
  have hcau : ∀ n, CauchySeq (fun k => taylorSeries (f k) a n) := by
    intro n
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hcn : 0 < c ^ n := pow_pos hcpos n
    have hδ : 0 < ε / (2 * c ^ n) := by positivity
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.1 hlim.uniformCauchySeqOn _ hδ
    refine ⟨N, fun k hk l hl => ?_⟩
    have hdiff : taylorSeries (f k) a n - taylorSeries (f l) a n =
        ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (f k - f l) a := by
      change ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (f k) a -
          ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (f l) a = _
      rw [iteratedFDeriv_sub_apply ((hf k a (mem_ball_self hR)).contDiffAt)
        ((hf l a (mem_ball_self hR)).contDiffAt), smul_sub]
    have hb := norm_inv_factorial_smul_iteratedFDeriv_le n hR ((hf k).sub (hf l))
      (M := ε / (2 * c ^ n)) (fun z hz => by
        have := hN k hk l hl z hz
        rw [dist_eq_norm] at this
        exact this.le)
    rw [dist_eq_norm, hdiff]
    refine lt_of_le_of_lt hb ?_
    rw [← hc]
    calc ε / (2 * c ^ n) * c ^ n = ε / 2 := by field_simp
      _ < ε := by linarith
  choose q hq using fun n => cauchySeq_tendsto_of_complete (hcau n)
  have hqb : ∀ n, ‖q n‖ ≤ M * c ^ n := fun n =>
    le_of_tendsto (hq n).norm (Eventually.of_forall fun k =>
      norm_inv_factorial_smul_iteratedFDeriv_le n hR (hf k) (hM k))
  set Q : FormalMultilinearSeries ℂ E F := q with hQ
  have hρ : 0 < R / Real.exp 1 := div_pos hR he
  have hQrad : ENNReal.ofReal (R / Real.exp 1) ≤ Q.radius := by
    have hr : (((R / Real.exp 1).toNNReal : ℝ≥0) : ℝ) = R / Real.exp 1 :=
      Real.coe_toNNReal _ hρ.le
    refine Q.le_radius_of_bound M (r := (R / Real.exp 1).toNNReal) (fun n => ?_)
    rw [hr]
    calc ‖Q n‖ * (R / Real.exp 1) ^ n ≤ (M * c ^ n) * (R / Real.exp 1) ^ n := by
          gcongr; exact hqb n
      _ = M := by
          rw [hc, mul_assoc, ← mul_pow, div_mul_div_comm, mul_comm (Real.exp 1) R,
            div_self (by positivity), one_pow, mul_one]
  refine ⟨Q, hQrad, ENNReal.ofReal_pos.mpr hρ, fun {y} hy => ?_⟩
  rw [Metric.eball_ofReal, mem_ball_zero_iff] at hy
  have hcy : c * ‖y‖ < 1 := by
    rw [hc, div_mul_eq_mul_div, div_lt_one hR]
    rw [div_eq_mul_inv] at *
    have : ‖y‖ < R / Real.exp 1 := hy
    rw [lt_div_iff₀ he] at this; linarith
  have hsum : Summable (fun n : ℕ => M * (c * ‖y‖) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hcy).mul_left M
  have hdiag : ∀ n (T : ContinuousMultilinearMap ℂ (fun _ : Fin n => E) F),
      ‖T (fun _ => y)‖ ≤ ‖T‖ * ‖y‖ ^ n := by
    intro n T
    have := T.le_opNorm (fun _ => y)
    simpa [Finset.prod_const] using this
  have hbd : ∀ k n, ‖taylorSeries (f k) a n (fun _ => y)‖ ≤ M * (c * ‖y‖) ^ n := by
    intro k n
    calc ‖taylorSeries (f k) a n (fun _ => y)‖ ≤ ‖taylorSeries (f k) a n‖ * ‖y‖ ^ n :=
          hdiag n _
      _ ≤ (M * c ^ n) * ‖y‖ ^ n := by
          gcongr
          exact norm_inv_factorial_smul_iteratedFDeriv_le n hR (hf k) (hM k)
      _ = M * (c * ‖y‖) ^ n := by rw [mul_pow]; ring
  have hlimsum : Tendsto (fun k => ∑' n, taylorSeries (f k) a n (fun _ => y)) atTop
      (𝓝 (∑' n, q n (fun _ => y))) :=
    tendsto_tsum_of_dominated_convergence hsum
      (fun n => ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F
        (fun _ => y)).continuous.tendsto (q n)).comp (hq n))
      (Eventually.of_forall hbd)
  have hyR : y ∈ Metric.eball (0 : E) (ENNReal.ofReal (R / Real.exp 1)) := by
    rw [Metric.eball_ofReal]; exact mem_ball_zero_iff.mpr hy
  have hfk : ∀ k, ∑' n, taylorSeries (f k) a n (fun _ => y) = f k (a + y) := fun k =>
    ((hp k).hasSum hyR).tsum_eq
  simp only [hfk] at hlimsum
  have hay : a + y ∈ ball a R := by
    rw [mem_ball, dist_eq_norm]
    have : a + y - a = y := by abel
    rw [this]
    have : ‖y‖ < R / Real.exp 1 := hy
    have h1 : R / Real.exp 1 < R := by
      have he1 : 1 < Real.exp 1 := by
        have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
        linarith
      rw [div_lt_iff₀ he]; nlinarith
    linarith
  have hlim2 := hlim.tendsto_at hay
  have heq := tendsto_nhds_unique hlim2 hlimsum
  have hsm : Summable (fun n => Q n (fun _ => y)) :=
    Summable.of_norm_bounded hsum (fun n => by
      calc ‖Q n (fun _ => y)‖ ≤ ‖Q n‖ * ‖y‖ ^ n := hdiag n _
        _ ≤ (M * c ^ n) * ‖y‖ ^ n := by gcongr; exact hqb n
        _ = M * (c * ‖y‖) ^ n := by rw [mul_pow]; ring)
  rw [heq]
  exact hsm.hasSum

/-- (b2) Uniform limits of analytic maps with a common bound on a ball are analytic on the ball. -/
theorem analyticOnNhd_of_tendstoUniformlyOn_ball {f : ℕ → E → F} {g : E → F} {a : E}
    {R M : ℝ} (hR : 0 < R) (hf : ∀ k, AnalyticOnNhd ℂ (f k) (ball a R))
    (hM : ∀ k, ∀ z ∈ ball a R, ‖f k z‖ ≤ M)
    (hlim : TendstoUniformlyOn f g atTop (ball a R)) :
    AnalyticOnNhd ℂ g (ball a R) := by
  intro b hb
  have hRb : 0 < R - dist b a := by rw [mem_ball] at hb; linarith
  have hsub : ball b (R - dist b a) ⊆ ball a R := ball_subset_ball' (by linarith)
  obtain ⟨q, hq⟩ := exists_hasFPowerSeriesOnBall_of_tendstoUniformlyOn hRb
    (fun k => (hf k).mono hsub) (fun k z hz => hM k z (hsub hz)) (hlim.mono hsub)
  exact hq.analyticAt

end

end NlsGge.S4Lib
