import Mathlib
import NlsGge.Atomic.G1.S4Picard
import NlsGge.Atomic.G1.S4LibOpen

/- G1-081 S4 / L1 unconditional (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/S4PicardAnalytic.lean.
   Discharges both hypotheses of `exists_local_complex_analytic_flow_of_hyp`: iterates are carried as
   `AnalyticOnNhd` directly (Riemann-sum approximants analytic; uniform limit via S4Lib.uniformLimitAnalytic_prod).
   Reuses S4Picard's PData, picardIter, riemannApprox, contr, tendstoU_iter, etc. -/
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Atomic.G1081S4Picard
namespace NlsGge.Atomic.G1081S4PicardAnalytic
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : E → E} {a : E} {ρ M τ r : ℝ} {K : NNReal}

lemma riemannApprox_analytic (h : PData F a ρ M τ r K) (hFa : AnalyticOnNhd ℂ F (ball a ρ)) {k : ℕ}
    (hk : AnalyticOnNhd ℂ (picardIter F k) (ball (0:ℂ) τ ×ˢ ball a r)) (n : ℕ) :
    AnalyticOnNhd ℂ (riemannApprox F k n) (ball (0:ℂ) τ ×ˢ ball a r) := by
  have hinner : ∀ j ∈ Finset.range (n+1), AnalyticOnNhd ℂ (fun p : ℂ × E =>
      F (picardIter F k ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2)))
      (ball (0:ℂ) τ ×ˢ ball a r) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hc : ((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ∈ Icc (0:ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]; exact_mod_cast hj'.le
    have hφ : AnalyticOnNhd ℂ (fun p : ℂ × E => ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2))
        (ball (0:ℂ) τ ×ˢ ball a r) := by
      intro p _
      simp only [Complex.real_smul]
      exact AnalyticAt.prod (analyticAt_const.fun_mul analyticAt_fst) analyticAt_snd
    have hmaps : MapsTo (fun p : ℂ × E => ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2))
        (ball (0:ℂ) τ ×ˢ ball a r) (ball (0:ℂ) τ ×ˢ ball a r) := fun p hp =>
      ⟨smul_mem_ball h hp.1 hc, hp.2⟩
    refine hFa.comp (hk.comp hφ hmaps) ?_
    intro p hp
    have hp' := hmaps hp
    exact mem_ball_of_close h hp'.1 hp'.2 ((inv_all h k _ hp'.1 _ hp'.2).1)
  unfold riemannApprox
  intro p hp
  have hs : AnalyticAt ℂ (fun p : ℂ × E => ∑ j ∈ Finset.range (n + 1),
      F (picardIter F k ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2))) p :=
    Finset.analyticAt_fun_sum _ (fun j hj => hinner j hj p hp)
  exact analyticAt_snd.add (analyticAt_fst.smul (hs.const_smul))

lemma analytic_iter (h : PData F a ρ M τ r K) (hFa : AnalyticOnNhd ℂ F (ball a ρ)) (k : ℕ) :
    AnalyticOnNhd ℂ (picardIter F k) (ball (0:ℂ) τ ×ˢ ball a r) := by
  induction k with
  | zero => intro p _; exact analyticAt_snd
  | succ k ih =>
    have hU : IsOpen (ball (0:ℂ) τ ×ˢ ball a r) := isOpen_ball.prod isOpen_ball
    exact NlsGge.S4Lib.uniformLimitAnalytic_prod E hU (fun n => riemannApprox_analytic h hFa ih n)
      (riemannApprox_tendsto h k)

lemma lim_analytic' (h : PData F a ρ M τ r K) (hFa : AnalyticOnNhd ℂ F (ball a ρ)) :
    AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r) :=
  NlsGge.S4Lib.uniformLimitAnalytic_prod E (isOpen_ball.prod isOpen_ball)
    (analytic_iter h hFa) (tendstoU_iter h)

lemma exists_pdata' (hF : AnalyticAt ℂ F a) :
    ∃ (ρ M τ r : ℝ) (K : NNReal), PData F a ρ M τ r K ∧ AnalyticOnNhd ℂ F (ball a ρ) := by
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 hF.eventually_analyticAt
  obtain ⟨K, s, hs, hL⟩ := hF.contDiffAt.exists_lipschitzOnWith
  obtain ⟨ε', hε', hε's⟩ := Metric.mem_nhds_iff.1 hs
  set ρ : ℝ := min ε ε' with hρ
  have hρ0 : 0 < ρ := lt_min hε hε'
  have hb1 : ball a ρ ⊆ ball a ε := ball_subset_ball (min_le_left _ _)
  have hb2 : ball a ρ ⊆ ball a ε' := ball_subset_ball (min_le_right _ _)
  have hKnn : (0:ℝ) ≤ K := K.coe_nonneg
  set M : ℝ := ‖F a‖ + K * ρ with hM
  have hM0 : 0 ≤ M := by positivity
  set τ : ℝ := min (ρ / (4 * (M + 1))) (1 / (2 * ((K:ℝ) + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by positivity) (by positivity)
  refine ⟨ρ, M, τ, ρ / 2, K, ?_, fun x hx => hεs x (hb1 hx)⟩
  have hLip : LipschitzOnWith K F (ball a ρ) := hL.mono (hb2.trans hε's)
  refine ⟨hρ0, fun x hx => (hεs x (hb1 hx)).differentiableAt.differentiableWithinAt, hLip, ?_, hM0, hτ0,
    by positivity, le_rfl, ?_, ?_⟩
  · intro x hx
    have h1 := hLip.dist_le_mul x hx a (mem_ball_self hρ0)
    rw [dist_eq_norm] at h1
    have h2 : dist x a < ρ := hx
    have h3 : ‖F x‖ ≤ ‖F a‖ + ‖F x - F a‖ := by simpa using norm_add_le (F a) (F x - F a)
    nlinarith
  · have h1 : τ ≤ ρ / (4 * (M + 1)) := min_le_left _ _
    have h2 : τ * (M + 1) ≤ ρ / 4 := by
      calc τ * (M + 1) ≤ ρ / (4 * (M + 1)) * (M + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ρ / 4 := by field_simp
    nlinarith
  · have h1 : τ ≤ 1 / (2 * ((K:ℝ) + 1)) := min_le_right _ _
    have h2 : τ * ((K:ℝ) + 1) ≤ 1 / 2 := by
      calc τ * ((K:ℝ) + 1) ≤ 1 / (2 * ((K:ℝ) + 1)) * ((K:ℝ) + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 1 / 2 := by field_simp
    nlinarith
lemma cont_lim_ray' (hLA : AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r))
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    ContinuousOn (fun θ : ℝ => F (picardLim F (θ • t, z))) {θ : ℝ | θ • t ∈ ball (0:ℂ) τ} := by
  have h1 : ContinuousOn (fun θ : ℝ => picardLim F (θ • t, z)) {θ : ℝ | θ • t ∈ ball (0:ℂ) τ} := by
    refine (hLA).continuousOn.comp ?_ (fun θ hθ => ⟨hθ, hz⟩)
    fun_prop
  exact h.hFL.continuousOn.comp h1 (fun θ hθ => lim_mem h hθ hz)

/-- The integral equation for the limit. -/
lemma lim_integral_eq' (hLA : AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r))
    (h : PData F a ρ M τ r K) {t : ℂ} {z : E} (ht : t ∈ ball (0:ℂ) τ) (hz : z ∈ ball a r) :
    picardLim F (t, z) = z + t • ∫ θ in (0:ℝ)..1, F (picardLim F (θ • t, z)) := by
  have hI : ∀ θ ∈ Icc (0:ℝ) 1, θ • t ∈ ball (0:ℂ) τ := fun θ hθ => smul_mem_ball h ht hθ
  have hcL := (cont_lim_ray' hLA h ht hz).mono (fun θ hθ => hI θ hθ)
  have hiL : IntervalIntegrable (fun θ : ℝ => F (picardLim F (θ • t, z))) volume 0 1 :=
    hcL.intervalIntegrable_of_Icc zero_le_one
  set I : E := ∫ θ in (0:ℝ)..1, F (picardLim F (θ • t, z)) with hIdef
  have hIk : Tendsto (fun k => ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) atTop (𝓝 I) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => K * (2 * (τ * M) / 2 ^ n)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul (K * (2 * (τ * M)))
      simpa [div_eq_mul_inv, one_div, inv_pow, mul_assoc] using this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
    obtain ⟨hik, hbk, _⟩ := g_bound h (inv_all h k) ht hz
    rw [← intervalIntegral.integral_sub hik hiL]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun θ : ℝ => F (picardIter F k (θ • t, z)) - F (picardLim F (θ • t, z)))
      (C := K * (2 * (τ * M) / 2 ^ k)) (by
        intro θ hθ
        rw [uIoc_of_le zero_le_one] at hθ
        have hθ' : θ ∈ Icc (0:ℝ) 1 := ⟨hθ.1.le, hθ.2⟩
        have h1 := hI θ hθ'
        have m1 := mem_ball_of_close h h1 hz ((inv_all h k _ h1 z hz).1)
        have m2 := lim_mem h h1 hz
        refine (h.hFL.norm_sub_le m1 m2).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ K.coe_nonneg
        have := dist_iter_lim h (p := (θ • t, z)) ⟨h1, hz⟩ k
        rwa [dist_eq_norm] at this)
    simpa using this
  have hA : Tendsto (fun k => picardIter F (k+1) (t, z)) atTop (𝓝 (picardLim F (t, z))) :=
    (tendsto_add_atTop_iff_nat (f := fun k => picardIter F k (t, z)) 1).2 (tendsto_iter h ⟨ht, hz⟩)
  have hB : Tendsto (fun k => picardIter F (k+1) (t, z)) atTop (𝓝 (z + t • I)) :=
    (tendsto_const_nhds.add (hIk.const_smul t))
  exact tendsto_nhds_unique hA hB

lemma lim_analyticAt_slice' (hLA : AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r))
    (h : PData F a ρ M τ r K) {s : ℂ} (hs : s ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    AnalyticAt ℂ (fun s : ℂ => picardLim F (s, z)) s := by
  have h1 := hLA (s, z) ⟨hs, hz⟩
  have h2 : AnalyticAt ℂ (fun s : ℂ => (s, z)) s := by fun_prop
  exact h1.comp_of_eq h2 rfl

lemma deriv_eq_of_ne' (hLA : AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r))
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) (ht0 : t ≠ 0) {z : E}
    (hz : z ∈ ball a r) :
    deriv (fun s : ℂ => picardLim F (s, z)) t = F (picardLim F (t, z)) := by
  set φ : ℂ → E := fun s => picardLim F (s, z) with hφ
  have hd : HasDerivAt φ (deriv φ t) t := (lim_analyticAt_slice' hLA h ht hz).differentiableAt.hasDerivAt
  set W : Set ℝ := {σ : ℝ | σ • t ∈ ball (0:ℂ) τ} with hW
  have hWo : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have h1W : (1:ℝ) ∈ W := by simpa [hW] using ht
  set G : ℝ → E := fun σ => F (picardLim F (σ • t, z)) with hG
  have hGc : ContinuousOn G W := cont_lim_ray' hLA h ht hz
  have hGi : IntervalIntegrable G volume 0 1 := by
    refine (hGc.mono ?_).intervalIntegrable_of_Icc zero_le_one
    intro θ hθ; exact smul_mem_ball h ht hθ
  have hint : HasDerivAt (fun ρ : ℝ => ∫ σ in (0:ℝ)..ρ, G σ) (G 1) 1 :=
    intervalIntegral.integral_hasDerivAt_right hGi
      (hGc.stronglyMeasurableAtFilter hWo 1 h1W) (hGc.continuousAt (hWo.mem_nhds h1W))
  have hR : HasDerivAt (fun ρ : ℝ => z + t • ∫ σ in (0:ℝ)..ρ, G σ) (t • G 1) 1 :=
    (hint.const_smul t).const_add z
  have hh : HasDerivAt (fun ρ : ℝ => ρ • t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const t
  have hd' : HasDerivAt φ (deriv φ t) ((fun ρ : ℝ => ρ • t) 1) := by simpa using hd
  have hψ : HasDerivAt (φ ∘ fun ρ : ℝ => ρ • t) (t • deriv φ t) 1 := hd'.scomp (1:ℝ) hh
  have hev : (φ ∘ fun ρ : ℝ => ρ • t) =ᶠ[𝓝 (1:ℝ)] fun ρ : ℝ => z + t • ∫ σ in (0:ℝ)..ρ, G σ := by
    filter_upwards [hWo.mem_nhds h1W, Ioi_mem_nhds (zero_lt_one : (0:ℝ) < 1)] with ρ hρW hρ0
    have hρ0' : (0:ℝ) < ρ := hρ0
    have heq := lim_integral_eq' hLA h hρW hz
    simp only [Function.comp, hφ]
    rw [heq]
    have hcomp : (∫ θ in (0:ℝ)..1, F (picardLim F (θ • ρ • t, z))) =
        ρ⁻¹ • ∫ σ in (0:ℝ)..ρ, G σ := by
      have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) G (c := ρ) hρ0'.ne'
      simp only [mul_zero, mul_one] at this
      rw [← this]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [hG]
      rw [smul_smul, mul_comm]
    rw [hcomp]
    congr 1
    rw [smul_assoc, smul_comm t ρ⁻¹, smul_smul, mul_inv_cancel₀ hρ0'.ne', one_smul]
  have hψ2 : HasDerivAt (φ ∘ fun ρ : ℝ => ρ • t) (t • G 1) 1 := hR.congr_of_eventuallyEq hev
  have := hψ.unique hψ2
  have hG1 : G 1 = F (picardLim F (t, z)) := by simp [hG]
  rw [hG1] at this
  exact smul_right_injective E ht0 this

lemma deriv_eq' (hLA : AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r))
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    deriv (fun s : ℂ => picardLim F (s, z)) t = F (picardLim F (t, z)) := by
  by_cases ht0 : t = 0
  · subst ht0
    set φ : ℂ → E := fun s => picardLim F (s, z) with hφ
    have hA : AnalyticAt ℂ φ 0 := lim_analyticAt_slice' hLA h ht hz
    have h1 : Tendsto (deriv φ) (𝓝[≠] (0:ℂ)) (𝓝 (deriv φ 0)) :=
      (hA.deriv.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s => F (φ s)) (𝓝[≠] (0:ℂ)) (𝓝 (F (φ 0))) := by
      have hFc : ContinuousAt F (φ 0) :=
        h.hFL.continuousOn.continuousAt (isOpen_ball.mem_nhds (lim_mem h ht hz))
      exact (hFc.comp hA.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have h3 : deriv φ =ᶠ[𝓝[≠] (0:ℂ)] fun s => F (φ s) := by
      have : ∀ᶠ s in 𝓝 (0:ℂ), s ∈ ball (0:ℂ) τ := isOpen_ball.mem_nhds ht
      filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with s hs hs0
      exact deriv_eq_of_ne' hLA h hs hs0 hz
    exact tendsto_nhds_unique_of_eventuallyEq h1 h2 h3
  · exact deriv_eq_of_ne' hLA h ht ht0 hz

lemma lim_hasDerivAt' (hLA : AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r))
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    HasDerivAt (fun s : ℂ => picardLim F (s, z)) (F (picardLim F (t, z))) t := by
  have := (lim_analyticAt_slice' hLA h ht hz).differentiableAt.hasDerivAt
  rwa [deriv_eq' hLA h ht hz] at this
end
end NlsGge.Atomic.G1081S4PicardAnalytic

namespace NlsGge.GKDefinitionDesign

theorem exists_local_complex_analytic_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : E → E) (a : E) (hF : AnalyticAt ℂ F a) :
  ∃ (tau r : ℝ) (Phi : ℂ × E → E),
    0 < tau ∧ 0 < r ∧
    AnalyticOnNhd ℂ Phi
      (Metric.ball (0 : ℂ) tau ×ˢ Metric.ball a r) ∧
    (∀ z : E, z ∈ Metric.ball a r → Phi (0, z) = z) ∧
    ∀ (t : ℂ) (z : E), t ∈ Metric.ball (0 : ℂ) tau →
      z ∈ Metric.ball a r →
      HasDerivAt (fun s : ℂ => Phi (s, z)) (F (Phi (t, z))) t := by
  obtain ⟨ρ, M, τ, r, K, h, hFa⟩ :=
    NlsGge.Atomic.G1081S4PicardAnalytic.exists_pdata' hF
  have hLA := NlsGge.Atomic.G1081S4PicardAnalytic.lim_analytic' h hFa
  exact ⟨τ, r, NlsGge.Atomic.G1081S4Picard.picardLim F, h.hτ, h.hr, hLA,
    fun z hz => NlsGge.Atomic.G1081S4Picard.lim_zero h hz,
    fun t z ht hz => NlsGge.Atomic.G1081S4PicardAnalytic.lim_hasDerivAt' hLA h ht hz⟩

end NlsGge.GKDefinitionDesign
