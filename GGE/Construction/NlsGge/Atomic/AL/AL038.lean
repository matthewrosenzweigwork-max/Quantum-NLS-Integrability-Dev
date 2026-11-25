import Mathlib
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                                                                                  
                                                                                                                                                                                                                                                   
                                                                                                                                                                                     
                                                                                                                                                         
                                                                                                                                                   
                                                                                                                                                        
                                                                                         
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem alPoly2_zero_of_littleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b0 b1 b2 : E)
    (h : Tendsto (fun x : ℝ => (x ^ 2)⁻¹ • (b0 + x • b1 + x ^ 2 • b2)) (𝓝[≠] 0) (𝓝 0)) :
    b0 = 0 ∧ b1 = 0 ∧ b2 = 0 := by
  have hx0 : Tendsto (fun x : ℝ => x) (𝓝[≠] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hP : Tendsto (fun x : ℝ => b0 + x • b1 + x ^ 2 • b2) (𝓝[≠] 0) (𝓝 b0) := by
    have : Tendsto (fun x : ℝ => b0 + x • b1 + x ^ 2 • b2) (𝓝 0) (𝓝 (b0 + (0 : ℝ) • b1 + (0 : ℝ) ^ 2 • b2)) :=
      Continuous.tendsto (by fun_prop) 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have e0 : ∀ᶠ x : ℝ in 𝓝[≠] 0, b0 + x • b1 + x ^ 2 • b2 = x ^ 2 • ((x ^ 2)⁻¹ • (b0 + x • b1 + x ^ 2 • b2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    rw [smul_smul, mul_inv_cancel₀ this, one_smul]
  have hb0 : b0 = 0 := by
    have h1 : Tendsto (fun x : ℝ => x ^ 2 • ((x ^ 2)⁻¹ • (b0 + x • b1 + x ^ 2 • b2))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) ^ 2 • (0 : E))) :=
      ((hx0.pow 2).smul h)
    simp only [smul_zero] at h1
    exact tendsto_nhds_unique (hP.congr' e0) h1
  subst hb0
  have hP1 : Tendsto (fun x : ℝ => x⁻¹ • (0 + x • b1 + x ^ 2 • b2)) (𝓝[≠] 0) (𝓝 b1) := by
    have e : ∀ᶠ x : ℝ in 𝓝[≠] 0, x⁻¹ • (0 + x • b1 + x ^ 2 • b2) = b1 + x • b2 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [zero_add, smul_add, smul_smul]
      rw [inv_mul_cancel₀ hx, one_smul, show x⁻¹ * x ^ 2 = x by field_simp]
    have : Tendsto (fun x : ℝ => b1 + x • b2) (𝓝 0) (𝓝 (b1 + (0 : ℝ) • b2)) :=
      Continuous.tendsto (by fun_prop) 0
    simpa using (this.mono_left nhdsWithin_le_nhds).congr' (e.mono fun x hx => hx.symm)
  have hb1 : b1 = 0 := by
    have e : ∀ᶠ x : ℝ in 𝓝[≠] 0, x⁻¹ • (0 + x • b1 + x ^ 2 • b2) =
        x • ((x ^ 2)⁻¹ • (0 + x • b1 + x ^ 2 • b2)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [smul_smul]
      congr 1
      field_simp
    have h1 : Tendsto (fun x : ℝ => x • ((x ^ 2)⁻¹ • (0 + x • b1 + x ^ 2 • b2))) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • (0 : E))) :=
      hx0.smul h
    simp only [smul_zero] at h1
    exact tendsto_nhds_unique (hP1.congr' e) h1
  subst hb1
  have hb2 : b2 = 0 := by
    have e : ∀ᶠ x : ℝ in 𝓝[≠] 0, (x ^ 2)⁻¹ • (0 + x • (0 : E) + x ^ 2 • b2) = b2 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      simp only [zero_add, smul_zero, smul_smul, inv_mul_cancel₀ this, one_smul]
    exact (tendsto_nhds_unique (tendsto_const_nhds.congr' (e.mono fun x hx => hx.symm)) h)
  exact ⟨rfl, rfl, hb2⟩

theorem alTaylor2_of_analytic_littleO {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (S : E) (hg : AnalyticAt ℝ g 0)
    (h1 : Tendsto (fun x : ℝ => (x ^ 2)⁻¹ • (g x - x ^ 2 • S)) (𝓝[≠] 0) (𝓝 0)) :
    g 0 = 0 ∧ iteratedDeriv 1 g 0 = 0 ∧ iteratedDeriv 2 g 0 = (2 : ℝ) • S := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hg.eventually_analyticAt
  have hcd : ContDiffOn ℝ 2 g (ball (0 : ℝ) ε) := fun y hy =>
    (hball y hy).contDiffAt.contDiffWithinAt
  have hT := taylor_tendsto (convex_ball (0 : ℝ) ε) (mem_ball_self hε) hcd
  rw [(isOpen_ball).nhdsWithin_eq (mem_ball_self hε)] at hT
  have hit : ∀ n : ℕ, iteratedDerivWithin n g (ball (0 : ℝ) ε) 0 = iteratedDeriv n g 0 := fun n =>
    iteratedDerivWithin_of_isOpen isOpen_ball (mem_ball_self hε)
  have hTe : ∀ x : ℝ, taylorWithinEval g 2 (ball (0 : ℝ) ε) 0 x =
      iteratedDeriv 0 g 0 + x • iteratedDeriv 1 g 0 + (x ^ 2 / 2) • iteratedDeriv 2 g 0 := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hit]
    simp [Nat.factorial, smul_smul]
    congr 1; ring
  set a0 := iteratedDeriv 0 g 0
  set a1 := iteratedDeriv 1 g 0
  set a2 := iteratedDeriv 2 g 0
  have hg0 : g 0 = a0 := by simp [a0]
  have hlim : Tendsto (fun x : ℝ => (x ^ 2)⁻¹ • (a0 + x • a1 + x ^ 2 • (((1 : ℝ) / 2) • a2 - S)))
      (𝓝[≠] 0) (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => (x ^ 2)⁻¹ • (g x - taylorWithinEval g 2 (ball (0 : ℝ) ε) 0 x))
        (𝓝[≠] 0) (𝓝 0) := by
      simpa using hT.mono_left nhdsWithin_le_nhds
    have h3 := h1.sub h2
    simp only [sub_zero, sub_self] at h3
    refine h3.congr fun x => ?_
    rw [← smul_sub, hTe x]
    congr 1
    module
  obtain ⟨hb0, hb1, hb2⟩ := alPoly2_zero_of_littleO _ _ _ hlim
  refine ⟨by rw [hg0]; exact hb0, hb1, ?_⟩
  have : ((1 : ℝ) / 2) • a2 = S := sub_eq_zero.1 hb2
  calc a2 = (2 : ℝ) • (((1 : ℝ) / 2) • a2) := by rw [smul_smul]; norm_num
    _ = (2 : ℝ) • S := by rw [this]

theorem alTaylor2_of_analytic_O4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (g : ℝ → E) (S : E) (hg : AnalyticAt ℝ g 0) (C δ : ℝ) (hδ : 0 < δ)
    (hb : ∀ t : ℝ, 0 < |t| → |t| < δ → ‖g t - t ^ 2 • S‖ ≤ C * t ^ 4) :
    g 0 = 0 ∧ iteratedDeriv 1 g 0 = 0 ∧ iteratedDeriv 2 g 0 = (2 : ℝ) • S := by
  refine alTaylor2_of_analytic_littleO g S hg ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hC : Tendsto (fun x : ℝ => C * x ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have : Tendsto (fun x : ℝ => C * x ^ 2) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ 2)) :=
      Continuous.tendsto (by fun_prop) 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hC
  have hev : ∀ᶠ x : ℝ in 𝓝[≠] 0, |x| < δ := by
    have : ∀ᶠ x : ℝ in 𝓝 0, |x| < δ := by
      have := (continuous_abs (G := ℝ)).tendsto 0
      simpa using this.eventually (gt_mem_nhds (by simpa using hδ : |(0 : ℝ)| < δ))
    exact this.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev, self_mem_nhdsWithin] with x hx hx0
  have hx0' : x ≠ 0 := hx0
  have hab : 0 < |x| := abs_pos.2 hx0'
  have hx2 : 0 < x ^ 2 := by positivity
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hx2.le]
  calc (x ^ 2)⁻¹ * ‖g x - x ^ 2 • S‖ ≤ (x ^ 2)⁻¹ * (C * x ^ 4) :=
        mul_le_mul_of_nonneg_left (hb x hab hx) (by positivity)
    _ = C * x ^ 2 := by field_simp

theorem alC38_analyticAt_zero {L : ℕ} [NeZero L] (k : ℕ) :
    AnalyticAt ℝ (fun a : ZMod L → ℂ => alC38 a k) 0 := by
  have h0 : IsALField38 (0 : ZMod L → ℂ) := fun j => by simp
  obtain ⟨U, ρ₁, hUo, hp0U, hUdom, hρ, hρ1, hDG, hlog, hexp, hreal⟩ := exists_alComplexLogNhd38 h0
  have hc : AnalyticAt ℂ (fun p => alCc38 p k) ((0 : ZMod L → ℂ), fun j => star ((0 : ZMod L → ℂ) j)) :=
    analyticAt_alCc38 hρ hUo hlog k hp0U
  have hι : AnalyticAt ℝ (alIota38 (L := L)) (0 : ZMod L → ℂ) := alIota38.analyticAt (0 : ZMod L → ℂ)
  have hcR : AnalyticAt ℝ (fun p => alCc38 p k) (alIota38 (0 : ZMod L → ℂ)) := hc.restrictScalars
  refine (hcR.comp hι).congr ?_
  have hn1 : ∀ᶠ α in 𝓝 (0 : ZMod L → ℂ), α ∈ alDisk38 L := isOpen_alDiskAn38.mem_nhds h0
  have hn2 : ∀ᶠ α in 𝓝 (0 : ZMod L → ℂ), alIota38 α ∈ U :=
    alIota38.continuous.continuousAt.eventually (hUo.mem_nhds hp0U)
  filter_upwards [hn1, hn2] with α hα hαU
  exact alCc38_real hρ (hreal α hα hαU) k

theorem al038 {L : ℕ} [NeZero L]
    (α : ZMod L → ℂ) (k : ℕ) (hk : 1 ≤ k) :
  AnalyticAt ℝ (fun a : ZMod L → ℂ => alC38 a k) 0 ∧
  alC38 (0 : ZMod L → ℂ) k = 0 ∧
  iteratedDeriv 1 (fun t : ℝ => alC38 (t • α) k) 0 = 0 ∧
  (1/2 : ℝ) • iteratedDeriv 2 (fun t : ℝ => alC38 (t • α) k) 0 =
    ∑ j : ZMod L, α j*star (α (j-(k : ZMod L))) := by
  have hcont := alC38_analyticAt_zero (L := L) k
  set S : ℂ := ∑ j : ZMod L, α j * star (α (j - (k : ZMod L))) with hS
  set s : ℝ := (1 + ∑ j, ‖α j‖)⁻¹ with hs
  have hsum0 : 0 ≤ ∑ j, ‖α j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hspos : 0 < s := by positivity
  have hsα : IsALField38 (s • α) := by
    intro j
    have hj : ‖α j‖ ≤ ∑ j, ‖α j‖ := Finset.single_le_sum (f := fun j => ‖α j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
    show ‖(s • α) j‖ < 1
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hspos.le, hs]
    have h1 : 0 < 1 + ∑ j, ‖α j‖ := by positivity
    rw [inv_mul_lt_iff₀ h1]
    linarith
  obtain ⟨C, δ, hC, hδ, hbd⟩ := alC38_quadratic38 hsα hk
  have hg : AnalyticAt ℝ (fun t : ℝ => alC38 (t • α) k) 0 := by
    have hlin : AnalyticAt ℝ (fun t : ℝ => t • α) 0 := analyticAt_id.smul analyticAt_const
    have h0 : (fun t : ℝ => t • α) 0 = 0 := zero_smul ℝ α
    exact hcont.comp_of_eq hlin h0
  have hSs : ∑ j : ZMod L, (s • α) j * (starRingEnd ℂ) ((s • α) (j - (k : ZMod L))) = ((s ^ 2 : ℝ) : ℂ) * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, Complex.real_smul, Complex.star_def, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hb : ∀ t : ℝ, 0 < |t| → |t| < s * δ → ‖alC38 (t • α) k - t ^ 2 • S‖ ≤ (C / s ^ 4) * t ^ 4 := by
    intro t ht0 htd
    have hu0 : 0 < |t / s| := by rw [abs_div, abs_of_pos hspos]; positivity
    have hud : |t / s| < δ := by
      rw [abs_div, abs_of_pos hspos, div_lt_iff₀ hspos]; linarith
    have h := hbd (t / s) hu0 hud
    have e1 : (t / s) • (s • α) = t • α := by rw [smul_smul, div_mul_cancel₀ _ hspos.ne']
    rw [e1, hSs] at h
    have e2 : ((t / s : ℝ) : ℂ) ^ 2 * (((s ^ 2 : ℝ) : ℂ) * S) = t ^ 2 • S := by
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hspos.ne'
      rw [Complex.real_smul]
      push_cast
      field_simp
    rw [e2] at h
    calc ‖alC38 (t • α) k - t ^ 2 • S‖ ≤ C * (t / s) ^ 4 := h
      _ = (C / s ^ 4) * t ^ 4 := by field_simp
  obtain ⟨h0, h1, h2⟩ := alTaylor2_of_analytic_O4 _ S hg (C / s ^ 4) (s * δ) (by positivity) hb
  refine ⟨hcont, ?_, h1, ?_⟩
  · simpa using h0
  · rw [h2, smul_smul]; norm_num

end
end NlsGge.ThirdConsultation.AL
