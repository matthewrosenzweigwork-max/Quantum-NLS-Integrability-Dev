import Mathlib
import NlsGge.Atomic.G1.S4PicardAnalytic
import NlsGge.Atomic.G1.S4L2
import NlsGge.Atomic.G1.S4Glob
import NlsGge.Atomic.G1.G1081Sup5

                                                                                            
                                                                                                                           
                                                                                                            
                                                                            
                                                                                                                              
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GKDefinitionDesign
namespace NlsGge.Atomic.G1081S4L3
noncomputable section

theorem ode_eq_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : E → E) (a : E) (ρ : ℝ) (K : NNReal) (hK : LipschitzOnWith K G (ball a ρ))
    (τ : ℝ) (hτ : 0 < τ) (γ1 γ2 : ℝ → E)
    (h1d : ∀ t ∈ Ioo (-τ) τ, HasDerivAt γ1 (G (γ1 t)) t)
    (h1b : ∀ t ∈ Ioo (-τ) τ, γ1 t ∈ ball a ρ)
    (h2d : ∀ t ∈ Ioo (-τ) τ, γ2 t ∈ ball a ρ → HasDerivAt γ2 (G (γ2 t)) t)
    (h2c : Continuous γ2) (h0 : γ1 0 = γ2 0) :
    ∀ t ∈ Ioo (-τ) τ, γ1 t = γ2 t := by
  have key : ∀ t0 ∈ Ioo (-τ) τ, γ1 t0 = γ2 t0 → γ1 =ᶠ[𝓝 t0] γ2 := by
    intro t0 ht0 heq
    have hI : Ioo (-τ) τ ∈ 𝓝 t0 := Ioo_mem_nhds ht0.1 ht0.2
    have hb2 : ∀ᶠ t in 𝓝 t0, γ2 t ∈ ball a ρ :=
      h2c.continuousAt.eventually (isOpen_ball.mem_nhds (heq ▸ h1b t0 ht0))
    refine ODE_solution_unique_of_eventually (v := fun _ => G) (s := fun _ => ball a ρ) (K := K)
      (Eventually.of_forall fun _ => hK) ?_ ?_ heq
    · filter_upwards [hI] with t ht using ⟨h1d t ht, h1b t ht⟩
    · filter_upwards [hI, hb2] with t ht hb using ⟨h2d t ht hb, hb⟩
  have hsub := (isPreconnected_Ioo (a := -τ) (b := τ)).subset_of_closure_inter_subset
    (u := {t | γ1 =ᶠ[𝓝 t] γ2}) (isOpen_setOf_eventually_nhds)
    ⟨0, ⟨by linarith, hτ⟩, key 0 ⟨by linarith, hτ⟩ h0⟩ (by
      intro t ⟨htc, htI⟩
      show γ1 =ᶠ[𝓝 t] γ2
      apply key t htI
      by_contra hne
      have hc1 : ContinuousAt γ1 t := (h1d t htI).continuousAt
      have hev : ∀ᶠ s in 𝓝 t, γ1 s ≠ γ2 s := by
        obtain ⟨U, V, hUo, hVo, hxU, hyV, hUV⟩ := t2_separation hne
        filter_upwards [hc1.eventually (hUo.mem_nhds hxU),
          h2c.continuousAt.eventually (hVo.mem_nhds hyV)] with s h1 h2 heq
        exact Set.disjoint_left.mp hUV h1 (heq ▸ h2)
      have hfr : ∃ᶠ s in 𝓝 t, s ∈ {t | γ1 =ᶠ[𝓝 t] γ2} := mem_closure_iff_frequently.mp htc
      obtain ⟨s, hs1, hs2⟩ := (hfr.and_eventually hev).exists
      exact hs2 hs1.eq_of_nhds)
  intro t ht
  exact (hsub ht).eq_of_nhds

theorem local_flow_analyticAt (n : ℤ)
    {f : ℝ → PhysicalL2 → PhysicalL2} (hf : completeGapFlow n f) (u0 : PhysicalL2) :
    AnalyticAt ℝ (fun p : ℝ × PhysicalL2 => f p.1 p.2) (0, u0) := by
  obtain ⟨r2, G, hr2, hGan, hGeq⟩ :=
    NlsGge.Atomic.G1081S4L2.singleGapField_local_complex_extension n u0
  set a : PotPair := realSlice u0 with ha
  have hGa : AnalyticAt ℂ G a := hGan a (mem_ball_self hr2)
  obtain ⟨tau, r1, Phi, htau, hr1, hPan, hP0, hPder⟩ :=
    exists_local_complex_analytic_flow G a hGa
  have hc : ContDiffAt ℝ 1 G a := (hGa.restrictScalars (𝕜 := ℝ)).contDiffAt
  obtain ⟨K, s, hs, hK⟩ := hc.exists_lipschitzOnWith
  obtain ⟨ρ0, hρ0, hρ0s⟩ := Metric.mem_nhds_iff.mp hs
  set ρ : ℝ := min ρ0 r2 with hρ
  have hρpos : 0 < ρ := lt_min hρ0 hr2
  have hKρ : LipschitzOnWith K G (ball a ρ) :=
    hK.mono (fun x hx => hρ0s (ball_subset_ball (min_le_left _ _) hx))
  have hρr2 : ball a ρ ⊆ ball a r2 := ball_subset_ball (min_le_right _ _)
  have hPa : AnalyticAt ℂ Phi (0, a) := hPan (0, a) ⟨mem_ball_self htau, mem_ball_self hr1⟩
  have hPev : ∀ᶠ q in 𝓝 ((0 : ℂ), a), q ∈ ball (0 : ℂ) tau ×ˢ ball a r1 ∧ Phi q ∈ ball a ρ := by
    have h1 : ∀ᶠ q in 𝓝 ((0 : ℂ), a), q ∈ ball (0 : ℂ) tau ×ˢ ball a r1 :=
      (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self htau, mem_ball_self hr1⟩
    have h2 : ∀ᶠ q in 𝓝 ((0 : ℂ), a), Phi q ∈ ball a ρ := by
      have : ContinuousAt Phi (0, a) := hPa.continuousAt
      refine this.eventually (isOpen_ball.mem_nhds ?_)
      rw [hP0 a (mem_ball_self hr1)]; exact mem_ball_self hρpos
    exact h1.and h2
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp (show {q : ℂ × PotPair | q ∈ ball (0 : ℂ) tau ×ˢ ball a r1 ∧ Phi q ∈ ball a ρ} ∈ 𝓝 ((0 : ℂ), a) from hPev)
  obtain ⟨τ', hτ', hτA⟩ := Metric.mem_nhds_iff.mp hA
  obtain ⟨r', hr', hrB⟩ := Metric.mem_nhds_iff.mp hB
  -- real-slice identification
  have hid : ∀ v : PhysicalL2, ‖v - u0‖ < r' → ∀ t : ℝ, |t| < τ' →
      f t v = (Phi ((t : ℂ), realSlice v)).1 := by
    intro v hv
    have hvB : realSlice v ∈ ball a r' := by
      rw [mem_ball_iff_norm, ha, ← map_sub, norm_realSlice]; exact hv
    have hγd : ∀ t ∈ Ioo (-τ') τ', HasDerivAt (fun s : ℝ => Phi ((s : ℂ), realSlice v))
        (G (Phi ((t : ℂ), realSlice v))) t := by
      intro t ht
      have htA : (t : ℂ) ∈ ball (0 : ℂ) τ' := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        exact ⟨ht.1, ht.2⟩
      have hmem : ((t : ℂ), realSlice v) ∈ ball (0 : ℂ) tau ×ˢ ball a r1 ∧
          Phi ((t : ℂ), realSlice v) ∈ ball a ρ :=
        hAB (Set.mk_mem_prod (hτA htA) (hrB hvB))
      have h1 := hPder (t : ℂ) (realSlice v) hmem.1.1 hmem.1.2
      have h2 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
      have h3 := h1.scomp t h2
      have h4 := h3
      rw [one_smul] at h4
      exact h4
    have hγb : ∀ t ∈ Ioo (-τ') τ', Phi ((t : ℂ), realSlice v) ∈ ball a ρ := by
      intro t ht
      have htA : (t : ℂ) ∈ ball (0 : ℂ) τ' := by
        rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_lt]
        exact ⟨ht.1, ht.2⟩
      exact (hAB (Set.mk_mem_prod (hτA htA) (hrB hvB)) : _ ∧ Phi ((t : ℂ), realSlice v) ∈ ball a ρ).2
    have hfd : ∀ t, HasDerivAt (fun s : ℝ => realSlice (f s v))
        (realSlice (singleGapField n (f t v))) t :=
      fun t => realSlice.hasFDerivAt.comp_hasDerivAt t (hf.2 v t)
    have hfc : Continuous (fun s : ℝ => realSlice (f s v)) :=
      continuous_iff_continuousAt.mpr fun t => (hfd t).continuousAt
    have key := ode_eq_on_interval G a ρ K hKρ τ' hτ' _ (fun s => realSlice (f s v)) hγd hγb
      (fun t _ hb => by
        have := hfd t
        rwa [← hGeq (f t v) (hρr2 hb)] at this)
      hfc (by
        have h00 : (0 : ℂ) ∈ ball (0 : ℂ) τ' := mem_ball_self hτ'
        have := (hAB (Set.mk_mem_prod (hτA h00) (hrB hvB)) : ((0:ℂ), realSlice v) ∈ ball (0 : ℂ) tau ×ˢ ball a r1 ∧ _).1.2
        simp only [Complex.ofReal_zero, hf.1 v]
        exact hP0 _ this)
    intro t ht
    have := key t (abs_lt.mp ht |> fun h => ⟨h.1, h.2⟩)
    rw [← realSlice_fst (f t v), ← this]
  -- analyticity of the representative
  have hPa' : AnalyticAt ℝ Phi (0, a) := hPa.restrictScalars
  have hin : AnalyticAt ℝ (fun p : ℝ × PhysicalL2 => (((p.1 : ℂ), realSlice p.2) : ℂ × PotPair))
      (0, u0) := by
    have h1 : AnalyticAt ℝ (fun p : ℝ × PhysicalL2 => (p.1 : ℂ)) (0, u0) :=
      (Complex.ofRealCLM.analyticAt _).comp analyticAt_fst
    have h2 : AnalyticAt ℝ (fun p : ℝ × PhysicalL2 => realSlice p.2) (0, u0) :=
      (realSlice.analyticAt _).comp analyticAt_snd
    exact h1.prod h2
  have hPa'' : AnalyticAt ℝ Phi (((((0 : ℝ) : ℂ)), realSlice u0) : ℂ × PotPair) := by
    rw [Complex.ofReal_zero]; exact hPa'
  have hcomp : AnalyticAt ℝ (fun p : ℝ × PhysicalL2 => (Phi ((p.1 : ℂ), realSlice p.2)).1)
      (0, u0) :=
    ((ContinuousLinearMap.fst ℝ PhysicalL2 PhysicalL2).analyticAt _).comp
      (AnalyticAt.comp (g := Phi)
        (f := fun p : ℝ × PhysicalL2 => (((p.1 : ℂ), realSlice p.2) : ℂ × PotPair)) hPa'' hin)
  refine hcomp.congr ?_
  have hopen : {p : ℝ × PhysicalL2 | |p.1| < τ' ∧ ‖p.2 - u0‖ < r'} ∈ 𝓝 ((0 : ℝ), u0) := by
    apply IsOpen.mem_nhds
    · exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
        (isOpen_lt ((continuous_snd.sub continuous_const).norm) continuous_const)
    · simp [hτ', hr']
  filter_upwards [hopen] with p hp
  exact (hid p.2 hp.2 p.1 hp.1).symm

theorem analyticOnNhd_complete_flow (n : ℤ)
    {f : ℝ → PhysicalL2 → PhysicalL2} (hf : completeGapFlow n f) :
    AnalyticOnNhd ℝ (fun p : ℝ × PhysicalL2 => f p.1 p.2) Set.univ :=
  NlsGge.Atomic.G1081S4Glob.analytic_of_local_flow f
    (fun s t v => NlsGge.Atomic.G1081Sup5.completeGapFlow_group n hf s t v)
    (fun v => continuous_iff_continuousAt.mpr fun t => (hf.2 v t).continuousAt)
    (local_flow_analyticAt n hf)

end
end NlsGge.Atomic.G1081S4L3
