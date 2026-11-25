import Mathlib
import NlsGge.Atomic.G4.G4036Host
import NlsGge.Atomic.G4.G4036Cauchy
import NlsGge.Atomic.G4.G4036Unique
import NlsGge.Atomic.G4.G4036Param
import NlsGge.Atomic.G4.G4036H2
import NlsGge.Atomic.G5.G5001
import NlsGge.Analysis.AffineCircleDeformation
import NlsGge.GK38.ContourActionDeformation
import NlsGge.GK38.IsolatingPersistence
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.TauGamma

                                                                                                          
                                                                                                       
                                                                                                        
                                                                                                                  
                                                                                                                  
                                                                                                              
                                                                                                            
                                                                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.Atomic.G4036Cauchy

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- K is analytic wherever the point avoids every other cut. -/
theorem g4036_K_analyticAt (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) (z : ℂ)
    (h : ∀ m : ℤ, m ≠ n → z ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)) :
    AnalyticAt ℂ (normalizedZeta n φ) z := by
  have hdom : (φ, z) ∈ a5OmittedRootDomain38 n := ⟨hgk, h⟩
  have hjoint : AnalyticAt ℂ (p2OmittedRatio38 n) ((φ, p2Extend38 n (sourceF n φ)), z) :=
    p2OmittedRatio_analytic38 n ((φ, p2Extend38 n (sourceF n φ)), z) hdom
  have hpair : AnalyticAt ℂ (fun w : ℂ => ((φ, p2Extend38 n (sourceF n φ)), w)) z :=
    AnalyticAt.prod analyticAt_const analyticAt_id
  exact hjoint.comp hpair

/-- The standard root is analytic and nonzero off the own cut. -/
theorem g4036_std_analyticAt (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) (z : ℂ)
    (hz : z ∉ segment ℝ (lamMinus φ n) (lamPlus φ n)) : AnalyticAt ℂ (standardRoot φ n) z := by
  obtain ⟨hne, hslit⟩ := stdRoot_slit38 (lamMinus φ n) (lamPlus φ n) z hz
  rw [g4036_std_eq φ hgk n]
  exact stdRoot_analyticAt38 (τ := fun _ : ℂ => (lamMinus φ n + lamPlus φ n) / 2)
    (g2 := fun _ : ℂ => (lamPlus φ n - lamMinus φ n) ^ 2) (z := fun y : ℂ => y)
    analyticAt_const analyticAt_const analyticAt_id hne hslit

/-- Joint analyticity of K on the fixed sphere over a neighbourhood carrying a fixed isolating family. -/
theorem g4036_K_joint (V : Set PotPair) (hV : V ⊆ sourceBetaW) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ)
    (N : ℕ) (hg : IsolatingGeometry38 C R c N) (hs : ∀ φ ∈ V, IsolatingSpectral38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q : PotPair × ℂ => normalizedZeta n q.1 q.2)
      (V ×ˢ Metric.sphere (C n) (R n)) := by
  intro q hq
  have hφS : q.1 ∈ sourceBetaW := hV hq.1
  have hgk : q.1 ∈ gkW := g5001_gk q.1 hφS
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hpos : 0 < c⁻¹ / 2 := by have := inv_pos.2 hc0; linarith
  have hdom : (q.1, q.2) ∈ a5OmittedRootDomain38 n := by
    refine ⟨hgk, fun m hm => g2073s1_tube_avoids C R c N hg q.1 (hs q.1 hq.1) n m hm q.2 ?_⟩
    have := mem_sphere.1 hq.2
    linarith
  have h1 : AnalyticAt ℂ (p2OmittedRatio38 n) ((q.1, p2Extend38 n (sourceF n q.1)), q.2) :=
    p2OmittedRatio_analytic38 n ((q.1, p2Extend38 n (sourceF n q.1)), q.2) hdom
  have h2 : AnalyticAt ℂ (fun p : PotPair × ℂ => ((p.1, p2Extend38 n (sourceF n p.1)), p.2)) q :=
    (analyticAt_fst.prod ((g5001_ext_analytic n q.1 hφS).comp analyticAt_fst)).prod analyticAt_snd
  exact AnalyticAt.comp (g := p2OmittedRatio38 n)
    (f := fun p : PotPair × ℂ => ((p.1, p2Extend38 n (sourceF n p.1)), p.2)) h1 h2

theorem g4036_std_joint (V : Set PotPair) (hV : V ⊆ sourceBetaW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hs : ∀ φ ∈ V, IsolatingSpectral38 φ C R) (n : ℤ) :
    AnalyticOnNhd ℂ (fun q : PotPair × ℂ => standardRoot q.1 n q.2)
      (V ×ˢ Metric.sphere (C n) (R n)) := by
  intro q hq
  have hgk : q.1 ∈ gkW := g5001_gk q.1 (hV hq.1)
  have hnot : q.2 ∉ segment ℝ (lamMinus q.1 n) (lamPlus q.1 n) := by
    intro hseg
    have h1 := mem_ball.1 (((hs q.1 hq.1).1 n).1 hseg)
    have h2 := mem_sphere.1 hq.2
    linarith
  obtain ⟨hne, hslit⟩ := stdRoot_slit38 (lamMinus q.1 n) (lamPlus q.1 n) q.2 hnot
  have ht : tauN q.1 n = (lamMinus q.1 n + lamPlus q.1 n) / 2 := by
    rw [tauN_value38 q.1 hgk n]; ring
  have hg2 : gamma2 q.1 n = (lamPlus q.1 n - lamMinus q.1 n) ^ 2 := gamma2_value38 q.1 hgk n
  have hτ : AnalyticAt ℂ (fun p : PotPair × ℂ => tauN p.1 n) q :=
    (tauN_analytic n q.1 hgk).comp analyticAt_fst
  have hγ : AnalyticAt ℂ (fun p : PotPair × ℂ => gamma2 p.1 n) q :=
    (gamma2_analytic n q.1 hgk).comp analyticAt_fst
  have hne' : tauN q.1 n - q.2 ≠ 0 := by rw [ht]; exact hne
  have hslit' : 1 - (gamma2 q.1 n / 4) / (tauN q.1 n - q.2) ^ 2 ∈ Complex.slitPlane := by
    rw [ht, hg2]; exact hslit
  exact stdRoot_analyticAt38 (τ := fun p : PotPair × ℂ => tauN p.1 n)
    (g2 := fun p : PotPair × ℂ => gamma2 p.1 n) (z := fun p : PotPair × ℂ => p.2)
    hτ hγ analyticAt_snd hne' hslit'

theorem g4036_std_ne_sphere (V : Set PotPair) (hV : V ⊆ sourceBetaW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hs : ∀ φ ∈ V, IsolatingSpectral38 φ C R) (n : ℤ) :
    ∀ x ∈ V, ∀ z ∈ Metric.sphere (C n) (R n), standardRoot x n z ≠ 0 := by
  intro x hx z hz
  have hgk : x ∈ gkW := g5001_gk x (hV hx)
  refine g2073s1_std_ne x hgk n z (fun hseg => ?_)
  have h1 := mem_ball.1 (((hs x hx).1 n).1 hseg)
  have h2 := mem_sphere.1 hz
  linarith

/-- Transport of the normalized zero period from the chosen circle to a second isolating family. -/
theorem g4036_zero_period_family (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) (C : ℤ → ℂ)
    (R : ℤ → ℝ) (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N) (hs : IsolatingSpectral38 φ C R) :
    (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap (C n) (R n)) θ *
      ((normalizedZeta n φ (circleMap (C n) (R n) θ) - 1) /
        standardRoot φ n (circleMap (C n) (R n) θ))) = 0 := by
  have hgk : φ ∈ gkW := g5001_gk φ hφ
  have h0 : IsolatingFamily38 φ (discC φ) (discR φ) := isolating_family38 φ hgk
  have h1 : IsolatingFamily38 φ C R := ⟨c, N, hg, hs⟩
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => (normalizedZeta n φ z - 1) / standardRoot φ n z)
      (actionCutDomain38 φ) := by
    intro z hz
    have hseg : ∀ m : ℤ, z ∉ segment ℝ (lamMinus φ m) (lamPlus φ m) := by
      intro m hm
      exact hz (Set.mem_iUnion.2 ⟨m, hm⟩)
    exact ((g4036_K_analyticAt φ hgk n z (fun m _ => hseg m)).sub analyticAt_const).div
      (g4036_std_analyticAt φ hgk n z (hseg n))
      (g2073s1_std_ne φ hgk n z (hseg n))
  have hr := action_contour_radii_pos38 φ (discC φ) C (discR φ) R h0 h1 n
  have hdef := (NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
    (isOpen_actionCutDomain38 φ hgk) hf hr.1 hr.2
    (fun t ht => action_contour_sphere_subset38 φ (discC φ) C (discR φ) R h0 h1 n t ht)).2.2
  have hch := g4036_zero_period_chosen n φ hφ
  have e1 : circleIntegral (fun z : ℂ => (normalizedZeta n φ z - 1) / standardRoot φ n z)
      (discC φ n) (discR φ n) = 0 := by
    rw [← hch]
    unfold circleIntegral
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [smul_eq_mul]
  rw [e1] at hdef
  have e2 : circleIntegral (fun z : ℂ => (normalizedZeta n φ z - 1) / standardRoot φ n z)
      (C n) (R n) = ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, deriv (circleMap (C n) (R n)) θ *
      ((normalizedZeta n φ (circleMap (C n) (R n) θ) - 1) /
        standardRoot φ n (circleMap (C n) (R n) θ)) := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr (fun θ _ => ?_)
    simp only [smul_eq_mul]
  rw [← e2]
  exact hdef.symm


/-- Identification of the fixed-circle and chosen-circle coefficients at the Dirichlet point. -/
theorem g4036_identify (n : ℤ) (φ : PotPair) (hφ : φ ∈ sourceBetaW) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (c : ℝ) (N : ℕ) (hg : IsolatingGeometry38 C R c N) (hs : IsolatingSpectral38 φ C R) :
    ownCorrection n φ (muSeq φ n) =
      cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) (muSeq φ n) := by
  have hgk : φ ∈ gkW := g5001_gk φ hφ
  obtain ⟨hA1, hO1⟩ := g4036_family_ode φ hgk C R c N hg hs n
    (g4036_zero_period_family n φ hφ C R c N hg hs)
  obtain ⟨hA2, hO2⟩ := ownCorrection_analytic_and_ode n φ hφ
  obtain ⟨c', N', hg', hs'⟩ := isolating_family38 φ hgk
  rw [g4036_ownCorrection_eq] at hA2 hO2 ⊢
  set T1 := cauchyOwnCorr (C n) (R n) (normalizedZeta n φ) (standardRoot φ n) with hT1
  set T2 := cauchyOwnCorr (discC φ n) (discR φ n) (normalizedZeta n φ) (standardRoot φ n) with hT2
  set I : Set ℂ := Metric.ball (C n) (R n) ∩ Metric.ball (discC φ n) (discR φ n) with hI
  have hIo : IsOpen I := isOpen_ball.inter isOpen_ball
  have hIc : IsPreconnected I :=
    ((convex_ball (C n) (R n)).inter (convex_ball (discC φ n) (discR φ n))).isPreconnected
  have heI : lamPlus φ n ∈ I :=
    ⟨((hs.1 n).1 (right_mem_segment ℝ _ _)), ((hs'.1 n).1 (right_mem_segment ℝ _ _))⟩
  have hPe : (lamPlus φ n - tauN φ n) ^ 2 - gamma2 φ n / 4 = 0 := by
    rw [tauN_value38 φ hgk n, gamma2_value38 φ hgk n]; ring
  have hS : AnalyticOnNhd ℂ (fun z => T1 z - T2 z) I :=
    (hA1.mono inter_subset_left).sub (hA2.mono inter_subset_right)
  have hode : ∀ z ∈ I, ((z - tauN φ n) ^ 2 - gamma2 φ n / 4) * deriv (fun z => T1 z - T2 z) z +
      (z - tauN φ n) * (T1 z - T2 z) = 0 := by
    intro z hz
    have d1 : DifferentiableAt ℂ T1 z := (hA1 z hz.1).differentiableAt
    have d2 : DifferentiableAt ℂ T2 z := (hA2 z hz.2).differentiableAt
    have hd : deriv (fun z => T1 z - T2 z) z = deriv T1 z - deriv T2 z :=
      (d1.hasDerivAt.sub d2.hasDerivAt).deriv
    rw [hd]
    linear_combination hO1 z hz.1 - hO2 z hz.2
  have hz0 := NlsGge.Atomic.G4036Unique.ode_unique hIc heI hIo hPe hS hode
  have hμ : muSeq φ n ∈ I := ⟨((hs.1 n).2.1), ((hs'.1 n).2.1)⟩
  have := hz0 _ hμ
  exact (sub_eq_zero.mp this).symm

theorem ownCorrection_at_dirichlet_analytic (n : ℤ) :
  AnalyticOnNhd ℂ
    (fun φ : PotPair => ownCorrection n φ (muSeq φ n)) sourceBetaW := by
  intro φ0 hφ0
  have hgk0 : φ0 ∈ gkW := g5001_gk φ0 hφ0
  obtain ⟨ρ, hρ, c, N, hgeom, hspec⟩ :=
    fixed_family_persistence38 φ0 (discC φ0) (discR φ0) (isolating_family38 φ0 hgk0)
  set V : Set PotPair := Metric.ball φ0 ρ ∩ sourceBetaW with hVdef
  have hVo : IsOpen V := isOpen_ball.inter sourceFamily.V_open
  have hφ0V : φ0 ∈ V := ⟨mem_ball_self hρ, hφ0⟩
  have hVS : V ⊆ sourceBetaW := inter_subset_right
  have hVs : ∀ φ ∈ V, IsolatingSpectral38 φ (discC φ0) (discR φ0) := fun φ hφ => hspec φ hφ.1
  have hr : 0 < discR φ0 n := (hgeom.1 n).1
  have hJ := NlsGge.Atomic.G4036Param.joint_cauchy_analytic (E := PotPair) (D := V)
    (c := discC φ0 n) (r := discR φ0 n)
    (K := fun x z => normalizedZeta n x z) (w := fun x z => standardRoot x n z) hr
    (g4036_K_joint V hVS (discC φ0) (discR φ0) c N hgeom hVs n)
    (g4036_std_joint V hVS (discC φ0) (discR φ0) hVs n)
    (g4036_std_ne_sphere V hVS (discC φ0) (discR φ0) hVs n) hVo
  have hΦ : AnalyticAt ℂ (fun φ : PotPair => (φ, muSeq φ n)) φ0 :=
    analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n φ0 hgk0)
  have hmu0 : muSeq φ0 n ∈ Metric.ball (discC φ0 n) (discR φ0 n) := ((hVs φ0 hφ0V).1 n).2.1
  have hcomp := AnalyticAt.comp
    (g := fun q : PotPair × ℂ => cauchyOwnCorr (discC φ0 n) (discR φ0 n)
      (normalizedZeta n q.1) (standardRoot q.1 n) q.2)
    (f := fun φ : PotPair => (φ, muSeq φ n)) (hJ (φ0, muSeq φ0 n) ⟨hφ0V, hmu0⟩) hΦ
  refine hcomp.congr ?_
  filter_upwards [hVo.mem_nhds hφ0V] with φ hφ
  exact (g4036_identify n φ (hVS hφ) (discC φ0) (discR φ0) c N hgeom (hVs φ hφ)).symm

end
end NlsGge.GKDefinitionDesign
