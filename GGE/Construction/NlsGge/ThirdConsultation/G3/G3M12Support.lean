import Mathlib
import NlsGge.Atomic.G2.G2022
import NlsGge.Atomic.G2.G2019
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.GK38.AngleCollapsedDirichletSeparation
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.IsolatingTopology
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3ZetaHost

                                                                                                           
                                                                                                        
                                                                                                  
                                                                                                   
                                                                                        
                                                                                       
                                                                                       
                                                                                                               
                                                                                                        
                                                                                                                   
                                                                                                                  
                                                                                                         
                                                                                       
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-! ## M1: continuity at the limit -/

theorem g3m1_muSeq_tendsto (m : ℤ) (v : ℕ → PotPair) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hv : Tendsto v atTop (𝓝 φ0)) :
    Tendsto (fun j : ℕ => muSeq (v j) m) atTop (𝓝 (muSeq φ0 m)) :=
  ((analyticOnNhd_muSeq_complex38 m φ0 (sourceFamily.W_gk hφ0)).continuousAt.tendsto).comp hv

theorem g3m1_collapsed_endpoints_tendsto (m : ℤ) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0)) :
    Tendsto (fun j : ℕ => lamMinus (v j) m) atTop (𝓝 (lamMinus φ0 m)) ∧
    Tendsto (fun j : ℕ => lamPlus (v j) m) atTop (𝓝 (lamPlus φ0 m)) :=
  ⟨((angleActual_collapsed_endpoint_continuity38 φ0 (sourceFamily.W_gk hφ0) m hgap).1.tendsto).comp hv,
   ((angleActual_collapsed_endpoint_continuity38 φ0 (sourceFamily.W_gk hφ0) m hgap).2.tendsto).comp hv⟩

/-! ## M2 helpers -/

theorem g3m2_coord_continuous (k : ℤ) : Continuous (fun s : Lib.L2Seq => s k) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact Lib.norm_coord_le (s - t) k

theorem g3m2_shift_continuous (n : ℤ) (a : ℂ) :
    Continuous (fun s : Lib.L2Seq => g2073s1ShiftSeq s n a) := by
  have hσ : Continuous (fun s : Lib.L2Seq => Lib.sigmaOf s n) := by
    unfold Lib.sigmaOf
    exact continuous_const.add (g3m2_coord_continuous n)
  unfold g2073s1ShiftSeq
  exact continuous_id.add ((continuous_const.sub hσ).smul continuous_const)

theorem g3m2_sourceF_continuousAt (n : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ContinuousAt (fun ψ : PotPair => p2Extend38 n (sourceF n ψ)) φ0 :=
  (p2Extend38 n).continuous.continuousAt.comp (sourceFamily.F_analytic n φ0 hφ0).continuousAt

theorem g3m2_shift_continuousAt (n : ℤ) (a : ℂ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ContinuousAt (fun ψ : PotPair => g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a) φ0 :=
  (g3m2_shift_continuous n a).continuousAt.comp (g3m2_sourceF_continuousAt n φ0 hφ0)

theorem g3m2_seg_continuousAt (m : ℤ) (φ0 : PotPair) (t0 : ℝ)
    (h1 : ContinuousAt (fun ψ : PotPair => lamMinus ψ m) φ0)
    (h2 : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0) :
    ContinuousAt (fun p : PotPair × ℝ => betaSegmentPoint m p.1 p.2) (φ0, t0) := by
  have hL : ContinuousAt (fun p : PotPair × ℝ => lamMinus p.1 m) (φ0, t0) :=
    ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0)) h1 continuous_fst.continuousAt
  have hM : ContinuousAt (fun p : PotPair × ℝ => muSeq p.1 m) (φ0, t0) :=
    ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0)) h2 continuous_fst.continuousAt
  have hT : ContinuousAt (fun p : PotPair × ℝ => (p.2 : ℂ)) (φ0, t0) :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousAt
  have h := hL.add (hT.mul (hM.sub hL))
  unfold betaSegmentPoint betaOmega
  exact h

theorem g3m2_seg_mem (C : ℤ → ℂ) (R : ℤ → ℝ) (m : ℤ) (ψ : PotPair)
    (hspec : IsolatingSpectral38 ψ C R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    betaSegmentPoint m ψ t ∈ ball (C m) (R m) := by
  have hL : lamMinus ψ m ∈ ball (C m) (R m) := (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have hM : muSeq ψ m ∈ ball (C m) (R m) := (hspec.1 m).2.1
  have h := (convex_ball (C m) (R m)).add_smul_sub_mem hL hM ht
  rw [Complex.real_smul] at h
  unfold betaSegmentPoint betaOmega
  exact h

theorem g3m2_dom (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (z : ℂ) (hz : z ∈ ball (C m) (R m)) :
    (ψ, z) ∈ a5OmittedRootDomain38 m := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
  have hpos : 0 < c⁻¹ / 2 := div_pos (inv_pos.2 hc0) two_pos
  have h2 : dist z (C m) < R m := mem_ball.1 hz
  refine ⟨hψ, fun k hk => g2073s1_tube_avoids C R c N hg ψ hspec m k hk z ?_⟩
  linarith

theorem g3m2_identity (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (a z : ℂ) (hz : z ∈ ball (C m) (R m)) (haz : a - z ≠ 0) :
    betaZeta n m ψ z =
      Complex.I * p2OmittedRatio38 m ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), z) /
        (a - z) := by
  have hdom : (ψ, z) ∈ a5OmittedRootDomain38 m := g3m2_dom n m hmn C R c N hg ψ hψ hspec z hz
  have hn : z ∉ segment ℝ (lamMinus ψ n) (lamPlus ψ n) :=
    g2073s1_tube_avoids C R c N hg ψ hspec m n (Ne.symm hmn) z (by
      have hc0 : 0 < c := lt_of_lt_of_le one_pos hg.2.2.1
      have hpos : 0 < c⁻¹ / 2 := div_pos (inv_pos.2 hc0) two_pos
      have h2 : dist z (C m) < R m := mem_ball.1 hz
      linarith)
  have hwn : standardRoot ψ n z ≠ 0 := g2073s1_std_ne ψ hψ n z hn
  exact g2073s1_psi_shift ψ n m hmn (p2Extend38 n (sourceF n ψ)) a z hdom hwn haz

/-! ## M2: uniform convergence of betaZeta along the collapsing sequence -/

theorem G3M2_betaZeta_unif (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    TendstoUniformlyOn (fun (j : ℕ) (t : ℝ) => betaZeta n m (v j) (betaSegmentPoint m (v j) t))
      (fun t : ℝ => betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      atTop (Icc ε 1) := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨U, hUo, hφ0U, hUgk, C, R, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hcen := angleCollapsed_center_values38 φ0 hgk0 m hgap
  set G : PotPair × ℝ → ℂ := fun p => betaZeta n m p.1 (betaSegmentPoint m p.1 p.2) with hG
  have hfun : (fun t : ℝ => betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      = fun t : ℝ => G (φ0, t) := by
    funext t
    simp only [hG, betaSegmentPoint, betaOmega, hcen.1]
  rw [hfun]
  have hLc : ContinuousAt (fun ψ : PotPair => lamMinus ψ m) φ0 :=
    (angleActual_collapsed_endpoint_continuity38 φ0 hgk0 m hgap).1
  have hMc : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0 :=
    (analyticOnNhd_muSeq_complex38 m φ0 hgk0).continuousAt
  -- pointwise joint continuity of G at (φ0, t0), t0 in Icc eps 1
  have hGc : ∀ t0 ∈ Icc ε 1, ContinuousAt G (φ0, t0) := by
    intro t0 ht0
    have ht01 : t0 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hε.1, ht0.1], ht0.2⟩
    have hw0ball : betaSegmentPoint m φ0 t0 ∈ ball (C m) (R m) :=
      g3m2_seg_mem C R m φ0 (hspecU φ0 hφ0U) t0 ht01
    have hwc : ContinuousAt (fun p : PotPair × ℝ => betaSegmentPoint m p.1 p.2) (φ0, t0) :=
      g3m2_seg_continuousAt m φ0 t0 hLc hMc
    have ha0 : (betaSegmentPoint m φ0 t0 + 1) - betaSegmentPoint m φ0 t0 ≠ 0 := by
      ring_nf
      exact one_ne_zero
    set a : ℂ := betaSegmentPoint m φ0 t0 + 1 with ha
    have hPc : ContinuousAt (fun p : PotPair × ℝ =>
        ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a), betaSegmentPoint m p.1 p.2))
        (φ0, t0) :=
      ContinuousAt.prodMk (ContinuousAt.prodMk continuousAt_fst
        (ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0))
          (g3m2_shift_continuousAt n a φ0 hφ0) continuous_fst.continuousAt)) hwc
    have hdomw0 : ((φ0, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ0)) n a),
        betaSegmentPoint m φ0 t0) ∈
        {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} :=
      g3m2_dom n m hmn C R c N hg φ0 hgk0 (hspecU φ0 hφ0U) _ hw0ball
    have hAn : ContinuousAt (p2OmittedRatio38 m)
        ((φ0, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ0)) n a), betaSegmentPoint m φ0 t0) :=
      ((G2_022 m).1 _ hdomw0).continuousAt
    have hRc : ContinuousAt (fun p : PotPair × ℝ =>
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          betaSegmentPoint m p.1 p.2)) (φ0, t0) :=
      ContinuousAt.comp (g := p2OmittedRatio38 m)
        (f := fun p : PotPair × ℝ => ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          betaSegmentPoint m p.1 p.2)) (x := (φ0, t0)) hAn hPc
    have hA : ContinuousAt (fun p : PotPair × ℝ => Complex.I *
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          betaSegmentPoint m p.1 p.2)) (φ0, t0) :=
      ContinuousAt.mul continuousAt_const hRc
    have hB : ContinuousAt (fun p : PotPair × ℝ => a - betaSegmentPoint m p.1 p.2) (φ0, t0) :=
      ContinuousAt.sub continuousAt_const hwc
    have hGac : ContinuousAt (fun p : PotPair × ℝ => Complex.I *
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          betaSegmentPoint m p.1 p.2) / (a - betaSegmentPoint m p.1 p.2)) (φ0, t0) :=
      ContinuousAt.div hA hB ha0
    have hwn : ∀ᶠ p in 𝓝 (φ0, t0), betaSegmentPoint m p.1 p.2 ∈ ball (C m) (R m) :=
      hwc.eventually_mem (isOpen_ball.mem_nhds hw0ball)
    have hne : ∀ᶠ p in 𝓝 (φ0, t0), a - betaSegmentPoint m p.1 p.2 ≠ 0 :=
      hB.eventually_ne ha0
    have hUn : U ×ˢ (univ : Set ℝ) ∈ 𝓝 (φ0, t0) :=
      prod_mem_nhds (hUo.mem_nhds hφ0U) univ_mem
    have hev : ∀ᶠ p in 𝓝 (φ0, t0), G p = Complex.I *
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          betaSegmentPoint m p.1 p.2) / (a - betaSegmentPoint m p.1 p.2) := by
      filter_upwards [hUn, hwn, hne] with p hpU hpw hpne
      exact g3m2_identity n m hmn C R c N hg p.1 (hUgk hpU.1) (hspecU p.1 hpU.1) a _ hpw hpne
    exact hGac.congr_of_eventuallyEq hev
  -- tube lemma: uniform in t over the compact interval
  have hK : IsCompact (Icc ε 1) := isCompact_Icc
  have hunif : ∀ η > 0, ∀ᶠ ψ in 𝓝 φ0, ∀ t ∈ Icc ε 1, dist (G (ψ, t)) (G (φ0, t)) < η := by
    intro η hη
    refine hK.eventually_forall_of_forall_eventually (P := fun ψ t => dist (G (ψ, t)) (G (φ0, t)) < η)
      ?_
    intro t0 ht0
    have h1 := hGc t0 ht0
    have h2 : ContinuousAt (fun p : PotPair × ℝ => G (φ0, p.2)) (φ0, t0) :=
      ContinuousAt.comp (f := fun p : PotPair × ℝ => (φ0, p.2)) (x := (φ0, t0)) h1
        (continuous_const.prodMk continuous_snd).continuousAt
    have hD : ContinuousAt (fun p : PotPair × ℝ => dist (G p) (G (φ0, p.2))) (φ0, t0) :=
      h1.dist h2
    have h0 : dist (G (φ0, t0)) (G (φ0, t0)) < η := by
      rw [dist_self]
      exact hη
    exact hD.tendsto.eventually (gt_mem_nhds h0)
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  filter_upwards [hv.eventually (hunif η hη)] with j hj
  intro t ht
  rw [dist_comm]
  exact hj t ht

end
end NlsGge.GKDefinitionDesign
