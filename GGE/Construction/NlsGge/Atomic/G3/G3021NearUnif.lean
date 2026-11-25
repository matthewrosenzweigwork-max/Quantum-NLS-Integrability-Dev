import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2022
import NlsGge.Atomic.G2.G2074
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G3.G3S1Support
import NlsGge.Atomic.G3.G3021NearBase

                                                                                                   
                                                                                   
                                                                                                                               
                                                                                                                            
                                                                                                                             
                                                                                                                            
                                                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem near_zeta_unif (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    TendstoUniformlyOn (fun (j : ℕ) (t : ℝ) => betaZeta n m (v j) (nearSegPoint m (v j) t))
      (fun t : ℝ => betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      atTop (Icc ε 1) := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨U, hUo, hφ0U, hUgk, C, R, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hcen := G3021N.near_collapsed_value m φ0 hφ0 hgap
  set G : PotPair × ℝ → ℂ := fun p => betaZeta n m p.1 (nearSegPoint m p.1 p.2) with hG
  have hfun : (fun t : ℝ => betaZeta n m φ0 (tauN φ0 m + (t : ℂ) * (muSeq φ0 m - tauN φ0 m)))
      = fun t : ℝ => G (φ0, t) := by
    funext t
    simp only [hG, nearSegPoint, nearOmega, hcen]
  rw [hfun]
  have hLc : ContinuousAt (fun ψ : PotPair => nearEnd m ψ) φ0 :=
    G3021N.near_continuousAt m φ0 hφ0 hgap
  have hMc : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0 :=
    (analyticOnNhd_muSeq_complex38 m φ0 hgk0).continuousAt
  have hGc : ∀ t0 ∈ Icc ε 1, ContinuousAt G (φ0, t0) := by
    intro t0 ht0
    have ht01 : t0 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hε.1, ht0.1], ht0.2⟩
    have hw0ball : nearSegPoint m φ0 t0 ∈ ball (C m) (R m) :=
      G3021N.seg_mem m φ0 (hspecU φ0 hφ0U) t0 ht01
    have hwc : ContinuousAt (fun p : PotPair × ℝ => nearSegPoint m p.1 p.2) (φ0, t0) :=
      G3021N.seg_continuousAt_joint m φ0 t0 hLc hMc
    have ha0 : (nearSegPoint m φ0 t0 + 1) - nearSegPoint m φ0 t0 ≠ 0 := by
      ring_nf
      exact one_ne_zero
    set a : ℂ := nearSegPoint m φ0 t0 + 1 with ha
    have hPc : ContinuousAt (fun p : PotPair × ℝ =>
        ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a), nearSegPoint m p.1 p.2))
        (φ0, t0) :=
      ContinuousAt.prodMk (ContinuousAt.prodMk continuousAt_fst
        (ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0))
          (g3m2_shift_continuousAt n a φ0 hφ0) continuous_fst.continuousAt)) hwc
    have hdomw0 : ((φ0, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ0)) n a),
        nearSegPoint m φ0 t0) ∈
        {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} :=
      g3m2_dom n m hmn C R c N hg φ0 hgk0 (hspecU φ0 hφ0U) _ hw0ball
    have hAn : ContinuousAt (p2OmittedRatio38 m)
        ((φ0, g2073s1ShiftSeq (p2Extend38 n (sourceF n φ0)) n a), nearSegPoint m φ0 t0) :=
      ((G2_022 m).1 _ hdomw0).continuousAt
    have hRc : ContinuousAt (fun p : PotPair × ℝ =>
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          nearSegPoint m p.1 p.2)) (φ0, t0) :=
      ContinuousAt.comp (g := p2OmittedRatio38 m)
        (f := fun p : PotPair × ℝ => ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          nearSegPoint m p.1 p.2)) (x := (φ0, t0)) hAn hPc
    have hA : ContinuousAt (fun p : PotPair × ℝ => Complex.I *
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          nearSegPoint m p.1 p.2)) (φ0, t0) :=
      ContinuousAt.mul continuousAt_const hRc
    have hB : ContinuousAt (fun p : PotPair × ℝ => a - nearSegPoint m p.1 p.2) (φ0, t0) :=
      ContinuousAt.sub continuousAt_const hwc
    have hGac : ContinuousAt (fun p : PotPair × ℝ => Complex.I *
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          nearSegPoint m p.1 p.2) / (a - nearSegPoint m p.1 p.2)) (φ0, t0) :=
      ContinuousAt.div hA hB ha0
    have hwn : ∀ᶠ p in 𝓝 (φ0, t0), nearSegPoint m p.1 p.2 ∈ ball (C m) (R m) :=
      hwc.eventually_mem (isOpen_ball.mem_nhds hw0ball)
    have hne : ∀ᶠ p in 𝓝 (φ0, t0), a - nearSegPoint m p.1 p.2 ≠ 0 :=
      hB.eventually_ne ha0
    have hUn : U ×ˢ (univ : Set ℝ) ∈ 𝓝 (φ0, t0) :=
      prod_mem_nhds (hUo.mem_nhds hφ0U) univ_mem
    have hev : ∀ᶠ p in 𝓝 (φ0, t0), G p = Complex.I *
        p2OmittedRatio38 m ((p.1, g2073s1ShiftSeq (p2Extend38 n (sourceF n p.1)) n a),
          nearSegPoint m p.1 p.2) / (a - nearSegPoint m p.1 p.2) := by
      filter_upwards [hUn, hwn, hne] with p hpU hpw hpne
      exact g3m2_identity n m hmn C R c N hg p.1 (hUgk hpU.1) (hspecU p.1 hpU.1) a _ hpw hpne
    exact hGac.congr_of_eventuallyEq hev
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

theorem near_ratio_pointwise (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hgap : gamma2 φ0 m = 0) (hω : nearOmega m φ0 ≠ 0) (ε : ℝ) (hε : 0 < ε) (t0 : ℝ)
    (ht0 : t0 ∈ Icc ε 1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ p : PotPair × ℝ in 𝓝 (φ0, t0),
      standardRoot p.1 m (nearSegPoint m p.1 p.2) ≠ 0 ∧
        ‖nearRatio n m p.1 p.2 - 1‖ < δ := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hnv := G3021N.near_collapsed_value m φ0 hφ0 hgap
  have hLc : ContinuousAt (fun ψ : PotPair => nearEnd m ψ) φ0 :=
    G3021N.near_continuousAt m φ0 hφ0 hgap
  have hMc : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0 :=
    (analyticOnNhd_muSeq_complex38 m φ0 hgk0).continuousAt
  have hZ : ContinuousAt (fun p : PotPair × ℝ => nearSegPoint m p.1 p.2) (φ0, t0) :=
    G3021N.seg_continuousAt_joint m φ0 t0 hLc hMc
  have ht0' : (t0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hε ht0.1))
  have hz0 : tauN φ0 m - nearSegPoint m φ0 t0 ≠ 0 := by
    have hid : tauN φ0 m - nearSegPoint m φ0 t0 = -((t0 : ℂ) * nearOmega m φ0) := by
      unfold nearSegPoint
      rw [hnv]
      ring
    rw [hid]
    exact neg_ne_zero.2 (mul_ne_zero ht0' hω)
  have hstd0 : standardRoot φ0 m (nearSegPoint m φ0 t0) =
      tauN φ0 m - nearSegPoint m φ0 t0 := by
    unfold standardRoot stdRoot38
    rw [hgap]
    simp
  have hRval : nearRatio n m φ0 t0 = 1 := by
    unfold nearRatio
    rw [g3s1_norm_value n m hmn φ0 hφ0 hgap, hstd0]
    exact div_self hz0
  have hD0 : standardRoot φ0 m (nearSegPoint m φ0 t0) ≠ 0 := by
    rw [hstd0]
    exact hz0
  have hNc : ContinuousAt (fun p : PotPair × ℝ =>
      normalizedRoot n m p.1 - nearSegPoint m p.1 p.2) (φ0, t0) :=
    (ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0))
      (g3s1_norm_continuousAt n m hmn φ0 hφ0) continuous_fst.continuousAt).sub hZ
  have hSc : ContinuousAt (fun p : PotPair × ℝ =>
      standardRoot p.1 m (nearSegPoint m p.1 p.2)) (φ0, t0) := by
    have hA := g3s1_std_analyticAt m φ0 hgk0 (nearSegPoint m φ0 t0) hz0
      (by rw [hgap]; simp)
    have hmap : ContinuousAt (fun p : PotPair × ℝ => (p.1, nearSegPoint m p.1 p.2))
        (φ0, t0) :=
      ContinuousAt.prodMk (f := fun p : PotPair × ℝ => p.1) continuous_fst.continuousAt hZ
    exact ContinuousAt.comp (f := fun p : PotPair × ℝ => (p.1, nearSegPoint m p.1 p.2))
      (x := (φ0, t0)) (g := fun q : PotPair × ℂ => standardRoot q.1 m q.2) hA.continuousAt hmap
  have hRc : ContinuousAt (fun p : PotPair × ℝ => nearRatio n m p.1 p.2) (φ0, t0) := by
    unfold nearRatio
    exact ContinuousAt.div hNc hSc hD0
  have hNe : ∀ᶠ p : PotPair × ℝ in 𝓝 (φ0, t0),
      standardRoot p.1 m (nearSegPoint m p.1 p.2) ≠ 0 :=
    hSc.eventually_ne hD0
  have hRtend : Tendsto (fun p : PotPair × ℝ => nearRatio n m p.1 p.2) (𝓝 (φ0, t0))
      (𝓝 (nearRatio n m φ0 t0)) := hRc.tendsto
  rw [hRval] at hRtend
  have hRe := Metric.tendsto_nhds.1 hRtend δ hδ
  filter_upwards [hNe, hRe] with p h1 h2
  rw [dist_eq_norm] at h2
  exact ⟨h1, h2⟩

theorem near_ratio_uniform (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ t ∈ Icc ε 1,
      standardRoot (v j) m (nearSegPoint m (v j) t) ≠ 0 ∧
        ‖nearRatio n m (v j) t - 1‖ < δ := by
  have hω : nearOmega m φ0 ≠ 0 := G3021N.omega_ne m φ0 hφ0 hnot
  have hK : IsCompact (Icc ε 1) := isCompact_Icc
  have hT : ∀ᶠ φ in 𝓝 φ0, ∀ t ∈ Icc ε 1,
      standardRoot φ m (nearSegPoint m φ t) ≠ 0 ∧
        ‖nearRatio n m φ t - 1‖ < δ := by
    refine hK.eventually_forall_of_forall_eventually
      (P := fun φ t => standardRoot φ m (nearSegPoint m φ t) ≠ 0 ∧
        ‖nearRatio n m φ t - 1‖ < δ) ?_
    intro t0 ht0
    exact near_ratio_pointwise n m hmn φ0 hφ0 hgap hω ε hε.1 t0 ht0 δ hδ
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hv.eventually hT)
  exact ⟨J, fun j hj t ht => hJ j hj t ht⟩

end
end NlsGge.GKDefinitionDesign
