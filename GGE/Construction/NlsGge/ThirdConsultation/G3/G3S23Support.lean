import Mathlib
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2022
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3RatioHost
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G3.G3SegmentHost
import NlsGge.ThirdConsultation.G3.G3M12Support
import NlsGge.ThirdConsultation.G3.G3S1Support

                                                                                                                    
                                                                                      
                                                                
                                                                                                                  
                                                                                                                        
                                                                                                                      
                                         
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-! ## Continuity of betaZeta along the segment at a fixed isolating point -/

theorem g3s2_betaZeta_seg_contAt (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (t0 : ℝ) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun t : ℝ => betaZeta n m ψ (betaSegmentPoint m ψ t)) t0 := by
  have hw0 : betaSegmentPoint m ψ t0 ∈ ball (C m) (R m) := g3m2_seg_mem C R m ψ hspec t0 ht0
  have hZ : Continuous (fun t : ℝ => betaSegmentPoint m ψ t) := by
    unfold betaSegmentPoint betaOmega
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = betaSegmentPoint m ψ t0 + 1 := ⟨_, rfl⟩
  have hdom : ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t0) ∈
      {p : (PotPair × Lib.L2Seq) × ℂ | (p.1.1, p.2) ∈ a5OmittedRootDomain38 m} :=
    g3m2_dom n m hmn C R c N hg ψ hψ hspec _ hw0
  have hAn : ContinuousAt (p2OmittedRatio38 m)
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t0) :=
    ((G2_022 m).1 _ hdom).continuousAt
  have hP : ContinuousAt (fun t : ℝ =>
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t)) t0 :=
    ContinuousAt.prodMk (ContinuousAt.prodMk continuousAt_const continuousAt_const) hZ.continuousAt
  have hR : ContinuousAt (fun t : ℝ => p2OmittedRatio38 m
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t)) t0 :=
    ContinuousAt.comp (g := p2OmittedRatio38 m)
      (f := fun t : ℝ => ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t))
      (x := t0) hAn hP
  have hden : ContinuousAt (fun t : ℝ => a - betaSegmentPoint m ψ t) t0 :=
    continuousAt_const.sub hZ.continuousAt
  have hne : a - betaSegmentPoint m ψ t0 ≠ 0 := by
    rw [ha]
    simp
  have hF : ContinuousAt (fun t : ℝ => Complex.I * p2OmittedRatio38 m
      ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t) /
      (a - betaSegmentPoint m ψ t)) t0 :=
    (ContinuousAt.mul continuousAt_const hR).div hden hne
  have hev : (fun t : ℝ => betaZeta n m ψ (betaSegmentPoint m ψ t)) =ᶠ[𝓝 t0]
      (fun t : ℝ => Complex.I * p2OmittedRatio38 m
        ((ψ, g2073s1ShiftSeq (p2Extend38 n (sourceF n ψ)) n a), betaSegmentPoint m ψ t) /
        (a - betaSegmentPoint m ψ t)) := by
    have hball : ∀ᶠ t in 𝓝 t0, betaSegmentPoint m ψ t ∈ ball (C m) (R m) :=
      hZ.continuousAt.eventually_mem (isOpen_ball.mem_nhds hw0)
    have hne' : ∀ᶠ t in 𝓝 t0, a - betaSegmentPoint m ψ t ≠ 0 := hden.eventually_ne hne
    filter_upwards [hball, hne'] with t ht1 ht2
    exact g3m2_identity n m hmn C R c N hg ψ hψ hspec a _ ht1 ht2
  exact hF.congr_of_eventuallyEq hev

theorem g3s2_betaZeta_contOn (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => betaZeta n m ψ (betaSegmentPoint m ψ t)) (Icc ε 1) :=
  fun t ht => (g3s2_betaZeta_seg_contAt n m hmn C R c N hg ψ hψ hspec t
    ⟨by linarith [ht.1], ht.2⟩).continuousWithinAt

/-! ## Ratio continuity on [eps,1] for psi with small gap/omega -/

theorem g3s2_sqrt_ne (w : ℂ) (hw : w ≠ 0) : Complex.sqrt w ≠ 0 := by
  show w ^ (2⁻¹ : ℂ) ≠ 0
  rw [Complex.cpow_def_of_ne_zero hw]
  exact Complex.exp_ne_zero _

theorem g3s2_key (m : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceW) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : betaOmega m ψ ≠ 0) (hratio : ‖gap ψ m / betaOmega m ψ‖ ≤ ε / 2) (t : ℝ)
    (ht : t ∈ Icc ε 1) :
    tauN ψ m - betaSegmentPoint m ψ t ≠ 0 ∧
    (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t) ^ 2)) ∈ Complex.slitPlane ∧
    standardRoot ψ m (betaSegmentPoint m ψ t) =
      (tauN ψ m - betaSegmentPoint m ψ t) *
        Complex.sqrt (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t) ^ 2)) := by
  obtain ⟨_, hd, hw, hid⟩ := G3_019 m ψ hψ ε t hε hε1 hω hratio ht
  refine ⟨hd, ?_, hid⟩
  have hsq : gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t) ^ 2) =
      (gap ψ m / (2 * (tauN ψ m - betaSegmentPoint m ψ t))) ^ 2 := by
    rw [div_pow, mul_pow]
    norm_num
  rw [hsq]
  generalize gap ψ m / (2 * (tauN ψ m - betaSegmentPoint m ψ t)) = w at hw ⊢
  have hw2 : ‖w ^ 2‖ ≤ 1 / 9 := by
    rw [norm_pow]
    have h0 := norm_nonneg w
    nlinarith
  have hre : 0 < (1 - w ^ 2).re := by
    have h1 : (w ^ 2).re ≤ ‖w ^ 2‖ := Complex.re_le_norm _
    rw [Complex.sub_re, Complex.one_re]
    linarith
  exact Complex.mem_slitPlane_iff.2 (Or.inl hre)

theorem g3s2_ratio_contOn (n m : ℤ) (ψ : PotPair) (hψ : ψ ∈ sourceW) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hω : betaOmega m ψ ≠ 0) (hratio : ‖gap ψ m / betaOmega m ψ‖ ≤ ε / 2) :
    ContinuousOn (fun t : ℝ => betaRootRatioAlong n m ψ t) (Icc ε 1) := by
  have hZ : Continuous (fun t : ℝ => betaSegmentPoint m ψ t) := by
    unfold betaSegmentPoint betaOmega
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hDcont : ContinuousOn (fun t : ℝ => standardRoot ψ m (betaSegmentPoint m ψ t)) (Icc ε 1) := by
    intro t0 ht0
    obtain ⟨hd0, hslit0, _⟩ := g3s2_key m ψ hψ ε hε hε1 hω hratio t0 ht0
    have hdc : ContinuousAt (fun t : ℝ => tauN ψ m - betaSegmentPoint m ψ t) t0 :=
      continuousAt_const.sub hZ.continuousAt
    have h4 : (4 : ℂ) * (tauN ψ m - betaSegmentPoint m ψ t0) ^ 2 ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)
    have hbase : ContinuousAt (fun t : ℝ =>
        1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t) ^ 2)) t0 :=
      continuousAt_const.sub (ContinuousAt.div continuousAt_const
        (continuousAt_const.mul (hdc.pow 2)) h4)
    have hcond : 0 ≤ (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t0) ^ 2)).re ∨
        (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t0) ^ 2)).im ≠ 0 :=
      (Complex.mem_slitPlane_iff.1 hslit0).imp (fun h => le_of_lt h) (fun h => h)
    have hsqrt : ContinuousAt (fun t : ℝ =>
        Complex.sqrt (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t) ^ 2))) t0 :=
      ContinuousAt.comp (g := Complex.sqrt) (Complex.continuousAt_sqrt hcond) hbase
    have hE : ContinuousAt (fun t : ℝ => (tauN ψ m - betaSegmentPoint m ψ t) *
        Complex.sqrt (1 - gap ψ m ^ 2 / (4 * (tauN ψ m - betaSegmentPoint m ψ t) ^ 2))) t0 :=
      hdc.mul hsqrt
    exact hE.continuousWithinAt.congr
      (fun t ht => (g3s2_key m ψ hψ ε hε hε1 hω hratio t ht).2.2)
      (g3s2_key m ψ hψ ε hε hε1 hω hratio t0 ht0).2.2
  have hDne : ∀ t ∈ Icc ε 1, standardRoot ψ m (betaSegmentPoint m ψ t) ≠ 0 := by
    intro t ht
    obtain ⟨hd0, hslit0, hid0⟩ := g3s2_key m ψ hψ ε hε hε1 hω hratio t ht
    rw [hid0]
    exact mul_ne_zero hd0 (g3s2_sqrt_ne _ (Complex.slitPlane_ne_zero hslit0))
  unfold betaRootRatioAlong
  exact ContinuousOn.div (continuousOn_const.sub hZ.continuousOn) hDcont hDne

theorem g3s2_density_contOn (n m : ℤ) (hmn : m ≠ n) (C : ℤ → ℂ) (R : ℤ → ℝ) (c : ℝ) (N : ℕ)
    (hg : IsolatingGeometry38 C R c N) (ψ : PotPair) (hψ : ψ ∈ sourceW) (hgk : ψ ∈ gkW)
    (hspec : IsolatingSpectral38 ψ C R) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hω : betaOmega m ψ ≠ 0) (hratio : ‖gap ψ m / betaOmega m ψ‖ ≤ ε / 2) :
    ContinuousOn (fun t : ℝ => betaSegmentDensity n m ψ t) (Icc ε 1) := by
  unfold betaSegmentDensity
  exact ((g3s2_ratio_contOn n m ψ hψ ε hε hε1 hω hratio).mul
    (g3s2_betaZeta_contOn n m hmn C R c N hg ψ hgk hspec ε hε)).mul continuousOn_const

/-! ## S2: eventual integrability of the canonical-sheet density -/

theorem g3s2_eventually_integrable (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hvmem : ∀ j, v j ∈ sourceW) (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ j in atTop, IntervalIntegrable (betaSegmentDensity n m (v j)) volume ε 1 := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨U, hUo, hφ0U, hUgk, C, R, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hω0 : betaOmega m φ0 ≠ 0 := g3s1_omega_ne m φ0 hφ0 hnot
  have hωT := g3s1_omega_tendsto v φ0 m hφ0 hgap hv
  have hgT := g3s1_gap_tendsto v φ0 m hφ0 hgap hv
  have hωlim : muSeq φ0 m - lamMinus φ0 m ≠ 0 := hω0
  have hq : Tendsto (fun j : ℕ => gap (v j) m / betaOmega m (v j)) atTop (𝓝 0) := by
    have h := hgT.div hωT hωlim
    rwa [zero_div] at h
  have hratio : ∀ᶠ j in atTop, ‖gap (v j) m / betaOmega m (v j)‖ ≤ ε / 2 := by
    have h := Metric.tendsto_nhds.1 hq (ε / 2) (by linarith [hε.1])
    filter_upwards [h] with j hj
    rw [dist_zero_right] at hj
    exact hj.le
  have hωne : ∀ᶠ j in atTop, betaOmega m (v j) ≠ 0 := hωT.eventually_ne hωlim
  have hvU : ∀ᶠ j in atTop, v j ∈ U := hv.eventually (hUo.mem_nhds hφ0U)
  filter_upwards [hvU, hratio, hωne] with j hU hr hω
  have hc := g3s2_density_contOn n m hmn C R c N hg (v j) (hvmem j) (hUgk hU)
    (hspecU (v j) hU) ε hε.1 hε.2.le hω hr
  exact ContinuousOn.intervalIntegrable (by rw [uIcc_of_le hε.2.le]; exact hc)

/-! ## S3: integrability of the collapsed integrand -/

theorem g3s3_integrable (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hgap : gamma2 φ0 m = 0) (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ =>
      betaZeta n m φ0 (tauN φ0 m+(t : ℂ)*(muSeq φ0 m-tauN φ0 m)) *
        (muSeq φ0 m-tauN φ0 m)) volume ε 1 := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hlam := g3s1_lam_eq φ0 hgk0 m hgap
  obtain ⟨U, hUo, hφ0U, hUgk, C, R, c, N, hg, hspecU⟩ := g2019_leaf_family φ0 hgk0
  have hfun : (fun t : ℝ => betaZeta n m φ0 (tauN φ0 m+(t : ℂ)*(muSeq φ0 m-tauN φ0 m)) *
        (muSeq φ0 m-tauN φ0 m)) =
      fun t : ℝ => betaZeta n m φ0 (betaSegmentPoint m φ0 t) * (muSeq φ0 m - tauN φ0 m) := by
    funext t
    rw [g3s1_seg_eq φ0 m hlam.2 t]
  rw [hfun]
  have hc := g3s2_betaZeta_contOn n m hmn C R c N hg φ0 hgk0 (hspecU φ0 hφ0U) ε hε.1
  exact ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le hε.2.le]
    exact hc.mul continuousOn_const)

end
end NlsGge.GKDefinitionDesign
