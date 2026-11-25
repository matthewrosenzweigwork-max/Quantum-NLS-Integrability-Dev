import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.Atomic.G2.G2074
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3RatioHost
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G3.G3SegmentHost
import NlsGge.ThirdConsultation.G3.G3M12Support

/- G3-020 S1 SUPPORT (proof development, AUTHOR; not self-reviewed). Supporting module for conjunct 1 of G3_020:
   forall delta > 0, eventually in j, forall t in Icc eps 1, standardRoot (v j) m (betaSegmentPoint m (v j) t) != 0
   and ||betaRootRatioAlong n m (v j) t - 1|| < delta.
   Route: at the collapsed limit phi0 (gamma2 = 0) the ratio is continuous jointly in (phi, t) at each (phi0, t0),
   t0 in Icc eps 1, with value 1 (normalizedRoot continuous by sourceF analytic; normalizedRoot phi0 = tauN phi0 from
   G2_074; standardRoot analytic in (phi,z) off the slit by stdRoot_analyticAt38). Then the tube lemma
   (IsCompact.eventually_forall_of_forall_eventually) and the sequence limit give the uniform statement.
   Also provides the shared helpers: g3s1_lam_eq, g3s1_omega_ne, g3s1_seg_eq, g3s1_gap_tendsto, g3s1_omega_tendsto. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-! ## Shared collapsed-point facts -/

theorem g3s1_lam_eq (φ : PotPair) (hφ : φ ∈ gkW) (m : ℤ) (hg : gamma2 φ m = 0) :
    lamPlus φ m = lamMinus φ m ∧ tauN φ m = lamMinus φ m := by
  rw [gamma2_value38 φ hφ m] at hg
  have h2 : lamPlus φ m - lamMinus φ m = 0 := (pow_eq_zero_iff two_ne_zero).1 hg
  have h3 : lamPlus φ m = lamMinus φ m := sub_eq_zero.1 h2
  refine ⟨h3, ?_⟩
  rw [tauN_value38 φ hφ m, h3]
  ring

theorem g3s1_omega_ne (m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW) (hnot : φ ∉ endpointSet m) :
    betaOmega m φ ≠ 0 := by
  intro h
  unfold betaOmega at h
  have hμ : muSeq φ m = lamMinus φ m := sub_eq_zero.1 h
  apply hnot
  show φ ∈ sourceW ∧ perChar φ (muSeq φ m) = 0
  refine ⟨hφ, ?_⟩
  rw [hμ]
  exact (lamSeq_enumeration38 φ).1 (2 * m)

theorem g3s1_seg_eq (φ : PotPair) (m : ℤ) (hlam : tauN φ m = lamMinus φ m) (t : ℝ) :
    tauN φ m + (t : ℂ) * (muSeq φ m - tauN φ m) = betaSegmentPoint m φ t := by
  unfold betaSegmentPoint betaOmega
  rw [hlam]

theorem g3s1_gap_tendsto (v : ℕ → PotPair) (φ0 : PotPair) (m : ℤ)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0)) :
    Tendsto (fun j : ℕ => gap (v j) m) atTop (𝓝 0) := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hlam := g3s1_lam_eq φ0 hgk0 m hgap
  have h := g3m1_collapsed_endpoints_tendsto m v φ0 hφ0 hgap hv
  have h' : Tendsto (fun j : ℕ => gap (v j) m) atTop (𝓝 (gap φ0 m)) := h.2.sub h.1
  have hg0 : gap φ0 m = 0 := by
    unfold gap
    rw [hlam.1, sub_self]
  rw [hg0] at h'
  exact h'

theorem g3s1_omega_tendsto (v : ℕ → PotPair) (φ0 : PotPair) (m : ℤ)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0)) :
    Tendsto (fun j : ℕ => betaOmega m (v j)) atTop (𝓝 (muSeq φ0 m - lamMinus φ0 m)) :=
  (g3m1_muSeq_tendsto m v φ0 hφ0 hv).sub (g3m1_collapsed_endpoints_tendsto m v φ0 hφ0 hgap hv).1

/-! ## Norm and standard-root continuity at the collapsed point -/

theorem g3s1_norm_continuousAt (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
    ContinuousAt (fun ψ : PotPair => normalizedRoot n m ψ) φ0 := by
  have hfun : (fun ψ : PotPair => normalizedRoot n m ψ) =
      fun ψ => countingCenter38 m + sourceF n ψ (⟨m, hmn⟩ : P2Index38 n) := by
    funext ψ
    unfold normalizedRoot
    rw [dif_pos hmn]
  rw [hfun]
  have hC : Continuous (fun x : P2Space38 n => x (⟨m, hmn⟩ : P2Index38 n)) := by
    refine (LipschitzWith.of_dist_le_mul (K := 1) fun s t => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
    exact G2071S1.coord_sub_norm_le s t _
  have hF : ContinuousAt (sourceF n) φ0 := (sourceFamily.F_analytic n φ0 hφ0).continuousAt
  exact continuousAt_const.add (hC.continuousAt.comp hF)

theorem g3s1_norm_value (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hgap : gamma2 φ0 m = 0) :
    normalizedRoot n m φ0 = tauN φ0 m := by
  obtain ⟨_, _, hφV, _, _, _, hA⟩ := G2_074 φ0 hφ0
  obtain ⟨A, hAfac, _, _⟩ := hA φ0 hφV n
  have h := hAfac ⟨m, hmn⟩
  change normalizedRoot n m φ0 = tauN φ0 m + gamma2 φ0 m * A ⟨m, hmn⟩ at h
  rw [h, hgap, zero_mul, add_zero]

theorem g3s1_std_analyticAt (m : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ gkW) (z0 : ℂ)
    (hne : tauN φ0 m - z0 ≠ 0)
    (hslit : 1 - (gamma2 φ0 m / 4) / (tauN φ0 m - z0) ^ 2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (fun p : PotPair × ℂ => standardRoot p.1 m p.2) (φ0, z0) := by
  have hf : AnalyticAt ℂ (fun p : PotPair × ℂ => p.1) (φ0, z0) := analyticAt_fst
  have hτ := (tauN_analytic m φ0 hφ0).comp hf
  have hg2 := (gamma2_analytic m φ0 hφ0).comp hf
  have hzz : AnalyticAt ℂ (fun p : PotPair × ℂ => p.2) (φ0, z0) := analyticAt_snd
  unfold standardRoot
  exact stdRoot_analyticAt38 hτ hg2 hzz hne hslit

/-! ## Pointwise joint continuity and the tube lemma -/

theorem g3s1_pointwise (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hgap : gamma2 φ0 m = 0) (hω : betaOmega m φ0 ≠ 0) (ε : ℝ) (hε : 0 < ε) (t0 : ℝ)
    (ht0 : t0 ∈ Icc ε 1) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ p : PotPair × ℝ in 𝓝 (φ0, t0),
      standardRoot p.1 m (betaSegmentPoint m p.1 p.2) ≠ 0 ∧
        ‖betaRootRatioAlong n m p.1 p.2 - 1‖ < δ := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hlam := g3s1_lam_eq φ0 hgk0 m hgap
  have hLc : ContinuousAt (fun ψ : PotPair => lamMinus ψ m) φ0 :=
    (angleActual_collapsed_endpoint_continuity38 φ0 hgk0 m hgap).1
  have hMc : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0 :=
    (analyticOnNhd_muSeq_complex38 m φ0 hgk0).continuousAt
  have hZ : ContinuousAt (fun p : PotPair × ℝ => betaSegmentPoint m p.1 p.2) (φ0, t0) :=
    g3m2_seg_continuousAt m φ0 t0 hLc hMc
  have ht0' : (t0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt (lt_of_lt_of_le hε ht0.1))
  have hz0 : tauN φ0 m - betaSegmentPoint m φ0 t0 ≠ 0 := by
    have hid : tauN φ0 m - betaSegmentPoint m φ0 t0 = -((t0 : ℂ) * betaOmega m φ0) := by
      unfold betaSegmentPoint
      rw [hlam.2]
      ring
    rw [hid]
    exact neg_ne_zero.2 (mul_ne_zero ht0' hω)
  have hstd0 : standardRoot φ0 m (betaSegmentPoint m φ0 t0) =
      tauN φ0 m - betaSegmentPoint m φ0 t0 := by
    unfold standardRoot stdRoot38
    rw [hgap]
    simp
  have hRval : betaRootRatioAlong n m φ0 t0 = 1 := by
    unfold betaRootRatioAlong
    rw [g3s1_norm_value n m hmn φ0 hφ0 hgap, hstd0]
    exact div_self hz0
  have hD0 : standardRoot φ0 m (betaSegmentPoint m φ0 t0) ≠ 0 := by
    rw [hstd0]
    exact hz0
  have hNc : ContinuousAt (fun p : PotPair × ℝ =>
      normalizedRoot n m p.1 - betaSegmentPoint m p.1 p.2) (φ0, t0) :=
    (ContinuousAt.comp (f := fun p : PotPair × ℝ => p.1) (x := (φ0, t0))
      (g3s1_norm_continuousAt n m hmn φ0 hφ0) continuous_fst.continuousAt).sub hZ
  have hSc : ContinuousAt (fun p : PotPair × ℝ =>
      standardRoot p.1 m (betaSegmentPoint m p.1 p.2)) (φ0, t0) := by
    have hA := g3s1_std_analyticAt m φ0 hgk0 (betaSegmentPoint m φ0 t0) hz0
      (by rw [hgap]; simp)
    have hmap : ContinuousAt (fun p : PotPair × ℝ => (p.1, betaSegmentPoint m p.1 p.2))
        (φ0, t0) :=
      ContinuousAt.prodMk (f := fun p : PotPair × ℝ => p.1) continuous_fst.continuousAt hZ
    exact ContinuousAt.comp (f := fun p : PotPair × ℝ => (p.1, betaSegmentPoint m p.1 p.2))
      (x := (φ0, t0)) (g := fun q : PotPair × ℂ => standardRoot q.1 m q.2) hA.continuousAt hmap
  have hRc : ContinuousAt (fun p : PotPair × ℝ => betaRootRatioAlong n m p.1 p.2) (φ0, t0) := by
    unfold betaRootRatioAlong
    exact ContinuousAt.div hNc hSc hD0
  have hNe : ∀ᶠ p : PotPair × ℝ in 𝓝 (φ0, t0),
      standardRoot p.1 m (betaSegmentPoint m p.1 p.2) ≠ 0 :=
    hSc.eventually_ne hD0
  have hRtend : Tendsto (fun p : PotPair × ℝ => betaRootRatioAlong n m p.1 p.2) (𝓝 (φ0, t0))
      (𝓝 (betaRootRatioAlong n m φ0 t0)) := hRc.tendsto
  rw [hRval] at hRtend
  have hRe := Metric.tendsto_nhds.1 hRtend δ hδ
  filter_upwards [hNe, hRe] with p h1 h2
  rw [dist_eq_norm] at h2
  exact ⟨h1, h2⟩

theorem g3s1_uniform (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ∀ t ∈ Icc ε 1,
      standardRoot (v j) m (betaSegmentPoint m (v j) t) ≠ 0 ∧
        ‖betaRootRatioAlong n m (v j) t - 1‖ < δ := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hω : betaOmega m φ0 ≠ 0 := g3s1_omega_ne m φ0 hφ0 hnot
  have hK : IsCompact (Icc ε 1) := isCompact_Icc
  have hT : ∀ᶠ φ in 𝓝 φ0, ∀ t ∈ Icc ε 1,
      standardRoot φ m (betaSegmentPoint m φ t) ≠ 0 ∧
        ‖betaRootRatioAlong n m φ t - 1‖ < δ := by
    refine hK.eventually_forall_of_forall_eventually
      (P := fun φ t => standardRoot φ m (betaSegmentPoint m φ t) ≠ 0 ∧
        ‖betaRootRatioAlong n m φ t - 1‖ < δ) ?_
    intro t0 ht0
    exact g3s1_pointwise n m hmn φ0 hφ0 hgap hω ε hε.1 t0 ht0 δ hδ
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hv.eventually hT)
  exact ⟨J, fun j hj t ht => hJ j hj t ht⟩

/-- Conjunct 1 of G3_020 (supporting form). -/
theorem g3s1_conj1 (n m : ℤ) (hmn : m ≠ n) (v : ℕ → PotPair) (φ0 : PotPair)
    (hφ0 : φ0 ∈ sourceW) (hgap : gamma2 φ0 m = 0) (hv : Tendsto v atTop (𝓝 φ0))
    (hnot : φ0 ∉ endpointSet m) (ε : ℝ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ∀ δ : ℝ, 0 < δ → ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      ∀ t ∈ Icc ε 1,
        standardRoot (v j) m (betaSegmentPoint m (v j) t) ≠ 0 ∧
          ‖betaRootRatioAlong n m (v j) t-1‖ < δ :=
  fun δ hδ => g3s1_uniform n m hmn v φ0 hφ0 hgap hv hnot ε hε δ hδ

end
end NlsGge.GKDefinitionDesign
