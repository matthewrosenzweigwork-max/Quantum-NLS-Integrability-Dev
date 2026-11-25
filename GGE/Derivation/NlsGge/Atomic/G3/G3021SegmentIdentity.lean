import Mathlib
import NlsGge.Atomic.G3.G3017
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.Atomic.G2.G2048

/- G3-021 supporting module PRODUCTION01 (proof development, AUTHOR; not self-reviewed; NOT the G3_021 head).
   Target NlsGge/Atomic/G3/G3021SegmentIdentity.lean, namespace NlsGge.GKDefinitionDesign.
   Content (source GK 15.2 p. 83, "beta = integral along the straight segment lamMinus -> mu"):
   (A) seg_ftc: FTC along a straight segment starting at a zero tau of perChar, for the primitive canonRoot38 * S
       (a copy of G3017Aux.segment_integral_generic with the analyticity of the integrand replaced by an
       integrability hypothesis, since the integrand has a t^(-1/2) singularity at t = 0 off the collapsed set);
   (B) beta_segment: for sourceW potentials whose segment (lamMinus, mu] avoids the gap slits,
       offDiagonalBeta = (antiDiscrim/canonRoot38)(mu) * integral_0^1 betaSegmentDensity;
   (C) seg_avoids: the geometric hypothesis of (B) holds when mu is not on a gap slit and
       ||mu - lamMinus|| <= ||mu - lamPlus||.
   No hypothesis beyond what each lemma states; used later by G3_021 (type "lamMinus is nearest endpoint"). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G3021Aux

theorem seg_ftc (φ : PotPair) (hgk : φ ∈ gkW) (τ μ : ℂ) (hne : μ ≠ τ)
    (hR : ∀ t : ℝ, 0 < t → t ≤ 1 → (φ, τ + (t : ℂ) * (μ - τ)) ∈ rootDomain38)
    (hτ0 : perChar φ τ = 0) (S b Ψ : ℂ → ℂ)
    (hS : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → AnalyticAt ℂ S (τ + (t : ℂ) * (μ - τ)))
    (hode : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      perChar φ (τ + (t : ℂ) * (μ - τ)) * deriv S (τ + (t : ℂ) * (μ - τ)) +
        (deriv (perChar φ) (τ + (t : ℂ) * (μ - τ)) / 2) * S (τ + (t : ℂ) * (μ - τ)) =
        Ψ (τ + (t : ℂ) * (μ - τ)))
    (hG : ∀ t : ℝ, 0 < t → t ≤ 1 →
      Ψ (τ + (t : ℂ) * (μ - τ)) / canonRoot38 φ (τ + (t : ℂ) * (μ - τ)) =
        b (τ + (t : ℂ) * (μ - τ)))
    (hint : IntervalIntegrable (fun t : ℝ => b (τ + (t : ℂ) * (μ - τ)) * (μ - τ)) volume 0 1) :
    (∫ t in (0 : ℝ)..1, b (τ + (t : ℂ) * (μ - τ)) * (μ - τ)) =
      canonRoot38 φ μ * S μ := by
  have hμτ : μ - τ ≠ 0 := sub_ne_zero.mpr hne
  let z : ℝ → ℂ := fun t => τ + (t : ℂ) * (μ - τ)
  have hzc : Continuous z := by
    show Continuous (fun t : ℝ => τ + (t : ℂ) * (μ - τ))
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hzne : ∀ t : ℝ, 0 < t → z t ≠ τ := by
    intro t ht h
    have h0 : (t : ℂ) * (μ - τ) = 0 := by
      have : τ + (t : ℂ) * (μ - τ) = τ + 0 := by rw [add_zero]; exact h
      exact add_left_cancel this
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact ht.ne' (Complex.ofReal_eq_zero.mp h1)
    · exact hμτ h1
  have hz1 : z 1 = μ := by
    show τ + ((1 : ℝ) : ℂ) * (μ - τ) = μ
    rw [Complex.ofReal_one, one_mul]
    ring
  have hz0 : z 0 = τ := by
    show τ + ((0 : ℝ) : ℂ) * (μ - τ) = τ
    rw [Complex.ofReal_zero, zero_mul, add_zero]
  let Φ : ℝ → ℂ := fun t => if t = 0 then 0 else canonRoot38 φ (z t) * S (z t)
  have hΦc : ContinuousOn Φ (Icc (0 : ℝ) 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst ht0
      have key : ∀ s ∈ Icc (0 : ℝ) 1,
          ‖Φ s‖ ^ 2 = ‖perChar φ (z s)‖ * ‖S (z s)‖ ^ 2 := by
        intro s hs
        by_cases hs0 : s = 0
        · subst hs0
          simp [Φ, hz0, hτ0]
        · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
          have hroot := hR s hsp hs.2
          have hc2 := canonRoot_sq38 φ hgk (z s) hroot.2
          have hn : ‖canonRoot38 φ (z s)‖ ^ 2 = ‖perChar φ (z s)‖ := by
            rw [← hc2, norm_pow]
          simp only [Φ, if_neg hs0]
          rw [norm_mul, mul_pow, hn]
      have hpc : ContinuousAt (fun s : ℝ => ‖perChar φ (z s)‖ * ‖S (z s)‖ ^ 2) 0 := by
        have h1 : ContinuousAt (perChar φ) (z 0) :=
          ((analyticOnNhd_perChar_z φ) _ (Set.mem_univ _)).continuousAt
        have h2 : ContinuousAt S (z 0) := (hS 0 ht).continuousAt
        exact ((h1.comp hzc.continuousAt).norm).mul
          (((h2.comp hzc.continuousAt).norm).pow 2)
      have hval : ‖perChar φ (z 0)‖ * ‖S (z 0)‖ ^ 2 = 0 := by
        rw [hz0, hτ0]; simp
      have hT : Tendsto (fun s : ℝ => ‖perChar φ (z s)‖ * ‖S (z s)‖ ^ 2) (𝓝 0) (𝓝 0) := by
        have := hpc.tendsto
        rwa [hval] at this
      have hT2 : Tendsto (fun s : ℝ => ‖Φ s‖ ^ 2) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
        refine (hT.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (key s hs).symm
      have hT3 : Tendsto (fun s : ℝ => ‖Φ s‖) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
        have h := (Real.continuous_sqrt.tendsto 0).comp hT2
        simp only [Real.sqrt_zero] at h
        refine h.congr (fun s => ?_)
        simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]
      have hT4 : Tendsto Φ (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) :=
        tendsto_zero_iff_norm_tendsto_zero.mpr hT3
      have hΦ0 : Φ 0 = 0 := by simp [Φ]
      show Tendsto Φ (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 (Φ 0))
      rw [hΦ0]
      exact hT4
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hroot := hR t htpos ht.2
      have hcA : ContinuousAt (canonRoot38 φ) (z t) :=
        (G3017Aux.canonRoot_analyticAt_slice φ _ hroot).continuousAt
      have hSA : ContinuousAt S (z t) := (hS t ht).continuousAt
      have hc : ContinuousAt (fun s : ℝ => canonRoot38 φ (z s) * S (z s)) t :=
        (hcA.comp hzc.continuousAt).mul (hSA.comp hzc.continuousAt)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ne.mem_nhds ht0] with s hs
      simp only [Φ, if_neg hs]
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (b (z t) * (μ - τ)) t := by
    intro t ht
    have htpos : 0 < t := ht.1
    have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hroot := hR t htpos ht.2.le
    have hcA := G3017Aux.canonRoot_analyticAt_slice φ _ hroot
    have hcd : HasDerivAt (canonRoot38 φ) (deriv (canonRoot38 φ) (z t)) (z t) :=
      hcA.differentiableAt.hasDerivAt
    have hSd : HasDerivAt S (deriv S (z t)) (z t) :=
      (hS t htI).differentiableAt.hasDerivAt
    have hpd : HasDerivAt (perChar φ) (deriv (perChar φ) (z t)) (z t) :=
      ((analyticOnNhd_perChar_z φ) _ (Set.mem_univ _)).differentiableAt.hasDerivAt
    have hev : (fun w => canonRoot38 φ w ^ 2) =ᶠ[𝓝 (z t)] perChar φ := by
      have hopen : IsOpen {w : ℂ | (φ, w) ∈ rootDomain38} :=
        isOpen_rootDomain38.preimage (continuous_const.prodMk continuous_id)
      filter_upwards [hopen.mem_nhds hroot] with w hw
      exact canonRoot_sq38 φ hgk w hw.2
    have hsq : 2 * canonRoot38 φ (z t) * deriv (canonRoot38 φ) (z t) =
        deriv (perChar φ) (z t) := by
      have h1 := hcd.pow 2
      have h2 := h1.congr_of_eventuallyEq hev.symm
      have h3 := h2.unique hpd
      norm_num at h3
      linear_combination h3
    have hcn : canonRoot38 φ (z t) ≠ 0 := canonRoot_ne_zero38 φ hgk _ hroot.2
    have hb' : b (z t) = deriv (canonRoot38 φ) (z t) * S (z t) +
        canonRoot38 φ (z t) * deriv S (z t) := by
      have hc2 : perChar φ (z t) = canonRoot38 φ (z t) ^ 2 := hev.self_of_nhds.symm
      rw [← hG t htpos ht.2.le, div_eq_iff hcn, ← hode t htI, hc2, ← hsq]
      ring
    have hprod : HasDerivAt (fun w => canonRoot38 φ w * S w)
        (deriv (canonRoot38 φ) (z t) * S (z t) + canonRoot38 φ (z t) * deriv S (z t))
        (z t) := hcd.mul hSd
    have hzd : HasDerivAt z (μ - τ) t := by
      have h1 : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 t :=
        (hasDerivAt_id t).ofReal_comp
      have h2 := (h1.mul_const (μ - τ)).const_add τ
      rwa [one_mul] at h2
    have hΦeq : Φ =ᶠ[𝓝 t] ((fun w => canonRoot38 φ w * S w) ∘ z) := by
      filter_upwards [isOpen_ne.mem_nhds htpos.ne'] with s hs
      simp only [Φ, if_neg hs, Function.comp]
    have h := (hprod.scomp t hzd).congr_of_eventuallyEq hΦeq
    convert h using 1
    rw [hb', smul_eq_mul]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (zero_le_one' ℝ) hΦc hder hint
  rw [hFTC]
  have hΦ1 : Φ 1 = canonRoot38 φ μ * S μ := by
    simp only [Φ, if_neg one_ne_zero, hz1]
  have hΦ0 : Φ 0 = 0 := by simp [Φ]
  rw [hΦ1, hΦ0, sub_zero]

theorem beta_segment (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ sourceW)
    (hω : betaOmega m φ ≠ 0)
    (hav : ∀ t : ℝ, 0 < t → t ≤ 1 → betaSegmentPoint m φ t ∉ gapSegments38 φ)
    (hint : IntervalIntegrable (betaSegmentDensity n m φ) volume 0 1) :
    offDiagonalBeta n m φ =
      (antiDiscrim φ (muSeq φ m) / canonRoot38 φ (muSeq φ m)) *
        ∫ t in (0 : ℝ)..1, betaSegmentDensity n m φ t := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨S, hS, hode, hbeta⟩ := G3017Aux.beta_eq n m hmn φ hφ
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ hgk
  have hτB : lamMinus φ m ∈ ball (discC φ m) (discR φ m) :=
    (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have hμB : muSeq φ m ∈ ball (discC φ m) (discR φ m) := (hspec.1 m).2.1
  have hzB : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m) ∈ ball (discC φ m) (discR φ m) := by
    intro t ht
    have h := (convex_ball (discC φ m) (discR φ m)).add_smul_sub_mem hτB hμB ht
    rw [Complex.real_smul] at h
    exact h
  have hseg1 : betaSegmentPoint m φ 1 = muSeq φ m := by
    unfold betaSegmentPoint betaOmega
    rw [Complex.ofReal_one, one_mul]; ring
  have hR : ∀ t : ℝ, 0 < t → t ≤ 1 →
      (φ, lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m)) ∈ rootDomain38 :=
    fun t ht ht1 => ⟨hgk, hav t ht ht1⟩
  have hμR : (φ, muSeq φ m) ∈ rootDomain38 := by
    refine ⟨hgk, ?_⟩
    have := hav 1 one_pos le_rfl
    rwa [hseg1] at this
  have hcne : canonRoot38 φ (muSeq φ m) ≠ 0 := canonRoot_ne_zero38 φ hgk _ hμR.2
  have hτ0 : perChar φ (lamMinus φ m) = 0 := rawBetaPerCharLowerTipZero38 ⟨φ, hgk⟩ m
  have hne : muSeq φ m ≠ lamMinus φ m := fun h => hω (by unfold betaOmega; rw [h]; ring)
  have hG : ∀ t : ℝ, 0 < t → t ≤ 1 →
      psi n φ (lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m)) /
          canonRoot38 φ (lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m)) =
        ((normalizedRoot n m φ - (lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m))) /
          standardRoot φ m (lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m))) *
          betaZeta n m φ (lamMinus φ m + (t : ℂ) * (muSeq φ m - lamMinus φ m)) := by
    intro t ht ht1
    have key := (G2_048 φ hgk (p2Extend38 n (sourceF n φ)) n m hmn _ (hR t ht ht1)).2.2.2
    rw [← normalizedRoot_eq_sigmaOf n m φ hmn] at key
    exact key
  have hI := seg_ftc φ hgk (lamMinus φ m) (muSeq φ m) hne hR hτ0 S
    (fun w => ((normalizedRoot n m φ - w) / standardRoot φ m w) * betaZeta n m φ w)
    (psi n φ)
    (fun t ht => hS _ (hzB t ht)) (fun t ht => hode _ (hzB t ht)) hG hint
  have hI' : (∫ t in (0 : ℝ)..1, betaSegmentDensity n m φ t) =
      canonRoot38 φ (muSeq φ m) * S (muSeq φ m) := hI
  rw [hbeta, hI']
  field_simp

theorem seg_avoids (m : ℤ) (φ : PotPair) (hφ : φ ∈ sourceW)
    (hω : betaOmega m φ ≠ 0) (hμ : muSeq φ m ∉ gapSegments38 φ)
    (hnear : ‖muSeq φ m - lamMinus φ m‖ ≤ ‖muSeq φ m - lamPlus φ m‖) :
    ∀ t : ℝ, 0 < t → t ≤ 1 → betaSegmentPoint m φ t ∉ gapSegments38 φ := by
  intro t ht ht1 hz
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ hgk
  have hτB : lamMinus φ m ∈ ball (discC φ m) (discR φ m) :=
    (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have hμB : muSeq φ m ∈ ball (discC φ m) (discR φ m) := (hspec.1 m).2.1
  have hzB : betaSegmentPoint m φ t ∈ ball (discC φ m) (discR φ m) := by
    have h := (convex_ball (discC φ m) (discR φ m)).add_smul_sub_mem hτB hμB
      (show t ∈ Icc (0 : ℝ) 1 from ⟨ht.le, ht1⟩)
    rw [Complex.real_smul] at h
    exact h
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
  by_cases hkm : k = m
  · subst hkm
    obtain ⟨a, b, ha, hb, hab, hzab⟩ := hk
    have hzeq : (t : ℂ) * betaOmega k φ = (b : ℂ) * (lamPlus φ k - lamMinus φ k) := by
      have h1 : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
      have h2 : a • lamMinus φ k + b • lamPlus φ k = betaSegmentPoint k φ t := hzab
      simp only [Complex.real_smul] at h2
      unfold betaSegmentPoint at h2
      have ha' : (a : ℂ) = 1 - b := by linear_combination h1
      rw [ha'] at h2
      linear_combination -h2
    by_cases hγ : lamPlus φ k - lamMinus φ k = 0
    · rw [hγ, mul_zero] at hzeq
      rcases mul_eq_zero.1 hzeq with h | h
      · exact ht.ne' (Complex.ofReal_eq_zero.1 h)
      · exact hω h
    · set r : ℝ := b / t with hr
      have hrω : betaOmega k φ = (r : ℂ) * (lamPlus φ k - lamMinus φ k) := by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ht.ne'
        rw [hr, Complex.ofReal_div]
        field_simp
        linear_combination hzeq
      have hr0 : 0 ≤ r := div_nonneg hb ht.le
      by_cases hr1 : r ≤ 1
      · apply hμ
        refine Set.mem_iUnion.2 ⟨k, ?_⟩
        refine ⟨1 - r, r, by linarith, hr0, by ring, ?_⟩
        simp only [Complex.real_smul]
        push_cast
        unfold betaOmega at hrω
        linear_combination (-1 : ℂ) * hrω
      · push_neg at hr1
        have hn1 : ‖muSeq φ k - lamMinus φ k‖ = r * ‖lamPlus φ k - lamMinus φ k‖ := by
          have : muSeq φ k - lamMinus φ k = (r : ℂ) * (lamPlus φ k - lamMinus φ k) := hrω
          rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0]
        have hn2 : ‖muSeq φ k - lamPlus φ k‖ = (r - 1) * ‖lamPlus φ k - lamMinus φ k‖ := by
          have : muSeq φ k - lamPlus φ k = ((r - 1 : ℝ) : ℂ) * (lamPlus φ k - lamMinus φ k) := by
            push_cast
            unfold betaOmega at hrω
            linear_combination hrω
          rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        have hpos : 0 < ‖lamPlus φ k - lamMinus φ k‖ := norm_pos_iff.2 hγ
        rw [hn1, hn2] at hnear
        nlinarith
  · exact closedBall_avoids_other_gaps φ hgk m k hkm _
      (Metric.ball_subset_closedBall hzB) hk

end G3021Aux
end
end NlsGge.GKDefinitionDesign
