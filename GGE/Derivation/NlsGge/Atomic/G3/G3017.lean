import Mathlib
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2072Host
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.ThirdConsultation.G3.G3003Host
import NlsGge.Atomic.G3.G3002
import NlsGge.Atomic.G3.G3003
import NlsGge.Atomic.G3.G3SegmentHost
import NlsGge.Atomic.G3.G3ZetaHost
import NlsGge.Atomic.G4.G4017
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.StdRootBranchesConvergence
import NlsGge.GK38.StdRootBranchesDomain
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.DirichletRealBridge
import Armstrong.Frozen.RawBeta.GKArcCurve38
import Armstrong.Frozen.RawBeta.GKArcSheet38
import Armstrong.Frozen.RawBeta.GKPathMiddleIntegral38
import Armstrong.Frozen.RawBeta.GKRootedArcChain38
import Armstrong.Frozen.RawBeta.GKRootedArcIntegrand38
import Armstrong.Frozen.RawBeta.GKRootedC1Arc38
import Armstrong.Frozen.RawBeta.GKOriginalSlit38
import Armstrong.Frozen.RawBeta.GKPathCompactIntegrable38
import Armstrong.Work.RawBetaRootedPath
import Armstrong.Work.RawBetaActualCoefficient
import Armstrong.Work.RawBetaSpectralInput

/- G3_017 PRODUCTION04 (proof development, AUTHOR; not semantically reviewed by its author).
   Target NlsGge/Atomic/G3/G3017.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from Pro round 9 (followup7) STATEMENTS/G3.md section "## G3-017".
   Route (source GK 15.2, pp. 83 and 85):
   (1) beta = antiDiscrim(mu) * S(mu), S the analytic coefficient of the actual Armstrong primitive
       (rawBetaPsiCoefficientOfZeroPeriod38 + rawBetaAllPathsOfPrimitiveCoefficient38), identified with the
       landed offDiagonalBeta by uniqueness of the improper limit (G3003).
   (2) On the collapsed disc canonRoot38 * S is a primitive of betaZeta along the straight segment tau -> mu
       (canonRoot^2 = perChar, psi/canonRoot = betaZeta from G3_002), vanishing at tau; FTC gives
       collapsedBetaFinalSegment = canonRoot(mu) * S(mu).
   (3) sheet ratio^2 = 1 from antiDiscrim^2 = perChar = canonRoot^2 at the Dirichlet root; local constancy
       from continuity of phi |-> (phi, mu_m phi) into the open rootDomain38 and of antiDiscrim, canonRoot38.
   Armstrong REVIEW_ONLY file RawBetaPathPrimitive is NOT imported: its off-diagonal primitive argument is re-proved natively (namespace G3017Aux.C6,
   copied from proof development G3005C6CORE_PRODUCTION01, itself a native re-proof of RawBetaPathPrimitive/RawBetaRootDerivative).
   No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section
namespace G3017Aux

theorem tau_eq_lamMinus (m : ℤ) (φ : PotPair) (hφ : φ ∈ gkW) (hgap : gamma2 φ m = 0) :
    lamPlus φ m = lamMinus φ m ∧ tauN φ m = lamMinus φ m := by
  have hsq : (lamPlus φ m - lamMinus φ m) ^ 2 = 0 := by
    rw [← gamma2_value38 φ hφ m, hgap]
  have hPM : lamPlus φ m = lamMinus φ m :=
    sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  refine ⟨hPM, ?_⟩
  rw [tauN_value38 φ hφ m, hPM]
  ring

theorem mu_facts (m : ℤ) (φ : PotPair) (hφ : φ ∈ collapsedSet m \ endpointSet m) :
    φ ∈ gkW ∧ perChar φ (muSeq φ m) ≠ 0 ∧ muSeq φ m ≠ tauN φ m ∧
    muSeq φ m ∉ gapSegments38 φ ∧ (φ, muSeq φ m) ∈ rootDomain38 ∧
    canonRoot38 φ (muSeq φ m) ≠ 0 := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ.1.1
  have hP : perChar φ (muSeq φ m) ≠ 0 := fun h => hφ.2 ⟨hφ.1.1, h⟩
  obtain ⟨hPM, hτ⟩ := tau_eq_lamMinus m φ hgk hφ.1.2
  have hlow : perChar φ (lamMinus φ m) = 0 := rawBetaPerCharLowerTipZero38 ⟨φ, hgk⟩ m
  have hneL : muSeq φ m ≠ lamMinus φ m := fun h => hP (by rw [h]; exact hlow)
  have hav : muSeq φ m ∉ gapSegments38 φ := by
    refine G4017Aux.avoids_all φ hgk m ?_
    rw [hPM, segment_same]
    exact fun h => hneL (Set.mem_singleton_iff.mp h)
  exact ⟨hgk, hP, by rw [hτ]; exact hneL, hav, ⟨hgk, hav⟩, canonRoot_ne_zero38 φ hgk _ hav⟩

theorem ratio_sq (m : ℤ) (φ : PotPair) (hgk : φ ∈ gkW) (hav : muSeq φ m ∉ gapSegments38 φ) :
    (antiDiscrim φ (muSeq φ m) / canonRoot38 φ (muSeq φ m)) ^ 2 = 1 := by
  have hne := canonRoot_ne_zero38 φ hgk _ hav
  have hA := dirichlet_perChar_eq_anti_sq38 φ _ (muSeq_root38 φ m)
  have hC := canonRoot_sq38 φ hgk _ hav
  rw [div_pow, ← hA, ← hC]
  exact div_self (pow_ne_zero 2 hne)

theorem eq_of_sq_one_of_dist_lt {a b : ℂ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (h : dist a b < 1) : a = b := by
  have hpm : ∀ x : ℂ, x ^ 2 = 1 → x = 1 ∨ x = -1 := by
    intro x hx
    have : (x - 1) * (x + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.1 this with h | h
    · left; linear_combination h
    · right; linear_combination h
  rcases hpm a ha with rfl | rfl <;> rcases hpm b hb with rfl | rfl
  · rfl
  · rw [Complex.dist_eq] at h; norm_num at h
  · rw [Complex.dist_eq] at h; norm_num at h
  · rfl

theorem local_ratio (m : ℤ) (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW)
    (hroot : (φ0, muSeq φ0 m) ∈ rootDomain38) :
    ∃ V : Set PotPair, IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW ∧
      ∀ φ ∈ V, (φ, muSeq φ m) ∈ rootDomain38 ∧ canonRoot38 φ (muSeq φ m) ≠ 0 ∧
        perChar φ (muSeq φ m) ≠ 0 ∧
        antiDiscrim φ (muSeq φ m) / canonRoot38 φ (muSeq φ m) =
          antiDiscrim φ0 (muSeq φ0 m) / canonRoot38 φ0 (muSeq φ0 m) := by
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  have hmu : ContinuousAt (fun ψ : PotPair => muSeq ψ m) φ0 :=
    ((analyticOnNhd_muSeq_complex38 m) φ0 hgk0).continuousAt
  have hg : ContinuousAt (fun ψ : PotPair => (ψ, muSeq ψ m)) φ0 :=
    continuousAt_id.prodMk hmu
  have hA : ContinuousAt (fun p : PotPair × ℂ => antiDiscrim p.1 p.2) (φ0, muSeq φ0 m) :=
    (analyticOnNhd_antiDiscrim _ (Set.mem_univ _)).continuousAt
  have hCr : ContinuousAt (fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (φ0, muSeq φ0 m) :=
    (canonRoot_analytic38 _ hroot).continuousAt
  have hne0 : canonRoot38 φ0 (muSeq φ0 m) ≠ 0 :=
    canonRoot_ne_zero38 φ0 hgk0 _ hroot.2
  have hA' : ContinuousAt (fun ψ : PotPair => antiDiscrim ψ (muSeq ψ m)) φ0 :=
    ContinuousAt.comp (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ m)) hA hg
  have hC' : ContinuousAt (fun ψ : PotPair => canonRoot38 ψ (muSeq ψ m)) φ0 :=
    ContinuousAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
      (f := fun ψ : PotPair => (ψ, muSeq ψ m)) hCr hg
  have hρ : ContinuousAt (fun ψ : PotPair =>
      antiDiscrim ψ (muSeq ψ m) / canonRoot38 ψ (muSeq ψ m)) φ0 := hA'.div hC' hne0
  have hev : ∀ᶠ ψ in 𝓝 φ0, ψ ∈ sourceW ∧ (ψ, muSeq ψ m) ∈ rootDomain38 ∧
      dist (antiDiscrim ψ (muSeq ψ m) / canonRoot38 ψ (muSeq ψ m))
        (antiDiscrim φ0 (muSeq φ0 m) / canonRoot38 φ0 (muSeq φ0 m)) < 1 := by
    have h1 : sourceW ∈ 𝓝 φ0 := sourceFamily.W_open.mem_nhds hφ0
    have h2 : {ψ : PotPair | (ψ, muSeq ψ m) ∈ rootDomain38} ∈ 𝓝 φ0 :=
      hg.preimage_mem_nhds (isOpen_rootDomain38.mem_nhds hroot)
    have h3 := hρ.eventually (Metric.ball_mem_nhds
      (antiDiscrim φ0 (muSeq φ0 m) / canonRoot38 φ0 (muSeq φ0 m)) one_pos)
    filter_upwards [h1, h2, h3] with ψ hψ1 hψ2 hψ3
    exact ⟨hψ1, hψ2, hψ3⟩
  obtain ⟨V, hVsub, hVopen, hφ0V⟩ := _root_.mem_nhds_iff.mp hev
  refine ⟨V, hVopen, hφ0V, fun ψ hψ => (hVsub hψ).1, fun ψ hψ => ?_⟩
  obtain ⟨hW, hR, hd⟩ := hVsub hψ
  have hgk : ψ ∈ gkW := sourceFamily.W_gk hW
  have hne := canonRoot_ne_zero38 ψ hgk _ hR.2
  have hsq := ratio_sq m ψ hgk hR.2
  have hsq0 := ratio_sq m φ0 hgk0 hroot.2
  have hPc : perChar ψ (muSeq ψ m) ≠ 0 := by
    rw [← canonRoot_sq38 ψ hgk _ hR.2]
    exact pow_ne_zero 2 hne
  exact ⟨hR, hne, hPc, eq_of_sq_one_of_dist_lt hsq hsq0 hd⟩

theorem canonRoot_analyticAt_slice (φ : PotPair) (w : ℂ) (hw : (φ, w) ∈ rootDomain38) :
    AnalyticAt ℂ (canonRoot38 φ) w :=
  AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
    (f := fun w : ℂ => (φ, w)) (canonRoot_analytic38 _ hw)
    (analyticAt_const.prod analyticAt_id)

theorem segment_integral_generic (φ : PotPair) (hgk : φ ∈ gkW) (B : Set ℂ)
    (hB : Convex ℝ B) (τ μ : ℂ) (hτB : τ ∈ B) (hμB : μ ∈ B) (hne : μ ≠ τ)
    (hR : ∀ w ∈ B, w ≠ τ → (φ, w) ∈ rootDomain38) (hτ0 : perChar φ τ = 0)
    (S b Ψ : ℂ → ℂ) (hS : AnalyticOnNhd ℂ S B) (hb : AnalyticOnNhd ℂ b B)
    (hode : ∀ w ∈ B, perChar φ w * deriv S w + (deriv (perChar φ) w / 2) * S w = Ψ w)
    (hG : ∀ w ∈ B, w ≠ τ → Ψ w / canonRoot38 φ w = b w) :
    IntervalIntegrable (fun t : ℝ => b (τ + (t : ℂ) * (μ - τ)) * (μ - τ)) volume 0 1 ∧
    (∫ t in (0 : ℝ)..1, b (τ + (t : ℂ) * (μ - τ)) * (μ - τ)) =
      canonRoot38 φ μ * S μ := by
  have hμτ : μ - τ ≠ 0 := sub_ne_zero.mpr hne
  let z : ℝ → ℂ := fun t => τ + (t : ℂ) * (μ - τ)
  have hzc : Continuous z := by
    show Continuous (fun t : ℝ => τ + (t : ℂ) * (μ - τ))
    exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hzB : ∀ t ∈ Icc (0 : ℝ) 1, z t ∈ B := by
    intro t ht
    have h := hB.add_smul_sub_mem hτB hμB ht
    rw [Complex.real_smul] at h
    exact h
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
  have hcont : ContinuousOn (fun t : ℝ => b (z t) * (μ - τ)) (Icc (0 : ℝ) 1) :=
    (hb.continuousOn.comp hzc.continuousOn hzB).mul continuousOn_const
  have hint : IntervalIntegrable (fun t : ℝ => b (z t) * (μ - τ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hcont
  refine ⟨hint, ?_⟩
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
          have hroot := hR _ (hzB s hs) (hzne s hsp)
          have hc2 := canonRoot_sq38 φ hgk (z s) hroot.2
          have hn : ‖canonRoot38 φ (z s)‖ ^ 2 = ‖perChar φ (z s)‖ := by
            rw [← hc2, norm_pow]
          simp only [Φ, if_neg hs0]
          rw [norm_mul, mul_pow, hn]
      have hpc : ContinuousAt (fun s : ℝ => ‖perChar φ (z s)‖ * ‖S (z s)‖ ^ 2) 0 := by
        have h1 : ContinuousAt (perChar φ) (z 0) :=
          ((analyticOnNhd_perChar_z φ) _ (Set.mem_univ _)).continuousAt
        have h2 : ContinuousAt S (z 0) := (hS _ (by rw [hz0]; exact hτB)).continuousAt
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
      have hroot := hR _ (hzB t ht) (hzne t htpos)
      have hcA : ContinuousAt (canonRoot38 φ) (z t) :=
        (canonRoot_analyticAt_slice φ _ hroot).continuousAt
      have hSA : ContinuousAt S (z t) := (hS _ (hzB t ht)).continuousAt
      have hc : ContinuousAt (fun s : ℝ => canonRoot38 φ (z s) * S (z s)) t :=
        (hcA.comp hzc.continuousAt).mul (hSA.comp hzc.continuousAt)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ne.mem_nhds ht0] with s hs
      simp only [Φ, if_neg hs]
  have hder : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt Φ (b (z t) * (μ - τ)) t := by
    intro t ht
    have htpos : 0 < t := ht.1
    have hzt : z t ∈ B := hzB t ⟨ht.1.le, ht.2.le⟩
    have hroot := hR _ hzt (hzne t htpos)
    have hcA := canonRoot_analyticAt_slice φ _ hroot
    have hcd : HasDerivAt (canonRoot38 φ) (deriv (canonRoot38 φ) (z t)) (z t) :=
      hcA.differentiableAt.hasDerivAt
    have hSd : HasDerivAt S (deriv S (z t)) (z t) :=
      (hS _ hzt).differentiableAt.hasDerivAt
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
      rw [← hG _ hzt (hzne t htpos), div_eq_iff hcn, ← hode _ hzt, hc2, ← hsq]
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

namespace C6
open intervalIntegral

theorem hasDerivAt_comp_left {f : ℂ → ℂ} {g h : ℝ → ℂ} {f' h' : ℂ} {t : ℝ}
    (hg : ContinuousAt g t) (hf : HasDerivAt f f' (g t))
    (hh : HasDerivAt h h' t) (hf' : f' ≠ 0)
    (hcomp : f ∘ g =ᶠ[nhds t] h) :
    HasDerivAt g (h' / f') t := by
  have hinv : Function.LeftInverse
      ((ContinuousLinearMap.toSpanSingleton ℂ f'⁻¹).restrictScalars ℝ)
      ((ContinuousLinearMap.toSpanSingleton ℂ f').restrictScalars ℝ) := by
    intro z
    simp [hf']
  have hd := HasFDerivAt.of_comp_of_leftInverse hg
    (hf.hasFDerivAt.restrictScalars ℝ) hh.hasFDerivAt hcomp hinv
  simpa [div_eq_mul_inv] using hd.hasDerivAt

theorem root_hasDerivAt {s : ℝ → ℂ} {t : ℝ} {q : ℂ}
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (hsq : HasDerivAt (fun u => s u ^ 2) q t) :
    HasDerivAt s (q / (2 * s t)) t := by
  have hpow : HasDerivAt (fun z : ℂ => z ^ 2) (2 * s t) (s t) := by
    simpa using hasDerivAt_pow 2 (s t)
  exact hasDerivAt_comp_left hsc hpow hsq
    (mul_ne_zero (by norm_num) hsn) Filter.EventuallyEq.rfl

theorem sheet_primitive_hasDerivAt
    {P Ψ R : ℂ → ℂ} {γ s : ℝ → ℂ} {t : ℝ} {P' R' γ' : ℂ}
    (hγ : HasDerivAt γ γ' t) (hP : HasDerivAt P P' (γ t))
    (hR : HasDerivAt R R' (γ t))
    (hsc : ContinuousAt s t) (hsn : s t ≠ 0)
    (he : (fun u => s u ^ 2) =ᶠ[nhds t] P ∘ γ)
    (hODE : P (γ t) * R' + (P' / 2) * R (γ t) = Ψ (γ t)) :
    HasDerivAt (fun u => s u * R (γ u)) ((Ψ (γ t) / s t) * γ') t := by
  have hs : HasDerivAt s ((P' * γ') / (2 * s t)) t :=
    root_hasDerivAt hsc hsn ((hP.comp t hγ).congr_of_eventuallyEq he)
  have hsq : s t ^ 2 = P (γ t) := he.self_of_nhds
  apply (hs.mul (hR.comp t hγ)).congr_deriv
  calc
    ((P' * γ') / (2 * s t)) * R (γ t) + s t * (R' * γ')
        = ((s t ^ 2 * R' + (P' / 2) * R (γ t)) / s t) * γ' := by
            field_simp [hsn]
            ring
    _ = ((Ψ (γ t) / s t) * γ') := by rw [hsq, hODE]

/-- The sheet of a rooted arc is nonzero on the open parameter interval. -/
theorem arc_sheet_ne_zero (φ : GKPotential38) (m : ℤ) (a : GKRootedC1Arc38 φ m)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : GKArcSheet38 a t ≠ 0 := by
  intro hz
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  apply rawBetaPerCharNonzeroOnSlit38 φ m (GKArcCurve38 a t) (a.2.2.2.2.2.2 t ht)
  have hsq : GKArcSheet38 a t ^ 2 = perChar φ.1 (GKArcCurve38 a t) := a.2.2.2.2.1 t htc
  simpa only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hsq.symm

/-- Primitive of the rooted arc integrand built from an analytic coefficient. -/
def arcPrim (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ) (a : GKRootedC1Arc38 φ m) (t : ℝ) : ℂ :=
  GKArcSheet38 a t * R (GKArcCurve38 a t)

theorem arcPrim_continuousOn (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (a : GKRootedC1Arc38 φ m) :
    ContinuousOn (arcPrim φ m R a) (Icc (0 : ℝ) 1) :=
  a.2.2.2.1.mul (hR.continuousOn.comp a.2.1 (fun t ht => a.2.2.2.2.2.1 t ht))

theorem arcPrim_hasDerivAt (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (a : GKRootedC1Arc38 φ m) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (arcPrim φ m R a) (GKRootedArcIntegrand38 n m F φ a t) t := by
  have htc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have htn : Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hγd : DifferentiableAt ℝ (GKArcCurve38 a) t :=
    (a.2.2.1.differentiableOn (by norm_num) t htc).differentiableAt htn
  have hsc : ContinuousAt (GKArcSheet38 a) t := a.2.2.2.1.continuousAt htn
  have hsn := arc_sheet_ne_zero φ m a t ht
  have he : (fun u => GKArcSheet38 a u ^ 2) =ᶠ[nhds t]
      perChar φ.1 ∘ GKArcCurve38 a := by
    filter_upwards [htn] with u hu
    exact a.2.2.2.2.1 u hu
  exact sheet_primitive_hasDerivAt hγd.hasDerivAt
    ((analyticOnNhd_perChar_z φ.1) _ (mem_univ _)).differentiableAt.hasDerivAt
    (hR _ (a.2.2.2.2.2.1 t htc)).differentiableAt.hasDerivAt
    hsc hsn he (hODE _ (a.2.2.2.2.2.2 t ht))

theorem arc_integral_of_prim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k)
    (φ : GKPotential38) (R : ℂ → ℂ)
    (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (a : GKRootedC1Arc38 φ m) (u v : ℝ)
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1)
    (hi : IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume u v) :
    (∫ t in u..v, GKRootedArcIntegrand38 n m F φ a t) =
      arcPrim φ m R a v - arcPrim φ m R a u :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
    ((arcPrim_continuousOn φ m R hR a).mono
      (fun t ht => ⟨hu.trans ht.1, ht.2.trans hv⟩))
    (fun t ht => arcPrim_hasDerivAt n m F φ R hR hODE a t
      ⟨hu.trans_lt ht.1, ht.2.trans_le hv⟩) hi

theorem arcPrim_join (φ : GKPotential38) (m : ℤ) (R : ℂ → ℂ)
    (a b : GKRootedC1Arc38 φ m) (h : GKRootedArcJoin38 φ m a b) :
    arcPrim φ m R a 1 = arcPrim φ m R b 0 := by
  simp only [arcPrim, h.1, h.2.1]

theorem middle_prim_telescopes
    (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (arcs : List (GKRootedC1Arc38 φ m)) :
    ∀ (a b : GKRootedC1Arc38 φ m),
      GKRootedArcChain38 φ m (a :: (arcs ++ [b])) →
      (∀ d ∈ arcs, (∫ t in (0 : ℝ)..1, GKRootedArcIntegrand38 n m F φ d t) =
        arcPrim φ m R d 1 - arcPrim φ m R d 0) →
      arcPrim φ m R a 1 + GKPathMiddleIntegral38 n m F φ arcs = arcPrim φ m R b 0 := by
  induction arcs with
  | nil =>
      intro a b hc hi
      simpa only [GKPathMiddleIntegral38, add_zero] using arcPrim_join φ m R a b hc.1
  | cons d tail ih =>
      intro a b hc hi
      have hjoin := arcPrim_join φ m R a d hc.1
      have hd := hi d List.mem_cons_self
      have htail := ih d b hc.2 (fun e he => hi e (List.mem_cons_of_mem _ he))
      calc
        arcPrim φ m R a 1 + GKPathMiddleIntegral38 n m F φ (d :: tail)
            = arcPrim φ m R d 1 + GKPathMiddleIntegral38 n m F φ tail := by
                  rw [GKPathMiddleIntegral38, hjoin, hd]
                  ring
        _ = arcPrim φ m R b 0 := htail

/-- The hypothesis shape of a truncated rooted path (compact integrability). -/
def ChainInt (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m) : Prop :=
  ∀ ε η : ℝ, 0 < ε → 0 < η → ε + η < 1 →
    IntervalIntegrable (GKRootedArcIntegrand38 n m F φ f) volume ε 1 ∧
    (∀ a ∈ mids, IntervalIntegrable (GKRootedArcIntegrand38 n m F φ a) volume 0 1) ∧
    IntervalIntegrable (GKRootedArcIntegrand38 n m F φ l) volume 0 (1 - η)

/-- The truncated chain integral. -/
def ChainTrunc (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (q : ℝ × ℝ) : ℂ :=
  (∫ t in q.1..(1 : ℝ), GKRootedArcIntegrand38 n m F φ f t) +
    GKPathMiddleIntegral38 n m F φ mids +
    (∫ t in (0 : ℝ)..(1 - q.2), GKRootedArcIntegrand38 n m F φ l t)

theorem trunc_prim (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (hchain : GKRootedArcChain38 φ m (f :: (mids ++ [l])))
    (hint : ChainInt n m F φ f mids l) (q : ℝ × ℝ) (hq : 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1) :
    ChainTrunc n m F φ f mids l q = arcPrim φ m R l (1 - q.2) - arcPrim φ m R f q.1 := by
  obtain ⟨hif, him, hil⟩ := hint q.1 q.2 hq.1 hq.2.1 hq.2.2
  have hf := arc_integral_of_prim n m F φ R hR hODE f q.1 1 hq.1.le
    (by linarith [hq.2.1, hq.2.2]) le_rfl hif
  have hl := arc_integral_of_prim n m F φ R hR hODE l 0 (1 - q.2) le_rfl
    (by linarith [hq.2.1, hq.2.2]) (by linarith [hq.2.1]) hil
  have hm := middle_prim_telescopes n m F φ R mids f l hchain
    (fun d hd => arc_integral_of_prim n m F φ R hR hODE d 0 1
      le_rfl zero_le_one le_rfl (him d hd))
  unfold ChainTrunc
  rw [hf, hl]
  calc
    _ = (arcPrim φ m R l (1 - q.2) - arcPrim φ m R f q.1) +
        (arcPrim φ m R f 1 + GKPathMiddleIntegral38 n m F φ mids -
          arcPrim φ m R l 0) := by ring
    _ = _ := by rw [hm, sub_self, add_zero]

/-- The filter of truncation parameters. -/
abbrev TruncFilter : Filter (ℝ × ℝ) :=
  nhdsWithin ((0 : ℝ), (0 : ℝ)) {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < 1}

theorem trunc_fst_tendsto : Tendsto (fun q : ℝ × ℝ => q.1) TruncFilter (nhdsWithin 0 (Icc (0 : ℝ) 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ⟨hq.1.le, by linarith [hq.2.1, hq.2.2]⟩

theorem trunc_snd_tendsto : Tendsto (fun q : ℝ × ℝ => 1 - q.2) TruncFilter
    (nhdsWithin 1 (Icc (0 : ℝ) 1)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hsnd : Tendsto (fun q : ℝ × ℝ => q.2) TruncFilter (nhds (0 : ℝ)) :=
      continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_zero] using (tendsto_const_nhds.sub hsnd :
      Tendsto (fun q : ℝ × ℝ => (1 : ℝ) - q.2) TruncFilter (nhds (1 - 0)))
  · filter_upwards [self_mem_nhdsWithin] with q hq
    constructor <;> linarith [hq.1, hq.2.1, hq.2.2]

/-- Off-diagonal limit: any improper chain integral equals the sheet value times the coefficient at the end. -/
theorem offdiag_limit (n m : ℤ) (F : (k : ℤ) → PotPair → P2Space38 k) (φ : GKPotential38)
    (R : ℂ → ℂ) (hR : AnalyticOnNhd ℂ R (ball (discC φ.1 m) (discR φ.1 m)))
    (hODE : ∀ z ∈ GKOriginalSlit38 φ m,
      perChar φ.1 z * deriv R z + (deriv (perChar φ.1) z / 2) * R z =
        p6PsiNumerator38 n (F n) φ.1 z)
    (f : GKRootedC1Arc38 φ m) (mids : List (GKRootedC1Arc38 φ m)) (l : GKRootedC1Arc38 φ m)
    (hchain : GKRootedArcChain38 φ m (f :: (mids ++ [l])))
    (hint : ChainInt n m F φ f mids l) (β : ℂ)
    (hlim : Tendsto (ChainTrunc n m F φ f mids l) TruncFilter (nhds β))
    (hstart : GKArcSheet38 f 0 = 0) :
    β = GKArcSheet38 l 1 * R (GKArcCurve38 l 1) := by
  letI : NeBot TruncFilter := triangleFilter_neBot
  have hgf := (arcPrim_continuousOn φ m R hR f 0 ⟨le_rfl, zero_le_one⟩).tendsto.comp trunc_fst_tendsto
  have hgl := (arcPrim_continuousOn φ m R hR l 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp trunc_snd_tendsto
  have hlim' := hgl.sub hgf
  have h0 : arcPrim φ m R f 0 = 0 := by simp only [arcPrim, hstart, zero_mul]
  rw [h0, sub_zero] at hlim'
  have hu : Tendsto (ChainTrunc n m F φ f mids l) TruncFilter
      (nhds (arcPrim φ m R l 1)) := by
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact (trunc_prim n m F φ R hR hODE f mids l hchain hint q hq).symm
  exact tendsto_nhds_unique hlim hu


theorem start_sheet_zero (φ : GKPotential38) (m : ℤ) (f : GKRootedC1Arc38 φ m) (c : ℂ)
    (hc : perChar φ.1 c = 0) (hstart : GKArcCurve38 f 0 = c) : GKArcSheet38 f 0 = 0 := by
  have hsq : GKArcSheet38 f 0 ^ 2 = perChar φ.1 (GKArcCurve38 f 0) :=
    f.2.2.2.2.1 0 ⟨le_rfl, zero_le_one⟩
  apply sq_eq_zero_iff.mp
  rw [hsq, hstart, hc]

theorem end_sheet_eq (φ : GKPotential38) (m : ℤ) (l : GKRootedC1Arc38 φ m)
    (hend : GKArcCurve38 l 1 = muSeq φ.1 m)
    (hterm : muSeq φ.1 m ≠ lamMinus φ.1 m → muSeq φ.1 m ≠ lamPlus φ.1 m →
      GKArcSheet38 l 1 = antiDiscrim φ.1 (muSeq φ.1 m)) :
    GKArcSheet38 l 1 = antiDiscrim φ.1 (muSeq φ.1 m) := by
  by_cases ht : muSeq φ.1 m = lamMinus φ.1 m ∨ muSeq φ.1 m = lamPlus φ.1 m
  · have hball : muSeq φ.1 m ∈ ball (discC φ.1 m) (discR φ.1 m) := by
      rw [← hend]
      exact l.2.2.2.2.2.1 1 ⟨zero_le_one, le_rfl⟩
    have hPzero := (rawBetaPerCharZeroInDiscIff38 φ m (muSeq φ.1 m) hball).mpr ht
    have hs0 : GKArcSheet38 l 1 = 0 := by
      apply sq_eq_zero_iff.mp
      have hsq : GKArcSheet38 l 1 ^ 2 = perChar φ.1 (GKArcCurve38 l 1) :=
        l.2.2.2.2.1 1 ⟨zero_le_one, le_rfl⟩
      rw [hsq, hend, hPzero]
    have hδ0 : antiDiscrim φ.1 (muSeq φ.1 m) = 0 :=
      sq_eq_zero_iff.mp ((rawBetaDirichletTerminalSquare38 φ m).trans hPzero)
    rw [hs0, hδ0]
  · exact hterm (fun h => ht (Or.inl h)) (fun h => ht (Or.inr h))

end C6

theorem beta_eq (n m : ℤ) (hmn : m ≠ n) (φ : PotPair) (hφ : φ ∈ sourceW) :
    ∃ S : ℂ → ℂ, AnalyticOnNhd ℂ S (ball (discC φ m) (discR φ m)) ∧
      (∀ z ∈ ball (discC φ m) (discR φ m),
        perChar φ z * deriv S z + (deriv (perChar φ) z / 2) * S z = psi n φ z) ∧
      offDiagonalBeta n m φ = antiDiscrim φ (muSeq φ m) * S (muSeq φ m) := by
  have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
  have hper : abelianPeriod38 m φ (p6PsiNumerator38 n (sourceF n) φ) = 0 := by
    have h := sourceFamily.F_period n φ hφ m
    rw [if_neg hmn] at h
    exact h
  obtain ⟨S, hS, hSode⟩ := rawBetaPsiCoefficientOfZeroPeriod38 n m (sourceF n) φ hgk hper
  refine ⟨S, hS, hSode, ?_⟩
  obtain ⟨p⟩ := rawBetaRootedPiecewisePathExists38 (sourceGK ⟨φ, hφ⟩) m
  have hp := offDiagonalBeta_pathValue n m hmn ⟨φ, hφ⟩ p
  have hlim := C6.offdiag_limit n m sourceF (sourceGK ⟨φ, hφ⟩) S hS
    (fun z hz => hSode z hz.1) p.1.1 p.1.2.1 p.1.2.2 p.2.2.1 hp.1
    (offDiagonalBeta n m φ) hp.2
    (C6.start_sheet_zero (sourceGK ⟨φ, hφ⟩) m p.1.1 (lamMinus φ m)
      (rawBetaPerCharLowerTipZero38 (sourceGK ⟨φ, hφ⟩) m) p.2.2.2.1)
  rw [hlim, C6.end_sheet_eq (sourceGK ⟨φ, hφ⟩) m p.1.2.2 p.2.2.2.2.1 p.2.2.2.2.2,
    p.2.2.2.2.1]
  rfl

end G3017Aux

theorem G3_017 (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair)
    (hφ0 : φ0 ∈ collapsedSet m \ endpointSet m) :
  canonRoot38 φ0 (muSeq φ0 m) ≠ 0 ∧
  (antiDiscrim φ0 (muSeq φ0 m)/canonRoot38 φ0 (muSeq φ0 m))^2 = 1 ∧
  IntervalIntegrable (fun t : ℝ =>
    betaZeta n m φ0 (tauN φ0 m+(t : ℂ)*(muSeq φ0 m-tauN φ0 m)) *
      (muSeq φ0 m-tauN φ0 m)) volume 0 1 ∧
  offDiagonalBeta n m φ0 =
    (antiDiscrim φ0 (muSeq φ0 m)/canonRoot38 φ0 (muSeq φ0 m)) *
      collapsedBetaFinalSegment n m φ0 0 ∧
  ∃ V : Set PotPair, IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW \ endpointSet m ∧
    ∀ φ ∈ V ∩ collapsedSet m,
      canonRoot38 φ (muSeq φ m) ≠ 0 ∧
      antiDiscrim φ (muSeq φ m)/canonRoot38 φ (muSeq φ m) =
        antiDiscrim φ0 (muSeq φ0 m)/canonRoot38 φ0 (muSeq φ0 m) := by
  obtain ⟨hgk, hP, hneT, hav, hroot, hcne⟩ := G3017Aux.mu_facts m φ0 hφ0
  obtain ⟨hPM, hτL⟩ := G3017Aux.tau_eq_lamMinus m φ0 hgk hφ0.1.2
  obtain ⟨-, -, -, -, hAn, hG⟩ := G3_002 n m hmn φ0 hφ0.1.1 hφ0.1.2
  obtain ⟨S, hS, hode, hbeta⟩ := G3017Aux.beta_eq n m hmn φ0 hφ0.1.1
  obtain ⟨_c, _N, _hg, hspec⟩ := isolating_family38 φ0 hgk
  have hτB : tauN φ0 m ∈ ball (discC φ0 m) (discR φ0 m) := by
    refine (hspec.1 m).1 ?_
    rw [hτL]
    exact left_mem_segment ℝ _ _
  have hμB : muSeq φ0 m ∈ ball (discC φ0 m) (discR φ0 m) := (hspec.1 m).2.1
  have hseg : segment ℝ (lamMinus φ0 m) (lamPlus φ0 m) = {tauN φ0 m} := by
    rw [hPM, hτL, segment_same]
  have hR : ∀ w ∈ ball (discC φ0 m) (discR φ0 m), w ≠ tauN φ0 m →
      (φ0, w) ∈ rootDomain38 := by
    intro w hw hne
    refine ⟨hgk, fun hzg => ?_⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hzg
    by_cases hkm : k = m
    · rw [hkm, hseg] at hk
      exact hne (Set.mem_singleton_iff.1 hk)
    · exact closedBall_avoids_other_gaps φ0 hgk m k hkm w
        (Metric.ball_subset_closedBall hw) hk
  have hτ0 : perChar φ0 (tauN φ0 m) = 0 := by
    rw [hτL]
    exact rawBetaPerCharLowerTipZero38 ⟨φ0, hgk⟩ m
  obtain ⟨hint, hI⟩ := G3017Aux.segment_integral_generic φ0 hgk
    (ball (discC φ0 m) (discR φ0 m)) (convex_ball _ _) (tauN φ0 m) (muSeq φ0 m)
    hτB hμB hneT hR hτ0 S (betaZeta n m φ0) (psi n φ0) hS hAn hode hG
  have hsq := G3017Aux.ratio_sq m φ0 hgk hav
  refine ⟨hcne, hsq, hint, ?_, ?_⟩
  · have hI' : collapsedBetaFinalSegment n m φ0 0 =
        canonRoot38 φ0 (muSeq φ0 m) * S (muSeq φ0 m) := hI
    rw [hbeta, hI']
    field_simp
  · obtain ⟨V, hVo, hφV, hVW, hV⟩ := G3017Aux.local_ratio m φ0 hφ0.1.1 hroot
    refine ⟨V, hVo, hφV, fun ψ hψ => ⟨hVW hψ, ?_⟩, fun ψ hψ => ?_⟩
    · intro hend
      exact (hV ψ hψ).2.2.1 hend.2
    · exact ⟨(hV ψ hψ.1).2.1, (hV ψ hψ.1).2.2.2⟩

end
end NlsGge.GKDefinitionDesign
