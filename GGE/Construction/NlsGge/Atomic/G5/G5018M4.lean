import Mathlib
import NlsGge.Atomic.G3.G3015
import NlsGge.ThirdConsultation.G3.G3015Support
import NlsGge.ThirdConsultation.G3.G3005C6Core
import NlsGge.Atomic.G2.G2021
import NlsGge.Atomic.G2.G2075
import NlsGge.Atomic.G5.G5001Host
import NlsGge.Atomic.G5.G5018Asm
import NlsGge.Atomic.G5.G5018M3b
import NlsGge.Atomic.G5.G5018M4Root
import NlsGge.Atomic.G5.G5018M4Lab
import NlsGge.Atomic.G5.G5018M4Line
import NlsGge.Atomic.G5.G5018M4Calc
import NlsGge.Atomic.G5.G5018M4Ftc
import NlsGge.GK38.RealTypeSpectrum
import NlsGge.GK38.DirichletRealBridge

                                                                                                          
                                                                                                                            
                                                                                                                                 
                                                                                                                                  
                                                                                                                      
                                                                                   
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
namespace G5018M4Aux
noncomputable section

theorem sqrt_deriv {f g : ℂ → ℂ} {f' g' : ℂ} (hf : HasDerivAt f f' 0) (hf0 : f 0 ≠ 0)
    (hsq : (fun w => f w ^ 2) =ᶠ[𝓝 0] g) (hg : HasDerivAt g g' 0) : f' = g' / (2 * f 0) := by
  have h1 : HasDerivAt (fun w => f w ^ 2) (2 * f 0 * f') 0 := by
    have e : (fun w => f w ^ 2) = fun w => f w * f w := by funext w; ring
    rw [e]
    exact (hf.mul hf).congr_deriv (by ring)
  have h2 := (hsq.hasDerivAt_iff).mp h1
  have h3 := h2.unique hg
  rw [← h3]
  field_simp

theorem line_hasDerivAt {F : PotPair → ℂ} {φ0 v : PotPair} (hF : DifferentiableAt ℂ F φ0) :
    HasDerivAt (fun w : ℂ => F (φ0 + w • v)) (fderiv ℂ F φ0 v) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => φ0 + w • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add φ0
  have hF' : HasFDerivAt F (fderiv ℂ F φ0) ((fun w : ℂ => φ0 + w • v) 0) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℂ) h1

/-- The M4 integrand derivative, in the form integrated by `g5018m4_ftc1d`. -/
def Dint (Q : ℂ → ℂ) (a0 μ0 ω0 dμ : ℂ) (r : ℝ → ℂ) (t : ℝ) : ℂ :=
  dμ * (ω0 * (t : ℂ) * deriv Q (a0 + (t : ℂ) * (μ0 - a0)) / r t
    + Q (a0 + (t : ℂ) * (μ0 - a0)) / (2 * ω0 * r t)
    - Q (a0 + (t : ℂ) * (μ0 - a0)) * ω0 * (t : ℂ) / (2 * r t ^ 3)) / (Real.sqrt t : ℂ)

theorem entry (u : PhysicalL2) (m : ℤ) (hm : InteriorRealDirichletGap m u) :
    realSlice u ∈ sourceW \ (collapsedSet m ∪ endpointSet m) ∧ gamma2 (realSlice u) m ≠ 0 := by
  have hW0 : realSlice u ∈ sourceW := sourceFamily.W_real (Set.mem_range_self u)
  have hgk : realSlice u ∈ gkW := realSlice_mem_gkW u
  have hγ : gamma2 (realSlice u) m ≠ 0 := by
    rw [gamma2_value38 _ hgk m]
    obtain ⟨hP, hM⟩ := lamPlus_real u m
    rw [hP, hM, ← Complex.ofReal_sub]
    have hlo := hm.1
    have hhi := hm.2
    have : (actualGapUpperAllE02_38 u m - actualGapLowerAllE02_38 u m) ≠ 0 := by
      have := lt_trans hlo hhi
      exact ne_of_gt (sub_pos.mpr this)
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr this)
  have hδ := g5018_antiDiscrim_ne_zero u m hm
  have hper : perChar (realSlice u) (muSeq (realSlice u) m) ≠ 0 := by
    have h := dirichlet_perChar_eq_anti_sq38 (realSlice u) (muSeq (realSlice u) m)
      (by rw [muSeq_eq_gkMu38]; exact gkMu_root38 u m)
    rw [h]
    exact pow_ne_zero 2 hδ
  refine ⟨⟨hW0, ?_⟩, hγ⟩
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · exact hγ h
  · exact hper h

theorem pointwise (n m : ℤ) (hmn : m ≠ n) (φ0 v : PotPair) (lam : ℂ)
    (V : Set PotPair) (a b rω : PotPair → ℂ) (rseg : PotPair → ℝ → ℂ)
    (hφV : φ0 ∈ V) (hsep : LocalEndpointSegmentSeparation m V a b)
    (hroots : AnalyticSegmentRoots m V a b rω rseg)
    (hk : gamma2 φ0 m ≠ 0) (hv : v = PoissonSpectral38.spectralDiscrimHamField38 φ0 lam)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun w : ℂ => G3015Aux.Hfun n m a rω rseg (φ0 + w • v) t / (Real.sqrt t : ℂ))
      (Dint (fun z => psi n φ0 z / (2 * Complex.I * rootProduct m (φ0, z)))
        (a φ0) (muSeq φ0 m) (rω φ0) (fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v)
        (rseg φ0) t) 0 := by
  obtain ⟨hVo, hVsub, haA, hbA, hVp⟩ := hsep
  obtain ⟨hrωA, hrsegA, hrsegC, hall⟩ := hroots
  have hW0 : φ0 ∈ sourceW := (hVsub hφV).1
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hW0
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
  have hΔ : ∀ w : ℂ, fderiv ℂ (fun ψ : PotPair => discrim ψ w) φ0 v = 0 := fun w => by
    rw [hv]; exact PoissonSpectral38.actual_fderiv_discrim_hamField_eq_zero φ0 w lam
  have hline : Continuous (fun w : ℂ => φ0 + w • v) := by fun_prop
  have hevV : ∀ᶠ w in 𝓝 (0 : ℂ), φ0 + w • v ∈ V :=
    hline.continuousAt.eventually_mem (hVo.mem_nhds (by simpa using hφV))
  have hgapne : ∀ φ ∈ V, lamPlus φ m - lamMinus φ m ≠ 0 := fun φ hφ =>
    G3015Aux.gap_ne_of_mem m φ (hVsub hφ)
  have hlab := g5018m4_labels_fderiv_zero m φ0 lam a b hgk0 hk
    (haA φ0 hφV).differentiableAt (hbA φ0 hφV).differentiableAt
    (by filter_upwards [hVo.mem_nhds hφV] with ψ hψ; exact (hVp ψ hψ).1)
    (by filter_upwards [hVo.mem_nhds hφV] with ψ hψ; exact hgapne ψ hψ)
  rw [← hv] at hlab
  have hAw : HasDerivAt (fun w : ℂ => a (φ0 + w • v)) 0 0 := by
    have := line_hasDerivAt (v := v) (haA φ0 hφV).differentiableAt
    rwa [hlab.1] at this
  have hBw : HasDerivAt (fun w : ℂ => b (φ0 + w • v)) 0 0 := by
    have := line_hasDerivAt (v := v) (hbA φ0 hφV).differentiableAt
    rwa [hlab.2] at this
  have hμd : DifferentiableAt ℂ (fun ψ : PotPair => muSeq ψ m) φ0 :=
    (analyticOnNhd_muSeq_complex38 m φ0 hgk0).differentiableAt
  have hMw := line_hasDerivAt (v := v) hμd
  obtain ⟨hω0, hωsq0, hrs0, hsign0⟩ := hall φ0 hφV
  obtain ⟨hr0, hrsq0⟩ := hrs0 t htI
  have h00 : φ0 + (0 : ℂ) • v = φ0 := by simp
  -- derivative of rω
  have hRWd := line_hasDerivAt (v := v) (hrωA φ0 hφV).differentiableAt
  have hsqRW : (fun w : ℂ => rω (φ0 + w • v) ^ 2) =ᶠ[𝓝 0]
      fun w => muSeq (φ0 + w • v) m - a (φ0 + w • v) := by
    filter_upwards [hevV] with w hw
    exact (hall _ hw).2.1
  have hRW' := sqrt_deriv hRWd (by simpa [h00] using hω0) hsqRW (hMw.sub hAw)
  simp only [h00, zero_smul, add_zero, sub_zero] at hRW'
  have hRW : HasDerivAt (fun w : ℂ => rω (φ0 + w • v))
      (fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v / (2 * rω φ0)) 0 := by
    rw [← hRW']; exact hRWd
  -- derivative of rseg
  have hRSd := line_hasDerivAt (v := v) (hrsegA t htI φ0 hφV).differentiableAt
  have hsqRS : (fun w : ℂ => rseg (φ0 + w • v) t ^ 2) =ᶠ[𝓝 0]
      fun w => a (φ0 + w • v) + (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v)) -
        b (φ0 + w • v) := by
    filter_upwards [hevV] with w hw
    exact ((hall _ hw).2.2.1 t htI).2
  have hZw : HasDerivAt (fun w : ℂ => a (φ0 + w • v) +
      (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v)))
      (0 + (t : ℂ) * (fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v - 0)) 0 :=
    hAw.add ((hMw.sub hAw).const_mul (t : ℂ))
  have hRS' := sqrt_deriv hRSd (by simpa [h00] using hr0) hsqRS (hZw.sub hBw)
  simp only [h00, zero_smul, add_zero, sub_zero, zero_add] at hRS'
  have hRS : HasDerivAt (fun w : ℂ => rseg (φ0 + w • v) t)
      ((t : ℂ) * fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v / (2 * rseg φ0 t)) 0 := by
    rw [← hRS']; exact hRSd
  -- the moving point
  have hZ' : HasDerivAt (fun w : ℂ => a (φ0 + w • v) +
      (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v)))
      ((t : ℂ) * fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v) 0 := by
    simpa using hZw
  have hZ0 : a (φ0 + (0 : ℂ) • v) + (t : ℂ) * (muSeq (φ0 + (0 : ℂ) • v) m - a (φ0 + (0 : ℂ) • v)) =
      a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) := by rw [h00]
  -- domain facts at the point z0
  have hzb : a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) ∈ ball (discC φ0 m) (discR φ0 m) :=
    G3015Aux.seg_mem_ball m φ0 hgk0 (a φ0) (b φ0) (hVp φ0 hφV).1 t htI
  have hdom : (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) ∈ a5OmittedRootDomain38 m :=
    ⟨hgk0, fun k hk' => closedBall_avoids_other_gaps φ0 hgk0 m k hk' _ (ball_subset_closedBall hzb)⟩
  have hq0 : rootProduct m (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) ≠ 0 :=
    (G2_021 m).2.2 _ hdom
  have hQne : (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - lamMinus φ0 m) *
      (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - lamPlus φ0 m) ≠ 0 := by
    have hpair : (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - lamMinus φ0 m) *
        (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - lamPlus φ0 m) =
        (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - a φ0) *
        (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - b φ0) := by
      rcases Set.pair_eq_pair_iff.1 (hVp φ0 hφV).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [← h1, ← h2]
      · rw [← h1, ← h2]; ring
    rw [hpair]
    have e1 : a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - a φ0 = (t : ℂ) * rω φ0 ^ 2 := by
      rw [hωsq0]; ring
    have e2 : a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0) - b φ0 = rseg φ0 t ^ 2 := hrsq0.symm
    rw [e1, e2]
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.1.ne') (pow_ne_zero 2 hω0))
      (pow_ne_zero 2 hr0)
  -- joint derivatives
  have hpsiJ : DifferentiableAt ℂ (fun p : PotPair × ℂ => psi n p.1 p.2)
      (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) :=
    ((G2_075.2.2.2.1 n) _ ⟨hW0, mem_univ _⟩).differentiableAt
  have hpsiL := g5018m4_joint_line_hasDerivAt (F := fun p : PotPair × ℂ => psi n p.1 p.2)
    (φ0 := φ0) (v := v) (z0 := a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0))
    (Z := fun w : ℂ => a (φ0 + w • v) + (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v)))
    hpsiJ hZ' hZ0 (g5018_psiAt_fderiv_eq_zero n _ φ0 v hW0 hΔ)
  have hrPJ : DifferentiableAt ℂ (fun p : PotPair × ℂ => rootProduct m p)
      (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) :=
    ((G2_021 m).2.1 _ hdom).differentiableAt
  have hrPL := g5018m4_joint_line_hasDerivAt (F := fun p : PotPair × ℂ => rootProduct m p)
    (φ0 := φ0) (v := v) (z0 := a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0))
    (Z := fun w : ℂ => a (φ0 + w • v) + (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v)))
    hrPJ hZ' hZ0 (by
      rw [hv]
      exact g5018m4_rootProduct_fderiv_zero m φ0 lam _ hgk0 hk hdom hQne)
  -- the quotient Q in z
  have hψz : DifferentiableAt ℂ (fun z : ℂ => psi n φ0 z) (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) :=
    (((G2_075.2.2.2.2.1 n φ0 hW0).1) _ (mem_univ _)).differentiableAt
  have hqz : DifferentiableAt ℂ (fun z : ℂ => rootProduct m (φ0, z))
      (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) :=
    ((G2_021 m).2.1 _ hdom).differentiableAt.comp _
      ((differentiableAt_const φ0).prodMk differentiableAt_id)
  have hEne : 2 * Complex.I * rootProduct m (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) hq0
  have hQd : HasDerivAt (fun z : ℂ => psi n φ0 z / (2 * Complex.I * rootProduct m (φ0, z)))
      ((deriv (fun z : ℂ => psi n φ0 z) (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) *
          (2 * Complex.I * rootProduct m (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0))) -
        psi n φ0 (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) *
          (2 * Complex.I * deriv (fun z : ℂ => rootProduct m (φ0, z))
            (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)))) /
        (2 * Complex.I * rootProduct m (φ0, a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0))) ^ 2)
      (a φ0 + (t : ℂ) * (muSeq φ0 m - a φ0)) :=
    hψz.hasDerivAt.div ((hqz.hasDerivAt).const_mul (2 * Complex.I)) hEne
  -- the G-form of the integrand
  have hGeq : ∀ φ ∈ V, G3015Aux.Hfun n m a rω rseg φ t =
      psi n φ (a φ + (t : ℂ) * (muSeq φ m - a φ)) * rω φ /
        (2 * Complex.I * rootProduct m (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) * rseg φ t) := by
    intro φ hφ
    have hφsW := (hVsub hφ).1
    have hgkφ := sourceFamily.W_gk hφsW
    have hzbφ := G3015Aux.seg_mem_ball m φ hgkφ (a φ) (b φ) (hVp φ hφ).1 t htI
    have hdomφ : (φ, a φ + (t : ℂ) * (muSeq φ m - a φ)) ∈ a5OmittedRootDomain38 m :=
      ⟨hgkφ, fun k hk' => closedBall_avoids_other_gaps φ hgkφ m k hk' _
        (ball_subset_closedBall hzbφ)⟩
    have hf := G3015Aux.factor n m hmn φ hφsW (hgapne φ hφ) _ hzbφ
    have hr := (G2_021 m).2.2 _ hdomφ
    have hρ := (((hall φ hφ).2.2.1 t htI)).1
    simp only [G3015Aux.Hfun]
    rw [hf]
    field_simp
  have hG : HasDerivAt (fun w : ℂ =>
      psi n (φ0 + w • v) (a (φ0 + w • v) + (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v))) *
        rω (φ0 + w • v) /
      (2 * Complex.I * rootProduct m (φ0 + w • v, a (φ0 + w • v) +
        (t : ℂ) * (muSeq (φ0 + w • v) m - a (φ0 + w • v))) * rseg (φ0 + w • v) t) /
      (Real.sqrt t : ℂ)) _ 0 :=
    ((hpsiL.mul hRW).div (((hrPL.const_mul (2 * Complex.I))).mul hRS)
      (show (2 * Complex.I * rootProduct m (φ0 + (0 : ℂ) • v, a (φ0 + (0 : ℂ) • v) +
          (t : ℂ) * (muSeq (φ0 + (0 : ℂ) • v) m - a (φ0 + (0 : ℂ) • v))) *
          rseg (φ0 + (0 : ℂ) • v) t) ≠ 0 by
        rw [hZ0, h00]; exact mul_ne_zero hEne hr0)).div_const _
  have hG' : HasDerivAt (fun w : ℂ => G3015Aux.Hfun n m a rω rseg (φ0 + w • v) t /
      (Real.sqrt t : ℂ)) _ 0 := hG.congr_of_eventuallyEq (by
    filter_upwards [hevV] with w hw
    rw [hGeq _ hw])
  refine hG'.congr_deriv ?_
  have hsne : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne'
  have hs2 : (Real.sqrt t : ℂ) ^ 2 = (t : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.1.le]
  unfold Dint
  rw [hQd.deriv]
  beta_reduce
  simp only [Pi.mul_apply, h00, zero_smul, add_zero, sub_zero]
  generalize (Real.sqrt t : ℂ) = s at hsne hs2 ⊢
  rw [← hs2]
  have hq0' := hq0
  have hI : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  field_simp
  ring


theorem core (n m : ℤ) (hmn : m ≠ n) (φ0 : PotPair) (lam : ℂ) (v : PotPair)
    (hv : v = PoissonSpectral38.spectralDiscrimHamField38 φ0 lam)
    (hφ0 : φ0 ∈ sourceW \ (collapsedSet m ∪ endpointSet m)) (hk : gamma2 φ0 m ≠ 0) :
    fderiv ℂ (offDiagonalBeta n m) φ0 v =
      (psi n φ0 (muSeq φ0 m) / antiDiscrim φ0 (muSeq φ0 m)) *
        fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v := by
  obtain ⟨V, a, b, rω, rseg, C, hφV, hsep, hroots, hC, hH⟩ := G3015Aux.local_data n m hmn φ0 hφ0
  obtain ⟨hHan, hHφ⟩ := hH
  have hVo : IsOpen V := hsep.1
  have hHan' : ∀ t ∈ Ioo (0 : ℝ) 1,
      AnalyticOnNhd ℂ (fun φ => G3015Aux.Hfun n m a rω rseg φ t) V := hHan
  have hHφ' : ∀ φ ∈ V, ContinuousOn (G3015Aux.Hfun n m a rω rseg φ) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ‖G3015Aux.Hfun n m a rω rseg φ t‖ ≤ C) ∧
      IntervalIntegrable (fun t => G3015Aux.Hfun n m a rω rseg φ t / (Real.sqrt t : ℂ)) volume 0 1 ∧
      offDiagonalBeta n m φ = ∫ t in (0 : ℝ)..1,
        G3015Aux.Hfun n m a rω rseg φ t / (Real.sqrt t : ℂ) := hHφ
  have hW0 : φ0 ∈ sourceW := hφ0.1
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hW0
  -- derivative under the integral
  have hpow : Integrable (fun t : ℝ => Real.rpow t (-1 / 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    change IntegrableOn (fun t : ℝ => t ^ (-1 / 2 : ℝ)) (Ioo (0 : ℝ) 1) volume
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 / 2 : ℝ)) (t := 1) (by norm_num)]
    norm_num
  have hg : Integrable (fun t : ℝ => C * Real.rpow t (-1 / 2))
      (volume.restrict (Ioo (0 : ℝ) 1)) := hpow.const_mul C
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hVo φ0 hφV
  have hS1 := g5018m4_scalar_integral_line_hasDerivAt (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (U := V) (a := fun (t : ℝ) (φ : PotPair) =>
      G3015Aux.Hfun n m a rω rseg φ t / (Real.sqrt t : ℂ)) (u := φ0) (h := v)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht φ hφ =>
      (hHan' t ht φ hφ).div analyticAt_const
        (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')))
    (fun φ hφ => by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
      refine ((hHφ' φ hφ).1.mono Ioo_subset_Icc_self).div
        (Complex.continuous_ofReal.comp_continuousOn Real.continuous_sqrt.continuousOn) ?_
      intro t ht
      exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 ht.1).ne')
    hφV hr hball hg
    (fun w hw => by
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => ?_)
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
      have hb := (hHφ' w (hball hw)).2.1 t ⟨ht.1.le, ht.2.le⟩
      have hr' : Real.rpow t (-1 / 2) = (Real.sqrt t)⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num]
        exact g3005_rpow_neg_half_eq ht.1
      show ‖G3015Aux.Hfun n m a rω rseg w t / (Real.sqrt t : ℂ)‖ ≤ C * Real.rpow t (-1 / 2)
      rw [hr', norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hb hs.le)
    (ContinuousLinearMap.id ℂ ℂ)
  obtain ⟨δ, -, hD1⟩ := hS1
  have hline : Continuous (fun w : ℂ => φ0 + w • v) := by fun_prop
  have hevV : ∀ᶠ w in 𝓝 (0 : ℂ), φ0 + w • v ∈ V :=
    hline.continuousAt.eventually_mem (hVo.mem_nhds (by simpa using hφV))
  have hβd := line_hasDerivAt (v := v)
    (G3015Aux.analytic_of_local n m hmn φ0 hφ0).differentiableAt
  have hβeq : (fun w : ℂ => offDiagonalBeta n m (φ0 + w • v)) =ᶠ[𝓝 0]
      fun w : ℂ => (ContinuousLinearMap.id ℂ ℂ) (∫ t, G3015Aux.Hfun n m a rω rseg (φ0 + w • v) t /
        (Real.sqrt t : ℂ) ∂(volume.restrict (Ioo (0 : ℝ) 1))) := by
    filter_upwards [hevV] with w hw
    rw [(hHφ' _ hw).2.2.2, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    rfl
  have key := hβd.unique (hD1.congr_of_eventuallyEq hβeq)
  -- pointwise integrand
  obtain ⟨hVo', hVsub, haA, hbA, hVp⟩ := id hsep
  obtain ⟨hrωA, hrsegA, hrsegC, hall⟩ := id hroots
  obtain ⟨hω0, hωsq0, hrs0, hsign0⟩ := hall φ0 hφV
  have hint_eq : (∫ t, deriv (fun w : ℂ => (ContinuousLinearMap.id ℂ ℂ)
        (G3015Aux.Hfun n m a rω rseg (φ0 + w • v) t / (Real.sqrt t : ℂ))) 0
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ t in Ioo (0 : ℝ) 1, Dint (fun z => psi n φ0 z / (2 * Complex.I * rootProduct m (φ0, z)))
        (a φ0) (muSeq φ0 m) (rω φ0) (fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v) (rseg φ0) t := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    exact (pointwise n m hmn φ0 v lam V a b rω rseg hφV hsep hroots hk hv t ht).deriv
  have hdomz : ∀ z ∈ ball (discC φ0 m) (discR φ0 m), (φ0, z) ∈ a5OmittedRootDomain38 m :=
    fun z hz => ⟨hgk0, fun k hk' => closedBall_avoids_other_gaps φ0 hgk0 m k hk' z
      (ball_subset_closedBall hz)⟩
  have hQan : AnalyticOnNhd ℂ
      (fun z => psi n φ0 z / (2 * Complex.I * rootProduct m (φ0, z)))
      (ball (discC φ0 m) (discR φ0 m)) := by
    intro z hz
    have hψ : AnalyticAt ℂ (psi n φ0) z := ((G2_075.2.2.2.2.1 n φ0 hW0).1) z (mem_univ _)
    have hrP : AnalyticAt ℂ (fun w : ℂ => rootProduct m (φ0, w)) z :=
      AnalyticAt.comp (g := rootProduct m) (f := fun w : ℂ => (φ0, w))
        ((G2_021 m).2.1 (φ0, z) (hdomz z hz)) (analyticAt_const.prod analyticAt_id)
    exact hψ.div (analyticAt_const.mul hrP)
      (mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) ((G2_021 m).2.2 _ (hdomz z hz)))
  have hrc : ContinuousOn (rseg φ0) (Icc (0 : ℝ) 1) :=
    hrsegC.comp (by fun_prop : Continuous fun t : ℝ => (φ0, t)).continuousOn
      (fun t ht => ⟨hφV, ht⟩)
  have hF := g5018m4_ftc1d (fun z => psi n φ0 z / (2 * Complex.I * rootProduct m (φ0, z)))
    (discC φ0 m) (discR φ0 m) hQan (a φ0) (muSeq φ0 m) (b φ0) (rω φ0)
    (fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v) (rseg φ0)
    (fun t ht => G3015Aux.seg_mem_ball m φ0 hgk0 (a φ0) (b φ0) (hVp φ0 hφV).1 t ht)
    hω0 hωsq0 hrc (fun t ht => (hrs0 t ht).1) (fun t ht => (hrs0 t ht).2)
  have hF2 : (∫ t in Ioo (0 : ℝ) 1,
      Dint (fun z => psi n φ0 z / (2 * Complex.I * rootProduct m (φ0, z)))
        (a φ0) (muSeq φ0 m) (rω φ0) (fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v) (rseg φ0) t) =
      fderiv ℂ (fun ψ : PotPair => muSeq ψ m) φ0 v *
        (psi n φ0 (muSeq φ0 m) / (2 * Complex.I * rootProduct m (φ0, muSeq φ0 m))) /
        (rω φ0 * rseg φ0 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
    exact hF.2
  have hr1 := (hrs0 1 ⟨zero_le_one, le_rfl⟩).1
  have hq1 : rootProduct m (φ0, muSeq φ0 m) ≠ 0 := by
    have hz1 : muSeq φ0 m ∈ ball (discC φ0 m) (discR φ0 m) := by
      have := G3015Aux.seg_mem_ball m φ0 hgk0 (a φ0) (b φ0) (hVp φ0 hφV).1 1 ⟨zero_le_one, le_rfl⟩
      simpa using this
    exact (G2_021 m).2.2 _ (hdomz _ hz1)
  rw [key, hint_eq, hF2, ← hsign0]
  field_simp

end
end G5018M4Aux

noncomputable section

theorem g5018_offDiagonal_endpoint_fderiv
    (u : PhysicalL2) (m n : ℤ) (lam : ℂ)
    (hmn : m ≠ n) (hm : InteriorRealDirichletGap m u) :
    fderiv ℂ (offDiagonalBeta n m) (realSlice u)
      (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) =
    (psiAt n (muSeq (realSlice u) m) (realSlice u) /
      antiDiscrim (realSlice u) (muSeq (realSlice u) m)) *
    fderiv ℂ (fun ψ : PotPair => muSeq ψ m) (realSlice u)
      (PoissonSpectral38.spectralDiscrimHamField38 (realSlice u) lam) := by
  obtain ⟨hφ0, hk⟩ := G5018M4Aux.entry u m hm
  exact G5018M4Aux.core n m hmn (realSlice u) lam _ rfl hφ0 hk

end
end NlsGge.GKDefinitionDesign
