import Mathlib
import NlsGge.Atomic.G4.G4019
import NlsGge.Atomic.G4.G4020
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G2.G2047
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
import NlsGge.ThirdConsultation.G2.G2073Support1
import NlsGge.GK38.AbelianRatio
import NlsGge.GK38.AbelianSpace
import NlsGge.GK38.IsolatingDefs
import NlsGge.GK38.IsolatingTopology
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.GK38.StdRootBranchesDefs
import NlsGge.GK38.TauGamma
import NlsGge.GK38.TauGammaCircleMoments
import NlsGge.GK38.XiSqOmittedRoot

                                                                              
                                                                                               
                                                                                                             
                                 
                                                                                                                 
                                                                                                          
                                                                                                  
                                                                                                  
                                                                                                              
                                                                                     
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Two points of a real segment are at distance at most the length of the segment. -/
theorem g4021_segment_sub_norm_le (a b z w : ℂ) (hz : z ∈ segment ℝ a b) (hw : w ∈ segment ℝ a b) :
    ‖z - w‖ ≤ ‖b - a‖ := by
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hz
  obtain ⟨p', q', hp', hq', hpq', rfl⟩ := hw
  have h1 : p = 1 - q := by linarith
  have h2 : p' = 1 - q' := by linarith
  have e : p • a + q • b - (p' • a + q' • b) = (q - q') • (b - a) := by
    rw [h1, h2]
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [e, norm_smul, Real.norm_eq_abs]
  have hq1 : |q - q'| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  exact mul_le_of_le_one_left (norm_nonneg _) hq1

/-- The normalized zeta function is analytic on the closed isolating disc of a gap. -/
theorem g4021_closed_analytic (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) :
    AnalyticOnNhd ℂ (normalizedZeta n φ) (Metric.closedBall (discC φ n) (discR φ n)) := by
  intro lam hlam
  have hdom : (φ, lam) ∈ a5OmittedRootDomain38 n := by
    show φ ∈ gkW ∧ ∀ m : ℤ, m ≠ n → lam ∉ segment ℝ (lamMinus φ m) (lamPlus φ m)
    exact ⟨hgk, fun m hm => closedBall_avoids_other_gaps φ hgk n m hm lam hlam⟩
  have hjoint : AnalyticAt ℂ (p2OmittedRatio38 n) ((φ, p2Extend38 n (sourceF n φ)), lam) :=
    p2OmittedRatio_analytic38 n ((φ, p2Extend38 n (sourceF n φ)), lam) hdom
  have hpair : AnalyticAt ℂ (fun w : ℂ => ((φ, p2Extend38 n (sourceF n φ)), w)) lam :=
    AnalyticAt.prod analyticAt_const analyticAt_id
  exact hjoint.comp hpair

/-- The standard root of the gap is the normalized root `stdRoot38` at the gap centre and square length. -/
theorem g4021_localRoot_eq (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) (z : ℂ) :
    localRoot n φ z = stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2)
      ((lamPlus φ n - lamMinus φ n) ^ 2) z := by
  have ht : tauN φ n = (lamMinus φ n + lamPlus φ n) / 2 := by
    rw [tauN_value38 φ hgk n]
    ring
  have hg : gamma2 φ n = (lamPlus φ n - lamMinus φ n) ^ 2 := gamma2_value38 φ hgk n
  show standardRoot φ n z = _
  unfold standardRoot
  rw [ht, hg]

/-- Arcsine bound on one gap contour: the normalized contour mean of `K - c` is at most `B`
whenever `‖K - c‖ ≤ B` on the gap segment. -/
theorem g4021_gapMean_bound (φ : PotPair) (hgk : φ ∈ gkW) (n : ℤ) (c : ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z ∈ gapSegment φ n, ‖normalizedZeta n φ z - c‖ ≤ B) :
    ‖gapContourMean n φ (fun z => normalizedZeta n φ z - c)‖ ≤ B := by
  have hfam := isolating_family38 φ hgk
  have hR : 0 < discR φ n := isolating_radius_pos38 hfam n
  have hcut : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ Metric.ball (discC φ n) (discR φ n) := by
    obtain ⟨-, -, -, hs⟩ := hfam
    exact (hs.1 n).1
  have hf : AnalyticOnNhd ℂ (fun z => normalizedZeta n φ z - c)
      (Metric.closedBall (discC φ n) (discR φ n)) :=
    fun z hz => (g4021_closed_analytic φ hgk n z hz).sub analyticAt_const
  obtain ⟨-, hbd, -⟩ := G2_047 (lamMinus φ n) (lamPlus φ n) (discC φ n) (discR φ n) hR hcut
    (fun z => normalizedZeta n φ z - c) hf
  have hbd' := hbd B hB (fun z hz => hb z hz)
  have hn : ‖(-2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
    first
    | simp [abs_of_nonneg Real.pi_pos.le]
    | rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
  have hcongr : (fun lam : ℂ => (normalizedZeta n φ lam - c) / localRoot n φ lam) =
      (fun z : ℂ => (normalizedZeta n φ z - c) /
        stdRoot38 ((lamMinus φ n + lamPlus φ n) / 2) ((lamPlus φ n - lamMinus φ n) ^ 2) z) := by
    funext z
    rw [g4021_localRoot_eq φ hgk n z]
  show ‖(-2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun lam : ℂ => (normalizedZeta n φ lam - c) / localRoot n φ lam)
      (discC φ n) (discR φ n)‖ ≤ B
  rw [hcongr, norm_mul, norm_inv, hn]
  have hpos : 0 < 2 * Real.pi := by positivity
  refine (mul_le_mul_of_nonneg_left hbd' (inv_nonneg.mpr hpos.le)).trans (le_of_eq ?_)
  exact inv_mul_cancel_left₀ hpos.ne' B

/-- Subtracting a constant from the normalized zeta lowers its normalized contour mean by that constant. -/
theorem g4021_gapContour_const_sub (φ : PotPair) (hφ : φ ∈ sourceBetaW) (n : ℤ) (c : ℂ) :
    gapContourMean n φ (fun z => normalizedZeta n φ z - c) = 1 - c := by
  obtain ⟨hI0, hI1, hm0, hm1⟩ := G4020 n φ hφ
  have hint : CircleIntegrable (fun lam : ℂ => c * ((1:ℂ) / localRoot n φ lam))
      (discC φ n) (discR φ n) := by
    simpa only [Pi.smul_def, smul_eq_mul] using hI1.const_smul (a := c)
  have hsplit : (fun lam : ℂ => (normalizedZeta n φ lam - c) / localRoot n φ lam) =
      fun lam : ℂ => normalizedZeta n φ lam / localRoot n φ lam - c * ((1:ℂ) / localRoot n φ lam) := by
    funext lam
    ring
  have hcalc : circleIntegral (fun lam : ℂ => (normalizedZeta n φ lam - c) / localRoot n φ lam)
      (discC φ n) (discR φ n) =
      circleIntegral (fun lam : ℂ => normalizedZeta n φ lam / localRoot n φ lam) (discC φ n) (discR φ n) -
        c * circleIntegral (fun lam : ℂ => (1:ℂ) / localRoot n φ lam) (discC φ n) (discR φ n) := by
    rw [hsplit, circleIntegral.integral_sub hI0 hint, circleIntegral.integral_const_mul]
  have h1 : (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun lam : ℂ => normalizedZeta n φ lam / localRoot n φ lam) (discC φ n) (discR φ n) = 1 :=
    hm0
  have h2 : (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral (fun lam : ℂ => (1:ℂ) / localRoot n φ lam) (discC φ n) (discR φ n) = 1 :=
    hm1
  show (-2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
    circleIntegral (fun lam : ℂ => (normalizedZeta n φ lam - c) / localRoot n φ lam)
      (discC φ n) (discR φ n) = 1 - c
  rw [hcalc]
  linear_combination h1 - c * h2

theorem G4021 (φ₀ : PotPair) (hφ₀ : φ₀ ∈ sourceBetaW) :
  ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ sourceBetaW ∧
  ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ V, ∀ n : ℤ,
    (∀ lam ∈ gapSegment φ n,
      ‖normalizedZeta n φ lam - 1‖ ≤ C * ‖lamPlus φ n - lamMinus φ n‖) ∧
    (gamma2 φ n = 0 → normalizedZeta n φ (tauN φ n) = 1)
:= by
  obtain ⟨V, hVn, -, hVB, Cc, R0, r0, ε0, M, -, hM, -, -, hseg, hdiff⟩ := G4019 φ₀ hφ₀
  refine ⟨V, hVn, hVB, M + 1, by linarith, fun φ hφ n => ?_⟩
  have hφS : φ ∈ sourceBetaW := hVB hφ
  have hgk : φ ∈ gkW := sourceFamily.W_gk (sourceFamily.V_W hφS)
  have hmean : ∀ lam ∈ gapSegment φ n, ∀ z ∈ gapSegment φ n,
      ‖normalizedZeta n φ z - normalizedZeta n φ lam‖ ≤ M * ‖lamPlus φ n - lamMinus φ n‖ := by
    intro lam hlam z hz
    have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := normalizedZeta n φ)
      (fun x hx => (hdiff φ hφ n x hx).1) (fun x hx => (hdiff φ hφ n x hx).2)
      (convex_ball (Cc n) (r0 n)) ((hseg φ hφ n).1 hlam) ((hseg φ hφ n).1 hz)
    exact hmv.trans (mul_le_mul_of_nonneg_left
      (g4021_segment_sub_norm_le (lamMinus φ n) (lamPlus φ n) z lam hz hlam) hM.le)
  have hkey : ∀ lam ∈ gapSegment φ n,
      ‖normalizedZeta n φ lam - 1‖ ≤ M * ‖lamPlus φ n - lamMinus φ n‖ := by
    intro lam hlam
    have hb := g4021_gapMean_bound φ hgk n (normalizedZeta n φ lam)
      (M * ‖lamPlus φ n - lamMinus φ n‖) (mul_nonneg hM.le (norm_nonneg _))
      (fun z hz => hmean lam hlam z hz)
    rw [g4021_gapContour_const_sub φ hφS n (normalizedZeta n φ lam)] at hb
    rw [norm_sub_rev]
    exact hb
  refine ⟨fun lam hlam => ?_, fun hg => ?_⟩
  · exact (hkey lam hlam).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · have hgap : lamPlus φ n - lamMinus φ n = 0 := by
      rw [gamma2_value38 φ hgk n] at hg
      exact (pow_eq_zero_iff two_ne_zero).mp hg
    have hτ : tauN φ n = lamMinus φ n := by
      have hpl : lamPlus φ n = lamMinus φ n := sub_eq_zero.mp hgap
      rw [tauN_value38 φ hgk n, hpl]
      ring
    have hmem : tauN φ n ∈ gapSegment φ n := by
      rw [hτ]
      exact left_mem_segment ℝ (lamMinus φ n) (lamPlus φ n)
    have h0 := hkey (tauN φ n) hmem
    rw [hgap, norm_zero, mul_zero] at h0
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

end
end NlsGge.GKDefinitionDesign
