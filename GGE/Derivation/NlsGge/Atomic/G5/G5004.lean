import Mathlib
import NlsGge.Atomic.G4.G4001
import NlsGge.Atomic.G5.G5001
import NlsGge.Atomic.G5.G5004Host
import NlsGge.Atomic.G5.G5004Support1
import NlsGge.Atomic.G5.G5004Support2
import NlsGge.Atomic.G5.G5004Support3
import NlsGge.Atomic.G5.G5004Support4
import NlsGge.ThirdConsultation.KO.Basic

/- G5-004 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5004.lean.
   Head byte-identical to Pro round 10 (PRO_DEFINITION_RESPONSE_FP80_10.md section 7, commit 178f84d6) block
   `theorem G5004`; `finiteGap` is NlsGge.ThirdConsultation.finiteGap (opened by name, the head text is unchanged).
   Route (Pro round 10): radiusQuotient = -(1/2)/a_n with a_n = radiusOmittedNormalized, on the nonvanishing locus of
   psi (G5001); local l2 norm continuity (Support4) gives |a_n| >= d0/2 uniformly on a ball; Cauchy estimate G4001
   and the real-slice differentiation (Support1).  LOCAL TACTIC VARIATION recorded: the quotient is identified with
   -(1/2)/a_n only on the (n-dependent) G5001 neighbourhood of realSlice u, which suffices for the derivative at
   realSlice u (EventuallyEq.fderiv_eq); the uniform psi nonvanishing on the whole ball is not needed. -/
set_option autoImplicit false

open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation (finiteGap)

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5004 (u : PhysicalL2) (hu : finiteGap u) :
  Memℓp (fun n : ℤ =>
    radiusQuotient n (realSlice u) - radiusQuotientLeading n) 2 ∧
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ,
    ‖fderiv ℝ
      (fun v : PhysicalL2 => radiusQuotient n (realSlice v)) u‖ ≤ C := by
  have _hu := hu
  have hφ₀ : realSlice u ∈ sourceBetaW := sourceFamily.V_real (Set.mem_range_self u)
  obtain ⟨d₀, r, hd₀, hr, hrW, hlow0, hlow⟩ := g5004_uniform_lower (realSlice u) hφ₀
  have hq : ∀ (n : ℤ) (φ : PotPair), φ ∈ sourceBetaW → psiAt n (muSeq φ n) φ ≠ 0 →
      radiusQuotient n φ = -(1 / 2 : ℂ) / radiusOmittedNormalized n φ := by
    intro n φ hφ hpsi
    have hA : a5OmittedRootProduct38 n (φ, muSeq φ n) ≠ 0 :=
      a5OmittedRoot_ne_zero38 n (φ, muSeq φ n) (g5001_dom φ hφ n)
    have hpi : (Lib.piN n : ℂ) ≠ 0 := by exact_mod_cast Lib.piN_ne_zero n
    rw [radiusQuotient_cancel n φ hφ hpsi]
    unfold radiusOmittedNormalized
    field_simp
  have hnorm : ∀ n : ℤ,
      ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ≤
        (1 / d₀) * ‖radiusOmittedNormalized n (realSlice u) - (-1 : ℂ) ^ n‖ := by
    intro n
    have ha := g5004_a_ne_zero n (realSlice u) hφ₀
    have hrq := hq n (realSlice u) hφ₀ (g5001_psi_ne_zero_real n u)
    have hp2 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
      rw [← mul_zpow]; norm_num
    have key : (-1 : ℂ) ^ n * (radiusOmittedNormalized n (realSlice u) - (-1 : ℂ) ^ n) =
        (-1 : ℂ) ^ n * radiusOmittedNormalized n (realSlice u) - 1 := by
      linear_combination (-1 : ℂ) * hp2
    have e : radiusQuotient n (realSlice u) - radiusQuotientLeading n =
        (-1 : ℂ) ^ n * (radiusOmittedNormalized n (realSlice u) - (-1 : ℂ) ^ n) /
          (2 * radiusOmittedNormalized n (realSlice u)) := by
      rw [hrq, key]
      unfold radiusQuotientLeading
      field_simp
      try ring
    have hp1 : ‖(-1 : ℂ) ^ n‖ = 1 := by simp
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have hy := hlow0 n
    have hpos : 0 < ‖(2 : ℂ)‖ * ‖radiusOmittedNormalized n (realSlice u)‖ := by
      rw [h2]; have := lt_of_lt_of_le hd₀ hy; positivity
    have hk : 1 ≤ 1 / d₀ * (2 * ‖radiusOmittedNormalized n (realSlice u)‖) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hd₀]
      linarith
    have hx := norm_nonneg (radiusOmittedNormalized n (realSlice u) - (-1 : ℂ) ^ n)
    rw [e, norm_div, norm_mul, hp1, one_mul, norm_mul, div_le_iff₀ hpos, h2]
    nlinarith [mul_le_mul_of_nonneg_left hk hx]
  refine ⟨?_, (1 / d₀) / r + 1, by positivity, fun n => ?_⟩
  · obtain ⟨U, -, hφU, -, B, -, hB⟩ := radiusOmittedNormalized_local_l2 (realSlice u) hφ₀
    have hs := (hB _ hφU).1
    have hs2 : Summable (fun n : ℤ =>
        ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2) := by
      refine (hs.mul_left ((1 / d₀) ^ 2)).of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      calc ‖radiusQuotient n (realSlice u) - radiusQuotientLeading n‖ ^ 2
          ≤ ((1 / d₀) * ‖radiusOmittedNormalized n (realSlice u) - (-1 : ℂ) ^ n‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
        _ = (1 / d₀) ^ 2 * ‖radiusOmittedNormalized n (realSlice u) - (-1 : ℂ) ^ n‖ ^ 2 :=
            mul_pow _ _ _
    exact (memℓp_gen_iff (by simp)).mpr (by simpa using hs2)
  · obtain ⟨V, hVn, -, hVW, -, hVpsi, -⟩ := G5001 n u
    have hEq : radiusQuotient n =ᶠ[𝓝 (realSlice u)]
        fun φ => -(1 / 2 : ℂ) / radiusOmittedNormalized n φ := by
      filter_upwards [hVn] with φ hφ
      exact hq n φ (hVW hφ) (hVpsi φ hφ)
    have hfa : AnalyticOnNhd ℂ
        (fun φ : PotPair => -(1 / 2 : ℂ) / radiusOmittedNormalized n φ)
        (Metric.ball (realSlice u) r) := by
      intro φ hφ
      have hne : radiusOmittedNormalized n φ ≠ 0 := by
        have h1 := hlow φ hφ n
        intro h0
        rw [h0, norm_zero] at h1
        linarith
      exact analyticAt_const.div (radiusOmittedNormalized_analytic n φ (hrW hφ)) hne
    have hbd : ∀ φ ∈ Metric.ball (realSlice u) r,
        ‖-(1 / 2 : ℂ) / radiusOmittedNormalized n φ‖ ≤ 1 / d₀ := by
      intro φ hφ
      have h1 := hlow φ hφ n
      have hpos : 0 < ‖radiusOmittedNormalized n φ‖ := lt_of_lt_of_le (by positivity) h1
      have h3 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [norm_div, norm_neg, h3, div_le_div_iff₀ hpos hd₀]
      linarith
    have hC := NlsGge.Atomic.G4.norm_fderiv_le_of_ball_bound hr hfa hbd
    have hdiff : DifferentiableAt ℂ (radiusQuotient n) (realSlice u) :=
      (hfa (realSlice u) (Metric.mem_ball_self hr)).differentiableAt.congr_of_eventuallyEq hEq
    have hfd : fderiv ℂ (radiusQuotient n) (realSlice u) =
        fderiv ℂ (fun φ : PotPair => -(1 / 2 : ℂ) / radiusOmittedNormalized n φ) (realSlice u) :=
      hEq.fderiv_eq
    have hR := norm_fderiv_realSlice_le (radiusQuotient n) u hdiff
    rw [hfd] at hR
    linarith

end
end NlsGge.GKDefinitionDesign
