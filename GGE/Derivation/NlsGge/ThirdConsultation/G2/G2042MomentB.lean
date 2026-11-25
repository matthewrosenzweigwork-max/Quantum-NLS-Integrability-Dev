import Mathlib
import NlsGge.ThirdConsultation.G2.G2042MomentA
import NlsGge.ThirdConsultation.G2.G2042Support2
import NlsGge.Atomic.G2.G2026

/- G2-042 MOMENT-B (proof development, AUTHOR; proof development repair PRODUCTION02: the collapsed-gap branch rewrites
   `norm_zero` once, since the first rewrite already removes every `‖0‖`; statement unchanged; not self-reviewed; no packet acceptance claimed).
   Target NlsGge/ThirdConsultation/G2/G2042MomentB.lean. Pro §26 `criticalMoment_uniform_bound`, verbatim
   statement (1 ≤ k). Inputs: M1 criticalMoment_rescaled and circle_moment_collapsed (G2042MomentA),
   MS-D a5Chi_rescaled_bound (G2042Support2), G2-026 (ℓ² bound on the critical coefficients), and the common
   isolating family (local_isolatingFamily_common38). Gap bound from the common radii; no new hypothesis. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G2042MomentB
noncomputable section
open NlsGge.GKDefinitionDesign.G2042MomentA

/-- Uniform gap bound on a common isolating neighbourhood: `‖λ+ - λ-‖ ≤ G` for all `n`. -/
theorem gap_bound_local (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ V : Set PotPair, V ∈ 𝓝 φ₀ ∧ V ⊆ gkW ∧
      ∃ G : ℝ, 0 ≤ G ∧ ∀ φ ∈ V, ∀ n : ℤ, ‖gap φ n‖ ≤ G := by
  obtain ⟨V, hV, hVW, -, -, C, R, c, Ng, hgeom, hspec⟩ := local_isolatingFamily_common38 φ₀ hφ₀
  have hsum0 : 0 ≤ ∑ m ∈ Finset.Icc (-(Ng : ℤ)) (Ng : ℤ), |R m| :=
    Finset.sum_nonneg (fun m _ => abs_nonneg _)
  refine ⟨V, hV, hVW, Real.pi / 2 + 2 * ∑ m ∈ Finset.Icc (-(Ng : ℤ)) (Ng : ℤ), |R m|, ?_, ?_⟩
  · have := Real.pi_pos
    linarith
  intro φ hφ n
  have hseg : segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) (R n) := by
    have h := hspec φ hφ
    unfold IsolatingSpectral38 at h
    exact (h.1 n).1
  have hL : lamPlus φ n ∈ ball (C n) (R n) := hseg (right_mem_segment ℝ _ _)
  have hM : lamMinus φ n ∈ ball (C n) (R n) := hseg (left_mem_segment ℝ _ _)
  have hdist : ‖gap φ n‖ = dist (lamPlus φ n) (lamMinus φ n) := by
    rw [dist_eq_norm]
    rfl
  rw [hdist]
  have hpi := Real.pi_pos
  by_cases hn : (Ng : ℤ) < |n|
  · have hball : ball (C n) (R n) = ball (countingCenter38 n) (Real.pi / 4) :=
      (hgeom.2.2.2.2 n hn).2.2
    rw [hball, mem_ball] at hL hM
    have htri := dist_triangle_right (lamPlus φ n) (lamMinus φ n) (countingCenter38 n)
    linarith
  · have hle : |n| ≤ (Ng : ℤ) := not_lt.mp hn
    have hnS : n ∈ Finset.Icc (-(Ng : ℤ)) (Ng : ℤ) := by
      rw [Finset.mem_Icc]
      exact abs_le.mp hle
    rw [mem_ball] at hL hM
    have htri := dist_triangle_right (lamPlus φ n) (lamMinus φ n) (C n)
    have hR1 : |R n| ≤ ∑ m ∈ Finset.Icc (-(Ng : ℤ)) (Ng : ℤ), |R m| :=
      Finset.single_le_sum (f := fun m => |R m|) (fun m _ => abs_nonneg _) hnS
    have hRn : R n ≤ |R n| := le_abs_self _
    linarith

/-- Pointwise bound of the rescaled integrand, with the arcsine weight. -/
theorem uniform_bound_pointwise (j : ℕ) (φ : PotPair) (n : ℤ) (t : ℝ)
    (ht : t ∈ Ioc (-1:ℝ) 1) (G A Xp P : ℝ) (hG0 : 0 ≤ G) (hA0 : 0 ≤ A) (hXp0 : 0 ≤ Xp)
    (hP : P = 1 + G + G * A) (hγ : ‖gap φ n‖ ≤ G)
    (ha : ‖a5CriticalA38 n φ‖ ≤ A) (hχ : ‖a5Chi38 n (φ, tauN φ n + (t:ℂ) * gap φ n / 2)‖ ≤ Xp) :
    ‖criticalMomentIntegrand j φ n t‖ ≤
      Xp * P ^ (j+1) * ‖(1:ℂ) / ((Real.sqrt (1 - t^2) : ℝ) : ℂ)‖ := by
  have hs : ‖((Real.sqrt (1 - t^2) : ℝ) : ℂ)‖ = Real.sqrt (1 - t^2) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hsnn : 0 ≤ Real.sqrt (1 - t^2) := Real.sqrt_nonneg _
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hbt : ‖(t:ℂ) / 2‖ ≤ 1 := by
    have h2 : ‖(2:ℂ)‖ = 2 := by simp
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, h2]
    linarith
  have hA1 : ‖(t:ℂ) / 2 - gap φ n * a5CriticalA38 n φ‖ ≤ P := by
    have h1 := norm_sub_le ((t:ℂ) / 2) (gap φ n * a5CriticalA38 n φ)
    have h2 : ‖gap φ n * a5CriticalA38 n φ‖ ≤ G * A := by
      rw [norm_mul]
      exact mul_le_mul hγ ha (norm_nonneg _) hG0
    have h3 : 0 ≤ G * A := mul_nonneg hG0 hA0
    rw [hP]
    linarith
  have hA2 : ‖((t:ℂ) / 2 - gap φ n * a5CriticalA38 n φ) ^ (j+1)‖ ≤ P ^ (j+1) := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hA1 _
  have hP0 : 0 ≤ P := by rw [hP]; have := mul_nonneg hG0 hA0; linarith
  unfold criticalMomentIntegrand
  rw [norm_div, norm_div, norm_one, hs, norm_mul]
  have hnum : ‖((t:ℂ) / 2 - gap φ n * a5CriticalA38 n φ) ^ (j+1)‖ *
      ‖a5Chi38 n (φ, tauN φ n + (t:ℂ) * gap φ n / 2)‖ ≤ P ^ (j+1) * Xp :=
    mul_le_mul hA2 hχ (norm_nonneg _) (pow_nonneg hP0 _)
  have hspos : 0 ≤ Real.sqrt (1 - t^2) := hsnn
  calc ‖((t:ℂ) / 2 - gap φ n * a5CriticalA38 n φ) ^ (j+1)‖ *
        ‖a5Chi38 n (φ, tauN φ n + (t:ℂ) * gap φ n / 2)‖ / Real.sqrt (1 - t^2)
      ≤ P ^ (j+1) * Xp / Real.sqrt (1 - t^2) := by
        exact div_le_div_of_nonneg_right hnum hspos
    _ = Xp * P ^ (j+1) * (1 / Real.sqrt (1 - t^2)) := by ring

/-- Uniform moment estimate on a neighbourhood (Pro §26, verbatim statement). -/
theorem criticalMoment_uniform_bound
    (k : ℕ) (hk : 1 ≤ k)
    (φ₀ : PotPair) (hφ₀ : φ₀ ∈ gkW) :
    ∃ U : Set PotPair,
      IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ φ ∈ U, ∀ n : ℤ, ∀ j : ℕ,
          1 ≤ j → j ≤ k →
          ‖criticalMoment j φ n‖ ≤ C * ‖gamma2 φ n‖ := by
  obtain ⟨V, hV, hVW, G, hG0, hGb⟩ := gap_bound_local φ₀ hφ₀
  obtain ⟨V1, hV1, hV1W, X, hX⟩ := G2042S2.a5Chi_rescaled_bound φ₀ hφ₀
  obtain ⟨U2, hU2o, hφU2, hU2W, C2, hC2, hU2⟩ := G2_026 φ₀ hφ₀
  have hWn : V ∩ V1 ∩ U2 ∈ 𝓝 φ₀ := inter_mem (inter_mem hV hV1) (hU2o.mem_nhds hφU2)
  refine ⟨interior (V ∩ V1 ∩ U2), isOpen_interior, mem_interior_iff_mem_nhds.mpr hWn,
    fun φ hφ => hVW (interior_subset hφ).1.1, ?_⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + C2 := ⟨_, rfl⟩
  obtain ⟨Xp, hXpdef⟩ : ∃ Xp : ℝ, Xp = max X 0 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = 1 + G + G * A := ⟨_, rfl⟩
  obtain ⟨KK, hKKdef⟩ : ∃ K : ℝ, K = ∫ t in (-1:ℝ)..1,
      ‖(1:ℂ) / ((Real.sqrt (1 - t^2) : ℝ) : ℂ)‖ := ⟨_, rfl⟩
  obtain ⟨c0, hc0def⟩ : ∃ c : ℝ, c = ‖(2 / (Real.pi : ℂ))‖ := ⟨_, rfl⟩
  obtain ⟨C0, hC0def⟩ : ∃ c : ℝ, c = c0 * Xp * KK * P ^ (2 * k + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; linarith
  have hXp0 : 0 ≤ Xp := by rw [hXpdef]; exact le_max_right _ _
  have hG0' : 0 ≤ G := hG0
  have hP1 : 1 ≤ P := by
    rw [hPdef]
    have := mul_nonneg hG0 hA0
    linarith
  have hP0 : 0 ≤ P := by linarith
  have hKK0 : 0 ≤ KK := by
    rw [hKKdef]
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)
  have hc0nn : 0 ≤ c0 := by rw [hc0def]; exact norm_nonneg _
  have hC0nn : 0 ≤ C0 := by
    rw [hC0def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hc0nn hXp0) hKK0) (pow_nonneg hP0 _)
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro φ hφ n j hj1 hjk
  have hφW : φ ∈ V ∩ V1 ∩ U2 := interior_subset hφ
  have hφV : φ ∈ V := hφW.1.1
  have hφV1 : φ ∈ V1 := hφW.1.2
  have hφU2' : φ ∈ U2 := hφW.2
  have hφ' : φ ∈ gkW := hVW hφV
  -- ℓ² bound on the critical coefficients
  obtain ⟨-, hs2, hle2⟩ := hU2 φ hφU2'
  have ha : ∀ m : ℤ, ‖a5CriticalA38 m φ‖ ≤ A := by
    intro m
    have h1 : ‖a5CriticalA38 m φ‖ ^ 2 ≤ ∑' m' : ℤ, ‖a5CriticalA38 m' φ‖ ^ 2 := by
      simpa only [Finset.sum_singleton] using
        hs2.sum_le_tsum ({m} : Finset ℤ) (fun _ _ => sq_nonneg _)
    rw [hAdef]
    nlinarith [norm_nonneg (a5CriticalA38 m φ)]
  have hγb : ∀ m : ℤ, ‖gap φ m‖ ≤ G := fun m => hGb φ hφV m
  have hχb : ∀ m : ℤ, ∀ t : ℝ, t ∈ Icc (-1:ℝ) 1 →
      ‖a5Chi38 m (φ, tauN φ m + (t:ℂ) * gap φ m / 2)‖ ≤ Xp := by
    intro m t ht
    rw [hXpdef]
    exact (hX φ hφV1 m t ht).trans (le_max_left _ _)
  -- the moment estimate
  have hg2n : ‖gamma2 φ n‖ = ‖gap φ n‖ ^ 2 := by
    rw [gamma2_value38 φ hφ' n, norm_pow]
    rfl
  have key : ‖criticalMoment j φ n‖ ≤ C0 * ‖gamma2 φ n‖ := by
    by_cases hγ : lamPlus φ n - lamMinus φ n = 0
    · have h0 : criticalMoment j φ n = 0 := by
        unfold criticalMoment
        rw [circle_moment_collapsed j φ hφ' n hγ, mul_zero]
      have hgz : gap φ n = 0 := hγ
      rw [h0, hg2n, hgz, norm_zero]
      simp
    · obtain ⟨-, hid⟩ := criticalMoment_rescaled j hj1 φ hφ' n
      rw [hid]
      -- integral bound
      have hint : ‖∫ t in (-1:ℝ)..1, criticalMomentIntegrand j φ n t‖ ≤ Xp * P ^ (j+1) * KK := by
        have hgi : IntervalIntegrable
            (fun t : ℝ => Xp * P ^ (j+1) * ‖(1:ℂ) / ((Real.sqrt (1 - t^2) : ℝ) : ℂ)‖)
            volume (-1) 1 := by
          have hc : ContinuousOn (fun _ : ℝ => (1:ℂ)) (Icc (-1) 1) := continuousOn_const
          exact ((G2032Arcsine.arcsine_intervalIntegrable (fun _ : ℝ => (1:ℂ)) hc).norm).const_mul _
        have hb := intervalIntegral.norm_integral_le_of_norm_le (f := criticalMomentIntegrand j φ n)
          (g := fun t : ℝ => Xp * P ^ (j+1) * ‖(1:ℂ) / ((Real.sqrt (1 - t^2) : ℝ) : ℂ)‖)
          (by norm_num)
          (ae_of_all _ (fun t ht => uniform_bound_pointwise j φ n t ht G A Xp P hG0 hA0 hXp0 hPdef
            (hγb n) (ha n) (hχb n t (Ioc_subset_Icc_self ht))))
          hgi
        rw [intervalIntegral.integral_const_mul, ← hKKdef] at hb
        exact hb
      have hPj : P ^ (j+1) ≤ P ^ (k+1) := pow_le_pow_right₀ hP1 (by omega)
      have hint' : ‖∫ t in (-1:ℝ)..1, criticalMomentIntegrand j φ n t‖ ≤ Xp * P ^ (k+1) * KK := by
        refine hint.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPj hXp0) hKK0
      -- the power of the gap
      have hγP : ‖gap φ n‖ ≤ P := by
        have := hγb n
        rw [hPdef]
        have := mul_nonneg hG0 hA0
        linarith
      have hpow : ‖gap φ n‖ ^ (j+1) ≤ ‖gap φ n‖ ^ 2 * P ^ k := by
        have hsplit : ‖gap φ n‖ ^ (j+1) = ‖gap φ n‖ ^ 2 * ‖gap φ n‖ ^ (j-1) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hsplit]
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (pow_le_pow_left₀ (norm_nonneg _) hγP _).trans (pow_le_pow_right₀ hP1 (by omega))
      have hnorm : ‖(2 / (Real.pi : ℂ)) * gap φ n ^ (j+1) *
          ∫ t in (-1:ℝ)..1, criticalMomentIntegrand j φ n t‖ =
          c0 * ‖gap φ n‖ ^ (j+1) * ‖∫ t in (-1:ℝ)..1, criticalMomentIntegrand j φ n t‖ := by
        rw [norm_mul, norm_mul, norm_pow, hc0def]
      rw [hnorm, hg2n]
      have hfin : c0 * ‖gap φ n‖ ^ (j+1) * ‖∫ t in (-1:ℝ)..1, criticalMomentIntegrand j φ n t‖ ≤
          c0 * (‖gap φ n‖ ^ 2 * P ^ k) * (Xp * P ^ (k+1) * KK) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow hc0nn) hint' (norm_nonneg _)
          (mul_nonneg hc0nn (mul_nonneg (sq_nonneg _) (pow_nonneg hP0 _)))
      refine hfin.trans (le_of_eq ?_)
      rw [hC0def]
      ring
  have hfinal : ‖criticalMoment j φ n‖ ≤ (C0 + 1) * ‖gamma2 φ n‖ := by
    nlinarith [key, norm_nonneg (gamma2 φ n)]
  exact hfinal

end
end G2042MomentB
end NlsGge.GKDefinitionDesign
