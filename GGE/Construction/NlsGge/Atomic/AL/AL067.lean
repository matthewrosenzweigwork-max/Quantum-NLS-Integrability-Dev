                                                                                                                                                                                                                                                                                                                             
import Mathlib
import NlsGge.Hierarchy.ALSampling38
import NlsGge.Hierarchy.ALPositiveDecompositions38

                                                                                          
                                                                                                                  
                                                                                                           
                                                                 
                                                                                                               
                                                                                                               
                                                                                    
                                                                                                              

set_option autoImplicit false
open Filter Topology NlsGge.Pilot NlsGge.Analysis NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core

namespace NlsGge.ThirdConsultation.AL

namespace al067Aux

noncomputable def Mb (u : SobolevHilbert 1) : ℝ := (‖u‖ + 1) * ‖reciprocalBracketL2‖

theorem Mb_nonneg (u : SobolevHilbert 1) : 0 ≤ Mb u := by
  unfold Mb; positivity

theorem alh38_tendsto : Tendsto (fun N : ℕ => alh38 N) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => (alh38_pos N).le) (fun N => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  unfold alh38
  exact one_div_le_one_div_of_le (by positivity)
    (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

theorem bound_of_norm (u y : SobolevHilbert 1) (N : ℕ) (j : ZMod (2 * N + 1))
    (hy : ‖y‖ ≤ ‖u‖ + 1) : ‖alSample38 N y j‖ ≤ Mb u := by
  have h := alCanon_norm_le38 y (alt38 N j)
  unfold alSample38
  unfold Mb
  calc ‖alCanon38 y (alt38 N j)‖ ≤ ‖y‖ * ‖reciprocalBracketL2‖ := h
    _ ≤ (‖u‖ + 1) * ‖reciprocalBracketL2‖ :=
        mul_le_mul_of_nonneg_right hy (norm_nonneg _)

theorem pow_sub_le (M : ℝ) (k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haM : a ≤ M) (hbM : b ≤ M) :
    |a ^ (k + 1) - b ^ (k + 1)| ≤ ((k : ℝ) + 1) * M ^ k * |a - b| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1 + 1) - b ^ (k + 1 + 1) =
        a * (a ^ (k + 1) - b ^ (k + 1)) + b ^ (k + 1) * (a - b) := by ring
    rw [e]
    have h1 : |a * (a ^ (k + 1) - b ^ (k + 1))| ≤ M * (((k : ℝ) + 1) * M ^ k * |a - b|) := by
      rw [abs_mul, abs_of_nonneg ha]
      exact mul_le_mul haM ih (abs_nonneg _) (le_trans ha haM)
    have h2 : |b ^ (k + 1) * (a - b)| ≤ M ^ (k + 1) * |a - b| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hb _)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hbM _) (abs_nonneg _)
    calc |a * (a ^ (k + 1) - b ^ (k + 1)) + b ^ (k + 1) * (a - b)|
        ≤ |a * (a ^ (k + 1) - b ^ (k + 1))| + |b ^ (k + 1) * (a - b)| := abs_add_le _ _
      _ ≤ M * (((k : ℝ) + 1) * M ^ k * |a - b|) + M ^ (k + 1) * |a - b| := add_le_add h1 h2
      _ = (((k + 1 : ℕ) : ℝ) + 1) * M ^ (k + 1) * |a - b| := by push_cast; ring

theorem sample_sub_le (y u : SobolevHilbert 1) (N : ℕ) (j : ZMod (2 * N + 1)) :
    ‖alSample38 N y j - alSample38 N u j‖ ≤
      ‖physicalH1CanonicalContinuousRepresentativeCLM (y - u)‖ := by
  unfold alSample38
  rw [← alCanon_sub38]
  unfold alCanon38
  exact ContinuousMap.norm_coe_le_norm _ _

/-- Conjunct 1 error: the expansion of the logarithmic sum, uniform in N, with M a common bound. -/
theorem expansion_err (β₁ : ℝ) (y : SobolevHilbert 1) (N : ℕ) (M : ℝ) (hM0 : 0 ≤ M)
    (hbound : ∀ j : ZMod (2 * N + 1), ‖alSample38 N y j‖ ≤ M) (hhM : alh38 N * M < 1 / 2) :
    |2 * β₁ / alh38 N ^ 3 * (∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2)) -
        β₁ * alh38 N * (∑ j, ‖alSample38 N y j‖ ^ 4)| ≤
      4 * |β₁| * M ^ 6 * alh38 N ^ 2 := by
  have hh := alh38_pos N
  -- per-term remainder bound
  have hrem : ∀ j : ZMod (2 * N + 1),
      |alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) - (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2|
        ≤ 2 * (alh38 N ^ 6 * M ^ 6) := by
    intro j
    have ha0 : 0 ≤ ‖alSample38 N y j‖ := norm_nonneg _
    have haM : ‖alSample38 N y j‖ ≤ M := hbound j
    have hr0 : 0 ≤ alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2 := by positivity
    have hra : alh38 N * ‖alSample38 N y j‖ ≤ alh38 N * M :=
      mul_le_mul_of_nonneg_left haM hh.le
    have hr_half : alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2 ≤ 1 / 2 := by
      have hp : 0 ≤ alh38 N * ‖alSample38 N y j‖ := mul_nonneg hh.le ha0
      nlinarith
    have hq := alEll_quad_38 hr0 hr_half
    have e3 : (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 3 =
        alh38 N ^ 6 * ‖alSample38 N y j‖ ^ 6 := by ring
    rw [e3] at hq
    have h6 : ‖alSample38 N y j‖ ^ 6 ≤ M ^ 6 := pow_le_pow_left₀ ha0 haM 6
    have hh6 : 0 ≤ alh38 N ^ 6 := by positivity
    have : alh38 N ^ 6 * ‖alSample38 N y j‖ ^ 6 ≤ alh38 N ^ 6 * M ^ 6 :=
      mul_le_mul_of_nonneg_left h6 hh6
    linarith
  -- the sum of the remainders
  have hsum_rem : |∑ j, (alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) -
      (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2)| ≤ (2 * N + 1 : ℝ) * (2 * (alh38 N ^ 6 * M ^ 6)) := by
    calc |∑ j, (alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) -
          (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2)|
        ≤ ∑ j, |alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) -
          (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ZMod (2 * N + 1), 2 * (alh38 N ^ 6 * M ^ 6) :=
          Finset.sum_le_sum (fun j _ => hrem j)
      _ = (2 * N + 1 : ℝ) * (2 * (alh38 N ^ 6 * M ^ 6)) := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          push_cast; ring
  -- algebraic split
  have hsq : ∑ j, (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2 =
      alh38 N ^ 4 / 2 * ∑ j, ‖alSample38 N y j‖ ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hdiff : ∑ j, (alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) -
      (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2) =
      (∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2)) - alh38 N ^ 4 / 2 * ∑ j, ‖alSample38 N y j‖ ^ 4 := by
    rw [Finset.sum_sub_distrib, hsq]
  have key : 2 * β₁ / alh38 N ^ 3 * (∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2)) -
      β₁ * alh38 N * (∑ j, ‖alSample38 N y j‖ ^ 4) =
      2 * β₁ / alh38 N ^ 3 * ∑ j, (alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) -
        (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2) := by
    rw [hdiff]
    field_simp
  rw [key, abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < alh38 N ^ 3)]
  have hfac : |2 * β₁| / alh38 N ^ 3 = 2 * |β₁| / alh38 N ^ 3 := by
    rw [abs_mul, abs_two]
  rw [hfac]
  have hA : (2 * |β₁| / alh38 N ^ 3) * |∑ j, (alEll (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) -
      (alh38 N ^ 2 * ‖alSample38 N y j‖ ^ 2) ^ 2 / 2)| ≤
      (2 * |β₁| / alh38 N ^ 3) * ((2 * N + 1 : ℝ) * (2 * (alh38 N ^ 6 * M ^ 6))) :=
    mul_le_mul_of_nonneg_left hsum_rem (by positivity)
  have hcomp : (2 * |β₁| / alh38 N ^ 3) * ((2 * N + 1 : ℝ) * (2 * (alh38 N ^ 6 * M ^ 6))) =
      4 * |β₁| * M ^ 6 * alh38 N ^ 2 := by
    have hN : (2 * (N : ℝ) + 1) * alh38 N = 1 := alh38_mul N
    have hN' : (2 * N + 1 : ℝ) = 1 / alh38 N := by
      field_simp; linarith
    rw [hN']
    field_simp
    ring
  linarith [hA, hcomp]


/-- Riemann limit of the real fourth-power sum of the actual canonical samples of u. -/
theorem riemann_norm4 (u : SobolevHilbert 1) :
    Tendsto (fun N : ℕ => alh38 N * ∑ j, ‖alSample38 N u j‖ ^ 4) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)) := by
  have hc : Continuous (fun t : ℝ => ((‖alCanon38 u t‖ ^ 4 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (((alCanon_cont38 u).norm).pow 4)
  have hp : Function.Periodic (fun t : ℝ => ((‖alCanon38 u t‖ ^ 4 : ℝ) : ℂ)) 1 :=
    fun t => by simp only [alCanon_periodic38 u t]
  have hR := riemann38 _ hc hp
  have hre := (Complex.continuous_re.tendsto _).comp hR
  simp only [Function.comp_def] at hre
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re] at hre
  convert hre using 1
  · funext N
    simp only [alSample38, Complex.re_ofReal_mul, Complex.re_sum, Complex.ofReal_re]

/-- Conjunct 2 core: the perturbed Riemann sum with the moving sample x N. -/
theorem riemann_perturb (u : SobolevHilbert 1) (x : ℕ → SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    Tendsto (fun N : ℕ => alh38 N * ∑ j, ‖alSample38 N (x N) j‖ ^ 4) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)) := by
  have hR := riemann_norm4 u
  -- the CLM distance tends to zero
  have hxn : Tendsto (fun N => x N - u) atTop (𝓝 0) := by
    have h := hx.sub_const u
    rwa [sub_self] at h
  have hδ : Tendsto (fun N => ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖) atTop (𝓝 0) := by
    have hc := ((physicalH1CanonicalContinuousRepresentativeCLM).continuous.tendsto
      (0 : SobolevHilbert 1)).comp hxn
    rw [map_zero] at hc
    have hn := hc.norm
    rw [norm_zero] at hn
    exact hn
  -- eventually x N stays in the ball of radius ‖u‖ + 1
  have hxN : ∀ᶠ N : ℕ in atTop, ‖x N‖ ≤ ‖u‖ + 1 :=
    (hx.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))).mono (fun N hN => hN.le)
  have hdiff : Tendsto (fun N : ℕ => alh38 N * ∑ j, ‖alSample38 N (x N) j‖ ^ 4 -
      alh38 N * ∑ j, ‖alSample38 N u j‖ ^ 4) atTop (𝓝 0) := by
    have hbd : Tendsto (fun N : ℕ =>
        4 * (Mb u) ^ 3 * ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖) atTop (𝓝 0) := by
      have := hδ.const_mul (4 * (Mb u) ^ 3)
      rwa [mul_zero] at this
    refine squeeze_zero_norm' ?_ hbd
    filter_upwards [hxN] with N hN
    have hh := alh38_pos N
    have hM0 := Mb_nonneg u
    have hterm : ∀ j : ZMod (2 * N + 1),
        |‖alSample38 N (x N) j‖ ^ 4 - ‖alSample38 N u j‖ ^ 4| ≤
          4 * (Mb u) ^ 3 * ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ := by
      intro j
      have ha : 0 ≤ ‖alSample38 N (x N) j‖ := norm_nonneg _
      have hb : 0 ≤ ‖alSample38 N u j‖ := norm_nonneg _
      have haM : ‖alSample38 N (x N) j‖ ≤ Mb u := bound_of_norm u (x N) N j hN
      have hbM : ‖alSample38 N u j‖ ≤ Mb u := bound_of_norm u u N j (by linarith)
      have hab : |‖alSample38 N (x N) j‖ - ‖alSample38 N u j‖| ≤
          ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ :=
        (abs_norm_sub_norm_le _ _).trans (sample_sub_le (x N) u N j)
      have hp := pow_sub_le (Mb u) 3 ha hb haM hbM
      norm_num at hp
      calc |‖alSample38 N (x N) j‖ ^ 4 - ‖alSample38 N u j‖ ^ 4|
          ≤ 4 * (Mb u) ^ 3 * |‖alSample38 N (x N) j‖ - ‖alSample38 N u j‖| := hp
        _ ≤ 4 * (Mb u) ^ 3 * ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ :=
            mul_le_mul_of_nonneg_left hab (by positivity)
    have hcount : ∑ _j : ZMod (2 * N + 1), (1 : ℝ) = 2 * (N : ℝ) + 1 := by
      simp [ZMod.card]
    rw [← mul_sub, ← Finset.sum_sub_distrib, Real.norm_eq_abs, abs_mul, abs_of_nonneg hh.le]
    calc alh38 N * |∑ j, (‖alSample38 N (x N) j‖ ^ 4 - ‖alSample38 N u j‖ ^ 4)|
        ≤ alh38 N * ∑ j, |‖alSample38 N (x N) j‖ ^ 4 - ‖alSample38 N u j‖ ^ 4| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hh.le
      _ ≤ alh38 N * ∑ _j : ZMod (2 * N + 1),
            4 * (Mb u) ^ 3 * ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hterm j)) hh.le
      _ = 4 * (Mb u) ^ 3 * ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖ := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
          have hN2 : alh38 N * (2 * (N : ℝ) + 1) = 1 := by
            have := alh38_mul N; linarith [mul_comm (alh38 N) (2 * (N : ℝ) + 1)]
          push_cast
          linear_combination (4 * (Mb u) ^ 3 * ‖physicalH1CanonicalContinuousRepresentativeCLM (x N - u)‖) * hN2
  have h3 := hR.add hdiff
  rw [add_zero] at h3
  exact h3.congr (fun N => by ring)

end al067Aux

open al067Aux in
theorem al067 (β₁ : ℝ) (x : ℕ → SobolevHilbert 1) (u : SobolevHilbert 1)
    (hx : Tendsto x atTop (𝓝 u)) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |(2 * β₁ / alh38 N ^ 3 *
        ∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)) -
        β₁ * alh38 N * (∑ j, ‖alSample38 N (x N) j‖ ^ 4)| ≤
        C * alh38 N ^ 2) ∧
    Tendsto (fun N => 2 * β₁ / alh38 N ^ 3 *
      ∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2))
      atTop (𝓝 (β₁ * ∫ t in (0 : ℝ)..1, ‖alCanon38 u t‖ ^ 4)) := by
  have hxN : ∀ᶠ N : ℕ in atTop, ‖x N‖ ≤ ‖u‖ + 1 :=
    (hx.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))).mono (fun N hN => hN.le)
  have hsmall : ∀ᶠ N : ℕ in atTop, alh38 N * Mb u < 1 / 2 := by
    have h := alh38_tendsto.mul_const (Mb u)
    rw [zero_mul] at h
    exact (tendsto_order.1 h).2 (1 / 2) (by norm_num)
  refine ⟨⟨4 * |β₁| * (Mb u) ^ 6, by positivity, ?_⟩, ?_⟩
  · filter_upwards [hxN, hsmall] with N hN hhM
    have hb : ∀ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ≤ Mb u :=
      fun j => bound_of_norm u (x N) N j hN
    exact expansion_err β₁ (x N) N (Mb u) (Mb_nonneg u) hb hhM
  · have hR := riemann_perturb u x hx
    have hbd2 : Tendsto (fun N : ℕ => 4 * |β₁| * (Mb u) ^ 6 * alh38 N ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun N : ℕ => alh38 N ^ 2) atTop (𝓝 0) := by
        simpa using alh38_tendsto.pow 2
      have := h2.const_mul (4 * |β₁| * (Mb u) ^ 6)
      rwa [mul_zero] at this
    have hE : Tendsto (fun N : ℕ =>
        2 * β₁ / alh38 N ^ 3 * (∑ j, alEll (alh38 N ^ 2 * ‖alSample38 N (x N) j‖ ^ 2)) -
        β₁ * alh38 N * (∑ j, ‖alSample38 N (x N) j‖ ^ 4)) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ hbd2
      filter_upwards [hxN, hsmall] with N hN hhM
      have hb : ∀ j : ZMod (2 * N + 1), ‖alSample38 N (x N) j‖ ≤ Mb u :=
        fun j => bound_of_norm u (x N) N j hN
      rw [Real.norm_eq_abs]
      exact expansion_err β₁ (x N) N (Mb u) (Mb_nonneg u) hb hhM
    have hsum := (hR.const_mul β₁).add hE
    rw [add_zero] at hsum
    refine hsum.congr (fun N => ?_)
    ring


end NlsGge.ThirdConsultation.AL
