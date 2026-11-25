import Mathlib
import NlsGge.Atomic.G2.G2074
import NlsGge.Atomic.G2.G2019
import NlsGge.Atomic.G2.G2046
import NlsGge.Atomic.G3.G3008
import NlsGge.Atomic.G3.G3019
import NlsGge.Atomic.G3.G3RatioHost
import NlsGge.GK38.TauGamma
import NlsGge.GK38.StdRootBranchesScalar
import NlsGge.GK38.IsolatingDefs

/- G3_009 PRODUCTION01 (proof development, AUTHOR; not self-reviewed). Target NlsGge/Atomic/G3/G3009.lean, namespace NlsGge.GKDefinitionDesign.
   Head VERBATIM from followup4 STATEMENTS/G3.md (sha256 d03d1697...), section "## G3-009". Helpers in namespace G3009Aux.
   Uses: G2-074 (quadratic-gap witness), G2-019 g2019_leaf_family (uniform isolating family), G3-008 (nearest endpoint),
   G3-019 (betaOmega, betaSegmentPoint), the shared RATIO host (betaRootRatioAlong). No hypothesis beyond the head. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G3009Aux

/-- Uniform radius bound for an isolating geometry (finitely many indices plus the constant pi/4 tail). -/
theorem radius_bound {C : ℤ → ℂ} {R : ℤ → ℝ} {c : ℝ} {N : ℕ}
    (hgeo : IsolatingGeometry38 C R c N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k : ℤ, R k ≤ M := by
  have hs : 0 ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), R j :=
    Finset.sum_nonneg (fun j _ => (hgeo.1 j).1.le)
  have hp : (0 : ℝ) < Real.pi / 4 := by positivity
  refine ⟨Real.pi / 4 + ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), R j, by linarith, ?_⟩
  intro k
  by_cases hk : (N : ℤ) < |k|
  · have hRk : R k = Real.pi / 4 := (hgeo.2.2.2.2 k hk).2.1
    linarith
  · have hmem : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      rw [Finset.mem_Icc]
      exact abs_le.1 (not_lt.1 hk)
    have hle : R k ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), R j :=
      Finset.single_le_sum (fun j _ => (hgeo.1 j).1.le) hmem
    linarith

/-- The gap of index m is at most twice the radius of its isolating disc. -/
theorem gap_le {C : ℤ → ℂ} {R : ℤ → ℝ} {φ : PotPair}
    (hsp : IsolatingSpectral38 φ C R) (m : ℤ) :
    ‖lamPlus φ m - lamMinus φ m‖ < 2 * R m := by
  have hb : lamPlus φ m ∈ Metric.ball (C m) (R m) := (hsp.1 m).1 (right_mem_segment ℝ _ _)
  have ha : lamMinus φ m ∈ Metric.ball (C m) (R m) := (hsp.1 m).1 (left_mem_segment ℝ _ _)
  rw [Metric.mem_ball] at hb ha
  rw [← dist_eq_norm]
  calc dist (lamPlus φ m) (lamMinus φ m)
      ≤ dist (lamPlus φ m) (C m) + dist (lamMinus φ m) (C m) := dist_triangle_right _ _ _
    _ < R m + R m := add_lt_add hb ha
    _ = 2 * R m := by ring

/-- Real inequality behind the numerator bound (uniform constant 2 + sqrt 2 * sqrt B * 2M). -/
theorem real_ineq (g w d B M : ℝ) (hg0 : 0 ≤ g) (hw : 0 < w) (hd : 0 < d)
    (hgd : g / 2 ≤ d) (hdw : d ≤ g + w) (hgM : g ≤ 2 * M) (hB : 0 ≤ B) (hM : 0 ≤ M) :
    Real.sqrt B * g ^ 2 + 2 * d ≤
      (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) * (Real.sqrt (g + w) * Real.sqrt d) := by
  have hp0 : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hq0 : 0 ≤ Real.sqrt (g + w) := Real.sqrt_nonneg _
  have hp2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have hq2 : Real.sqrt (g + w) ^ 2 = g + w := Real.sq_sqrt (by linarith)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpq : Real.sqrt d ≤ Real.sqrt (g + w) := Real.sqrt_le_sqrt hdw
  have hX0 : 0 ≤ Real.sqrt 2 * Real.sqrt (g + w) * Real.sqrt d :=
    mul_nonneg (mul_nonneg hs20 hq0) hp0
  have hXsq : (Real.sqrt 2 * Real.sqrt (g + w) * Real.sqrt d) ^ 2 = 2 * (g + w) * d := by
    rw [mul_pow, mul_pow, hs2, hq2, hp2]
  have hgd2 : g ≤ 2 * d := by linarith
  have hgw : g ≤ g + w := by linarith
  have hgX : g ≤ Real.sqrt 2 * Real.sqrt (g + w) * Real.sqrt d := by
    rw [← sq_le_sq₀ hg0 hX0, hXsq]
    have h := mul_le_mul hgd2 hgw hg0 (by linarith)
    nlinarith
  have hg2 : g ^ 2 ≤ 2 * M * (Real.sqrt 2 * Real.sqrt (g + w) * Real.sqrt d) := by
    have h1 : g ^ 2 ≤ 2 * M * g := by nlinarith
    have h2 : 2 * M * g ≤ 2 * M * (Real.sqrt 2 * Real.sqrt (g + w) * Real.sqrt d) :=
      mul_le_mul_of_nonneg_left hgX (by linarith)
    linarith
  have hpp : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd.le
  have hd2 : 2 * d ≤ 2 * (Real.sqrt (g + w) * Real.sqrt d) := by
    have h3 : Real.sqrt d * Real.sqrt d ≤ Real.sqrt (g + w) * Real.sqrt d :=
      mul_le_mul_of_nonneg_right hpq hp0
    linarith
  calc Real.sqrt B * g ^ 2 + 2 * d
      ≤ Real.sqrt B * (2 * M * (Real.sqrt 2 * Real.sqrt (g + w) * Real.sqrt d))
          + 2 * (Real.sqrt (g + w) * Real.sqrt d) :=
        add_le_add (mul_le_mul_of_nonneg_left hg2 hsB0) hd2
    _ = (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) * (Real.sqrt (g + w) * Real.sqrt d) := by ring

end G3009Aux

theorem G3_009 (φ0 : PotPair) (hφ0 : φ0 ∈ sourceW) :
  ∃ V : Set PotPair, ∃ C : ℝ,
    IsOpen V ∧ φ0 ∈ V ∧ V ⊆ sourceW ∧ 0 < C ∧
    ∀ φ ∈ V, ∀ n m : ℤ, m ≠ n →
      ‖muSeq φ m-lamMinus φ m‖ ≤ ‖muSeq φ m-lamPlus φ m‖ →
      betaOmega m φ ≠ 0 → ∀ t ∈ Ioo (0 : ℝ) 1,
        standardRoot φ m (betaSegmentPoint m φ t) ≠ 0 ∧
        ‖betaRootRatioAlong n m φ t‖ ≤
          C * Real.sqrt (‖gap φ m‖+‖betaOmega m φ‖) /
            (Real.sqrt t * Real.sqrt ‖betaOmega m φ‖) := by
  obtain ⟨V74, hV74o, hφV74, hV74W, B, hB, hA74⟩ := G2_074 φ0 hφ0
  have hgk0 : φ0 ∈ gkW := sourceFamily.W_gk hφ0
  obtain ⟨U, hUo, hφU, hUgk, C₀, R, c, N, hgeo, hspec⟩ := g2019_leaf_family φ0 hgk0
  obtain ⟨M, hM0, hM⟩ := G3009Aux.radius_bound hgeo
  refine ⟨V74 ∩ U, 2 + Real.sqrt 2 * Real.sqrt B * (2 * M), hV74o.inter hUo,
    ⟨hφV74, hφU⟩, fun φ hφ => hV74W hφ.1, ?_, ?_⟩
  · have h0 : 0 ≤ Real.sqrt 2 * Real.sqrt B * (2 * M) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg B)) (by linarith)
    linarith
  intro φ hφ n m hmn hnear hω t ht
  unfold gap
  have hgk : φ ∈ gkW := hUgk hφ.2
  have hsp : IsolatingSpectral38 φ C₀ R := hspec φ hφ.2
  have ht0 : 0 < t := ht.1
  have ht1 : t < 1 := ht.2
  have hωpos : 0 < ‖betaOmega m φ‖ := norm_pos_iff.2 hω
  have hτd : tauN φ m = (lamPlus φ m + lamMinus φ m) / 2 := tauN_value38 φ hgk m
  have hg2d : gamma2 φ m = (lamPlus φ m - lamMinus φ m) ^ 2 := gamma2_value38 φ hgk m
  have hgM : ‖lamPlus φ m - lamMinus φ m‖ ≤ 2 * M :=
    le_trans (G3009Aux.gap_le hsp m).le (by linarith [hM m])
  -- normalized root against tau, from the G2-074 quadratic-gap witness
  obtain ⟨A, hfac, hsum, hle⟩ := hA74 φ hφ.1 n
  have hν : normalizedRoot n m φ = tauN φ m + gamma2 φ m * A ⟨m, hmn⟩ := hfac ⟨m, hmn⟩
  have hAsq : ‖A ⟨m, hmn⟩‖ ^ 2 ≤ B :=
    le_trans (hsum.le_tsum ⟨m, hmn⟩ (fun j _ => sq_nonneg _)) hle
  have hAn : ‖A ⟨m, hmn⟩‖ ≤ Real.sqrt B := by
    have h := Real.abs_le_sqrt hAsq
    rwa [abs_of_nonneg (norm_nonneg _)] at h
  have hντ : ‖normalizedRoot n m φ - tauN φ m‖ ≤
      Real.sqrt B * ‖lamPlus φ m - lamMinus φ m‖ ^ 2 := by
    rw [hν, add_sub_cancel_left, norm_mul, hg2d, norm_pow, mul_comm (Real.sqrt B)]
    exact mul_le_mul_of_nonneg_left hAn (sq_nonneg _)
  -- nearest-endpoint estimate (G3-008) and the distance bounds for z = betaSegmentPoint
  have hgd : ‖lamPlus φ m - lamMinus φ m‖ / 2 ≤ ‖lamPlus φ m - betaSegmentPoint m φ t‖ := by
    by_cases hγ : lamPlus φ m = lamMinus φ m
    · rw [hγ, sub_self, norm_zero, zero_div]
      exact norm_nonneg _
    · have hab : lamMinus φ m ≠ lamPlus φ m := fun h => hγ h.symm
      exact NlsGge.Atomic.G3.nearest_endpoint_segment (lamMinus φ m) (lamPlus φ m) (muSeq φ m) t
        hab hnear ⟨ht0.le, ht1.le⟩
  have hdw : ‖lamPlus φ m - betaSegmentPoint m φ t‖ ≤
      ‖lamPlus φ m - lamMinus φ m‖ + ‖betaOmega m φ‖ := by
    have e : lamPlus φ m - betaSegmentPoint m φ t =
        (lamPlus φ m - lamMinus φ m) - (t : ℂ) * betaOmega m φ := by
      unfold betaSegmentPoint
      ring
    rw [e]
    have h1 : ‖(t : ℂ) * betaOmega m φ‖ ≤ ‖betaOmega m φ‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact mul_le_of_le_one_left (norm_nonneg _) ht1.le
    calc ‖(lamPlus φ m - lamMinus φ m) - (t : ℂ) * betaOmega m φ‖
        ≤ ‖lamPlus φ m - lamMinus φ m‖ + ‖(t : ℂ) * betaOmega m φ‖ := norm_sub_le _ _
      _ ≤ ‖lamPlus φ m - lamMinus φ m‖ + ‖betaOmega m φ‖ := by linarith
  have hτz_le : ‖tauN φ m - betaSegmentPoint m φ t‖ ≤
      2 * ‖lamPlus φ m - betaSegmentPoint m φ t‖ := by
    have e : tauN φ m - betaSegmentPoint m φ t =
        (lamPlus φ m - betaSegmentPoint m φ t) -
          ((1 / 2 : ℝ) : ℂ) * (lamPlus φ m - lamMinus φ m) := by
      rw [hτd]
      push_cast
      ring
    rw [e]
    calc ‖(lamPlus φ m - betaSegmentPoint m φ t) -
          ((1 / 2 : ℝ) : ℂ) * (lamPlus φ m - lamMinus φ m)‖
        ≤ ‖lamPlus φ m - betaSegmentPoint m φ t‖ +
            ‖((1 / 2 : ℝ) : ℂ) * (lamPlus φ m - lamMinus φ m)‖ := norm_sub_le _ _
      _ = ‖lamPlus φ m - betaSegmentPoint m φ t‖ + ‖lamPlus φ m - lamMinus φ m‖ / 2 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          ring
      _ ≤ 2 * ‖lamPlus φ m - betaSegmentPoint m φ t‖ := by linarith [hgd]
  -- the point z = betaSegmentPoint m φ t is not the centre tau (uses the nearest-endpoint condition)
  have hzτ : betaSegmentPoint m φ t ≠ tauN φ m := by
    intro h
    have h' : lamMinus φ m + (t : ℂ) * betaOmega m φ = (lamPlus φ m + lamMinus φ m) / 2 := by
      rw [← hτd]
      exact h
    have hγω : lamPlus φ m - lamMinus φ m = 2 * (t : ℂ) * betaOmega m φ := by
      linear_combination (-2 : ℂ) * h'
    have hωd : betaOmega m φ = muSeq φ m - lamMinus φ m := rfl
    have hμb : muSeq φ m - lamPlus φ m = (1 - 2 * (t : ℂ)) * betaOmega m φ := by
      linear_combination (-1 : ℂ) * hωd - hγω
    have hle' : ‖betaOmega m φ‖ ≤ ‖(1 - 2 * (t : ℂ)) * betaOmega m φ‖ := by
      rw [← hμb]
      exact hnear
    have hc : ‖(1 - 2 * (t : ℂ))‖ = |1 - 2 * t| := by
      have e : (1 - 2 * (t : ℂ)) = ((1 - 2 * t : ℝ) : ℂ) := by
        push_cast
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
    rw [norm_mul, hc] at hle'
    have habs : |1 - 2 * t| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
    nlinarith [hωpos, habs]
  have hdpos : 0 < ‖lamPlus φ m - betaSegmentPoint m φ t‖ := by
    rcases (norm_nonneg (lamPlus φ m - betaSegmentPoint m φ t)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 : lamPlus φ m - betaSegmentPoint m φ t = 0 := norm_eq_zero.1 h.symm
      have hbz : lamPlus φ m = lamMinus φ m + (t : ℂ) * betaOmega m φ := by
        unfold betaSegmentPoint at h0
        exact sub_eq_zero.1 h0
      have hg0 : ‖lamPlus φ m - lamMinus φ m‖ = 0 := by
        rw [← h] at hgd
        exact le_antisymm (by linarith) (norm_nonneg _)
      have hab : lamPlus φ m = lamMinus φ m := sub_eq_zero.1 (norm_eq_zero.1 hg0)
      have htω : (t : ℂ) * betaOmega m φ = 0 := by
        linear_combination hab - hbz
      exact hω ((mul_eq_zero.1 htω).resolve_left (Complex.ofReal_ne_zero.2 ht0.ne'))
  -- the standard root: square identity, norm, and nonvanishing
  have hτz0 : tauN φ m - betaSegmentPoint m φ t ≠ 0 := sub_ne_zero.mpr (Ne.symm hzτ)
  have hstdsq : standardRoot φ m (betaSegmentPoint m φ t) ^ 2 =
      (lamMinus φ m - betaSegmentPoint m φ t) * (lamPlus φ m - betaSegmentPoint m φ t) := by
    unfold standardRoot
    rw [stdRoot_sq_of_ne38 hτz0, hg2d, hτd]
    ring
  have hstdnorm : ‖standardRoot φ m (betaSegmentPoint m φ t)‖ =
      Real.sqrt t * Real.sqrt ‖betaOmega m φ‖ * Real.sqrt ‖lamPlus φ m - betaSegmentPoint m φ t‖ := by
    have haz : ‖lamMinus φ m - betaSegmentPoint m φ t‖ = t * ‖betaOmega m φ‖ := by
      have e : lamMinus φ m - betaSegmentPoint m φ t = -((t : ℂ) * betaOmega m φ) := by
        unfold betaSegmentPoint
        ring
      rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hsq2 : ‖standardRoot φ m (betaSegmentPoint m φ t)‖ ^ 2 =
        t * ‖betaOmega m φ‖ * ‖lamPlus φ m - betaSegmentPoint m φ t‖ := by
      rw [← norm_pow, hstdsq, norm_mul, haz]
    rw [← Real.sqrt_sq (norm_nonneg (standardRoot φ m (betaSegmentPoint m φ t))), hsq2,
      Real.sqrt_mul (mul_nonneg ht0.le (norm_nonneg _)), Real.sqrt_mul ht0.le]
  have hstdpos : 0 < ‖standardRoot φ m (betaSegmentPoint m φ t)‖ := by
    rw [hstdnorm]
    exact mul_pos (mul_pos (Real.sqrt_pos.2 ht0) (Real.sqrt_pos.2 hωpos))
      (Real.sqrt_pos.2 hdpos)
  have hstd0 : standardRoot φ m (betaSegmentPoint m φ t) ≠ 0 := norm_pos_iff.1 hstdpos
  -- numerator bound
  have hR := G3009Aux.real_ineq ‖lamPlus φ m - lamMinus φ m‖ ‖betaOmega m φ‖
    ‖lamPlus φ m - betaSegmentPoint m φ t‖ B M (norm_nonneg _) hωpos hdpos hgd hdw hgM
    hB.le hM0
  have hsplit : normalizedRoot n m φ - betaSegmentPoint m φ t =
      (normalizedRoot n m φ - tauN φ m) + (tauN φ m - betaSegmentPoint m φ t) := by ring
  have htri := norm_add_le (normalizedRoot n m φ - tauN φ m) (tauN φ m - betaSegmentPoint m φ t)
  have hnum : ‖normalizedRoot n m φ - betaSegmentPoint m φ t‖ ≤
      (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
        (Real.sqrt (‖lamPlus φ m - lamMinus φ m‖ + ‖betaOmega m φ‖) *
          Real.sqrt ‖lamPlus φ m - betaSegmentPoint m φ t‖) := by
    rw [hsplit]
    linarith [htri, hντ, hτz_le, hR]
  -- assemble the ratio bound
  refine ⟨hstd0, ?_⟩
  unfold betaRootRatioAlong
  rw [norm_div, div_le_iff₀ hstdpos, hstdnorm]
  have hsr : Real.sqrt t * Real.sqrt ‖betaOmega m φ‖ ≠ 0 :=
    (mul_pos (Real.sqrt_pos.2 ht0) (Real.sqrt_pos.2 hωpos)).ne'
  have key : (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
        Real.sqrt (‖lamPlus φ m - lamMinus φ m‖ + ‖betaOmega m φ‖) /
          (Real.sqrt t * Real.sqrt ‖betaOmega m φ‖) *
        (Real.sqrt t * Real.sqrt ‖betaOmega m φ‖ *
          Real.sqrt ‖lamPlus φ m - betaSegmentPoint m φ t‖) =
      (2 + Real.sqrt 2 * Real.sqrt B * (2 * M)) *
        (Real.sqrt (‖lamPlus φ m - lamMinus φ m‖ + ‖betaOmega m φ‖) *
          Real.sqrt ‖lamPlus φ m - betaSegmentPoint m φ t‖) := by
    rw [div_mul_eq_mul_div, div_eq_iff hsr]
    ring
  rw [key]
  exact hnum

end
end NlsGge.GKDefinitionDesign
