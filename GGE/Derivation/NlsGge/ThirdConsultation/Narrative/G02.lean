import Mathlib
import NlsGge.Atomic.KSPS.KSPS028
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform7
import NlsGge.ThirdConsultation.KSPS.KSPS023Uniform2
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform2
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform9
import NlsGge.Schur.PhysicalH1ComplexCarrierSchurBridge
import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1

/-!
G02 author packet 03, proof development. Root owns the compiler lane.
The 31 revision02 declarations passed root compilation. New uniform half-gap
and full endpoint expansion proofs below are uncompiled candidates. The local
smallness condition concerns the unscaled correction; tP powers are retained.
No missing quantitative estimate is assumed in the final uniform theorem.
-/
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators
open NlsGge.Pilot NlsGge.Schur NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.Narrative

abbrev G02H1 := WeightedHilbert (sobolevModeWeight (1 : ℝ))

/-- Both members of the SAME actual real spectral potential pair. -/
def g02_field (w : G02H1) (b : Bool) : PhysicalL2 :=
  if b then physicalH1ComplexCarrierToL2Actual22 w
  else star (physicalH1ComplexCarrierToL2Actual22 w)

/-- The reflected source Fourier energy of each member equals the actual H1 norm. -/
theorem g02_field_hasSum (w : G02H1) (b : Bool) :
    HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
      ‖fourierSeq38 (g02_field w b) n‖^2) (‖w‖^2) := by
  have hw := weightedHilbert_hasSum (sobolevModeWeight (1 : ℝ)) w
  cases b
  · simpa only [g02_field, Bool.false_eq_true, ite_false, fourierSeq38_apply,
      physicalFourier_star38, neg_neg, physicalH1ComplexCarrierToL2Actual22_fourier,
      norm_neg, norm_star, Nat.cast_one] using hw
  · let f : ℤ → ℝ := fun n => sobolevModeWeight (1 : ℝ) n * ‖w n‖^2
    have hs : Summable (fun n : ℤ => f (-n)) := hw.summable.comp_injective neg_injective
    have he : (∑' n : ℤ, f (-n)) = ‖w‖^2 :=
      ((Equiv.neg ℤ).tsum_eq f).trans hw.tsum_eq
    have hh : HasSum (fun n : ℤ => f (-n)) (‖w‖^2) := he ▸ hs.hasSum
    simpa only [g02_field, ite_true, fourierSeq38_apply,
      physicalH1ComplexCarrierToL2Actual22_fourier, norm_neg, Nat.cast_one,
      f, sobolevModeWeight_neg] using hh

theorem g02_field_membership (w : G02H1) (b : Bool) :
    fourierSeq38 (g02_field w b) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := by
  rw [mem_seqSobolev38_iff]
  exact (g02_field_hasSum w b).summable

/-- Canonical actual completed physical Sobolev preimage; no existence is postulated. -/
def g02_recover (w : G02H1) (b : Bool) : PhysicalSobolev38 ((1 : ℕ) : ℝ) :=
  (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm
    (carrierMk38 ((1 : ℕ) : ℝ) (fourierSeq38 (g02_field w b)) (g02_field_membership w b))

theorem g02_recover_embed (w : G02H1) (b : Bool) :
    physicalSobolevEmbed 1 (g02_recover w b) = g02_field w b := by
  apply fourierSeq38_injective
  funext n
  rw [physicalSobolevEmbed_fourier]
  simp only [g02_recover, LinearIsometryEquiv.apply_symm_apply, carrierCoe38_mk]

theorem g02_recover_norm (w : G02H1) (b : Bool) : ‖g02_recover w b‖ = ‖w‖ := by
  let z := carrierMk38 ((1 : ℕ) : ℝ)
    (fourierSeq38 (g02_field w b)) (g02_field_membership w b)
  have hz := carrier_hasSum_norm_sq38 ((1 : ℕ) : ℝ) z
  change HasSum (fun n : ℤ => sobolevModeWeight ((1 : ℕ) : ℝ) n *
    ‖fourierSeq38 (g02_field w b) n‖^2) (‖z‖^2) at hz
  have he : ‖z‖^2 = ‖w‖^2 := hz.unique (g02_field_hasSum w b)
  have hn : ‖z‖ = ‖w‖ := (sq_eq_sq₀ (norm_nonneg z) (norm_nonneg w)).mp he
  calc
    ‖g02_recover w b‖ = ‖z‖ := (physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).symm.norm_map z
    _ = ‖w‖ := hn

def g02_pair (w : G02H1) : KSPS.SobolevC 1 := (g02_recover w true, g02_recover w false)

theorem g02_pair_toPotPair (w : G02H1) :
    KSPS.toPotPair (g02_pair w) = realSlice (physicalH1ComplexCarrierToL2Actual22 w) := by
  change (physicalSobolevEmbed 1 (g02_recover w true),
    physicalSobolevEmbed 1 (g02_recover w false)) = _
  rw [g02_recover_embed, g02_recover_embed]
  rfl

theorem g02_pair_real (w : G02H1) : MRiccati.RealPair (g02_pair w) := by
  unfold MRiccati.RealPair MRiccati.realPhysicalFromPair
  rw [g02_pair_toPotPair, realSlice_fst]

theorem g02_pair_norm_le (w : G02H1) : KSPS.sobolevNorm 1 (g02_pair w) ≤ 2*‖w‖ := by
  change Real.sqrt (‖g02_recover w true‖^2 + ‖g02_recover w false‖^2) ≤ 2*‖w‖
  rw [g02_recover_norm, g02_recover_norm, Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg ‖w‖]

theorem g02_pair_upper (w : G02H1) (n : ℤ) :
    KSPS.periodicPlus (g02_pair w) n =
      (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n : ℂ) := by
  rw [KSPS.periodicPlus, g02_pair_toPotPair]
  exact (lamPlus_real _ n).1

theorem g02_pair_lower (w : G02H1) (n : ℤ) :
    KSPS.periodicMinus (g02_pair w) n =
      (actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n : ℂ) := by
  rw [KSPS.periodicMinus, g02_pair_toPotPair]
  exact (lamPlus_real _ n).2

theorem g02_pair_fourier (w : G02H1) (n : ℤ) :
    physicalFourier (KSPS.toPotPair (g02_pair w)).1 (-n) =
      physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n) := by
  rw [g02_pair_toPotPair, realSlice_fst]

/-- The coefficient convention from the exact N=1 spectral polynomial. -/
def g02_c1 (w : G02H1) : ℝ := (KSPS.massCoefficient (g02_pair w)).re

def g02_c2 (w : G02H1) : ℝ := -(KSPS.momentumCoefficient (g02_pair w)).re

theorem g02_coefficients_uniform (B : ℝ) (hB : 0 ≤ B) :
    ∀ w : G02H1, ‖w‖ ≤ B → |g02_c1 w| ≤ (2*B)^2 ∧ |g02_c2 w| ≤ (2*B)^2 := by
  intro w hw
  have hp : KSPS.sobolevNorm 1 (g02_pair w) ≤ 2*B :=
    (g02_pair_norm_le w).trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  have h := KSPS.first_two_spectral_coefficients_bounded (2*B) (by positivity) (g02_pair w) hp
  constructor
  · exact (Complex.abs_re_le_norm _).trans h.1
  · simpa only [g02_c2, abs_neg] using (Complex.abs_re_le_norm _).trans h.2

/-- A purely scalar real-part identity, valid also at the totalized zero denominator. -/
theorem g02_re_div_real (z : ℂ) (a : ℝ) : (z / (a : ℂ)).re = z.re / a := by
  simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

theorem g02_polynomial_re (w : G02H1) (n : ℤ) :
    (KSPS.spectralPolynomial (g02_pair w) n).re =
      (n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2 := by
  rw [KSPS025U2.spectralPolynomial_one_eq]
  have hn : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
  simp only [hn, ← Complex.ofReal_pow, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, g02_re_div_real, g02_c1, g02_c2]
  ring

/-- Canonical real residuals, selected before any ball radius. The zero mode is retained. -/
def g02_rPlus (w : G02H1) (n : ℤ) : ℝ :=
  (n : ℝ)^2 * (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n -
    ((n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2) -
      ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖)

def g02_rMinus (w : G02H1) (n : ℤ) : ℝ :=
  (n : ℝ)^2 * (actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n -
    ((n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2) +
      ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖)

theorem g02_endpoint_identities (w : G02H1) (n : ℤ) (hn : n ≠ 0) :
    actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n =
      (n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2 +
        ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖ + g02_rPlus w n/(n : ℝ)^2 ∧
    actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n =
      (n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2 -
        ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖ + g02_rMinus w n/(n : ℝ)^2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  constructor <;> dsimp only [g02_rPlus, g02_rMinus] <;> field_simp [hnR] <;> ring

/-- The single remaining uniform estimate concerns this real half-gap residual. -/
def g02_halfGap (φ : KSPS.SobolevC 1) (n : ℤ) : ℝ :=
  KSPS.indexWeight n^2 * (((KSPS.periodicPlus φ n - KSPS.periodicMinus φ n)/2).re -
    ‖physicalFourier (KSPS.toPotPair φ).1 (-n)‖)

def g02_midError (φ : KSPS.SobolevC 1) (n : ℤ) : ℝ :=
  KSPS.indexWeight n^2 * (KSPS.midpoint φ n - KSPS.spectralPolynomial φ n).re

/-- Uniform fourth-power control of the midpoint component, proved from the landed l2 estimate. -/
theorem g02_midpoint_uniform (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : KSPS.SobolevC 1, KSPS.sobolevNorm 1 φ ≤ B →
      Summable (fun n : ℤ => |g02_midError φ n|^4) ∧
      (∑' n : ℤ, |g02_midError φ n|^4) ≤ C := by
  obtain ⟨C, hC, hmid⟩ := KSPS.midpoint_spectral_expansion_uniform 1 le_rfl B hB
  refine ⟨C^4, by positivity, ?_⟩
  intro φ hφ
  have hfinite (F : Finset ℤ) : ∑ n ∈ F, |g02_midError φ n|^4 ≤ C^4 := by
    have hs : ∑ n ∈ F, (g02_midError φ n)^2 ≤ C^2 := by
      refine (Finset.sum_le_sum (fun n _ => ?_)).trans ((hmid φ hφ).2 F)
      have hab : |g02_midError φ n| ≤ KSPS.indexWeight n^2 *
          ‖KSPS.midpoint φ n - KSPS.spectralPolynomial φ n‖ := by
        dsimp only [g02_midError]
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (sq_nonneg _)
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2
    calc
      ∑ n ∈ F, |g02_midError φ n|^4 = ∑ n ∈ F, ((g02_midError φ n)^2)^2 := by
        apply Finset.sum_congr rfl
        intro n _
        rw [show |g02_midError φ n|^4 = (|g02_midError φ n|^2)^2 by ring, sq_abs]
      _ ≤ (∑ n ∈ F, (g02_midError φ n)^2)^2 :=
        KSPS025U7.sum_sq_le_sq_sum F (fun n => (g02_midError φ n)^2) (fun _ _ => sq_nonneg _)
      _ ≤ (C^2)^2 := pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs 2
      _ = C^4 := by ring
  have hs := summable_of_sum_le (fun n => pow_nonneg (abs_nonneg _) 4) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

/-- The uniform midpoint component is transported to the actual physical H1 ball. -/
theorem g02_physical_midpoint_uniform (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : G02H1, ‖w‖ ≤ B →
      Summable (fun n : ℤ => |g02_midError (g02_pair w) n|^4) ∧
      (∑' n : ℤ, |g02_midError (g02_pair w) n|^4) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := g02_midpoint_uniform (2*B) (by positivity)
  refine ⟨C, hC, fun w hw => hbound (g02_pair w) ?_⟩
  exact (g02_pair_norm_le w).trans (mul_le_mul_of_nonneg_left hw (by norm_num))

/-- Exact decomposition of the two independent actual residuals into midpoint and half-gap. -/
theorem g02_remainders_decompose (w : G02H1) (n : ℤ) :
    g02_rPlus w n = ((n : ℝ)^2 / KSPS.indexWeight n^2) *
      (g02_midError (g02_pair w) n + g02_halfGap (g02_pair w) n) ∧
    g02_rMinus w n = ((n : ℝ)^2 / KSPS.indexWeight n^2) *
      (g02_midError (g02_pair w) n - g02_halfGap (g02_pair w) n) := by
  have hw : KSPS.indexWeight n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (KSPS015W.one_le_w n))
  have hmid : (KSPS.midpoint (g02_pair w) n).re =
      (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n +
        actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n)/2 := by
    rw [KSPS.midpoint, g02_pair_lower, g02_pair_upper]
    change (((actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n : ℂ) +
      (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n : ℂ))/((2 : ℝ) : ℂ)).re = _
    rw [g02_re_div_real]
    simp only [Complex.add_re, Complex.ofReal_re]
    ring
  dsimp only [g02_rPlus, g02_rMinus, g02_midError, g02_halfGap]
  simp only [Complex.sub_re, hmid, g02_polynomial_re, g02_pair_upper, g02_pair_lower,
    g02_pair_fourier, Complex.div_ofNat_re, Complex.ofReal_re]
  constructor <;> field_simp [hw] <;> ring


/-- Fourth-power summability of the half-gap error is already pointwise in the landed KSPS028.
This theorem supplies no bound uniform in a ball radius. -/
theorem g02_halfGap_summable (φ : KSPS.SobolevC 1) (hφ : MRiccati.RealPair φ) :
    Summable (fun n : ℤ => |g02_halfGap φ n|^4) := by
  obtain ⟨ep, em, hp, hm, hEq⟩ := KSPS.real_periodic_endpoint_expansion 1 le_rfl φ hφ
  have hp4 : Summable (fun n : ℤ => ‖ep n‖^4) := by
    simpa only [KSPS.LpSequence, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using hp
  have hm4 : Summable (fun n : ℤ => ‖em n‖^4) := by
    simpa only [KSPS.LpSequence, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using hm
  have hdom := (hp4.add hm4).mul_left (27 : ℝ)
  have hne : ∀ᶠ n : ℤ in cofinite, n ≠ 0 := by
    rw [Filter.eventually_cofinite]
    simpa using Set.finite_singleton (0 : ℤ)
  refine Summable.of_norm_bounded_eventually hdom ?_
  filter_upwards [hne] with n hn
  obtain ⟨hplus, hminus⟩ := hEq n hn
  have hplus' : KSPS.periodicPlus φ n = KSPS.spectralPolynomial φ n +
      (‖physicalFourier (KSPS.toPotPair φ).1 (-n)‖ : ℂ) + ep n/(KSPS.indexWeight n : ℂ)^2 := by
    simpa only [KSPS.indexValue] using hplus
  have hminus' : KSPS.periodicMinus φ n = KSPS.spectralPolynomial φ n -
      (‖physicalFourier (KSPS.toPotPair φ).1 (-n)‖ : ℂ) + em n/(KSPS.indexWeight n : ℂ)^2 := by
    simpa only [KSPS.indexValue] using hminus
  have hw : (KSPS.indexWeight n : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (lt_of_lt_of_le zero_lt_one (KSPS015W.one_le_w n))
  have hC : (KSPS.indexWeight n : ℂ)^2 *
      (((KSPS.periodicPlus φ n-KSPS.periodicMinus φ n)/2) -
        (‖physicalFourier (KSPS.toPotPair φ).1 (-n)‖ : ℂ)) = (ep n-em n)/2 := by
    rw [hplus', hminus']
    field_simp [hw] <;> ring
  have he : g02_halfGap φ n = ((ep n).re-(em n).re)/2 := by
    have h := congrArg Complex.re hC
    simpa only [g02_halfGap, ← Complex.ofReal_pow, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re,
      Complex.div_ofNat_re] using h
  have hab : |g02_halfGap φ n| ≤ ‖ep n‖+‖em n‖ := by
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := (abs_sub (ep n).re (em n).re).trans
      (add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _))
    linarith [norm_nonneg (ep n), norm_nonneg (em n)]
  have hq := KSPS028P.pow4_sum_le ‖ep n‖ ‖em n‖ 0 (norm_nonneg _) (norm_nonneg _) le_rfl
  simp only [add_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hq
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 4)]
  exact (pow_le_pow_left₀ (abs_nonneg _) hab 4).trans hq

/-- Ratio between the manuscript n² scaling and the regularized KSPS weight. -/
theorem g02_index_ratio (n : ℤ) :
    0 ≤ (n : ℝ)^2/KSPS.indexWeight n^2 ∧ (n : ℝ)^2/KSPS.indexWeight n^2 ≤ 1 := by
  have hw : 0 < KSPS.indexWeight n := lt_of_lt_of_le zero_lt_one (KSPS015W.one_le_w n)
  constructor
  · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · rw [div_le_one (pow_pos hw 2)]
    unfold KSPS.indexWeight
    rw [Real.sq_sqrt (by positivity)]
    linarith

/-- Both canonical actual remainders are summable to the fourth power, pointwise in w.
The missing G02 clause is a bound on these convergent sums uniform on H1 balls. -/
theorem g02_physical_remainders_summable (w : G02H1) :
    Summable (fun n : ℤ => |g02_rPlus w n|^4) ∧
    Summable (fun n : ℤ => |g02_rMinus w n|^4) := by
  obtain ⟨C, _, hmid⟩ := g02_midpoint_uniform (KSPS.sobolevNorm 1 (g02_pair w))
    (Real.sqrt_nonneg _)
  have hm := (hmid (g02_pair w) le_rfl).1
  have hg := g02_halfGap_summable (g02_pair w) (g02_pair_real w)
  have hdom := (hm.add hg).mul_left (27 : ℝ)
  have hbound (upper : Bool) (n : ℤ) :
      |(if upper then g02_rPlus w n else g02_rMinus w n)|^4 ≤
        27*(|g02_midError (g02_pair w) n|^4+|g02_halfGap (g02_pair w) n|^4) := by
    have hdec := g02_remainders_decompose w n
    have hr := g02_index_ratio n
    have hab : |(if upper then g02_rPlus w n else g02_rMinus w n)| ≤
        |g02_midError (g02_pair w) n|+|g02_halfGap (g02_pair w) n| := by
      cases upper
      · simp only [Bool.false_eq_true, ite_false]
        rw [hdec.2, abs_mul, abs_of_nonneg hr.1]
        exact ((mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans_eq (one_mul _)).trans (abs_sub _ _)
      · simp only [ite_true]
        rw [hdec.1, abs_mul, abs_of_nonneg hr.1]
        exact ((mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans_eq (one_mul _)).trans (abs_add_le _ _)
    have hq := KSPS028P.pow4_sum_le |g02_midError (g02_pair w) n|
      |g02_halfGap (g02_pair w) n| 0 (abs_nonneg _) (abs_nonneg _) le_rfl
    simp only [add_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hq
    exact (pow_le_pow_left₀ (abs_nonneg _) hab 4).trans hq
  constructor
  · exact Summable.of_nonneg_of_le (fun n => pow_nonneg (abs_nonneg _) 4)
      (fun n => by simpa only [ite_true] using hbound true n) hdom
  · exact Summable.of_nonneg_of_le (fun n => pow_nonneg (abs_nonneg _) 4)
      (fun n => by simpa only [Bool.false_eq_true, ite_false] using hbound false n) hdom

/-- Actual physical-carrier endpoint expansion with independent real remainders.
This is pointwise in the field and does not assert the missing ball-uniform bound. -/
theorem g02_physical_endpoint_expansion (w : G02H1) :
    Summable (fun n : ℤ => |g02_rPlus w n|^4) ∧
    Summable (fun n : ℤ => |g02_rMinus w n|^4) ∧
    ∀ n : ℤ, n ≠ 0 →
      actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n =
        (n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2 +
          ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖ +
          g02_rPlus w n/(n : ℝ)^2 ∧
      actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n =
        (n : ℝ)*Real.pi + g02_c1 w/(n : ℝ) + g02_c2 w/(n : ℝ)^2 -
          ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖ +
          g02_rMinus w n/(n : ℝ)^2 := by
  exact ⟨(g02_physical_remainders_summable w).1,
    (g02_physical_remainders_summable w).2, g02_endpoint_identities w⟩


/-! G02 uniform extension: all endpoint data below are the same landed objects.
The local smallness assumption is on the unscaled correction, obtained on a
uniform tail from a uniform bound on tP. Powers of tP are retained explicitly. -/
open MeasureTheory
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W
open NlsGge.ThirdConsultation.KSPS023W NlsGge.ThirdConsultation.KSPS024W
open NlsGge.ThirdConsultation.KSPS025W NlsGge.ThirdConsultation.KSPS027W
open NlsGge.ThirdConsultation.KSPS028P NlsGge.ThirdConsultation.KSPS028C
open NlsGge.ThirdConsultation.KSPS028W

theorem g02_side_core_uniform (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ indexWeight n ^ N / 4) (hz : xi n ≠ 0)
    (hq : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) ^ 2 +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 = 0) :
    ∃ R : ℝ, 0 ≤ R ∧ R ≤ 1 / 4 ∧ indexWeight n ^ N * R ≤ tP N φ n ∧
      indexWeight n ^ (N + 1) * Eent N φ upper n ≤ tP N φ n ∧
      ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 1‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 1‖ ≤ R ∧
      ‖KSPSWKB.alpha φ (xi n) 0‖ ≤ KSPS016W.Sb φ / indexWeight n ∧
      ‖KSPSWKB.beta φ (xi n) 0‖ ≤ KSPS016W.Sb φ / indexWeight n ∧
      ‖KSPSWKB.beta φ (xi n) 0‖ ≤ 1 / 4 ∧
      ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 10 * R ∧
      ‖NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) - (n : ℂ) * (Real.pi : ℂ)‖ ≤ 1 / 2 ∧
      ‖Complex.exp (Complex.I * (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) -
          (n : ℂ) * (Real.pi : ℂ))) - 1‖ ≤ 5 * R ∧
      ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 0 -
          integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 1 -
          -(integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1))‖ ≤ Eent N φ upper n := by
  obtain ⟨hX1, hXT, hwX⟩ := KSPS015W.tail_facts a _ ha xi hxi n h1
  obtain ⟨-, hXS, -⟩ := KSPS015W.tail_facts a _ ha xi hxi n h2
  have hX0 : 0 < ‖xi n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (xi n) := ⟨hX0, hXT⟩
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  obtain ⟨-, -, hα, hβ⟩ := KSPS016W.dinv_facts φ (xi n) (indexWeight n) hX1 hthr hw0 hwX
  have hS0 := KSPS016W.Sb_nonneg φ
  have hq4 : KSPS016W.Sb φ / (2 * ‖xi n‖) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hSw : KSPS016W.Sb φ / (2 * ‖xi n‖) ≤ KSPS016W.Sb φ / indexWeight n :=
    div_le_div_of_nonneg_left hS0 hw0 hwX
  have hn1R : (1 : ℝ) ≤ |(n : ℝ)| := (KSPS016W.tail_nat a _ n h1).1
  obtain ⟨-, -, hF1, hF2⟩ := KSPS016W.fourier_facts φ n hn1R
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ with hrdef
  have hE : ∀ i j : Fin 2, KSPSWKB.endpointEntryError N φ upper i j n =
      r i j - (!![integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1),
            Complex.I * physicalFourier (toPotPair φ).1 (-n);
            -Complex.I * physicalFourier (toPotPair φ).2 n,
            -integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)] :
              Matrix (Fin 2) (Fin 2) ℂ) i j :=
    fun i j => NlsGge.ThirdConsultation.KSPS026W.entryError_eq φ upper xi hxe i j n hz
  have hY : ‖integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)‖ =
      ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
  have hent : ∀ (i j : Fin 2) (lead : ℂ),
      KSPSWKB.endpointEntryError N φ upper i j n = r i j - lead →
      ‖r i j‖ ≤ ‖lead‖ + ‖KSPSWKB.endpointEntryError N φ upper i j n‖ := by
    intro i j lead h
    have e : r i j = lead + KSPSWKB.endpointEntryError N φ upper i j n := by rw [h]; ring
    rw [e]; exact norm_add_le _ _
  set L : ℂ := integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1) with hLdef
  have hE00 := hE 0 0
  have hE11 := hE 1 1
  have e00 := hent 0 0 L hE00
  have e01 := hent 0 1 (Complex.I * physicalFourier (toPotPair φ).1 (-n)) (hE 0 1)
  have e10 := hent 1 0 (-Complex.I * physicalFourier (toPotPair φ).2 n) (hE 1 0)
  have e11 := hent 1 1 (-integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1)) hE11
  have hENT : ‖r 0 0 - L‖ + ‖r 1 1 - (-L)‖ ≤ Eent N φ upper n := by
    have f00 : r 0 0 - L = KSPSWKB.endpointEntryError N φ upper 0 0 n := by rw [hE00]; rfl
    have f11 : r 1 1 - (-L) = KSPSWKB.endpointEntryError N φ upper 1 1 n := by
      rw [hE11]
      congr 1
      rw [hLdef, ← neg_div]
      rfl
    rw [f00, f11]
    unfold Eent
    linarith [norm_nonneg (KSPSWKB.endpointEntryError N φ upper 0 1 n),
      norm_nonneg (KSPSWKB.endpointEntryError N φ upper 1 0 n)]
  rw [hLdef, hY] at e00
  rw [neg_div, norm_neg, hY] at e11
  rw [norm_mul, Complex.norm_I, one_mul] at e01
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul] at e10
  set R : ℝ := ‖r 0 0‖ + ‖r 0 1‖ + ‖r 1 0‖ + ‖r 1 1‖ with hRdef
  have hEu : Eent N φ upper n ≤ Eent N φ true n + Eent N φ false n := by
    have := Eent_nonneg N φ true n
    have := Eent_nonneg N φ false n
    cases upper <;> linarith
  have hRs : R ≤ Eent N φ upper n +
      (‖physicalFourier (toPotPair φ).1 (-n)‖ + ‖physicalFourier (toPotPair φ).2 n‖) +
      2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by
    have h2c : 2 * ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) =
        ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) +
          ‖integralRiccatiLeft φ (N + 1)‖ / (2 * ‖xi n‖) ^ (N + 1) := by ring
    rw [hRdef, h2c]; unfold Eent; linarith
  have hEw : indexWeight n ^ (N + 1) * Eent N φ upper n ≤ tP N φ n := by
    have h9 : indexWeight n ^ (N + 1) * Eent N φ upper n ≤
        indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) :=
      mul_le_mul_of_nonneg_left hEu (pow_nonneg hw0.le _)
    unfold tP
    have := norm_nonneg (physicalFourier (iteratedDerivative N φ.1) (-n))
    have := norm_nonneg (physicalFourier (iteratedDerivative N φ.2) n)
    have : 0 ≤ 2 * ‖integralRiccatiLeft φ (N + 1)‖ * (1 / indexWeight n) := by positivity
    linarith
  have hRw : indexWeight n ^ N * R ≤ tP N φ n := by
    have h8 := tau_pure N (indexWeight n) ‖xi n‖ (Eent N φ upper n) _ _ _ _ ‖integralRiccatiLeft φ (N + 1)‖ R
      hw1 hwX (Eent_nonneg N φ upper n) (norm_nonneg _) hF1 hF2 hRs
    have h9 : indexWeight n ^ (N + 1) * Eent N φ upper n ≤
        indexWeight n ^ (N + 1) * (Eent N φ true n + Eent N φ false n) :=
      mul_le_mul_of_nonneg_left hEu (pow_nonneg hw0.le _)
    unfold tP
    linarith
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hwN : 1 ≤ indexWeight n ^ N := one_le_pow₀ hw1
  have hR4 : R ≤ 1 / 4 := by
    apply (mul_le_mul_iff_of_pos_left (pow_pos hw0 N)).mp
    exact hRw.trans (by linarith only [h5])
  -- the root bound and eps
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have heta : (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) = Complex.exp (Complex.I * ε) := eta_eq θ n
  rw [heta] at hq
  have hq' : (-1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 0 0 -
        KSPSWKB.beta φ (xi n) 0 * r 1 0) * ((Complex.exp (Complex.I * ε) - 1) + 1) ^ 2 +
      (1 + (1 - r 0 0) * (1 - r 1 1) - KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 -
        (KSPSWKB.alpha φ (xi n) 0 - r 1 0) * (KSPSWKB.beta φ (xi n) 0 - r 0 1)) *
          ((Complex.exp (Complex.I * ε) - 1) + 1) +
      (-1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 1 1 -
        KSPSWKB.alpha φ (xi n) 0 * r 0 1) = 0 := by
    rw [sub_add_cancel]
    exact hq
  have hu := quad_root_bound _ _ _ _ _ _ _ R le_rfl hR4 (hα.trans hq4) (hβ.trans hq4) hq'
  have hε : ‖ε‖ ≤ 1 / 2 := by
    have := phase_small φ (xi n) n (indexWeight n) a hw0 hX1 hwX (hxi n)
    have h7 : (a + Jsum φ) / indexWeight n ≤ 1 / 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    unfold Jsum at h7
    rw [hεdef, hθ]
    linarith
  have hεu := eps_le_two_exp ε hε
  have h10 : ‖ε‖ ≤ 10 * R := by linarith
  exact ⟨R, hR0, hR4, hRw, hEw, le_rfl, hα.trans hSw, hβ.trans hSw, hβ.trans hq4, h10, hε, hu, hENT⟩

theorem g02_side_Z_uniform (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ indexWeight n ^ N / 4)
    (T : ℝ) (hT : 0 ≤ T) (htT : tP N φ n ≤ T) (hz : xi n ≠ 0)
    (hq : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) ^ 2 +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
        KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 = 0) :
    indexWeight n ^ (N + 1) *
      ‖(2 * KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 *
          ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))) +
          KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1) +
        2 * Complex.I * (xi n + KSPSRiccati.phasePolynomial φ (N + 1) (xi n)⁻¹ -
          (n : ℂ) * (Real.pi : ℂ))‖ ≤
      (215 * T + 1 + 4 * KSPS016W.Sb φ) * tP N φ n := by
  obtain ⟨R, hR0, hR4, hRw, hEw, hR, hα, hβ, hβ4, h10, hε, hu, hENT⟩ :=
    g02_side_core_uniform N hN φ a ha upper xi hxe hxi n h1 h2 h4 h5 hz hq
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hS0 := KSPS016W.Sb_nonneg φ
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ with hrdef
  set L : ℂ := integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1) with hLdef
  set θ : ℂ := NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n) with hθ
  set ε : ℂ := θ - (n : ℂ) * (Real.pi : ℂ) with hεdef
  have heta : (-1 : ℂ) ^ n * Complex.exp (Complex.I * θ) = Complex.exp (Complex.I * ε) := eta_eq θ n
  rw [heta]
  -- the phase identity g(lam) - n pi = eps + i e1
  have hg : xi n + KSPSRiccati.phasePolynomial φ (N + 1) (xi n)⁻¹ - (n : ℂ) * (Real.pi : ℂ) =
      ε + Complex.I * (((2 * Complex.I * xi n) ^ (N + 1))⁻¹ * integralRiccatiLeft φ (N + 1)) := by
    rw [phase_poly_eq φ (xi n), ← hθ, hεdef]
    ring
  have hgL : 2 * Complex.I * (xi n + KSPSRiccati.phasePolynomial φ (N + 1) (xi n)⁻¹ -
      (n : ℂ) * (Real.pi : ℂ)) = 2 * Complex.I * ε - 2 * L := by
    rw [hg, hLdef, div_eq_mul_inv]
    linear_combination (2 * (((2 * Complex.I * xi n) ^ (N + 1))⁻¹ *
      integralRiccatiLeft φ (N + 1))) * Complex.I_sq
  have hq0 : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 =
      -1 + KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 + r 0 0 -
        KSPSWKB.beta φ (xi n) 0 * r 1 0 := rfl
  have hq1 : KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1 =
      1 + (1 - r 0 0) * (1 - r 1 1) - KSPSWKB.alpha φ (xi n) 0 * KSPSWKB.beta φ (xi n) 0 -
        (KSPSWKB.alpha φ (xi n) 0 - r 1 0) * (KSPSWKB.beta φ (xi n) 0 - r 0 1) := rfl
  rw [hgL, hq0, hq1, Z_alg]
  have hZ := Z_norm (KSPSWKB.alpha φ (xi n) 0) (KSPSWKB.beta φ (xi n) 0) (r 0 0) (r 0 1) (r 1 0) (r 1 1)
    ε L R (KSPS016W.Sb φ) (indexWeight n) (Eent N φ upper n) hw1 hS0 hR hR4
    hα hβ hβ4 h10 (by linarith) hu hENT
  have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  refine (mul_le_mul_of_nonneg_left hZ hwp).trans ?_
  -- weights
  have hRR : indexWeight n ^ (N + 1) * R ^ 2 ≤ T * tP N φ n := by
    have hw2 : indexWeight n ^ (N + 1) ≤ indexWeight n ^ (2 * N) := pow_le_pow_right₀ hw1 (by omega)
    have h6 : indexWeight n ^ (N + 1) * R ^ 2 ≤ (indexWeight n ^ N * R) ^ 2 := by
      have e : (indexWeight n ^ N * R) ^ 2 = indexWeight n ^ (2 * N) * R ^ 2 := by ring
      rw [e]; exact mul_le_mul_of_nonneg_right hw2 (sq_nonneg _)
    have h7 : (indexWeight n ^ N * R) ^ 2 ≤ tP N φ n ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (pow_nonneg hw0.le _) hR0) hRw 2
    have htP0 : 0 ≤ tP N φ n := le_trans (mul_nonneg (pow_nonneg hw0.le _) hR0) hRw
    have h8 : tP N φ n ^ 2 ≤ T * tP N φ n := by
      have h9 := mul_le_mul_of_nonneg_right htT htP0
      simpa only [pow_two] using h9
    exact h6.trans (h7.trans h8)
  have hRl : indexWeight n ^ (N + 1) * (4 * KSPS016W.Sb φ * R / indexWeight n) =
      4 * KSPS016W.Sb φ * (indexWeight n ^ N * R) := by
    rw [pow_succ]; field_simp
  have e : indexWeight n ^ (N + 1) * (215 * R ^ 2 + 4 * KSPS016W.Sb φ * R / indexWeight n +
      Eent N φ upper n) = 215 * (indexWeight n ^ (N + 1) * R ^ 2) +
        indexWeight n ^ (N + 1) * (4 * KSPS016W.Sb φ * R / indexWeight n) +
        indexWeight n ^ (N + 1) * Eent N φ upper n := by ring
  rw [e, hRl]
  have h11 : 4 * KSPS016W.Sb φ * (indexWeight n ^ N * R) ≤ 4 * KSPS016W.Sb φ * tP N φ n :=
    mul_le_mul_of_nonneg_left hRw (by linarith)
  linarith

def g02_Cb (N : ℕ) (φ : SobolevC N) (CT T : ℝ) (n : ℤ) : ℝ :=
  (215*T + 1 + 4*KSPS016W.Sb φ) * tP N φ n + 2*Db N φ CT n

theorem g02_radicand_uniform (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (a : ℝ) (ha : 0 ≤ a)
    (hxp : ∀ n : ℤ, ‖periodicPlus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hxm : ∀ n : ℤ, ‖periodicMinus φ n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (hplus hminus : ℤ → ℂ) (ζ : ℂ → ℂ) (CT : ℝ) (hCT : 0 ≤ CT) (n : ℤ)
    (h1 : ((⌈a⌉₊ + ⌈KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h2 : ((⌈a⌉₊ + ⌈2 * KSPS016W.Sb φ⌉₊ + 1 : ℕ) : ℤ) ≤ |n|)
    (h4 : 2 * (a + Jsum φ) ≤ indexWeight n)
    (h5 : tP N φ n ≤ indexWeight n ^ N / 4)
    (T : ℝ) (hT : 0 ≤ T) (htT : tP N φ n ≤ T)
    (hL : 2 * Lp φ ≤ |(n : ℝ)| ^ 2)
    (hL' : 2 * Lsum φ ≤ |(n : ℝ)| ^ 2)
    (hne : (Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹ ≠ 0)
    (heq : ζ (n : ℂ)⁻¹ + KSPSRiccati.phasePolynomial φ (N + 1)
      ((n : ℂ)⁻¹ / ((Real.pi : ℂ) + (n : ℂ)⁻¹ * ζ (n : ℂ)⁻¹)) = 0)
    (hsmall : ‖ζ (n : ℂ)⁻¹‖ ≤ 1)
    (htay : ‖ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
        KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k‖ ≤ CT * ‖(n : ℂ)⁻¹‖ ^ (N + 2))
    (hqf : KSPSWKB.endpointQuadraticFormula N φ n hplus hminus) :
    ∃ B : ℂ, indexWeight n ^ (N + 1) * ‖B‖ ≤ g02_Cb N φ CT T n ∧
      4 * (((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 -
        physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -hplus n + B ^ 2 - 2 * Complex.I * (periodicPlus φ n - periodicMinus φ n) * B := by
  have hg := KSPS025U5.gap_bound_U N hN φ a ha hxp hxm hplus hminus n h1 h2 h4 hL hqf
  obtain ⟨hp, hm, hqp, -⟩ := hqf
  obtain ⟨-, hqp2, hqp3⟩ := hqp
  have hZ := g02_side_Z_uniform N hN φ a ha true (periodicPlus φ) (fun _ => rfl) hxp n h1 h2 h4 h5 T hT htT hp hqp2
  set Z : ℂ := 2 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 *
      ((-1 : ℂ) ^ n * Complex.exp (Complex.I * NlsGge.ThirdConsultation.KSPS.wkbPhase φ (periodicPlus φ n))) +
      KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1 with hZdef
  have hZsq : Z ^ 2 = -4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n +
      hplus n := (Z_sq _ _ _ _ hqp2).trans hqp3
  -- basic facts
  obtain ⟨hn1R, hνa⟩ := KSPS016W.tail_nat a _ n h1
  have hw1 := KSPS015W.one_le_w n
  have hw0 : 0 < indexWeight n := by linarith
  have hν0 : 0 < |(n : ℝ)| := by linarith
  have hwν : indexWeight n ≤ 2 * |(n : ℝ)| := KSPS015W.w_le_two n hn1R
  have htP0 := tP_nonneg N φ n
  have hnC : (n : ℂ) ≠ 0 := by
    intro h0
    have : (n : ℝ) = 0 := by exact_mod_cast h0
    rw [this, abs_zero] at hn1R
    linarith
  -- the exact germ solution
  set ls : ℂ := (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ with hls
  have hgs := lamStar_eq φ ζ n hnC hne heq
  rw [← hls] at hgs
  have hnpi : ‖(n : ℂ) * (Real.pi : ℂ)‖ = Real.pi * |(n : ℝ)| := by
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]; ring
  have hpi := Real.pi_gt_three
  have h10 : 3 * |(n : ℝ)| ≤ Real.pi * |(n : ℝ)| := mul_le_mul_of_nonneg_right hpi.le (abs_nonneg _)
  have hpν : |(n : ℝ)| ≤ ‖periodicPlus φ n‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) (periodicPlus φ n)
    rw [norm_sub_rev, hnpi] at h7
    have h8 : a / indexWeight n ≤ a := div_le_self ha hw1
    have h9 := hxp n
    linarith
  have hlsν : |(n : ℝ)| ≤ ‖ls‖ := by
    have h7 := norm_sub_norm_le ((n : ℂ) * (Real.pi : ℂ)) ls
    rw [norm_sub_rev, hnpi] at h7
    have h8 : ls - (n : ℂ) * (Real.pi : ℂ) = ζ (n : ℂ)⁻¹ := by rw [hls]; ring
    rw [h8] at h7
    linarith
  have hp0 : periodicPlus φ n ≠ 0 := hp
  have hls0 : ls ≠ 0 := by intro h0; rw [h0, norm_zero] at hlsν; linarith
  have hpi1 : ‖(periodicPlus φ n)⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hlsi : ‖ls⁻¹‖ ≤ 1 := by
    rw [norm_inv]; exact inv_le_one_of_one_le₀ (by linarith)
  have hinv : ‖(periodicPlus φ n)⁻¹ - ls⁻¹‖ ≤ ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    rw [inv_sub_inv hp0 hls0, norm_div, norm_mul, norm_sub_rev]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hν0 2)
    rw [pow_two]
    exact mul_le_mul hpν hlsν hν0.le (norm_nonneg _)
  have hL0 : 0 ≤ Lsum φ := Finset.sum_nonneg (fun k _ => by positivity)
  have hΔp : ‖KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹‖ ≤ Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 := by
    refine (phasePoly_lip φ (N + 1) _ _ hpi1 hlsi).trans ?_
    unfold Lsum
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hinv (Finset.sum_nonneg (fun k _ => by positivity))
  -- D := g(lam+) - n pi - gamma/2 = (tau - ls) + (P(1/lam+) - P(1/ls))
  set γ : ℂ := periodicPlus φ n - periodicMinus φ n with hγdef
  set τ : ℂ := NlsGge.ThirdConsultation.KSPS.midpoint φ n with hτdef
  have hτp : periodicPlus φ n = τ + γ / 2 := by
    rw [hτdef, hγdef]; unfold NlsGge.ThirdConsultation.KSPS.midpoint; ring
  set D : ℂ := periodicPlus φ n + KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      (n : ℂ) * (Real.pi : ℂ) - γ / 2 with hDdef
  have hDe : D = (τ - ls) + (KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ -
      KSPSRiccati.phasePolynomial φ (N + 1) ls⁻¹) := by
    rw [hDdef]
    have := hτp
    linear_combination this + hgs
  have hT0 : ‖ls - spectralPolynomial φ n‖ ≤ CT * (1 / |(n : ℝ)| ^ (N + 2)) := by
    rw [spoly_eq, hls]
    have e : (n : ℂ) * (Real.pi : ℂ) + ζ (n : ℂ)⁻¹ - ((n : ℂ) * (Real.pi : ℂ) +
        ∑ k ∈ Finset.Icc 1 (N + 1), KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k) =
        ζ (n : ℂ)⁻¹ - ∑ k ∈ Finset.Icc 1 (N + 1),
          KSPSRiccati.spectralCoefficient φ k * ((n : ℂ)⁻¹) ^ k := by ring
    rw [e]
    refine htay.trans (le_of_eq ?_)
    rw [norm_inv, Complex.norm_intCast, inv_pow]
    ring
  have hτls : ‖τ - ls‖ ≤ ‖τ - spectralPolynomial φ n‖ + CT * (1 / |(n : ℝ)| ^ (N + 2)) := by
    have e : τ - ls = (τ - spectralPolynomial φ n) - (ls - spectralPolynomial φ n) := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith)
  have hpls : ‖periodicPlus φ n - ls‖ ≤ ‖τ - ls‖ + ‖γ‖ / 2 := by
    rw [hτp]
    have e : τ + γ / 2 - ls = (τ - ls) + γ / 2 := by ring
    rw [e]
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [norm_div, Complex.norm_ofNat]
  have hLn : Lsum φ / |(n : ℝ)| ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (pow_pos hν0 2)]; linarith
  have hDn : ‖D‖ ≤ 3 / 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
    rw [hDe]
    refine (norm_add_le _ _).trans ?_
    have h7 : Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 ≤
        Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
      have e1 : Lsum φ * ‖periodicPlus φ n - ls‖ / |(n : ℝ)| ^ 2 =
          Lsum φ / |(n : ℝ)| ^ 2 * ‖periodicPlus φ n - ls‖ := by ring
      have e2 : Lsum φ / |(n : ℝ)| ^ 2 * (‖τ - ls‖ + ‖γ‖ / 2) =
          Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
        ring
      rw [e1, ← e2]
      exact mul_le_mul_of_nonneg_left hpls (by positivity)
    have h8 : Lsum φ / |(n : ℝ)| ^ 2 * ‖τ - ls‖ ≤ 1 / 2 * ‖τ - ls‖ :=
      mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
    linarith
  -- weighted D
  have hwp : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  have hD : indexWeight n ^ (N + 1) * ‖D‖ ≤ Db N φ CT n := by
    have hr := wpow_ratio N (indexWeight n) |(n : ℝ)| hw1 hn1R hwν
    have hγw : indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) ≤ 80 * Lsum φ * tP N φ n := by
      have hwn2 : indexWeight n ^ 2 ≤ 4 * |(n : ℝ)| ^ 2 :=
        calc indexWeight n ^ 2 ≤ (2 * |(n : ℝ)|) ^ 2 := pow_le_pow_left₀ hw0.le hwν 2
          _ = 4 * |(n : ℝ)| ^ 2 := by ring
      have e : indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) =
          Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * (indexWeight n / |(n : ℝ)| ^ 2) := by
        ring
      have h7 : indexWeight n / |(n : ℝ)| ^ 2 ≤ 4 := by
        rw [div_le_iff₀ (pow_pos hν0 2)]
        have := le_self_pow₀ hw1 (by norm_num : (2 : ℕ) ≠ 0)
        linarith
      rw [e]
      have h8 : 0 ≤ Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) :=
        mul_nonneg (by linarith) (mul_nonneg (pow_nonneg hw0.le _) (norm_nonneg _))
      calc Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * (indexWeight n / |(n : ℝ)| ^ 2)
          ≤ Lsum φ / 2 * (indexWeight n ^ N * ‖γ‖) * 4 := mul_le_mul_of_nonneg_left h7 h8
        _ ≤ Lsum φ / 2 * (40 * tP N φ n) * 4 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by linarith)) (by norm_num)
        _ = 80 * Lsum φ * tP N φ n := by ring
    have hDn' : ‖D‖ ≤ 3 / 2 * (‖τ - spectralPolynomial φ n‖ + CT * (1 / |(n : ℝ)| ^ (N + 2))) +
        Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2) := by
      have := mul_le_mul_of_nonneg_left hτls (by norm_num : (0 : ℝ) ≤ 3 / 2)
      linarith
    have h9 := mul_le_mul_of_nonneg_left hDn' hwp
    have h11 : indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2))) ≤
        CT * 2 ^ (N + 2) * (1 / indexWeight n) := by
      have := mul_le_mul_of_nonneg_left hr hCT
      calc indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2)))
          = CT * (indexWeight n ^ (N + 1) * (1 / |(n : ℝ)| ^ (N + 2))) := by ring
        _ ≤ CT * (2 ^ (N + 2) * (1 / indexWeight n)) := this
        _ = CT * 2 ^ (N + 2) * (1 / indexWeight n) := by ring
    have e : indexWeight n ^ (N + 1) * (3 / 2 * (‖τ - spectralPolynomial φ n‖ +
        CT * (1 / |(n : ℝ)| ^ (N + 2))) + Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) =
        3 / 2 * (indexWeight n ^ (N + 1) * ‖τ - spectralPolynomial φ n‖) +
        3 / 2 * (indexWeight n ^ (N + 1) * (CT * (1 / |(n : ℝ)| ^ (N + 2)))) +
        indexWeight n ^ (N + 1) * (Lsum φ * ‖γ‖ / (2 * |(n : ℝ)| ^ 2)) := by ring
    unfold Db
    rw [← hτdef]
    linarith
  -- B' := Z + i gamma
  have hB : indexWeight n ^ (N + 1) * ‖Z + Complex.I * γ‖ ≤ g02_Cb N φ CT T n := by
    have e : Z + Complex.I * γ = (Z + 2 * Complex.I * (periodicPlus φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ))) -
        2 * Complex.I * D := by rw [hDdef]; ring
    rw [e]
    have h7 := norm_sub_le (Z + 2 * Complex.I * (periodicPlus φ n +
        KSPSRiccati.phasePolynomial φ (N + 1) (periodicPlus φ n)⁻¹ - (n : ℂ) * (Real.pi : ℂ)))
      (2 * Complex.I * D)
    have h8 : ‖2 * Complex.I * D‖ = 2 * ‖D‖ := by
      rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one]
    rw [h8] at h7
    have h9 := mul_le_mul_of_nonneg_left h7 hwp
    rw [mul_add] at h9
    unfold g02_Cb
    linarith
  -- the radicand relation
  set B : ℂ := Z + Complex.I * γ with hBdef
  have hH : 4 * ((γ / 2) ^ 2 - physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -hplus n + B ^ 2 - 2 * Complex.I * γ * B := by
    have hZB : Z = B - Complex.I * γ := by rw [hBdef]; ring
    rw [hZB] at hZsq
    linear_combination (-1 : ℂ) * hZsq + γ ^ 2 * Complex.I_sq
  exact ⟨B, hB, hH⟩
/-- Quantitative radicand majorant; no smallness of t is imposed. -/
def g02_radPolynomial (CI S t : ℝ) : ℝ :=
  4*CI*S*t + ((1+S)^2 + 8 + 8*S^2)*t^2 + 4*(1+S)*t^3 + 4*t^4

theorem g02_rs_real_polynomial (w W0 W1 t CI S Eu R nT nX nAC nP nEE nab ne : ℝ)
    (hw : 1 ≤ w) (hW1 : W1 = W0 * w) (hW1sq : W1 ≤ W0 * W0) (hW0 : 0 ≤ W0) (hS : 0 ≤ S)
    (ht0 : 0 ≤ t) (hR0 : 0 ≤ R) (hEu0 : 0 ≤ Eu)
    (hRw : W0 * R ≤ t) (hEw : W1 * Eu ≤ t) (he : W1 * ne ≤ CI) (hne : 0 ≤ ne)
    (hnT : nT ≤ S / w * R) (hnX : nX ≤ Eu + S / w * R) (hnAC : nAC ≤ Eu + S / w * R)
    (hnP : nP ≤ 2 * R ^ 2) (hnEE : nEE ≤ 2 * Eu ^ 2) (hnab : nab ≤ (S / w) ^ 2)
    (h0T : 0 ≤ nT) (h0X : 0 ≤ nX) (h0AC : 0 ≤ nAC) (h0P : 0 ≤ nP) (h0ab : 0 ≤ nab) :
    W1 ^ 2 * (4 * (ne * nT) + nX * nX + 4 * nEE + 4 * (nab * nP) + 2 * (nAC * nP) + nP * nP) ≤
      g02_radPolynomial CI S t := by
  have hw0 : 0 < w := by linarith
  have hW1p : 0 ≤ W1 := by rw [hW1]; exact mul_nonneg hW0 hw0.le
  have wSR : W1 * (S / w * R) = S * (W0 * R) := by rw [hW1]; field_simp
  have hSR : S * (W0 * R) ≤ S * t := mul_le_mul_of_nonneg_left hRw hS
  have wT : W1 * nT ≤ S * t := by
    have := mul_le_mul_of_nonneg_left hnT hW1p
    linarith
  have wX : W1 * nX ≤ (1 + S) * t := by
    have h1 := mul_le_mul_of_nonneg_left hnX hW1p
    rw [mul_add, wSR] at h1
    linarith
  have wAC : W1 * nAC ≤ (1 + S) * t := by
    have h1 := mul_le_mul_of_nonneg_left hnAC hW1p
    rw [mul_add, wSR] at h1
    linarith
  have hW0R : 0 ≤ W0 * R := mul_nonneg hW0 hR0
  have wRR : W0 * W0 * R ^ 2 ≤ t ^ 2 := by
    have h3 : (W0 * R) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hW0R hRw 2
    have h2 : W0 * W0 * R ^ 2 = (W0 * R) ^ 2 := by ring
    linarith
  have wP : W1 * nP ≤ 2 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hnP hW1p
    have h2 : W1 * R ^ 2 ≤ W0 * W0 * R ^ 2 := mul_le_mul_of_nonneg_right hW1sq (sq_nonneg _)
    linarith
  have wP0 : 0 ≤ W1 * nP := mul_nonneg hW1p h0P
  have t1 : W1 ^ 2 * (4 * (ne * nT)) ≤ 4 * CI * S * t := by
    have e1 : W1 ^ 2 * (4 * (ne * nT)) = 4 * ((W1 * ne) * (W1 * nT)) := by ring
    rw [e1]
    have h3 := mul_le_mul he wT (mul_nonneg hW1p h0T) (le_trans (mul_nonneg hW1p hne) he)
    have e2 : CI * (S * t) = CI * S * t := by ring
    linarith
  have t2 : W1 ^ 2 * (nX * nX) ≤ (1 + S) ^ 2 * t ^ 2 := by
    have e1 : W1 ^ 2 * (nX * nX) = (W1 * nX) ^ 2 := by ring
    rw [e1]
    have h := pow_le_pow_left₀ (mul_nonneg hW1p h0X) wX 2
    have e2 : ((1 + S) * t) ^ 2 = (1 + S) ^ 2 * t ^ 2 := by ring
    rw [e2] at h
    exact h
  have t3 : W1 ^ 2 * (4 * nEE) ≤ 8 * t ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hnEE (sq_nonneg W1)
    have h2 : W1 ^ 2 * Eu ^ 2 ≤ t ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hW1p hEu0) hEw 2
    have e1 : W1 ^ 2 * (4 * nEE) = 4 * (W1 ^ 2 * nEE) := by ring
    have e2 : W1 ^ 2 * (2 * Eu ^ 2) = 2 * (W1 ^ 2 * Eu ^ 2) := by ring
    linarith
  have t4 : W1 ^ 2 * (4 * (nab * nP)) ≤ 8 * S ^ 2 * t ^ 2 := by
    have h1 : W1 ^ 2 * (S / w) ^ 2 = S ^ 2 * W0 ^ 2 := by rw [hW1]; field_simp
    have h2 : W0 ^ 2 * nP ≤ 2 * t ^ 2 := by
      have := mul_le_mul_of_nonneg_left hnP (sq_nonneg W0)
      have h3 : W0 ^ 2 * (2 * R ^ 2) = 2 * (W0 * W0 * R ^ 2) := by ring
      linarith
    have h5 : nab * nP ≤ (S / w) ^ 2 * nP := mul_le_mul_of_nonneg_right hnab h0P
    have h6 : W1 ^ 2 * (4 * (nab * nP)) ≤ W1 ^ 2 * (4 * ((S / w) ^ 2 * nP)) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have h7 : W1 ^ 2 * (4 * ((S / w) ^ 2 * nP)) = 4 * S ^ 2 * (W0 ^ 2 * nP) := by
      calc W1 ^ 2 * (4 * ((S / w) ^ 2 * nP)) = 4 * (W1 ^ 2 * (S / w) ^ 2) * nP := by ring
        _ = 4 * (S ^ 2 * W0 ^ 2) * nP := by rw [h1]
        _ = 4 * S ^ 2 * (W0 ^ 2 * nP) := by ring
    have h8 : 4 * S ^ 2 * (W0 ^ 2 * nP) ≤ 4 * S ^ 2 * (2 * t ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have t5 : W1 ^ 2 * (2 * (nAC * nP)) ≤ 4 * (1 + S) * t ^ 3 := by
    have e1 : W1 ^ 2 * (2 * (nAC * nP)) = 2 * ((W1 * nAC) * (W1 * nP)) := by ring
    rw [e1]
    have h1 := mul_le_mul wAC wP wP0 (by positivity)
    have e2 : (1 + S) * t * (2 * t ^ 2) = 2 * (1 + S) * t ^ 3 := by ring
    linarith
  have t6 : W1 ^ 2 * (nP * nP) ≤ 4 * t ^ 4 := by
    have e1 : W1 ^ 2 * (nP * nP) = (W1 * nP) ^ 2 := by ring
    rw [e1]
    have h1 := pow_le_pow_left₀ wP0 wP 2
    have e2 : (2 * t ^ 2) ^ 2 = 4 * t ^ 4 := by ring
    linarith
  have e3 : W1 ^ 2 * (4 * (ne * nT) + nX * nX + 4 * nEE + 4 * (nab * nP) + 2 * (nAC * nP) + nP * nP) =
      W1 ^ 2 * (4 * (ne * nT)) + W1 ^ 2 * (nX * nX) + W1 ^ 2 * (4 * nEE) + W1 ^ 2 * (4 * (nab * nP)) +
        W1 ^ 2 * (2 * (nAC * nP)) + W1 ^ 2 * (nP * nP) := by ring
  rw [e3]
  unfold g02_radPolynomial
  linarith only [t1, t2, t3, t4, t5, t6]

theorem g02_rad_split_polynomial (N : ℕ) (hN : 1 ≤ N) (w : ℝ) (hw : 1 ≤ w) (e a1 a2 E00 E01 E10 E11 α β : ℂ)
    (R S t CI Eu : ℝ) (hS : 0 ≤ S) (ht0 : 0 ≤ t)
    (hR : ‖e + E00‖ + ‖Complex.I * a1 + E01‖ + ‖-Complex.I * a2 + E10‖ + ‖-e + E11‖ ≤ R)
    (hRw : w ^ N * R ≤ t)
    (hEu : ‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖ ≤ Eu) (hEw : w ^ (N + 1) * Eu ≤ t)
    (he : w ^ (N + 1) * ‖e‖ ≤ CI) (hα : ‖α‖ ≤ S / w) (hβ : ‖β‖ ≤ S / w) :
    (w ^ (N + 1)) ^ 2 *
      ‖(4 * (e * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
          (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
        4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
        4 * ((α * β) * ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
        2 * (((e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01))) *
          ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
        ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
          ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
        4 * (-Complex.I * (a1 * E10) + Complex.I * (a2 * E01))‖ ≤
      g02_radPolynomial CI S t := by
  obtain ⟨nT, nX, nAC, nP, nEE, nab⟩ := rs_norms w hw e a1 a2 E00 E01 E10 E11 α β R S Eu hS hR hEu hα hβ
  generalize hT : α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10) = T at nT
  generalize hX : E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01) = X at nX
  generalize hAC : (e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01)) = AC at nAC
  generalize hP : (e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10) = P at nP
  have eq : (4 * (e * T) + X * X +
        4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
        4 * ((α * β) * P) - 2 * (AC * P) + P * P) -
        4 * (-Complex.I * (a1 * E10) + Complex.I * (a2 * E01)) =
      4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P) - 2 * (AC * P) + P * P := by ring
  rw [eq]
  have hsum : ‖4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P) - 2 * (AC * P) + P * P‖ ≤
      4 * (‖e‖ * ‖T‖) + ‖X‖ * ‖X‖ + 4 * ‖E00 * E11 - E01 * E10‖ + 4 * (‖α‖ * ‖β‖ * ‖P‖) +
        2 * (‖AC‖ * ‖P‖) + ‖P‖ * ‖P‖ := by
    have s1 := norm_add_le (4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P) -
      2 * (AC * P)) (P * P)
    have s2 := norm_sub_le (4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10) - 4 * ((α * β) * P))
      (2 * (AC * P))
    have s3 := norm_sub_le (4 * (e * T) + X * X + 4 * (E00 * E11 - E01 * E10)) (4 * ((α * β) * P))
    have s4 := norm_add_le (4 * (e * T) + X * X) (4 * (E00 * E11 - E01 * E10))
    have s5 := norm_add_le (4 * (e * T)) (X * X)
    simp only [norm_mul, Complex.norm_ofNat] at s1 s2 s3 s4 s5
    linarith
  have hw0 : 0 < w := by linarith
  have hW1sq : w ^ (N + 1) ≤ w ^ N * w ^ N := by
    rw [← pow_add]; exact pow_le_pow_right₀ hw (by omega)
  have hR0 : 0 ≤ R := le_trans (by positivity) hR
  have hEu0 : 0 ≤ Eu := le_trans (by positivity) hEu
  have key := g02_rs_real_polynomial w (w ^ N) (w ^ (N + 1)) t CI S Eu R ‖T‖ ‖X‖ ‖AC‖ ‖P‖ ‖E00 * E11 - E01 * E10‖
    (‖α‖ * ‖β‖) ‖e‖ hw (pow_succ w N) hW1sq (pow_nonneg hw0.le N) hS ht0 hR0 hEu0 hRw hEw he
    (norm_nonneg _) nT nX nAC nP nEE nab (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg _)).trans key

theorem g02_tail_halfGap_bound (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (n : ℤ) (hp : periodicPlus φ n ≠ 0)
    (h : ℂ) (B : ℂ) (R S t c : ℝ) (hS0 : 0 ≤ S) (htP0 : 0 ≤ t) (hCb0 : 0 ≤ c)
    (hw1 : 1 ≤ indexWeight n) (hwX : indexWeight n ≤ 2 * ‖periodicPlus φ n‖)
    (hqp3 : (KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1) ^ 2 -
      4 * KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 *
        KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 2 =
      -4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n + h)
    (hR : ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 0 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 0 1‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 1 0‖ +
        ‖KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ 1 1‖ ≤ R)
    (hRw : indexWeight n ^ N * R ≤ t)
    (hEw : indexWeight n ^ (N + 1) * (‖KSPSWKB.endpointEntryError N φ true 0 0 n‖ +
        ‖KSPSWKB.endpointEntryError N φ true 0 1 n‖ + ‖KSPSWKB.endpointEntryError N φ true 1 0 n‖ +
        ‖KSPSWKB.endpointEntryError N φ true 1 1 n‖) ≤ t)
    (hα : ‖KSPSWKB.alpha φ (periodicPlus φ n) 0‖ ≤ S / indexWeight n)
    (hβ : ‖KSPSWKB.beta φ (periodicPlus φ n) 0‖ ≤ S / indexWeight n)
    (hB : indexWeight n ^ (N + 1) * ‖B‖ ≤ c)
    (hH : 4 * (((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 -
        physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n) =
      -h + B ^ 2 - 2 * Complex.I * (periodicPlus φ n - periodicMinus φ n) * B)
    (hre : ∃ U L : ℝ, L ≤ U ∧ periodicPlus φ n = (U : ℂ) ∧ periodicMinus φ n = (L : ℂ))
    (hst : physicalFourier (toPotPair φ).2 n = star (physicalFourier (toPotPair φ).1 (-n))) :
    indexWeight n ^ (N + 1) *
      |((periodicPlus φ n - periodicMinus φ n)/2).re -
        ‖physicalFourier (toPotPair φ).1 (-n)‖| ≤
      2*(t+c) + Real.sqrt ((g02_radPolynomial ‖integralRiccatiLeft φ (N+1)‖ S t + c^2)/2) := by
  have hw0 : 0 < indexWeight n := by linarith
  -- entries at lam+
  set r := KSPSWKB.scaledEndpointCorrection N φ n ⟨periodicPlus φ n, hp⟩ with hrdef
  set IL : ℂ := integralRiccatiLeft φ (N + 1) with hILdef
  set Y : ℂ := (2 * Complex.I * periodicPlus φ n) ^ (N + 1) with hYdef
  set a1 : ℂ := physicalFourier (toPotPair φ).1 (-n) with ha1
  set a2 : ℂ := physicalFourier (toPotPair φ).2 n with ha2
  set E00 := KSPSWKB.endpointEntryError N φ true 0 0 n with hE00
  set E01 := KSPSWKB.endpointEntryError N φ true 0 1 n with hE01
  set E10 := KSPSWKB.endpointEntryError N φ true 1 0 n with hE10
  set E11 := KSPSWKB.endpointEntryError N φ true 1 1 n with hE11
  set α := KSPSWKB.alpha φ (periodicPlus φ n) 0 with hαdef
  set β := KSPSWKB.beta φ (periodicPlus φ n) 0 with hβdef
  have q00 : E00 = r 0 0 - IL / Y :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 0 0 n hp
  have q01 : E01 = r 0 1 - Complex.I * a1 :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 0 1 n hp
  have q10 : E10 = r 1 0 - -Complex.I * a2 :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 1 0 n hp
  have q11 : E11 = r 1 1 - -IL / Y :=
    entryError_eq' φ true (periodicPlus φ) (fun _ => rfl) 1 1 n hp
  have hr00 : r 0 0 = IL / Y + E00 := by rw [q00]; ring
  have hr01 : r 0 1 = Complex.I * a1 + E01 := by rw [q01]; ring
  have hr10 : r 1 0 = -Complex.I * a2 + E10 := by rw [q10]; ring
  have hr11 : r 1 1 = -(IL / Y) + E11 := by rw [q11]; ring
  -- the radicand at lam+ in entry form
  have hq0 : KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 0 =
      -1 + α * β + r 0 0 - β * r 1 0 := rfl
  have hq1 : KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 1 =
      1 + (1 - r 0 0) * (1 - r 1 1) - α * β - (α - r 1 0) * (β - r 0 1) := rfl
  have hq2 : KSPSWKB.endpointQuadraticABC N φ n ⟨periodicPlus φ n, hp⟩ 2 =
      -1 + α * β + r 1 1 - α * r 0 1 := rfl
  have hq3 := hqp3
  rw [hq0, hq1, hq2, hr00, hr01, hr10, hr11] at hq3
  have key := rad_identity' (IL / Y) a1 a2 E00 E01 E10 E11 α β
  have hh : h = 4 * ((IL / Y) * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
      (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
      4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
      4 * ((α * β) * ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
      2 * (((IL / Y + E00) - β * (-Complex.I * a2 + E10) + ((-(IL / Y) + E11) - α * (Complex.I * a1 + E01))) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
      ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) := by
    linear_combination key - hq3
  -- the sharper radicand estimate
  rw [hr00, hr01, hr10, hr11] at hR
  have he : indexWeight n ^ (N + 1) * ‖IL / Y‖ ≤ ‖IL‖ := by
    rw [hYdef]; exact e_bound N IL (periodicPlus φ n) (indexWeight n) hw0 hwX
  have hsplit := g02_rad_split_polynomial N hN (indexWeight n) hw1 (IL / Y) a1 a2 E00 E01 E10 E11 α β R
    S t ‖IL‖ (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) hS0 htP0 hR hRw le_rfl hEw he hα hβ
  set RHS : ℂ := 4 * ((IL / Y) * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
      (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
      4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
      4 * ((α * β) * ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
      2 * (((IL / Y + E00) - β * (-Complex.I * a2 + E10) + ((-(IL / Y) + E11) - α * (Complex.I * a1 + E01))) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
      ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
        ((IL / Y + E00) * (-(IL / Y) + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) with hRHS
  -- real-type facts
  obtain ⟨U, L, hLU, hPU, hML⟩ := hre
  have ha2n : ‖a2‖ = ‖a1‖ := by rw [hst, norm_star]
  have hP : a1 * a2 = ((‖a1‖ ^ 2 : ℝ) : ℂ) := by
    rw [hst, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  set s : ℝ := ‖a1‖ with hsdef
  have hs0 : 0 ≤ s := norm_nonneg _
  set x : ℝ := (U - L) / 2 with hxdef
  have hx0 : 0 ≤ x := by rw [hxdef]; linarith
  have hγ : periodicPlus φ n - periodicMinus φ n = ((2 * x : ℝ) : ℂ) := by
    rw [hPU, hML, hxdef]; push_cast; ring
  have hHx : ((periodicPlus φ n - periodicMinus φ n) / 2) ^ 2 - a1 * a2 = ((x ^ 2 - s ^ 2 : ℝ) : ℂ) := by
    rw [hγ, hP]; push_cast; ring
  rw [hHx, hγ, hh] at hH
  -- |x^2 - s^2| <= Hg + (x + s) K
  set bad : ℂ := 4 * (-Complex.I * (a1 * E10) + Complex.I * (a2 * E01)) with hbad
  have hbadn : ‖bad‖ ≤ 4 * (s * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖)) := by
    rw [hbad, norm_mul, Complex.norm_ofNat]
    have h7 := norm_add_le (-Complex.I * (a1 * E10)) (Complex.I * (a2 * E01))
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul] at h7
    rw [ha2n] at h7
    have h8 : s * ‖E10‖ + s * ‖E01‖ ≤ s * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) := by
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ hs0
      linarith [norm_nonneg E00, norm_nonneg E11]
    have e9 : ‖a1‖ = s := rfl
    rw [e9] at h7
    linarith
  have hxs : |x ^ 2 - s ^ 2| ≤ (‖RHS - bad‖ + ‖B‖ ^ 2) / 4 + (x + s) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) := by
    have h7 : (4 : ℝ) * |x ^ 2 - s ^ 2| = ‖-RHS + B ^ 2 - 2 * Complex.I * ((2 * x : ℝ) : ℂ) * B‖ := by
      rw [← hH, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
    have h8 : -RHS + B ^ 2 - 2 * Complex.I * ((2 * x : ℝ) : ℂ) * B =
        -(RHS - bad) - bad + B ^ 2 - 2 * Complex.I * ((2 * x : ℝ) : ℂ) * B := by ring
    have h9 : ‖2 * Complex.I * ((2 * x : ℝ) : ℂ) * B‖ = 4 * x * ‖B‖ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * x)]
      ring
    have s1 := norm_sub_le (-(RHS - bad) - bad + B ^ 2) (2 * Complex.I * ((2 * x : ℝ) : ℂ) * B)
    have s2 := norm_add_le (-(RHS - bad) - bad) (B ^ 2)
    have s3 := norm_sub_le (-(RHS - bad)) bad
    rw [norm_neg] at s3
    rw [norm_pow] at s2
    rw [h9] at s1
    rw [h8] at h7
    have hEnt0 : 0 ≤ (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) := by positivity
    have h10 : s * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) ≤ (x + s) * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) :=
      mul_le_mul_of_nonneg_right (by linarith) hEnt0
    have h11 : x * ‖B‖ ≤ (x + s) * ‖B‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have e1 : (x + s) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) = (x + s) * (‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + (x + s) * ‖B‖ := by ring
    linarith
  have hd := d_bound x s ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4) ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) hx0 hs0
    (by positivity) (by positivity) hxs
  -- weighted
  have hW1 : 0 ≤ indexWeight n ^ (N + 1) := pow_nonneg hw0.le _
  have hK : indexWeight n ^ (N + 1) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) ≤ t + c := by
    rw [mul_add]; linarith
  have hHg : indexWeight n ^ (N + 1) * Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) ≤
      Real.sqrt ((g02_radPolynomial ‖integralRiccatiLeft φ (N+1)‖ S t + c ^ 2) / 2) := by
    have e1 : indexWeight n ^ (N + 1) * Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) =
        Real.sqrt ((indexWeight n ^ (N + 1)) ^ 2 * (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4))) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW1]
    rw [e1]
    apply Real.sqrt_le_sqrt
    have h7 : (indexWeight n ^ (N + 1) * ‖B‖) ^ 2 ≤ c ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hW1 (norm_nonneg _)) hB 2
    have h8 : (indexWeight n ^ (N + 1)) ^ 2 * ‖RHS - bad‖ ≤ g02_radPolynomial ‖integralRiccatiLeft φ (N+1)‖ S t := by
      exact hsplit
    have e2 : (indexWeight n ^ (N + 1)) ^ 2 * (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) =
        ((indexWeight n ^ (N + 1)) ^ 2 * ‖RHS - bad‖ + (indexWeight n ^ (N + 1) * ‖B‖) ^ 2) / 2 := by ring
    rw [e2]
    linarith
  have hwd : indexWeight n ^ (N + 1) * |x - s| ≤ 2 * (t + c) +
      Real.sqrt ((g02_radPolynomial ‖integralRiccatiLeft φ (N+1)‖ S t + c ^ 2) / 2) := by
    have h7 := mul_le_mul_of_nonneg_left hd hW1
    have e1 : indexWeight n ^ (N + 1) * (2 * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖) +
        Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4))) =
        2 * (indexWeight n ^ (N + 1) * ((‖E00‖ + ‖E01‖ + ‖E10‖ + ‖E11‖) + ‖B‖)) +
        indexWeight n ^ (N + 1) * Real.sqrt (2 * ((‖RHS - bad‖ + ‖B‖ ^ 2) / 4)) := by ring
    rw [e1] at h7
    linarith
  have hx : ((periodicPlus φ n - periodicMinus φ n)/2).re = x := by
    simpa only [hPU, hML, Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re] using hxdef.symm
  simpa only [hx, ha1, hsdef] using hwd


/-- Finite weighted endpoint-error bounds give a uniform tP bound, not a small tP tail. -/
theorem g02_tP_uniform (B : ℝ) (hB : 0 ≤ B) :
    ∃ M : ℕ, ∃ T : ℝ, 1 ≤ M ∧ 1 ≤ T ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
        (∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
          ∑ n ∈ F, tP 1 φ n ^ 2 ≤ T) ∧
        (∀ n : ℤ, (M : ℤ) ≤ |n| → tP 1 φ n ≤ T) := by
  obtain ⟨M26, CE, h26⟩ := KSPS025U15.h26_uniform 1 le_rfl B hB
  obtain ⟨L, hL, hLb⟩ := KSPS025U5.riccati_consts_uniform 1 le_rfl B hB
  have hSi := KSPS016W.sq_summable_inv_w
  let S : ℝ := ∑' n : ℤ, (1 / indexWeight n)^2
  have hS : 0 ≤ S := tsum_nonneg (fun _ => sq_nonneg _)
  let M : ℕ := M26 + 1
  let T : ℝ := 1 + 4*(64*|CE| + (2*Real.pi)^2*B^2 + 4*L^2*S)
  have hT : 1 ≤ T := by
    have hp : 0 ≤ 4*(64*|CE| + (2*Real.pi)^2*B^2 + 4*L^2*S) := by positivity
    dsimp only [T]
    linarith only [hp]
  refine ⟨M, T, by dsimp only [M]; omega, hT, ?_⟩
  intro φ hφ
  have hsum (F : Finset ℤ) (hF : ∀ n ∈ F, (M : ℤ) ≤ |n|) :
      ∑ n ∈ F, tP 1 φ n^2 ≤ T := by
    have hF1 : ∀ n ∈ F, (1 : ℝ) ≤ |(n : ℝ)| := by
      intro n hn
      have h1M : (1 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (show 1 ≤ M by dsimp only [M]; omega)
      have hi : (1 : ℤ) ≤ |n| := h1M.trans (hF n hn)
      have hr := (Int.cast_le (R := ℝ)).2 hi
      simpa only [Int.cast_abs, Int.cast_one] using hr
    have hMM : (M26 : ℤ) ≤ (M : ℤ) := by exact_mod_cast (show M26 ≤ M by dsimp only [M]; omega)
    have hEs : ∀ (u : Bool) (i j : Fin 2),
        ∑ n ∈ F, (indexWeight n^2 * ‖KSPSWKB.endpointEntryError 1 φ u i j n‖)^2 ≤ |CE| := by
      intro u i j
      exact ((h26 φ hφ).1 u i j F (fun n hn =>
        hMM.trans (hF n hn))).trans (le_abs_self _)
    have h := KSPS025U7.tP_sum_le 1 φ F hF1 |CE| L (hLb φ hφ).2.2.2 hEs
    have hsq : sobolevNorm 1 φ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (show 0 ≤ sobolevNorm 1 φ from Real.sqrt_nonneg _) hφ 2
    have hp := mul_le_mul_of_nonneg_left hsq (sq_nonneg (2*Real.pi))
    change ∑ n ∈ F, tP 1 φ n^2 ≤
      4*(64*|CE| + (2*Real.pi)^2*sobolevNorm 1 φ^2 + 4*L^2*S) at h
    dsimp only [T]
    linarith only [h, hp]
  refine ⟨hsum, ?_⟩
  intro n hn
  have hs := hsum {n} (by intro m hm; simpa only [Finset.mem_singleton.mp hm] using hn)
  rw [Finset.sum_singleton] at hs
  have ht0 := tP_nonneg 1 φ n
  nlinarith only [hs, ht0, hT]

/-- A polynomial radicand bound becomes linear in t under a uniform upper bound. -/
theorem g02_radPolynomial_le (CI S t L SB T : ℝ)
    (hCI : 0 ≤ CI) (hS : 0 ≤ S) (ht : 0 ≤ t)
    (hIL : CI ≤ L) (hSB : S ≤ SB) (htT : t ≤ T) :
    g02_radPolynomial CI S t ≤
      (4*L*SB + ((1+SB)^2+8+8*SB^2)*T + 4*(1+SB)*T^2 + 4*T^3)*t := by
  have hL : 0 ≤ L := hCI.trans hIL
  have hSB0 : 0 ≤ SB := hS.trans hSB
  have hT : 0 ≤ T := ht.trans htT
  have hmono : g02_radPolynomial CI S t ≤ g02_radPolynomial L SB t := by
    unfold g02_radPolynomial
    gcongr
  have h2 : t^2 ≤ T*t := by simpa only [pow_two] using mul_le_mul_of_nonneg_right htT ht
  have h3 : t^3 ≤ T^2*t := by
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htT 2) ht
    simpa only [pow_succ] using h
  have h4 : t^4 ≤ T^3*t := by
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htT 3) ht
    simpa only [pow_succ] using h
  have p2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (1+SB)^2+8+8*SB^2 by positivity)
  have p3 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 4*(1+SB) by positivity)
  have p4 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 4)
  apply hmono.trans
  unfold g02_radPolynomial
  linarith only [p2, p3, p4]

/-- Fourth-power majorization of the real square-root cancellation bound. -/
theorem g02_real_fourth_bound (x t c D T U : ℝ)
    (hx : 0 ≤ x) (ht : 0 ≤ t) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (ht2 : t^2 ≤ T) (hc2 : c^2 ≤ U)
    (h : x ≤ 2*(t+c) + Real.sqrt ((D*t+c^2)/2)) :
    x^4 ≤ 27*((16*T+D^2)*t^2 + 17*U*c^2) := by
  let q : ℝ := Real.sqrt ((D*t+c^2)/2)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2 = (D*t+c^2)/2 := Real.sq_sqrt (by positivity)
  have hq4 : q^4 ≤ D^2*t^2+c^4 := by
    have he : q^4 = (q^2)^2 := by ring
    rw [he, hq2]
    nlinarith only [sq_nonneg (D*t-c^2)]
  have ht4 : t^4 ≤ T*t^2 := by
    have h := mul_le_mul_of_nonneg_right ht2 (sq_nonneg t)
    nlinarith only [h]
  have hc4 : c^4 ≤ U*c^2 := by
    have h := mul_le_mul_of_nonneg_right hc2 (sq_nonneg c)
    nlinarith only [h]
  have hpow := pow_le_pow_left₀ hx h 4
  have hsum := KSPS028P.pow4_sum_le (2*t) (2*c) q (by positivity) (by positivity) hq
  have he : 2*(t+c)+q = 2*t+2*c+q := by ring
  change x^4 ≤ (2*(t+c)+q)^4 at hpow
  rw [he] at hpow
  nlinarith only [hpow.trans hsum, hq4, ht4, hc4]

/-- Nonnegative majorants of the new completed-square correction. -/
theorem g02_Cb_nonneg (N : ℕ) (φ : SobolevC N) (CT T : ℝ)
    (hCT : 0 ≤ CT) (hT : 0 ≤ T) (n : ℤ) : 0 ≤ g02_Cb N φ CT T n := by
  have ht := tP_nonneg N φ n
  have hS := KSPS016W.Sb_nonneg φ
  have hL : 0 ≤ Lsum φ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hw : 0 ≤ indexWeight n := le_trans zero_le_one (KSPS015W.one_le_w n)
  unfold g02_Cb Db
  positivity

/-- Uniform fourth-power bound for the real half-gap correction on completed physical H1 pairs. -/
theorem g02_halfGap_uniform_sobolev (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
      MRiccati.RealPair φ → ∀ F : Finset ℤ,
        ∑ n ∈ F, |g02_halfGap φ n|^4 ≤ C := by
  obtain ⟨Mt, T, hMt, hT1, ht⟩ := g02_tP_uniform B hB
  have hT : 0 ≤ T := le_trans zero_le_one hT1
  obtain ⟨M26, CE, h26⟩ := KSPS025U15.h26_uniform 1 le_rfl B hB
  obtain ⟨a, ha, hloc⟩ := KSPS025U4.periodic_loc_uniform 1 le_rfl B hB
  obtain ⟨L, hL, hLb⟩ := KSPS025U5.riccati_consts_uniform 1 le_rfl B hB
  obtain ⟨CM, hCM, hmid⟩ := KSPS.midpoint_spectral_expansion_uniform 1 le_rfl B hB
  obtain ⟨r0, hr0, CT, hCT, hgerm⟩ := KSPS025U9.germ_uniform 1 le_rfl B hB
  let SB := KSPS025U5.SbB 1 B
  have hSB : 0 ≤ SB := KSPS025U5.SbB_nonneg 1 B
  have hSi := KSPS016W.sq_summable_inv_w
  let SI : ℝ := ∑' n : ℤ, (1/indexWeight n)^2
  have hSI : 0 ≤ SI := tsum_nonneg (fun _ => sq_nonneg _)
  let K : ℝ := 215*T+1+4*SB+160*L
  let J : ℝ := 24*CT
  let U : ℝ := 4*(K^2*T+9*CM^2+J^2*SI)
  let D : ℝ := 4*L*SB+((1+SB)^2+8+8*SB^2)*T+4*(1+SB)*T^2+4*T^3
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  let M : ℕ := Mt+M26+⌈a⌉₊+⌈KSPSVolterra.threshold 1 B⌉₊+⌈2*SB⌉₊+
    ⌈2*(a+L)⌉₊+⌈2*L⌉₊+⌈4*T⌉₊+⌈1/r0⌉₊+2
  let KL : ℝ := (1+(M : ℝ))^2*(a+B)
  let CL : ℝ := ((Finset.Icc (-(M : ℤ)) M).card : ℝ)*KL^4
  let CH : ℝ := 27*((16*T+D^2)*T+17*U*U)
  refine ⟨CH+CL, by dsimp only [CH, CL]; positivity, ?_⟩
  intro φ hφ hreal F
  have hSφ := KSPS025U5.Sb_le 1 B φ hφ
  change KSPS016W.Sb φ ≤ SB at hSφ
  obtain ⟨hJφ, hLp, hLs, hIL⟩ := hLb φ hφ
  obtain ⟨hEs, hplus, hminus, hquad⟩ := h26 φ hφ
  obtain ⟨ζ, hζ⟩ := hgerm φ hφ
  obtain ⟨hre, hstar⟩ := KSPS028Q.real_facts φ hreal
  let A : ℤ → ℝ := fun n => indexWeight n^2*‖KSPS.midpoint φ n-spectralPolynomial φ n‖
  let c : ℤ → ℝ := fun n => g02_Cb 1 φ CT T n
  have hc0 : ∀ n, 0 ≤ c n := g02_Cb_nonneg 1 φ CT T hCT hT
  have hA0 : ∀ n, 0 ≤ A n := fun n => mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have hc_bound (n : ℤ) : c n ≤ K*tP 1 φ n+3*A n+J*(1/indexWeight n) := by
    have ht0 := tP_nonneg 1 φ n
    have hS := mul_le_mul_of_nonneg_right hSφ (show 0 ≤ 4*tP 1 φ n by positivity)
    have hLs' := mul_le_mul_of_nonneg_right hLs (show 0 ≤ 160*tP 1 φ n by positivity)
    dsimp only [c, g02_Cb, Db, K, J, A]
    norm_num only [Nat.add_one, pow_succ, pow_zero, mul_one]
    nlinarith only [hS, hLs']
  have htail_t (G : Finset ℤ) (hG : ∀ n ∈ G, (M : ℤ) ≤ |n|) :
      ∑ n ∈ G, tP 1 φ n^2 ≤ T := by
    apply (ht φ hφ).1
    intro n hn
    have hMtM : (Mt : ℤ) ≤ (M : ℤ) := by exact_mod_cast (show Mt ≤ M by dsimp only [M]; omega)
    exact hMtM.trans (hG n hn)
  have hc_sum (G : Finset ℤ) (hG : ∀ n ∈ G, (M : ℤ) ≤ |n|) :
      ∑ n ∈ G, c n^2 ≤ U := by
    have hp (n : ℤ) : c n^2 ≤ 4*(K^2*tP 1 φ n^2+9*(A n)^2+J^2*(1/indexWeight n)^2) := by
      have h := pow_le_pow_left₀ (hc0 n) (hc_bound n) 2
      have hs := KSPS025U7.sq_add4_le (K*tP 1 φ n) (3*A n) (J*(1/indexWeight n)) 0
      nlinarith only [h, hs]
    have hS := Finset.sum_le_sum (fun n (_ : n ∈ G) => hp n)
    have hAM := (hmid φ hφ).2 G
    have hInv : ∑ n ∈ G, (1/indexWeight n)^2 ≤ SI :=
      hSi.sum_le_tsum G (fun _ _ => sq_nonneg _)
    have htp := htail_t G hG
    have h1 := mul_le_mul_of_nonneg_left htp (sq_nonneg K)
    have h2 := mul_le_mul_of_nonneg_left hAM (by norm_num : (0 : ℝ) ≤ 9)
    have h3 := mul_le_mul_of_nonneg_left hInv (sq_nonneg J)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hS
    change ∑ n ∈ G, c n^2 ≤ 4*(K^2*T+9*CM^2+J^2*SI)
    change ∑ n ∈ G, A n^2 ≤ CM^2 at hAM
    linarith only [hS, h1, h2, h3]
  have htail (n : ℤ) (hn : (M : ℤ) ≤ |n|) :
      |g02_halfGap φ n|^4 ≤ 27*((16*T+D^2)*tP 1 φ n^2+17*U*c n^2) := by
    have hcast (m : ℕ) (hm : m ≤ M) : (m : ℤ) ≤ |n| := by
      have hmM : (m : ℤ) ≤ (M : ℤ) := by exact_mod_cast hm
      exact hmM.trans hn
    have hnR : (M : ℝ) ≤ |(n : ℝ)| := by
      have h := (Int.cast_le (R := ℝ)).2 hn
      simpa only [Int.cast_abs, Int.cast_natCast] using h
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show 1 ≤ M by dsimp only [M]; omega)
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := hM1.trans hnR
    have hn0 : 0 < |(n : ℝ)| := lt_of_lt_of_le zero_lt_one hn1
    have hcceil (R : ℝ) (hR : ⌈R⌉₊ ≤ M) : R ≤ |(n : ℝ)| := by
      have hRM : ((⌈R⌉₊ : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hR
      exact (Nat.le_ceil R).trans (hRM.trans hnR)
    have ht0 := tP_nonneg 1 φ n
    have htT : tP 1 φ n ≤ T := (ht φ hφ).2 n (hcast Mt (by dsimp only [M]; omega))
    have hth := Nat.ceil_mono (KSPS025U5.threshold_le 1 B φ hφ)
    have hsb := Nat.ceil_mono (show 2*KSPS016W.Sb φ ≤ 2*SB by linarith only [hSφ])
    have h1 := hcast (⌈a⌉₊+⌈KSPSVolterra.threshold 1 (sobolevNorm 1 φ)⌉₊+1) (by dsimp only [M]; omega)
    have h2 := hcast (⌈a⌉₊+⌈2*KSPS016W.Sb φ⌉₊+1) (by dsimp only [M]; omega)
    have h4 : 2*(a+Jsum φ) ≤ indexWeight n := by
      have hh := hcceil (2*(a+L)) (by dsimp only [M]; omega)
      have hw := KSPS025U7.abs_le_w n
      linarith only [hh, hw, hJφ]
    have hsmall : tP 1 φ n ≤ indexWeight n^1/4 := by
      have hh := hcceil (4*T) (by dsimp only [M]; omega)
      have hw := KSPS025U7.abs_le_w n
      simp only [pow_one]
      linarith only [hh, hw, htT]
    have hL1 : 2*Lp φ ≤ |(n : ℝ)|^2 := by
      have hh := hcceil (2*L) (by dsimp only [M]; omega)
      have hsq : |(n : ℝ)| ≤ |(n : ℝ)|^2 := by nlinarith only [hn1]
      linarith only [hh, hsq, hLp]
    have hL2 : 2*Lsum φ ≤ |(n : ℝ)|^2 := by
      have hh := hcceil (2*L) (by dsimp only [M]; omega)
      have hsq : |(n : ℝ)| ≤ |(n : ℝ)|^2 := by nlinarith only [hn1]
      linarith only [hh, hsq, hLs]
    have hinv : ‖(n : ℂ)⁻¹‖ ≤ r0 := by
      rw [norm_inv, Complex.norm_intCast, inv_eq_one_div]
      have hh := hcceil (1/r0) (by dsimp only [M]; omega)
      calc
        1/|(n : ℝ)| ≤ 1/(1/r0) := one_div_le_one_div_of_le (by positivity) hh
        _ = r0 := one_div_one_div r0
    obtain ⟨hne, heq, hsmallζ, htay⟩ := hζ (n : ℂ)⁻¹ hinv
    have hq := hquad n (hcast M26 (by dsimp only [M]; omega))
    obtain ⟨BC, hBC, hH⟩ := g02_radicand_uniform 1 le_rfl φ a ha
      (fun m => (hloc φ hφ m).1) (fun m => (hloc φ hφ m).2)
      hplus hminus ζ CT hCT n h1 h2 h4 hsmall T hT htT hL1 hL2 hne heq hsmallζ htay hq
    obtain ⟨hp, hm, hqp, hqm⟩ := hq
    obtain ⟨hqp1, hqp2, hqp3⟩ := hqp
    obtain ⟨R, _, _, hRw, hEw, hR, hα, hβ, _, _, _, _, _⟩ :=
      g02_side_core_uniform 1 le_rfl φ a ha true (periodicPlus φ) (fun _ => rfl)
        (fun m => (hloc φ hφ m).1) n h1 h2 h4 hsmall hp hqp2
    obtain ⟨_, _, hwX⟩ := KSPS015W.tail_facts a _ ha (periodicPlus φ) (fun m => (hloc φ hφ m).1) n h1
    have hg := g02_tail_halfGap_bound 1 le_rfl φ n hp (hplus n) BC R (KSPS016W.Sb φ)
      (tP 1 φ n) (c n) (KSPS016W.Sb_nonneg φ) ht0 (hc0 n) (KSPS015W.one_le_w n)
      hwX hqp3 hR hRw hEw hα hβ hBC hH (hre n) (hstar n)
    have hpoly : g02_radPolynomial ‖integralRiccatiLeft φ 2‖ (KSPS016W.Sb φ) (tP 1 φ n) ≤ D*tP 1 φ n :=
      g02_radPolynomial_le _ _ _ L SB T (norm_nonneg _) (KSPS016W.Sb_nonneg φ) ht0 hIL hSφ htT
    have hsqrt := Real.sqrt_le_sqrt (show
        (g02_radPolynomial ‖integralRiccatiLeft φ 2‖ (KSPS016W.Sb φ) (tP 1 φ n)+(c n)^2)/2 ≤
          (D*tP 1 φ n+(c n)^2)/2 by linarith only [hpoly])
    have hg' : |g02_halfGap φ n| ≤ 2*(tP 1 φ n+c n)+Real.sqrt ((D*tP 1 φ n+(c n)^2)/2) := by
      have h : indexWeight n^2 *
          |((periodicPlus φ n-periodicMinus φ n)/2).re-
            ‖physicalFourier (toPotPair φ).1 (-n)‖| ≤
          2*(tP 1 φ n+c n)+Real.sqrt ((D*tP 1 φ n+(c n)^2)/2) :=
        hg.trans (add_le_add le_rfl hsqrt)
      simpa only [g02_halfGap, abs_mul,
        abs_of_nonneg (sq_nonneg (indexWeight n : ℝ))] using h
    have ht2 := htail_t {n} (by intro m hm; rw [Finset.mem_singleton.mp hm]; exact hn)
    have hc2 := hc_sum {n} (by intro m hm; rw [Finset.mem_singleton.mp hm]; exact hn)
    rw [Finset.sum_singleton] at ht2 hc2
    exact g02_real_fourth_bound _ _ _ D T U (abs_nonneg _) ht0 (hc0 n) hD ht2 hc2 hg'
  have hlow (n : ℤ) (hn : ¬ (M : ℤ) ≤ |n|) : |g02_halfGap φ n| ≤ KL := by
    have hnM : n.natAbs ≤ M := by
      have h := Int.natCast_natAbs n
      omega
    have hw1 := KSPS015W.one_le_w n
    have hwM := KSPS025U7.w_le_of_natAbs n M hnM
    obtain ⟨hp, hm⟩ := hloc φ hφ n
    have haw : a/indexWeight n ≤ a := div_le_self ha hw1
    have hgap : ‖(periodicPlus φ n-periodicMinus φ n)/2‖ ≤ a := by
      have he : (periodicPlus φ n-periodicMinus φ n)/2 =
          ((periodicPlus φ n-(n : ℂ)*Real.pi)-(periodicMinus φ n-(n : ℂ)*Real.pi))/2 := by ring
      rw [he, norm_div, Complex.norm_ofNat]
      have h := norm_sub_le (periodicPlus φ n-(n : ℂ)*Real.pi) (periodicMinus φ n-(n : ℂ)*Real.pi)
      linarith only [h, hp, hm, haw]
    have hfour : ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤ B := by
      have hf := KSPSU4.weighted_fourier_le 1 φ {n}
      simp only [Finset.sum_singleton, pow_one] at hf
      have hnorm : sobolevNorm 1 φ ^ 2 ≤ B ^ 2 :=
        pow_le_pow_left₀ (show 0 ≤ sobolevNorm 1 φ from Real.sqrt_nonneg _) hφ 2
      have hp0 := norm_nonneg (physicalFourier (toPotPair φ).1 (-n))
      have hmul : ‖physicalFourier (toPotPair φ).1 (-n)‖ ≤
          indexWeight n*‖physicalFourier (toPotPair φ).1 (-n)‖ := le_mul_of_one_le_left hp0 hw1
      have hmul2 := pow_le_pow_left₀ hp0 hmul 2
      nlinarith only [hf, hnorm, hp0, hmul, hmul2, hB,
        sq_nonneg (indexWeight n*‖physicalFourier (toPotPair φ).2 n‖)]
    have hab : |((periodicPlus φ n-periodicMinus φ n)/2).re-
        ‖physicalFourier (toPotPair φ).1 (-n)‖| ≤ a+B := by
      have h := abs_sub ((periodicPlus φ n-periodicMinus φ n)/2).re
        ‖physicalFourier (toPotPair φ).1 (-n)‖
      rw [abs_of_nonneg (norm_nonneg _)] at h
      exact h.trans (add_le_add ((Complex.abs_re_le_norm _).trans hgap) hfour)
    dsimp only [g02_halfGap, KL]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (pow_le_pow_left₀ (le_trans zero_le_one hw1) hwM 2) hab (abs_nonneg _) (by positivity)
  let Ft := F.filter (fun n : ℤ => (M : ℤ) ≤ |n|)
  let Fl := F.filter (fun n : ℤ => ¬ (M : ℤ) ≤ |n|)
  have hFt : ∀ n ∈ Ft, (M : ℤ) ≤ |n| := fun n hn => (Finset.mem_filter.mp hn).2
  have hTail : ∑ n ∈ Ft, |g02_halfGap φ n|^4 ≤ CH := by
    have hs := Finset.sum_le_sum (fun n hn => htail n (hFt n hn))
    have htS := htail_t Ft hFt
    have hcS := hc_sum Ft hFt
    have h1 := mul_le_mul_of_nonneg_left htS (show 0 ≤ 16*T+D^2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcS (show 0 ≤ 17*U by positivity)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    dsimp only [CH]
    linarith only [hs, h1, h2]
  have hLow : ∑ n ∈ Fl, |g02_halfGap φ n|^4 ≤ CL := by
    have hsub : Fl ⊆ Finset.Icc (-(M : ℤ)) M := by
      intro n hn
      have hh := (Finset.mem_filter.mp hn).2
      apply Finset.mem_Icc.mpr
      have habs : |n| < (M : ℤ) := lt_of_not_ge hh
      have hb := abs_lt.mp habs
      constructor <;> omega
    calc
      ∑ n ∈ Fl, |g02_halfGap φ n|^4 ≤ ∑ _n ∈ Fl, KL^4 :=
        Finset.sum_le_sum (fun n hn => pow_le_pow_left₀ (abs_nonneg _) (hlow n (Finset.mem_filter.mp hn).2) 4)
      _ = (Fl.card : ℝ)*KL^4 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ CL := mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub) (by positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not F (fun n : ℤ => (M : ℤ) ≤ |n|)
    (fun n => |g02_halfGap φ n|^4)
  change (∑ n ∈ Ft, |g02_halfGap φ n|^4)+(∑ n ∈ Fl, |g02_halfGap φ n|^4) = _ at hsplit
  rw [← hsplit]
  exact add_le_add hTail hLow

/-- The exact previously missing actual-carrier quantitative leaf. -/
theorem g02_halfGap_uniform_missing (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : G02H1, ‖w‖ ≤ B →
      ∀ F : Finset ℤ, (∀ n ∈ F, n ≠ 0) →
        ∑ n ∈ F, |g02_halfGap (g02_pair w) n|^4 ≤ C := by
  obtain ⟨C, hC, hb⟩ := g02_halfGap_uniform_sobolev (2*B) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro w hw F _hF
  apply hb (g02_pair w) _ (g02_pair_real w) F
  exact (g02_pair_norm_le w).trans (mul_le_mul_of_nonneg_left hw (by norm_num))

/-- The independent canonical residuals are each majorized by midpoint and half-gap fourth powers. -/
theorem g02_remainder_fourth_le (w : G02H1) (n : ℤ) (upper : Bool) :
    |(if upper then g02_rPlus w n else g02_rMinus w n)|^4 ≤
      27*(|g02_midError (g02_pair w) n|^4+|g02_halfGap (g02_pair w) n|^4) := by
  have hdec := g02_remainders_decompose w n
  have hr := g02_index_ratio n
  have hab : |(if upper then g02_rPlus w n else g02_rMinus w n)| ≤
      |g02_midError (g02_pair w) n|+|g02_halfGap (g02_pair w) n| := by
    cases upper
    · simp only [Bool.false_eq_true, ite_false]
      rw [hdec.2, abs_mul, abs_of_nonneg hr.1]
      exact ((mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans_eq (one_mul _)).trans (abs_sub _ _)
    · simp only [ite_true]
      rw [hdec.1, abs_mul, abs_of_nonneg hr.1]
      exact ((mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)).trans_eq (one_mul _)).trans (abs_add_le _ _)
  have hq := KSPS028P.pow4_sum_le |g02_midError (g02_pair w) n|
    |g02_halfGap (g02_pair w) n| 0 (abs_nonneg _) (abs_nonneg _) le_rfl
  simp only [add_zero, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] at hq
  exact (pow_le_pow_left₀ (abs_nonneg _) hab 4).trans hq

/-- Summability is established before either real tsum is bounded uniformly on a physical H1 ball. -/
theorem g02_physical_remainders_uniform (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : G02H1, ‖w‖ ≤ B →
      Summable (fun n : ℤ => |g02_rPlus w n|^4) ∧
      Summable (fun n : ℤ => |g02_rMinus w n|^4) ∧
      (∑' n : ℤ, |g02_rPlus w n|^4) ≤ C ∧
      (∑' n : ℤ, |g02_rMinus w n|^4) ≤ C := by
  obtain ⟨CM, hCM, hmid⟩ := g02_physical_midpoint_uniform B hB
  obtain ⟨CG, hCG, hgap⟩ := g02_halfGap_uniform_sobolev (2*B) (by positivity)
  refine ⟨27*(CM+CG), by positivity, ?_⟩
  intro w hw
  have hpair : sobolevNorm 1 (g02_pair w) ≤ 2*B :=
    (g02_pair_norm_le w).trans (mul_le_mul_of_nonneg_left hw (by norm_num))
  have hm := hmid w hw
  have hg := hgap (g02_pair w) hpair (g02_pair_real w)
  have hfinite (upper : Bool) (F : Finset ℤ) :
      ∑ n ∈ F, |(if upper then g02_rPlus w n else g02_rMinus w n)|^4 ≤ 27*(CM+CG) := by
    have hs := Finset.sum_le_sum (fun n (_ : n ∈ F) => g02_remainder_fourth_le w n upper)
    have hM := (hm.1.sum_le_tsum F (fun _ _ => pow_nonneg (abs_nonneg _) 4)).trans hm.2
    have hG := hg F
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    linarith only [hs, hM, hG]
  obtain ⟨hp, hm'⟩ := g02_physical_remainders_summable w
  refine ⟨hp, hm', hp.tsum_le_of_sum_le ?_, hm'.tsum_le_of_sum_le ?_⟩
  · intro F
    simpa only [ite_true] using hfinite true F
  · intro F
    simpa only [Bool.false_eq_true, ite_false] using hfinite false F

/-- The source's uniform periodic endpoint expansion on the actual physical H1 carrier. -/
theorem grouped_periodic_endpoint_expansion_uniform :
  ∃ c1 c2 : WeightedHilbert (sobolevModeWeight (1 : ℝ)) → ℝ,
    ∃ rPlus rMinus : WeightedHilbert (sobolevModeWeight (1 : ℝ)) → ℤ → ℝ,
      ∀ B : ℝ, 0 ≤ B →
        ∃ C : ℝ, ∃ N0 : ℕ, 0 ≤ C ∧ 1 ≤ N0 ∧
          ∀ w : WeightedHilbert (sobolevModeWeight (1 : ℝ)), ‖w‖ ≤ B →
            |c1 w| ≤ C ∧ |c2 w| ≤ C ∧
            Summable (fun n : ℤ => |rPlus w n| ^ 4) ∧
            Summable (fun n : ℤ => |rMinus w n| ^ 4) ∧
            (∑' n : ℤ, |rPlus w n| ^ 4) ≤ C ∧
            (∑' n : ℤ, |rMinus w n| ^ 4) ≤ C ∧
            ∀ n : ℤ, N0 ≤ n.natAbs →
              actualGapUpperAllE02_38
                  (physicalH1ComplexCarrierToL2Actual22 w) n =
                (n : ℝ) * Real.pi + c1 w / (n : ℝ) + c2 w / (n : ℝ)^2 +
                  ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖ +
                  rPlus w n / (n : ℝ)^2 ∧
              actualGapLowerAllE02_38
                  (physicalH1ComplexCarrierToL2Actual22 w) n =
                (n : ℝ) * Real.pi + c1 w / (n : ℝ) + c2 w / (n : ℝ)^2 -
                  ‖physicalFourier (physicalH1ComplexCarrierToL2Actual22 w) (-n)‖ +
                  rMinus w n / (n : ℝ)^2 := by
  refine ⟨g02_c1, g02_c2, g02_rPlus, g02_rMinus, ?_⟩
  intro B hB
  obtain ⟨CR, hCR, hrem⟩ := g02_physical_remainders_uniform B hB
  let C : ℝ := (2*B)^2+CR+1
  have hcoef : (2*B)^2 ≤ C := by dsimp only [C]; linarith only [hCR]
  have hremC : CR ≤ C := by dsimp only [C]; nlinarith only [sq_nonneg (2*B)]
  refine ⟨C, 1, by dsimp only [C]; positivity, le_rfl, ?_⟩
  intro w hw
  have hc := g02_coefficients_uniform B hB w hw
  obtain ⟨hp, hm, hpb, hmb⟩ := hrem w hw
  refine ⟨hc.1.trans hcoef, hc.2.trans hcoef, hp, hm, hpb.trans hremC, hmb.trans hremC, ?_⟩
  intro n hn
  apply g02_endpoint_identities w n
  intro hzero
  rw [hzero] at hn
  norm_num at hn

end NlsGge.ThirdConsultation.Narrative
