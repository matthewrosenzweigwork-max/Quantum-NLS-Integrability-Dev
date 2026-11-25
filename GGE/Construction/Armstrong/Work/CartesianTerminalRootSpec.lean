import Armstrong.Work.RawBetaFixedCoefficient
import Armstrong.Work.RawBetaSpectralInput
import NlsGge.GK38.AngleDirichletAnalytic
import NlsGge.GK38.GradFundamentalDefs
import NlsGge.GK38.AngleCollapsedEndpointContinuity

/-!
# Actual analytic terminal root for the diagonal exponential

The antidiscriminant specifies the actual terminal sheet. Dividing by the
nonvanishing omitted-root factor gives a root of the own quadratic that is
analytic in the potential, including complex collapsed gaps. No canonical-root
value on the own cut or chosen sign of a square root is used.

These are ordinary speculative helpers. The two algebraic prefactors are not
asserted to be the source Cartesian coordinates: the own-path exponential
characterization and the uniform exponential correction remain separate.
-/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

/-- Literal actual terminal sheet divided by the exact omitted-root factor. -/
def gk16TerminalRoot38 (n : ℤ) (phi : PotPair) : ℂ :=
  antiDiscrim phi (muSeq phi n) /
    (((2*Complex.I)/(Lib.piN n : ℂ)) *
      a5OmittedRootProduct38 n (phi,muSeq phi n))

/-- The actual terminal denominator is nonzero even at an own-gap endpoint. -/
theorem gk16_terminal_denominator_ne_zero38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW) :
    ((2*Complex.I)/(Lib.piN n : ℂ)) *
      a5OmittedRootProduct38 n (phi,muSeq phi n) ≠ 0 := by
  have hfam := isolating_family38 phi hphi
  have hfamCopy := hfam
  obtain ⟨c,N,hgeom,hspec⟩ := hfamCopy
  have hmu := (hspec.1 n).2.1
  have hdom := a5OwnClosedBall_omittedDomain38 phi hphi
    (discC phi) (discR phi) hfam n (muSeq phi n) (ball_subset_closedBall hmu)
  exact mul_ne_zero
    (div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero n)))
    (a5OmittedRoot_ne_zero38 n (phi,muSeq phi n) hdom)

/-- Exact own-quadratic identity, with all complex and collapsed gaps retained. -/
theorem gk16_terminal_root_sq38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW) :
    (gk16TerminalRoot38 n phi)^2 =
      (muSeq phi n-lamMinus phi n)*(muSeq phi n-lamPlus phi n) := by
  have hfam := isolating_family38 phi hphi
  have hfamCopy := hfam
  obtain ⟨c,N,hgeom,hspec⟩ := hfamCopy
  have hmu := (hspec.1 n).2.1
  have hsquare := (rawBetaDirichletTerminalSquare38 ⟨phi,hphi⟩ n).trans
    (rawBetaFixedFilledFactorization38 phi hphi (discC phi) (discR phi)
      hfam n (muSeq phi n) (ball_subset_closedBall hmu))
  have hden := gk16_terminal_denominator_ne_zero38 n phi hphi
  unfold gk16TerminalRoot38
  rw [div_pow,hsquare]
  apply (div_eq_iff (pow_ne_zero 2 hden)).2
  ring

/-- The actual terminal root is analytic on all gkW, without differentiating
any individually labelled periodic endpoint. -/
theorem gk16_terminal_root_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ (gk16TerminalRoot38 n) gkW := by
  intro phi hphi
  have hfam := isolating_family38 phi hphi
  have hfamCopy := hfam
  obtain ⟨c,N,hgeom,hspec⟩ := hfamCopy
  have hmu := (hspec.1 n).2.1
  have hdom := a5OwnClosedBall_omittedDomain38 phi hphi
    (discC phi) (discR phi) hfam n (muSeq phi n) (ball_subset_closedBall hmu)
  have hJ : AnalyticAt ℂ (fun psi : PotPair => (psi,muSeq psi n)) phi :=
    analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n phi hphi)
  have hA : AnalyticAt ℂ (fun psi : PotPair => antiDiscrim psi (muSeq psi n)) phi :=
    AnalyticAt.comp
      (g := fun p : PotPair × ℂ => antiDiscrim p.1 p.2)
      (f := fun psi : PotPair => (psi,muSeq psi n)) (x := phi)
      (analyticOnNhd_antiDiscrim (phi,muSeq phi n) (mem_univ _)) hJ
  have hD : AnalyticAt ℂ
      (fun psi : PotPair => a5OmittedRootProduct38 n (psi,muSeq psi n)) phi :=
    AnalyticAt.comp (g := a5OmittedRootProduct38 n)
      (f := fun psi : PotPair => (psi,muSeq psi n)) (x := phi)
      (a5OmittedRoot_analytic38 n (phi,muSeq phi n) hdom) hJ
  exact hA.div (analyticAt_const.mul hD)
    (gk16_terminal_denominator_ne_zero38 n phi hphi)

/-- Both actual algebraic prefactors are analytic before the exponential
correction or source-path identification is considered. -/
theorem gk16_terminal_prefactors_analytic38 (n : ℤ) :
    AnalyticOnNhd ℂ
      (fun phi => 2*(tauN phi n-muSeq phi n)+2*gk16TerminalRoot38 n phi) gkW ∧
    AnalyticOnNhd ℂ
      (fun phi => 2*(tauN phi n-muSeq phi n)-2*gk16TerminalRoot38 n phi) gkW := by
  have hcenter := (analyticOnNhd_const (v := (2 : ℂ))).mul
    ((tauN_analytic n).sub (analyticOnNhd_muSeq_complex38 n))
  have hroot := (analyticOnNhd_const (v := (2 : ℂ))).mul
    (gk16_terminal_root_analytic38 n)
  exact ⟨hcenter.add hroot,hcenter.sub hroot⟩

/-- The product is exactly the symmetric squared gap, with no sheet-sign
hypothesis and no division by the gap. -/
theorem gk16_terminal_prefactors_product38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW) :
    (2*(tauN phi n-muSeq phi n)+2*gk16TerminalRoot38 n phi) *
      (2*(tauN phi n-muSeq phi n)-2*gk16TerminalRoot38 n phi) =
        gamma2 phi n := by
  have hsquare := gk16_terminal_root_sq38 n phi hphi
  rw [tauN_value38 phi hphi n,gamma2_value38 phi hphi n]
  linear_combination -4 * hsquare

/-- The square identity and actual centered endpoints control the terminal
root by precisely the source gap/displacement scales. -/
theorem gk16_terminal_root_norm38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW) :
    ‖gk16TerminalRoot38 n phi‖ ≤
      ‖muSeq phi n-tauN phi n‖ + Real.sqrt ‖gamma2 phi n‖/2 := by
  let B : ℝ := ‖muSeq phi n-tauN phi n‖ + Real.sqrt ‖gamma2 phi n‖/2
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (by positivity)
  have hends := anglePeriodic_centered_norm38 phi hphi n
  have ha : ‖muSeq phi n-lamMinus phi n‖ ≤ B := by
    have ht := norm_sub_le (muSeq phi n-tauN phi n) (lamMinus phi n-tauN phi n)
    have he : (muSeq phi n-tauN phi n)-(lamMinus phi n-tauN phi n) =
        muSeq phi n-lamMinus phi n := by ring
    rw [he,hends.1] at ht
    exact ht
  have hb : ‖muSeq phi n-lamPlus phi n‖ ≤ B := by
    have ht := norm_sub_le (muSeq phi n-tauN phi n) (lamPlus phi n-tauN phi n)
    have he : (muSeq phi n-tauN phi n)-(lamPlus phi n-tauN phi n) =
        muSeq phi n-lamPlus phi n := by ring
    rw [he,hends.2] at ht
    exact ht
  have hsquare := congrArg norm (gk16_terminal_root_sq38 n phi hphi)
  rw [norm_pow,norm_mul] at hsquare
  have hsqbound : ‖gk16TerminalRoot38 n phi‖^2 ≤ B^2 := by
    rw [hsquare,pow_two]
    exact mul_le_mul ha hb (norm_nonneg _) hB
  change ‖gk16TerminalRoot38 n phi‖ ≤ B
  nlinarith [norm_nonneg (gk16TerminalRoot38 n phi)]

/-- Both prefactors have the actual locally square-summable spectral scales;
no inverse-distance convolution is used. -/
theorem gk16_terminal_prefactors_norm38
    (n : ℤ) (phi : PotPair) (hphi : phi ∈ gkW) :
    ‖2*(tauN phi n-muSeq phi n)+2*gk16TerminalRoot38 n phi‖ ≤
        4*‖muSeq phi n-tauN phi n‖ + Real.sqrt ‖gamma2 phi n‖ ∧
    ‖2*(tauN phi n-muSeq phi n)-2*gk16TerminalRoot38 n phi‖ ≤
        4*‖muSeq phi n-tauN phi n‖ + Real.sqrt ‖gamma2 phi n‖ := by
  have hr := gk16_terminal_root_norm38 n phi hphi
  have hc : ‖(2 : ℂ)*(tauN phi n-muSeq phi n)‖ =
      2*‖muSeq phi n-tauN phi n‖ := by
    rw [norm_mul,norm_sub_rev]
    norm_num
  have hh : ‖(2 : ℂ)*gk16TerminalRoot38 n phi‖ =
      2*‖gk16TerminalRoot38 n phi‖ := by
    rw [norm_mul]
    norm_num
  have hp := norm_add_le ((2 : ℂ)*(tauN phi n-muSeq phi n))
    ((2 : ℂ)*gk16TerminalRoot38 n phi)
  have hm := norm_sub_le ((2 : ℂ)*(tauN phi n-muSeq phi n))
    ((2 : ℂ)*gk16TerminalRoot38 n phi)
  rw [hc,hh] at hp hm
  constructor <;> linarith

end
end NlsGge.GK38
