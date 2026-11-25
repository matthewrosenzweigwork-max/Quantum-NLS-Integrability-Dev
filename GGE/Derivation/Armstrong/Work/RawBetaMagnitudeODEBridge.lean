import Armstrong.Work.RawBetaOriginalValue
import Armstrong.Work.RawBetaFixedCoefficient
import Armstrong.Work.RawBetaMagnitudeRegularFactor
import NlsGge.GK38.Lib.QuadraticODETerminalMagnitude

/-!
# Fixed-coefficient bridge to the quadratic terminal-magnitude estimate

Working proof code for GK Lemma 15.1. No frozen target or graph metadata is
modified here.
-/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem gk151_fullNumerator_div_KD_eq_regularFactor38
    (n m : ℤ) (hnm : n ≠ m)
    (phi : PotPair) (hphi : phi ∈ gkW)
    (C : ℤ → ℂ) (Rho : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi C Rho)
    (s : Lib.L2Seq)
    (hsn : Lib.sigmaOf s n ∈ closedBall (C n) (Rho n))
    (z : ℂ) (hz : z ∈ closedBall (C m) (Rho m)) :
    p2FullNumerator38 n s z /
        (((2 * Complex.I) / (Lib.piN m : ℂ)) *
          a5OmittedRootProduct38 m (phi, z)) =
      (Lib.sigmaOf s m - z) *
        angleRegularFactor38 n m ((phi, s), z) := by
  have hD : a5OmittedRootProduct38 m (phi, z) ≠ 0 :=
    a5OmittedRoot_ne_zero38 m (phi,z)
      (a5OwnClosedBall_omittedDomain38 phi hphi C Rho hfam m z hz)
  obtain ⟨c, N, hgeom, _hspec⟩ := hfam
  have hden := (p2OwnSigma_denominator38 C Rho c N hgeom
    n m hnm s hsn z hz).1
  have hcross := p2Omit_cross_identity38 n m s z
  unfold p2FullNumerator38 angleRegularFactor38 p2OmittedRatio38
  field_simp [hD, hden,
    Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m), Complex.I_ne_zero]
  simp only [Complex.I_sq] at *
  linear_combination -hcross

theorem gk151_terminal_norm_algebra38
    (a b mu delta K D R T : ℂ)
    (hdelta : delta^2 = K^2 * ((mu-a)*(mu-b)) * D^2)
    (hT : T = K * D * R) :
    ‖delta * R‖ =
      Real.sqrt (‖(mu-a)*(mu-b)‖) * ‖T‖ := by
  have hsquare :
      ‖delta * R‖^2 =
        (Real.sqrt (‖(mu-a)*(mu-b)‖) * ‖T‖)^2 := by
    have hd := congrArg norm hdelta
    simp only [norm_pow, norm_mul] at hd
    have hsqrt :
        (Real.sqrt (‖mu-a‖ * ‖mu-b‖))^2 =
          ‖mu-a‖ * ‖mu-b‖ :=
      Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have hTnorm : ‖T‖ = ‖K‖ * ‖D‖ * ‖R‖ := by
      rw [hT, norm_mul, norm_mul]
    rw [norm_mul, hTnorm]
    calc
      (‖delta‖ * ‖R‖)^2 = ‖delta‖^2 * ‖R‖^2 := by ring
      _ = (‖K‖^2 * (‖mu-a‖ * ‖mu-b‖) * ‖D‖^2) * ‖R‖^2 := by rw [hd]
      _ = (Real.sqrt (‖mu-a‖ * ‖mu-b‖) *
          (‖K‖ * ‖D‖ * ‖R‖))^2 := by rw [mul_pow, hsqrt]; ring
      _ = (Real.sqrt (‖(mu-a)*(mu-b)‖) *
          (‖K‖ * ‖D‖ * ‖R‖))^2 := by rw [norm_mul]
  have hl : 0 <= ‖delta * R‖ := norm_nonneg _
  have hr : 0 <= Real.sqrt (‖(mu-a)*(mu-b)‖) * ‖T‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith


/-- The literal fixed coefficient for the same supplied numerator becomes the
quadratic coefficient needed by the terminal-magnitude estimate after multiplying
by the exact nonvanishing omitted-root factor. Its terminal norm is exactly the
norm of the corresponding genuine source-beta value. -/
theorem gk151_fixedCoefficient_quadratic_terminal_bridge38
    (n m : ℤ) (hmn : m ≠ n)
    (F : (k : ℤ) → PotPair → P2Space38 k)
    (phi : GKPotential38)
    (C : ℤ → ℂ) (Rho : ℤ → ℝ)
    (hfam : IsolatingFamily38 phi.1 C Rho)
    (s : Lib.L2Seq)
    (hsn : Lib.sigmaOf s n ∈ closedBall (C n) (Rho n))
    (hnum : p6PsiNumerator38 n (F n) phi.1 = p2FullNumerator38 n s)
    (hperiod : abelianPeriod38 m phi.1
      (p6PsiNumerator38 n (F n) phi.1) = 0) :
    let a : ℂ := lamMinus phi.1 m
    let b : ℂ := lamPlus phi.1 m
    let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
    let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (phi.1,z)
    let R : ℂ → ℂ := rawBetaFixedCoefficient38 n m (F n) phi.1 (C m) (Rho m)
    let T : ℂ → ℂ := fun z => K * D z * R z
    AnalyticOnNhd ℂ T (ball (C m) (Rho m)) ∧
      (∀ z ∈ ball (C m) (Rho m),
        (z-a)*(z-b)*deriv T z + (z-(a+b)/2)*T z =
          (Lib.sigmaOf s m-z) * angleRegularFactor38 n m ((phi.1,s),z)) ∧
      GKSourceBetaValue38 n m hmn F phi
        (antiDiscrim phi.1 (muSeq phi.1 m) * R (muSeq phi.1 m)) ∧
      ‖antiDiscrim phi.1 (muSeq phi.1 m) * R (muSeq phi.1 m)‖ =
        Real.sqrt (‖(muSeq phi.1 m-a)*(muSeq phi.1 m-b)‖) *
          ‖T (muSeq phi.1 m)‖ := by
  let a : ℂ := lamMinus phi.1 m
  let b : ℂ := lamPlus phi.1 m
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (phi.1,z)
  let R : ℂ → ℂ := rawBetaFixedCoefficient38 n m (F n) phi.1 (C m) (Rho m)
  let T : ℂ → ℂ := fun z => K * D z * R z
  let H : ℂ → ℂ := fun z => K^2 * ((z-a)*(z-b)) * D z^2
  have hK : K ≠ 0 := by
    dsimp [K]
    exact div_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (Lib.piN_ne_zero m))
  have hD : AnalyticOnNhd ℂ D (closedBall (C m) (Rho m)) := by
    intro z hz
    exact (a5OmittedRoot_analytic38 m (phi.1,z)
      (a5OwnClosedBall_omittedDomain38 phi.1 phi.2 C Rho hfam m z hz)).comp
        (analyticAt_const.prod analyticAt_id)
  have hDn : ∀ z ∈ closedBall (C m) (Rho m), D z ≠ 0 := by
    intro z hz
    exact a5OmittedRoot_ne_zero38 m (phi.1,z)
      (a5OwnClosedBall_omittedDomain38 phi.1 phi.2 C Rho hfam m z hz)
  obtain ⟨_hI0, _hI1, hR, hRode⟩ :=
    rawBetaFixedCoefficientOfZeroPeriod38 n m (F n) phi.1 phi.2
      C Rho hfam hperiod
  have hT : AnalyticOnNhd ℂ T (ball (C m) (Rho m)) := by
    exact (analyticOnNhd_const.mul (hD.mono ball_subset_closedBall)).mul hR
  have hPH : EqOn (perChar phi.1) H (ball (C m) (Rho m)) := by
    intro z hz
    exact rawBetaFixedFilledFactorization38 phi.1 phi.2 C Rho hfam m z
      (ball_subset_closedBall hz)
  have hquad : ∀ z ∈ ball (C m) (Rho m),
      (z-a)*(z-b)*deriv T z + (z-(a+b)/2)*T z =
        (Lib.sigmaOf s m-z) * angleRegularFactor38 n m ((phi.1,s),z) := by
    intro z hz
    have hzcl := ball_subset_closedBall hz
    have hDd : HasDerivAt D (deriv D z) z :=
      (hD z hzcl).differentiableAt.hasDerivAt
    have hRd : HasDerivAt R (deriv R z) z :=
      (hR z hz).differentiableAt.hasDerivAt
    have hTd : HasDerivAt T
        ((K * deriv D z) * R z + (K * D z) * deriv R z) z := by
      convert (hDd.const_mul K).mul hRd using 1
    have hDsq : HasDerivAt (fun w => D w^2) (2*D z*deriv D z) z := by
      simpa using! hDd.pow 2
    have hq : HasDerivAt (fun w : ℂ => (w-a)*(w-b))
        (2*(z-(a+b)/2)) z := by
      apply (((hasDerivAt_id z).sub_const a).mul
        ((hasDerivAt_id z).sub_const b)).congr_deriv
      simp only [id_eq]
      ring
    have hHd : HasDerivAt H
        (2*K^2*((z-(a+b)/2)*D z^2 +
          ((z-a)*(z-b))*D z*deriv D z)) z := by
      apply ((hq.const_mul (K^2)).mul hDsq).congr_deriv
      ring
    have hPE : perChar phi.1 =ᶠ[nhds z] H := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hPH hw
    have hPd : HasDerivAt (perChar phi.1)
        (2*K^2*((z-(a+b)/2)*D z^2 +
          ((z-a)*(z-b))*D z*deriv D z)) z :=
      hHd.congr_of_eventuallyEq hPE
    have hode := hRode z hz
    rw [hPH hz, hPd.deriv] at hode
    have hscaled :
        (z-a)*(z-b)*deriv T z + (z-(a+b)/2)*T z =
          p6PsiNumerator38 n (F n) phi.1 z / (K * D z) := by
      rw [hTd.deriv]
      change (z-a)*(z-b)*
          ((K*deriv D z)*R z+(K*D z)*deriv R z) +
        (z-(a+b)/2)*(K*D z*R z) = _
      have hDz : D z ≠ 0 := hDn z hzcl
      change (K^2*((z-a)*(z-b))*D z^2)*deriv R z +
          ((2*K^2*((z-(a+b)/2)*D z^2 +
            ((z-a)*(z-b))*D z*deriv D z))/2)*R z = _ at hode
      field_simp [hK, hDz] at hode ⊢
      linear_combination hode
    rw [hscaled, hnum]
    exact gk151_fullNumerator_div_KD_eq_regularFactor38
      n m (Ne.symm hmn) phi.1 phi.2 C Rho hfam s hsn z hzcl
  have hsource : GKSourceBetaValue38 n m hmn F phi
      (antiDiscrim phi.1 (muSeq phi.1 m) * R (muSeq phi.1 m)) :=
    rawBetaSourceValueOfFixedCoefficient38 n m hmn F phi C Rho hfam hperiod
      R hR hRode
  have hfamCopy := hfam
  obtain ⟨c, N, hgeom, hspec⟩ := hfamCopy
  have hmu : muSeq phi.1 m ∈ ball (C m) (Rho m) := (hspec.1 m).2.1
  have hPmu : perChar phi.1 (muSeq phi.1 m) =
      K^2 * ((muSeq phi.1 m-a)*(muSeq phi.1 m-b)) *
        D (muSeq phi.1 m)^2 := by
    exact rawBetaFixedFilledFactorization38 phi.1 phi.2 C Rho hfam m
      (muSeq phi.1 m) (ball_subset_closedBall hmu)
  have hdelta : antiDiscrim phi.1 (muSeq phi.1 m)^2 =
      K^2 * ((muSeq phi.1 m-a)*(muSeq phi.1 m-b)) *
        D (muSeq phi.1 m)^2 :=
    (rawBetaDirichletTerminalSquare38 phi m).trans hPmu
  have hnorm := gk151_terminal_norm_algebra38 a b (muSeq phi.1 m)
    (antiDiscrim phi.1 (muSeq phi.1 m)) K (D (muSeq phi.1 m))
    (R (muSeq phi.1 m)) (T (muSeq phi.1 m)) hdelta rfl
  exact ⟨hT, hquad, hsource, hnorm⟩

end
end NlsGge.GK38
