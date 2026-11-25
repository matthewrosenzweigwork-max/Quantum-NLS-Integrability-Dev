import Armstrong.Work.RawBetaMagnitudeRegularFactorSameFamily
import Armstrong.Work.RawBetaMagnitudeEndpointPlacement
import Armstrong.Work.RawBetaMagnitudeODEBridge
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38

/-!
# Local sharp GK15.1 estimate

Working proof code. This proves the frozen nearest-endpoint inequality locally
around one real base point, using the same supplied W/F. It is not yet the
global Wbeta assembly and does not alter the frozen provider.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk151_local_nearestEndpoint_bound38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2 * (Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (u : PhysicalL2) :
    ∃ delta C0 : ℝ, 0 < delta ∧ 0 < C0 ∧
      ball (realSlice u) delta ⊆ W ∧
      ∀ psi : {chi : PotPair // chi ∈ W}, psi.1 ∈ ball (realSlice u) delta →
        ∀ n m : ℤ, ∀ hmn : m ≠ n,
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn psi‖ <=
          C0 * Real.sqrt (‖lamPlus psi.1 m - lamMinus psi.1 m‖ +
            min ‖muSeq psi.1 m - lamMinus psi.1 m‖
              ‖muSeq psi.1 m - lamPlus psi.1 m‖) *
            Real.sqrt (min ‖muSeq psi.1 m - lamMinus psi.1 m‖
              ‖muSeq psi.1 m - lamPlus psi.1 m‖) *
            Lib.c3w n m := by
  have huW : realSlice u ∈ W := hreal (mem_range_self u)
  have huGK : realSlice u ∈ gkW := hWgk huW
  let Cb : ℤ → ℂ := discC (realSlice u)
  let Rb : ℤ → ℝ := discR (realSlice u)
  have hfam0 : IsolatingFamily38 (realSlice u) Cb Rb := by
    simpa only [Cb, Rb] using isolating_family38 (realSlice u) huGK
  obtain ⟨dr, Br, hdr, hBr, hdrW, hreg⟩ :=
    gk151_same_family_regular_factor_original_discs38
      W hWopen hreal hWgk F hFanalytic hFn hFinv hperiod hFreal u
  have hFspec : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi, F n phi) = 0 ∧
        (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
          (F n phi)).IsInvertible := by
    intro n phi hphi
    exact ⟨hFn n phi hphi, hFinv n phi hphi⟩
  obtain ⟨dp, L, hdp, hL, hdpW, hplace⟩ :=
    gk151_same_family_endpoint_placement38
      W hWopen hWgk F hFanalytic hFspec hFreal u huW
  have hfamCopy := hfam0
  obtain ⟨df, hdf, cf, Nf, hgeomf, hpersist⟩ :=
    fixed_family_persistence38 (realSlice u) Cb Rb hfamCopy
  let delta : ℝ := min dr (min dp df)
  let C0 : ℝ :=
    2 * Br * Real.sqrt (1 + 2 * L) * Real.sqrt (L + 1)
  have hdelta : 0 < delta := lt_min hdr (lt_min hdp hdf)
  have hC0 : 0 < C0 := by
    dsimp [C0]
    positivity
  have hsubr : ball (realSlice u) delta ⊆ ball (realSlice u) dr :=
    ball_subset_ball (min_le_left _ _)
  have hsubp : ball (realSlice u) delta ⊆ ball (realSlice u) dp :=
    ball_subset_ball ((min_le_right dr (min dp df)).trans (min_le_left _ _))
  have hsubf : ball (realSlice u) delta ⊆ ball (realSlice u) df :=
    ball_subset_ball ((min_le_right dr (min dp df)).trans (min_le_right _ _))
  have hdeltaW : ball (realSlice u) delta ⊆ W := hsubr.trans hdrW
  refine ⟨delta, C0, hdelta, hC0, hdeltaW, ?_⟩
  rintro ⟨psi, hpsiW⟩ hpsi n m hmn
  have hpsiGK : psi ∈ gkW := hWgk hpsiW
  have hfampsi : IsolatingFamily38 psi Cb Rb :=
    ⟨cf, Nf, hgeomf, hpersist psi (hsubf hpsi)⟩
  obtain ⟨S, hSan, hSspec⟩ := hreg n
  obtain ⟨hFnS, hSn, hnum, hfactor⟩ := hSspec psi (hsubr hpsi)
  have hfam0Copy := hfam0
  obtain ⟨c0, N0, hgeom0, hspec0⟩ := hfam0Copy
  have hsn : Lib.sigmaOf (S psi) n ∈ closedBall (Cb n) (Rb n) := by
    rw [hSn]
    exact ball_subset_closedBall
      ((hspec0.1 n).1 (left_mem_segment ℝ _ _))
  have hsigma_m :
      Lib.sigmaOf (S psi) m =
        countingCenter38 m + F n psi ⟨m, hmn⟩ := by
    unfold Lib.sigmaOf
    rw [← p2Restrict_apply38 n (S psi) ⟨m, hmn⟩, ← hFnS]
    rfl
  have hper : abelianPeriod38 m psi (p6PsiNumerator38 n (F n) psi) = 0 := by
    simpa only [ite_eq_right hmn] using hperiod n psi hpsiW m
  let gphi : GKPotential38 := ⟨psi, hpsiGK⟩
  have hbridge :=
    gk151_fixedCoefficient_quadratic_terminal_bridge38
      n m hmn F gphi Cb Rb hfampsi (S psi) hsn hnum hper
  let a : ℂ := lamMinus psi m
  let b : ℂ := lamPlus psi m
  let K : ℂ := (2 * Complex.I) / (Lib.piN m : ℂ)
  let D : ℂ → ℂ := fun z => a5OmittedRootProduct38 m (psi,z)
  let Rc : ℂ → ℂ :=
    rawBetaFixedCoefficient38 n m (F n) psi (Cb m) (Rb m)
  let T : ℂ → ℂ := fun z => K * D z * Rc z
  have hT : AnalyticOnNhd ℂ T (ball (Cb m) (Rb m)) := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.1
  have hode : ∀ z ∈ ball (Cb m) (Rb m),
      (z-a)*(z-b)*deriv T z + (z-(a+b)/2)*T z =
        (Lib.sigmaOf (S psi) m-z) *
          angleRegularFactor38 n m ((psi,S psi),z) := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.2.1
  have hsource : GKSourceBetaValue38 n m hmn F gphi
      (antiDiscrim psi (muSeq psi m) * Rc (muSeq psi m)) := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.2.2.1
  have hterminal :
      ‖antiDiscrim psi (muSeq psi m) * Rc (muSeq psi m)‖ =
        Real.sqrt (‖(muSeq psi m-a)*(muSeq psi m-b)‖) *
          ‖T (muSeq psi m)‖ := by
    simpa only [gphi, a, b, K, D, Rc, T] using hbridge.2.2.2
  let pW : {chi : PotPair // chi ∈ W} := ⟨psi, hpsiW⟩
  have hchar :=
    gkSourceBeta_characterization38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod n m hmn pW
  have hsource' : GKSourceBetaValue38 n m hmn F
      ⟨pW.1, hWgk pW.2⟩
      (antiDiscrim psi (muSeq psi m) * Rc (muSeq psi m)) := by
    simpa only [pW, gphi] using hsource
  have hbeta :
      antiDiscrim psi (muSeq psi m) * Rc (muSeq psi m) =
        gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m hmn pW :=
    hchar.2.1 _ hsource'
  have hfampsiCopy := hfampsi
  obtain ⟨cs, Ns, hgeoms, hspecs⟩ := hfampsiCopy
  have ha : a ∈ ball (Cb m) (Rb m) :=
    (hspecs.1 m).1 (left_mem_segment ℝ _ _)
  have hb : b ∈ ball (Cb m) (Rb m) :=
    (hspecs.1 m).1 (right_mem_segment ℝ _ _)
  have hmu : muSeq psi m ∈ ball (Cb m) (Rb m) := (hspecs.1 m).2.1
  have hconv : Convex ℝ (ball (Cb m) (Rb m)) := convex_ball _ _
  have hzeta : ContinuousOn
      (fun z => angleRegularFactor38 n m ((psi,S psi),z))
      (ball (Cb m) (Rb m)) := by
    intro z hz
    have haJoint := angleRegularFactor_joint_own_disc38 n m (Ne.symm hmn)
      psi hpsiGK Cb Rb hfampsi (S psi) hsn z
      (ball_subset_closedBall hz)
    have haOne : AnalyticAt ℂ
        (fun w : ℂ => angleRegularFactor38 n m ((psi,S psi),w)) z :=
      AnalyticAt.comp (g := angleRegularFactor38 n m)
        (f := fun w : ℂ => ((psi,S psi),w)) haJoint
        (analyticAt_const.prod analyticAt_id)
    exact haOne.continuousAt.continuousWithinAt
  have hZ : 0 <= Br * Lib.c3w n m :=
    mul_nonneg hBr.le (Lib.c3w_nonneg n m)
  have hzetaBound : ∀ z ∈ segment ℝ a (muSeq psi m),
      ‖angleRegularFactor38 n m ((psi,S psi),z)‖ <=
        Br * Lib.c3w n m := by
    intro z hz
    have hzball : z ∈ ball (Cb m) (Rb m) :=
      hconv.segment_subset ha hmu hz
    exact (hfactor m hmn z hzball).2.1
  have hplacePsi := hplace psi (hsubp hpsi) n m hmn
  have hsigmaA :
      ‖Lib.sigmaOf (S psi) m - a‖ <=
        L * ‖a-b‖ := by
    rw [hsigma_m]
    simpa only [a, b, norm_sub_rev (lamMinus psi m) (lamPlus psi m)]
      using hplacePsi.1
  have hsigmaB :
      ‖Lib.sigmaOf (S psi) m - b‖ <=
        L * ‖a-b‖ := by
    rw [hsigma_m]
    simpa only [a, b, norm_sub_rev (lamMinus psi m) (lamPlus psi m)]
      using hplacePsi.2
  by_cases hnear : ‖muSeq psi m-a‖ <= ‖muSeq psi m-b‖
  · have hq := Lib.quadraticODE_terminal_magnitude_le38
      (ball (Cb m) (Rb m)) isOpen_ball hconv
      a b (muSeq psi m) (Lib.sigmaOf (S psi) m)
      ha hmu T (fun z => angleRegularFactor38 n m ((psi,S psi),z))
      hT hzeta hode L (Br * Lib.c3w n m) hL hZ
      hsigmaB hzetaBound hnear
    have htermActual :
        Real.sqrt (‖(muSeq psi m-a)*(muSeq psi m-b)‖) *
            ‖T (muSeq psi m)‖ =
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn pW‖ :=
      hterminal.symm.trans (congrArg norm hbeta)
    rw [htermActual] at hq
    have hmin :
        min ‖muSeq psi m-lamMinus psi m‖
          ‖muSeq psi m-lamPlus psi m‖ = ‖muSeq psi m-a‖ := by
      simpa only [a, b] using min_eq_left hnear
    rw [hmin]
    dsimp [C0]
    have hgapnorm : ‖a-b‖ = ‖b-a‖ := norm_sub_rev _ _
    rw [hgapnorm] at hq
    simpa only [pW, a, b, mul_assoc, mul_left_comm, mul_comm] using hq
  · have hnear' : ‖muSeq psi m-b‖ <= ‖muSeq psi m-a‖ :=
      (not_le.mp hnear).le
    have hode' : ∀ z ∈ ball (Cb m) (Rb m),
        (z-b)*(z-a)*deriv T z + (z-(b+a)/2)*T z =
          (Lib.sigmaOf (S psi) m-z) *
            angleRegularFactor38 n m ((psi,S psi),z) := by
      intro z hz
      have hh := hode z hz
      simpa only [add_comm a b, mul_comm (z-b) (z-a)] using hh
    have hzetaBound' : ∀ z ∈ segment ℝ b (muSeq psi m),
        ‖angleRegularFactor38 n m ((psi,S psi),z)‖ <=
          Br * Lib.c3w n m := by
      intro z hz
      have hzball : z ∈ ball (Cb m) (Rb m) :=
        hconv.segment_subset hb hmu hz
      exact (hfactor m hmn z hzball).2.1
    have hq := Lib.quadraticODE_terminal_magnitude_le38
      (ball (Cb m) (Rb m)) isOpen_ball hconv
      b a (muSeq psi m) (Lib.sigmaOf (S psi) m)
      hb hmu T (fun z => angleRegularFactor38 n m ((psi,S psi),z))
      hT hzeta hode' L (Br * Lib.c3w n m) hL hZ
      (by simpa only [norm_sub_rev b a] using hsigmaA) hzetaBound' hnear'
    have htermActual :
        Real.sqrt (‖(muSeq psi m-a)*(muSeq psi m-b)‖) *
            ‖T (muSeq psi m)‖ =
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn pW‖ :=
      hterminal.symm.trans (congrArg norm hbeta)
    have htermSwap :
        Real.sqrt (‖(muSeq psi m-b)*(muSeq psi m-a)‖) *
            ‖T (muSeq psi m)‖ =
          ‖gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m hmn pW‖ := by
      rw [mul_comm (muSeq psi m-b) (muSeq psi m-a)]
      exact htermActual
    rw [htermSwap] at hq
    have hmin :
        min ‖muSeq psi m-lamMinus psi m‖
          ‖muSeq psi m-lamPlus psi m‖ = ‖muSeq psi m-b‖ := by
      simpa only [a, b] using min_eq_right hnear'
    rw [hmin]
    dsimp [C0]
    simpa only [pW, a, b, mul_assoc, mul_left_comm, mul_comm] using hq

end
end NlsGge.GK38
