import Armstrong.Work.RealQuadraticODEInvariant
import Armstrong.Work.RawBetaOriginalValue
import Armstrong.Frozen.RawBetaAnalytic.gkSourceBeta_characterization38
import Armstrong.Work.RawBetaSourceSum
import NlsGge.GK38.AbelianRealImage
import NlsGge.GK38.DirichletRealBridge
import NlsGge.GK38.RealTypeSpectrum

/-!
# Literal source beta real trace

SPECULATIVE_PARENT_UNACCEPTED, ACTUAL-BETA-RT-013. The SAME original W/F and
actual real normalized family are retained. The genuine full-characteristic
coefficient is analytic on the original filled disc. Its real-axis weighted
ODE invariant, actual real terminal antidiscriminant, and exact all-path
source characterization prove literal beta reality, including collapsed gaps
and terminal tips. The coupled row-sum statement earns actual absolute
summability from A8 before mapping the imaginary part through its literal tsum.
This module does not prove own weighted-correction reality, eta real trace,
Cartesian conjugation, outer square summability, or a global map/inverse.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- The original all-path offdiagonal source value is real on the real slice. -/
theorem gkSourceBeta_real_trace38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi,F n phi) = 0)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (n m : ℤ) (hmn : m ≠ n) (u : PhysicalL2) :
    (gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
      n m hmn ⟨realSlice u,hreal (mem_range_self u)⟩).im = 0 := by
  let phi : PotPair := realSlice u
  have huW : phi ∈ W := hreal (mem_range_self u)
  have hphi : phi ∈ gkW := realSlice_mem_gkW u
  obtain ⟨s,_hsCube,_hsZero,hFs⟩ := hFreal n u
  have hseq : ∀ k : ℤ, (p2Extend38 n (F n phi) k).im = 0 := by
    intro k
    by_cases hk : k = n
    · subst k
      simp only [p2Extend_self38,Complex.zero_im]
    · rw [p2Extend_at38 n (F n phi) ⟨k,hk⟩]
      change (F n (realSlice u) ⟨k,hk⟩).im = 0
      rw [hFs,p3RealInclude_apply38,Complex.ofReal_im]
  have hPsiReal : ∀ x : ℝ,
      (p6PsiNumerator38 n (F n) phi (x : ℂ)).im = 0 := by
    intro x
    exact p2FullNumerator_real38 n (p2Extend38 n (F n phi)) hseq x
  have hper :
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) = 0 := by
    simpa only [ite_eq_right hmn] using hperiod n phi huW m
  obtain ⟨R,hR,hRode⟩ :=
    rawBetaPsiCoefficientOfZeroPeriod38 n m (F n) phi hphi hper
  let C : ℤ → ℂ := discC phi
  let rho : ℤ → ℝ := discR phi
  have hfam : IsolatingFamily38 phi C rho := isolating_family38 phi hphi
  have hfamCopy := hfam
  obtain ⟨_c,_N,_hgeom,hspec⟩ := hfamCopy
  have haDisc : lamMinus phi m ∈ ball (C m) (rho m) :=
    (hspec.1 m).1 (left_mem_segment ℝ _ _)
  have hxDisc : muSeq phi m ∈ ball (C m) (rho m) := (hspec.1 m).2.1
  let a : ℝ := NlsGge.SpectralFoundations.actualGapLowerAllE02_38 u m
  have hminus : lamMinus phi m = (a : ℂ) := (lamPlus_real u m).2
  have hmu : muSeq phi m = (gkMu u m : ℂ) := muSeq_eq_gkMu38 u m
  let U : Set ℝ := {x : ℝ | (x : ℂ) ∈ ball (C m) (rho m)}
  have hU : IsOpen U := isOpen_ball.preimage Complex.continuous_ofReal
  have hUc : IsPreconnected U :=
    ((convex_ball (C m) (rho m)).linear_preimage
      Complex.ofRealCLM.toLinearMap).isPreconnected
  have ha : a ∈ U := by
    change (a : ℂ) ∈ ball (C m) (rho m)
    rw [← hminus]
    exact haDisc
  have hx : gkMu u m ∈ U := by
    change (gkMu u m : ℂ) ∈ ball (C m) (rho m)
    rw [← hmu]
    exact hxDisc
  have hQReal : ∀ x : ℝ, (perChar phi (x : ℂ)).im = 0 := by
    intro x
    have hD : (discrim phi (x : ℂ)).im = 0 :=
      (dirichlet_real_characteristic38 u x).2.2
    have hfour : (4 : ℂ).im = 0 := by norm_num
    simp only [perChar_eq,pow_two,Complex.sub_im,Complex.mul_im,hD,hfour,
      zero_mul,mul_zero,add_zero,sub_zero]
  have hQa : perChar phi (a : ℂ) = 0 := by
    rw [← hminus]
    exact rawBetaPerCharLowerTipZero38 ⟨phi,hphi⟩ m
  have hInv := gk_real_axis_weighted_ode_invariant38 U hU hUc
    (perChar phi) R (p6PsiNumerator38 n (F n) phi)
    (fun x _hx =>
      (analyticOnNhd_perChar_z phi (x : ℂ) (mem_univ _)).differentiableAt)
    (fun x hx => (hR (x : ℂ) hx).differentiableAt)
    (fun x _hx => hQReal x) (fun x _hx => hPsiReal x)
    (fun x hx => hRode (x : ℂ) hx) a (gkMu u m) ha hx hQa
  have hweighted : (perChar phi (muSeq phi m)).re *
      ((R (muSeq phi m)).im)^2 = 0 := by
    rw [hmu]
    exact hInv
  let delta : ℂ := antiDiscrim phi (muSeq phi m)
  have hdeltaIm : delta.im = 0 := by
    change (antiDiscrim phi (muSeq phi m)).im = 0
    rw [hmu]
    exact (dirichlet_real_characteristic38 u (gkMu u m)).2.1
  have hdeltaSq : delta^2 = perChar phi (muSeq phi m) :=
    rawBetaDirichletTerminalSquare38 ⟨phi,hphi⟩ m
  have hdeltaSqRe : delta.re^2 = (perChar phi (muSeq phi m)).re := by
    have heq := congrArg Complex.re hdeltaSq
    simpa only [pow_two,Complex.mul_re,hdeltaIm,mul_zero,sub_zero] using heq
  have hsquare : (delta.re * (R (muSeq phi m)).im)^2 = 0 := by
    rw [mul_pow,hdeltaSqRe]
    exact hweighted
  have hvalueReal : (delta * R (muSeq phi m)).im = 0 := by
    simp only [Complex.mul_im,hdeltaIm,zero_mul,add_zero]
    exact sq_eq_zero_iff.mp hsquare
  have hvalue : GKSourceBetaValue38 n m hmn F ⟨phi,hphi⟩
      (delta * R (muSeq phi m)) :=
    rawBetaSourceValueOfFixedCoefficient38 n m hmn F ⟨phi,hphi⟩ C rho
      hfam hper R hR hRode
  have hchar := gkSourceBeta_characterization38 W hWopen hreal hWgk F
    hFanalytic hFn hperiod n m hmn (⟨phi,huW⟩ : {psi : PotPair // psi ∈ W})
  have heq : delta * R (muSeq phi m) =
      gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
        n m hmn ⟨phi,huW⟩ := hchar.2.1 _ hvalue
  change (gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
    n m hmn ⟨phi,huW⟩).im = 0
  rw [← heq]
  exact hvalueReal

/-- The literal convergent offdiagonal source row has real sum. -/
theorem gk151_source_beta_sum_real_trace38
    (W : Set PotPair) (hWopen : IsOpen W)
    (hreal : range realSlice ⊆ W) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hFanalytic : ∀ n : ℤ, AnalyticOnNhd ℂ (F n) W)
    (hFn : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      p2Fn38 n (phi,F n phi) = 0)
    (hFinv : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W →
      (fderiv ℂ (fun y : P2Space38 n => p2Fn38 n (phi,y))
        (F n phi)).IsInvertible)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (hFreal : ∀ (n : ℤ) (u : PhysicalL2), ∃ t : P3RealSpace38 n,
      t ∈ p5RealGapCube38 n u ∧ p3RealFn38 n u t = 0 ∧
        F n (realSlice u) = p3RealInclude38 n t)
    (n : ℤ) (u : PhysicalL2) :
    Summable (fun m : P2Index38 n =>
      ‖gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
        n m.1 m.2 ⟨realSlice u,hreal (mem_range_self u)⟩‖) ∧
    (∑' m : P2Index38 n,
      gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
        n m.1 m.2 ⟨realSlice u,hreal (mem_range_self u)⟩).im = 0 := by
  obtain ⟨Wbeta,_hWbetaOpen,hrealBeta,_hBetaW,hsum,_hunif,_hanalytic,_hdecay⟩ :=
    gk151_source_beta_series38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal
  let phi : {psi : PotPair // psi ∈ W} :=
    ⟨realSlice u,hreal (mem_range_self u)⟩
  have hsumNorm : Summable (fun m : P2Index38 n =>
      ‖gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
        n m.1 m.2 phi‖) := hsum n phi (hrealBeta (mem_range_self u))
  refine ⟨hsumNorm,?_⟩
  rw [Complex.im_tsum hsumNorm.of_norm]
  have hzero : ∀ m : P2Index38 n,
      (gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
        n m.1 m.2 phi).im = 0 := by
    intro m
    exact gkSourceBeta_real_trace38 W hWopen hreal hWgk F
      hFanalytic hFn hperiod hFreal n m.1 m.2 u
  simp only [hzero,tsum_zero]

end
end NlsGge.GK38
