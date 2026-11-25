import Armstrong.Work.RawEtaOwnQuotient

/-!
# Same-family own-gap quotient branch

This composes the accepted normalized same-W/same-F family with one open input
tube that preserves every root in the original isolating family. It supplies the
nonvanishing analytic own-gap quotient and its exact nonzero own period.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk16_same_family_own_quotient38
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
    ∃ delta : ℝ, 0 < delta ∧ ball (realSlice u) delta ⊆ W ∧
      ∀ n : ℤ, ∃ S : PotPair → Lib.L2Seq,
        AnalyticOnNhd ℂ S (ball (realSlice u) delta) ∧
        ∀ phi ∈ ball (realSlice u) delta,
          F n phi = p2Restrict38 n (S phi) ∧
          p6PsiNumerator38 n (F n) phi = p2FullNumerator38 n (S phi) ∧
          (∀ k : ℤ,
            Lib.sigmaOf (S phi) k ∈
              ball (discC (realSlice u) k) (discR (realSlice u) k)) ∧
          AnalyticOnNhd ℂ
            (fun z => p2OmittedRatio38 n ((phi,S phi),z))
            (closedBall (discC (realSlice u) n)
              (discR (realSlice u) n)) ∧
          (∀ z ∈ closedBall (discC (realSlice u) n)
              (discR (realSlice u) n),
            p2OmittedRatio38 n ((phi,S phi),z) ≠ 0) ∧
          abelianPeriod38 n phi (p2FullNumerator38 n (S phi)) =
            2 * (Real.pi : ℂ) ∧
          (∀ z : ℂ, (phi,z) ∈ rootDomain38 →
            p6PsiNumerator38 n (F n) phi z / canonRoot38 phi z =
              Complex.I * p2OmittedRatio38 n ((phi,S phi),z) /
                stdRoot38 (tauN phi n) (gamma2 phi n) z) := by
  have huW : realSlice u ∈ W := hreal (mem_range_self u)
  have huGK : realSlice u ∈ gkW := hWgk huW
  let C : ℤ → ℂ := discC (realSlice u)
  let R : ℤ → ℝ := discR (realSlice u)
  have hfam0 : IsolatingFamily38 (realSlice u) C R := by
    simpa only [C,R] using isolating_family38 (realSlice u) huGK
  obtain ⟨V,hVopen,hKV,hVplace⟩ :=
    gk16_compact_input_all_own_disc_tube38 u C R hfam0
  obtain ⟨rho,hrho,hrhoW,hbranches⟩ :=
    gk151_same_family_common_input_tube38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u V hVopen hKV
  obtain ⟨r,hr,c,N,hgeom,hpersist⟩ :=
    fixed_family_persistence38 (realSlice u) C R hfam0
  let delta : ℝ := min rho r
  have hdelta : 0 < delta := lt_min hrho hr
  have hsubrho : ball (realSlice u) delta ⊆ ball (realSlice u) rho :=
    ball_subset_ball (min_le_left _ _)
  have hsubr : ball (realSlice u) delta ⊆ ball (realSlice u) r :=
    ball_subset_ball (min_le_right _ _)
  refine ⟨delta,hdelta,hsubrho.trans hrhoW,?_⟩
  intro n
  obtain ⟨t,ht,htzero,S,hSbase,hSan,hSspec⟩ := hbranches n
  refine ⟨S,hSan.mono hsubrho,?_⟩
  intro phi hphi
  obtain ⟨hSV,hFrestrict,hSn,hcoords,hnum,hroots,hperiods⟩ :=
    hSspec phi (hsubrho hphi)
  have hphiW : phi ∈ W := hrhoW (hsubrho hphi)
  have hphiGK : phi ∈ gkW := hWgk hphiW
  have hfamphi : IsolatingFamily38 phi C R :=
    ⟨c,N,hgeom,hpersist phi (hsubr hphi)⟩
  have hsigma : ∀ k : ℤ,
      Lib.sigmaOf (S phi) k ∈ ball (C k) (R k) :=
    hVplace (S phi) hSV
  have han := gk16_own_ratio_analytic38
    n phi hphiGK C R hfamphi (S phi)
  have hnz : ∀ z ∈ closedBall (C n) (R n),
      p2OmittedRatio38 n ((phi,S phi),z) ≠ 0 := by
    intro z hz
    exact gk16_own_ratio_ne_zero38 n phi hphiGK C R hfamphi
      (S phi) (fun k => ball_subset_closedBall (hsigma k)) z hz
  have hown : abelianPeriod38 n phi
      (p2FullNumerator38 n (S phi)) = 2 * (Real.pi : ℂ) := by
    simpa using hperiods n
  refine ⟨hFrestrict,hnum,?_,han,hnz,hown,?_⟩
  · simpa only [C,R] using hsigma
  · intro z hz
    rw [hnum]
    exact gk16_own_factorization38 n (S phi) phi z hz

end
end NlsGge.GK38
