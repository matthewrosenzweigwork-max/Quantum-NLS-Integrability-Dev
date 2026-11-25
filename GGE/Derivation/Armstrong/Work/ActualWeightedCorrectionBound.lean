import Armstrong.Work.RawEtaUniformSourceBound
import Armstrong.Work.CorrectionCircleGeometrySpec
import Armstrong.Work.CorrectionCauchyBoundSpec
import Armstrong.Work.CartesianCorrectionOverlapSpec
import Armstrong.Work.RawBetaSumSpectralMass

/-!
# Actual same-family weighted correction bound

A common real-centered neighborhood bounds the literal original-disc weighted
correction at the actual Dirichlet terminal, uniformly in every signed mode.
The fixed-disc completion is retained from the actual q producer and transferred
by the earned weighted-overlap identity. All parent candidates remain subject
to their separate acceptance gates; this file does not close GK16.4.
-/

set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem gk16_same_family_actual_weighted_correction_bound38
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
    ∃ delta K : ℝ, 0 < delta ∧ 0 ≤ K ∧ ball (realSlice u) delta ⊆ W ∧
      ∀ phi ∈ ball (realSlice u) delta, ∀ n : ℤ,
        ‖gk16TerminalRoot38 n phi *
          gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
            (discC phi n) (discR phi n) (muSeq phi n)‖ ≤ K := by
  classical
  have huGK : realSlice u ∈ gkW := hWgk (hreal (mem_range_self u))
  obtain ⟨rq, H, hrq, hH, hqW, _hqFamily, hbranches⟩ :=
    gk16_same_family_own_ratio_closed_bound38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u
  obtain ⟨rg, rmax, s0, d0, hrg, hrmax, hs0, hd0, _hgW, hgeometry⟩ :=
    gk16_fixed_real_circle_uniform_geometry38 u
  obtain ⟨Um, hUm, _hUmg, M, hM, hmass⟩ :=
    gk151BetaMass_local_l2_38 (realSlice u) huGK
  obtain ⟨rm, hrm, hrmU⟩ := Metric.mem_nhds_iff.mp hUm
  let delta : ℝ := min rq (min rg rm)
  have hdelta : 0 < delta := lt_min hrq (lt_min hrg hrm)
  have hsubq : ball (realSlice u) delta ⊆ ball (realSlice u) rq :=
    ball_subset_ball (min_le_left _ _)
  have hsubg : ball (realSlice u) delta ⊆ ball (realSlice u) rg :=
    ball_subset_ball ((min_le_right rq (min rg rm)).trans (min_le_left rg rm))
  have hsubm : ball (realSlice u) delta ⊆ Um :=
    (ball_subset_ball
      ((min_le_right rq (min rg rm)).trans (min_le_right rg rm))).trans hrmU
  let L : ℝ := 2*Real.pi*rmax^2*(H+1)/(s0^2*d0)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨delta, Real.sqrt M * L, hdelta,
    mul_nonneg (Real.sqrt_nonneg M) hL, hsubq.trans hqW, ?_⟩
  intro phi hphi n
  have hphiQ := hsubq hphi
  have hphiG := hsubg hphi
  have hphiW : phi ∈ W := hqW hphiQ
  have hphiGK : phi ∈ gkW := hWgk hphiW
  obtain ⟨S, _hSan, hSspec⟩ := hbranches n
  obtain ⟨hrestrict, _hnum, _hperiods, hq⟩ := hSspec phi hphiQ
  obtain ⟨hfamily, hgeom⟩ := hgeometry phi hphiG
  obtain ⟨hradius, hcircle⟩ := hgeom n
  have hrho : 0 < discR (realSlice u) n := isolating_radius_pos38 hfamily n
  have hcircleMem (theta : ℝ) :
      circleMap (discC (realSlice u) n) (discR (realSlice u) n) theta ∈
        sphere (discC (realSlice u) n) (discR (realSlice u) n) :=
    circleMap_mem_sphere _ hrho.le theta
  have hR :
      ‖gk16OwnCorrectionCoefficient38 phi n (S phi)
        (discC (realSlice u) n) (discR (realSlice u) n) (muSeq phi n)‖ ≤ L :=
    gk16_own_correction_cauchy_bound38 H rmax s0 d0 hH hs0 hd0
      phi hphiGK n (S phi) (discC (realSlice u)) (discR (realSlice u))
      hfamily hradius
      (fun theta _htheta => hq _ (sphere_subset_closedBall (hcircleMem theta)))
      (fun theta _htheta => (hcircle _ (hcircleMem theta)).1)
      (fun theta _htheta => (hcircle _ (hcircleMem theta)).2)
  obtain ⟨hsum, hsumM⟩ := hmass phi (hsubm hphi)
  have hterm : ‖gk151BetaMass38 phi n‖^2 ≤
      ∑' m : ℤ, ‖gk151BetaMass38 phi m‖^2 := by
    simpa only [Finset.sum_singleton] using
      hsum.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
  have hpointSq : ‖gk151BetaMass38 phi n‖^2 ≤ M := hterm.trans hsumM
  have hpoint : ‖gk151BetaMass38 phi n‖ ≤ Real.sqrt M := by
    nlinarith only [hpointSq, Real.sq_sqrt hM, Real.sqrt_nonneg M]
  have hterminal : ‖gk16TerminalRoot38 n phi‖ ≤ Real.sqrt M := by
    apply le_trans _ hpoint
    rw [norm_gk151BetaMass38]
    have hh := gk16_terminal_root_norm38 n phi hphiGK
    rw [gamma2_value38 phi hphiGK n, norm_pow,
      Real.sqrt_sq (norm_nonneg _)] at hh
    nlinarith only [hh, norm_nonneg (lamPlus phi n-lamMinus phi n)]
  have hown : abelianPeriod38 n phi (p6PsiNumerator38 n (F n) phi) =
      2*(Real.pi : ℂ) := by
    exact (hperiod n phi hphiW n).trans (if_pos (show n = n from rfl))
  have htransfer := gk16_actual_original_fixed_weighted_correction38 n F
    ⟨phi,hphiGK⟩ (S phi) hrestrict (discC (realSlice u)) (discR (realSlice u))
    hfamily hown
  calc
    ‖gk16TerminalRoot38 n phi *
        gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
          (discC phi n) (discR phi n) (muSeq phi n)‖ =
        ‖gk16TerminalRoot38 n phi *
          gk16OwnCorrectionCoefficient38 phi n (S phi)
            (discC (realSlice u) n) (discR (realSlice u) n) (muSeq phi n)‖ :=
      congrArg norm htransfer
    _ = ‖gk16TerminalRoot38 n phi‖ *
        ‖gk16OwnCorrectionCoefficient38 phi n (S phi)
          (discC (realSlice u) n) (discR (realSlice u) n) (muSeq phi n)‖ :=
      norm_mul _ _
    _ ≤ Real.sqrt M * L :=
      mul_le_mul hterminal hR (norm_nonneg _) (Real.sqrt_nonneg M)

end
end NlsGge.GK38
