import Armstrong.Work.CartesianCorrectionOverlapSpec
import NlsGge.GK38.IsolatingPersistence

/-!
# Local analytic chart for the actual weighted correction

The same supplied W/F and existing analytic full completions are retained.
A single further persistence shrink, before all indices, exports the certified
fixed family and therefore actual Dirichlet placement. The selected-disc
weighted correction equals the fixed-disc expression, whose joint analyticity
can be evaluated at the actual mu. No regularity of the disc selectors and no
analytic labelling of the periodic endpoints is assumed.

Ordinary speculative infrastructure. Complex collapsed gaps remain included.
This file proves no uniform bound, eta at collapse, or Cartesian source closure.
-/
set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- One common local chart retains the actual family's numerator and full
completion, earns its fixed-family certificate, and makes the literal
selected-disc weighted exponent analytic by exact overlap transfer. -/
theorem gk16_same_family_actual_correction_chart38
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
      (∀ phi ∈ ball (realSlice u) delta,
        IsolatingFamily38 phi (discC (realSlice u)) (discR (realSlice u))) ∧
      ∀ n : ℤ, ∃ S : PotPair → Lib.L2Seq,
        AnalyticOnNhd ℂ S (ball (realSlice u) delta) ∧
        (∀ phi ∈ ball (realSlice u) delta,
          F n phi = p2Restrict38 n (S phi) ∧
          p6PsiNumerator38 n (F n) phi = p2FullNumerator38 n (S phi) ∧
          abelianPeriod38 n phi (p2FullNumerator38 n (S phi)) =
            2*(Real.pi : ℂ)) ∧
        AnalyticOnNhd ℂ
          (fun p : PotPair × ℂ => gk16OwnCorrectionCoefficient38
            p.1 n (S p.1) (discC (realSlice u) n) (discR (realSlice u) n) p.2)
          (ball (realSlice u) delta ×ˢ
            ball (discC (realSlice u) n) (discR (realSlice u) n)) ∧
        (∀ phi ∈ ball (realSlice u) delta,
          gk16TerminalRoot38 n phi *
            gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
              (discC phi n) (discR phi n) (muSeq phi n) =
          gk16TerminalRoot38 n phi *
            gk16OwnCorrectionCoefficient38 phi n (S phi)
              (discC (realSlice u) n) (discR (realSlice u) n) (muSeq phi n)) ∧
        AnalyticOnNhd ℂ
          (fun phi : PotPair => gk16TerminalRoot38 n phi *
            gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
              (discC phi n) (discR phi n) (muSeq phi n))
          (ball (realSlice u) delta) := by
  have huGK : realSlice u ∈ gkW := hWgk (hreal (mem_range_self u))
  let C : ℤ → ℂ := discC (realSlice u)
  let rho : ℤ → ℝ := discR (realSlice u)
  have hbase : IsolatingFamily38 (realSlice u) C rho :=
    isolating_family38 (realSlice u) huGK
  obtain ⟨delta0,hdelta0,hdelta0W,hbranches⟩ :=
    gk16_same_family_correction38 W hWopen hreal hWgk F hFanalytic hFn hFinv
      hperiod hFreal u
  obtain ⟨r,hr,c,N,hgeom,hpersist⟩ :=
    fixed_family_persistence38 (realSlice u) C rho hbase
  let delta : ℝ := min delta0 r
  have hdelta : 0 < delta := lt_min hdelta0 hr
  have hsub0 : ball (realSlice u) delta ⊆ ball (realSlice u) delta0 :=
    ball_subset_ball (min_le_left _ _)
  have hsubr : ball (realSlice u) delta ⊆ ball (realSlice u) r :=
    ball_subset_ball (min_le_right _ _)
  have hsubW : ball (realSlice u) delta ⊆ W := hsub0.trans hdelta0W
  have hfamily : ∀ phi ∈ ball (realSlice u) delta, IsolatingFamily38 phi C rho :=
    fun phi hphi => ⟨c,N,hgeom,hpersist phi (hsubr hphi)⟩
  refine ⟨delta,hdelta,hsubW,hfamily,?_⟩
  intro n
  obtain ⟨S,hS,hSspec,hTjoint,_hODE⟩ := hbranches n
  have hTsmall : AnalyticOnNhd ℂ
      (fun p : PotPair × ℂ => gk16OwnCorrectionCoefficient38
        p.1 n (S p.1) (C n) (rho n) p.2)
      (ball (realSlice u) delta ×ˢ ball (C n) (rho n)) :=
    fun p hp => hTjoint p ⟨hsub0 hp.1,hp.2⟩
  have heq : ∀ phi ∈ ball (realSlice u) delta,
      gk16TerminalRoot38 n phi *
        gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
          (discC phi n) (discR phi n) (muSeq phi n) =
      gk16TerminalRoot38 n phi *
        gk16OwnCorrectionCoefficient38 phi n (S phi) (C n) (rho n) (muSeq phi n) := by
    intro phi hphi
    have hown : abelianPeriod38 n phi (p6PsiNumerator38 n (F n) phi) =
        2*(Real.pi : ℂ) := by
      exact (hperiod n phi (hsubW hphi) n).trans (if_pos (show n = n from rfl))
    exact gk16_actual_original_fixed_weighted_correction38
      n F ⟨phi,hWgk (hsubW hphi)⟩ (S phi) (hSspec phi (hsub0 hphi)).1
      C rho (hfamily phi hphi) hown
  have hfixed : AnalyticOnNhd ℂ
      (fun phi : PotPair => gk16TerminalRoot38 n phi *
        gk16OwnCorrectionCoefficient38 phi n (S phi) (C n) (rho n) (muSeq phi n))
      (ball (realSlice u) delta) := by
    intro phi hphi
    have hphiGK : phi ∈ gkW := hWgk (hsubW hphi)
    have hmu : muSeq phi n ∈ ball (C n) (rho n) := by
      obtain ⟨c',N',hgeom',hspec'⟩ := hfamily phi hphi
      exact (hspec'.1 n).2.1
    have hmap : AnalyticAt ℂ (fun psi : PotPair => (psi,muSeq psi n)) phi :=
      analyticAt_id.prod (analyticOnNhd_muSeq_complex38 n phi hphiGK)
    have hTmu : AnalyticAt ℂ
        (fun psi : PotPair =>
          gk16OwnCorrectionCoefficient38 psi n (S psi) (C n) (rho n) (muSeq psi n)) phi :=
      AnalyticAt.comp
        (g := fun p : PotPair × ℂ =>
          gk16OwnCorrectionCoefficient38 p.1 n (S p.1) (C n) (rho n) p.2)
        (f := fun psi : PotPair => (psi,muSeq psi n)) (x := phi)
        (hTsmall (phi,muSeq phi n) ⟨hphi,hmu⟩) hmap
    exact (gk16_terminal_root_analytic38 n phi hphiGK).mul hTmu
  refine ⟨S,hS.mono hsub0,(fun phi hphi => hSspec phi (hsub0 hphi)),
    hTsmall,heq,?_⟩
  intro phi hphi
  apply (hfixed phi hphi).congr
  filter_upwards [isOpen_ball.mem_nhds hphi] with psi hpsi
  exact (heq psi hpsi).symm

end
end NlsGge.GK38
