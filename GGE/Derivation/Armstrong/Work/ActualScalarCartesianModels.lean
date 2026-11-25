import Armstrong.Work.CartesianEtaPathSpec
import Armstrong.Work.CartesianCorrectionLocalSpec

/-!
# Actual scalar Cartesian models and source continuation

SPECULATIVE_PARENT_UNACCEPTED, ledger Z-006. The direct ambient formulas below
use the same supplied normalized family and its literal original selected-disc
coefficient. Their source characterization is restricted to that family's W.
The actual positive omitted quotient gives plus exponent -H*R and minus +H*R.
No printed Section16 collapsed sign formula or additive eta at collapse is used.
One common real-centered complex chart supplies analytic continuation through
all complex collapsed gaps. Uniform norm bounds and x/y remain separate work.
-/

set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Literal ambient plus model. Source interpretation is asserted only on the
supplied normalized family's W; outside W this is only the displayed formula. -/
def gk16ActualScalarZPlus38
    (F : (n : ℤ) → PotPair → P2Space38 n) (n : ℤ) (phi : PotPair) : ℂ :=
  (2*(tauN phi n-muSeq phi n)+2*gk16TerminalRoot38 n phi) *
    Complex.exp (-(gk16TerminalRoot38 n phi *
      gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
        (discC phi n) (discR phi n) (muSeq phi n)))

/-- Literal ambient minus model, with the same original coefficient and F. -/
def gk16ActualScalarZMinus38
    (F : (n : ℤ) → PotPair → P2Space38 n) (n : ℤ) (phi : PotPair) : ℂ :=
  (2*(tauN phi n-muSeq phi n)-2*gk16TerminalRoot38 n phi) *
    Complex.exp (gk16TerminalRoot38 n phi *
      gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
        (discC phi n) (discR phi n) (muSeq phi n))

/-- The exact product identity includes all complex collapsed gaps. -/
theorem gk16_actual_scalar_models_product38
    (F : (n : ℤ) → PotPair → P2Space38 n) (n : ℤ)
    (phi : PotPair) (hphi : phi ∈ gkW) :
    gk16ActualScalarZPlus38 F n phi * gk16ActualScalarZMinus38 F n phi =
      gamma2 phi n := by
  unfold gk16ActualScalarZPlus38 gk16ActualScalarZMinus38
  rw [mul_mul_mul_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  exact gk16_terminal_prefactors_product38 n phi hphi


/-- Every original noncollapsed rooted path has an additive eta integral, and
both literal models equal its signed gap-scaled exponentials. -/
theorem gk16_actual_scalar_models_path38
    (W : Set PotPair) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (n : ℤ) (phi : {chi : PotPair // chi ∈ W})
    (hgap : lamMinus phi.1 n ≠ lamPlus phi.1 n) :
    ∀ p : GKRootedPiecewisePath38 ⟨phi.1,hWgk phi.2⟩ n, ∃ eta : ℂ,
      HasGKImproperPathIntegral38 n n F ⟨phi.1,hWgk phi.2⟩ p eta ∧
      gk16ActualScalarZPlus38 F n phi.1 =
        (lamPlus phi.1 n-lamMinus phi.1 n)*Complex.exp (Complex.I*eta) ∧
      gk16ActualScalarZMinus38 F n phi.1 =
        (lamPlus phi.1 n-lamMinus phi.1 n)*Complex.exp (-Complex.I*eta) := by
  intro p
  have hown : abelianPeriod38 n phi.1 (p6PsiNumerator38 n (F n) phi.1) =
      2*(Real.pi : ℂ) :=
    (hperiod n phi.1 phi.2 n).trans (if_pos (show n = n from rfl))
  have hnum : p6PsiNumerator38 n (F n) phi.1 =
      p2FullNumerator38 n (p2Extend38 n (F n phi.1)) := rfl
  obtain ⟨eta, heta, hplus, hminus⟩ :=
    gk16_diagonal_original_path_exponential38 n F ⟨phi.1,hWgk phi.2⟩
      (p2Extend38 n (F n phi.1)) hnum hown hgap p
  have htau : tauN phi.1 n = (lamMinus phi.1 n+lamPlus phi.1 n)/2 := by
    rw [tauN_value38 phi.1 (hWgk phi.2) n]
    ring
  refine ⟨eta,heta,?_,?_⟩
  · simpa only [gk16ActualScalarZPlus38,htau,neg_mul] using hplus
  · simpa only [gk16ActualScalarZMinus38,htau] using hminus


/-- Any genuine additive improper value on that path gives the same two
models; no eta representative is selected in their definitions. -/
theorem gk16_actual_scalar_models_of_path_integral38
    (W : Set PotPair) (hWgk : W ⊆ gkW)
    (F : (n : ℤ) → PotPair → P2Space38 n)
    (hperiod : ∀ n : ℤ, ∀ phi : PotPair, phi ∈ W → ∀ m : ℤ,
      abelianPeriod38 m phi (p6PsiNumerator38 n (F n) phi) =
        if m = n then 2*(Real.pi : ℂ) else 0)
    (n : ℤ) (phi : {chi : PotPair // chi ∈ W})
    (hgap : lamMinus phi.1 n ≠ lamPlus phi.1 n)
    (p : GKRootedPiecewisePath38 ⟨phi.1,hWgk phi.2⟩ n) (eta : ℂ)
    (heta : HasGKImproperPathIntegral38 n n F ⟨phi.1,hWgk phi.2⟩ p eta) :
    gk16ActualScalarZPlus38 F n phi.1 =
      (lamPlus phi.1 n-lamMinus phi.1 n)*Complex.exp (Complex.I*eta) ∧
    gk16ActualScalarZMinus38 F n phi.1 =
      (lamPlus phi.1 n-lamMinus phi.1 n)*Complex.exp (-Complex.I*eta) := by
  obtain ⟨eta0, heta0, hplus, hminus⟩ :=
    gk16_actual_scalar_models_path38 W hWgk F hperiod n phi hgap p
  letI : NeBot (nhdsWithin ((0 : ℝ),(0 : ℝ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ q.1+q.2 < 1}) :=
    rawBetaImproperApproachNeBot38
  have heq : eta0 = eta := tendsto_nhds_unique heta0.2 heta.2
  subst eta0
  exact ⟨hplus,hminus⟩


/-- One complex neighborhood before all indices makes both actual scalar
models analytic, including every complex collapsed gap in that neighborhood. -/
theorem gk16_same_family_scalar_models_analytic38
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
    (u : PhysicalL2) :
    ∃ delta : ℝ, 0 < delta ∧ ball (realSlice u) delta ⊆ W ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (gk16ActualScalarZPlus38 F n) (ball (realSlice u) delta) ∧
        AnalyticOnNhd ℂ (gk16ActualScalarZMinus38 F n) (ball (realSlice u) delta) := by
  obtain ⟨delta,hdelta,hsubW,_hfamily,hbranches⟩ :=
    gk16_same_family_actual_correction_chart38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u
  have hsubGK : ball (realSlice u) delta ⊆ gkW := hsubW.trans hWgk
  refine ⟨delta,hdelta,hsubW,?_⟩
  intro n
  obtain ⟨_S,_hS,_hSspec,_hjoint,_heq,hweighted⟩ := hbranches n
  have hpref := gk16_terminal_prefactors_analytic38 n
  constructor
  · change AnalyticOnNhd ℂ
      (fun phi : PotPair =>
        (2*(tauN phi n-muSeq phi n)+2*gk16TerminalRoot38 n phi) *
          Complex.exp (-(gk16TerminalRoot38 n phi *
            gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
              (discC phi n) (discR phi n) (muSeq phi n))))
      (ball (realSlice u) delta)
    exact (hpref.1.mono hsubGK).mul (hweighted.neg.cexp)
  · change AnalyticOnNhd ℂ
      (fun phi : PotPair =>
        (2*(tauN phi n-muSeq phi n)-2*gk16TerminalRoot38 n phi) *
          Complex.exp (gk16TerminalRoot38 n phi *
            gk16OwnCorrectionCoefficient38 phi n (p2Extend38 n (F n phi))
              (discC phi n) (discR phi n) (muSeq phi n)))
      (ball (realSlice u) delta)
    exact (hpref.2.mono hsubGK).mul hweighted.cexp


/-- Every sequence of genuine noncollapsed source path exponentials converges
to the literal continued models at any complex collapsed point in one common
chart. No additive eta value or convergence is asserted at collapse. -/
theorem gk16_same_family_scalar_models_collapsed_limit38
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
    (u : PhysicalL2) :
    ∃ delta : ℝ, 0 < delta ∧ ball (realSlice u) delta ⊆ W ∧
      ∀ (n : ℤ) (phi : PotPair), phi ∈ ball (realSlice u) delta →
        gamma2 phi n = 0 →
        ∀ (psi : ℕ → {chi : PotPair // chi ∈ W})
          (p : ∀ k : ℕ, GKRootedPiecewisePath38
            ⟨(psi k).1,hWgk (psi k).2⟩ n) (eta : ℕ → ℂ),
          (∀ k : ℕ, lamMinus (psi k).1 n ≠ lamPlus (psi k).1 n) →
          (∀ k : ℕ, HasGKImproperPathIntegral38 n n F
            ⟨(psi k).1,hWgk (psi k).2⟩ (p k) (eta k)) →
          Tendsto (fun k : ℕ => (psi k).1) atTop (nhds phi) →
          Tendsto (fun k : ℕ => (lamPlus (psi k).1 n-lamMinus (psi k).1 n) *
            Complex.exp (Complex.I*eta k)) atTop
              (nhds (gk16ActualScalarZPlus38 F n phi)) ∧
          Tendsto (fun k : ℕ => (lamPlus (psi k).1 n-lamMinus (psi k).1 n) *
            Complex.exp (-Complex.I*eta k)) atTop
              (nhds (gk16ActualScalarZMinus38 F n phi)) := by
  obtain ⟨delta,hdelta,hsubW,hanalytic⟩ :=
    gk16_same_family_scalar_models_analytic38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal u
  refine ⟨delta,hdelta,hsubW,?_⟩
  intro n phi hphi _hcollapsed psi p eta hgap heta hlim
  have hvalues : ∀ k : ℕ,
      gk16ActualScalarZPlus38 F n (psi k).1 =
        (lamPlus (psi k).1 n-lamMinus (psi k).1 n)*Complex.exp (Complex.I*eta k) ∧
      gk16ActualScalarZMinus38 F n (psi k).1 =
        (lamPlus (psi k).1 n-lamMinus (psi k).1 n)*Complex.exp (-Complex.I*eta k) :=
    fun k => gk16_actual_scalar_models_of_path_integral38 W hWgk F hperiod
      n (psi k) (hgap k) (p k) (eta k) (heta k)
  have hplus := ((hanalytic n).1 phi hphi).continuousAt.tendsto.comp hlim
  have hminus := ((hanalytic n).2 phi hphi).continuousAt.tendsto.comp hlim
  exact ⟨hplus.congr (fun k => (hvalues k).1),
    hminus.congr (fun k => (hvalues k).2)⟩


end
end NlsGge.GK38
