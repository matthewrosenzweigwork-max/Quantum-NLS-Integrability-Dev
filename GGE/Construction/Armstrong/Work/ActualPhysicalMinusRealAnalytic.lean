import Armstrong.Work.ActualCartesianHilbertModels
import NlsGge.GK38.PairPotential
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars

/-!
# Real analyticity of the same physical minus representative

SPECULATIVE_UNACCEPTED_H14_XY_PARENTS, task REALAN020.
Exactly one reviewed ordinary theorem, zero new definitions or instances.
The supplied Phi is retained using its complete physical coordinates.
One H14 neighborhood covers every realSlice input. Its complex analyticity
is restricted to real scalars at those actual points, then composed with
realSlice and the minus/sqrt2 continuous linear map. No continuity or
analyticity of Phi is assumed, and no global complex extension, action,
mass, canonicity, inverse or choice independence is asserted.
-/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Real analyticity of the supplied SAME physical minus representative,
derived from one earned H14 complex model and complete physical coordinate
equality. No complex extension or cross-family independence is asserted. -/
theorem gk16_same_family_minus_physical_real_analytic38
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
    (V : Set PotPair) (hVopen : IsOpen V)
    (hrealV : range realSlice ⊆ V) (hVW : V ⊆ W)
    (beta : ℤ → PotPair → ℂ)
    (hbeta : ∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ V →
      Summable (fun m : P2Index38 n =>
        ‖gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
      beta n phi.1 = (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))
    (hXY : ∀ n : ℤ,
      AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) V ∧
      AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) V)
    (Phi : PhysicalL2 → Lib.L2Z)
    (hcoords : ∀ (u : PhysicalL2) (n : ℤ),
      Phi u n = (xiN38 n (realSlice u)/2) *
        (gk16ActualScalarZMinus38 F n (realSlice u) *
          Complex.exp (-Complex.I*beta n (realSlice u)))) :
    ∀ u : PhysicalL2, AnalyticAt ℝ Phi u := by
  obtain ⟨U,Omega,_hUopen,hrealU,_hUV,_hXYcoords,hOmega,hminus⟩ :=
    gk16_same_family_xy_hilbert_representative38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
  let L : (Lib.L2Z × Lib.L2Z) →L[ℂ] Lib.L2Z :=
    (Real.sqrt 2 : ℂ)⁻¹ •
      ((ContinuousLinearMap.fst ℂ Lib.L2Z Lib.L2Z) -
        Complex.I • (ContinuousLinearMap.snd ℂ Lib.L2Z Lib.L2Z))
  let LR : (Lib.L2Z × Lib.L2Z) →L[ℝ] Lib.L2Z := L.restrictScalars ℝ
  let Psi : PhysicalL2 → Lib.L2Z := fun v => LR (Omega (realSlice v))
  have hPsiCoords : ∀ (v : PhysicalL2) (n : ℤ),
      Psi v n = (xiN38 n (realSlice v)/2) *
        (gk16ActualScalarZMinus38 F n (realSlice v) *
          Complex.exp (-Complex.I*beta n (realSlice v))) := by
    intro v n
    have hmem : realSlice v ∈ U := hrealU (mem_range_self v)
    change (Real.sqrt 2 : ℂ)⁻¹ *
      ((Omega (realSlice v)).1 n-Complex.I*(Omega (realSlice v)).2 n) = _
    simpa only [div_eq_mul_inv,mul_comm] using hminus (realSlice v) hmem n
  have hsame : Phi = Psi := by
    funext v
    apply lp.ext
    funext n
    exact (hcoords v n).trans (hPsiCoords v n).symm
  rw [hsame]
  intro u
  have hmem : realSlice u ∈ U := hrealU (mem_range_self u)
  have hOmegaAt : AnalyticAt ℝ Omega (realSlice u) :=
    (hOmega (realSlice u) hmem).restrictScalars (𝕜 := ℝ)
  have hSliceAt : AnalyticAt ℝ (fun v : PhysicalL2 => Omega (realSlice v)) u :=
    hOmegaAt.comp (realSlice.analyticAt u)
  change AnalyticAt ℝ (fun v : PhysicalL2 => LR (Omega (realSlice v))) u
  exact AnalyticAt.comp (𝕜 := ℝ)
    (g := LR) (f := fun v : PhysicalL2 => Omega (realSlice v)) (x := u)
    (LR.analyticAt (Omega (realSlice u))) hSliceAt

end
end NlsGge.GK38
