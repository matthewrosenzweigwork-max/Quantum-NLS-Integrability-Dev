import Armstrong.Work.ActualCartesianHilbertModels
import NlsGge.GK38.PairPotential

/-!
# Global continuous physical minus-coordinate representative

SPECULATIVE_UNCOMPILED_XY_H14_PARENTS, task PHYSICAL_MINUS_REP_014.
Exactly one reviewed ordinary theorem, zero new definitions/instances.
The SAME original W/F and earned V/beta are retained. One earned U/Omega
covers every realSlice input; only those source values are used below.
This is a partial continuous carrier before action, not full realMap.
No action, Cartesian realtrace, real analyticity, Fourier phase,
choice independence, canonicity or inverse is asserted.
-/
set_option autoImplicit false
open Set
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- A single globally continuous physical lp2 representative of the literal
minus coordinates, derived from one actual common complex Hilbert model. -/
theorem gk16_same_family_minus_physical_representative38
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
      AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) V) :
    ∃ Phi : PhysicalL2 → Lib.L2Z,
      Continuous Phi ∧
      ∀ (u : PhysicalL2) (n : ℤ),
        Phi u n = (xiN38 n (realSlice u)/2) *
          (gk16ActualScalarZMinus38 F n (realSlice u) *
            Complex.exp (-Complex.I*beta n (realSlice u))) := by
  obtain ⟨U,Omega,_hUopen,hrealU,_hUV,_hcoords,hOmega,hminus⟩ :=
    gk16_same_family_xy_hilbert_representative38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
  let L : (Lib.L2Z × Lib.L2Z) →L[ℂ] Lib.L2Z :=
    (Real.sqrt 2 : ℂ)⁻¹ •
      ((ContinuousLinearMap.fst ℂ Lib.L2Z Lib.L2Z) -
        Complex.I • (ContinuousLinearMap.snd ℂ Lib.L2Z Lib.L2Z))
  let Phi : PhysicalL2 → Lib.L2Z := fun u => L (Omega (realSlice u))
  refine ⟨Phi,?_,?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro u
    have hmem : realSlice u ∈ U := hrealU (mem_range_self u)
    have hOmegaAt : ContinuousAt Omega (realSlice u) :=
      (hOmega (realSlice u) hmem).continuousAt
    exact L.continuous.continuousAt.comp
      (hOmegaAt.comp realSlice.continuous.continuousAt)
  · intro u n
    have hmem : realSlice u ∈ U := hrealU (mem_range_self u)
    change (Real.sqrt 2 : ℂ)⁻¹ *
      ((Omega (realSlice u)).1 n-Complex.I*(Omega (realSlice u)).2 n) = _
    simpa only [div_eq_mul_inv,mul_comm] using hminus (realSlice u) hmem n

end
end NlsGge.GK38
