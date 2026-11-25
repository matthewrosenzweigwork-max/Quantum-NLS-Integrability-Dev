import Armstrong.Work.ActualPhysicalMinusRepresentative
import Armstrong.Work.ActualCartesianRealTraceAction
import Armstrong.Work.ActualL2MassFromCoordinates

/-!
# Actual physical minus representative, pointwise action and all-L2 mass

SPECULATIVE_UNACCEPTED_PARENT_CHAIN, task PHYSICAL_ACTION_MASS_019.
Exactly one reviewed coupled theorem, zero new definitions or instances.
One PHYS witness is retained with the same original W/F and scalar V/beta.
The literal XY-minus equality is explicitly earned before the action rewrite;
the existing conditional MASS helper is then instantiated with that same Phi.
The final norm identity uses genuine lp2 HasSum uniqueness. No real-analytic,
canonical, inverse, cross-family choice-independence or source-node closure is
asserted here. Approved proof-only parent successors preserve the interfaces.
-/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gk16_same_family_minus_physical_action_mass38
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
      (∀ (u : PhysicalL2) (n : ℤ),
        Phi u n = (xiN38 n (realSlice u)/2) *
          (gk16ActualScalarZMinus38 F n (realSlice u) *
            Complex.exp (-Complex.I*beta n (realSlice u)))) ∧
      (∀ (u : PhysicalL2) (n : ℤ),
        ‖Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n) ∧
      ∀ u : PhysicalL2,
        HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) ∧
        ‖Phi u‖ ^ 2 = ‖u‖ ^ 2 := by
  obtain ⟨Phi,hPhi,hcoords⟩ :=
    gk16_same_family_minus_physical_representative38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta hXY
  have hrootReal : Real.sqrt 8 * Real.sqrt 2 = 4 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hroot : (Real.sqrt 8 : ℂ)*(Real.sqrt 2 : ℂ) = 4 := by
    exact_mod_cast hrootReal
  have hroot8 : (Real.sqrt 8 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 8)))
  have hroot2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)))
  have halgebra (a p m : ℂ) :
      (a/(Real.sqrt 8 : ℂ)*(p+m) -
        Complex.I*(a/((Real.sqrt 8 : ℂ)*Complex.I)*(p-m)))/
          (Real.sqrt 2 : ℂ) =
        (a*2/((Real.sqrt 8 : ℂ)*(Real.sqrt 2 : ℂ)))*m := by
    field_simp [hroot8,hroot2,Complex.I_ne_zero] <;> ring
  have hC (u : PhysicalL2) (n : ℤ) :
      (gk16ScalarXModel38 F beta n (realSlice u) -
        Complex.I*gk16ScalarYModel38 F beta n (realSlice u))/(Real.sqrt 2 : ℂ) =
      (xiN38 n (realSlice u)/2) *
        (gk16ActualScalarZMinus38 F n (realSlice u) *
          Complex.exp (-Complex.I*beta n (realSlice u))) := by
    unfold gk16ScalarXModel38 gk16ScalarYModel38
    rw [halgebra,hroot]
    ring
  have hAction : ∀ (u : PhysicalL2) (n : ℤ),
      ‖Phi u n‖ ^ 2 = actualGapActionAllE02_38 u n := by
    intro u n
    have hpoint :=
      (gk16_same_family_xy_real_trace_action38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod hFreal V hrealV beta hbeta n u).2.2
    rw [hcoords u n,← hC u n]
    exact hpoint
  refine ⟨Phi,hPhi,hcoords,hAction,?_⟩
  intro u
  have hMass : HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) :=
    actualGapAction_hasSum_of_continuous_hilbert_coordinates38 Phi hPhi hAction u
  refine ⟨hMass,?_⟩
  have hCoordsSum :
      HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖Phi u‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,hAction] using
      (lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) (Phi u))
  exact hCoordsSum.unique hMass

end
end NlsGge.GK38
