import Armstrong.Work.ActualCartesianXYModels
import NlsGge.GK38.TauGammaL2Realization

/-!
# Same-family complex Cartesian sequence realization

SPECULATIVE_UNCOMPILED_XY_PARENT, task HILBERT_REALIZATION_014.
Exactly one independently reviewed ordinary theorem, zero new definitions.
The same original W/F and earned V/beta are retained. Actual lp2 membership
comes from existing realization of both scalar sequences on one earned U.
No source values off U, realtrace, physical/global map, action, canonical
relations, reflected Fourier derivative or inverse are asserted.
-/

set_option autoImplicit false
open Set Metric Filter Topology
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- One ordinary complex pair representative of the actual scalar models on
an earned common open source neighborhood. The final scalar identity records
the minus/sqrt2 convention without any reality or action-norm premise. -/
theorem gk16_same_family_xy_hilbert_representative38
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
    ∃ U : Set PotPair, ∃ Omega : PotPair → (Lib.L2Z × Lib.L2Z),
      IsOpen U ∧ range realSlice ⊆ U ∧ U ⊆ V ∩ xiCommonDomain38 ∧
      (∀ phi : PotPair, phi ∈ U → ∀ n : ℤ,
        (Omega phi).1 n = gk16ScalarXModel38 F beta n phi ∧
        (Omega phi).2 n = gk16ScalarYModel38 F beta n phi) ∧
      AnalyticOnNhd ℂ Omega U ∧
      ∀ phi : PotPair, phi ∈ U → ∀ n : ℤ,
        ((Omega phi).1 n-Complex.I*(Omega phi).2 n)/(Real.sqrt 2 : ℂ) =
          (xiN38 n phi/2) * (gk16ActualScalarZMinus38 F n phi *
            Complex.exp (-Complex.I*beta n phi)) := by
  obtain ⟨U,hUopen,hrealU,hUV,hl2⟩ :=
    gk16_same_family_xy_local_l2_domain38 W hWopen hreal hWgk F
      hFanalytic hFn hFinv hperiod hFreal V hVopen hrealV hVW beta hbeta
  have hUVonly : U ⊆ V := fun phi hphi => (hUV hphi).1
  have hXanalytic : ∀ n : ℤ,
      AnalyticOnNhd ℂ (gk16ScalarXModel38 F beta n) U :=
    fun n => (hXY n).1.mono hUVonly
  have hYanalytic : ∀ n : ℤ,
      AnalyticOnNhd ℂ (gk16ScalarYModel38 F beta n) U :=
    fun n => (hXY n).2.mono hUVonly
  obtain ⟨AX,hAX,hAXanalytic⟩ :=
    local_l2_analytic_realization38 U
      (fun phi n => gk16ScalarXModel38 F beta n phi) hUopen hXanalytic
      (fun phi hphi => (hl2 phi hphi).1)
  obtain ⟨AY,hAY,hAYanalytic⟩ :=
    local_l2_analytic_realization38 U
      (fun phi n => gk16ScalarYModel38 F beta n phi) hUopen hYanalytic
      (fun phi hphi => (hl2 phi hphi).2)
  let Omega : PotPair → (Lib.L2Z × Lib.L2Z) := fun phi => (AX phi,AY phi)
  have hrootReal : Real.sqrt 8 * Real.sqrt 2 = 4 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hroot : (Real.sqrt 8 : ℂ) * (Real.sqrt 2 : ℂ) = 4 := by
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
  refine ⟨U,Omega,hUopen,hrealU,hUV,?_,?_,?_⟩
  · intro phi hphi n
    exact ⟨hAX phi hphi n,hAY phi hphi n⟩
  · exact hAXanalytic.prod hAYanalytic
  · intro phi hphi n
    change (AX phi n-Complex.I*AY phi n)/(Real.sqrt 2 : ℂ) = _
    rw [hAX phi hphi n,hAY phi hphi n]
    unfold gk16ScalarXModel38 gk16ScalarYModel38
    rw [halgebra,hroot]
    ring

end
end NlsGge.GK38
