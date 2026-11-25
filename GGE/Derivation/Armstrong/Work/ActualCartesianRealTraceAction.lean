import Armstrong.Work.ActualCartesianXYModels
import Armstrong.Work.ActualBetaRealTrace
import Armstrong.Work.ActualScalarZRealTrace
import NlsGge.GK38.ActionRealBridge

/-!
# Actual Cartesian real trace and pointwise action normalization

SPECULATIVE_UNCOMPILED_PARENTS, task ACTUAL_XY_REAL_TRACE_ACTION_014.
Exactly one coupled theorem, zero definitions. The original W/F and the same
earned V/beta are retained. Source-row summability precedes beta reality.
Actual signed-model conjugation and xi reality earn the two real traces; the
explicit minus/sqrt2 scalar identity and actual product/action bridges earn
the pointwise physical norm. No gap division or complex-collapse zero rule
is used. This module constructs no global map or inverse and proves no
canonical relation or actual-source node closure.
-/
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gk16_same_family_xy_real_trace_action38
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
    (V : Set PotPair) (hrealV : range realSlice ⊆ V)
    (beta : ℤ → PotPair → ℂ)
    (hbeta : ∀ n : ℤ, ∀ phi : {chi : PotPair // chi ∈ W}, phi.1 ∈ V →
      Summable (fun m : P2Index38 n =>
        ‖gkSourceBeta38 W hWopen hreal hWgk F
          hFanalytic hFn hperiod n m.1 m.2 phi‖) ∧
      beta n phi.1 = (∑' m : P2Index38 n,
          gkSourceBeta38 W hWopen hreal hWgk F
            hFanalytic hFn hperiod n m.1 m.2 phi))
    (n : ℤ) (u : PhysicalL2) :
    (gk16ScalarXModel38 F beta n (realSlice u)).im = 0 ∧
    (gk16ScalarYModel38 F beta n (realSlice u)).im = 0 ∧
    ‖(gk16ScalarXModel38 F beta n (realSlice u) -
        Complex.I * gk16ScalarYModel38 F beta n (realSlice u)) /
      (Real.sqrt 2 : ℂ)‖ ^ 2 = actualGapActionAllE02_38 u n := by
  let phi : PotPair := realSlice u
  have huW : phi ∈ W := hreal (mem_range_self u)
  let phiW : {chi : PotPair // chi ∈ W} := ⟨phi,huW⟩
  obtain ⟨hsumNorm,hbetaEq⟩ := hbeta n phiW (hrealV (mem_range_self u))
  have hbetaIm : (beta n phi).im = 0 := by
    rw [hbetaEq,Complex.im_tsum hsumNorm.of_norm]
    have hterms : ∀ m : P2Index38 n,
        (gkSourceBeta38 W hWopen hreal hWgk F hFanalytic hFn hperiod
          n m.1 m.2 phiW).im = 0 := by
      intro m
      exact gkSourceBeta_real_trace38 W hWopen hreal hWgk F
        hFanalytic hFn hperiod hFreal n m.1 m.2 u
    simp only [hterms,tsum_zero]
  have hbetaConj : (starRingEnd ℂ) (beta n phi) = beta n phi := by
    apply Complex.ext <;>
      simp only [Complex.conj_re,Complex.conj_im,hbetaIm,neg_zero]
  let xi : ℂ := xiN38 n phi
  have hxiIm : xi.im = 0 := (xiN38_real_ge_one u n).1
  have hxiConj : (starRingEnd ℂ) xi = xi := by
    apply Complex.ext <;>
      simp only [Complex.conj_re,Complex.conj_im,hxiIm,neg_zero]
  have hZConj :
      (starRingEnd ℂ) (gk16ActualScalarZPlus38 F n phi) =
        gk16ActualScalarZMinus38 F n phi :=
    gk16_same_family_scalar_models_conj38 W hreal F hperiod hFreal n u
  let P : ℂ := gk16ActualScalarZPlus38 F n phi *
    Complex.exp (Complex.I * beta n phi)
  let M : ℂ := gk16ActualScalarZMinus38 F n phi *
    Complex.exp (-Complex.I * beta n phi)
  have hPConj : (starRingEnd ℂ) P = M := by
    change (starRingEnd ℂ)
        (gk16ActualScalarZPlus38 F n phi * Complex.exp (Complex.I * beta n phi)) =
      gk16ActualScalarZMinus38 F n phi * Complex.exp (-Complex.I * beta n phi)
    rw [map_mul,hZConj,← Complex.exp_conj]
    simp only [map_mul,Complex.conj_I,hbetaConj]
  have hMConj : (starRingEnd ℂ) M = P := by
    rw [← hPConj,Complex.conj_conj]
  let X : ℂ := gk16ScalarXModel38 F beta n phi
  let Y : ℂ := gk16ScalarYModel38 F beta n phi
  have hXConj : (starRingEnd ℂ) X = X := by
    change (starRingEnd ℂ) ((xi/(Real.sqrt 8 : ℂ))*(P+M)) =
      (xi/(Real.sqrt 8 : ℂ))*(P+M)
    rw [map_mul,map_div₀,hxiConj,Complex.conj_ofReal,map_add,hPConj,hMConj]
    ring
  have hYConj : (starRingEnd ℂ) Y = Y := by
    change (starRingEnd ℂ) ((xi/((Real.sqrt 8 : ℂ)*Complex.I))*(P-M)) =
      (xi/((Real.sqrt 8 : ℂ)*Complex.I))*(P-M)
    rw [map_mul,map_div₀,hxiConj,map_mul,Complex.conj_ofReal,
      Complex.conj_I,map_sub,hPConj,hMConj]
    simp only [mul_neg,div_neg]
    ring
  have hXIm : X.im = 0 := by
    have h := congrArg Complex.im hXConj
    simp only [Complex.conj_im] at h
    linarith
  have hYIm : Y.im = 0 := by
    have h := congrArg Complex.im hYConj
    simp only [Complex.conj_im] at h
    linarith
  have hPM : P*M = gamma2 phi n := by
    change (gk16ActualScalarZPlus38 F n phi *
        Complex.exp (Complex.I*beta n phi)) *
      (gk16ActualScalarZMinus38 F n phi *
        Complex.exp (-Complex.I*beta n phi)) = gamma2 phi n
    rw [mul_mul_mul_comm,← Complex.exp_add]
    have hexp : Complex.I*beta n phi + -Complex.I*beta n phi = 0 := by ring
    rw [hexp,Complex.exp_zero,mul_one]
    exact gk16_actual_scalar_models_product38 F n phi (hWgk huW)
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
  let C : ℂ := (X-Complex.I*Y)/(Real.sqrt 2 : ℂ)
  have hC : C = (xi/2)*M := by
    change (xi/(Real.sqrt 8 : ℂ)*(P+M) -
        Complex.I*(xi/((Real.sqrt 8 : ℂ)*Complex.I)*(P-M)))/
          (Real.sqrt 2 : ℂ) = (xi/2)*M
    rw [halgebra,hroot]
    ring
  have hCConj : (starRingEnd ℂ) C = (xi/2)*P := by
    rw [hC,map_mul,map_div₀,hxiConj,map_ofNat,hMConj]
  have hCProduct : C*(starRingEnd ℂ) C = xi^2*gamma2 phi n/4 := by
    rw [hCConj,hC]
    calc
      ((xi/2)*M)*((xi/2)*P) = (xi^2/4)*(P*M) := by ring
      _ = xi^2*gamma2 phi n/4 := by rw [hPM]; ring
  have hCAction : C*(starRingEnd ℂ) C = (actualGapActionAllE02_38 u n : ℂ) := by
    calc
      _ = xi^2*gamma2 phi n/4 := hCProduct
      _ = gkActionC38 phi n := (actionXiN38_identity n phi (hWgk huW)).symm
      _ = (actualGapActionAllE02_38 u n : ℂ) := ActionRealBridge.action_real_bridge u n
  refine ⟨hXIm,hYIm,?_⟩
  change ‖C‖ ^ 2 = actualGapActionAllE02_38 u n
  rw [Complex.mul_conj'] at hCAction
  exact_mod_cast hCAction

end
end NlsGge.GK38
