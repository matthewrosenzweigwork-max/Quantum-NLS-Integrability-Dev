import Mathlib
import NlsGge.Atomic.G5.G5010
import NlsGge.Atomic.G5.G5012
import NlsGge.Atomic.G5.G5012Sup2
import NlsGge.Atomic.G5.G5012Sup3
import NlsGge.Atomic.G5.G5012Sup4
import NlsGge.Atomic.G4.G4042
import NlsGge.Atomic.X.X004

/- G5-011 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5011.lean.
   Head `G5011` verbatim from STATEMENTS/G5.md (followup12, "## G5-011"; round 14 cluster 5 retains the vacuum signs:
   "G5011's printed +sqrt2 Re F and -sqrt2 Im F are consistent and are retained", audit N1). No lexical edits.
   Route (G5011_ROUTE.md; GK-17.2 p. 94 vacuum gradients): by the landed G5-012 adjoint identity at u = 0, landed
   gradient_physicalCoordinate (Sup3), the landed G5-010 vacuum gradients (g5010_vacuum) and the landed basis projection
   (Sup2), the adjoint of the conjugated Jacobian fixes every vector of the physical real Fourier Hilbert basis, hence equals
   the identity (dense span, Sup2); taking adjoints, reflectedFourierL2.symm o d_0 Phi = id, i.e. d_0 Phi = reflectedFourierL2.
   The Cartesian clauses use Phi = L o realBirkhoffCartesian with L x = ((x(true,n) - i x(false,n))/sqrt 2)_n (Sup4, X004,
   G4-042 analyticity, as in G5012), and the l2 norm on Bool x Z split into its two real slices. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5011_adjoint_basis (j : Bool × ℤ) :
    jacobianAdjoint 0 (physicalFourierBasis j) = physicalFourierBasis j := by
  obtain ⟨b, n⟩ := j
  rw [G5012.2.2 0 (b, n), gradient_physicalCoordinate, map_zero]
  obtain ⟨hX, hY⟩ := g5010_vacuum n
  obtain ⟨hp, hm⟩ := physicalFourierBasis_projection n
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hY]
    exact hm
  · simp only [↓reduceIte]
    rw [hX]
    exact hp

theorem g5011_fderiv_of_basis
    (hb : ∀ j : Bool × ℤ, jacobianAdjoint 0 (physicalFourierBasis j) = physicalFourierBasis j) :
    fderiv ℝ physicalBirkhoff 0 =
      reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ := by
  have hd : Dense (Submodule.span ℝ (Set.range physicalFourierBasis) : Set PhysicalL2) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (eq_top_iff.mpr physicalFourierBasis_dense_span)
  have hA : jacobianAdjoint 0 = ContinuousLinearMap.id ℝ PhysicalL2 := by
    refine ContinuousLinearMap.ext_on hd ?_
    rintro _ ⟨j, rfl⟩
    exact hb j
  have hC : jacobianConjugate 0 = ContinuousLinearMap.id ℝ PhysicalL2 := by
    have h : ContinuousLinearMap.adjoint (jacobianAdjoint 0) =
        ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ PhysicalL2) := by
      rw [hA]
    unfold jacobianAdjoint at h
    rwa [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_id] at h
  apply ContinuousLinearMap.ext
  intro h
  have h2 : reflectedFourierL2.symm (fderiv ℝ physicalBirkhoff 0 h) = h := by
    have h1 := congrArg (fun T : PhysicalL2 →L[ℝ] PhysicalL2 => T h) hC
    exact h1
  show fderiv ℝ physicalBirkhoff 0 h = reflectedFourierL2 h
  calc fderiv ℝ physicalBirkhoff 0 h
      = reflectedFourierL2 (reflectedFourierL2.symm (fderiv ℝ physicalBirkhoff 0 h)) :=
        (reflectedFourierL2.apply_symm_apply _).symm
    _ = reflectedFourierL2 h := by rw [h2]

theorem g5011_coord_aux (a b : ℝ) (z : ℂ)
    (h : (((a : ℝ) : ℂ) - Complex.I * ((b : ℝ) : ℂ)) / (Real.sqrt 2 : ℂ) = z) :
    a = Real.sqrt 2 * z.re ∧ b = -Real.sqrt 2 * z.im := by
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  subst h
  constructor
  · rw [Complex.div_ofReal_re]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero]
    first
    | (field_simp; done)
    | (field_simp; ring)
  · rw [Complex.div_ofReal_im]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, mul_zero, zero_add, zero_sub]
    first
    | (field_simp; done)
    | (field_simp; ring)

theorem g5011_norm_aux (y : CartesianReal) (z : Lib.L2Z)
    (hy : ∀ n : ℤ, y (true, n) = Real.sqrt 2 * (z n).re ∧ y (false, n) = -Real.sqrt 2 * (z n).im) :
    ‖y‖ ^ 2 = 2 * ‖z‖ ^ 2 := by
  have hyn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) y
  have hzn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) z
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hyn hzn
  have hpt : ∀ n : ℤ, ‖y (true, n)‖ ^ 2 + ‖y (false, n)‖ ^ 2 = 2 * ‖z n‖ ^ 2 := by
    intro n
    obtain ⟨h1, h2⟩ := hy n
    have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, h1, h2, Complex.sq_norm,
      Complex.normSq_apply]
    linear_combination ((z n).re ^ 2 + (z n).im ^ 2) * hs
  rw [hyn, hzn]
  calc ∑' j : Bool × ℤ, ‖y j‖ ^ 2
      = ∑' (b : Bool) (n : ℤ), ‖y (b, n)‖ ^ 2 :=
        (g5012_cart_sq_summable y).tsum_prod' (fun b => g5012_slice_sq_summable y b)
    _ = ∑' n : ℤ, ‖y (true, n)‖ ^ 2 + ∑' n : ℤ, ‖y (false, n)‖ ^ 2 := by
        rw [tsum_fintype, Fintype.sum_bool]
    _ = ∑' n : ℤ, (‖y (true, n)‖ ^ 2 + ‖y (false, n)‖ ^ 2) :=
        ((g5012_slice_sq_summable y true).tsum_add (g5012_slice_sq_summable y false)).symm
    _ = ∑' n : ℤ, 2 * ‖z n‖ ^ 2 := tsum_congr hpt
    _ = 2 * ∑' n : ℤ, ‖z n‖ ^ 2 := tsum_mul_left

theorem g5011_cart_of_fderiv
    (hF : fderiv ℝ physicalBirkhoff 0 =
      reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ)
    (h : PhysicalL2) (n : ℤ) :
    fderiv ℝ realBirkhoffCartesian 0 h (true, n) =
      Real.sqrt 2 * (reflectedFourierL2 h n).re ∧
    fderiv ℝ realBirkhoffCartesian 0 h (false, n) =
      -Real.sqrt 2 * (reflectedFourierL2 h n).im := by
  obtain ⟨L, hL⟩ := g5012_L_exists
  have hcomp : physicalBirkhoff = ⇑L ∘ realBirkhoffCartesian := by
    funext u
    have hmem := G4042.2.1 u
    have hr : realBirkhoffCartesian u = ⟨realCartesianSequence u, hmem⟩ := by
      unfold realBirkhoffCartesian
      rw [dif_pos hmem]
    ext m
    rw [Function.comp_apply, hL, hr]
    obtain ⟨hx, hy, hphi, -⟩ := NlsGge.Atomic.X004.samePhi_cartesian_normalization u m
    have hX' : cartesianX m (realSlice u) = ((cartesianX m (realSlice u)).re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hx)
    have hY' : cartesianY m (realSlice u) = ((cartesianY m (realSlice u)).re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hy)
    show sourceFamily.Phi u m = _
    rw [hphi, hX', hY']
    rfl
  have hA : AnalyticOnNhd ℝ realBirkhoffCartesian Set.univ := G4042.2.2
  have hD : HasFDerivAt physicalBirkhoff (L.comp (fderiv ℝ realBirkhoffCartesian 0)) 0 := by
    rw [hcomp]
    exact L.hasFDerivAt.comp 0 (hA 0 (Set.mem_univ 0)).differentiableAt.hasFDerivAt
  have hR : L (fderiv ℝ realBirkhoffCartesian 0 h) n = reflectedFourierL2 h n := by
    have h1 := congrArg (fun T : PhysicalL2 →L[ℝ] Lib.L2Z => T h n) (hD.fderiv.symm.trans hF)
    exact h1
  rw [hL] at hR
  exact g5011_coord_aux _ _ _ hR

theorem G5011 :
  fderiv ℝ physicalBirkhoff 0 =
    reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ ∧
  (∀ h : PhysicalL2, ‖fderiv ℝ physicalBirkhoff 0 h‖ = ‖h‖) ∧
  (∀ (h : PhysicalL2) (n : ℤ),
    fderiv ℝ realBirkhoffCartesian 0 h (true, n) =
      Real.sqrt 2 * (reflectedFourierL2 h n).re ∧
    fderiv ℝ realBirkhoffCartesian 0 h (false, n) =
      -Real.sqrt 2 * (reflectedFourierL2 h n).im) ∧
  (∀ h : PhysicalL2, ‖fderiv ℝ realBirkhoffCartesian 0 h‖^2 = 2 * ‖h‖^2) := by
  have hF := g5011_fderiv_of_basis g5011_adjoint_basis
  refine ⟨hF, fun h => ?_, g5011_cart_of_fderiv hF, fun h => ?_⟩
  · rw [hF]
    exact reflectedFourierL2.norm_map h
  · rw [g5011_norm_aux _ (reflectedFourierL2 h) (g5011_cart_of_fderiv hF h),
      LinearIsometryEquiv.norm_map]

end
end NlsGge.GKDefinitionDesign
