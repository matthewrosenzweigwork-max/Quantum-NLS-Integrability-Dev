import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G5.G5012Sup1
import NlsGge.Atomic.G5.G5012Sup4
import NlsGge.Atomic.G4.G4042
import NlsGge.Atomic.X.X004
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff

/- G5-012 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G5/G5012.lean.
   Head `G5012` verbatim from STATEMENTS/G5.md (followup12; round 14, cluster 5). No lexical edits.
   Route (GK-17.3, pp. 94-95): physicalBirkhoff = Phi = L o realBirkhoffCartesian, with the bounded real-linear
   L x = ((x(true,n) - i x(false,n))/sqrt 2)_n (G5012Sup4); this identity is X-006's Phi = (X - iY)/sqrt 2 with X, Y real on the
   slice (landed X004). realBirkhoffCartesian is real-analytic on the whole space (G4-042), so its derivative is analytic
   and hence norm-continuous, and so is fderiv Phi = L o fderiv realBirkhoffCartesian. The conjugate and its adjoint are continuous
   (constant composition; the adjoint is a linear isometry). Adjoint identity: <A* b_j, h> = <b_j, R^-1 DPhi h>
   = Re(conj c_j (DPhi h)_n) = d(physicalCoordinate j) h = <gradient (physicalCoordinate j), h>. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g5012_phi_comp : ∃ L : CartesianReal →L[ℝ] Lib.L2Z,
    physicalBirkhoff = ⇑L ∘ realBirkhoffCartesian := by
  obtain ⟨L, hL⟩ := g5012_L_exists
  refine ⟨L, funext fun u => ?_⟩
  have hmem := G4042.2.1 u
  have hr : realBirkhoffCartesian u = ⟨realCartesianSequence u, hmem⟩ := by
    unfold realBirkhoffCartesian
    rw [dif_pos hmem]
  ext n
  rw [Function.comp_apply, hL, hr]
  obtain ⟨hx, hy, hphi, -⟩ := NlsGge.Atomic.X004.samePhi_cartesian_normalization u n
  have hX' : cartesianX n (realSlice u) = ((cartesianX n (realSlice u)).re : ℂ) :=
    Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hx)
  have hY' : cartesianY n (realSlice u) = ((cartesianY n (realSlice u)).re : ℂ) :=
    Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hy)
  show sourceFamily.Phi u n = _
  rw [hphi, hX', hY']
  rfl

theorem g5012_deriv : ∃ L : CartesianReal →L[ℝ] Lib.L2Z,
    (∀ u : PhysicalL2, HasFDerivAt physicalBirkhoff (L.comp (fderiv ℝ realBirkhoffCartesian u)) u) ∧
    Continuous (fun u : PhysicalL2 => fderiv ℝ physicalBirkhoff u) := by
  obtain ⟨L, hL⟩ := g5012_phi_comp
  have hA : AnalyticOnNhd ℝ realBirkhoffCartesian Set.univ := G4042.2.2
  have hD : ∀ u : PhysicalL2,
      HasFDerivAt physicalBirkhoff (L.comp (fderiv ℝ realBirkhoffCartesian u)) u := by
    intro u
    rw [hL]
    exact L.hasFDerivAt.comp u (hA u (Set.mem_univ u)).differentiableAt.hasFDerivAt
  refine ⟨L, hD, ?_⟩
  have hc : Continuous (fderiv ℝ realBirkhoffCartesian) :=
    continuousOn_univ.mp hA.fderiv.continuousOn
  have he : (fun u : PhysicalL2 => fderiv ℝ physicalBirkhoff u) =
      fun u => L.comp (fderiv ℝ realBirkhoffCartesian u) := funext fun u => (hD u).fderiv
  rw [he]
  exact continuous_const.clm_comp hc

theorem g5012_coord_fderiv (u h : PhysicalL2) (n : ℤ) (D : PhysicalL2 →L[ℝ] Lib.L2Z)
    (hD : HasFDerivAt physicalBirkhoff D u) :
    fderiv ℝ (physicalCoordinate (true, n)) u h = (D h n).re ∧
    fderiv ℝ (physicalCoordinate (false, n)) u h = (D h n).im := by
  have hev : HasFDerivAt (fun v : PhysicalL2 => physicalBirkhoff v n)
      ((lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n).comp D) u :=
    (lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n).hasFDerivAt.comp u hD
  have h1 : physicalCoordinate (true, n) = fun v : PhysicalL2 => (physicalBirkhoff v n).re := rfl
  have h2 : physicalCoordinate (false, n) = fun v : PhysicalL2 => (physicalBirkhoff v n).im := rfl
  have hre : HasFDerivAt (fun v : PhysicalL2 => (physicalBirkhoff v n).re)
      (Complex.reCLM.comp ((lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n).comp D)) u :=
    Complex.reCLM.hasFDerivAt.comp u hev
  have him : HasFDerivAt (fun v : PhysicalL2 => (physicalBirkhoff v n).im)
      (Complex.imCLM.comp ((lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 n).comp D)) u :=
    Complex.imCLM.hasFDerivAt.comp u hev
  constructor
  · rw [h1, hre.fderiv]
    rfl
  · rw [h2, him.fderiv]
    rfl

theorem g5012_adjoint_identity (D : PhysicalL2 → PhysicalL2 →L[ℝ] Lib.L2Z)
    (hD : ∀ u : PhysicalL2, HasFDerivAt physicalBirkhoff (D u) u) (u : PhysicalL2) (j : Bool × ℤ) :
    jacobianAdjoint u (physicalFourierBasis j) = gradient (physicalCoordinate j) u := by
  obtain ⟨b, n⟩ := j
  apply ext_inner_right ℝ
  intro h
  unfold jacobianAdjoint
  rw [ContinuousLinearMap.adjoint_inner_left, gradient, InnerProductSpace.toDual_symm_apply]
  obtain ⟨hre, him⟩ := g5012_coord_fderiv u h n _ (hD u)
  rw [← (hD u).fderiv] at hre him
  have hJu : jacobianConjugate u h = reflectedFourierL2.symm (fderiv ℝ physicalBirkhoff u h) := rfl
  rw [hJu, real_inner_eq_re_inner_g5012]
  unfold physicalFourierBasis
  rw [LinearIsometryEquiv.inner_map_map, lp.inner_single_left]
  cases b
  · rw [him]
    simp [RCLike.inner_apply, Complex.mul_re]
  · rw [hre]
    simp [RCLike.inner_apply]

theorem G5012 :
  Continuous jacobianConjugate ∧ Continuous jacobianAdjoint ∧
  ∀ (u : PhysicalL2) (j : Bool × ℤ),
    jacobianAdjoint u (physicalFourierBasis j) = gradient (physicalCoordinate j) u := by
  obtain ⟨L, hD, hcont⟩ := g5012_deriv
  have hJ : Continuous jacobianConjugate := by
    unfold jacobianConjugate
    exact continuous_const.clm_comp hcont
  refine ⟨hJ, ?_, ?_⟩
  · unfold jacobianAdjoint
    exact ContinuousLinearMap.adjoint.continuous.comp hJ
  · exact g5012_adjoint_identity _ hD

end
end NlsGge.GKDefinitionDesign
