import Mathlib
import NlsGge.GK38.Lib.CompactOps
import NlsGge.Atomic.X.X004
import NlsGge.Atomic.G5.G5012Sup4
import NlsGge.ThirdConsultation.G6.BirkhoffBasic
import NlsGge.ThirdConsultation.G6.RealCartesianBirkhoff

/- G6-002 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6002Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6002Aux.
   (1) `adjoint_equiv`: an injective compact perturbation of the identity is a continuous linear automorphism (GK Lemma F.7
       Fredholm step; landed NlsGge.GK38.Lib.bijective_of_one_add_compact with B = refl).
   (2) `phi_comp_formula`: physicalBirkhoff = L o realBirkhoffCartesian for the explicit landed G5012Sup4.g5012_L_exists map L
       (reused, not redefined), which is injective by its coordinate formula.  The composition proof is the landed
       g5012_phi_comp argument (X004.samePhi_cartesian_normalization) with the explicit L kept.
   (3) `cart_equiv`: if the physical Jacobian is an isomorphism and realBirkhoffCartesian is differentiable at u, then
       D = fderiv realBirkhoffCartesian u is bijective (L o D = dPhi, L injective) and hence a continuous linear equivalence
       (open mapping, ContinuousLinearEquiv.ofBijective).  No sourceFamily.XY_analytic field. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
namespace G6002Aux
noncomputable section

theorem adjoint_equiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (hinj : Function.Injective A)
    (hK : IsCompactOperator (A - ContinuousLinearMap.id ℝ E)) :
    ∃ e : E ≃L[ℝ] E, e.toContinuousLinearMap = A := by
  have hsum : ((ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) + (A - ContinuousLinearMap.id ℝ E)) = A := by
    ext x
    simp
  obtain ⟨e, he⟩ := NlsGge.GK38.Lib.bijective_of_one_add_compact (ContinuousLinearEquiv.refl ℝ E)
    (A - ContinuousLinearMap.id ℝ E) hK (by rw [hsum]; exact hinj)
  refine ⟨e, ContinuousLinearMap.ext fun x => ?_⟩
  have hx := congrFun he x
  rw [hsum] at hx
  exact hx

theorem phi_comp_formula : ∃ L : CartesianReal →L[ℝ] Lib.L2Z,
    Function.Injective L ∧ physicalBirkhoff = ⇑L ∘ realBirkhoffCartesian := by
  obtain ⟨L, hL⟩ := g5012_L_exists
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by norm_num)).ne'
  refine ⟨L, ?_, funext fun u => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    ext ⟨b, n⟩
    have h := congrArg (fun z : Lib.L2Z => z n) hx
    simp only [hL] at h
    have h0 : ((x (true, n) : ℝ) : ℂ) - Complex.I * ((x (false, n) : ℝ) : ℂ) = 0 := by
      have hz : (0 : Lib.L2Z) n = 0 := rfl
      rw [hz, div_eq_zero_iff] at h
      exact h.resolve_right hs
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp at hre him
    cases b
    · simpa using him
    · simpa using hre
  · ext n
    rw [Function.comp_apply, hL, realBirkhoffCartesian_eq]
    obtain ⟨hx, hy, hphi, -⟩ := NlsGge.Atomic.X004.samePhi_cartesian_normalization u n
    have hX' : cartesianX n (realSlice u) = ((cartesianX n (realSlice u)).re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hx)
    have hY' : cartesianY n (realSlice u) = ((cartesianY n (realSlice u)).re : ℂ) :=
      Complex.ext (Complex.ofReal_re _).symm (by rw [Complex.ofReal_im]; exact hy)
    show sourceFamily.Phi u n = _
    rw [hphi, hX', hY']
    rfl

theorem cart_equiv (u : PhysicalL2) (hA : DifferentiableAt ℝ realBirkhoffCartesian u)
    (h1 : ∃ e : PhysicalL2 ≃L[ℝ] Lib.L2Z,
      e.toContinuousLinearMap = fderiv ℝ physicalBirkhoff u) :
    ∃ e : PhysicalL2 ≃L[ℝ] CartesianReal,
      e.toContinuousLinearMap = fderiv ℝ realBirkhoffCartesian u := by
  obtain ⟨L, hLi, hP⟩ := phi_comp_formula
  obtain ⟨e1, he1⟩ := h1
  set D := fderiv ℝ realBirkhoffCartesian u with hDdef
  have hD : fderiv ℝ physicalBirkhoff u = L.comp D := by
    rw [hP]
    exact (L.hasFDerivAt.comp u hA.hasFDerivAt).fderiv
  have key : ∀ h : PhysicalL2, L (D h) = e1 h := by
    intro h
    calc L (D h) = (L.comp D) h := rfl
      _ = fderiv ℝ physicalBirkhoff u h := by rw [hD]
      _ = e1 h := by rw [← he1]; rfl
  have hinj : Function.Injective D := fun h h' hh =>
    e1.injective (by rw [← key, ← key, hh])
  have hsurj : Function.Surjective D := by
    intro y
    refine ⟨e1.symm (L y), hLi ?_⟩
    rw [key, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective _ _ _

end
end G6002Aux
end NlsGge.GKDefinitionDesign
