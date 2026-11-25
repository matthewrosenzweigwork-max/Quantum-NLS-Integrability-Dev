import Mathlib
import NlsGge.Atomic.G5.G5012Host
import NlsGge.Atomic.G5.G5012Sup1
import NlsGge.Atomic.G5.G5012Sup2
import NlsGge.Atomic.G5.G5017Host
import NlsGge.Atomic.G5.G5018Sup1
import NlsGge.Atomic.G6.G6001Sup1Core
import NlsGge.Atomic.G6.G6028Sup1Core

/- G6-028 SUPPORT 2 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6028Sup2Core.lean, namespace NlsGge.GKDefinitionDesign.G6028Aux.
   Symplectic clause of G6-028 (GK Theorem 19.1/§20.2: the canonical relations make dPhi(u) symplectic) from exactly the
   hypotheses of landed G6001Aux.core6001 (gradient identities G5012 / G5012Sup3, real-covector identities G5032Sup1+G4040,
   canonical relations G5040) plus injectivity of dPhi(u) (from landed G6002, discharged in the G6028 glue):
   (1) on the physical real Hilbert basis d = physicalFourierHilbertBasis, with A = jacobianAdjoint u and J = (-i)·,
       <J A d_i, A d_j> = <J d_i, d_j> (left side: omega_scaled + the brackets, as in core6001; right side: J d_(true,n) =
       -d_(false,n), J d_(false,n) = d_(true,n) and orthonormality);
   (2) G6028Aux.form_eq_of_basis extends it to all vectors; (3) G6028Aux.symplectic_of_adjoint with C = jacobianConjugate u
       (A = C† by definition; C = F^{-1} dPhi(u) injective); (4) transport through the reflected Fourier isometry by
       G6028Aux.real_inner_map_of_norm, and i· = -J. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GK38
open scoped InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6028Aux
noncomputable section

theorem smul_basis_true (n : ℤ) :
    (-Complex.I) • physicalFourierBasis (true, n) = -physicalFourierBasis (false, n) := by
  unfold physicalFourierBasis
  rw [← LinearIsometryEquiv.map_smul, ← map_neg reflectedFourierL2.symm]
  congr 1
  apply lp.ext
  funext m
  by_cases hm : m = n
  · subst hm
    simp only [lp.coeFn_smul, lp.coeFn_neg, lp.coeFn_single, Pi.neg_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul]
    simp
  · simp only [lp.coeFn_smul, lp.coeFn_neg, lp.coeFn_single, Pi.neg_apply, Pi.smul_apply,
      Pi.single_apply, hm, if_false, smul_eq_mul]
    simp

theorem smul_basis_false (n : ℤ) :
    (-Complex.I) • physicalFourierBasis (false, n) = physicalFourierBasis (true, n) := by
  unfold physicalFourierBasis
  rw [← LinearIsometryEquiv.map_smul]
  congr 1
  apply lp.ext
  funext m
  by_cases hm : m = n
  · subst hm
    simp only [lp.coeFn_smul, lp.coeFn_neg, lp.coeFn_single, Pi.neg_apply, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul]
    simp
  · simp only [lp.coeFn_smul, lp.coeFn_neg, lp.coeFn_single, Pi.neg_apply, Pi.smul_apply,
      Pi.single_apply, hm, if_false, smul_eq_mul]
    simp

theorem basis_inner (i j : Bool × ℤ) :
    inner ℝ (physicalFourierBasis i) (physicalFourierBasis j) = if i = j then (1 : ℝ) else 0 :=
  orthonormal_iff_ite.mp physicalFourierBasis_orthonormal i j

theorem sqrt2_half : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = 1 / 2 := by
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The symplectic clause of G6-028 from the hypotheses of core6001 and injectivity of dPhi(u). -/
theorem core6028 (u : PhysicalL2)
    (hgrad : ∀ j : Bool × ℤ,
      jacobianAdjoint u (physicalFourierBasis j) = gradient (physicalCoordinate j) u)
    (hcoord : ∀ j : Bool × ℤ, gradient (physicalCoordinate j) u =
      if j.1 then
        (1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianX j.2) (realSlice u))
      else
        (-1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianY j.2) (realSlice u)))
    (hX : ∀ n : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianX n) (realSlice u))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianX n) (realSlice u))).1)
    (hY : ∀ n : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianY n) (realSlice u))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianY n) (realSlice u))).1)
    (h40 : ∀ m n : ℤ,
      pairPoisson (cartesianX m) (cartesianX n) (realSlice u) = 0 ∧
      pairPoisson (cartesianX m) (cartesianY n) (realSlice u) =
        -(if m = n then (1 : ℂ) else 0) ∧
      pairPoisson (cartesianY m) (cartesianY n) (realSlice u) = 0)
    (hinj : Function.Injective (fderiv ℝ physicalBirkhoff u)) (h k : PhysicalL2) :
    inner ℝ ((Complex.I : ℂ) • fderiv ℝ physicalBirkhoff u h)
      (fderiv ℝ physicalBirkhoff u k) = inner ℝ ((Complex.I : ℂ) • h) k := by
  set A : PhysicalL2 →L[ℝ] PhysicalL2 := jacobianAdjoint u with hA
  set C : PhysicalL2 →L[ℝ] PhysicalL2 := jacobianConjugate u with hC
  set J : PhysicalL2 →L[ℝ] PhysicalL2 :=
    ((-Complex.I) • ContinuousLinearMap.id ℂ PhysicalL2).restrictScalars ℝ with hJdef
  have hJ : ∀ x : PhysicalL2, J x = (-Complex.I) • x := fun x => rfl
  have hJJ : ∀ x : PhysicalL2, J (J x) = -x := by
    intro x
    rw [hJ, hJ, smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul]
  have hAC : A = C.adjoint := rfl
  have gT : ∀ n : ℤ, A (physicalFourierBasis (true, n)) =
      (1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradientCLM (fderiv ℂ (cartesianX n) (realSlice u))) := by
    intro n
    rw [hA, hgrad, hcoord]
    rfl
  have gF : ∀ n : ℤ, A (physicalFourierBasis (false, n)) =
      (-1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradientCLM (fderiv ℂ (cartesianY n) (realSlice u))) := by
    intro n
    rw [hA, hgrad, hcoord]
    rfl
  have pXY : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianX m) (realSlice u))
      (fderiv ℂ (cartesianY n) (realSlice u)) = -(if m = n then (1 : ℂ) else 0) :=
    fun m n => (h40 m n).2.1
  have pXX : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianX m) (realSlice u))
      (fderiv ℂ (cartesianX n) (realSlice u)) = 0 := fun m n => (h40 m n).1
  have pYY : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianY m) (realSlice u))
      (fderiv ℂ (cartesianY n) (realSlice u)) = 0 := fun m n => (h40 m n).2.2
  have pYX : ∀ m n : ℤ, pairPoissonCLM (fderiv ℂ (cartesianY m) (realSlice u))
      (fderiv ℂ (cartesianX n) (realSlice u)) = (if n = m then (1 : ℂ) else 0) := by
    intro m n
    rw [pairPoissonCLM_antisymm, pXY n m, neg_neg]
  have hs2 : (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) * 2 = 1 := by
    rw [sqrt2_half]; norm_num
  -- (1) the basis identity
  have hbasis : ∀ i j : Bool × ℤ,
      inner ℝ (J (A (physicalFourierHilbertBasis i))) (A (physicalFourierHilbertBasis j)) =
        inner ℝ (J (physicalFourierHilbertBasis i)) (physicalFourierHilbertBasis j) := by
    rintro ⟨b, n⟩ ⟨b', m⟩
    simp only [physicalFourierHilbertBasis_apply, hJ]
    cases b <;> cases b'
    · -- (false, n), (false, m)
      rw [gF, gF, G6001Aux.omega_scaled _ _ _ _ (hY m) (hY n), pYY, smul_basis_false,
        basis_inner]
      simp
    · -- (false, n), (true, m)
      rw [gF, gT, G6001Aux.omega_scaled _ _ _ _ (hX m) (hY n), pXY, smul_basis_false,
        basis_inner]
      by_cases hmn : m = n
      · subst hmn
        simp only [eq_self_iff_true, if_true, Complex.neg_re, Complex.one_re]
        have : (1 / Real.sqrt 2 : ℝ) * (-1 / Real.sqrt 2) * (2 * -1) =
            (1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) * 2 := by ring
        rw [this, hs2]
      · have hne : ((true, n) : Bool × ℤ) ≠ (true, m) := fun h => hmn (Prod.mk.inj h).2.symm
        rw [if_neg hmn, if_neg hne]
        simp
    · -- (true, n), (false, m)
      rw [gT, gF, G6001Aux.omega_scaled _ _ _ _ (hY m) (hX n), pYX, smul_basis_true,
        inner_neg_left, basis_inner]
      by_cases hmn : n = m
      · subst hmn
        simp only [eq_self_iff_true, if_true, Complex.one_re]
        have : (-1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) * (2 * 1) =
            -((1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) * 2) := by ring
        rw [this, hs2]
      · have hne : ((false, n) : Bool × ℤ) ≠ (false, m) := fun h => hmn (Prod.mk.inj h).2
        rw [if_neg hmn, if_neg hne]
        simp
    · -- (true, n), (true, m)
      rw [gT, gT, G6001Aux.omega_scaled _ _ _ _ (hX m) (hX n), pXX, smul_basis_true,
        inner_neg_left, basis_inner]
      simp
  -- (2) all vectors
  have hall : ∀ x y : PhysicalL2, inner ℝ (J (C.adjoint x)) (C.adjoint y) = inner ℝ (J x) y := by
    intro x y
    rw [← hAC]
    exact form_eq_of_basis physicalFourierHilbertBasis J A hbasis x y
  -- (3) C is injective and symplectic
  have hCapp : ∀ x : PhysicalL2, C x = reflectedFourierL2.symm (fderiv ℝ physicalBirkhoff u x) :=
    fun x => rfl
  have hCinj : Function.Injective C := by
    intro a b hab
    rw [hCapp, hCapp] at hab
    exact hinj (reflectedFourierL2.symm.injective hab)
  have hsymp := symplectic_of_adjoint J C hJJ hCinj hall h k
  -- (4) transport through the reflected Fourier isometry
  let T : Lib.L2Z →+ PhysicalL2 :=
    AddMonoidHom.mk' (fun x => reflectedFourierL2.symm x) (map_add reflectedFourierL2.symm)
  have hT : ∀ x : Lib.L2Z, ‖T x‖ = ‖x‖ := fun x => reflectedFourierL2.symm.norm_map x
  have hiJ : ∀ x : PhysicalL2, (Complex.I : ℂ) • x = -J x := by
    intro x
    rw [hJ, neg_smul, neg_neg]
  rw [← real_inner_map_of_norm T hT]
  have e1 : T ((Complex.I : ℂ) • fderiv ℝ physicalBirkhoff u h) = (Complex.I : ℂ) • C h := by
    show reflectedFourierL2.symm ((Complex.I : ℂ) • fderiv ℝ physicalBirkhoff u h) = _
    rw [LinearIsometryEquiv.map_smul, hCapp]
  have e2 : T (fderiv ℝ physicalBirkhoff u k) = C k := (hCapp k).symm
  rw [e1, e2, hiJ, hiJ, inner_neg_left, inner_neg_left, hsymp]

end
end G6028Aux
end NlsGge.GKDefinitionDesign
