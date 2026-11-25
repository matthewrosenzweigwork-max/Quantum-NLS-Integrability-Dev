import Mathlib
import NlsGge.Atomic.G6.G6016Host
import NlsGge.Atomic.G6.G6001Sup1Core

/- G6-016 SUPPORT 1 CORE (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G6/G6016Sup1Core.lean, namespace NlsGge.GKDefinitionDesign.G6016Aux.
   GK Theorem 20.1 (first step): with X_H = -(i/2) grad H and I_n = |Phi_n|^2 (X-006 field Phi_action),
   (1) `omega_coord`: the real symplectic pairings <(-i) grad c_j, grad c_k> of the physical coordinate gradients
       (c_(true,n) = Re Phi_n, c_(false,n) = Im Phi_n), computed from the canonical relations (G5040 shape) exactly as
       in the landed G6001Sup1Core (omega_scaled); the landed inputs (gradient_physicalCoordinate, G5032Sup1 real-covector
       identities, G5040) are explicit hypotheses with exactly their landed conclusions, as in core6001, discharged in G6016;
   (2) `fderiv_actionField`: dPhi(v) X_{I_n}(v) = -i Phi_n(v) e_n, by expanding jacobianConjugate v X_{I_n} in the
       landed real Hilbert basis (adjoint identity G5012: A^* d_j = grad c_j);
   (3) `hasDerivAt_rotate`: d/ds rotateOneCoordinate n s z = -i (R_t z)_n e_n;
   (4) `core16`: G6-016 head from (2) (hypothesis `hfield`, discharged in G6016 by (2) with the landed inputs) and the inverse equations and analyticity of the global inverse (G6013/G6014 heads, passed
       as hypotheses of their exact types and discharged in G6016), via the chain rule and D Psi(Phi v) o D Phi(v) = id. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace

namespace NlsGge.GKDefinitionDesign
namespace G6016Aux
noncomputable section

theorem inner_I_smul_right (x y : PhysicalL2) :
    inner ℝ x ((Complex.I : ℂ) • y) = inner ℝ ((-Complex.I) • x) y := by
  rw [real_inner_eq_re_inner_g5012, real_inner_eq_re_inner_g5012, inner_smul_right,
    inner_smul_left]
  simp

theorem k1 : (1 / Real.sqrt 2 : ℝ) * (-1 / Real.sqrt 2) = -1 / 2 := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_mul_div_comm, hs]
  ring

theorem k2 : (-1 / Real.sqrt 2 : ℝ) * (1 / Real.sqrt 2) = -1 / 2 := by
  rw [mul_comm, k1]

/-- Symplectic pairings of the physical coordinate gradients (canonical relations G5040). -/
theorem omega_coord (v : PhysicalL2)
    (hcoord : ∀ j : Bool × ℤ, gradient (physicalCoordinate j) v =
      if j.1 then
        (1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianX j.2) (realSlice v))
      else
        (-1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianY j.2) (realSlice v)))
    (hX : ∀ k : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianX k) (realSlice v))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianX k) (realSlice v))).1)
    (hY : ∀ k : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianY k) (realSlice v))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianY k) (realSlice v))).1)
    (h40 : ∀ m n : ℤ,
      pairPoisson (cartesianX m) (cartesianX n) (realSlice v) = 0 ∧
      pairPoisson (cartesianX m) (cartesianY n) (realSlice v) =
        -(if m = n then (1 : ℂ) else 0) ∧
      pairPoisson (cartesianY m) (cartesianY n) (realSlice v) = 0)
    (j : Bool × ℤ) (n : ℤ) :
    inner ℝ ((-Complex.I) • gradient (physicalCoordinate j) v)
        (gradient (physicalCoordinate (true, n)) v) =
      (if j = (false, n) then 1 else 0) ∧
    inner ℝ ((-Complex.I) • gradient (physicalCoordinate j) v)
        (gradient (physicalCoordinate (false, n)) v) =
      (if j = (true, n) then -1 else 0) := by
  have gT : ∀ k : ℤ, gradient (physicalCoordinate (true, k)) v =
      (1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradientCLM (fderiv ℂ (cartesianX k) (realSlice v))) := by
    intro k
    rw [hcoord]
    rfl
  have gF : ∀ k : ℤ, gradient (physicalCoordinate (false, k)) v =
      (-1 / Real.sqrt 2 : ℝ) •
        pairGradientProjection (pairGradientCLM (fderiv ℂ (cartesianY k) (realSlice v))) := by
    intro k
    rw [hcoord]
    rfl
  have pXY : ∀ a b : ℤ, pairPoissonCLM (fderiv ℂ (cartesianX a) (realSlice v))
      (fderiv ℂ (cartesianY b) (realSlice v)) = -(if a = b then (1 : ℂ) else 0) :=
    fun a b => (h40 a b).2.1
  have pXX : ∀ a b : ℤ, pairPoissonCLM (fderiv ℂ (cartesianX a) (realSlice v))
      (fderiv ℂ (cartesianX b) (realSlice v)) = 0 := fun a b => (h40 a b).1
  have pYY : ∀ a b : ℤ, pairPoissonCLM (fderiv ℂ (cartesianY a) (realSlice v))
      (fderiv ℂ (cartesianY b) (realSlice v)) = 0 := fun a b => (h40 a b).2.2
  have pYX : ∀ a b : ℤ, pairPoissonCLM (fderiv ℂ (cartesianY a) (realSlice v))
      (fderiv ℂ (cartesianX b) (realSlice v)) = (if b = a then (1 : ℂ) else 0) := by
    intro a b
    rw [pairPoissonCLM_antisymm, pXY b a, neg_neg]
  obtain ⟨b, m⟩ := j
  cases b
  · refine ⟨?_, ?_⟩
    · rw [gF, gT, G6001Aux.omega_scaled _ _ _ _ (hX n) (hY m), pXY, k1]
      by_cases h : n = m
      · subst h
        simp
      · have h' : ¬ ((false, m) : Bool × ℤ) = (false, n) := fun e => h (Prod.ext_iff.1 e).2.symm
        rw [if_neg h, if_neg h']
        simp
    · rw [gF, gF, G6001Aux.omega_scaled _ _ _ _ (hY n) (hY m), pYY]
      simp
  · refine ⟨?_, ?_⟩
    · rw [gT, gT, G6001Aux.omega_scaled _ _ _ _ (hX n) (hX m), pXX]
      simp
    · rw [gT, gF, G6001Aux.omega_scaled _ _ _ _ (hY n) (hX m), pYX, k2]
      by_cases h : m = n
      · subst h
        simp
      · have h' : ¬ ((true, m) : Bool × ℤ) = (true, n) := fun e => h (Prod.ext_iff.1 e).2
        rw [if_neg h, if_neg h']
        simp

theorem differentiableAt_physicalCoordinate (v : PhysicalL2) (j : Bool × ℤ) :
    DifferentiableAt ℝ (physicalCoordinate j) v := by
  have hdΦ : DifferentiableAt ℝ sourceFamily.Phi v := (sourceFamily.Phi_analytic v).differentiableAt
  have he : DifferentiableAt ℝ (fun w : PhysicalL2 => sourceFamily.Phi w j.2) v :=
    ((lp.evalCLM ℝ (fun _ : ℤ => ℂ) 2 j.2).differentiableAt).comp v hdΦ
  obtain ⟨b, k⟩ := j
  cases b
  · show DifferentiableAt ℝ (fun w : PhysicalL2 => (sourceFamily.Phi w k).im) v
    exact Complex.imCLM.differentiableAt.comp v he
  · show DifferentiableAt ℝ (fun w : PhysicalL2 => (sourceFamily.Phi w k).re) v
    exact Complex.reCLM.differentiableAt.comp v he

theorem hasGradientAt_action (v : PhysicalL2) (n : ℤ) :
    HasGradientAt (fun w : PhysicalL2 => actualGapActionAllE02_38 w n)
      ((2 * physicalCoordinate (true, n) v) • gradient (physicalCoordinate (true, n)) v +
        (2 * physicalCoordinate (false, n) v) • gradient (physicalCoordinate (false, n)) v) v := by
  have hfun : (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) =
      fun w => physicalCoordinate (true, n) w * physicalCoordinate (true, n) w +
        physicalCoordinate (false, n) w * physicalCoordinate (false, n) w := by
    funext w
    rw [← sourceFamily.Phi_action w n, Complex.sq_norm, Complex.normSq_apply]
    rfl
  have hT := (hasGradientAt_iff_hasFDerivAt.1
    (differentiableAt_physicalCoordinate v (true, n)).hasGradientAt)
  have hF := (hasGradientAt_iff_hasFDerivAt.1
    (differentiableAt_physicalCoordinate v (false, n)).hasGradientAt)
  have h := (hT.mul hT).add (hF.mul hF)
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, inner_add_left, real_inner_smul_left, smul_eq_mul]
  ring

theorem physicalBirkhoff_eq_coords (v : PhysicalL2) (n : ℤ) :
    physicalBirkhoff v n =
      ((physicalCoordinate (true, n) v : ℝ) : ℂ) +
        ((physicalCoordinate (false, n) v : ℝ) : ℂ) * Complex.I := by
  show sourceFamily.Phi v n = ((sourceFamily.Phi v n).re : ℂ) + ((sourceFamily.Phi v n).im : ℂ) * Complex.I
  exact (Complex.re_add_im _).symm

/-- GK Theorem 20.1: the action field is mapped by dPhi to the unit coordinate rotation field. -/
theorem fderiv_actionField (v : PhysicalL2)
    (hgrad : ∀ j : Bool × ℤ,
      jacobianAdjoint v (physicalFourierBasis j) = gradient (physicalCoordinate j) v)
    (hcoord : ∀ j : Bool × ℤ, gradient (physicalCoordinate j) v =
      if j.1 then
        (1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianX j.2) (realSlice v))
      else
        (-1 / Real.sqrt 2 : ℝ) •
          pairGradientProjection (pairGradient (cartesianY j.2) (realSlice v)))
    (hX : ∀ k : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianX k) (realSlice v))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianX k) (realSlice v))).1)
    (hY : ∀ k : ℤ, star (pairGradientCLM (fderiv ℂ (cartesianY k) (realSlice v))).2 =
      (pairGradientCLM (fderiv ℂ (cartesianY k) (realSlice v))).1)
    (h40 : ∀ m n : ℤ,
      pairPoisson (cartesianX m) (cartesianX n) (realSlice v) = 0 ∧
      pairPoisson (cartesianX m) (cartesianY n) (realSlice v) =
        -(if m = n then (1 : ℂ) else 0) ∧
      pairPoisson (cartesianY m) (cartesianY n) (realSlice v) = 0)
    (n : ℤ) :
    fderiv ℝ physicalBirkhoff v
        (physicalHamiltonianField (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v) =
      lp.single 2 n (-Complex.I * physicalBirkhoff v n) := by
  have hgA := (hasGradientAt_action v n).gradient
  set cT : ℝ := physicalCoordinate (true, n) v with hcT
  set cF : ℝ := physicalCoordinate (false, n) v with hcF
  set X : PhysicalL2 :=
    physicalHamiltonianField (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v with hXd
  have hXe : X = -((1 / 2 : ℝ) • ((Complex.I : ℂ) •
      ((2 * cT) • gradient (physicalCoordinate (true, n)) v +
        (2 * cF) • gradient (physicalCoordinate (false, n)) v))) := by
    rw [hXd, physicalHamiltonianField, hgA]
  have hB : jacobianConjugate v X =
      cF • physicalFourierHilbertBasis (true, n) - cT • physicalFourierHilbertBasis (false, n) := by
    apply physicalFourierHilbertBasis.repr.injective
    ext j
    have ho := orthonormal_iff_ite.1 physicalFourierHilbertBasis.orthonormal
    rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, inner_sub_right,
      real_inner_smul_right, real_inner_smul_right, ho, ho,
      ← ContinuousLinearMap.adjoint_inner_left]
    change inner ℝ (jacobianAdjoint v (physicalFourierHilbertBasis j)) X = _
    rw [physicalFourierHilbertBasis_apply, hgrad j, hXe]
    rw [inner_neg_right,
      real_inner_smul_right, smul_add, inner_add_right, smul_comm (Complex.I : ℂ) (2 * cT),
      smul_comm (Complex.I : ℂ) (2 * cF), real_inner_smul_right, real_inner_smul_right,
      inner_I_smul_right, inner_I_smul_right, (omega_coord v hcoord hX hY h40 j n).1,
      (omega_coord v hcoord hX hY h40 j n).2]
    by_cases hj1 : j = (true, n)
    · subst hj1
      simp
    · by_cases hj2 : j = (false, n)
      · subst hj2
        simp
      · simp [hj1, hj2]
  have h1 : fderiv ℝ physicalBirkhoff v X = reflectedFourierL2 (jacobianConjugate v X) := by
    rw [show jacobianConjugate v X = reflectedFourierL2.symm (fderiv ℝ physicalBirkhoff v X) from rfl,
      LinearIsometryEquiv.apply_symm_apply]
  have hFs : ∀ (r : ℝ) (x : PhysicalL2), reflectedFourierL2 (r • x) = r • reflectedFourierL2 x := by
    intro r x
    first
    | exact map_smul_of_tower reflectedFourierL2 r x
    | exact (reflectedFourierL2.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).map_smul r x
  rw [h1, hB, physicalFourierHilbertBasis_apply, physicalFourierHilbertBasis_apply,
    map_sub, hFs, hFs]
  unfold physicalFourierBasis
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    physicalBirkhoff_eq_coords v n, ← hcT, ← hcF]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext k
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, lp.coeFn_smul, Pi.smul_apply, Pi.smul_apply]
  by_cases hk : k = n
  · subst hk
    rw [lp.single_apply_self, lp.single_apply_self, lp.single_apply_self, Complex.real_smul,
      Complex.real_smul, if_pos rfl, if_neg (by decide : ¬ (false = true))]
    linear_combination (↑cF : ℂ) * hI
  · rw [lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hk, lp.single_apply_ne _ _ _ hk,
      smul_zero, smul_zero, sub_zero]

theorem rotate_apply_self (n : ℤ) (t : ℝ) (z : Lib.L2Z) :
    rotateOneCoordinate n t z n = Complex.exp (-Complex.I * (t : ℂ)) * z n := by
  unfold rotateOneCoordinate
  simp
  ring

theorem rotate_zero (n : ℤ) (z : Lib.L2Z) : rotateOneCoordinate n 0 z = z := by
  unfold rotateOneCoordinate
  simp

theorem single_eq_smul (n : ℤ) (c : ℂ) :
    lp.single (E := fun _ : ℤ => ℂ) 2 n c = c • lp.single (E := fun _ : ℤ => ℂ) 2 n (1 : ℂ) := by
  rw [← lp.single_smul, smul_eq_mul, mul_one]

theorem hasDerivAt_rotate (n : ℤ) (z : Lib.L2Z) (t : ℝ) :
    HasDerivAt (fun s : ℝ => rotateOneCoordinate n s z)
      (lp.single 2 n (-Complex.I * rotateOneCoordinate n t z n)) t := by
  have h0 : HasDerivAt (fun s : ℝ => -Complex.I * (s : ℂ)) (-Complex.I) t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (-Complex.I)
  have hg := ((h0.cexp).sub_const 1).mul_const (z n)
  have hs := (hg.smul_const (lp.single 2 n (1 : ℂ))).const_add z
  have hfun : (fun s : ℝ => rotateOneCoordinate n s z) = fun s : ℝ =>
      z + ((Complex.exp (-Complex.I * (s : ℂ)) - 1) * z n) • lp.single 2 n (1 : ℂ) := by
    funext s
    unfold rotateOneCoordinate
    rw [single_eq_smul n ((Complex.exp (-Complex.I * (s : ℂ)) - 1) * z n)]
  rw [hfun, single_eq_smul n (-Complex.I * rotateOneCoordinate n t z n), rotate_apply_self]
  convert hs using 2
  ring

/-- Core of G6-016: the inverse equations and analyticity of the global inverse enter as hypotheses
(exactly the G6013 / G6014 conjuncts); discharged in G6016. -/
theorem core16
    (hfield : ∀ (v : PhysicalL2) (n : ℤ),
      fderiv ℝ physicalBirkhoff v
          (physicalHamiltonianField (fun w : PhysicalL2 => actualGapActionAllE02_38 w n) v) =
        lp.single 2 n (-Complex.I * physicalBirkhoff v n))
    (hL : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hR : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (hΨ : AnalyticOnNhd ℝ physicalInverseBirkhoff Set.univ) (n : ℤ) (u : PhysicalL2) :
  (fun t : ℝ => physicalInverseBirkhoff
    (rotateOneCoordinate n t (physicalBirkhoff u))) 0 = u ∧
  ∀ t : ℝ, HasDerivAt
    (fun s : ℝ => physicalInverseBirkhoff
      (rotateOneCoordinate n s (physicalBirkhoff u)))
    (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n)
      (physicalInverseBirkhoff (rotateOneCoordinate n t (physicalBirkhoff u)))) t := by
  refine ⟨?_, fun t => ?_⟩
  · show physicalInverseBirkhoff (rotateOneCoordinate n 0 (physicalBirkhoff u)) = u
    rw [rotate_zero, hL u]
  · have hrot := hasDerivAt_rotate n (physicalBirkhoff u) t
    set w : Lib.L2Z := rotateOneCoordinate n t (physicalBirkhoff u) with hw
    set v : PhysicalL2 := physicalInverseBirkhoff w with hv
    have hΦv : physicalBirkhoff v = w := hR w
    have hΨd : HasFDerivAt physicalInverseBirkhoff (fderiv ℝ physicalInverseBirkhoff w) w :=
      (hΨ w (Set.mem_univ _)).differentiableAt.hasFDerivAt
    have hchain := hΨd.comp_hasDerivAt t hrot
    have hdiff : DifferentiableAt ℝ physicalBirkhoff v :=
      (sourceFamily.Phi_analytic v).differentiableAt
    have hcomp : (fderiv ℝ physicalInverseBirkhoff w).comp (fderiv ℝ physicalBirkhoff v) =
        ContinuousLinearMap.id ℝ PhysicalL2 := by
      have hΨd' : HasFDerivAt physicalInverseBirkhoff (fderiv ℝ physicalInverseBirkhoff w)
          (physicalBirkhoff v) := by
        rw [hΦv]
        exact hΨd
      have h1 := hΨd'.comp v hdiff.hasFDerivAt
      have h2 : physicalInverseBirkhoff ∘ physicalBirkhoff = id := funext hL
      rw [h2] at h1
      exact h1.unique (hasFDerivAt_id v)
    have key : fderiv ℝ physicalInverseBirkhoff w (lp.single 2 n (-Complex.I * w n)) =
        physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n) v := by
      have h3 := congrArg (fun L : PhysicalL2 →L[ℝ] PhysicalL2 =>
        L (physicalHamiltonianField (fun v => actualGapActionAllE02_38 v n) v)) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h3
      rw [hfield v n, hΦv] at h3
      exact h3
    rw [← key]
    exact hchain

end
end G6016Aux
end NlsGge.GKDefinitionDesign
