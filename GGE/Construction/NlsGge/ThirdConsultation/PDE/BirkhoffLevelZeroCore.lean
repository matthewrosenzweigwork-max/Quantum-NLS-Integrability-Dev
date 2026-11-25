import Mathlib
import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Birkhoff.F01Determinant38

                                                                                                                            
                                                                                                                      
                                                                                                                    
                                                                                                                       
                                                                                                                    
                                                                                                                      
                                                                 
set_option autoImplicit false
open Set
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
namespace NlsGge.ThirdConsultation.PDE
noncomputable section

namespace BirkhoffLevelZeroCore

/-- Coefficientwise map `ℓ²(ℤ) → h⁰`. -/
def toCarrier0 (w : lp (fun _ : ℤ => ℂ) 2) : SobolevCarrier38 ((0 : ℕ) : ℝ) :=
  carrierZero38 (w : ℤ → ℂ) ((mem_seqSobolev38_zero_iff _).2 (lp.memℓp w))

/-- Coefficientwise map `h⁰ → ℓ²(ℤ)`. -/
def ofCarrier0 (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) : lp (fun _ : ℤ => ℂ) 2 :=
  seqToLp38 (carrierCoe38 _ x) (carrierCoe38_mem_zero x)

theorem toCarrier0_coe (w : lp (fun _ : ℤ => ℂ) 2) :
    carrierCoe38 ((0 : ℕ) : ℝ) (toCarrier0 w) = (w : ℤ → ℂ) :=
  carrierCoe38_carrierZero38 _ _

theorem ofCarrier0_coe (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    ((ofCarrier0 x : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) = carrierCoe38 ((0 : ℕ) : ℝ) x := rfl

theorem carrierCoe0_add (x y : SobolevCarrier38 ((0 : ℕ) : ℝ)) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (x + y) n =
      carrierCoe38 ((0 : ℕ) : ℝ) x n + carrierCoe38 ((0 : ℕ) : ℝ) y n := rfl

theorem carrierCoe0_smul (c : ℝ) (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (c • x) n = (c : ℂ) * carrierCoe38 ((0 : ℕ) : ℝ) x n := by
  change ((c : ℝ) • (carrierCoe38 ((0 : ℕ) : ℝ) x)) n = _
  simp [Complex.real_smul]

theorem toCarrier0_add (a b : lp (fun _ : ℤ => ℂ) 2) :
    toCarrier0 (a + b) = toCarrier0 a + toCarrier0 b := by
  apply carrierExt38
  funext n
  rw [carrierCoe0_add, toCarrier0_coe, toCarrier0_coe, toCarrier0_coe, lp.coeFn_add, Pi.add_apply]

theorem toCarrier0_smul (c : ℝ) (a : lp (fun _ : ℤ => ℂ) 2) :
    toCarrier0 (c • a) = c • toCarrier0 a := by
  apply carrierExt38
  funext n
  rw [carrierCoe0_smul, toCarrier0_coe, toCarrier0_coe, lp.coeFn_smul, Pi.smul_apply,
    Complex.real_smul]

theorem ofCarrier0_toCarrier0 (w : lp (fun _ : ℤ => ℂ) 2) : ofCarrier0 (toCarrier0 w) = w := by
  apply lp.ext
  rw [ofCarrier0_coe, toCarrier0_coe]

theorem toCarrier0_ofCarrier0 (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) : toCarrier0 (ofCarrier0 x) = x := by
  apply carrierExt38
  rw [toCarrier0_coe, ofCarrier0_coe]

theorem norm_toCarrier0 (w : lp (fun _ : ℤ => ℂ) 2) : ‖toCarrier0 w‖ = ‖w‖ := by
  have h1 := carrier_hasSum_norm_sq_zero38 (toCarrier0 w)
  rw [toCarrier0_coe] at h1
  have h2 := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) w
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.unique h2)

/-- `ℓ²(ℤ)` as the level-zero real carrier (same coefficients). -/
def l2Carrier0 : lp (fun _ : ℤ => ℂ) 2 ≃ₗᵢ[ℝ] SobolevCarrier38 ((0 : ℕ) : ℝ) where
  toFun := toCarrier0
  invFun := ofCarrier0
  map_add' := toCarrier0_add
  map_smul' := toCarrier0_smul
  left_inv := ofCarrier0_toCarrier0
  right_inv := toCarrier0_ofCarrier0
  norm_map' := norm_toCarrier0

theorem l2Carrier0_coe (w : lp (fun _ : ℤ => ℂ) 2) :
    carrierCoe38 ((0 : ℕ) : ℝ) (l2Carrier0 w) = (w : ℤ → ℂ) :=
  toCarrier0_coe w

theorem l2Carrier0_symm_apply (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    l2Carrier0.symm x = seqToLp38 (carrierCoe38 _ x) (carrierCoe38_mem_zero x) := rfl

theorem l2Carrier0_clm_coe (w : lp (fun _ : ℤ => ℂ) 2) :
    carrierCoe38 ((0 : ℕ) : ℝ) (l2Carrier0.toContinuousLinearEquiv.toContinuousLinearMap w) =
      (w : ℤ → ℂ) :=
  toCarrier0_coe w

theorem l2Carrier0_symm_coe (x : SobolevCarrier38 ((0 : ℕ) : ℝ)) :
    ((l2Carrier0.symm x : lp (fun _ : ℤ => ℂ) 2) : ℤ → ℂ) = carrierCoe38 ((0 : ℕ) : ℝ) x := rfl

/-- The standard symplectic form on `ℓ²` is `⟪i a, b⟫_ℝ` (absolutely summable). -/
theorem stdSymplectic38_lp (a b : lp (fun _ : ℤ => ℂ) 2) :
    stdSymplectic38 (a : ℤ → ℂ) (b : ℤ → ℂ) = inner ℝ ((Complex.I : ℂ) • a) b := by
  have h1 := stdSymplectic38_eq_inner (l2Carrier0 a) (l2Carrier0 b)
  have hJ : J38 _ (l2Carrier0 a) = l2Carrier0 ((Complex.I : ℂ) • a) :=
    carrierExt38 (funext fun n => by
      rw [carrierCoe38_J38, l2Carrier0_coe, l2Carrier0_coe, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul])
  rw [hJ, LinearIsometryEquiv.inner_map_map, l2Carrier0_coe, l2Carrier0_coe] at h1
  exact h1

section Transport

variable (f : (ℤ → ℂ) → (ℤ → ℂ)) (P : lp (fun _ : ℤ => ℂ) 2 → lp (fun _ : ℤ => ℂ) 2)
  (hf : ∀ (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0), f x = (P (seqToLp38 x hx) : ℤ → ℂ))
  (hmap : ∀ x ∈ seqSobolev38 ((0 : ℕ) : ℝ), f x ∈ seqSobolev38 ((0 : ℕ) : ℝ))

include hf in
theorem carrierMap38_zero_eq :
    carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap =
      fun x => l2Carrier0 (P (l2Carrier0.symm x)) := by
  funext x
  apply carrierExt38
  rw [carrierMap38_coe, hf _ (carrierCoe38_mem_zero x), l2Carrier0_coe, l2Carrier0_symm_apply]

include hf in
theorem analytic_zero_of (hP : AnalyticOnNhd ℝ P Set.univ) :
    AnalyticOnNhd ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap) Set.univ := by
  rw [carrierMap38_zero_eq f P hf hmap]
  intro x _
  have hS : AnalyticAt ℝ (fun y => l2Carrier0.symm y) x :=
    l2Carrier0.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt x
  have hE : AnalyticAt ℝ (fun w => l2Carrier0 w) (P (l2Carrier0.symm x)) :=
    l2Carrier0.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _
  have h2 : AnalyticAt ℝ (fun y => P (l2Carrier0.symm y)) x :=
    AnalyticAt.comp (g := P) (f := fun y => l2Carrier0.symm y) (hP _ (Set.mem_univ _)) hS
  exact AnalyticAt.comp (g := fun w => l2Carrier0 w) (f := fun y => P (l2Carrier0.symm y)) hE h2

include hf in
theorem continuous_zero_of (hP : AnalyticOnNhd ℝ P Set.univ) :
    Continuous (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap) :=
  continuous_iff_continuousAt.2 fun x =>
    (analytic_zero_of f P hf hmap hP x (Set.mem_univ x)).continuousAt

include hf in
theorem hasFDerivAt_zero_of (w : lp (fun _ : ℤ => ℂ) 2)
    (D : lp (fun _ : ℤ => ℂ) 2 →L[ℝ] lp (fun _ : ℤ => ℂ) 2) (hD : HasFDerivAt P D w) :
    HasFDerivAt (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap)
      ((l2Carrier0.toContinuousLinearEquiv.toContinuousLinearMap).comp
        (D.comp l2Carrier0.symm.toContinuousLinearEquiv.toContinuousLinearMap)) (l2Carrier0 w) := by
  rw [carrierMap38_zero_eq f P hf hmap]
  have hS := l2Carrier0.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    (x := l2Carrier0 w)
  have hw : l2Carrier0.symm (l2Carrier0 w) = w := l2Carrier0.symm_apply_apply w
  have hD' : HasFDerivAt P D
      (l2Carrier0.symm.toContinuousLinearEquiv.toContinuousLinearMap (l2Carrier0 w)) := by
    show HasFDerivAt P D (l2Carrier0.symm (l2Carrier0 w))
    rw [hw]
    exact hD
  have hE := l2Carrier0.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    (x := P (l2Carrier0.symm (l2Carrier0 w)))
  exact hE.comp (l2Carrier0 w) (hD'.comp (l2Carrier0 w) hS)

include hf in
theorem fderiv_zero_of
    (hP0 : HasFDerivAt P (ContinuousLinearMap.id ℝ (lp (fun _ : ℤ => ℂ) 2)) 0) :
    fderiv ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap) 0 =
      ContinuousLinearMap.id ℝ (SobolevCarrier38 ((0 : ℕ) : ℝ)) := by
  have h := hasFDerivAt_zero_of f P hf hmap 0 _ hP0
  rw [map_zero] at h
  rw [h.fderiv]
  refine ContinuousLinearMap.ext fun x => ?_
  show l2Carrier0 (l2Carrier0.symm x) = x
  exact l2Carrier0.apply_symm_apply x

include hf in
theorem canonical_zero_of (hPd : ∀ w, DifferentiableAt ℝ P w)
    (hPc : ∀ w h k : lp (fun _ : ℤ => ℂ) 2,
      stdSymplectic38 (fderiv ℝ P w h : ℤ → ℂ) (fderiv ℝ P w k : ℤ → ℂ) =
        stdSymplectic38 (h : ℤ → ℂ) (k : ℤ → ℂ)) :
    ∀ x ξ η : SobolevCarrier38 ((0 : ℕ) : ℝ),
      stdSymplectic38
          (carrierCoe38 _ (fderiv ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap) x ξ))
          (carrierCoe38 _ (fderiv ℝ (carrierMap38 ((0 : ℕ) : ℝ) ((0 : ℕ) : ℝ) f hmap) x η)) =
        stdSymplectic38 (carrierCoe38 _ ξ) (carrierCoe38 _ η) := by
  intro x ξ η
  have hx : l2Carrier0 (l2Carrier0.symm x) = x := l2Carrier0.apply_symm_apply x
  have h := hasFDerivAt_zero_of f P hf hmap (l2Carrier0.symm x) _ (hPd _).hasFDerivAt
  rw [hx] at h
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, l2Carrier0_clm_coe,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, l2Carrier0_clm_coe,
    ← ofCarrier0_coe ξ, ← ofCarrier0_coe η]
  exact hPc (l2Carrier0.symm x) (l2Carrier0.symm ξ) (l2Carrier0.symm η)

end Transport

end BirkhoffLevelZeroCore

end
end NlsGge.ThirdConsultation.PDE
