import Mathlib
import NlsGge.Atomic.G6.G6036Host

                                                                                                                          
                                                                             
                                                                                                                 
                                                                                                                     
                                                                                                                      
                                                                                                            
                                                                                                        
                                                                                                                      
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6036S
noncomputable section

/-- The coordinate projection `x ↦ x_n e_n` on the real diagonal space. -/
def projN (n : ℤ) : RealDiagonalSpace →L[ℝ] RealDiagonalSpace :=
  LinearMap.mkContinuous
    { toFun := fun x => lp.single 2 n (x n)
      map_add' := fun x y => by
        apply lp.ext; funext m
        simp only [lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.single_apply]
        split_ifs <;> simp
      map_smul' := fun c x => by
        apply lp.ext; funext m
        simp only [lp.single_apply, lp.coeFn_smul, Pi.smul_apply, Pi.single_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> simp }
    1 (fun x => by
      rw [one_mul]
      show ‖lp.single (E := fun _ : ℤ => ℝ) 2 n (x n)‖ ≤ ‖x‖
      rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
      exact lp.norm_apply_le_norm (by norm_num) x n)

def flipR (n : ℤ) : RealDiagonalSpace →L[ℝ] RealDiagonalSpace :=
  ContinuousLinearMap.id ℝ RealDiagonalSpace - (2 : ℝ) • projN n

theorem flipR_coe (n : ℤ) (x : RealDiagonalSpace) (m : ℤ) :
    (flipR n x : ℤ → ℝ) m = if m = n then -x m else x m := by
  show (x - (2 : ℝ) • lp.single 2 n (x n) : RealDiagonalSpace) m = _
  simp only [lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply, lp.single_apply, Pi.single_apply,
    smul_eq_mul]
  split_ifs with h
  · subst h; ring
  · ring

theorem flipR_flipR (n : ℤ) (x : RealDiagonalSpace) : flipR n (flipR n x) = x := by
  apply lp.ext; funext m
  rw [flipR_coe, flipR_coe]
  split_ifs <;> simp

def flipE (n : ℤ) : RealDiagonalSpace ≃L[ℝ] RealDiagonalSpace :=
  ContinuousLinearEquiv.equivOfInverse (flipR n) (flipR n) (flipR_flipR n) (flipR_flipR n)

theorem coe_diag (x : RealDiagonalSpace) (m : ℤ) :
    carrierCoe38 ((1 : ℕ) : ℝ) (diagonalToSobolev x) m =
      diagonalPhase * ((x m / Real.sqrt (actionWeight m) : ℝ) : ℂ) := by
  unfold diagonalToSobolev
  rw [carrierCoe38_mk]

theorem diagH_flip
    (h33 : ∀ z w : SobolevCarrier38 ((1 : ℕ) : ℝ),
      (∀ n : ℤ, ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2 = ‖carrierCoe38 ((1 : ℕ) : ℝ) w n‖^2) →
      transformedNLSHamiltonian z = transformedNLSHamiltonian w)
    (n : ℤ) (x : RealDiagonalSpace) : diagonalHamiltonian (flipR n x) = diagonalHamiltonian x := by
  unfold diagonalHamiltonian
  apply h33
  intro m
  rw [coe_diag, coe_diag, flipR_coe]
  split_ifs
  · rw [neg_div, Complex.ofReal_neg, mul_neg, norm_neg]
  · rfl

theorem flipR_single (n m : ℤ) :
    flipR n (lp.single 2 m (1 : ℝ)) = (if m = n then (-1 : ℝ) else 1) • lp.single 2 m (1 : ℝ) := by
  apply lp.ext; funext i
  rw [flipR_coe]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  split_ifs <;> simp_all

theorem G6036_of
    (h33 : ∀ z w : SobolevCarrier38 ((1 : ℕ) : ℝ),
      (∀ n : ℤ, ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2 = ‖carrierCoe38 ((1 : ℕ) : ℝ) w n‖^2) →
      transformedNLSHamiltonian z = transformedNLSHamiltonian w)
    (x₀ : RealDiagonalSpace)
    (hfin : (Function.support (x₀ : ℤ → ℝ)).Finite)
    (k : ℕ) (α : Fin k → ℤ) (n : ℤ)
    (hinactive : n ∉ Function.support (x₀ : ℤ → ℝ))
    (hodd : Odd ((Finset.univ.filter (fun j : Fin k => α j = n)).card)) :
  iteratedFDeriv ℝ k diagonalHamiltonian x₀
    (fun j : Fin k => lp.single 2 (α j) (1 : ℝ)) = 0 := by
  have hx0 : x₀ n = 0 := Function.notMem_support.1 hinactive
  have hEx : flipE n x₀ = x₀ := by
    apply lp.ext; funext m
    show (flipR n x₀ : ℤ → ℝ) m = x₀ m
    rw [flipR_coe]
    split_ifs with h
    · subst h; rw [hx0, neg_zero]
    · rfl
  have hcomp : diagonalHamiltonian ∘ (flipE n) = diagonalHamiltonian :=
    funext fun x => diagH_flip h33 n x
  have h := (flipE n).iteratedFDerivWithin_comp_right diagonalHamiltonian uniqueDiffOn_univ
    (Set.mem_univ (flipE n x₀)) k
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  rw [hcomp, hEx] at h
  have h2 := congrArg (fun M => M (fun j : Fin k => lp.single 2 (α j) (1 : ℝ))) h
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  have hv : (fun j : Fin k => ((flipE n : RealDiagonalSpace ≃L[ℝ] RealDiagonalSpace) :
      RealDiagonalSpace →L[ℝ] RealDiagonalSpace) (lp.single 2 (α j) (1 : ℝ))) =
      fun j => (if α j = n then (-1 : ℝ) else 1) • lp.single 2 (α j) (1 : ℝ) :=
    funext fun j => flipR_single n (α j)
  rw [hv, ContinuousMultilinearMap.map_smul_univ, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
    mul_one, hodd.neg_one_pow, neg_one_smul] at h2
  linarith

end
end NlsGge.ThirdConsultation.G6036S
