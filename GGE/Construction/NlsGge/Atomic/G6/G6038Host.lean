import Mathlib
import NlsGge.GK38.Lib.ParamProductsRoot
import NlsGge.GK38.Lib.InterpolationTail

                                                                                                                          
                                                                                                                      
                                                                                                            
                                                                                                      
                                                                                                             
                                                            
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev ComplexActionSpace := lp (fun _ : ℤ => ℂ) 1
abbrev ComplexDiagonalSpace := lp (fun _ : ℤ => ℂ) 2

theorem complexActionRoot_mem (I : ComplexActionSpace) :
  Memℓp (fun n : ℤ => Complex.sqrt (I n)) 2 := by
  refine memℓp_gen ?_
  have he : (fun n : ℤ => ‖Complex.sqrt (I n)‖ ^ (2 : ℝ≥0∞).toReal) = fun n => ‖I n‖ := by
    funext n
    rw [ENNReal.toReal_ofNat, Real.rpow_two, ← norm_pow, NlsGge.GK38.Lib.sqrt_sq]
  rw [he]
  have h := (lp.memℓp I).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_one, Real.rpow_one] using h

def complexActionRoot (I : ComplexActionSpace) : ComplexDiagonalSpace :=
  ⟨fun n => Complex.sqrt (I n), complexActionRoot_mem I⟩

def actionDescent (f : ComplexDiagonalSpace → ℂ) (I : ComplexActionSpace) : ℂ :=
  f (complexActionRoot I)

def truncateComplexActions (N : ℕ) (I : ComplexActionSpace) : ComplexActionSpace :=
  ∑ n ∈ Lib.win N, lp.single 1 n (I n)

def finiteActionDescent (f : ComplexDiagonalSpace → ℂ) (N : ℕ)
    (I : ComplexActionSpace) : ℂ :=
  actionDescent f (truncateComplexActions N I)

end
end NlsGge.GKDefinitionDesign
