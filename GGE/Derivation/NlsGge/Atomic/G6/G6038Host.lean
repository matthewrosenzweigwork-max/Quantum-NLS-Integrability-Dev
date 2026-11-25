import Mathlib
import NlsGge.GK38.Lib.ParamProductsRoot
import NlsGge.GK38.Lib.InterpolationTail

/- G6038 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6038Host.lean.
   Hosts ONCE the G6-038 design names, bodies byte-identical to followup13 DEFINITIONS/G6.lean.md:211,213 and 277-295,
   namespace NlsGge.GKDefinitionDesign: ComplexActionSpace, ComplexDiagonalSpace, the constructor obligation
   complexActionRoot_mem (proved here: ‖√a‖² = ‖a‖ by the landed NlsGge.GK38.Lib.sqrt_sq, and I ∈ ℓ¹),
   complexActionRoot, actionDescent, truncateComplexActions, finiteActionDescent.  Complex.sqrt is Mathlib's.
   grep NlsGge/ (2026-11-02): none of these names exists. -/
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
