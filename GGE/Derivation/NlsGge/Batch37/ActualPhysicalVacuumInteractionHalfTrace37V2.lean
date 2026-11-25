import NlsGge.Spectral.GenericRoughDysonAECongruence36V4
import NlsGge.Spectral.ActualPhysicalInteractionDysonIdentification32V2
import NlsGge.Spectral.ActualPhysicalUnitHalfTraceGeneralRescaling35V3
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-- Every positive-order actual interaction integral vanishes for the zero
physical potential. This uses the checked AE-safe zero-coupling realization,
not pointwise vanishing of an arbitrary Lp representative. -/
theorem actualPhysicalVacuumInteraction_positiveTerm_zero37V2
    (z : ℂ) (n : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 (0 : PhysicalL2) (s : SpectralCircle)) z)
      (n+1) t = 0 := by
  have h := actualPhysicalInteractionDysonTerm_realCoupling36V4
    (0 : PhysicalL2) 0 z (n+1) t ht
  simpa only [Complex.ofReal_zero, zero_smul, zero_pow (Nat.succ_ne_zero n)] using h

/-- The actual vacuum interaction Dyson series is summable entrywise and
equals the identity matrix. Summability is established before summation. -/
theorem actualPhysicalVacuumInteraction_summable_identity37V2
    (z : ℂ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i j : Fin 2, Summable (fun n => genericRoughMatrixDysonTerm32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 (0 : PhysicalL2) (s : SpectralCircle)) z)
      n t i j)) ∧
    genericRoughMatrixDysonTsum32
      (actualZsInteractionCoefficient32
        (fun s => naturalPhysicalCoverL2 (0 : PhysicalL2) (s : SpectralCircle)) z)
      t = 1 := by
  let B := actualZsInteractionCoefficient32
    (fun s => naturalPhysicalCoverL2 (0 : PhysicalL2) (s : SpectralCircle)) z
  have hz (n : ℕ) (hn : n ≠ 0) (i j : Fin 2) :
      genericRoughMatrixDysonTerm32 B n t i j = 0 := by
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ n =>
      have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j)
        (actualPhysicalVacuumInteraction_positiveTerm_zero37V2 z n t ht)
      simpa only [B, Matrix.zero_apply] using h
  have hs (i j : Fin 2) : Summable (fun n => genericRoughMatrixDysonTerm32 B n t i j) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    exact hz n (by simpa only [Finset.mem_singleton] using hn) i j
  refine ⟨hs, ?_⟩
  ext i j
  change (∑' n, genericRoughMatrixDysonTerm32 B n t i j) = _
  rw [tsum_eq_single 0 (fun n hn => hz n hn i j)]
  rfl

/-- The actual period-one half trace at zero potential is exactly cos z,
with the original free Fourier signs and endpoint one retained. -/
theorem actualPhysicalUnitHalfTrace_zeroPotential37V2 (z : ℂ) :
    actualPhysicalUnitHalfTrace32 (0 : PhysicalL2) z = Complex.cos z := by
  have hstate := actualPhysicalInteractionState_unit_eq_Dyson32 (0 : PhysicalL2) z
  rw [(actualPhysicalVacuumInteraction_summable_identity37V2 z 1 (by norm_num)).2] at hstate
  have hres := actualPhysicalUnitHalfTrace_generalRescaling35 (0 : PhysicalL2) z
  rw [hstate] at hres
  simp only [Matrix.one_apply, ite_true] at hres
  have hneg : Complex.exp (Complex.I*z)*Complex.exp (-z*Complex.I) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  have hdouble : Complex.exp (Complex.I*z)*Complex.exp (z*Complex.I) =
      Complex.exp (2*Complex.I*z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hcos : Complex.exp (Complex.I*z)*Complex.cos z =
      (1+Complex.exp (2*Complex.I*z))/2 := by
    calc
      _ = (Complex.exp (Complex.I*z)*Complex.exp (z*Complex.I)+
        Complex.exp (Complex.I*z)*Complex.exp (-z*Complex.I))/2 := by
        simp only [Complex.cos, mul_div, mul_add, neg_mul]
      _ = _ := by rw [hdouble, hneg]; ring
  apply mul_left_cancel₀ (Complex.exp_ne_zero (Complex.I*z))
  rw [hres, hcos]
  ring
end NlsGge.SpectralFoundations
end
