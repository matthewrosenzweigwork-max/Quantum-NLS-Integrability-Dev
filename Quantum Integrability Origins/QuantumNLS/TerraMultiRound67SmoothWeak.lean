import QuantumNLS.RelativeEnergyTransport
import QuantumNLS.TerraMultiRound66WeakMap
import QuantumNLS.TerraMultiRound59SobolevCoordinates

/-! Classical and weak first derivatives agree for a smooth H¹ representative. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open MeasureTheory
open QuantumNLS.ClassicalCharges QuantumNLS.RelativeEnergy QuantumNLS.TranslatedCorrelation
open QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.TerraMultiRound66WeakMap
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound49SobolevBridge
namespace QuantumNLS.TerraMultiRound67SmoothWeak
variable {L : ℝ} [Fact (0 < L)]

theorem smooth_lift_weak (f : ℝ → ℂ) (hf : SmoothPeriodic L f) :
    HasWeakDeriv ((memLp_of_continuous (continuous_lift hf)).toLp (lift hf))
      ((memLp_of_continuous (continuous_lift (sp_deriv hf))).toLp (lift (sp_deriv hf))) :=
  (isWD_iff_hasWeakDeriv (memLp_of_continuous (continuous_lift hf))
    (memLp_of_continuous (continuous_lift (sp_deriv hf)))).1 (IsWD.smooth hf)

theorem contRep_eq_lift (u : Hk L 1) (hf : SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))) :
    (contRep (by omega) u : AddCircle L → ℂ) = lift hf := by
  funext x
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  calc
    _ = contRep (by omega) (physicalToHk 1 (coordinates (L := L) 1 u)) (x : AddCircle L) := by rw [physical_coordinates]
    _ = physRep L 1 (coordinates (L := L) 1 u) x := by
      simpa only [Nat.cast_one] using physicalToHk_rep (L := L) (k := 1) (by omega) (coordinates (L := L) 1 u) x
    _ = lift hf (x : AddCircle L) := (lift_coe hf x).symm

theorem smooth_weakD_eq (u : Hk L 1) (hf : SmoothPeriodic L (physRep L 1 (coordinates (L := L) 1 u))) :
    weakD u = (memLp_of_continuous (continuous_lift (sp_deriv hf))).toLp (lift (sp_deriv hf)) := by
  have he : u.val = (memLp_of_continuous (continuous_lift hf)).toLp (lift hf) := by
    apply Lp.ext
    filter_upwards [ae_eq_contRep (by omega) u,
      (memLp_of_continuous (continuous_lift hf)).coeFn_toLp] with x hx hy
    rw [hx, hy, contRep_eq_lift u hf]
  apply hasWeakDeriv_unique (weakD_is_derivative u)
  rw [he]
  exact smooth_lift_weak _ hf

#print axioms smooth_lift_weak
#print axioms contRep_eq_lift
#print axioms smooth_weakD_eq
end QuantumNLS.TerraMultiRound67SmoothWeak
