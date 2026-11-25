import Mathlib
import QuantumNLS.LocalSpectralOperator
import QuantumNLS.RootMassBoostSymbol
import QuantumNLS.BornTranslation
import QuantumNLS.ResetNormalizationBinding
import QuantumNLS.Local001TransportB
import QuantumNLS.Local020Mul2

/-! LOCAL-020: interval representatives (`circleRep`) of the symmetry images of `u ∈ L²(𝕋_L)`.

For `R = reflectR`, `star`, scalar multiplication, `boost` and `trans`, the representative of the image is, `μI L`-a.e.,
the explicit transformed function of `circleRep u` used by the operator-level stages. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
noncomputable section

open MeasureTheory Set Filter QuantumNLS.LocalSpectral ComplexConjugate
open QuantumNLS.PhysicalTensor (L2T)

namespace QuantumNLS.Local020Rep

variable {L : ℝ} [Fact (0 < L)]

theorem circleRep_ae_fun {v : L2T L} {f : AddCircle L → ℂ} (h : (v : AddCircle L → ℂ) =ᵐ[volume] f) :
    (fun x : ℝ => circleRep v x) =ᵐ[μI L] fun x : ℝ => f (x : AddCircle L) := by
  have := QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.circle_ae_to_interval (L := L)
    (P := fun x => (v : AddCircle L → ℂ) x = f x) h
  exact this

theorem circleRep_periodic (u : L2T L) (x : ℝ) : circleRep u (x + L) = circleRep u x := by
  unfold circleRep
  congr 1
  rw [AddCircle.coe_add, AddCircle.coe_period, add_zero]

theorem circleRep_refl (u : L2T L) :
    circleRep (QuantumNLS.ResetNormalizationUniqueness.reflectR L u) =ᵐ[μI L]
      fun x => circleRep u (L - x) := by
  have h := circleRep_ae_fun (QuantumNLS.ResetNormalizationUniqueness.coeFn_reflectR L u)
  refine h.trans (Eventually.of_forall fun x => ?_)
  simp only [circleRep]
  congr 1
  rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]

theorem circleRep_star (u : L2T L) :
    circleRep (star u) =ᵐ[μI L] fun x => conj (circleRep u x) := by
  have h := circleRep_ae_fun (QuantumNLS.ResetNormalizationUniqueness.coeFn_cj L u)
  exact h

theorem circleRep_smul (c : ℂ) (u : L2T L) :
    circleRep (c • u) =ᵐ[μI L] fun x => c * circleRep u x := by
  have h := circleRep_ae_fun (v := c • u) (f := fun y => c * u y) (by
    filter_upwards [Lp.coeFn_smul c u] with y hy
    rw [hy]; rfl)
  exact h

theorem circleRep_trans (y : ℝ) (u : L2T L) :
    circleRep (QuantumNLS.BornTranslation.trans y u) =ᵐ[μI L] fun x => circleRep u (x + y) := by
  have h := circleRep_ae_fun (QuantumNLS.BornTranslation.coeFn_trans y u)
  refine h.trans (Eventually.of_forall fun x => ?_)
  simp only [circleRep]
  rfl

theorem circleRep_boost (k : ℤ) (u : L2T L) :
    circleRep (QuantumNLS.RootMassBoostSymbol.boost k u) =ᵐ[μI L]
      QuantumNLS.Local020Mul2.upb 0 (pm L k / 2) (circleRep u) := by
  have h := circleRep_ae_fun (QuantumNLS.RootMassBoostSymbol.coe_boost k u)
  refine h.trans (Eventually.of_forall fun x => ?_)
  simp only [circleRep, QuantumNLS.Local020Mul2.upb, QuantumNLS.Local020Mul2.bf]
  rw [fourier_coe_apply, ← Complex.exp_nat_mul]
  congr 2
  unfold pm
  push_cast
  ring

end QuantumNLS.Local020Rep

#print axioms QuantumNLS.Local020Rep.circleRep_boost
#print axioms QuantumNLS.Local020Rep.circleRep_refl
