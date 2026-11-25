import QuantumNLS.TerraMultiRound65FourthCore
import QuantumNLS.WeakDerivatives

/-! The first weak derivative exists uniquely on the realized H¹ field space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open QuantumNLS.TranslatedCorrelation QuantumNLS.WeakDerivatives QuantumNLS.Fourier
open QuantumNLS.Sobolev
namespace QuantumNLS.TerraMultiRound66WeakFirst

theorem exists_unique_first_weak_derivative (L : ℝ) [Fact (0 < L)] (u : Hk L 1) :
    ∃! g, HasWeakDeriv u.val g := by
  have hm : MemHs L 1 (fun n => coeff L u.val n) := by
    have h := u.summable
    simpa only [def002, fourierL2_apply, MemHs, Nat.cast_one] using h
  obtain ⟨g, hg⟩ := (exists_hasWeakDeriv_iff_memHs u.val).2 hm
  exact ⟨g, hg, fun y hy => hasWeakDeriv_unique hy hg⟩

#print axioms exists_unique_first_weak_derivative
end QuantumNLS.TerraMultiRound66WeakFirst
