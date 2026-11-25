import Mathlib
import QuantumNLS.RiccatiMainFull
import QuantumNLS.RiccatiFourierBase

/-!
# R-3FEAD88B discharge: `RiccatiPrintedConclusion` for smooth periodic profiles

For a smooth periodic `f`, the frozen base lemma `RiccatiFourierBase.riccati_fourier_base` supplies
an Ell2 base with `physRep L a (lowT L a S base) = f`, and the frozen `RiccatiMainFull.riccati_main_full`
builds the `LocalOutput` at every admissible `(M, a, δ, S, K)`. This closes
`SmoothScalarMomentsPrerequisite.RiccatiPrintedConclusion L f` for smooth periodic `f`.

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Set

namespace QuantumNLS.RiccatiDischarge

open QuantumNLS.SmoothScalarMomentsPrerequisite QuantumNLS.ClassicalCharges
open QuantumNLS.RiccatiFourierBase QuantumNLS.RiccatiMainFull

theorem riccati_printed_conclusion_of_smooth (L : ℝ) [Fact (0 < L)] {f : ℝ → ℂ}
    (hf : SmoothPeriodic L f) : RiccatiPrintedConclusion L f := by
  intro M hM a δ ha hδ _hδ1 S hS K hK hKpos
  have hL : 0 < L := Fact.out
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have haS : a + (M : ℝ) + 1 ≤ (S : ℝ) := by linarith
  have haS' : a ≤ (S : ℝ) := by linarith
  obtain ⟨base, hbase⟩ := riccati_fourier_base hL ha haS' hf
  exact riccati_main_full L hL ha hM haS hδ hK hKpos base hbase

#print axioms QuantumNLS.RiccatiDischarge.riccati_printed_conclusion_of_smooth
#print axioms QuantumNLS.RiccatiMainFull.riccati_main_full
#print axioms QuantumNLS.RiccatiMainFull.deriv_opnorm_le
#print axioms QuantumNLS.RiccatiMainFull.modeSum_analyticAt
#print axioms QuantumNLS.RiccatiModeAnalytic.logTrace_analyticAt
#print axioms QuantumNLS.RiccatiModeAnalytic.one_add_exp_mem_slit
#print axioms QuantumNLS.RiccatiCoeffAnalytic.coeffs_analyticAt
#print axioms QuantumNLS.RiccatiCoeffAnalytic.chg_analyticAt
#print axioms QuantumNLS.RiccatiSectorBounds.exists_R
#print axioms QuantumNLS.RiccatiSectorBounds.sector_facts
#print axioms QuantumNLS.RiccatiFourierBase.riccati_fourier_base

end QuantumNLS.RiccatiDischarge
