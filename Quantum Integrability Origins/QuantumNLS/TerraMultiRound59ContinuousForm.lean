import QuantumNLS.TerraMultiRound59IntegratedBound

/-! The REG-006 correlation coefficient is a continuous multilinear form. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59ContinuousForm
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.TerraMultiRound59IntegratedForm QuantumNLS.TerraMultiRound59IntegratedBound

variable {L : ℝ} [Fact (0 < L)]

def continuousIntegratedForm {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (m + 2) => Hk L k) ℂ :=
  (integratedForm hk hd paths).mkContinuous (bound L n m k d)
    (fun f => integrated_coeff_bound hk hd paths f)

@[simp] theorem continuousIntegratedForm_apply {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) (f : Fin (m + 2) → Hk L k) :
    continuousIntegratedForm hk hd paths f = integratedCoeff (Cfun f) paths d := rfl

#print axioms continuousIntegratedForm
#print axioms continuousIntegratedForm_apply
end QuantumNLS.TerraMultiRound59ContinuousForm
