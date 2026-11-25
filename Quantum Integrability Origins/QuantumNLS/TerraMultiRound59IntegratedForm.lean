import QuantumNLS.TerraMultiRound59IntegratedLinear

/-! The integrated differentiated correlation as a factor-slot multilinear map. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59IntegratedForm
open QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound51TaylorIntegral QuantumNLS.TerraMultiRound59IntegratedLinear

variable {L : ℝ} [Fact (0 < L)]

def integratedForm {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) :
    MultilinearMap ℂ (fun _ : Fin (m + 2) => Hk L k) ℂ :=
  MultilinearMap.mk' (fun f => integratedCoeff (Cfun f) paths d)
    (fun f i a b => integrated_update_add hk hd f i a b paths)
    (fun f i c a => by
      simpa only [smul_eq_mul] using integrated_update_smul hk hd f i c a paths)

@[simp] theorem integratedForm_apply {n m k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (paths : Fin (m + 2) → Finset (Fin n)) (f : Fin (m + 2) → Hk L k) :
    integratedForm hk hd paths f = integratedCoeff (Cfun f) paths d := rfl

#print axioms integratedForm
#print axioms integratedForm_apply
end QuantumNLS.TerraMultiRound59IntegratedForm
