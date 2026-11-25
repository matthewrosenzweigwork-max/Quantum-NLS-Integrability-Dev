import QuantumNLS.TerraMultiRound59ContinuousForm

/-! Correlation coefficients are independent of the Sobolev realization of their factors. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59OrderCompatibility
open QuantumNLS.TranslatedCorrelation QuantumNLS.TerraMultiRound51TaylorIntegral
open QuantumNLS.TerraMultiRound59ContinuousForm

variable {L : ℝ} [Fact (0 < L)]

theorem cfun_order_compatible {q k l : ℕ} (f : Fin q → Hk L k) (g : Fin q → Hk L l)
    (hfg : ∀ i, (f i).val = (g i).val) : Cfun f = Cfun g := by
  funext h
  unfold Cfun
  congr 1
  funext x
  congr 1
  funext i
  rw [hfg i]

theorem integrated_order_compatible {n q k l d : ℕ}
    (paths : Fin q → Finset (Fin n)) (f : Fin q → Hk L k) (g : Fin q → Hk L l)
    (hfg : ∀ i, (f i).val = (g i).val) :
    integratedCoeff (Cfun f) paths d = integratedCoeff (Cfun g) paths d := by
  rw [cfun_order_compatible f g hfg]

theorem continuous_forms_order_compatible {n m k l d : ℕ}
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hdk : d ≤ 2 * k) (hdl : d ≤ 2 * l)
    (paths : Fin (m + 2) → Finset (Fin n))
    (f : Fin (m + 2) → Hk L k) (g : Fin (m + 2) → Hk L l)
    (hfg : ∀ i, (f i).val = (g i).val) :
    continuousIntegratedForm hk hdk paths f = continuousIntegratedForm hl hdl paths g := by
  simp only [continuousIntegratedForm_apply]
  exact integrated_order_compatible paths f g hfg

#print axioms cfun_order_compatible
#print axioms integrated_order_compatible
#print axioms continuous_forms_order_compatible
end QuantumNLS.TerraMultiRound59OrderCompatibility
