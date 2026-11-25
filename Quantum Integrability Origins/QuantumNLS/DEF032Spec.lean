import QuantumNLS.WickKernelBridge
/-! integrator-authored trusted spec for DEF-032 Balanced finite polynomial and Wick quantization (Terra r135 REALIZED parametric): the ledger equality with the auxiliary-kernel placement: frozen statements restated verbatim. -/
namespace DEF032Spec
open scoped InnerProductSpace ComplexConjugate
open QuantumNLS.TensorCarrier
open QuantumNLS.OccupationUnitary
open QuantumNLS.Occupation (Occ Arr e total IsArray)
open QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition QuantumNLS.MixedTraceNorm
open QuantumNLS.Occupation (mdesc)
open QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition QuantumNLS.MixedTraceNorm
open QuantumNLS.Occupation (mdesc)
open QuantumNLS.Occupation (mdesc ket Ann Cre AnnMono CreMono FS)
open QuantumNLS.Occupation (mdesc WMono emb ket emb_ket)
open QuantumNLS.OccupationHilbert (core ext_core)
open QuantumNLS.WickSymbols (zm Mon Sym)
open QuantumNLS.BalancedWickDefinition (auxiliaryWick monomial_core)
open QuantumNLS.KernelDefinition
open QuantumNLS.Occupation (mdesc WMono emb ket emb_ket)
open QuantumNLS.OccupationHilbert (core ext_core)
open QuantumNLS.WickSymbols (zm Mon Sym WN symLin_expand Balanced)
open QuantumNLS.BalancedWickDefinition (auxiliaryWick monomial_core)
open QuantumNLS.KernelDefinition
open QuantumNLS.BalancedWickDefinition (Polynomial wick kernelQuantization evaluate quantization)
open QuantumNLS.WickSymbols (Sym)
open QuantumNLS.KernelDefinition QuantumNLS.TensorPlacements QuantumNLS.MixedTraceNorm
open QuantumNLS.BalancedWickDefinition (Polynomial evaluate)
open QuantumNLS QuantumNLS.WickKernelBridge

set_option maxHeartbeats 4000000 in
theorem auxiliaryWick_eq_kernel_spec  (p q : ℕ) (hp : 1 ≤ p) (f : Sym)
    (hf : ∀ pr ∈ f.coeff.support, total pr.1 = p ∧ total pr.2 = p) :
    auxiliaryWick (p + q) f =
      conjU4 (p + q) (((((p + q).descFactorial p : ℕ) : ℂ) * (((p + q : ℕ) : ℂ))⁻¹ ^ p) •
        genericU_N_r (p + q) p (Nat.le_add_right p q) (kernelOf p f)) := by
  apply QuantumNLS.WickKernelBridge.auxiliaryWick_eq_kernel <;> assumption

set_option maxHeartbeats 4000000 in
theorem wick_eq_kernelQuantization_spec {L : ℝ} [Fact (0 < L)]  (p q : ℕ) (hp : 1 ≤ p)
    (b : QuantumNLS.BetheCoefficientTransform.BetheBasis L (p + q))
    (g : QuantumNLS.BetheOccupationGauge.Gauge) (f : Polynomial)
    (hf : ∀ pr ∈ f.symbol.coeff.support, total pr.1 = p ∧ total pr.2 = p) :
    wick b g f = kernelQuantization b g (Nat.le_add_right p q) (kernelOf p f.symbol) := by
  apply QuantumNLS.WickKernelBridge.wick_eq_kernelQuantization <;> assumption

set_option maxHeartbeats 4000000 in
theorem kernelOf_symbol_spec  (p : ℕ) (f : Polynomial)
    (hf : ∀ pr ∈ f.symbol.coeff.support, total pr.1 = p ∧ total pr.2 = p) (u : OneParticle) :
    kernelProductSymbol (kernelOf p f.symbol) u = evaluate f (fun n => u n) := by
  apply QuantumNLS.WickKernelBridge.kernelOf_symbol <;> assumption

end DEF032Spec
#print axioms DEF032Spec.auxiliaryWick_eq_kernel_spec
#print axioms DEF032Spec.wick_eq_kernelQuantization_spec
#print axioms DEF032Spec.kernelOf_symbol_spec
