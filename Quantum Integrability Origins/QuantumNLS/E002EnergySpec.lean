import QuantumNLS.SmoothKernelNormalForm

/-! integrator-authored trusted spec for ENERGY-002 `lem:A1-trace` (energy_prepared/cubic_charge.tex:74).
The hypothesis class "finite-rank operator with smooth kernel on k variables" is written out here: J a
bounded operator on L²(T_L^k) with finite-dimensional range, equal a.e. to ∫ K(x,y) ψ(y) dy for every ψ,
with K jointly C^∞ on ℝ^k × ℝ^k and Lℤ^k-periodic in each variable. The clause predicates
(TraceClause, TraceClauseSym: (a) H¹→H^{1/2} bound, (b) compact T A^{-1/2}, (c) B_ij bound and compact
sandwich, bosonic restriction; ExtCommLit, IntCommLit: compact A^{-1/2}[B, J⊗Id]A^{-1/2} external and
internal, with J⊗Id constructed and characterized, and compressions) are the author's definitions
reviewed by Terra in R56 and R60; they are not re-derived here (qualified spec). -/

open MeasureTheory
open scoped ContDiff
open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.ProductWeakDerivatives
open QuantumNLS.EnergyContactCommutator QuantumNLS.SmoothKernelNormalForm

namespace QuantumNLS.E002EnergySpec

def LitFRSK (L : ℝ) [Fact (0 < L)] {k : ℕ} (J : L2TN L k →L[ℂ] L2TN L k) : Prop :=
  FiniteDimensional ℂ (LinearMap.range (J : L2TN L k →ₗ[ℂ] L2TN L k)) ∧
  ∃ K : (Fin k → ℝ) → (Fin k → ℝ) → ℂ,
    ContDiff ℝ ∞ (fun p : (Fin k → ℝ) × (Fin k → ℝ) => K p.1 p.2) ∧
    (∀ y, LatticePeriodic L (fun x => K x y)) ∧ (∀ x, LatticePeriodic L (K x)) ∧
    ∀ ψ : L2TN L k, (J ψ : (Fin k → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L k]
      fun x => ∫ y, K (fun i => rep (x i)) (fun i => rep (y i)) * (ψ : (Fin k → AddCircle L) → ℂ) y
        ∂(torusPiMeasure L k)

def Spec : Prop :=
  ∀ (L : ℝ) [Fact (0 < L)],
    (∀ m : ℕ, 2 ≤ m → ∀ (i j : Fin m) (hij : i ≠ j),
        TraceClause L m i j hij ∧ TraceClauseSym L m i j hij) ∧
    (∀ (k : ℕ) (J : L2TN L k →L[ℂ] L2TN L k), LitFRSK L J →
      (∀ i : Fin k, ExtCommLit L J i) ∧ ∀ (i j : Fin k) (hij : i ≠ j), IntCommLit L J hij)

theorem spec : Spec := by
  intro L _
  obtain ⟨h0, -, h2⟩ := energy002_literal L
  refine ⟨h0, fun k J hJ => h2 k J ?_⟩
  obtain ⟨hfr, K, hs, hl, hr, hi⟩ := hJ
  exact ⟨hfr, K, ⟨hs, hl, hr⟩, hi⟩

end QuantumNLS.E002EnergySpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.E002EnergySpec.spec
  IO.println s!"E002EnergySpec.spec axioms: {ax}"
