import QuantumNLS.BornConvergence

/-! integrator-authored trusted spec for DEF-007, DEF-010 and DEF-011 (DEFINITIONS_LEDGER.md:137, 203, 225),
realized PARAMETRICALLY in the normalized complete basis (Terra r100: acceptable, since the ledger says
"given the normalized complete Bethe basis"; physical instantiation by R-8E4D05E7).
DEF-007: for any Hilbert basis Ψ of the bosonic N-particle space Sym^N L²(𝕋_L) indexed by the DEF-006 labels
𝓜_N, the coefficient transform ψ ↦ (⟨Ψ_m, ψ⟩)_m is a unitary onto ℓ²(𝓜_N), and the Born law
p_{N,u}(m) = |⟨Ψ_m, u^{⊗N}⟩|² of a unit profile has total mass 1 over all of 𝓜_N (no finite-label conditioning).
DEF-010: ν_N = N⁻¹ Σ_j δ_{q_j} with q the DEF-006 ordered roots (a probability measure for N ≥ 1);
G_M(z) = ∫ (z − t)⁻¹ dM(t); for nonzero finite M and Im z > 0, Im G_M(z) < 0.
DEF-011: X_N → x in probability iff for every ε > 0, P_N(d(X_N, x) > ε) → 0, on varying spaces. -/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open QuantumNLS.BetheCoefficientTransform QuantumNLS.EmpiricalRapidity QuantumNLS.BornConvergence
open QuantumNLS.PhysicalTensor

namespace QuantumNLS.DEF007_010_011Spec

variable {L : ℝ} [Fact (0 < L)]

theorem spec_def007 (N : ℕ) :
    Nonempty (BetheBasis L N) ∧
    ∀ Ψ : BetheBasis L N,
      (∀ ψ m, coefficientTransform Ψ ψ m = ⟪Ψ m, ψ⟫_ℂ) ∧
      (∀ ψ, ‖coefficientTransform Ψ ψ‖ = ‖ψ‖) ∧ Function.Surjective (coefficientTransform Ψ) ∧
      (∀ u m, bornLaw Ψ u m = ‖⟪Ψ m, productVec L N u⟫_ℂ‖ ^ 2) ∧
      (∀ u : L2T L, ‖u‖ = 1 → HasSum (bornLaw Ψ u) 1) :=
  ⟨⟨freeBasis L N⟩, fun Ψ => ⟨fun ψ m => coefficientTransform_apply Ψ ψ m,
    fun ψ => (coefficientTransform Ψ).norm_map ψ, (coefficientTransform Ψ).surjective,
    fun u m => rfl, fun u hu => hasSum_bornLaw_unit Ψ u hu⟩⟩

theorem spec_def010 :
    (∀ (c : ℝ) (N : ℕ) (m : QuantumNLS.BetheLabels.MArr N),
      empiricalMeasure L c m = ((N : ℝ≥0∞)⁻¹) • ∑ j : Fin N,
        Measure.dirac (QuantumNLS.BetheLabels.arrRoots L c m j)) ∧
    (∀ (c : ℝ) (N : ℕ), 0 < N → ∀ m : QuantumNLS.BetheLabels.MArr N,
      IsProbabilityMeasure (empiricalMeasure L c m)) ∧
    (∀ (M : Measure ℝ) (z : ℂ), cauchyTransform M z = ∫ t : ℝ, ((z - (t : ℂ))⁻¹ : ℂ) ∂M) ∧
    (∀ (M : Measure ℝ) [IsFiniteMeasure M], M ≠ 0 → ∀ z : ℂ, 0 < z.im → (cauchyTransform M z).im < 0) :=
  ⟨fun c N m => rfl, fun c N hN m => isProbabilityMeasure_empiricalMeasure L c hN m, fun M z => rfl,
    fun M _ hM z hz => im_cauchyTransform_neg M hM z hz⟩

theorem spec_def011 {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] {E : Type} [PseudoMetricSpace E]
    (P : ∀ N, Measure (Ω N)) (X : ∀ N, Ω N → E) (x : E) :
    TendstoInProbability P X x ↔
      ∀ ε : ℝ, 0 < ε → Tendsto (fun N => P N {ω | ε < dist (X N ω) x}) atTop (𝓝 0) :=
  Iff.rfl

end QuantumNLS.DEF007_010_011Spec

open Lean in
#eval show CoreM Unit from do
  for n in [``QuantumNLS.DEF007_010_011Spec.spec_def007, ``QuantumNLS.DEF007_010_011Spec.spec_def010,
      ``QuantumNLS.DEF007_010_011Spec.spec_def011] do
    let ax ← Lean.collectAxioms n
    IO.println s!"{n} axioms: {ax}"
