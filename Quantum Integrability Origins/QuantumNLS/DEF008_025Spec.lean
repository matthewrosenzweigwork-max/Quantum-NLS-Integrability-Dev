import QuantumNLS.BetheOccupationGauge
/-! integrator-authored trusted spec for DEF-008 and DEF-025 (DEFINITIONS_LEDGER.md; definitions.tex:49, :151),
parametric in a supplied complete normalized Bethe basis Ψ = b (as DEF-007; the physical interacting N ≥ 2
basis is BCB1, conditional on the EXT-001 AbstractContinuity premise).
DEF-008: Λ_{N,r}(m) = Σ_j q_j(m)^r with q the DEF-006 source rapidities; domain = {ψ : Σ_m |Λ(m)|²|⟨Ψ_m,ψ⟩|² < ∞},
maximal (exists unique vector with multiplied coordinates); Q_{N,0} = N·Id on everything; polynomial combinations
use the maximal domain of the evaluated symbol; spectral unitaries e^{-itΛ} act on every vector, strongly
continuous, commuting.
DEF-025: a gauge is a unit phase for every complete array in every sector; a universal selection depends only on
period and coupling; it rephases the basis literally (g(m)Ψ_m), leaves Born laws and maximal charge domains
invariant; selections exist and need not equal the intrinsic normalization. -/
namespace DEF008_025Spec
open QuantumNLS QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheSpectralCharges
  QuantumNLS.BetheOccupationGauge
open scoped InnerProductSpace

theorem spec :
    -- DEF-008
    (∀ (L : ℝ) (N : ℕ) (c : ℝ) (r : ℕ) (m : MArr N),
      eigenvalue L N c r m = ∑ j, BetheSmooth.sourceRoots L ((BetheConditionalBasis.labelArr N).symm m).val c j ^ r) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (c : ℝ) (r : ℕ) (ψ : HN L N),
      ψ ∈ (charge b c r).domain ↔ Summable (fun m => |eigenvalue L N c r m| ^ 2 * ‖⟪b m, ψ⟫_ℂ‖ ^ 2)) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (ev : MArr N → ℝ) (ψ : HN L N),
      ψ ∈ (multiplier b ev).domain ↔ ∃! φ : HN L N, ∀ m, ⟪b m, φ⟫_ℂ = (ev m : ℂ) * ⟪b m, ψ⟫_ℂ) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (ev : MArr N → ℝ)
      (ψ : (multiplier b ev).domain) (m : MArr N),
      ⟪b m, multiplier b ev ψ⟫_ℂ = (ev m : ℂ) * ⟪b m, (ψ : HN L N)⟫_ℂ) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (c : ℝ),
      (charge b c 0).domain = ⊤ ∧ ∀ ψ : (charge b c 0).domain, charge b c 0 ψ = (N : ℂ) • (ψ : HN L N)) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (c : ℝ) (p : Polynomial ℝ),
      polynomialCharge b c p = multiplier b (fun m => ∑ j, p.eval (rapidity L N c m j))) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (ev : MArr N → ℝ) (t : ℝ) (ψ : HN L N) (m : MArr N),
      ⟪b m, evolution b ev t ψ⟫_ℂ = Complex.exp (-(((t * ev m : ℝ) : ℂ)) * Complex.I) * ⟪b m, ψ⟫_ℂ) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (ev μ : MArr N → ℝ) (s t : ℝ) (ψ : HN L N),
      evolution b ev s (evolution b μ t ψ) = evolution b μ t (evolution b ev s ψ)) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (ev : MArr N → ℝ) (ψ : HN L N),
      Continuous (fun t : ℝ => evolution b ev t ψ)) ∧
    -- DEF-025
    (Gauge = ∀ N : ℕ, MArr N → {z : ℂ // ‖z‖ = 1}) ∧
    (UniversalSelection = ((L : ℝ) → 0 < L → (c : ℝ) → 0 < c → Gauge)) ∧
    Nonempty UniversalSelection ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (m : MArr N),
      gaugedBasis b g m = (g N m).val • b m) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (ψ : HN L N) (m : MArr N),
      gaugedTransform b g ψ m = (starRingEnd ℂ) (g N m).val * ⟪b m, ψ⟫_ℂ) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (u : PhysicalTensor.L2T L) (m : MArr N),
      bornLaw (gaugedBasis b g) u m = bornLaw b u m) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (ev : MArr N → ℝ),
      multiplier (gaugedBasis b g) ev = multiplier b ev) ∧
    (∀ (N : ℕ) (m : MArr N), (negativeGauge N m).val ≠ (identityGauge N m).val) := by
  refine ⟨fun L N c r m => rfl, fun L _ N b c r ψ => mem_domain b _ ψ, fun L _ N b ev ψ => maximal b ev ψ,
    fun L _ N b ev ψ m => multiplier_coord b ev ψ m,
    fun L _ N b c => ⟨charge_zero_domain b c, charge_zero_apply b c⟩, fun L _ N b c p => rfl,
    fun L _ N b ev t ψ m => evolution_coord b ev t ψ m,
    fun L _ N b ev μ s t ψ => evolution_commute b ev μ s t ψ,
    fun L _ N b ev ψ => evolution_continuous b ev ψ, rfl, rfl, selection_exists,
    fun L _ N b g m => gaugedBasis_apply b g m, fun L _ N b g ψ m => gaugedTransform_apply b g ψ m,
    fun L _ N b g u m => bornLaw_invariant b g u m, fun L _ N b g ev => multiplier_invariant b g ev,
    negative_phase_ne_identity⟩

end DEF008_025Spec
#print axioms DEF008_025Spec.spec
