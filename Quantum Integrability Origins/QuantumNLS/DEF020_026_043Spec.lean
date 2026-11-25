import QuantumNLS.CartesianOccupationTransfer
import QuantumNLS.IndexedScalarMeasureCuts
/-! integrator-authored trusted spec for DEF-020, DEF-026, DEF-043 (DEFINITIONS_LEDGER.md def:report-20/26/43).
DEF-020 (specification predicate, parametric in DEF-014 data D; no map existence assumed): w is normalized by the
orthonormal Fourier differential at 0, w(conj u(−·)) = conj w(u), and |w_n(u)|² = a_n(u).
DEF-026: on the normalized occupation basis E_{N,ab} = N⁻¹ a_b^* a_a has coefficient N⁻¹√(m_a(m_b+1)) (a ≠ b),
m_a/N (a = b), 0 on empty donors, norm ≤ 1; pullback through the gauged Bethe transform E^q; symbol c_ab = w_a conj w_b
(parametric in the supplied basis b, as DEF-007).
DEF-043 (parametric in the explicit regular-cut set): nonatomic probability μ, F(x) = Lx − 2κ Re G_μ(x), boundary
alternative, a.e. integer label n(t) = Lt/(2π) − κ Re G(t)/π, separation at each regular cut x ∉ supp μ. -/
namespace DEF020_026_043Spec
open QuantumNLS QuantumNLS.QuantumFourierSpecification QuantumNLS.CartesianOccupationTransfer
  QuantumNLS.IndexedMassProperness QuantumNLS.ResetNormalizationUniqueness QuantumNLS.Fourier
  QuantumNLS.BetheLabels QuantumNLS.BetheCoefficientTransform QuantumNLS.BetheOccupationGauge QuantumNLS.Occupation
  QuantumNLS.IndexedScalarMeasure QuantumNLS.IndexedScalarMeasureCuts MeasureTheory
open scoped ComplexConjugate

theorem spec :
    -- DEF-020
    (∀ (L κ : ℝ) [Fact (0 < L)] (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates),
      Specification D w ↔ (HasFDerivAt w (differential L) 0 ∧ (∀ u, w (Cphys L u) = star (w u)) ∧
        (∀ u n, ‖w u n‖ ^ 2 = D.seq u n))) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (u : PhysicalField L) (n : ℤ), differential L u n = fourierL2 L u n) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (u : PhysicalField L),
      (Cphys L u : AddCircle L → ℂ) =ᵐ[volume] fun x => conj (u (-x))) ∧
    -- DEF-026
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (a c : ℤ) (m : MArr N), a ≠ c →
      ∀ hd : DonorOK a (marrArr N m).1, physical b g a c (gaugedBasis b g m) =
        ((Real.sqrt (((marrArr N m).1 a : ℝ) * (((marrArr N m).1 c : ℝ) + 1)) / N : ℝ) : ℂ) •
          gaugedBasis b g ((marrArr N).symm (shiftArr a c (marrArr N m) hd))) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (a : ℤ) (m : MArr N),
      physical b g a a (gaugedBasis b g m) = ((((marrArr N m).1 a : ℝ) / N : ℝ) : ℂ) • gaugedBasis b g m) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (g : Gauge) (a c : ℤ), ‖physical b g a c‖ ≤ 1) ∧
    (∀ (q : ℕ) (a b : ℤ) (m : Arr (1+q)), ¬ DonorOK a m.1 → auxiliary q a b (OccupationUnitary.basisVector m) = 0) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (w : PhysicalField L → Coordinates) (a b : ℤ) (u : PhysicalField L),
      symbol w a b u = w u a * conj (w u b)) ∧
    -- DEF-043
    (∀ (L κ : ℝ) (μ : Measure ℝ) (x : ℝ), exteriorForce L κ μ x = L * x - 2 * κ * ∫ t : ℝ, (x - t)⁻¹ ∂μ) ∧
    (∀ (L κ : ℝ) (g : ℝ → ℝ) (t : ℝ), indexLabel L κ g t = L * t / (2 * Real.pi) - κ * g t / Real.pi) ∧
    (∀ (L κ : ℝ) (S : IndexedScalarMeasureCuts L κ), IsProbabilityMeasure S.μ ∧ NoAtoms S.μ ∧ 0 < L ∧ 0 < κ ∧
      S.cuts ⊆ (S.μ.support)ᶜ ∧
      (∀ x ∈ S.cuts, ∀ a : ℤ, 2 * Real.pi * a < exteriorForce L κ S.μ x →
        exteriorForce L κ S.μ x < 2 * Real.pi * (a + 1) →
        (∀ᵐ t ∂S.μ, t < x → indexLabel L κ S.reG t ≤ a) ∧
        (∀ᵐ t ∂S.μ, x < t → (a : ℝ) + 1 ≤ indexLabel L κ S.reG t))) ∧
    (∀ (L κ : ℝ) (S : IndexedScalarMeasure.IndexedScalarMeasure L κ), S.toCuts.cuts = (S.μ.support)ᶜ) := by
  refine ⟨fun L κ _ D w => Iff.rfl, fun L _ u n => rfl, fun L _ u => physical_reflection u,
    fun L _ N b g a c m hac hd => physical_offdiag b g a c hac m hd,
    fun L _ N b g a m => physical_diag b g a m, fun L _ N b g a c => physical_norm_le b g a c,
    fun q a b m hd => auxiliary_empty q a b m hd, fun L _ w a b u => rfl,
    exteriorForce_eq, fun L κ g t => rfl,
    fun L κ S => ⟨S.isProb, S.noAtoms, S.hL, S.hκ, S.cuts_sub, S.separation⟩, fun L κ S => rfl⟩

end DEF020_026_043Spec
#print axioms DEF020_026_043Spec.spec
