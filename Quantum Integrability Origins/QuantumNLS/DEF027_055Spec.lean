import QuantumNLS.FullOccupationAffinity
/-! integrator-authored trusted spec for DEF-027 and DEF-055 (DEFINITIONS_LEDGER.md def:report-27, def:report-55).
DEF-027: the partial shift W_{N,ab}|m⟩ = |m − e_a + e_b⟩ if m_a ≥ 1, else 0 (on complete arrays, norm ≤ 1); polar symbol
ζ_ab = w_a conj(w_b)/√(a_a a_b), defined only on the positive-endpoint domain (a ≠ b, a_a, a_b > 0), of modulus 1
under DEF-020; zero actions excluded; Cartesian symbol = ζ·√(a_a a_b) (parametric in DEF-014 data).
DEF-055: for W|m⟩ = α_m|m − e_a + e_b⟩ (unit edge phases), coefficients g, |ζ| = 1: H = Σ_{m_a≥1} |g_m||g_{m−e_a+e_b}|
(all full occupations), D = H − Re(conj ζ · Σ α_m g_m conj g_{m−e_a+e_b}) with no factor two; the complex sum is
⟨g, W g⟩; sums converge absolutely (derived). -/
namespace DEF027_055Spec
open QuantumNLS QuantumNLS.UnitPhaseTransfer QuantumNLS.FullOccupationAffinity QuantumNLS.Occupation
  QuantumNLS.OccupationHilbert QuantumNLS.QuantumFourierSpecification QuantumNLS.IndexedMassProperness
open scoped InnerProductSpace ComplexConjugate

theorem spec :
    -- DEF-027
    (∀ (N : ℕ) (a b : ℤ) (m : Arr N), UnitPhaseTransfer.auxiliary N a b (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then lp.single 2 (shiftArr a b m hd) 1 else 0) ∧
    (∀ (N : ℕ) (a b : ℤ), ‖UnitPhaseTransfer.auxiliary N a b‖ ≤ 1) ∧
    (∀ (L κ : ℝ) [Fact (0 < L)] (D : IndexedMassData L κ) (a b : ℤ) (u : PhysicalField L),
      (∃ v : Endpoints D a b, v.1 = u) ↔ (a ≠ b ∧ 0 < D.seq u a ∧ 0 < D.seq u b)) ∧
    (∀ (L κ : ℝ) [Fact (0 < L)] (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates) (a b : ℤ)
      (u : Endpoints D a b), UnitPhaseTransfer.symbol D w a b u =
        (w u.1 a * conj (w u.1 b)) / (Real.sqrt (D.seq u.1 a * D.seq u.1 b) : ℂ)) ∧
    (∀ (L κ : ℝ) [Fact (0 < L)] (D : IndexedMassData L κ) (w : PhysicalField L → Coordinates),
      Specification D w → ∀ (a b : ℤ) (u : Endpoints D a b), ‖UnitPhaseTransfer.symbol D w a b u‖ = 1) ∧
    -- DEF-055
    (∀ (N : ℕ) (a b : ℤ) (g : H N), Summable (affinityTerm a b g) ∧
      affinity a b g = ∑' m : Donor N a, ‖g m.1‖ * ‖g (destination N a b m)‖) ∧
    (∀ (N : ℕ) (a b : ℤ) (α : Donor N a → Phase) (g : H N),
      overlap a b α g = ∑' m : Donor N a, (α m).1 * g m.1 * conj (g (destination N a b m))) ∧
    (∀ (N : ℕ) (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N),
      defect a b α ζ g = affinity a b g - (conj ζ.1 * overlap a b α g).re) ∧
    (∀ (N : ℕ) (a b : ℤ) (α : Donor N a → Phase) (m : Arr N), transfer a b α (lp.single 2 m 1) =
      if hd : DonorOK a m.1 then (α ⟨m, hd⟩).1 • lp.single 2 (shiftArr a b m hd) 1 else 0) ∧
    (∀ (N : ℕ) (a b : ℤ) (α : Donor N a → Phase) (g : H N), ⟪g, transfer a b α g⟫_ℂ = overlap a b α g) ∧
    (∀ (N : ℕ) (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N), 0 ≤ defect a b α ζ g) := by
  refine ⟨UnitPhaseTransfer.auxiliary_basis, UnitPhaseTransfer.auxiliary_norm_le, ?_,
    fun L κ _ D w a b u => rfl, fun L κ _ D w h a b u => UnitPhaseTransfer.symbol_norm D w h a b u,
    fun N a b g => ⟨summable_affinityTerm a b g, rfl⟩, fun N a b α g => rfl, fun N a b α ζ g => rfl,
    fun N a b α m => transfer_basis a b α m, fun N a b α g => inner_transfer a b α g,
    fun N a b α ζ g => defect_nonneg a b α ζ g⟩
  intro L κ _ D a b u
  exact ⟨fun ⟨v, hv⟩ => hv ▸ v.2, fun h => ⟨⟨u, h⟩, rfl⟩⟩

end DEF027_055Spec
#print axioms DEF027_055Spec.spec
