import QuantumNLS.PhysicalCubic
/-! integrator-authored trusted spec for DEF-023 "The physical cubic solution" (DEFINITIONS_LEDGER.md def:report-23):
the unique Duhamel solution of i u_t = −u_xx + 2κ|u|²u in C(ℝ;L²) ∩ L⁴_loc(ℝ×𝕋_L), for arbitrary L² data, κ ≥ 0;
supplied by the (internally proved, EXT-003 Route Y) harmonic-analysis well-posedness. No identification with
coordinate rotations is asserted. The class: w continuous into L², and on every interval (α,β] of length ≤ T_L there
is an L⁴ class u whose Duhamel curve (with coefficient −2iκ, data at some a ∈ [α,β]) equals w on [α,β]. -/
namespace DEF023Spec
open QuantumNLS QuantumNLS.PhysicalCubic QuantumNLS.L2Flow QuantumNLS.L4Gluing QuantumNLS.LocalL4Contraction
  QuantumNLS.DuhamelDuality QuantumNLS.L4StrichartzL2 QuantumNLS.L4Strichartz MeasureTheory

theorem spec (L : ℝ) [Fact (0 < L)] :
    (∀ (κ : ℝ) (f : HL L) (w : ℝ → HL L), IsPhysicalCubicSolution κ f w ↔
      ((Continuous w ∧ ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L),
        ∃ u : Lp ℂ 4 (μJ (L := L) α β), ∃ a ∈ Set.Icc α β,
          IsDuhamel hαβ hlen (-(2 * (κ : ℂ) * Complex.I)) a (w a) u ∧
          ∀ t ∈ Set.Icc α β, Dcurve hαβ hlen (-(2 * (κ : ℂ) * Complex.I)) a (w a) u t = w t) ∧ w 0 = f)) ∧
    (∀ (κ : ℝ) (hκ : 0 ≤ κ) (f : HL L),
      IsPhysicalCubicSolution κ f (physicalCubic hκ f) ∧
        ∀ w : ℝ → HL L, IsPhysicalCubicSolution κ f w → w = physicalCubic hκ f) :=
  ⟨fun κ f w => Iff.rfl, fun κ hκ f => physicalCubic_spec hκ f⟩

end DEF023Spec
#print axioms DEF023Spec.spec
