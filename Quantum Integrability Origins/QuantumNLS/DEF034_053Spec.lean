import QuantumNLS.CommonBethePacket
import QuantumNLS.CountRotations
/-! integrator-authored trusted spec for DEF-034 and DEF-053 (DEFINITIONS_LEDGER.md), both REALIZED parametric
(Terra r128 / r129): parametric in a supplied complete Bethe basis and (DEF-053) a supplied coordinate bijection Φ.
DEF-034: a finite Bethe packet is a normalized finite linear combination of basis vectors; a common packet sequence (one
sequence, indexed by N = n+1) is norm-close to the product and has every fixed intensive charge limit and every fixed
weighted action limit, support-uniformly; no existence asserted.
DEF-053: angles θ ∈ ∏_ℤ Circle with product Haar probability; V_N(θ)Ψ_m = e^{−iΣθ_n m_n}Ψ_m; coordinate action
w_n ↦ e^{−iθ_n}w_n; physical action = Φ⁻¹ ∘ coordinate action ∘ Φ. -/
namespace DEF034_053Spec
open QuantumNLS QuantumNLS.CommonBethePacket QuantumNLS.CountRotations QuantumNLS.BetheLabels
  QuantumNLS.BetheCoefficientTransform QuantumNLS.PhysicalTensor QuantumNLS.QuantumFourierSpecification Filter Topology
open scoped InnerProductSpace

theorem spec :
    -- DEF-034
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (P : Packet b),
      vector P = ∑ m ∈ P.coefficients.support, P.coefficients m • b m ∧ ‖vector P‖ = 1) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (b : (n : ℕ) → BetheBasis L (n+1)) (P : (n : ℕ) → Packet (b n))
      (u : L2T L) (coupling : ℕ → ℝ) (chargeTarget : ℕ → ℝ) (A : ActionTarget),
      IsCommon P u coupling chargeTarget A ↔
        (‖u‖ = 1 ∧ Tendsto (fun n => ‖vector (P n) - productVec L (n+1) u‖) atTop (𝓝 0) ∧
          (∀ r : ℕ, 1 ≤ r → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ m ∈ (P n).coefficients.support,
            |BetheSpectralCharges.eigenvalue L (n+1) (coupling n) r m / (n+1 : ℕ) - chargeTarget r| ≤ ε) ∧
          (∀ a : ℝ, 0 ≤ a → ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ m ∈ (P n).coefficients.support,
            RapidityTransport.weightedError a A.values (n+1) m ≤ ENNReal.ofReal ε))) ∧
    -- DEF-053
    (productHaar = MeasureTheory.Measure.infinitePi fun _ : ℤ => circleHaar) ∧
    (∀ (N : ℕ) (θ : AngleTorus) (m : MArr N), countPhase θ m = m.1.prod fun n k => (θ n)⁻¹ ^ k) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (N : ℕ) (b : BetheBasis L N) (θ : AngleTorus) (m : MArr N),
      quantumRotation b θ (b m) = ((countPhase θ m : Circle) : ℂ) • b m) ∧
    (∀ (θ : AngleTorus) (w : Coordinates), coordinateRotation θ w = ActionTorus.rotate (fun n => (θ n)⁻¹) w) ∧
    (∀ (L : ℝ) [Fact (0 < L)] (Φ : PhysicalField L ≃ Coordinates) (θ : AngleTorus) (u : PhysicalField L),
      physicalRotation Φ θ u = Φ.symm (coordinateRotation θ (Φ u))) := by
  refine ⟨fun L _ N b P => ⟨rfl, P.normalized⟩, fun L _ b P u coupling chargeTarget A => Iff.rfl, rfl,
    fun N θ m => rfl, fun L _ N b θ m => quantumRotation_basis b θ m, fun θ w => rfl, fun L _ Φ θ u => rfl⟩

end DEF034_053Spec
#print axioms DEF034_053Spec.spec
