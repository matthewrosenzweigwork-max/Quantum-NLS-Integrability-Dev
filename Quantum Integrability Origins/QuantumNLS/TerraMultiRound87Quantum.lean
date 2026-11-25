import QuantumNLS.TerraMultiRound87Projection

/-! Direct use of the accepted R-F1423202 theorem on the entire actual
energy subspace, plus the two projection errors. The remaining spectral
Markov step must supply the projected unit vector and its distance. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor
open QuantumNLS.CountRotations QuantumNLS.HighAngleRotations
open QuantumNLS.HaarSpectralTail QuantumNLS.HaarNonlinearAbstract
open QuantumNLS.HighAngleReconstruction QuantumNLS.HighAngleEvolutionBridge
namespace QuantumNLS.TerraMultiRound87Quantum

variable (L : ℝ) [Fact (0 < L)]

/-- Accepted energy-subspace tail extended to a unit vector near that
subspace, retaining full uniformity over all high angles and all states. -/
theorem inherited_tail_with_projection {κ E : ℝ} (hκ : 0 < κ) (hE : 0 < E)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ NE : ℕ, ∃ η : ℕ → ℝ, 0 < NE ∧ (∀ R, 0 ≤ η R) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ (N : ℕ), NE ≤ N → ∀ hkN : k ≤ N,
        ∃ P : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N,
          (∀ m, P (bas L hκ (hk.trans hkN) m) =
            mask L κ N E m • bas L hκ (hk.trans hkN) m) ∧
          ∀ (v w : SymSector ℂ (L2T L) N), ‖v‖ = 1 → ‖w‖ = 1 → P w = w →
          ∀ δ : ℝ, 0 ≤ δ → ‖v - w‖ ≤ δ → ∀ R : ℕ, ∀ θ : AngleTorus,
          (∀ n : ℤ, |n| ≤ (R : ℤ) → θ n = 1) →
            TraceClass.traceNorm (reducedDensityN N k hkN
              (quantumRotation (bas L hκ (hk.trans hkN)) θ v).val -
                reducedDensityN N k hkN v.val) ≤ ENNReal.ofReal (4 * δ + η R) := by
  obtain ⟨NE, η, hNE, hη, hlim, htail⟩ :=
    QuantumHighAngleTail.natural_tail L hκ hE hk
  refine ⟨NE, η, hNE, hη, hlim, ?_⟩
  intro N hN hkN
  obtain ⟨P, hP, hPt⟩ := htail N hN hkN
  refine ⟨P, hP, ?_⟩
  intro v w hv hw hwP δ hδ hclose R θ hθ
  exact TerraMultiRound87Projection.marginal_projection_cost N k hkN v w
    (quantumRotation (bas L hκ (hk.trans hkN)) θ) hv hw δ (η R) hδ (hη R) hclose
    (hPt w hwP hw R θ hθ)

#print axioms inherited_tail_with_projection
end QuantumNLS.TerraMultiRound87Quantum
