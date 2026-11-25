import QuantumNLS.TerraMultiRound23ResolventSymmetry

/-! The component sign symmetry of the graph transports resolvents. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
namespace QuantumNLS.LocalSpectral.Round23

theorem liftFiber_parity_smul (L : ℝ) (z : ℂ) (f : H2 L) :
    liftFiber L parityFlipIsometry (z • f) = z • liftFiber L parityFlipIsometry f := by
  rw [Lp.ext_iff]
  filter_upwards [parityFlipIsometry.toContinuousLinearMap.coeFn_compLp (z • f),
    parityFlipIsometry.toContinuousLinearMap.coeFn_compLp f,
    Lp.coeFn_smul z f, Lp.coeFn_smul z (liftFiber L parityFlipIsometry f)] with x h1 h2 h3 h4
  change (parityFlipIsometry.toContinuousLinearMap.compLp (z • f)) x = _
  rw [h1, h4, h3]
  change parityFlip (z • (f : ℝ → E2) x) =
    z • (parityFlipIsometry.toContinuousLinearMap.compLp f) x
  rw [h2]
  ext i
  fin_cases i <;> simp [parityFlipIsometry, parityFlip, Jm, vec2, mul_neg]

/-- Whenever both resolvents exist, the sign flip intertwines their action
at potentials `u` and `-u`. -/
theorem resolvent_parity_intertwines (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ) (z : ℂ)
    (R S : H2 L →L[ℂ] H2 L)
    (hR : IsResolvent L κ u σ z R)
    (hS : IsResolvent L κ (fun x => -u x) σ z S) (φ : H2 L) :
    S (liftFiber L parityFlipIsometry φ) = liftFiber L parityFlipIsometry (R φ) := by
  have hp := graph_parityFlip L κ u σ (hR.1 φ)
  rw [liftFiber_sub, liftFiber_parity_smul] at hp
  have hs := hS.2 _ hp
  simpa using hs

end QuantumNLS.LocalSpectral.Round23
#print axioms QuantumNLS.LocalSpectral.Round23.liftFiber_parity_smul
#print axioms QuantumNLS.LocalSpectral.Round23.resolvent_parity_intertwines
