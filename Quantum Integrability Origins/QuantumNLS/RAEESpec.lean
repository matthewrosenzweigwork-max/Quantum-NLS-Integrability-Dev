import QuantumNLS.RAEEMain
/-! integrator-authored trusted spec for R-AEE17FD6 thm:root-L2-flow (terra_review r206 PASS): headline statement(s) copied verbatim from RAEEMain (QuantumNLS.RAEEMain). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal
open QuantumNLS.Fourier QuantumNLS.L4Strichartz QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality
  QuantumNLS.LocalL4Contraction QuantumNLS.L4Gluing QuantumNLS.L2Flow QuantumNLS.H1Bridge
  QuantumNLS.Sobolev QuantumNLS.F04Regularity QuantumNLS.RootEnergyVariation
namespace QuantumNLS.RAEESpec
open QuantumNLS.RAEEMain
open QuantumNLS.PhysicalTensor (L2T)
variable {L : ℝ} [Fact (0 < L)]

set_option maxHeartbeats 8000000 in
theorem root_L2_flow_spec {κ : ℝ} (hκ : 0 ≤ κ) :
    ((∀ f : HL L, IsFlow κ (flowMap hκ f) ∧ flowMap hκ f 0 = f) ∧
    (∀ f : HL L, ∀ w : ℝ → HL L, IsFlow κ w → w 0 = f → w = flowMap hκ f) ∧
    (∀ f : HL L, ∀ t, ‖flowMap hκ f t‖ = ‖f‖) ∧
    (∀ (g : QuantumNLS.Sobolev.h04 L 1) (t : ℝ), flowMap hκ (emb g) t =
      emb (QuantumNLS.LocalWellPosednessFull.umax (le_refl (1 : ℝ)) κ g t)) ∧
    (∀ R T : ℝ, 0 ≤ R → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ t ∈ Set.Icc (-T) T, ‖flowMap hκ f t - flowMap hκ g t‖ ≤ K * ‖f - g‖) ∧
    (∀ R T : ℝ, 0 ≤ R → 0 ≤ T → ∃ K : ℝ, 0 ≤ K ∧ ∀ f g : HL L, ‖f‖ ≤ R → ‖g‖ ≤ R →
      ∀ (α β : ℝ) (hαβ : α ≤ β) (hlen : β ≤ α + TL L), -T ≤ α → β ≤ T →
        ∀ u v : Lp ℂ 4 (μJ (L := L) α β), Sol hαβ hlen (cNLS κ) u (flowMap hκ f) →
          Sol hαβ hlen (cNLS κ) v (flowMap hκ g) → ‖u - v‖ ≤ K * ‖f - g‖) ∧
    (∀ s t : ℝ, ∀ f : HL L, flowMap hκ (flowMap hκ f t) s = flowMap hκ f (s + t)) ∧
    (∀ t : ℝ, ∃ e : HL L ≃ₜ HL L, (∀ f, e f = flowMap hκ f t) ∧ ∀ f, e.symm f = flowMap hκ f (-t))) ∧
    (∀ hκ' : 0 < κ,
      (∀ f : HL L, ∀ t s : ℝ,
        FullMass.Mmeas κ (flowMap hκ f t) = FullMass.Mmeas κ (flowMap hκ f s) ∧
        (∀ z : ℂ, L2SpatialTransfer.discriminant κ (flowMap hκ f t) z =
          L2SpatialTransfer.discriminant κ (flowMap hκ f s) z) ∧
        (∀ z : ℂ, NormalizedTransfer.productSymbol L κ (flowMap hκ f t) z =
          NormalizedTransfer.productSymbol L κ (flowMap hκ f s) z) ∧
        ∀ n : ℤ, (RootIndexedMasses.masses hκ' (flowMap hκ f t)).1 n =
          (RootIndexedMasses.masses hκ' (flowMap hκ f s)).1 n) ∧
      (∀ (fs : ℕ → HL L) (f : HL L), Tendsto fs atTop (𝓝 f) → ∀ T : ℝ,
        (∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ t ∈ Icc (-T) T,
          TotalVariation.tvNorm (FullMass.Mmeas κ (flowMap hκ (fs j) t))
            (FullMass.Mmeas κ (flowMap hκ f t)) < ENNReal.ofReal ε) ∧
        TendstoUniformlyOn (fun j t => RootIndexedMasses.masses hκ' (flowMap hκ (fs j) t))
          (fun t => RootIndexedMasses.masses hκ' (flowMap hκ f t)) atTop (Icc (-T) T))) := by
  exact QuantumNLS.RAEEMain.root_L2_flow hκ

end QuantumNLS.RAEESpec
#print axioms QuantumNLS.RAEESpec.root_L2_flow_spec
