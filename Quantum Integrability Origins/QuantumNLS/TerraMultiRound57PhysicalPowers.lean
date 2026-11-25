import QuantumNLS.TerraMultiRound57CollectedPowers
import QuantumNLS.TerraMultiRound57PhysicalSelection

/-! Physical-ratio tree expansion in finite inverse-power coefficient form. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound57PhysicalPowers
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound57PhysicalSelection QuantumNLS.TerraMultiRound57CollectedPowers

/-- The actual physical ratio has a finite inverse-power tree expansion with
an exact free term and a fixed-field little-oh remainder. -/
theorem physical_ratio_power_expansion (L : ℝ) [hLf : Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ (x : Ell2) (ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ)) (r : ℝ → Ell2),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      (∀ᶠ Y : ℝ in atTop, ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 (r Y) = ratioL2 hY hlog hκ.le u hsmall) ∧
      (fun Y : ℝ => scalar L (s - 1 : ℕ) x (r Y) -
        (freeScalar (L := L) (s - 1 : ℕ) x Y +
          ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
            treeCoefficient (L := L) (k := s - 1) κ x s n))
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  obtain ⟨x, ha0, r, hx, hr, he⟩ := physical_ratio_tree_expansion L s hs κ hκ u hu
  refine ⟨x, ha0, r, hx, hr, ?_⟩
  convert he using 1
  funext Y
  rw [← collect_tree_powers (L := L) (k := s - 1) s hs κ x Y]
  ring

#print axioms physical_ratio_power_expansion
end QuantumNLS.TerraMultiRound57PhysicalPowers
