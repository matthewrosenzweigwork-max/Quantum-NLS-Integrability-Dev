import QuantumNLS.REF88STruncation
import QuantumNLS.REF88SQuantiles

/-! R-EF8C2837 item (iv), physical_cubic.tex:316–321.
Concrete H¹ truncations containing an active pair, preservation of that pair,
and W₂/L² convergence of their normalized spectral quantiles.
REG-015 is the sole named predecessor input, explicit in the intermediate theorem.
Author sol_multi round23; independent reviewer terra_review. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.REF88SH1Approximation
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Sobolev QuantumNLS.REF88Chart QuantumNLS.REF88Reg015
open QuantumNLS.REF88PrintedChart QuantumNLS.REF88STruncation QuantumNLS.REF88SQuantiles
open QuantumNLS.RootIndexedMasses (masses)
variable {L κ : ℝ} [Fact (0 < L)]

/-- A positive indexed mass forces a nonzero physical field. -/
theorem nonzero_of_active (hκ : 0 < κ) {u : L2T L} {a : ℤ}
    (ha : 0 < (masses hκ u).1 a) : u ≠ 0 := by
  have hcl := RootIndexedMasses.root_indexed_masses_proved_clauses hκ u
  have hle : (masses hκ u).1 a ≤ ‖u‖ ^ 2 := by
    rw [← hcl.2.2.2.1]
    exact hcl.2.2.1.le_tsum a (fun n _ => hcl.2.1 n)
  intro hu
  simp only [hu,norm_zero,zero_pow (by norm_num : 2 ≠ 0)] at hle ha
  exact (not_le_of_gt ha) hle

/-- All of the analytic approximation hypotheses in the printed H¹ paragraph.
The endpoint empirical W₂ convergence is derived separately by actual_diagonal_endpoint. -/
theorem H1_approximationInput (hκ : 0 < κ) (hR : Reg015Input L κ hκ)
    {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ) (u : H02 L 1) (a b : ℤ)
    (ha : 0 < (masses hκ u.val).1 a) (hb : 0 < (masses hκ u.val).1 b) :
    ∃ v : ℕ → H02 L 1,
      Tendsto v atTop (𝓝 u) ∧
      (∀ j n, Φ (v j).val n = if n ∈ supports a b j then Φ u.val n else 0) ∧
      (∀ j, (masses hκ (v j).val).1 a = (masses hκ u.val).1 a ∧
        (masses hκ (v j).val).1 b = (masses hκ u.val).1 b) ∧
      (∀ j, (v j).val ≠ 0) ∧
      Tendsto (fun j => QuantileTransport.W2 (normalized hκ (v j).val) (normalized hκ u.val))
        atTop (𝓝 0) := by
  obtain ⟨v,hv,hcoord⟩ := physical_truncationInput hκ hR hΦ 1 (by norm_num) u a b
  have hc : ∀ j n, Φ (v j).val n = if n ∈ supports a b j then Φ u.val n else 0 := hcoord
  have hp : ∀ j, (masses hκ (v j).val).1 a = (masses hκ u.val).1 a ∧
      (masses hκ (v j).val).1 b = (masses hκ u.val).1 b := by
    intro j
    constructor
    · rw [← hΦ.moduli, ← hΦ.moduli, hc, if_pos (pair_mem a b j).1]
    · rw [← hΦ.moduli, ← hΦ.moduli, hc, if_pos (pair_mem a b j).2]
  have hz : ∀ j, (v j).val ≠ 0 := fun j => nonzero_of_active hκ (by rw [(hp j).1]; exact ha)
  exact ⟨v,hv,hc,hp,hz,normalized_W2 hκ (nonzero_of_active hκ ha) hz hv⟩

/-- Conditional wrapper using the requested 3efaf508 REG-015 bridge; no acceptance claimed. -/
theorem H1_approximation_of_final (hκ : 0 < κ)
    {Φ : L2T L → K} (hΦ : PrintedChart hκ Φ) (u : H02 L 1) (a b : ℤ)
    (ha : 0 < (masses hκ u.val).1 a) (hb : 0 < (masses hκ u.val).1 b) :
    ∃ v : ℕ → H02 L 1,
      Tendsto v atTop (𝓝 u) ∧
      (∀ j n, Φ (v j).val n = if n ∈ supports a b j then Φ u.val n else 0) ∧
      (∀ j, (masses hκ (v j).val).1 a = (masses hκ u.val).1 a ∧
        (masses hκ (v j).val).1 b = (masses hκ u.val).1 b) ∧
      (∀ j, (v j).val ≠ 0) ∧
      Tendsto (fun j => QuantileTransport.W2 (normalized hκ (v j).val) (normalized hκ u.val))
        atTop (𝓝 0) :=
  H1_approximationInput hκ (REF88Reg015Bridge.reg015Input_of_final hκ) hΦ u a b ha hb

#print axioms nonzero_of_active
#print axioms H1_approximationInput
#print axioms H1_approximation_of_final
end QuantumNLS.REF88SH1Approximation
