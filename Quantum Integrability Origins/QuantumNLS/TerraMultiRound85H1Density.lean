import QuantumNLS.TerraMultiRound84FlowDensity
import QuantumNLS.H1Bridge

/-! Density of the H¹ embedding, via the previously checked finite Fourier span. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight
open QuantumNLS.H1Bridge QuantumNLS.L4StrichartzL2 QuantumNLS.DuhamelDuality
open QuantumNLS.TerraMultiRound84FlowDensity
namespace QuantumNLS.TerraMultiRound85H1Density
variable {L : ℝ} [Fact (0 < L)]

/-- Every Fourier mode is in the H¹ coefficient space. -/
def modeH1 (k : ℤ) : h04 L 1 := h04.ofMem (x := fun n => if n = k then 1 else 0) (by
  classical
  apply summable_of_ne_finset_zero (s := {k})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [hn])

/-- The H¹ embedding sends the coefficient basis to the physical mode. -/
theorem emb_mode (k : ℤ) : emb (modeH1 (L := L) k) = modeLp L k := by
  apply (fourierL2 L).injective
  refine lp.ext (funext fun n => ?_)
  rw [fourierL2_emb, fourierL2_modeLp]
  classical
  change (if n = k then (1 : ℂ) else 0) = (Pi.single k (1 : ℂ) : ℤ → ℂ) n
  simp [Pi.single_apply, eq_comm]

/-- Smooth Fourier span in the actual H¹ embedding is dense in physical L². -/
theorem denseRange_emb : DenseRange (emb (L := L)) := by
  change Dense (LinearMap.range (emb (L := L)).toLinearMap : Set (HL L))
  apply Dense.mono _ (dense_finiteModes (L := L))
  intro u hu
  have hsub : finiteModes (L := L) ≤ LinearMap.range (emb (L := L)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact ⟨modeH1 k, emb_mode k⟩
  exact hsub hu

#print axioms emb_mode
#print axioms denseRange_emb
end QuantumNLS.TerraMultiRound85H1Density
