import QuantumNLS.L2Flow

/-! Bridge from a continuous global H¹ Duhamel curve to the accepted L² flow.
The actual transformed curves' H¹ continuity and Duhamel identities remain
separate obligations; this lemma does not assume or assert symmetry. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open QuantumNLS.Sobolev QuantumNLS.LocalWellPosedness QuantumNLS.H1Bridge
open QuantumNLS.L2Flow QuantumNLS.L4StrichartzL2
namespace QuantumNLS.TerraMultiRound85H1Bridge
variable {L : ℝ} [Fact (0 < L)]

/-- The accepted `H1Bridge.bridge_gen` supplies every local L⁴ representative
of a continuous H¹ curve satisfying the rebased Duhamel formula. -/
theorem isFlow_of_global_H1Duhamel {κ : ℝ} (v : ℝ → h04 L 1)
    (hv : Continuous v)
    (hduh : ∀ a t : ℝ, v t = Sgrp 1 (t-a) (v a) - (2*Complex.I*κ) •
      ∫ r in a..t, Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (v r))) :
    IsFlow κ (fun t => emb (v t)) := by
  refine ⟨emb.continuous.comp hv, fun α β hαβ hlen => ?_⟩
  obtain ⟨U, hU, hUw, -⟩ := bridge_gen hαβ hlen hv α (hduh α) ⟨le_rfl, hαβ⟩
  exact ⟨U, α, ⟨le_rfl, hαβ⟩, hU, hUw⟩

/-- Uniqueness identifies such a curve with the actual physical flow. -/
theorem flowMap_of_global_H1Duhamel {κ : ℝ} (hκ : 0 ≤ κ) (v : ℝ → h04 L 1)
    (hv : Continuous v)
    (hduh : ∀ a t : ℝ, v t = Sgrp 1 (t-a) (v a) - (2*Complex.I*κ) •
      ∫ r in a..t, Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (v r))) :
    ∀ t, flowMap hκ (emb (v 0)) t = emb (v t) := by
  have h := flowMap_unique hκ (emb (v 0)) (isFlow_of_global_H1Duhamel v hv hduh) rfl
  intro t
  exact (congrFun h t).symm

/-- A global H¹ mild solution based at zero meets the rebased hypotheses,
so it is the actual L² flow at its initial value. -/
theorem flowMap_of_global_mild {κ : ℝ} (hκ : 0 ≤ κ) (u0 : h04 L 1)
    (v : ℝ → h04 L 1) (hv : IsMild (le_refl (1 : ℝ)) κ Set.univ u0 v) :
    ∀ t, flowMap hκ (emb u0) t = emb (v t) := by
  have h0 : v 0 = u0 := hv.at_zero
  have hduh : ∀ a t : ℝ, v t = Sgrp 1 (t-a) (v a) - (2*Complex.I*κ) •
      ∫ r in a..t, Sgrp 1 (t-r) (Fh (le_refl (1 : ℝ)) (v r)) := by
    intro a t
    exact duhamel_rebase (le_refl (1 : ℝ)) hv (Set.mem_univ a) (Set.mem_univ t)
  have he := flowMap_of_global_H1Duhamel hκ v (continuousOn_univ.mp hv.cont) hduh
  simpa [h0] using he

#print axioms flowMap_of_global_mild
#print axioms isFlow_of_global_H1Duhamel
#print axioms flowMap_of_global_H1Duhamel
end QuantumNLS.TerraMultiRound85H1Bridge
