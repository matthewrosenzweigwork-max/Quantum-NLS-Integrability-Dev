import QuantumNLS.AllOrderEnergyFinalR60a
import QuantumNLS.ReconstructionInputsR33m

/-!
# MainTheoremR01Physical: part (iv) of R-AF8F7562 `thm:main` (physical marginals)

PRINTED SOURCE: `source-text/chapters/principal_correspondence.tex`, lines 55-68 (part (iv), eq:physical-main and
eq:allorder-energy-main); proof `source-text/chapters/core/correspondence_theorem.tex`, lines 39-45.

* eq:physical-main, for every compact `K` in the active joint times, from the accepted R-E679E41D final
  `ActualModelCorollaryR60a.cor_MP_actual_model` with the action set empty
  (`AllOrderEnergyInputsR56a.empty_action_trace_limit`, which also identifies the empty-action target with the
  joint flow), and the compact set enclosed in a symmetric box.
* eq:allorder-energy-main, its two preparation classes, from the accepted R-568BCDF8 final
  `AllOrderEnergyFinalR60a.energy_allorder_energy`. The common packets of part (i) are handled in
  `MainTheoremR01Values.PacketClause` (the same sequence carries the DEF-031 energy preparation).

No acceptance claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Filter Topology
open scoped ENNReal

namespace QuantumNLS.MainTheoremR01Physical

open Def033HierarchyR24m (Smooth physical jointSmooth)
open BetheCoefficientTransform (HN)
open TensorCarrier (HilbertTensorPower htpow)
open PhysicalTensor (L2T reducedDensityN)
open ActualModelTargetR53a (hamFlows)
open EnergyPreparationDef (EnergyPreparation)

variable {L κ : ℝ} [Fact (0 < L)]

/-- The accepted hierarchy theorem (R-7B122087 binding). -/
abbrev H (hκ : 0 < κ) := RB7BindFinal.hierarchyInputR25m_unconditional (L := L) hκ

/-- The actual higher flows `Φ_t` of the accepted hierarchy (the object used by parts (iii) and (v)). -/
abbrev F (hκ : 0 < κ) : ActualModelTargetR53a.HigherFlows L κ := ReconstructionR33m.flows hκ (H (L := L) hκ)

/-- The R-568BCDF8 flows and the R-FAF88C8A flows are the same object. -/
theorem flows_eq (hκ : 0 < κ) : AllOrderEnergyInputsR56a.flows hκ (H (L := L) hκ) = F (L := L) hκ := rfl

/-- **eq:physical-main.** For every fixed rank `k`, finite charge family `𝓡`, compact time set `K`, and every
normalized preparation with `‖ψ_N - u^{⊗N}‖ → 0` (particle number `N+1`), the trace-one `k`-particle marginal of
`U_N(t)ψ_N` converges in trace norm to `|(Φ_t u)^{⊗k}⟩⟨(Φ_t u)^{⊗k}|`, uniformly on `K`. -/
def PhysicalMarginal (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
  ∀ (ψ : ∀ N : ℕ, HN L (N + 1)), (∀ N, ‖ψ N‖ = 1) →
    Tendsto (fun N => ‖ψ N - HighMomentsOps.wvec (N + 1) (physical u)‖) atTop (𝓝 0) →
  ∀ k : ℕ, Tendsto (fun N => if hk : k ≤ N + 1 then
      ⨆ t : K, TraceClass.traceNorm (reducedDensityN (N + 1) k hk
        (ActualModelQuantumR52a.chargeUnitary hκ R t.val N (ψ N) : HilbertTensorPower ℂ (L2T L) (N + 1)) -
        Prop025OInputs.tensorProj k (physical (jointSmooth (hamFlows (F (L := L) hκ) R) t.val u)))
      else 0) atTop (𝓝 0)

theorem physical_marginal (hκ : 0 < κ) : PhysicalMarginal (L := L) hκ := by
  intro u hu R K hK ψ hψ hprep k
  classical
  have hb : ∀ r : ℕ, ∃ B : ℝ, ∀ t ∈ K, |t r| ≤ B := by
    intro r
    obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_abs.comp (continuous_apply r)).continuousOn
    exact ⟨B, fun t ht => hB (Set.mem_image_of_mem _ ht)⟩
  choose B hB using hb
  let T : ℕ → ℝ := fun r => max 0 (B r)
  have h := AllOrderEnergyInputsR56a.empty_action_trace_limit hκ (H (L := L) hκ)
    (fun v hv I R' k' Θ T' hΘ hT' => ActualModelCorollaryR60a.cor_MP_actual_model hκ v hv I R' k' Θ T' hΘ hT')
    u hu R T (fun r _ => le_max_left _ _) k ψ hψ hprep
  rw [flows_eq] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => bot_le) (fun N => ?_)
  dsimp only
  split_ifs with hk
  · exact iSup_le fun t => le_iSup_of_le
      ⟨t.val, fun r _ => (hB r t.val t.property).trans (le_max_right _ _)⟩ le_rfl
  · exact le_rfl

/-- **eq:allorder-energy-main** with both printed preparation hypotheses (norm closeness and form-energy
preparation, DEF-031 `EnergyPreparation`), for every rank `k ≥ 1`, finite `𝓡` and compact `K`; and exact
products are energy-prepared. -/
def EnergyClause (hκ : 0 < κ) : Prop :=
  ∀ (u : Smooth L), ‖physical u‖ = 1 →
  ∀ (R : Finset ℕ) (K : Set (ℕ → ℝ)), IsCompact K →
    (∀ (ψ : ∀ N, HilbertTensorPower ℂ (L2T L) N) (hψ : EnergyPreparation κ (physical u) ψ) (k : ℕ), 1 ≤ k →
      AllOrderEnergyAssemblyR57a.EnergyLimit hκ (H (L := L) hκ) u
        (fun n => ⟨ψ (n + 1), hψ.mem_sector (n + 1)⟩) R K k) ∧
    EnergyPreparation κ (physical u) (fun N => htpow N (physical u))

theorem energy_clause (hκ : 0 < κ) : EnergyClause (L := L) hκ := by
  intro u hu R K hK
  obtain ⟨h1, h2, -, -⟩ := AllOrderEnergyFinalR60a.energy_allorder_energy (L := L) hκ u hu R K hK
  exact ⟨h1, h2⟩

end QuantumNLS.MainTheoremR01Physical

#print axioms QuantumNLS.MainTheoremR01Physical.physical_marginal
#print axioms QuantumNLS.MainTheoremR01Physical.energy_clause
