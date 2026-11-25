import QuantumNLS.Ext025B2Vague
import QuantumNLS.Ext025B2Weak

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-10

Exact source text (FINAL_EXTERNAL_THEOREM_INSTANCES.json, sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782, instance
`FIN-EXT025-GP-10`, "Vague compactness of bounded measures and the mass-preserving weak
upgrade"):

* Hypotheses: "The measures are nonnegative finite Borel measures on the real line with a
  common bound on their total masses. Vague convergence is tested against compactly
  supported continuous functions." and "For the upgrade to bounded continuous test
  functions, the total masses also converge to the mass of the vague limit."
* Conclusion: "Every bounded sequence has a vaguely convergent subsequence. Vague
  convergence plus convergence of masses gives weak convergence against bounded continuous
  functions."
* Normalization: "The contract is on the real line ... It is not a substitute for the
  specialized infinite-dimensional strong quantum de Finetti theorem."

Lean reading.  Nonnegative finite Borel measures on `ℝ` are `FiniteMeasure ℝ`; total mass is
`FiniteMeasure.mass`; vague convergence is convergence of `∫ f dμ_n` for every
`f : C_c(ℝ, ℝ)`.  Clause 1: a mass-bounded sequence has a subsequence converging vaguely
to a finite Borel measure whose mass is `≤` the bound (the limit is in general only a
subprobability-type measure: mass may escape to infinity, as the application wrapper says, and
no full-mass conclusion is claimed).  Clause 2 is stated for an arbitrary filter (in
particular the filter `atTop` of a sequence, and any subsequence): vague convergence and
convergence of total masses give convergence of `∫ f` for every bounded continuous `f`
(real and complex valued) and weak convergence in the topology of `FiniteMeasure ℝ`.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped CompactlySupported NNReal

namespace QuantumNLS.Ext025L

universe u

/-- FIN-EXT025-GP-10 as a Lean theorem. -/
theorem contract_GP10 :
    -- (1) every mass-bounded sequence has a vaguely convergent subsequence
    (∀ (C : ℝ≥0) (u : ℕ → FiniteMeasure ℝ), (∀ n, (u n).mass ≤ C) →
      ∃ (μ : FiniteMeasure ℝ) (φ : ℕ → ℕ), μ.mass ≤ C ∧ StrictMono φ ∧
        ∀ f : C_c(ℝ, ℝ), Tendsto (fun n => ∫ x, f x ∂(u (φ n))) atTop (𝓝 (∫ x, f x ∂μ))) ∧
    -- (2) vague convergence plus convergence of masses gives weak convergence
    (∀ (ι : Type u) (L : Filter ι) (u : ι → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ),
      (∀ f : C_c(ℝ, ℝ), Tendsto (fun i => ∫ x, f x ∂(u i)) L (𝓝 (∫ x, f x ∂μ))) →
      Tendsto (fun i => ((u i).mass : ℝ)) L (𝓝 (μ.mass : ℝ)) →
      (∀ f : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun i => ∫ x, f x ∂(u i)) L (𝓝 (∫ x, f x ∂μ))) ∧
      (∀ f : BoundedContinuousFunction ℝ ℂ,
        Tendsto (fun i => ∫ x, f x ∂(u i)) L (𝓝 (∫ x, f x ∂μ))) ∧
      Tendsto u L (𝓝 μ)) := by
  refine ⟨?_, ?_⟩
  · intro C u hu
    exact Ext025B2Vague.«FIN-EXT025-GP-10» C u hu
  · intro ι L u μ hv hm
    refine ⟨?_, ?_, ?_⟩
    · intro f
      exact (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
        (Ext025B2Weak.«FIN-EXT025-GP-10-weak-upgrade» u μ hv hm)) f
    · exact Ext025B2Weak.«FIN-EXT025-GP-10-complex-upgrade» u μ hv hm
    · exact Ext025B2Weak.«FIN-EXT025-GP-10-weak-upgrade» u μ hv hm

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP10
