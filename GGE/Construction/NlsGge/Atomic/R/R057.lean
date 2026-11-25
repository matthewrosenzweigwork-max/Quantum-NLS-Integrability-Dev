import Mathlib
import NlsGge.ThirdConsultation.R.RamerSetting06
import NlsGge.Measure.CountableReconstruction

                                                                                                          
                                                                                                                    
                                                                                                                  
                                                                                                      
                                                                                                                   
                                                                                             
                                                                                                                 
                                                                                                                        
                                                                                                         
set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

namespace R057Aux

/-- Subadditivity over the first `N` cover pieces: a measure of any set is bounded by the mass outside the union
plus the restricted masses. No measurability of `A` is needed. -/
theorem measure_le_compl_union_add_sum {α : Type*} [MeasurableSpace α] (γ : Measure α)
    (U : ℕ → Set α) (hU : ∀ k, MeasurableSet (U k)) (A : Set α) (N : ℕ) :
    γ A ≤ γ (⋃ k ∈ Finset.range N, U k)ᶜ +
      ∑ k ∈ Finset.range N, (γ.restrict (U k)) A := by
  have hsub : A ⊆ (⋃ k ∈ Finset.range N, U k)ᶜ ∪ ⋃ k ∈ Finset.range N, (A ∩ U k) := by
    intro z hz
    by_cases hzV : z ∈ ⋃ k ∈ Finset.range N, U k
    · obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.1 hzV
      exact Set.mem_union_right _ (Set.mem_iUnion₂.2 ⟨k, hk, hz, hzk⟩)
    · exact Set.mem_union_left _ (Set.mem_compl hzV)
  calc γ A ≤ γ ((⋃ k ∈ Finset.range N, U k)ᶜ ∪ ⋃ k ∈ Finset.range N, (A ∩ U k)) :=
        measure_mono hsub
    _ ≤ γ (⋃ k ∈ Finset.range N, U k)ᶜ + γ (⋃ k ∈ Finset.range N, (A ∩ U k)) :=
        measure_union_le _ _
    _ ≤ γ (⋃ k ∈ Finset.range N, U k)ᶜ + ∑ k ∈ Finset.range N, γ (A ∩ U k) := by
        gcongr
        exact measure_biUnion_finset_le _ _
    _ = γ (⋃ k ∈ Finset.range N, U k)ᶜ +
          ∑ k ∈ Finset.range N, (γ.restrict (U k)) A := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Measure.restrict_apply' (hU k)]

/-- Convergence in measure on a finite measure space from convergence in measure on the pieces of a countable
cover whose complement is null (full-measure cover, not all-point cover). -/
theorem tendstoInMeasure_of_null_complement_cover {α β : Type*} [MeasurableSpace α] [EDist β]
    {γ : Measure α} [IsFiniteMeasure γ]
    (U : ℕ → Set α) (hU : ∀ k, MeasurableSet (U k))
    (hcov : γ (⋃ k, U k)ᶜ = 0)
    (f : ℕ → α → β) (g : α → β)
    (hloc : ∀ k, TendstoInMeasure (γ.restrict (U k)) f atTop g) :
    TendstoInMeasure γ f atTop g := by
  have hmeasU : ∀ N : ℕ, MeasurableSet (⋃ k ∈ Finset.range N, U k) := fun N =>
    Finset.measurableSet_biUnion _ (fun k _ => hU k)
  have hmeas : ∀ N : ℕ, NullMeasurableSet (⋃ k ∈ Finset.range N, U k)ᶜ γ := fun N =>
    (hmeasU N).compl.nullMeasurableSet
  have hanti : Antitone (fun N : ℕ => (⋃ k ∈ Finset.range N, U k)ᶜ) := by
    intro N M hNM
    refine Set.compl_subset_compl.2 ?_
    intro z hz
    obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.1 hz
    exact Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hk) hNM), hzk⟩
  have hsub : (⋂ N : ℕ, (⋃ k ∈ Finset.range N, U k)ᶜ) ⊆ (⋃ k, U k)ᶜ := by
    intro z hz
    refine Set.mem_compl ?_
    intro hzU
    obtain ⟨k, hzk⟩ := Set.mem_iUnion.1 hzU
    have hzV := Set.mem_iInter.1 hz (k + 1)
    rw [Set.mem_compl_iff] at hzV
    exact hzV (Set.mem_iUnion₂.2 ⟨k, Finset.mem_range.2 (Nat.lt_succ_self k), hzk⟩)
  have h0 : γ (⋂ N : ℕ, (⋃ k ∈ Finset.range N, U k)ᶜ) = 0 := measure_mono_null hsub hcov
  have hSc : Tendsto (fun N : ℕ => γ (⋃ k ∈ Finset.range N, U k)ᶜ) atTop (𝓝 0) := by
    have hT : Tendsto (fun N : ℕ => γ (⋃ k ∈ Finset.range N, U k)ᶜ) atTop
        (𝓝 (γ (⋂ N : ℕ, (⋃ k ∈ Finset.range N, U k)ᶜ))) :=
      tendsto_measure_iInter_atTop (μ := γ)
        (s := fun N : ℕ => (⋃ k ∈ Finset.range N, U k)ᶜ) hmeas hanti ⟨0, measure_ne_top _ _⟩
    rw [h0] at hT
    exact hT
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have he2 : 0 < e / 2 := ENNReal.half_pos he.ne'
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_nhds_zero.1 hSc (e / 2) he2).exists
  have hsum := tendsto_finsetSum (Finset.range N) (fun k _ => hloc k ε hε)
  rw [Finset.sum_const_zero] at hsum
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum (e / 2) he2] with n hn
  calc γ {x | ε ≤ edist (f n x) (g x)}
      ≤ γ (⋃ k ∈ Finset.range N, U k)ᶜ +
          ∑ k ∈ Finset.range N, (γ.restrict (U k)) {x | ε ≤ edist (f n x) (g x)} :=
        measure_le_compl_union_add_sum γ U hU _ N
    _ ≤ e / 2 + e / 2 := add_le_add hN hn
    _ = e := ENNReal.add_halves e

end R057Aux

section R057Main
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "μ" => ramerGaussian c s

/-- **R-057, local probability cover implies global convergence** (Pro round 6 head, verbatim). -/
theorem tendstoInMeasure_cylindricalDensity_global
    (JN : ℕ → E → ℝ) (Jlim : E → ℝ)
    (hLocal : CountableLocalDensityConvergence μ JN Jlim) :
    TendstoInMeasure μ JN atTop Jlim := by
  unfold CountableLocalDensityConvergence at hLocal
  obtain ⟨U, hU, hcov, hloc⟩ := hLocal
  have : IsProbabilityMeasure (ramerGaussian c s) := by
    unfold ramerGaussian; infer_instance
  exact R057Aux.tendstoInMeasure_of_null_complement_cover U hU hcov JN Jlim hloc

end R057Main
end
end NlsGge.ThirdConsultation.R
