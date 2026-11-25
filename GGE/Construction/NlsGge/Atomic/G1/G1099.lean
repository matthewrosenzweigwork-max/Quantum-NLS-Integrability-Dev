import NlsGge.Atomic.G1.G1098
import NlsGge.Atomic.G1.G1092

                                                                                               
                                                                                        
                                                                                                               
                                                                       
                                                                                                                      
                                                                                                                 
                                                                                                                     
                                                                                                                    
                                                                                                                   
                                                                                                          
                                                                 
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.G1098Basis NlsGge.Atomic.G1098Synth NlsGge.Atomic.G1098Assembly
open NlsGge.Atomic.G1098Reindex

namespace NlsGge.Atomic.G1099
noncomputable section

/-- A synthesis operator with square-summable coefficient family is compact. -/
theorem synthOp_isCompact {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ι ℝ H) {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) :
    IsCompactOperator (synthOp b hw) := by
  set T := synthOp b hw with hT
  have hTb : ∀ i, T (b i) = w i := fun i => synthOp_basis b hw i
  have hS : HasSum (fun i => ‖T (b i)‖ ^ 2) (∑' j, ‖w j‖ ^ 2) := by
    simp only [hTb]
    exact hw.hasSum
  have hlim : Tendsto (fun s : Finset ι =>
      ∑ i ∈ s, ((innerSL ℝ (b i)).smulRight (T (b i)) : H →L[ℝ] H)) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm : ∀ s : Finset ι,
        ‖(∑ i ∈ s, ((innerSL ℝ (b i)).smulRight (T (b i)) : H →L[ℝ] H)) - T‖ ≤
          Real.sqrt ((∑' j, ‖w j‖ ^ 2) - ∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
      intro s
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (fun v => ?_)
      rw [ContinuousLinearMap.sub_apply, norm_sub_rev]
      exact NlsGge.GKDefinitionDesign.G1092L3.trunc_bound T b hS s v
    have h1 : Tendsto (fun s : Finset ι =>
        (∑' j, ‖w j‖ ^ 2) - ∑ i ∈ s, ‖T (b i)‖ ^ 2) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := ∑' j, ‖w j‖ ^ 2)).sub hS
      simpa using this
    have h2 : Tendsto (fun s : Finset ι =>
        Real.sqrt ((∑' j, ‖w j‖ ^ 2) - ∑ i ∈ s, ‖T (b i)‖ ^ 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at this
      exact this
    exact squeeze_zero (fun s => norm_nonneg _) hnorm h2
  exact isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (fun s =>
      NlsGge.GKDefinitionDesign.G1092L3.sum_rankOne_compact s (fun i => b i) (fun i => T (b i))))

/-- G1-099 (verbatim head of STATEMENTS/G1.md lines 691-694; Grebert-Kappeler 10.10). -/
theorem G1_099 (u v : PhysicalL2) :
    mixedSquaredOperator 0 0 = ContinuousLinearMap.id ℝ PhysicalL2 ∧
    IsCompactOperator
      (mixedSquaredOperator u v - mixedSquaredOperator 0 0) := by
  refine ⟨?_, ?_⟩
  · refine NlsGge.Atomic.G1098Assembly.mixedSquaredOperator_eq_of 0 0
      (ContinuousLinearMap.id ℝ PhysicalL2) ?_
    intro n minus
    rw [ContinuousLinearMap.id_apply, NlsGge.Atomic.G1098.mixedColumn_eq_complex, realSlice_zero,
      NlsGge.ThirdConsultation.G1098M2A.complexMixedColumn_vacuum]
  · rw [NlsGge.Atomic.G1098.mixedSquaredOperator_eq_synthA,
      NlsGge.Atomic.G1098.mixedSquaredOperator_eq_synthA]
    unfold NlsGge.Atomic.G1098.synthA
    rw [add_sub_add_left_eq_sub,
      synthOp_sub mixedRealBasis (NlsGge.Atomic.G1098.summable_wfam u v)
        (NlsGge.Atomic.G1098.summable_wfam 0 0)
        (NlsGge.Atomic.G1098.summable_wfam_sub u v 0 0)]
    exact synthOp_isCompact mixedRealBasis (NlsGge.Atomic.G1098.summable_wfam_sub u v 0 0)

end
end NlsGge.Atomic.G1099
