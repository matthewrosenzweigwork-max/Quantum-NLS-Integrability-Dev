import QuantumNLS.EnergyTraceLimit

/-! A positive nuclear series and its exact trace; no spectral theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.PositiveSeriesR13
open TraceClass
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def series (g : ι → E) : E →L[ℂ] E := ∑' i, InnerProductSpace.rankOne ℂ (g i) (g i)

theorem summable_rankOne (g : ι → E) (hg : Summable (fun i => ‖g i‖^2)) :
    Summable (fun i => InnerProductSpace.rankOne ℂ (g i) (g i)) := by
  apply Summable.of_norm
  simpa only [InnerProductSpace.norm_rankOne,pow_two] using hg

theorem diagonal_hasSum (g : ι → E) (hg : Summable (fun i => ‖g i‖^2)) (x : E) :
    HasSum (fun i => ‖inner ℂ x (g i)‖^2) (inner ℂ x (series g x)).re := by
  have hh := ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E x)).hasSum
    (summable_rankOne g hg).hasSum
  have hd (i : ι) : (inner ℂ x (InnerProductSpace.rankOne ℂ (g i) (g i) x)).re =
      ‖inner ℂ x (g i)‖^2 := by
    rw [InnerProductSpace.rankOne_apply,inner_smul_right,
      ← inner_conj_symm (g i) x,RCLike.conj_mul]
    norm_cast
  change HasSum (fun i => inner ℂ x (InnerProductSpace.rankOne ℂ (g i) (g i) x))
    (inner ℂ x (series g x)) at hh
  simpa only [hd] using Complex.hasSum_re hh

theorem series_selfAdjoint (g : ι → E) (hg : Summable (fun i => ‖g i‖^2)) :
    IsSelfAdjoint (series g) := by
  change (series g).adjoint = series g
  have hh := ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap.hasSum (summable_rankOne g hg).hasSum
  change HasSum (fun i => (InnerProductSpace.rankOne ℂ (g i) (g i)).adjoint)
    (series g).adjoint at hh
  simp only [InnerProductSpace.adjoint_rankOne] at hh
  exact hh.unique (summable_rankOne g hg).hasSum

theorem series_positive (g : ι → E) (hg : Summable (fun i => ‖g i‖^2)) :
    (series g).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨series_selfAdjoint g hg,fun x => ?_⟩
  have hh := diagonal_hasSum g hg x
  have hn : 0 ≤ ∑' i, ‖inner ℂ x (g i)‖^2 := tsum_nonneg (fun i => sq_nonneg _)
  rw [hh.tsum_eq] at hn
  change 0 ≤ (inner ℂ (series g x) x).re
  have he := inner_re_symm (𝕜 := ℂ) x (series g x)
  change (inner ℂ x (series g x)).re = (inner ℂ (series g x) x).re at he
  rwa [← he]

theorem series_trace (g : ι → E) (hg : Summable (fun i => ‖g i‖^2)) :
    posTrace (series g) = ∑' i, ENNReal.ofReal (‖g i‖^2) := by
  obtain ⟨κ,b,_⟩ := exists_hilbertBasis ℂ E
  rw [posTrace_eq b (series_positive g hg),traceIn]
  calc
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b j) (g i)‖^2) := by
      apply tsum_congr
      intro j
      have hh := diagonal_hasSum g hg (b j)
      change ENNReal.ofReal (inner ℂ (b j) (series g (b j))).re = _
      rw [← hh.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hh.summable]
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (b j) (g i)‖^2) := ENNReal.tsum_comm
    _ = _ := by simp_rw [tsum_ofReal_norm_inner_sq]

theorem series_finite (g : ι → E) (hg : Summable (fun i => ‖g i‖^2)) :
    IsTraceClass (series g) := by
  rw [IsTraceClass,traceNorm_of_isPositive (series_positive g hg),series_trace g hg,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hg]
  exact ENNReal.ofReal_lt_top
end QuantumNLS.PositiveSeriesR13
