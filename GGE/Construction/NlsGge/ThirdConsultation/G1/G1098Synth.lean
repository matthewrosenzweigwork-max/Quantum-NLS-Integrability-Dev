import Mathlib

                                                                      
                                                                                                       
                                                                                                          
                                                                                                        
                                                                                                  
                                                                                                
                                                                                                                  
set_option autoImplicit false

open Finset Filter Topology

namespace NlsGge.Atomic.G1098Synth

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Finite Cauchy-Schwarz: `‖∑ c_k w_k‖² ≤ (∑ c_k²)(∑ ‖w_k‖²)`. -/
theorem norm_sum_sq_le_hs {I : Type*} (s : Finset I) (c : I → ℝ) (w : I → H) :
    ‖∑ k ∈ s, c k • w k‖ ^ 2 ≤ (∑ k ∈ s, ‖c k‖ ^ 2) * (∑ k ∈ s, ‖w k‖ ^ 2) := by
  have h1 : ‖∑ k ∈ s, c k • w k‖ ≤ ∑ k ∈ s, |c k| * ‖w k‖ :=
    (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun k _ => by
      rw [norm_smul, Real.norm_eq_abs]))
  have h2 : (∑ k ∈ s, |c k| * ‖w k‖) ^ 2 ≤ (∑ k ∈ s, |c k| ^ 2) * (∑ k ∈ s, ‖w k‖ ^ 2) :=
    sum_mul_sq_le_sq_mul_sq s (fun k => |c k|) (fun k => ‖w k‖)
  have h3 : ∑ k ∈ s, |c k| ^ 2 = ∑ k ∈ s, ‖c k‖ ^ 2 :=
    sum_congr rfl fun k _ => by rw [Real.norm_eq_abs]
  calc ‖∑ k ∈ s, c k • w k‖ ^ 2 ≤ (∑ k ∈ s, |c k| * ‖w k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ k ∈ s, |c k| ^ 2) * (∑ k ∈ s, ‖w k‖ ^ 2) := h2
    _ = (∑ k ∈ s, ‖c k‖ ^ 2) * (∑ k ∈ s, ‖w k‖ ^ 2) := by rw [h3]

section Basis

variable (b : HilbertBasis ι ℝ H)

/-- Summable squared coefficients of `h` in the basis (Bessel). -/
theorem summable_coef_sq (h : H) : Summable fun j => ‖inner ℝ (b j) h‖ ^ 2 :=
  b.orthonormal.inner_products_summable h

/-- Summability of the coefficient products in norm, from the AM-GM bound
`|a|·‖w‖ ≤ (a² + ‖w‖²)/2`. -/
theorem summable_norm_coef_smul {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (h : H) :
    Summable fun j => ‖inner ℝ (b j) h • w j‖ := by
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (((summable_coef_sq b h).add hw).div_const 2)
  rw [norm_smul]
  nlinarith [sq_nonneg (‖inner ℝ (b j) h‖ - ‖w j‖)]

theorem summable_coef_smul {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (h : H) :
    Summable fun j => inner ℝ (b j) h • w j :=
  Summable.of_norm (summable_norm_coef_smul b hw h)

/-- The coefficient synthesis of `h` (totalized: a tsum; summability is proved above). -/
noncomputable def synthFun (w : ι → H) (h : H) : H :=
  ∑' j, inner ℝ (b j) h • w j

/-- Finite-partial-sum bound: the squared norm of any finite partial sum is at most `‖h‖² C`,
where `C = ∑' ‖w j‖²`. -/
theorem norm_partial_sq_le {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (h : H) (s : Finset ι) :
    ‖∑ j ∈ s, inner ℝ (b j) h • w j‖ ^ 2 ≤ ‖h‖ ^ 2 * ∑' j, ‖w j‖ ^ 2 := by
  have hA : ∑ j ∈ s, ‖inner ℝ (b j) h‖ ^ 2 ≤ ‖h‖ ^ 2 := Orthonormal.sum_inner_products_le h b.orthonormal
  have hB : ∑ j ∈ s, ‖w j‖ ^ 2 ≤ ∑' j, ‖w j‖ ^ 2 :=
    Summable.sum_le_tsum s (fun j _ => sq_nonneg _) hw
  calc ‖∑ j ∈ s, inner ℝ (b j) h • w j‖ ^ 2
      ≤ (∑ j ∈ s, ‖inner ℝ (b j) h‖ ^ 2) * (∑ j ∈ s, ‖w j‖ ^ 2) :=
        norm_sum_sq_le_hs s (fun j => inner ℝ (b j) h) w
    _ ≤ ‖h‖ ^ 2 * ∑' j, ‖w j‖ ^ 2 :=
        mul_le_mul hA hB (Finset.sum_nonneg fun j _ => sq_nonneg _) (sq_nonneg _)

/-- Norm bound for the synthesis: `‖synthFun w h‖ ≤ sqrt(C) ‖h‖`. -/
theorem norm_synthFun_le {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (h : H) :
    ‖synthFun b w h‖ ≤ Real.sqrt (∑' j, ‖w j‖ ^ 2) * ‖h‖ := by
  have ht : Tendsto (fun s : Finset ι => ‖∑ j ∈ s, inner ℝ (b j) h • w j‖ ^ 2) atTop
      (𝓝 (‖synthFun b w h‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto _).comp (summable_coef_smul b hw h).hasSum
  have hle : ‖synthFun b w h‖ ^ 2 ≤ ‖h‖ ^ 2 * ∑' j, ‖w j‖ ^ 2 :=
    le_of_tendsto ht (Eventually.of_forall fun s => norm_partial_sq_le b hw h s)
  have hC : 0 ≤ ∑' j, ‖w j‖ ^ 2 := tsum_nonneg fun j => sq_nonneg _
  have hs : Real.sqrt (∑' j, ‖w j‖ ^ 2) ^ 2 = ∑' j, ‖w j‖ ^ 2 := Real.sq_sqrt hC
  have hrhs : 0 ≤ Real.sqrt (∑' j, ‖w j‖ ^ 2) * ‖h‖ := by positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hrhs two_ne_zero).mp ?_
  calc ‖synthFun b w h‖ ^ 2 ≤ ‖h‖ ^ 2 * ∑' j, ‖w j‖ ^ 2 := hle
    _ = (Real.sqrt (∑' j, ‖w j‖ ^ 2) * ‖h‖) ^ 2 := by rw [mul_pow, hs]; ring

theorem synthFun_add {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (h k : H) :
    synthFun b w (h + k) = synthFun b w h + synthFun b w k := by
  unfold synthFun
  have e : (fun j => inner ℝ (b j) (h + k) • w j) =
      fun j => inner ℝ (b j) h • w j + inner ℝ (b j) k • w j := by
    funext j
    rw [inner_add_right, add_smul]
  rw [e]
  exact ((summable_coef_smul b hw h).hasSum.add (summable_coef_smul b hw k).hasSum).tsum_eq

theorem synthFun_smul {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (c : ℝ) (h : H) :
    synthFun b w (c • h) = c • synthFun b w h := by
  unfold synthFun
  have e : (fun j => inner ℝ (b j) (c • h) • w j) =
      fun j => c • (inner ℝ (b j) h • w j) := by
    funext j
    rw [real_inner_smul_right, mul_smul]
  rw [e]
  exact ((summable_coef_smul b hw h).hasSum.const_smul c).tsum_eq

/-- The bounded real-linear synthesis operator. -/
noncomputable def synthOp {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := synthFun b w
      map_add' := fun h k => synthFun_add b hw h k
      map_smul' := fun c h => synthFun_smul b hw c h }
    (Real.sqrt (∑' j, ‖w j‖ ^ 2))
    (fun h => norm_synthFun_le b hw h)

theorem synthOp_apply {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (h : H) :
    synthOp b hw h = synthFun b w h := rfl

theorem norm_synthOp_le {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) :
    ‖synthOp b hw‖ ≤ Real.sqrt (∑' j, ‖w j‖ ^ 2) :=
  LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) (fun h => norm_synthFun_le b hw h)

/-- Values on the basis: `synthOp (b j) = w j`. -/
theorem synthOp_basis {w : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2) (j : ι) :
    synthOp b hw (b j) = w j := by
  rw [synthOp_apply]
  unfold synthFun
  rw [tsum_eq_single j]
  · have hn : inner ℝ (b j) (b j) = 1 := by
      rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j]
      norm_num
    rw [hn, one_smul]
  · intro i hi
    have h0 : inner ℝ (b i) (b j) = 0 := b.orthonormal.2 hi
    rw [h0, zero_smul]

/-- Uniqueness: two bounded real-linear maps agreeing on the basis coincide (density). -/
theorem eq_of_basis (K K' : H →L[ℝ] H) (hK : ∀ j, K (b j) = K' (b j)) : K = K' := by
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 := K.hasSum (b.hasSum_repr x)
  have h2 := K'.hasSum (b.hasSum_repr x)
  have e : (fun i => K (b.repr x i • b i)) = fun i => K' (b.repr x i • b i) := by
    funext i
    rw [map_smul, map_smul, hK i]
  rw [e] at h1
  exact h1.unique h2

/-- Difference of two synthesis operators is the synthesis of the difference family. -/
theorem synthOp_sub {w w' : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2)
    (hw' : Summable fun j => ‖w' j‖ ^ 2)
    (hd : Summable fun j => ‖w j - w' j‖ ^ 2) :
    synthOp b hw - synthOp b hw' = synthOp b hd := by
  refine ContinuousLinearMap.ext fun h => ?_
  rw [sub_apply, synthOp_apply, synthOp_apply, synthOp_apply]
  unfold synthFun
  have e : (fun j => inner ℝ (b j) h • (w j - w' j)) =
      fun j => inner ℝ (b j) h • w j - inner ℝ (b j) h • w' j := by
    funext j
    rw [smul_sub]
  rw [show (∑' j, inner ℝ (b j) h • (w j - w' j)) =
      ∑' j, (inner ℝ (b j) h • w j - inner ℝ (b j) h • w' j) from congrArg tsum e]
  exact ((summable_coef_smul b hw h).hasSum.sub (summable_coef_smul b hw' h).hasSum).tsum_eq.symm

/-- The difference estimate used for norm continuity: an ℓ²-small change of the synthesis data
gives a small operator-norm change. -/
theorem norm_synthOp_sub_le {w w' : ι → H} (hw : Summable fun j => ‖w j‖ ^ 2)
    (hw' : Summable fun j => ‖w' j‖ ^ 2)
    (hd : Summable fun j => ‖w j - w' j‖ ^ 2) :
    ‖synthOp b hw - synthOp b hw'‖ ≤ Real.sqrt (∑' j, ‖w j - w' j‖ ^ 2) := by
  rw [synthOp_sub b hw hw' hd]
  exact norm_synthOp_le b hd

end Basis

end NlsGge.Atomic.G1098Synth

