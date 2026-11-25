import QuantumNLS.IndexedCoefficientAnalyticR29b
import QuantumNLS.IndexedInverseBoundsR29b
import QuantumNLS.HighMomentsDerivative

/-! Continuity of chosen inverse kernels on the source contour tubes.
This supplies measurability of the actual kernels for subsequent Cauchy and
contour integration; no parameter continuity is assumed. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace QuantumNLS.IndexedKernelContinuityR29b
open TensorCarrier KernelDefinition LocalPlacement KernelConvergence
  PlacementFusion PlacementProduct PlacementFiberPrefixCommutatorAssembly
  PlacementFiberPrefixProductExpansionLOCAL011 Local013Powers Local013PowerSeries
  IndexedInverseR28b IndexedTransferR28b IndexedInverseSeriesR28b
  IndexedInverseBoundsR29b IndexedCoefficientAnalyticR29b

section Generic
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local instance kernelNormed (p : ℕ) : NormedAddCommGroup (BoundedSymmetricKernel H p) :=
  ContinuousLinearMap.toNormedAddCommGroup

theorem continuous_average {p q s : ℕ} (hsp : s ≤ p) (hsq : s ≤ q) :
    Continuous (fun ab : BoundedSymmetricKernel H p × BoundedSymmetricKernel H q =>
      averagedOverlapKernel hsp hsq ab.1 ab.2) := by
  apply continuous_iff_continuousAt.mpr
  intro ab
  change Tendsto (fun x : BoundedSymmetricKernel H p × BoundedSymmetricKernel H q =>
    averagedOverlapKernel hsp hsq x.1 x.2) (𝓝 ab)
    (𝓝 (averagedOverlapKernel hsp hsq ab.1 ab.2))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hA : Tendsto (fun x : BoundedSymmetricKernel H p × BoundedSymmetricKernel H q =>
      ‖x.1-ab.1‖) (𝓝 ab) (𝓝 0) := by simpa using (continuous_fst.tendsto ab).sub_const ab.1 |>.norm
  have hB : Tendsto (fun x : BoundedSymmetricKernel H p × BoundedSymmetricKernel H q =>
      ‖x.2-ab.2‖) (𝓝 ab) (𝓝 0) := by simpa using (continuous_snd.tendsto ab).sub_const ab.2 |>.norm
  have hb := (continuous_snd.tendsto ab).norm
  have hu := (hA.mul hb).add (hB.const_mul ‖ab.1‖)
  simp only [zero_mul,mul_zero,zero_add] at hu
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun x => TerraMultiRound21OverlapContinuity.average_difference_bound
      hsp hsq x.1 ab.1 x.2 ab.2) hu

#print axioms continuous_average

theorem continuous_spike {N n : ℕ} (p : Fin (N+1)) :
    Continuous (fun K : BoundedSymmetricKernel H n => (kernelSpike (N := N) K) p) := by
  unfold kernelSpike
  split_ifs with h
  · cases h
    exact continuous_id
  · exact continuous_const

#print axioms continuous_spike

theorem continuous_overlap_term (N : ℕ) (p q : Fin (N+1))
    (s : PlacementFiberPrefixAlignedTransport.FeasibleOverlapIndex N p.1 q.1) (j : Fin (N+1)) :
    Continuous (fun ab : KernelList (H := H) N × KernelList (H := H) N =>
      overlapProductKernelTerm (H := H) ab.1 ab.2 p q s j) := by
  have hA : Continuous (fun ab : KernelList (H := H) N × KernelList (H := H) N => ab.1 p) :=
    (continuous_apply p).comp continuous_fst
  have hB : Continuous (fun ab : KernelList (H := H) N × KernelList (H := H) N => ab.2 q) :=
    (continuous_apply q).comp continuous_snd
  have hc := (continuous_average (H := H)
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _))).comp (hA.prodMk hB)
  have hs := hc.const_smul ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)
  exact (continuous_spike (H := H) (N := N) (n := unionSize p.1 q.1 s.1.1) j).comp hs

#print axioms continuous_overlap_term

theorem continuous_product_coord (N : ℕ) (j : Fin (N+1)) :
    Continuous (fun ab : KernelList (H := H) N × KernelList (H := H) N =>
      chosenProductKernelList (H := H) N ab.1 ab.2 j) := by
  classical
  unfold chosenProductKernelList
  simp only [Finset.sum_apply]
  exact continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ =>
    continuous_finsetSum _ fun s _ => continuous_overlap_term (H := H) N p q s j

theorem continuous_chosen_product (N : ℕ) :
    Continuous (fun ab : KernelList (H := H) N × KernelList (H := H) N =>
      chosenProductKernelList (H := H) N ab.1 ab.2) :=
  continuous_pi (fun j => continuous_product_coord (H := H) N j)

#print axioms continuous_chosen_product


theorem continuous_pow_family {X : Type*} [TopologicalSpace X]
    (A : X → ∀ N : ℕ, KernelList (H := H) N)
    (hA : ∀ N, Continuous (fun x => A x N)) (k N : ℕ) :
    Continuous (fun x => powList (H := H) (A x) k N) := by
  induction k with
  | zero => exact continuous_const
  | succ k ih =>
    apply continuous_pi
    intro j
    change Continuous (fun x => chosenProductKernelList (H := H) N (A x N)
      (powList (H := H) (A x) k N) j)
    have hp : Continuous (fun x => (A x N,powList (H := H) (A x) k N)) := (hA N).prodMk ih
    exact Continuous.comp'
      (f := fun x : X => (A x N,powList (H := H) (A x) k N))
      (g := fun ab : KernelList (H := H) N × KernelList (H := H) N =>
        chosenProductKernelList (H := H) N ab.1 ab.2 j)
      (continuous_product_coord (H := H) N j) hp

#print axioms continuous_pow_family

end Generic

attribute [local instance] kernelNormed
open PhysicalTensor
variable {L κ : ℝ} [Fact (0 < L)]

theorem continuous_kernels (κ : ℝ) (N : ℕ) :
    Continuous (fun z => kernels (L := L) κ z N) := by
  apply continuous_pi
  intro p
  unfold kernels
  split_ifs
  · exact continuous_const
  · exact (HighMomentsDerivative.differentiable_physicalKernel L p.1).continuous.const_smul
      (((κ^p.1*HighMomentsRank.fallR N p.1 : ℝ) : ℂ))

#print axioms continuous_kernels

theorem continuous_powList (κ : ℝ) (k N : ℕ) :
    Continuous (fun z => powList (kernels (L := L) κ z) k N) := by
  exact continuous_pow_family (H := L2T L) (fun z : ℂ => kernels (L := L) κ z)
    (continuous_kernels (L := L) κ) k N

#print axioms continuous_powList

/-- Every coordinate of the chosen inverse expansion is continuous on the
entire tube, with a summable majorant independent of N and z. -/
theorem continuousOn_inverseKernels (hκ : 0 < κ) (hs : κ*L ≤ 1/1000000000000)
    (n : ℤ) (N : ℕ) (p : Fin (N+1)) :
    ContinuousOn (fun z => inverseKernels (L := L) κ z N p) (tube L n) := by
  have hq := q_bounds hκ hs
  have hq1 : q κ L < 1 := by linarith
  have hg : Summable (fun k : ℕ => W κ*(q κ L)^k) :=
    (summable_geometric_of_lt_one hq.1 hq1).mul_left _
  change ContinuousOn (fun z => ∑' k, coeff (L := L) κ z k •
    powList (kernels (L := L) κ z) k N p) (tube L n)
  refine continuousOn_tsum (F := BoundedSymmetricKernel (L2T L) p.1)
    (f := fun k z => coeff (L := L) κ z k • powList (kernels (L := L) κ z) k N p) ?_ hg ?_
  · intro k
    exact ((analytic_coeff (L := L) hκ n k).continuousOn).smul
      ((continuous_apply p).comp (continuous_powList (L := L) κ k N)).continuousOn
  · intro k z hz
    rw [RadiusBound.norm_smul_kernel (H := L2T L)]
    have hk := (norm_coeff_le_radiusBound (H := L2T L) (by norm_num : (1 : ℝ) ≤ 8)
      (powList (kernels (L := L) κ z) k N) p).trans
      (radiusBound_powList_le (H := L2T L) (by norm_num) (radius_bound (L := L) hκ hs n hz) k N)
    calc
      _ ≤ (W κ*(rstar/2)⁻¹^k)*(256*(κ*L))^k :=
        mul_le_mul (norm_coeff_le_uniform (L := L) hκ n hz k) hk (norm_nonneg _) (by
          exact mul_nonneg (W_pos hκ).le (pow_nonneg (by norm_num [rstar]) _))
      _ = W κ*(q κ L)^k := by
        rw [mul_assoc,← mul_pow]
        congr 2
        unfold q
        ring

end QuantumNLS.IndexedKernelContinuityR29b
#print axioms QuantumNLS.IndexedKernelContinuityR29b.continuous_chosen_product
#print axioms QuantumNLS.IndexedKernelContinuityR29b.continuousOn_inverseKernels
