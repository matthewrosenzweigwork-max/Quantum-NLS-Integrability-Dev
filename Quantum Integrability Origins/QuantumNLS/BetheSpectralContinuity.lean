import QuantumNLS.BethePhysicalAssembly

/-! Spectral continuity of the literal physical action, including spectators. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators InnerProductSpace ComplexConjugate Topology
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
namespace QuantumNLS.BetheSpectralContinuity
open TensorCarrier TensorPlacements PhysicalTensor BetheIntegralOperator
open BetheCompressedKernel BetheBlockSlice BetheHigherPlacement
open BetheTransferKernelAdjoint BetheTransferOperators BethePhysicalAssembly

theorem continuous_rawKernel {m : ℕ} (L : ℝ) (x y : Fin m → ℝ) :
    Continuous (fun z => rawKernel L z x y) := by
  unfold rawKernel rawPlus rawMinus
  split_ifs <;> fun_prop

theorem continuous_compressed_fn (L : ℝ) [Fact (0 < L)] (m : ℕ)
    (p : (Fin m → AddCircle L) × (Fin m → AddCircle L)) :
    Continuous (fun z => (compressedKernel L m z).fn p) := by
  rcases p with ⟨x,y⟩
  simp only [compressedKernel_fn, averagedRaw]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro σ _
  apply continuous_const.mul
  apply continuous_finsetSum
  intro τ _
  exact continuous_rawKernel L _ _

theorem continuous_compressed_bound (L : ℝ) [Fact (0 < L)] (m : ℕ) :
    Continuous (fun z => (compressedKernel L m z).bound) := by
  unfold compressedKernel outputAverage inputAverage weightedKernel permutedKernel
    BetheTensorSlice.sumKernel plusKernel minusKernel
  fun_prop

/-- A parameterized bounded kernel acts continuously on every continuous
input, in the actual L² norm; spectators are retained inside the integral. -/
theorem continuous_sliceMap (L : ℝ) [Fact (0 < L)] (m q : ℕ)
    (k : ℂ → Kernel (torusPiMeasure L m))
    (hk : ∀ p, Continuous (fun z => (k z).fn p))
    (hb : Continuous (fun z => (k z).bound))
    (F : C(Fin (m+q) → AddCircle L, ℂ)) :
    Continuous (fun z => sliceMap L m q (k z) F) := by
  have hs (x : Fin (m+q) → AddCircle L) :
      Continuous (fun z => slice L m q (k z) F x) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    have he : ∀ᶠ z in 𝓝 z₀, (k z).bound < (k z₀).bound + 1 :=
      (hb.tendsto z₀).eventually (gt_mem_nhds (by linarith))
    apply continuousAt_of_dominated
      (bound := fun _ => ((k z₀).bound + 1) * ‖F‖)
    · exact Eventually.of_forall (fun z => (integrable_slice L m q (k z) F x).1)
    · filter_upwards [he] with z hz
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul ((k z).norm_le _ |>.trans hz.le)
        (F.norm_coe_le_norm _) (norm_nonneg _) (by linarith [(k z₀).bound_nonneg])
    · exact integrable_const _
    · exact Eventually.of_forall (fun t =>
        ((hk _).mul continuous_const).continuousAt)
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let C := (torusPiMeasure L m).real univ * ((k z₀).bound + 1) * ‖F‖
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg measureReal_nonneg (by linarith [(k z₀).bound_nonneg])) (norm_nonneg _)
  have he : ∀ᶠ z in 𝓝 z₀, (k z).bound < (k z₀).bound + 1 :=
    (hb.tendsto z₀).eventually (gt_mem_nhds (by linarith))
  have hn (x : Fin (m+q) → AddCircle L) : ‖slice L m q (k z₀) F x‖ ≤ C := by
    refine (norm_slice_le L m q (k z₀) F x).trans ?_
    dsimp [C]
    gcongr
    linarith
  have hi : ContinuousAt (fun z => ∫ x,
      ‖slice L m q (k z) F x - slice L m q (k z₀) F x‖ ^ 2
        ∂torusPiMeasure L (m+q)) z₀ := by
    apply continuousAt_of_dominated (bound := fun _ => (C+C)^2)
    · exact Eventually.of_forall (fun z =>
        (((memLp_slice L m q (k z) F).aestronglyMeasurable.sub
          (memLp_slice L m q (k z₀) F).aestronglyMeasurable).norm.pow 2))
    · filter_upwards [he] with z hz
      filter_upwards with x
      have hzC : ‖slice L m q (k z) F x‖ ≤ C := by
        refine (norm_slice_le L m q (k z) F x).trans ?_
        dsimp [C]
        gcongr
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((norm_sub_le _ _).trans (add_le_add hzC (hn x))) 2
    · exact integrable_const _
    · exact Eventually.of_forall (fun x =>
        (((hs x).sub continuous_const).norm.pow 2).continuousAt)
  have hid (z : ℂ) :
      ‖sliceMap L m q (k z) F - sliceMap L m q (k z₀) F‖ ^ 2 =
        ∫ x, ‖slice L m q (k z) F x - slice L m q (k z₀) F x‖ ^ 2
          ∂torusPiMeasure L (m+q) := by
    rw [← real_inner_self_eq_norm_sq]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (sliceMap L m q (k z) F)
      (sliceMap L m q (k z₀) F), coe_sliceMap L m q (k z) F,
      coe_sliceMap L m q (k z₀) F] with x hx hz h₀
    rw [hx, Pi.sub_apply, hz, h₀, real_inner_self_eq_norm_sq]
  have ht : Tendsto (fun z => ‖sliceMap L m q (k z) F -
      sliceMap L m q (k z₀) F‖ ^ 2) (𝓝 z₀) (𝓝 0) := by
    simpa only [hid, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
      using hi.tendsto
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

/-- The original positive degree, with exactly c^m(N)_m and both physical
averages, acts continuously on the original continuous representative. -/
theorem continuous_degree_position (L : ℝ) [Fact (0 < L)] (m q : ℕ)
    (hm : 0 < m) (c : ℝ) (F : C(Fin (m+q) → AddCircle L, ℂ))
    (ψ : SymSector ℂ (L2T L) (m+q))
    (hψ : physUnitary ψ.1 = ContinuousMap.toLp 2 (torusPiMeasure L (m+q)) ℂ F) :
    Continuous (fun z => physUnitary
      ((BethePhysicalTransfer.transferTerm L (m+q) c z ⟨m,by omega⟩ ψ).1)) := by
  have he := funext (fun z => transferTerm_degree L m q hm c z F ψ hψ)
  rw [he]
  have h : Continuous (fun z : ℂ => ∑ σ : Equiv.Perm (Fin (m+q)),
      physPerm σ (sliceMap L m q (compressedKernel L m z) F)) := by
    apply continuous_finsetSum
    intro σ _
    exact (physPerm σ).continuous.comp
      (continuous_sliceMap L m q (compressedKernel L m)
        (continuous_compressed_fn L m) (continuous_compressed_bound L m) F)
  exact (h.const_smul (((m+q).factorial : ℂ)⁻¹)).const_smul
    (((c^m * (m+q).descFactorial m : ℝ) : ℂ))

/-- Norm continuity of every actual degree on the physical source vector,
with arbitrary particle number and spectator count. -/
theorem continuous_source_degree (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (d : Fin (N+1)) :
    Continuous (fun z => BethePhysicalTransfer.transferTerm L N c z d
      (sourceVector L hc hn)) := by
  by_cases hd : 0 < d.val
  · have hsplit (m q : ℕ) (h : m+q=N) (hm : m=d.val) :
        Continuous (fun z => BethePhysicalTransfer.transferTerm L N c z d
          (sourceVector L hc hn)) := by
      subst N
      obtain ⟨dv,dh⟩ := d
      dsimp only [Fin.val_mk] at hm
      subst dv
      have hp := continuous_degree_position L m q hd c
        (BetheGeneralSliceEndpoints.sourceInput L hc hn) (sourceVector L hc hn)
        (sourceVector_position L hc hn)
      apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
      exact (physUnitary (L := L) (N := m+q)).comp_continuous_iff.mp hp
    exact hsplit d.val (N-d.val) (by omega) rfl
  · simpa only [BethePhysicalTransfer.transferTerm, hd, ↓reduceIte,
      zero_apply] using
      (continuous_const : Continuous (fun _ : ℂ => (0 : SymSector ℂ (L2T L) N)))

/-- Spectral continuity in the actual physical Hilbert norm, proved from
kernel integrals before using any spectral identity at a root. -/
theorem continuous_source_action (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) :
    Continuous (fun z => BethePhysicalTransfer.transfer L N c z
      (sourceVector L hc hn)) := by
  simp only [BethePhysicalTransfer.transfer, add_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    sum_apply]
  apply Continuous.add
  · fun_prop
  · exact continuous_finsetSum _ (fun d _ => continuous_source_degree L hc hn d)

/-- The value of the actual physical operator at every source root is the
explicit numerator derivative divided by the other root differences. -/
theorem transfer_source_root (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (i : Fin N) :
    BethePhysicalTransfer.transfer L N c (BetheSmooth.sourceRoots L n c i)
      (sourceVector L hc hn) =
      (deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k)) •
              sourceVector L hc hn := by
  exact tendsto_nhds_unique
    (((continuous_source_action L hc hn).tendsto _).mono_left nhdsWithin_le_nhds)
    (transfer_source_removable_limit L hc hn i)

/-- The entire scalar continuation constructed from the proved on-shell
numerator factorization; its root values are not the totalized rational values. -/
def spectralValue (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) : ℂ → ℂ :=
  Classical.choose (BetheEndpointProducts.source_spectral_entire_extension
    (Fact.out : 0 < L) hc hn)

theorem spectralValue_entire (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) :
    Differentiable ℂ (spectralValue L hc hn) :=
  (Classical.choose_spec (BetheEndpointProducts.source_spectral_entire_extension
    (Fact.out : 0 < L) hc hn)).1

theorem spectralValue_nonpole (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n)
    (z : ℂ) (hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) :
    spectralValue L hc hn z = TransferSeparation.sFun L c
      (BetheSmooth.sourceRoots L n c) z :=
  (Classical.choose_spec (BetheEndpointProducts.source_spectral_entire_extension
    (Fact.out : 0 < L) hc hn)).2 z hz

theorem spectralValue_root (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (i : Fin N) :
    spectralValue L hc hn (BetheSmooth.sourceRoots L n c i) =
      deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k) := by
  have ht := BetheEndpointProducts.source_spectral_removable_value
    (Fact.out : 0 < L) hc hn i
  have he : (fun z => spectralValue L hc hn z) =ᶠ[
      𝓝[≠] (BetheSmooth.sourceRoots L n c i : ℂ)]
      (fun z => TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z) := by
    filter_upwards [BetheEndpointProducts.source_nonpole_eventually_at_root
      (Fact.out : 0 < L) hc hn i] with z hz
    exact spectralValue_nonpole L hc hn z hz
  exact tendsto_nhds_unique
    ((((spectralValue_entire L hc hn).continuous.tendsto _).mono_left
      nhdsWithin_le_nhds).congr' he) ht

/-- The literal transfer has the continued printed spectral value for all
complex parameters, every N (including zero), and actual positive-c roots. -/
theorem transfer_source_all (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) :
    BethePhysicalTransfer.transfer L N c z (sourceVector L hc hn) =
      spectralValue L hc hn z • sourceVector L hc hn := by
  by_cases hz : ∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)
  · rw [spectralValue_nonpole L hc hn z hz]
    exact transfer_source_nonpole L hc hn z hz
  · push Not at hz
    obtain ⟨i,rfl⟩ := hz
    rw [spectralValue_root L hc hn i]
    exact transfer_source_root L hc hn i

/-- The all-configuration continuous representative also holds at roots. -/
theorem transfer_continuous_representative_all (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) (z : ℂ) :
    physUnitary ((BethePhysicalTransfer.transfer L N c z (sourceVector L hc hn)).1) =
      ContinuousMap.toLp 2 (torusPiMeasure L N) ℂ
        (spectralValue L hc hn z • BetheGeneralSliceEndpoints.sourceInput L hc hn) := by
  rw [transfer_source_all L hc hn z]
  change physUnitary (spectralValue L hc hn z • (sourceVector L hc hn).1) = _
  rw [map_smul, sourceVector_position]
  exact (map_smul (ContinuousMap.toLp 2 (torusPiMeasure L N) ℂ) _ _).symm

/-- basis:eq:eigenvalue, with all its exact physical and scalar hypotheses
and with the printed expression interpreted by its entire continuation. -/
theorem basis_eigenvalue (L : ℝ) [Fact (0 < L)] {N : ℕ}
    {c : ℝ} (hc : 0 < c) {n : Fin N → ℤ} (hn : Antitone n) :
    Differentiable ℂ (spectralValue L hc hn) ∧
    (∀ z, (∀ k, z ≠ (BetheSmooth.sourceRoots L n c k : ℂ)) →
      spectralValue L hc hn z =
        TransferSeparation.sFun L c (BetheSmooth.sourceRoots L n c) z) ∧
    (∀ i : Fin N, spectralValue L hc hn (BetheSmooth.sourceRoots L n c i) =
      deriv (BetheOnShell.numerator L c (BetheSmooth.sourceRoots L n c))
        (BetheSmooth.sourceRoots L n c i) /
          ∏ k ∈ Finset.univ.erase i,
            ((BetheSmooth.sourceRoots L n c i : ℂ) - BetheSmooth.sourceRoots L n c k)) ∧
    (∀ z : ℂ, BethePhysicalTransfer.transfer L N c z (sourceVector L hc hn) =
      spectralValue L hc hn z • sourceVector L hc hn) :=
  ⟨spectralValue_entire L hc hn, spectralValue_nonpole L hc hn,
    spectralValue_root L hc hn, transfer_source_all L hc hn⟩

end QuantumNLS.BetheSpectralContinuity

#print axioms QuantumNLS.BetheSpectralContinuity.continuous_rawKernel
#print axioms QuantumNLS.BetheSpectralContinuity.continuous_compressed_fn
#print axioms QuantumNLS.BetheSpectralContinuity.continuous_compressed_bound
#print axioms QuantumNLS.BetheSpectralContinuity.continuous_sliceMap
#print axioms QuantumNLS.BetheSpectralContinuity.continuous_degree_position
#print axioms QuantumNLS.BetheSpectralContinuity.continuous_source_degree
#print axioms QuantumNLS.BetheSpectralContinuity.continuous_source_action
#print axioms QuantumNLS.BetheSpectralContinuity.transfer_source_root
#print axioms QuantumNLS.BetheSpectralContinuity.spectralValue
#print axioms QuantumNLS.BetheSpectralContinuity.spectralValue_entire
#print axioms QuantumNLS.BetheSpectralContinuity.spectralValue_nonpole
#print axioms QuantumNLS.BetheSpectralContinuity.spectralValue_root
#print axioms QuantumNLS.BetheSpectralContinuity.transfer_source_all
#print axioms QuantumNLS.BetheSpectralContinuity.transfer_continuous_representative_all
#print axioms QuantumNLS.BetheSpectralContinuity.basis_eigenvalue

set_option maxHeartbeats 4000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[
    ``QuantumNLS.BetheSpectralContinuity.continuous_rawKernel,
    ``QuantumNLS.BetheSpectralContinuity.continuous_compressed_fn,
    ``QuantumNLS.BetheSpectralContinuity.continuous_compressed_bound,
    ``QuantumNLS.BetheSpectralContinuity.continuous_sliceMap,
    ``QuantumNLS.BetheSpectralContinuity.continuous_degree_position,
    ``QuantumNLS.BetheSpectralContinuity.continuous_source_degree,
    ``QuantumNLS.BetheSpectralContinuity.continuous_source_action,
    ``QuantumNLS.BetheSpectralContinuity.transfer_source_root,
    ``QuantumNLS.BetheSpectralContinuity.spectralValue,
    ``QuantumNLS.BetheSpectralContinuity.spectralValue_entire,
    ``QuantumNLS.BetheSpectralContinuity.spectralValue_nonpole,
    ``QuantumNLS.BetheSpectralContinuity.spectralValue_root,
    ``QuantumNLS.BetheSpectralContinuity.transfer_source_all,
    ``QuantumNLS.BetheSpectralContinuity.transfer_continuous_representative_all,
    ``QuantumNLS.BetheSpectralContinuity.basis_eigenvalue,
    ``QuantumNLS.BethePhysicalAssembly.blockExpansion,
    ``QuantumNLS.BethePhysicalAssembly.degreeExpansion,
    ``QuantumNLS.BethePhysicalAssembly.complement_zero_rank,
    ``QuantumNLS.BethePhysicalAssembly.mergeChart_zero,
    ``QuantumNLS.BethePhysicalAssembly.sourceCorners_zero,
    ``QuantumNLS.BethePhysicalAssembly.block_zero,
    ``QuantumNLS.BethePhysicalAssembly.source_wave_finCongr,
    ``QuantumNLS.BethePhysicalAssembly.degree_zero,
    ``QuantumNLS.BethePhysicalAssembly.source_degree_ae,
    ``QuantumNLS.BethePhysicalAssembly.transfer_position_ae,
    ``QuantumNLS.BethePhysicalAssembly.source_transfer_expansion_ordered_ae,
    ``QuantumNLS.BethePhysicalAssembly.source_transfer_spectral_ordered_ae,
    ``QuantumNLS.BethePhysicalAssembly.torus_ae_injective,
    ``QuantumNLS.BethePhysicalAssembly.symmetric_ordered_ae,
    ``QuantumNLS.BethePhysicalAssembly.source_transfer_spectral_ae,
    ``QuantumNLS.BethePhysicalAssembly.transfer_source_nonpole,
    ``QuantumNLS.BethePhysicalAssembly.transfer_continuous_representative_nonpole,
    ``QuantumNLS.BethePhysicalAssembly.transfer_source_removable_limit,

    ``QuantumNLS.BetheEndpointProducts.exteriorSelected_true_zero,
    ``QuantumNLS.BetheEndpointProducts.exteriorSelected_false_last,
    ``QuantumNLS.BetheEndpointProducts.mergeChart_original,
    ``QuantumNLS.BetheEndpointProducts.endpoint_charts,
    ``QuantumNLS.BetheEndpointProducts.endpoint_orientations,
    ``QuantumNLS.BetheEndpointProducts.activeRanks_firstPositions,
    ``QuantumNLS.BetheEndpointProducts.primitive_finCongr,
    ``QuantumNLS.BetheEndpointProducts.endpoint_values,
    ``QuantumNLS.BetheEndpointProducts.degreeSubsetEquiv,
    ``QuantumNLS.BetheEndpointProducts.sum_degree_subsets,
    ``QuantumNLS.BetheEndpointProducts.sum_primitive_product,
    ``QuantumNLS.BetheEndpointProducts.frequency_inverse,
    ``QuantumNLS.BetheEndpointProducts.endpoint_spectral_products,
    ``QuantumNLS.BetheEndpointProducts.degree_zero_values,
    ``QuantumNLS.BetheEndpointProducts.endpoint_sum_eq_spectral,
    ``QuantumNLS.BetheEndpointProducts.original_sum_eq_spectral,
    ``QuantumNLS.BetheEndpointProducts.filledScalar,
    ``QuantumNLS.BetheEndpointProducts.other_root_product_ne_zero,
    ``QuantumNLS.BetheEndpointProducts.filledScalar_continuousAt,
    ``QuantumNLS.BetheEndpointProducts.filledScalar_at_root,
    ``QuantumNLS.BetheEndpointProducts.filledScalar_eq_spectral,
    ``QuantumNLS.BetheEndpointProducts.source_numerator_zero,
    ``QuantumNLS.BetheEndpointProducts.source_spectral_removable_value,
    ``QuantumNLS.BetheEndpointProducts.endpoint_sum_removable_value,
    ``QuantumNLS.BetheEndpointProducts.originalExpansion,
    ``QuantumNLS.BetheEndpointProducts.source_nonpole_eventually_at_root,
    ``QuantumNLS.BetheEndpointProducts.original_sum_removable_value,
    ``QuantumNLS.BetheEndpointProducts.source_spectral_entire_extension,
    ``QuantumNLS.BetheEndpointProducts.original_sum_entire_extension,

    ``QuantumNLS.BetheCyclicGeometry.exteriorSelected_true_succ,
    ``QuantumNLS.BetheCyclicGeometry.exteriorSelected_false_castSucc,
    ``QuantumNLS.BetheCyclicGeometry.paired_branch_displacement,
    ``QuantumNLS.BetheCyclicGeometry.cutBooleans_succ_update,
    ``QuantumNLS.BetheCyclicGeometry.paired_orientation,
    ``QuantumNLS.BetheCyclicGeometry.exteriorChart_strict,
    ``QuantumNLS.BetheCyclicGeometry.mergeChart_bounds,
    ``QuantumNLS.BetheCyclicGeometry.antitone_rotate_update_zero,
    ``QuantumNLS.BetheCyclicGeometry.exterior_true_boundary_rank,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chart_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_selected_rank_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_spectator_rank_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_pending_rotation,
    ``QuantumNLS.BetheCyclicGeometry.exterior_merged_rotation,
    ``QuantumNLS.BetheCyclicGeometry.source_primitive_rotate_boundary,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic,
    ``QuantumNLS.BetheCyclicGeometry.exterior_chartPrimitive_cyclic_degree,
    ``QuantumNLS.BetheCyclicGeometry.exteriorValue_cyclic,
    ``QuantumNLS.BetheCyclicGeometry.sum_exterior_cuts,
    ``QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum,
    ``QuantumNLS.BetheCyclicGeometry.CyclicArm,
    ``QuantumNLS.BetheCyclicGeometry.cyclicArmIndexEquiv,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_apply,
    ``QuantumNLS.BetheCyclicGeometry.exterior_cyclic_label_equiv_value,
    ``QuantumNLS.BetheCyclicGeometry.global_exterior_cyclic_sum_degree_zero,
    ``QuantumNLS.BetheCyclicGeometry.sum_original_eq_endpoint_survivors,

    ``QuantumNLS.BetheMarkedCancellation.sourceRoots_finCongr,
    ``QuantumNLS.BetheMarkedCancellation.cornerSummand_finCongr,
    ``QuantumNLS.BetheMarkedCancellation.cornerSummand_boolean_congr,
    ``QuantumNLS.BetheMarkedCancellation.rawLabel_cornerSummand_transport,
    ``QuantumNLS.BetheMarkedCancellation.exchangeLabel_value,
    ``QuantumNLS.BetheMarkedCancellation.promoteLabel_value,
    ``QuantumNLS.BetheMarkedCancellation.actual_value_triple_balance,
    ``QuantumNLS.BetheMarkedCancellation.marked_fiber_cancellation,
    ``QuantumNLS.BetheMarkedCancellation.global_marked_cancellation,
    ``QuantumNLS.BetheMarkedCancellation.sum_labels_eq_exterior,
    ``QuantumNLS.BetheMarkedCancellation.sum_original_eq_exterior,

    ``QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_degree_input,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_rank_iff,
    ``QuantumNLS.BetheExteriorMultiplicity.extendedOutput_sum,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_branch_displacement,
    ``QuantumNLS.BetheExteriorMultiplicity.exterior_full_branch_phase,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorValue,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorSurvivor_value,
    ``QuantumNLS.BetheExteriorMultiplicity.survivorFiberEquiv,
    ``QuantumNLS.BetheExteriorMultiplicity.noneMarkEquiv,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_weighted,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_noneMark_value,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark,
    ``QuantumNLS.BetheExteriorMultiplicity.exteriorRegroupedMark_eq,
    ``QuantumNLS.BetheExteriorMultiplicity.sum_exterior_triples_original_weighted,

    ``QuantumNLS.BetheExteriorReconstruction.rectangle_corner_clipping,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart_sorted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorChart_unique,
    ``QuantumNLS.BetheExteriorReconstruction.exterior_box,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch_admitted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorBranch_corner,
    ``QuantumNLS.BetheExteriorReconstruction.ExteriorData,
    ``QuantumNLS.BetheExteriorReconstruction.Survivor,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_admitted,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_input,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorRaw_noSeam,
    ``QuantumNLS.BetheExteriorReconstruction.toSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.survivorCut,
    ``QuantumNLS.BetheExteriorReconstruction.survivorCut_spec,
    ``QuantumNLS.BetheExteriorReconstruction.fromSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.from_toSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.to_fromSurvivor,
    ``QuantumNLS.BetheExteriorReconstruction.exteriorSurvivorEquiv,

    ``QuantumNLS.BetheExteriorSurvivors.extendedOutput,
    ``QuantumNLS.BetheExteriorSurvivors.cutBooleans,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_corner,
    ``QuantumNLS.BetheExteriorSurvivors.extendedOutput_strict,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_strict,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_origin,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_rectangle,
    ``QuantumNLS.BetheExteriorSurvivors.exteriorSelected_ne_spectator,
    ``QuantumNLS.BetheExteriorSurvivors.exterior_append_injective,
    ``QuantumNLS.BetheExteriorSurvivors.exterior_chart_exists,

    ``QuantumNLS.BetheExteriorCut.rectangle_rise_collision,
    ``QuantumNLS.BetheExteriorCut.rectangle_injective_antitone,
    ``QuantumNLS.BetheExteriorCut.antitone_boolean_cut,
    ``QuantumNLS.BetheExteriorCut.noSeam_boolean_cut,

    ``QuantumNLS.BetheExteriorOrigin.noSeam_iff_injective,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_selected_ne_spectator,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_endpoint_origin,
    ``QuantumNLS.BetheExteriorOrigin.noSeam_coordinates,

    ``QuantumNLS.BetheTripleStrata.seamMark,
    ``QuantumNLS.BetheTripleStrata.FirstLower,
    ``QuantumNLS.BetheTripleStrata.SecondLower,
    ``QuantumNLS.BetheTripleStrata.Higher,
    ``QuantumNLS.BetheTripleStrata.SeamStratum,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv,
    ``QuantumNLS.BetheTripleStrata.raise,
    ``QuantumNLS.BetheTripleStrata.higher_pinned,
    ``QuantumNLS.BetheTripleStrata.higher_demotable,
    ``QuantumNLS.BetheTripleStrata.lower,
    ``QuantumNLS.BetheTripleStrata.higherEquiv,
    ``QuantumNLS.BetheTripleStrata.marked_input_eq,
    ``QuantumNLS.BetheTripleStrata.marked_has_moving,
    ``QuantumNLS.BetheTripleStrata.armEquiv,
    ``QuantumNLS.BetheTripleStrata.tripleEquiv,
    ``QuantumNLS.BetheTripleStrata.lowerEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.higherEquiv_degree,
    ``QuantumNLS.BetheTripleStrata.triple_inputs,
    ``QuantumNLS.BetheTripleStrata.triple_noncollapsed,
    ``QuantumNLS.BetheTripleStrata.sum_triples,
    ``QuantumNLS.BetheTripleStrata.sum_triples_degree,
    ``QuantumNLS.BetheTripleStrata.seamMark_branch,
    ``QuantumNLS.BetheTripleStrata.branchFiberEquiv,
    ``QuantumNLS.BetheTripleStrata.sum_branches,
    ``QuantumNLS.BetheTripleStrata.chosenTripleSum,
    ``QuantumNLS.BetheTripleStrata.sum_chosen_triples,
    ``QuantumNLS.BetheTripleStrata.regroupedMark,
    ``QuantumNLS.BetheTripleStrata.regroupedMark_eq,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original,
    ``QuantumNLS.BetheTripleStrata.sum_regrouped_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_value_weighted,
    ``QuantumNLS.BetheTripleStrata.sum_marks_triples_original_weighted,

    ``QuantumNLS.BetheStrictLabelStrata.endpoint_candidates_disjoint,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCell_strict,
    ``QuantumNLS.BetheStrictLabelStrata.Noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.label_physical_strict,
    ``QuantumNLS.BetheStrictLabelStrata.admitted_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.no_admitted_collapsed,
    ``QuantumNLS.BetheStrictLabelStrata.promoteLabel_noncollapsed,
    ``QuantumNLS.BetheStrictLabelStrata.mixed_incident_iff,
    ``QuantumNLS.BetheStrictLabelStrata.selected_seam_demote_strict,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_data,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_booleans,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_degree,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_inverse,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_ne,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported,
    ``QuantumNLS.BetheStrictLabelStrata.physicalCorner_exchange_any,
    ``QuantumNLS.BetheStrictLabelStrata.exchangeLabel_supported_any,
    ``QuantumNLS.BetheStrictLabelStrata.MixedStratum,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_involutive,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_ne,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_degree,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_input,
    ``QuantumNLS.BetheStrictLabelStrata.mixedExchange_orientation,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv,
    ``QuantumNLS.BetheStrictLabelStrata.lowerOrientationEquiv_degree,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae]
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Spectral continuity nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  for n in #[
    ``QuantumNLS.BetheEndpointProducts.endpoint_spectral_products,
    ``QuantumNLS.BetheEndpointProducts.original_sum_removable_value,
    ``QuantumNLS.BetheEndpointProducts.original_sum_entire_extension,
    ``QuantumNLS.BetheOnShell.sourceRoots_numerator_zero,
    ``QuantumNLS.BetheOnShell.sourceRoots_entire_factorization,
    ``QuantumNLS.BetheSeamProfiles.sum_marks_original,
    ``QuantumNLS.BetheSeamProfiles.sum_collapsed_mark,
    ``QuantumNLS.BetheSeamProfiles.source_chosen_corner_balance,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_promote,
    ``QuantumNLS.BetheCornerTransport.physicalCorner_exchanged,
    ``QuantumNLS.BetheCornerTransport.source_generated_corner_balance,
    ``QuantumNLS.BetheGeneratedLabels.source_transferTerm_labels_ae,
    ``QuantumNLS.BetheInputAdjacency.chartOrderingEquiv,
    ``QuantumNLS.BetheHigherPlacement.coefficient_normalization,
    ``QuantumNLS.BetheSmooth.sourceRoots,
    ``QuantumNLS.BetheCrossDegreeReconstruction.physicalLabelEquiv,
    ``QuantumNLS.BetheCrossDegreeReconstruction.demote_promote_inverse,
    ``QuantumNLS.BetheCrossDegreeReconstruction.promote_demote_inverse] do
    unless seen.contains n do
      throwError "Spectral continuity aggregate missing ingredient: {n}"
  unless seen.contains ``QuantumNLS.BetheEigen.pi_ae_injective do
    throwError "Spectral continuity missing nonatomic product lemma"
  for n in seen do
    if n == ``sorryAx ||
        (n.toString.startsWith "QuantumNLS.BetheEigen." &&
          !(n.toString.startsWith "QuantumNLS.BetheEigen.pi_ae_injective")) || (n.toString.startsWith "QuantumNLS.TransferSeparation" &&
        !(#[``QuantumNLS.TransferSeparation.sFun,
          ``QuantumNLS.TransferSeparation.OnShell,
          ``QuantumNLS.TransferSeparation.shiftPoly,
          ``QuantumNLS.TransferSeparation.eval_shiftPoly,
          ``QuantumNLS.TransferSeparation.prod_plus_mul,
          ``QuantumNLS.TransferSeparation.prod_minus_mul].contains n)) ||
        n.toString.startsWith "QuantumNLS.BetheOneParticleAction." ||
        n.toString.startsWith "QuantumNLS.BetheTwoParticle" ||
        (n.toString.startsWith "QuantumNLS." &&
          (n.toString.toLower.contains "eigenrelation" || n.toString.contains "U5")) then
      throwError "Spectral continuity aggregate forbidden dependency: {n}"
  Lean.logInfo m!"Spectral continuity aggregate audit PASS: {seen.size} transitive constants. Own all-N nonpole physical action, permutation and a.e. transport, continuous representative, physical punctured root limits and inherited BEP1 roots audited. Only the six listed scalar TransferSeparation definitions/lemmas and the nonatomic product lemma from BetheEigen are allowed. Genuine physical source action continuity and all-z physical values, including every source root, proved. No whole-node promotion."
