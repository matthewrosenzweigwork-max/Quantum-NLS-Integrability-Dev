import QuantumNLS.RootMassBoundR27
import QuantumNLS.RootMassUniformR27
import QuantumNLS.RootMassCompactR27

/-! Properness of the actual indexed-mass map on the full physical L2 space. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace QuantumNLS.RootMassProperR27
open PhysicalTensor (L2T)
open QuantumNLS.Fourier ActionTorus RootWeightedCellsR26
open RootMassBoundR27 RootMassUniformR27 RootMassCompactR27
variable {L κ : ℝ} [Fact (0 < L)]

lemma mass_bound (hκ : 0 < κ) {K : Set PosL1} {M : ℝ}
    (hM : ∀ a ∈ K,‖a.1‖ ≤ M) {u : L2T L} (hu : RootIndexedMasses.masses (L := L) hκ u ∈ K) :
    ‖u‖^2 ≤ M := by
  have hm := (RootIndexedMasses.root_indexed_masses_proved_clauses hκ u).2.2.2.1
  rw [← hm,RootMassUniformR27.mass_norm]
  exact hM _ hu

lemma error_tendsto (κ L M : ℝ) :
    Tendsto (fun Y : ℝ => 4*κ*M^2/(L*Y^2)+8*κ*M^2/Y) atTop (𝓝 0) := by
  have h := ((tendsto_inv_atTop_zero.pow 2).const_mul (4*κ*M^2/L)).add
    (tendsto_inv_atTop_zero.const_mul (8*κ*M^2))
  convert h using 1
  · funext Y; simp only [div_eq_mul_inv,inv_pow,mul_inv_rev]; ring
  · simp

lemma uniform_fourier (hκ : 0 < κ) {K : Set PosL1} (hK : IsCompact K) :
    ∀ ε : ℝ,0 < ε → ∃ Y : ℝ,0 < Y ∧ ∀ u : L2T L,
      RootIndexedMasses.masses (L := L) hκ u ∈ K → fourierTail Y u < ε := by
  obtain ⟨M₀,hM₀⟩ := hK.exists_bound_of_continuousOn continuous_subtype_val.continuousOn
  let M := max 1 M₀
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM : ∀ a ∈ K,‖a.1‖ ≤ M := fun a ha => (hM₀ a ha).trans (le_max_right _ _)
  intro ε hε
  obtain ⟨Y,hY,hweight,herror⟩ := ((eventually_gt_atTop (max 1 (max (Real.log 3/L) (16*κ*M)))).and
    ((uniform_weighted L hK (show 0 < ε/8 by positivity)).and
      ((error_tendsto κ L M).eventually (gt_mem_nhds (show 0 < ε/2 by positivity))))).exists
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hY.le)
  refine ⟨Y,hY0,fun u hu => ?_⟩
  have hm := mass_bound hκ hM hu
  have h4 : ‖u‖^4 ≤ M^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg ‖u‖) hm 2
  have ht : max 1 (max (Real.log 3/L) (16*κ*‖u‖^2)) ≤ Y := by
    apply (max_le_max le_rfl (max_le_max le_rfl ?_)).trans hY.le
    exact mul_le_mul_of_nonneg_left hm (by positivity)
  calc
    _ ≤ 4*weighted L Y (RootIndexedMasses.masses (L := L) hκ u)+4*κ*‖u‖^4/(L*Y^2)+8*κ*‖u‖^4/Y :=
      fourier_tail_bound hκ u ht
    _ ≤ 4*weighted L Y (RootIndexedMasses.masses (L := L) hκ u)+4*κ*M^2/(L*Y^2)+8*κ*M^2/Y := by
      gcongr
      exact mul_nonneg (Fact.out : 0 < L).le (sq_nonneg Y)
    _ < ε := by linarith [hweight _ hu]

lemma compact_preimage (hκ : 0 < κ) {K : Set PosL1} (hK : IsCompact K) :
    IsCompact ((RootIndexedMasses.masses (L := L) hκ) ⁻¹' K) := by
  let S := (RootIndexedMasses.masses (L := L) hκ) ⁻¹' K
  obtain ⟨M₀,hM₀⟩ := hK.exists_bound_of_continuousOn continuous_subtype_val.continuousOn
  let M := max 1 M₀
  have hM : ∀ a ∈ K,‖a.1‖ ≤ M := fun a ha => (hM₀ a ha).trans (le_max_right _ _)
  have hp : 0 ≤ M := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hS : TotallyBounded ((fourierL2 L) '' S) := by
    apply totallyBounded_of_tails _ (M+1)
    · rintro a ⟨u,hu,rfl⟩
      rw [norm_fourierL2]
      have hm := mass_bound hκ hM hu
      nlinarith [norm_nonneg u]
    · intro ε hε
      obtain ⟨Y,hY,hT⟩ := uniform_fourier (L := L) hκ hK ε hε
      refine ⟨frequencies L Y,?_⟩
      rintro a ⟨u,hu,rfl⟩
      apply lt_of_le_of_lt ?_ (hT u hu)
      let f : {n : ℤ // n ∉ frequencies L Y} → {n : ℤ // Y ≤ |momentum L n|} :=
        fun n => ⟨n.1,outside_frequencies hY n.2⟩
      have hf : Function.Injective f := fun a b h =>
        Subtype.ext (congrArg (fun q : {n : ℤ // Y ≤ |momentum L n|} => q.1) h)
      exact ((Energy.summable_sq (fourierL2 L u)).comp_injective Subtype.val_injective).tsum_le_tsum_of_inj
        f hf (fun _ _ => sq_nonneg _) (fun _ => le_rfl)
        ((Energy.summable_sq (fourierL2 L u)).comp_injective Subtype.val_injective)
  have ht : TotallyBounded S := (totallyBounded_image_iff (fourierL2 L).isometry.isUniformInducing).mp hS
  exact ht.isCompact_of_isClosed (hK.isClosed.preimage (DEF014Continuity.continuous_physical_masses hκ))

end QuantumNLS.RootMassProperR27
