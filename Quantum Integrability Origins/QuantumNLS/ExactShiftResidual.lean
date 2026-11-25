import QuantumNLS.FullOccupationAffinity

/-! R-284267AA: literal full-array residuals of the frozen FOA1 transfer. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace QuantumNLS.ExactShiftResidual
open Occupation OccupationHilbert FullOccupationAffinity
variable {N : ℕ}
local instance (I : Type*) : DecidableEq I := Classical.decEq I

theorem norm_sq_tsum {I : Type*} (v : L2 I) : ‖v‖ ^ 2 = ∑' i, ‖v i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) v

theorem summable_norm_sq {I : Type*} (v : L2 I) : Summable (fun i => ‖v i‖ ^ 2) := by
  simpa using (lp.memℓp v).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

theorem ext_single {I J : Type*} {A B : L2 I →L[ℂ] L2 J}
    (h : ∀ i, A (lp.single 2 i 1) = B (lp.single 2 i 1)) : A = B := by
  apply ContinuousLinearMap.ext
  intro v
  have hs (i : I) : A (lp.single 2 i (v i)) = B (lp.single 2 i (v i)) := by
    have hi := congrArg (fun x => (v i) • x) (h i)
    simpa only [← map_smul, ← lp.single_smul, smul_eq_mul, mul_one] using hi
  exact ((A.hasSum (lp.hasSum_single (by norm_num) v)).congr_fun (fun i => (hs i).symm)).unique
    (B.hasSum (lp.hasSum_single (by norm_num) v))

def emptyCoefficients (a : ℤ) (g : H N) : L2 {m : Arr N // m.1 a = 0} :=
  restrictL2 Subtype.val Subtype.val_injective g

/-- The missing-support probability is the literal full occupation sum. -/
def missing (a : ℤ) (g : H N) : ℝ := ∑' m : {m : Arr N // m.1 a = 0}, ‖g m.1‖ ^ 2

theorem missing_eq_norm (a : ℤ) (g : H N) : missing a g = ‖emptyCoefficients a g‖ ^ 2 := by
  rw [norm_sq_tsum]
  simp only [missing, emptyCoefficients, restrictL2_apply]

theorem missing_nonneg (a : ℤ) (g : H N) : 0 ≤ missing a g :=
  tsum_nonneg (fun _ => sq_nonneg _)

theorem support_partition (a : ℤ) (g : H N) :
    ‖sourceCoefficients a g‖ ^ 2 + missing a g = ‖g‖ ^ 2 := by
  have h := (summable_norm_sq g).tsum_subtype_add_tsum_subtype_compl
    {m : Arr N | DonorOK a m.1}
  have he : {m : Arr N | m.1 a = 0} = {m : Arr N | DonorOK a m.1}ᶜ := by
    ext m; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, DonorOK]; omega
  have hm : missing a g = ∑' m : ↥({m : Arr N | DonorOK a m.1}ᶜ), ‖g m.1‖ ^ 2 := by
    change (∑' m : ↥{m : Arr N | m.1 a = 0}, ‖g m.1‖ ^ 2) = _
    rw [he]
  rw [norm_sq_tsum, norm_sq_tsum, hm]
  simp only [sourceCoefficients, restrictL2_apply]
  exact h

theorem phase_diagonal_norm {I : Type*} (α : I → Phase) (v : L2 I) :
    ‖diagonal (fun i => (α i).1) 1 zero_le_one (fun i => (α i).2.le) v‖ = ‖v‖ := by
  have hs : ‖diagonal (fun i => (α i).1) 1 zero_le_one (fun i => (α i).2.le) v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [norm_sq_tsum, norm_sq_tsum]
    apply tsum_congr
    intro i
    simp only [diagonal_apply, norm_mul, (α i).2, one_mul]
  nlinarith [norm_nonneg v, norm_nonneg
    (diagonal (fun i => (α i).1) 1 zero_le_one (fun i => (α i).2.le) v)]

theorem diagonal_adjoint {I : Type*} (α : I → Phase) :
    (diagonal (fun i => (α i).1) 1 zero_le_one (fun i => (α i).2.le)).adjoint =
    diagonal (fun i => conj (α i).1) 1 zero_le_one
      (fun i => by rw [Complex.norm_conj]; exact (α i).2.le) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [diagonal_apply, RCLike.inner_apply, map_mul]
  ring

theorem transfer_norm_sq (a b : ℤ) (α : Donor N a → Phase) (g : H N) :
    ‖transfer a b α g‖ ^ 2 = ‖g‖ ^ 2 - missing a g := by
  unfold FullOccupationAffinity.transfer transferOp
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometry.norm_map]
  rw [phase_diagonal_norm]
  change ‖sourceCoefficients a g‖ ^ 2 = ‖g‖ ^ 2 - missing a g
  linarith [support_partition a g]

theorem transfer_adjoint_norm (a b : ℤ) (α : Donor N a → Phase) (g : H N) :
    ‖(transfer a b α).adjoint g‖ = ‖targetCoefficients a b g‖ := by
  change ‖(transferOp N a b _ _).adjoint g‖ = _
  simp only [transferOp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  simp only [restrictL2, ContinuousLinearMap.adjoint_adjoint, diagonal_adjoint,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  exact phase_diagonal_norm (fun i => ⟨conj (α i).1, by simp [(α i).2]⟩) _

/-- The actual bijection between complete donor and receiver arrays. -/
def edgeEquiv (a b : ℤ) (hab : a ≠ b) : Donor N a ≃ Donor N b where
  toFun m := ⟨destination N a b m, donorOK_shift_receiver hab⟩
  invFun m := ⟨destination N b a m, donorOK_shift_receiver hab.symm⟩
  left_inv m := by apply Subtype.ext; apply Subtype.ext; exact shift_shift_reverse m.2
  right_inv m := by apply Subtype.ext; apply Subtype.ext; exact shift_shift_reverse m.2

theorem target_norm_sq (a b : ℤ) (hab : a ≠ b) (g : H N) :
    ‖targetCoefficients a b g‖ ^ 2 = ‖sourceCoefficients b g‖ ^ 2 := by
  rw [norm_sq_tsum, norm_sq_tsum]
  simp only [targetCoefficients, sourceCoefficients, restrictL2_apply]
  change (∑' i : Donor N a, ‖g ((edgeEquiv a b hab) i).1‖ ^ 2) = _
  exact (edgeEquiv a b hab).tsum_eq (fun m => ‖g m.1‖ ^ 2)

theorem adjoint_norm_sq (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) (g : H N) :
    ‖(transfer a b α).adjoint g‖ ^ 2 = ‖g‖ ^ 2 - missing b g := by
  rw [transfer_adjoint_norm, target_norm_sq a b hab]
  linarith [support_partition b g]

/-- The first exact source identity, on the actual FOA1 operator. -/
theorem residual_identity (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase)
    (g : UnitCoefficients N) :
    ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2 =
      2 - missing a g.1 - 2 * affinity a b g.1 + 2 * defect a b α ζ g.1 := by
  rw [norm_sub_sq (𝕜 := ℂ), transfer_norm_sq, norm_smul, ζ.2, one_mul, g.2,
    inner_smul_right, ← inner_conj_symm (𝕜 := ℂ)]
  have hr := real_inner_eq_affinity_sub_defect a b α ζ g.1
  have he : (ζ.1 * conj ⟪g.1, transfer a b α g.1⟫_ℂ).re =
      (conj ζ.1 * ⟪g.1, transfer a b α g.1⟫_ℂ).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [RCLike.re_to_complex]
  rw [he, hr]; ring

/-- The adjoint has the same real overlap, with the conjugate target phase. -/
theorem adjoint_residual_identity (a b : ℤ) (hab : a ≠ b)
    (α : Donor N a → Phase) (ζ : Phase) (g : UnitCoefficients N) :
    ‖(transfer a b α).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 =
      2 - missing b g.1 - 2 * affinity a b g.1 + 2 * defect a b α ζ g.1 := by
  rw [norm_sub_sq (𝕜 := ℂ), adjoint_norm_sq a b hab, norm_smul, Complex.norm_conj, ζ.2,
    one_mul, g.2, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]
  simp only [RCLike.re_to_complex]
  rw [real_inner_eq_affinity_sub_defect]
  ring

theorem restrict_inject_disjoint {I J K : Type*} (f : I → K) (hf : Function.Injective f)
    (k : J → K) (hk : Function.Injective k) (h : ∀ i j, k j ≠ f i) :
    restrictL2 k hk ∘L (injectL2 f hf).toContinuousLinearMap = 0 := by
  apply ext_single
  intro i
  apply lp.ext
  funext j
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    injectL2_single, restrictL2_apply, zero_apply, lp.coeFn_zero,
    Pi.zero_apply]
  simp [lp.single_apply, Pi.single_eq_of_ne (h i j)]

theorem empty_transfer (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) (g : H N) :
    emptyCoefficients b (transfer a b α g) = 0 := by
  have hd := restrict_inject_disjoint (destination N a b) (destination_injective N a b)
    (Subtype.val : {m : Arr N // m.1 b = 0} → Arr N) Subtype.val_injective (by
      intro i j he
      have hi := donorOK_shift_receiver hab (m := i.1.1)
      change 1 ≤ (destination N a b i).1 b at hi
      rw [← he, j.2] at hi
      omega)
  exact congrArg (fun A : L2 (Donor N a) →L[ℂ] L2 {m : Arr N // m.1 b = 0} =>
    A (diagonal (fun m => (α m).1) 1 zero_le_one (fun m => (α m).2.le)
      (sourceCoefficients a g))) hd

theorem empty_adjoint (a b : ℤ) (α : Donor N a → Phase) (g : H N) :
    emptyCoefficients a ((transfer a b α).adjoint g) = 0 := by
  have hd := restrict_inject_disjoint (Subtype.val : Donor N a → Arr N) Subtype.val_injective
    (Subtype.val : {m : Arr N // m.1 a = 0} → Arr N) Subtype.val_injective (by
      intro i j he
      have hi : 1 ≤ i.1.1 a := i.2
      rw [← he, j.2] at hi
      omega)
  change restrictL2 _ _ ((transferOp N a b _ _).adjoint g) = 0
  simp only [transferOp, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
  simp only [restrictL2, ContinuousLinearMap.adjoint_adjoint]
  exact congrArg (fun A : L2 (Donor N a) →L[ℂ] L2 {m : Arr N // m.1 a = 0} =>
    A ((diagonal (fun m => (α m).1) 1 zero_le_one (fun m => (α m).2.le)).adjoint
      (targetCoefficients a b g))) hd

/-- Projecting the actual residual onto the missing receiver support. -/
theorem missing_receiver_le (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase)
    (ζ : Phase) (g : H N) :
    missing b g ≤ ‖transfer a b α g - ζ.1 • g‖ ^ 2 := by
  have he : emptyCoefficients b (transfer a b α g - ζ.1 • g) =
      -ζ.1 • emptyCoefficients b g := by
    change restrictL2 _ _ (_ - _) = _
    rw [map_sub, map_smul, show restrictL2 _ _ (transfer a b α g) = 0 from
      empty_transfer a b hab α g, zero_sub, neg_smul]
    rfl
  have h := restrictL2_norm_le (Subtype.val : {m : Arr N // m.1 b = 0} → Arr N)
    Subtype.val_injective (transfer a b α g - ζ.1 • g)
  change ‖emptyCoefficients b _‖ ≤ _ at h
  rw [he, norm_smul, norm_neg, ζ.2, one_mul] at h
  rw [missing_eq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem missing_donor_le (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase) (g : H N) :
    missing a g ≤ ‖(transfer a b α).adjoint g - conj ζ.1 • g‖ ^ 2 := by
  have he : emptyCoefficients a ((transfer a b α).adjoint g - conj ζ.1 • g) =
      -(conj ζ.1) • emptyCoefficients a g := by
    change restrictL2 _ _ (_ - _) = _
    rw [map_sub, map_smul, show restrictL2 _ _ ((transfer a b α).adjoint g) = 0 from
      empty_adjoint a b α g, zero_sub, neg_smul]
    rfl
  have h := restrictL2_norm_le (Subtype.val : {m : Arr N // m.1 a = 0} → Arr N)
    Subtype.val_injective ((transfer a b α).adjoint g - conj ζ.1 • g)
  change ‖emptyCoefficients a _‖ ≤ _ at h
  rw [he, norm_smul, norm_neg, Complex.norm_conj, ζ.2, one_mul] at h
  rw [missing_eq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The source's explicit estimates, with its factor 1/2 and unscaled D. -/
theorem affinity_defect_bounds (a b : ℤ) (α : Donor N a → Phase) (ζ : Phase)
    (g : UnitCoefficients N) :
    (0 ≤ 1 - affinity a b g.1 ∧
      1 - affinity a b g.1 ≤ (missing a g.1 + ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2) / 2) ∧
    (0 ≤ defect a b α ζ g.1 ∧
      defect a b α ζ g.1 ≤ (missing a g.1 + ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2) / 2) := by
  have hi := residual_identity a b α ζ g
  have hH := affinity_le_one a b g
  have hD := defect_nonneg a b α ζ g.1
  constructor <;> constructor <;> linarith

/-- A single pointwise estimate also supplies every uniform version: the
sum of squared residuals controls all four errors on any indexing set. -/
theorem all_errors_le (a b : ℤ) (hab : a ≠ b) (α : Donor N a → Phase) (ζ : Phase)
    (g : UnitCoefficients N) (ε : ℝ)
    (hε : ‖transfer a b α g.1 - ζ.1 • g.1‖ ^ 2 +
      ‖(transfer a b α).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 ≤ ε) :
    missing a g.1 ≤ ε ∧ missing b g.1 ≤ ε ∧
      |affinity a b g.1 - 1| ≤ ε / 2 ∧ |defect a b α ζ g.1| ≤ ε / 2 := by
  have ha := missing_donor_le a b α ζ g.1
  have hb := missing_receiver_le a b hab α ζ g.1
  have hh := affinity_defect_bounds a b α ζ g
  have h1 := sq_nonneg ‖transfer a b α g.1 - ζ.1 • g.1‖
  have h2 := sq_nonneg ‖(transfer a b α).adjoint g.1 - conj ζ.1 • g.1‖
  rw [abs_of_nonpos (by linarith [hh.1.1]), abs_of_nonneg hh.2.1]
  exact ⟨by linarith, by linarith, by linarith [hh.1.2], by linarith [hh.2.2]⟩

/-- The pointwise limit consequence permits varying sectors and all edge phases. -/
theorem residual_limits {I : Type*} (l : Filter I) (n : I → ℕ)
    (a b : ℤ) (hab : a ≠ b) (α : ∀ i, Donor (n i) a → Phase)
    (ζ : I → Phase) (g : ∀ i, UnitCoefficients (n i))
    (hW : Filter.Tendsto (fun i => ‖transfer a b (α i) (g i).1 - (ζ i).1 • (g i).1‖) l (nhds 0))
    (hA : Filter.Tendsto (fun i => ‖(transfer a b (α i)).adjoint (g i).1 -
      conj (ζ i).1 • (g i).1‖) l (nhds 0)) :
    Filter.Tendsto (fun i => missing a (g i).1) l (nhds 0) ∧
    Filter.Tendsto (fun i => missing b (g i).1) l (nhds 0) ∧
    Filter.Tendsto (fun i => affinity a b (g i).1) l (nhds 1) ∧
    Filter.Tendsto (fun i => defect a b (α i) (ζ i) (g i).1) l (nhds 0) := by
  have hw := hW.pow 2
  have ha := hA.pow 2
  simp only [zero_pow (by decide : 2 ≠ 0)] at hw ha
  have hs := hw.add ha
  simp only [zero_add] at hs
  have hh := hs.div_const 2
  simp only [zero_div] at hh
  have hb i := all_errors_le a b hab (α i) (ζ i) (g i) _ (le_refl _)
  refine ⟨squeeze_zero (fun i => missing_nonneg a (g i).1) (fun i => (hb i).1) hs,
    squeeze_zero (fun i => missing_nonneg b (g i).1) (fun i => (hb i).2.1) hs, ?_, ?_⟩
  · apply (tendsto_iff_norm_sub_tendsto_zero).mpr
    simpa only [Real.norm_eq_abs] using
      squeeze_zero (fun i => abs_nonneg (affinity a b (g i).1 - 1)) (fun i => (hb i).2.2.1) hh
  · exact squeeze_zero (fun i => defect_nonneg a b (α i) (ζ i) (g i).1)
      (fun i => (le_abs_self _).trans (hb i).2.2.2) hh

/-- Exact uniform epsilon control, with arbitrary parameter set and sector.
Applying this eventually for every epsilon proves the source uniform assertion. -/
theorem uniform_errors {I : Type*} (S : Set I) (n : I → ℕ)
    (a b : ℤ) (hab : a ≠ b) (α : ∀ i, Donor (n i) a → Phase)
    (ζ : I → Phase) (g : ∀ i, UnitCoefficients (n i)) (ε : ℝ)
    (h : ∀ i ∈ S, ‖transfer a b (α i) (g i).1 - (ζ i).1 • (g i).1‖ ^ 2 +
      ‖(transfer a b (α i)).adjoint (g i).1 - conj (ζ i).1 • (g i).1‖ ^ 2 ≤ ε) :
    ∀ i ∈ S, missing a (g i).1 ≤ ε ∧ missing b (g i).1 ≤ ε ∧
      |affinity a b (g i).1 - 1| ≤ ε / 2 ∧ |defect a b (α i) (ζ i) (g i).1| ≤ ε / 2 := by
  intro i hi
  exact all_errors_le a b hab (α i) (ζ i) (g i) ε (h i hi)

/-- UPT1 is the literal unit-edge specialization; no alternative shift is used. -/
theorem unitPhase_identity (a b : ℤ) (ζ : Phase) (g : UnitCoefficients N) :
    ‖UnitPhaseTransfer.auxiliary N a b g.1 - ζ.1 • g.1‖ ^ 2 =
      2 - missing a g.1 - 2 * affinity a b g.1 +
        2 * defect a b (fun _ => ⟨1, norm_one⟩) ζ g.1 := by
  simpa only [transfer_identity] using residual_identity a b (fun _ => ⟨1, norm_one⟩) ζ g

theorem unitPhase_adjoint_identity (a b : ℤ) (hab : a ≠ b) (ζ : Phase) (g : UnitCoefficients N) :
    ‖(UnitPhaseTransfer.auxiliary N a b).adjoint g.1 - conj ζ.1 • g.1‖ ^ 2 =
      2 - missing b g.1 - 2 * affinity a b g.1 +
        2 * defect a b (fun _ => ⟨1, norm_one⟩) ζ g.1 := by
  simpa only [transfer_identity] using adjoint_residual_identity a b hab (fun _ => ⟨1, norm_one⟩) ζ g

end QuantumNLS.ExactShiftResidual

#print axioms QuantumNLS.ExactShiftResidual.norm_sq_tsum
#print axioms QuantumNLS.ExactShiftResidual.summable_norm_sq
#print axioms QuantumNLS.ExactShiftResidual.ext_single
#print axioms QuantumNLS.ExactShiftResidual.emptyCoefficients
#print axioms QuantumNLS.ExactShiftResidual.missing
#print axioms QuantumNLS.ExactShiftResidual.missing_eq_norm
#print axioms QuantumNLS.ExactShiftResidual.missing_nonneg
#print axioms QuantumNLS.ExactShiftResidual.support_partition
#print axioms QuantumNLS.ExactShiftResidual.phase_diagonal_norm
#print axioms QuantumNLS.ExactShiftResidual.diagonal_adjoint
#print axioms QuantumNLS.ExactShiftResidual.transfer_norm_sq
#print axioms QuantumNLS.ExactShiftResidual.transfer_adjoint_norm
#print axioms QuantumNLS.ExactShiftResidual.edgeEquiv
#print axioms QuantumNLS.ExactShiftResidual.target_norm_sq
#print axioms QuantumNLS.ExactShiftResidual.adjoint_norm_sq
#print axioms QuantumNLS.ExactShiftResidual.residual_identity
#print axioms QuantumNLS.ExactShiftResidual.adjoint_residual_identity
#print axioms QuantumNLS.ExactShiftResidual.restrict_inject_disjoint
#print axioms QuantumNLS.ExactShiftResidual.empty_transfer
#print axioms QuantumNLS.ExactShiftResidual.empty_adjoint
#print axioms QuantumNLS.ExactShiftResidual.missing_receiver_le
#print axioms QuantumNLS.ExactShiftResidual.missing_donor_le
#print axioms QuantumNLS.ExactShiftResidual.affinity_defect_bounds
#print axioms QuantumNLS.ExactShiftResidual.all_errors_le
#print axioms QuantumNLS.ExactShiftResidual.residual_limits
#print axioms QuantumNLS.ExactShiftResidual.uniform_errors
#print axioms QuantumNLS.ExactShiftResidual.unitPhase_identity
#print axioms QuantumNLS.ExactShiftResidual.unitPhase_adjoint_identity

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.ExactShiftResidual.norm_sq_tsum,
    ``QuantumNLS.ExactShiftResidual.summable_norm_sq,
    ``QuantumNLS.ExactShiftResidual.ext_single,
    ``QuantumNLS.ExactShiftResidual.emptyCoefficients,
    ``QuantumNLS.ExactShiftResidual.missing,
    ``QuantumNLS.ExactShiftResidual.missing_eq_norm,
    ``QuantumNLS.ExactShiftResidual.missing_nonneg,
    ``QuantumNLS.ExactShiftResidual.support_partition,
    ``QuantumNLS.ExactShiftResidual.phase_diagonal_norm,
    ``QuantumNLS.ExactShiftResidual.diagonal_adjoint,
    ``QuantumNLS.ExactShiftResidual.transfer_norm_sq,
    ``QuantumNLS.ExactShiftResidual.transfer_adjoint_norm,
    ``QuantumNLS.ExactShiftResidual.edgeEquiv,
    ``QuantumNLS.ExactShiftResidual.target_norm_sq,
    ``QuantumNLS.ExactShiftResidual.adjoint_norm_sq,
    ``QuantumNLS.ExactShiftResidual.residual_identity,
    ``QuantumNLS.ExactShiftResidual.adjoint_residual_identity,
    ``QuantumNLS.ExactShiftResidual.restrict_inject_disjoint,
    ``QuantumNLS.ExactShiftResidual.empty_transfer,
    ``QuantumNLS.ExactShiftResidual.empty_adjoint,
    ``QuantumNLS.ExactShiftResidual.missing_receiver_le,
    ``QuantumNLS.ExactShiftResidual.missing_donor_le,
    ``QuantumNLS.ExactShiftResidual.affinity_defect_bounds,
    ``QuantumNLS.ExactShiftResidual.all_errors_le,
    ``QuantumNLS.ExactShiftResidual.residual_limits,
    ``QuantumNLS.ExactShiftResidual.uniform_errors,
    ``QuantumNLS.ExactShiftResidual.unitPhase_identity,
    ``QuantumNLS.ExactShiftResidual.unitPhase_adjoint_identity]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ExactShiftResidual." then
      pending := pending.push n
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
            throwError "Result nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.ExactShiftResidual.norm_sq_tsum,
    ``QuantumNLS.ExactShiftResidual.summable_norm_sq,
    ``QuantumNLS.ExactShiftResidual.ext_single,
    ``QuantumNLS.ExactShiftResidual.emptyCoefficients,
    ``QuantumNLS.ExactShiftResidual.missing,
    ``QuantumNLS.ExactShiftResidual.missing_eq_norm,
    ``QuantumNLS.ExactShiftResidual.missing_nonneg,
    ``QuantumNLS.ExactShiftResidual.support_partition,
    ``QuantumNLS.ExactShiftResidual.phase_diagonal_norm,
    ``QuantumNLS.ExactShiftResidual.diagonal_adjoint,
    ``QuantumNLS.ExactShiftResidual.transfer_norm_sq,
    ``QuantumNLS.ExactShiftResidual.transfer_adjoint_norm,
    ``QuantumNLS.ExactShiftResidual.edgeEquiv,
    ``QuantumNLS.ExactShiftResidual.target_norm_sq,
    ``QuantumNLS.ExactShiftResidual.adjoint_norm_sq,
    ``QuantumNLS.ExactShiftResidual.residual_identity,
    ``QuantumNLS.ExactShiftResidual.adjoint_residual_identity,
    ``QuantumNLS.ExactShiftResidual.restrict_inject_disjoint,
    ``QuantumNLS.ExactShiftResidual.empty_transfer,
    ``QuantumNLS.ExactShiftResidual.empty_adjoint,
    ``QuantumNLS.ExactShiftResidual.missing_receiver_le,
    ``QuantumNLS.ExactShiftResidual.missing_donor_le,
    ``QuantumNLS.ExactShiftResidual.affinity_defect_bounds,
    ``QuantumNLS.ExactShiftResidual.all_errors_le,
    ``QuantumNLS.ExactShiftResidual.residual_limits,
    ``QuantumNLS.ExactShiftResidual.uniform_errors,
    ``QuantumNLS.ExactShiftResidual.unitPhase_identity,
    ``QuantumNLS.ExactShiftResidual.unitPhase_adjoint_identity]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; {checked.size} generic constants independent of EXT-001. Concrete instantiations require its explicit Prop hypothesis only."
