import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.BetheSpectralCharges

/-! R-892D1666 / prop:transfer. DEF-048's normalizedTransfer is the
literal finite ordered-kernel operator, equal to transfer at κ/N. All
spectral assertions use the actual UBB1 basis and ACP1 without hypotheses.
Charge projections below are characteristic multipliers of the actual
rapidity power sums on the full Bethe coefficient space. -/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace QuantumNLS.BoundedBetheTransfer
open PhysicalTensor TensorCarrier KernelDefinition NormalizedTransfer NormalityBridge BetheLabels
local instance (p : Prop) : Decidable p := Classical.propDecidable p

section Diagonal
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) (a : ι → ℂ)

theorem adjoint_basis (h : ∀ i, T (b i) = a i • b i) (i : ι) :
    T.adjoint (b i) = conj (a i) • b i := by
  apply b.repr.injective
  ext j
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply,
    ContinuousLinearMap.adjoint_inner_right, h, inner_smul_left, inner_smul_right]
  by_cases hj : j = i
  · subst j; rfl
  · rw [b.orthonormal.inner_eq_zero hj, mul_zero, mul_zero]

theorem diagonal_coord (h : ∀ i, T (b i) = a i • b i) (f : E) (i : ι) :
    b.repr (T f) i = a i * b.repr f i := by
  rw [HilbertBasis.repr_apply_apply, ← ContinuousLinearMap.adjoint_inner_left,
    adjoint_basis b T a h, inner_smul_left, starRingEnd_self_apply,
    HilbertBasis.repr_apply_apply]

theorem diagonal_norm_le (h : ∀ i, T (b i) = a i • b i) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) : ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro f
  rw [← b.repr.norm_map (T f)]
  have hn : ‖b.repr (T f)‖ ≤ ‖(C : ℂ) • b.repr f‖ := by
    apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
    intro i
    rw [diagonal_coord b T a h, norm_mul, lp.coeFn_smul, Pi.smul_apply, norm_smul,
      Complex.norm_real, Real.norm_of_nonneg hC]
    exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _)
  simpa only [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC,
    b.repr.norm_map] using hn

/-- Full label masks, with no finite-support restriction. -/
def mask (s : Set ι) : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  classical
  let F : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun x => ⟨fun i => if i ∈ s then x i else 0,
        (lp.memℓp x).mono' (fun i => by split_ifs <;> simp)⟩
      map_add' := fun x y => by
        ext i
        change (if i ∈ s then x i + y i else 0) =
          (if i ∈ s then x i else 0) + (if i ∈ s then y i else 0)
        split_ifs <;> simp
      map_smul' := fun z x => by
        ext i
        change (if i ∈ s then z * x i else 0) = z * (if i ∈ s then x i else 0)
        split_ifs <;> simp }
  exact F.mkContinuous 1 (fun x => by
    simpa only [one_mul] using lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      (x := F x) (y := x) (fun i => by change ‖if i ∈ s then x i else 0‖ ≤ ‖x i‖; split_ifs <;> simp))

def projection (s : Set ι) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L mask s ∘L
    b.repr.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace E] in
theorem projection_coord (s : Set ι) (f : E) (i : ι) :
    b.repr (projection b s f) i = if i ∈ s then b.repr f i else 0 := by
  classical
  change b.repr (b.repr.symm (mask s (b.repr f))) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

omit [CompleteSpace E] in
theorem projection_basis (s : Set ι) (i : ι) :
    projection b s (b i) = (if i ∈ s then (1 : ℂ) else 0) • b i := by
  classical
  apply b.repr.injective
  ext j
  rw [projection_coord, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [b.repr_self]
  by_cases hj : j = i
  · subst j; simp
  · simp [lp.single_apply, hj]

omit [CompleteSpace E] in
theorem projection_fixed_iff (s : Set ι) (f : E) :
    projection b s f = f ↔ ∀ i, i ∉ s → b.repr f i = 0 := by
  constructor
  · intro h i hi
    have he := congrArg (fun x => b.repr x i) h
    rw [projection_coord, ite_eq_right hi] at he
    exact he.symm
  · intro h
    apply b.repr.injective
    ext i
    rw [projection_coord]
    split_ifs with hi
    · rfl
    · exact (h i hi).symm

theorem projection_selfAdjoint (s : Set ι) : (projection b s).adjoint = projection b s := by
  classical
  apply clm_ext_basis b
  intro i
  rw [adjoint_basis b _ _ (projection_basis b s), projection_basis]
  split_ifs <;> simp

omit [CompleteSpace E] in
theorem projection_idempotent (s : Set ι) : projection b s * projection b s = projection b s := by
  classical
  apply clm_ext_basis b
  intro i
  change projection b s (projection b s (b i)) = _
  rw [projection_basis, map_smul, projection_basis, smul_smul]
  split_ifs <;> simp

end Diagonal

variable (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 0 < N)

/-- DEF-048 is entire in operator norm, hence bounded at every z by its CLM type. -/
theorem entire : Differentiable ℂ (normalizedTransfer L κ N) :=
  differentiable_normalizedTransfer

theorem eigenrelation (z : ℂ) (m : MArr N) :
    normalizedTransfer L κ N z (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m) =
      eigen (L := L) κ hκ hN m z • UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ m :=
  UnconditionalBetheBasis.transfer_physicalBasis hκ hN z m

theorem spectral_formula (m : MArr N) (z : ℂ)
    (hz : ∀ j, z ≠ (BetheSpectralCharges.rapidity L N (κ / N) m j : ℂ)) :
    eigen (L := L) κ hκ hN m z =
      TransferSeparation.sFun L (κ / N) (BetheSpectralCharges.rapidity L N (κ / N) m) z :=
  BetheSpectralContinuity.spectralValue_nonpole L (cpos hκ hN) (label m).property z hz

theorem spectral_entire (m : MArr N) :
    Differentiable ℂ (eigen (L := L) κ hκ hN m) := eigen_differentiable κ hκ hN m

theorem spectral_root (m : MArr N) (i : Fin N) :
    eigen (L := L) κ hκ hN m (BetheSpectralCharges.rapidity L N (κ / N) m i) =
      deriv (BetheOnShell.numerator L (κ / N) (BetheSpectralCharges.rapidity L N (κ / N) m))
        (BetheSpectralCharges.rapidity L N (κ / N) m i) /
        ∏ j ∈ Finset.univ.erase i,
          ((BetheSpectralCharges.rapidity L N (κ / N) m i : ℂ) -
            BetheSpectralCharges.rapidity L N (κ / N) m j) :=
  BetheSpectralContinuity.spectralValue_root L (cpos hκ hN) (label m).property i

theorem diagonal (z : ℂ) : IsDiag (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
    (normalizedTransfer L κ N z) := fun m => ⟨_, eigenrelation L hκ hN z m⟩

include hκ hN in
theorem normal (z : ℂ) : Commute (normalizedTransfer L κ N z).adjoint
    (normalizedTransfer L κ N z) := (diagonal L hκ hN z).normal

include hκ hN in
theorem commute (z w : ℂ) : Commute (normalizedTransfer L κ N z)
    (normalizedTransfer L κ N w) := (diagonal L hκ hN z).commute (diagonal L hκ hN w)

include hκ hN in
theorem commute_adjoint (z w : ℂ) : Commute (normalizedTransfer L κ N z)
    (normalizedTransfer L κ N w).adjoint :=
  (diagonal L hκ hN z).commute (diagonal L hκ hN w).adjoint

include hκ hN in
theorem commute_adjoints (z w : ℂ) : Commute (normalizedTransfer L κ N z).adjoint
    (normalizedTransfer L κ N w).adjoint :=
  (diagonal L hκ hN z).adjoint.commute (diagonal L hκ hN w).adjoint

theorem commute_projection (z : ℂ) (s : Set (MArr N)) :
    Commute (normalizedTransfer L κ N z)
      (projection (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ) s) :=
  (diagonal L hκ hN z).commute (fun m => ⟨_, projection_basis _ _ m⟩)

/-- Spectral projection of the realized maximal rapidity-power charge. -/
def chargeProjection (r : ℕ) (s : Set ℝ) : physSector L N →L[ℂ] physSector L N :=
  projection (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
    {m | BetheSpectralCharges.eigenvalue L N (κ / N) r m ∈ s}

theorem chargeProjection_coord (r : ℕ) (s : Set ℝ) (f : physSector L N) (m : MArr N) :
    (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ).repr
      (chargeProjection L hκ hN r s f) m =
    if BetheSpectralCharges.eigenvalue L N (κ / N) r m ∈ s then
      (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ).repr f m else 0 :=
  projection_coord _ _ _ _

theorem chargeProjection_orthogonal (r : ℕ) (s : Set ℝ) :
    (chargeProjection L hκ hN r s).adjoint = chargeProjection L hκ hN r s ∧
    chargeProjection L hκ hN r s * chargeProjection L hκ hN r s = chargeProjection L hκ hN r s :=
  ⟨projection_selfAdjoint _ _, projection_idempotent _ _⟩

theorem commute_chargeProjection (z : ℂ) (r : ℕ) (s : Set ℝ) :
    Commute (normalizedTransfer L κ N z) (chargeProjection L hκ hN r s) :=
  (diagonal L hκ hN z).commute (fun m => ⟨_, projection_basis _ _ m⟩)

/-- Uniform upper half-plane scalar bound on the literal product formula. -/
theorem product_bound {M : ℕ} {c η : ℝ} (hc : 0 ≤ c) (hη : 0 < η)
    (q : Fin M → ℝ) (z : ℂ) (hz : z.im = η) :
    ‖TransferSeparation.sFun L c q z‖ ≤ 2 * (1 + c / η) ^ M := by
  have hd (j : Fin M) : η ≤ ‖z - (q j : ℂ)‖ := by
    have := Complex.abs_im_le_norm (z - (q j : ℂ))
    simpa [hz, abs_of_pos hη] using this
  have hfrac (j : Fin M) : ‖Complex.I * (c : ℂ) / (z - q j)‖ ≤ c / η := by
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hc]
    exact div_le_div_of_nonneg_left hc hη (hd j)
  have hp : ‖∏ j, (1 + Complex.I * (c : ℂ) / (z - q j))‖ ≤ (1 + c / η) ^ M := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _j : Fin M, (1 + c / η) := Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ =>
        (norm_add_le _ _).trans (by simpa using add_le_add_left (hfrac j) 1))
      _ = _ := by simp
  have hm : ‖∏ j, (1 - Complex.I * (c : ℂ) / (z - q j))‖ ≤ (1 + c / η) ^ M := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _j : Fin M, (1 + c / η) := Finset.prod_le_prod₀ (fun j _ => norm_nonneg _) (fun j _ =>
        (norm_sub_le _ _).trans (by simpa using add_le_add_left (hfrac j) 1))
      _ = _ := by simp
  have he : ‖Complex.exp (Complex.I * L * z)‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero, mul_zero, zero_add,
      zero_sub, hz]
    nlinarith [Fact.out (p := 0 < L)]
  unfold TransferSeparation.sFun
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ (1 + c / η) ^ M + 1 * (1 + c / η) ^ M :=
      add_le_add hp (by rw [norm_mul]; exact mul_le_mul he hm (norm_nonneg _) (by norm_num))
    _ = _ := by ring

include hκ hN in
theorem norm_bound (η : ℝ) (hη : 0 < η) (z : ℂ) (hz : z.im = η) :
    ‖normalizedTransfer L κ N z‖ ≤ 2 * (1 + κ / ((N : ℝ) * η)) ^ N := by
  apply diagonal_norm_le (UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ)
    _ _ (eigenrelation L hκ hN z) (by positivity)
  intro m
  have hn (j : Fin N) : z ≠ (BetheSpectralCharges.rapidity L N (κ / N) m j : ℂ) := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.ofReal_im, hz] at this
    linarith
  rw [spectral_formula L hκ hN m z hn]
  simpa only [div_div] using product_bound L (cpos hκ hN).le hη
    (BetheSpectralCharges.rapidity L N (κ / N) m) z hz

include hκ hN in
theorem exponential_bound (η : ℝ) (hη : 0 < η) :
    2 * (1 + κ / ((N : ℝ) * η)) ^ N ≤ 2 * Real.exp (κ / η) := by
  have h : 1 + κ / ((N : ℝ) * η) ≤ Real.exp (κ / ((N : ℝ) * η)) := by
    simpa only [add_comm] using Real.add_one_le_exp (κ / ((N : ℝ) * η))
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + κ / ((N : ℝ) * η)) h N
  rw [← Real.exp_nat_mul] at hp
  have he : (N : ℝ) * (κ / ((N : ℝ) * η)) = κ / η := by
    field_simp [Nat.ne_of_gt hN]
  rw [he] at hp
  exact mul_le_mul_of_nonneg_left hp (by norm_num)

include hκ hN in
theorem transfer_consequences :
    Differentiable ℂ (normalizedTransfer L κ N) ∧
    (∀ z, Commute (normalizedTransfer L κ N z).adjoint (normalizedTransfer L κ N z) ∧
      (∀ w, Commute (normalizedTransfer L κ N z) (normalizedTransfer L κ N w) ∧
        Commute (normalizedTransfer L κ N z) (normalizedTransfer L κ N w).adjoint) ∧
      ∀ r s, Commute (normalizedTransfer L κ N z) (chargeProjection L hκ hN r s)) ∧
    ∀ η, 0 < η → ∀ z, z.im = η →
      ‖normalizedTransfer L κ N z‖ ≤ 2 * (1 + κ / ((N : ℝ) * η)) ^ N ∧
      2 * (1 + κ / ((N : ℝ) * η)) ^ N ≤ 2 * Real.exp (κ / η) :=
  ⟨entire L, fun z => ⟨normal L hκ hN z,
    fun w => ⟨commute L hκ hN z w, commute_adjoint L hκ hN z w⟩,
    commute_chargeProjection L hκ hN z⟩,
    fun η hη z hz => ⟨norm_bound L hκ hN η hη z hz, exponential_bound hκ hN η hη⟩⟩

include hN in
/-- Exact identification for EVERY fixed positive c: κ=cN. -/
theorem fixed_c (c : ℝ) (_hc : 0 < c) (z : ℂ) :
    normalizedTransfer L (c * N) N z = BethePhysicalTransfer.transfer L N c z := by
  rw [normalizedTransfer_eq_transfer]
  congr 1
  exact mul_div_cancel_right₀ c (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))

include hN in
theorem fixed_c_entire (c : ℝ) (hc : 0 < c) :
    Differentiable ℂ (BethePhysicalTransfer.transfer L N c) := by
  have hf : BethePhysicalTransfer.transfer L N c = normalizedTransfer L (c * N) N :=
    funext (fun z => (fixed_c L hN c hc z).symm)
  rw [hf]
  exact entire L

include hN in
theorem fixed_c_eigenrelation (c : ℝ) (hc : 0 < c) (z : ℂ) (m : MArr N) :
    BethePhysicalTransfer.transfer L N c z (UnconditionalBetheBasis.physicalBasis L N hN c hc m) =
      BetheSpectralContinuity.spectralValue L hc (label m).property z •
        UnconditionalBetheBasis.physicalBasis L N hN c hc m := by
  have he := eigenrelation L (mul_pos hc (Nat.cast_pos.mpr hN)) hN z m
  rw [fixed_c L hN c hc z] at he
  have hdiv : c * (N : ℝ) / N = c := mul_div_cancel_right₀ c (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))
  simpa only [UnconditionalBetheBasis.meanField_physicalBasis,
    BetheConditionalBasis.meanField_physicalBasis, UnconditionalBetheBasis.physicalBasis,
    eigen, hdiv] using he

include hN in
theorem fixed_c_joint (c : ℝ) (hc : 0 < c) (z w : ℂ) :
    Commute (BethePhysicalTransfer.transfer L N c z).adjoint (BethePhysicalTransfer.transfer L N c z) ∧
    Commute (BethePhysicalTransfer.transfer L N c z) (BethePhysicalTransfer.transfer L N c w) ∧
    Commute (BethePhysicalTransfer.transfer L N c z) (BethePhysicalTransfer.transfer L N c w).adjoint := by
  rw [← fixed_c L hN c hc z, ← fixed_c L hN c hc w]
  exact ⟨normal L (mul_pos hc (Nat.cast_pos.mpr hN)) hN z,
    commute L (mul_pos hc (Nat.cast_pos.mpr hN)) hN z w,
    commute_adjoint L (mul_pos hc (Nat.cast_pos.mpr hN)) hN z w⟩

include hN in
theorem fixed_c_projection (c : ℝ) (hc : 0 < c) (z : ℂ) (s : Set (MArr N)) :
    Commute (BethePhysicalTransfer.transfer L N c z)
      (projection (UnconditionalBetheBasis.physicalBasis L N hN c hc) s) := by
  have hd : IsDiag (UnconditionalBetheBasis.physicalBasis L N hN c hc)
      (BethePhysicalTransfer.transfer L N c z) :=
    fun m => ⟨_, fixed_c_eigenrelation L hN c hc z m⟩
  exact hd.commute (fun m => ⟨_, projection_basis _ _ m⟩)

end QuantumNLS.BoundedBetheTransfer

#print axioms QuantumNLS.BoundedBetheTransfer.adjoint_basis
#print axioms QuantumNLS.BoundedBetheTransfer.diagonal_coord
#print axioms QuantumNLS.BoundedBetheTransfer.diagonal_norm_le
#print axioms QuantumNLS.BoundedBetheTransfer.mask
#print axioms QuantumNLS.BoundedBetheTransfer.projection
#print axioms QuantumNLS.BoundedBetheTransfer.projection_coord
#print axioms QuantumNLS.BoundedBetheTransfer.projection_basis
#print axioms QuantumNLS.BoundedBetheTransfer.projection_fixed_iff
#print axioms QuantumNLS.BoundedBetheTransfer.projection_selfAdjoint
#print axioms QuantumNLS.BoundedBetheTransfer.projection_idempotent
#print axioms QuantumNLS.BoundedBetheTransfer.entire
#print axioms QuantumNLS.BoundedBetheTransfer.eigenrelation
#print axioms QuantumNLS.BoundedBetheTransfer.spectral_formula
#print axioms QuantumNLS.BoundedBetheTransfer.spectral_entire
#print axioms QuantumNLS.BoundedBetheTransfer.spectral_root
#print axioms QuantumNLS.BoundedBetheTransfer.diagonal
#print axioms QuantumNLS.BoundedBetheTransfer.normal
#print axioms QuantumNLS.BoundedBetheTransfer.commute
#print axioms QuantumNLS.BoundedBetheTransfer.commute_adjoint
#print axioms QuantumNLS.BoundedBetheTransfer.commute_adjoints
#print axioms QuantumNLS.BoundedBetheTransfer.commute_projection
#print axioms QuantumNLS.BoundedBetheTransfer.chargeProjection
#print axioms QuantumNLS.BoundedBetheTransfer.chargeProjection_coord
#print axioms QuantumNLS.BoundedBetheTransfer.chargeProjection_orthogonal
#print axioms QuantumNLS.BoundedBetheTransfer.commute_chargeProjection
#print axioms QuantumNLS.BoundedBetheTransfer.product_bound
#print axioms QuantumNLS.BoundedBetheTransfer.norm_bound
#print axioms QuantumNLS.BoundedBetheTransfer.exponential_bound
#print axioms QuantumNLS.BoundedBetheTransfer.transfer_consequences
#print axioms QuantumNLS.BoundedBetheTransfer.fixed_c
#print axioms QuantumNLS.BoundedBetheTransfer.fixed_c_entire
#print axioms QuantumNLS.BoundedBetheTransfer.fixed_c_eigenrelation
#print axioms QuantumNLS.BoundedBetheTransfer.fixed_c_joint
#print axioms QuantumNLS.BoundedBetheTransfer.fixed_c_projection

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.BoundedBetheTransfer.adjoint_basis,
    ``QuantumNLS.BoundedBetheTransfer.diagonal_coord,
    ``QuantumNLS.BoundedBetheTransfer.diagonal_norm_le,
    ``QuantumNLS.BoundedBetheTransfer.mask,
    ``QuantumNLS.BoundedBetheTransfer.projection,
    ``QuantumNLS.BoundedBetheTransfer.projection_coord,
    ``QuantumNLS.BoundedBetheTransfer.projection_basis,
    ``QuantumNLS.BoundedBetheTransfer.projection_fixed_iff,
    ``QuantumNLS.BoundedBetheTransfer.projection_selfAdjoint,
    ``QuantumNLS.BoundedBetheTransfer.projection_idempotent,
    ``QuantumNLS.BoundedBetheTransfer.entire,
    ``QuantumNLS.BoundedBetheTransfer.eigenrelation,
    ``QuantumNLS.BoundedBetheTransfer.spectral_formula,
    ``QuantumNLS.BoundedBetheTransfer.spectral_entire,
    ``QuantumNLS.BoundedBetheTransfer.spectral_root,
    ``QuantumNLS.BoundedBetheTransfer.diagonal,
    ``QuantumNLS.BoundedBetheTransfer.normal,
    ``QuantumNLS.BoundedBetheTransfer.commute,
    ``QuantumNLS.BoundedBetheTransfer.commute_adjoint,
    ``QuantumNLS.BoundedBetheTransfer.commute_adjoints,
    ``QuantumNLS.BoundedBetheTransfer.commute_projection,
    ``QuantumNLS.BoundedBetheTransfer.chargeProjection,
    ``QuantumNLS.BoundedBetheTransfer.chargeProjection_coord,
    ``QuantumNLS.BoundedBetheTransfer.chargeProjection_orthogonal,
    ``QuantumNLS.BoundedBetheTransfer.commute_chargeProjection,
    ``QuantumNLS.BoundedBetheTransfer.product_bound,
    ``QuantumNLS.BoundedBetheTransfer.norm_bound,
    ``QuantumNLS.BoundedBetheTransfer.exponential_bound,
    ``QuantumNLS.BoundedBetheTransfer.transfer_consequences,
    ``QuantumNLS.BoundedBetheTransfer.fixed_c,
    ``QuantumNLS.BoundedBetheTransfer.fixed_c_entire,
    ``QuantumNLS.BoundedBetheTransfer.fixed_c_eigenrelation,
    ``QuantumNLS.BoundedBetheTransfer.fixed_c_joint,
    ``QuantumNLS.BoundedBetheTransfer.fixed_c_projection]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.BoundedBetheTransfer." then
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
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; all own and generated constants standard-only; ACP1 supplies proved continuity, no hcont premise."
