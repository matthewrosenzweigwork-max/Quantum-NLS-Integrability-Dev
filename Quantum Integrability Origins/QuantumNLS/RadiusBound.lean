import QuantumNLS.LocalPlacement

/-!
# DEF-050: radius bound for a chosen kernel expansion

Source (ledger DEF-050, `DEFINITIONS_LEDGER.md:1223`; canonical occurrence
`source/chapters/local/quantum_periods.tex:32-42`, `def:local-kernel-radius-bound`; prerequisites
DEF-009, DEF-017, DEF-041):
"An expansion of a sector operator is a specified list `(A_{p,N})_{0≤p≤N}` with
`A_N = Σ_p Q_{N,p}(A_{p,N})`. For `R ≥ 1`, its radius bound is `Σ_p R^p ‖A_{p,N}‖`. This is a norm on
the specified list of kernels; no uniqueness of expansions of the same operator is asserted."
The chapter adds: "In particular `‖A_N‖ ≤ ‖(A_{p,N})‖_R`."

Realization (all imports frozen and read-only):
* kernels: `KernelDefinition.BoundedSymmetricKernel H p = L(Sym^p H)` (generic complex Hilbert `H`);
  the list type is Luna's `LocalPlacement.KernelList N = (p : Fin (N+1)) → L(Sym^p H)`;
* `Q N p hp A`: DEF-041's realized `TensorPlacements.Q_N_p` (binomial subset average on
  `Sym^{p+(N−p)}`), transported to `Sym^N` along `p + (N − p) = N`
  (`KernelDefinition.castSymSectorOperator`); `Q_eq_genericU_N_r` identifies it with DEF-009's
  realized `genericU_N_r` (the sandwich `P_N(A ⊗ 1)P_N`);
* `IsExpansion A_N (A_p)`: `A_N = Σ_p Q_{N,p}(A_{p,N})`; `represented` is that sum;
* `radiusBound R (A_p) = Σ_p R^p ‖A_{p,N}‖` (equal to Luna's `LocalPlacement.radiusBound`);
* the norm: `radiusNorm R` is an `AddGroupNorm` on the list space, `radiusSeminorm R` the same
  function as a `Seminorm ℂ` (absolute homogeneity); together with `radiusBound_eq_zero_iff`
  this is a norm on the list space (for `R ≥ 1`; positivity of `R` suffices).
* `norm_represented_le`: `‖A_N‖ ≤ ‖(A_{p,N})‖_R` for every expansion and `R ≥ 1`;
  `radiusBound_mono`: the bound is nondecreasing in `R ≥ 1`.

No uniqueness of expansions is asserted or used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.LocalPlacement

namespace QuantumNLS.RadiusBound

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. The placement operators `Q_{N,p}` at a literal total particle number -/

/-- DEF-041's `Q_{N,p}` on `Sym^N H`: the realized `Q_N_p` transported along `p + (N−p) = N`. -/
def Q (N p : ℕ) (hp : p ≤ N) (A : BoundedSymmetricKernel H p) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  castSymSectorOperator (Nat.add_sub_of_le hp) (Q_N_p (q := N - p) A)

/-- `Q_{N,p}` is DEF-009's realized `U_{N,p}` (`P_N(A ⊗ 1)P_N`). -/
theorem Q_eq_genericU_N_r (N p : ℕ) (hp : p ≤ N) (A : BoundedSymmetricKernel H p) :
    Q N p hp A = genericU_N_r N p hp A := by
  unfold Q genericU_N_r
  rw [U_N_r_eq_Q_N_p]

/-- `‖Q_{N,p}(A)‖ ≤ ‖A‖`. -/
theorem norm_Q_le (N p : ℕ) (hp : p ≤ N) (A : BoundedSymmetricKernel H p) :
    ‖Q N p hp A‖ ≤ ‖A‖ := by
  rw [Q, norm_castSymSectorOperator]; exact norm_Q_N_p_le A

/-! ## 2. Expansions -/

/-- The operator `Σ_{p=0}^N Q_{N,p}(A_{p,N})` represented by a kernel list. -/
def represented {N : ℕ} (A : KernelList (H := H) N) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  ∑ p : Fin (N + 1), Q N p.1 (Nat.lt_succ_iff.mp p.2) (A p)

/-- **DEF-050**: `(A_{p,N})` is an expansion of the sector operator `A_N`. -/
def IsExpansion {N : ℕ} (AN : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (A : KernelList (H := H) N) : Prop :=
  AN = represented A

/-- The represented operator agrees with Luna's `LocalPlacement.representedOperator`
(DEF-009 form). -/
theorem represented_eq_representedOperator {N : ℕ} (A : KernelList (H := H) N) :
    represented A = representedOperator A := by
  unfold represented representedOperator
  exact Finset.sum_congr rfl fun p _ => Q_eq_genericU_N_r _ _ _ _

/-- A chosen expansion of LocalPlacement is an expansion in the sense of DEF-050. -/
theorem chosenExpansion_isExpansion {N : ℕ} (A : ChosenExpansion (H := H) N) :
    IsExpansion A.operator A.kernels := by
  unfold IsExpansion; rw [represented_eq_representedOperator]; exact A.represents

/-- **DEF-050**: the radius bound `‖(A_{p,N})‖_R = Σ_p R^p ‖A_{p,N}‖`. -/
def radiusBound {N : ℕ} (R : ℝ) (A : KernelList (H := H) N) : ℝ :=
  ∑ p : Fin (N + 1), R ^ p.1 * ‖A p‖

theorem radiusBound_eq_local {N : ℕ} (R : ℝ) (A : ChosenExpansion (H := H) N) :
    radiusBound R A.kernels = LocalPlacement.radiusBound A R := rfl

/-! ## 3. The radius bound is a norm on the list of kernels -/

variable {N : ℕ}

theorem radiusBound_nonneg {R : ℝ} (hR : 0 ≤ R) (A : KernelList (H := H) N) :
    0 ≤ radiusBound R A :=
  Finset.sum_nonneg fun p _ => mul_nonneg (pow_nonneg hR _)
    (norm_nonneg (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))

theorem radiusBound_zero (R : ℝ) : radiusBound R (0 : KernelList (H := H) N) = 0 := by
  unfold radiusBound
  refine Finset.sum_eq_zero fun p _ => ?_
  exact mul_eq_zero_of_right _ (norm_zero (E := SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))

theorem radiusBound_add {R : ℝ} (hR : 0 ≤ R) (A B : KernelList (H := H) N) :
    radiusBound R (A + B) ≤ radiusBound R A + radiusBound R B := by
  unfold radiusBound
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [← mul_add]
  have : ((A + B) p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1) =
      (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1) + B p := rfl
  rw [this]
  exact mul_le_mul_of_nonneg_left
    (norm_add_le (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1) (B p)) (pow_nonneg hR _)

theorem radiusBound_neg (R : ℝ) (A : KernelList (H := H) N) :
    radiusBound R (-A) = radiusBound R A := by
  unfold radiusBound
  refine Finset.sum_congr rfl fun p _ => ?_
  exact congrArg (R ^ p.1 * ·) (norm_neg (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))

omit [CompleteSpace H] in
/-- `‖c • f‖ = ‖c‖ ‖f‖` for sector operators (from the two operator-norm inequalities). -/
theorem norm_smul_kernel {p : ℕ} (c : ℂ) (f : SymSector ℂ H p →L[ℂ] SymSector ℂ H p) :
    ‖c • f‖ = ‖c‖ * ‖f‖ := by
  refine le_antisymm (ContinuousLinearMap.opNorm_smul_le c f) ?_
  by_cases hc : c = 0
  · subst hc; simp only [norm_zero, zero_mul]; exact norm_nonneg (0 • f)
  · have h1 := ContinuousLinearMap.opNorm_smul_le c⁻¹ (c • f)
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul, norm_inv] at h1
    have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
    calc ‖c‖ * ‖f‖ ≤ ‖c‖ * (‖c‖⁻¹ * ‖c • f‖) := mul_le_mul_of_nonneg_left h1 hc0.le
      _ = ‖c • f‖ := by field_simp

theorem radiusBound_smul (R : ℝ) (c : ℂ) (A : KernelList (H := H) N) :
    radiusBound R (c • A) = ‖c‖ * radiusBound R A := by
  unfold radiusBound
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have h := norm_smul_kernel c (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1)
  calc R ^ p.1 * ‖(c • A) p‖ = R ^ p.1 * (‖c‖ * ‖(A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1)‖) :=
        congrArg (R ^ p.1 * ·) h
    _ = _ := by ring

theorem radiusBound_eq_zero_iff {R : ℝ} (hR : 0 < R) (A : KernelList (H := H) N) :
    radiusBound R A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
      mul_nonneg (pow_nonneg hR.le p.1)
        (norm_nonneg (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1)))).mp h
    funext p
    have := h0 p (Finset.mem_univ _)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (pow_ne_zero _ hR.ne')
    · exact (norm_eq_zero (a := (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))).mp h1
  · rintro rfl; exact radiusBound_zero R

/-- The radius bound as an additive group norm (`R > 0`, in particular `R ≥ 1`). -/
def radiusNorm (R : ℝ) (hR : 0 < R) : AddGroupNorm (KernelList (H := H) N) where
  toFun := radiusBound R
  map_zero' := radiusBound_zero R
  add_le' := radiusBound_add hR.le
  neg' := radiusBound_neg R
  eq_zero_of_map_eq_zero' A h := (radiusBound_eq_zero_iff hR A).mp h

/-- The radius bound as a seminorm over `ℂ` (absolute homogeneity). -/
def radiusSeminorm (R : ℝ) (hR : 0 ≤ R) : Seminorm ℂ (KernelList (H := H) N) where
  toFun := radiusBound R
  map_zero' := radiusBound_zero R
  add_le' := radiusBound_add hR
  neg' := radiusBound_neg R
  smul' c A := radiusBound_smul R c A

/-! ## 4. Consequences stated with the definition -/

/-- **`‖A_N‖ ≤ ‖(A_{p,N})‖_R`** for every expansion and every `R ≥ 1`. -/
theorem norm_le_radiusBound {R : ℝ} (hR : 1 ≤ R) {AN : SymSector ℂ H N →L[ℂ] SymSector ℂ H N}
    {A : KernelList (H := H) N} (h : IsExpansion AN A) : ‖AN‖ ≤ radiusBound R A := by
  rw [h, represented]
  refine (norm_sum_le Finset.univ (fun p : Fin (N + 1) =>
    Q N p.1 (Nat.lt_succ_iff.mp p.2) (A p))).trans (Finset.sum_le_sum fun p _ => ?_)
  calc ‖Q N p.1 (Nat.lt_succ_iff.mp p.2) (A p)‖ ≤ ‖A p‖ := norm_Q_le _ _ _ _
    _ = 1 * ‖A p‖ := (one_mul _).symm
    _ ≤ R ^ p.1 * ‖A p‖ := mul_le_mul_of_nonneg_right (one_le_pow₀ hR)
        (norm_nonneg (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))

/-- The radius bound is nondecreasing in `R ≥ 0`. -/
theorem radiusBound_mono {R R' : ℝ} (hR : 0 ≤ R) (hRR' : R ≤ R') (A : KernelList (H := H) N) :
    radiusBound R A ≤ radiusBound R' A :=
  Finset.sum_le_sum fun p _ =>
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hR hRR' _)
      (norm_nonneg (A p : SymSector ℂ H p.1 →L[ℂ] SymSector ℂ H p.1))

/-! Kernel axiom audit (checkpoint RB1). -/
#print axioms Q_eq_genericU_N_r
#print axioms norm_Q_le
#print axioms represented_eq_representedOperator
#print axioms chosenExpansion_isExpansion
#print axioms radiusBound_eq_local
#print axioms radiusBound_nonneg
#print axioms radiusBound_zero
#print axioms radiusBound_add
#print axioms radiusBound_neg
#print axioms norm_smul_kernel
#print axioms radiusBound_smul
#print axioms radiusBound_eq_zero_iff
#print axioms radiusNorm
#print axioms radiusSeminorm
#print axioms norm_le_radiusBound
#print axioms radiusBound_mono

end QuantumNLS.RadiusBound
