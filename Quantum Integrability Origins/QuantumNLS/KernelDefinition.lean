/-
QuantumNLS.KernelDefinition — the bounded symmetric-kernel carrier and the
normalized placement in DEF-009.

Source: source-text/chapters/definitions.tex:55 (DEF-009), with the concrete
completed-tensor and symmetric-sector constructions from TensorCarrier and
TensorPlacements.  The source writes P_N (A ⊗ 1) P_N and identifies it with
the distinct-coordinate average.  This file proves that identification on
the symmetric N-sector, where the operator acts.

The product-symbol clause is a kernel pairing.  For a non-unit profile, the
expectation on an N-fold product vector also contains the norm of the q
spectator factors; no unit-mass limiting measure or convergence assertion is
part of DEF-009.  `ProductPreparation` remains frozen and is not imported:
its `fullMassMeasure` continues to take `unitLimit` as an explicit input.
The generic placement admits degree zero as a useful extension for DEF-041;
the DEF-009 source scope itself has positive degree.
-/
import QuantumNLS.PhysicalPlacements

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.PhysicalTensor

noncomputable section

namespace QuantumNLS.KernelDefinition

/-- The actual DEF-009 carrier: bounded operators on the symmetric r-particle
Hilbert sector, with its operator-norm topology. -/
abbrev BoundedSymmetricKernel (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (r : ℕ) :=
  SymSector ℂ H r →L[ℂ] SymSector ℂ H r

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `A` extended by zero from `Sym^r H` to the completed full tensor power.
This is the concrete zero-extension from TensorPlacements. -/
abbrev zeroExtendKernel {r : ℕ} (A : BoundedSymmetricKernel H r) :=
  extendSymKernel A

/-- The literal DEF-009 operator on the ambient completed tensor power:
`P_{r+q} (A ⊗ 1) P_{r+q}`.  `firstPlacement` is the completed-tensor map
`A ⊗ 1`, with `A` first extended by zero. -/
def sandwichPlacement {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    HilbertTensorPower ℂ H (r + q) →L[ℂ] HilbertTensorPower ℂ H (r + q) :=
  (symProj ℂ H (r + q)).comp
    ((firstPlacement (q := q) A).comp (symProj ℂ H (r + q)))

/-- The DEF-009 operator, with both domain and codomain the symmetric
`(r+q)`-particle sector. -/
def U_N_r {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    SymSector ℂ H (r + q) →L[ℂ] SymSector ℂ H (r + q) :=
  ((sandwichPlacement A).comp (SymSector ℂ H (r + q)).subtypeL).codRestrict
    (SymSector ℂ H (r + q)) (by
      intro x
      change symProj ℂ H (r + q) _ ∈ SymSector ℂ H (r + q)
      rw [symProj_eq_starProjection]
      exact Submodule.starProjection_apply_mem _ _)

/-- The restricted source definition is literally the projection sandwich on
the completed tensor power, with the symmetric sector as both endpoints. -/
theorem U_N_r_eq_sandwich {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    U_N_r (r := r) (q := q) A =
      ((sandwichPlacement (r := r) (q := q) A).comp
        (SymSector ℂ H (r + q)).subtypeL).codRestrict
        (SymSector ℂ H (r + q)) (by
          intro x
          change symProj ℂ H (r + q) _ ∈ SymSector ℂ H (r + q)
          rw [symProj_eq_starProjection]
          exact Submodule.starProjection_apply_mem _ _) := rfl

/-- On a symmetric input, the symmetrized placement is just `P_N(A ⊗ 1)`.
This is the key compression identity behind the source definition. -/
theorem symmetrizedPlacement_apply_symmetric {r q : ℕ}
    (A : BoundedSymmetricKernel H r) (x : SymSector ℂ H (r + q)) :
    symmetrizedPlacement (q := q) A x.1 =
      symProj ℂ H (r + q) (firstPlacement (q := q) A x.1) := by
  have hx (σ : Equiv.Perm (Fin (r + q))) :
      (permRep ℂ H (r + q) σ⁻¹ :
        HilbertTensorPower ℂ H (r + q) →L[ℂ] HilbertTensorPower ℂ H (r + q)) x.1 = x.1 :=
    x.property σ⁻¹
  have hterm (σ : Equiv.Perm (Fin (r + q))) :
      permutedPlacement σ A x.1 =
        (permRep ℂ H (r + q) σ :
          HilbertTensorPower ℂ H (r + q) →L[ℂ] HilbertTensorPower ℂ H (r + q))
          (firstPlacement (q := q) A x.1) := by
    change (permRep ℂ H (r + q) σ :
        HilbertTensorPower ℂ H (r + q) →L[ℂ] HilbertTensorPower ℂ H (r + q))
        (firstPlacement (q := q) A
          ((permRep ℂ H (r + q) σ⁻¹ :
            HilbertTensorPower ℂ H (r + q) →L[ℂ] HilbertTensorPower ℂ H (r + q)) x.1))
        =
        (permRep ℂ H (r + q) σ :
          HilbertTensorPower ℂ H (r + q) →L[ℂ] HilbertTensorPower ℂ H (r + q))
          (firstPlacement (q := q) A x.1)
    rw [hx σ]
  calc
    symmetrizedPlacement (q := q) A x.1 =
        ((Fintype.card (Equiv.Perm (Fin (r + q))) : ℂ)⁻¹) •
          ∑ σ : Equiv.Perm (Fin (r + q)),
            (permRep ℂ H (r + q) σ :
              HilbertTensorPower ℂ H (r + q) →L[ℂ] _)
              (firstPlacement (q := q) A x.1) := by
          simp only [symmetrizedPlacement, smul_apply, sum_apply]
          congr 1
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hterm σ
    _ = symProj ℂ H (r + q) (firstPlacement (q := q) A x.1) := by
          rw [symProj_eq_factorial_average]
          simp [Fintype.card_perm, Fintype.card_fin]

/-- The source sandwich restricted to the symmetric sector equals the
permutation-average realization `Q_N_p`. -/
theorem U_N_r_eq_Q_N_p {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    U_N_r A = Q_N_p (q := q) A := by
  ext x
  change sandwichPlacement (r := r) (q := q) A x.1 =
    symmetrizedPlacement (q := q) A x.1
  rw [sandwichPlacement, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  have hPx : symProj ℂ H (r + q) x.1 = x.1 := by
    change groupAverage (permRep ℂ H (r + q)) x.1 = x.1
    exact groupAverage_apply_of_mem (permRep ℂ H (r + q)) x.property
  rw [hPx]
  exact (symmetrizedPlacement_apply_symmetric A x).symm

/-- Exact source normalization: the DEF-009 sandwich is the reciprocal
binomial average over all distinct r-element coordinate subsets. -/
theorem U_N_r_eq_subsetPlacementAverage {r q : ℕ}
    (A : BoundedSymmetricKernel H r) :
    U_N_r A =
      ((subsetPlacementAverage (q := q) A).comp
        (SymSector ℂ H (r + q)).subtypeL).codRestrict
        (SymSector ℂ H (r + q)) (subsetPlacementAverage_apply_mem A) := by
  rw [U_N_r_eq_Q_N_p]
  exact Q_N_p_eq_subsetPlacementAverage A

/-- The bounded-kernel norm contract is inherited by the literal DEF-009
operator. -/
theorem norm_U_N_r_le {r q : ℕ} (A : BoundedSymmetricKernel H r) :
    ‖U_N_r (r := r) (q := q) A‖ ≤ ‖A‖ := by
  rw [U_N_r_eq_Q_N_p (r := r) (q := q)]
  exact norm_Q_N_p_le A

/-- Transport a symmetric sector operator along an equality of particle
counts. -/
def castSymSectorOperator {m n : ℕ} (h : m = n)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    SymSector ℂ H n →L[ℂ] SymSector ℂ H n := by
  cases h
  exact A

/-- The DEF-009 operator with a literal total particle number `N`, using the
canonical split `r + (N-r) = N`. -/
def genericU_N_r (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  castSymSectorOperator (Nat.add_sub_of_le hr)
    (U_N_r (r := r) (q := N - r) A)

/-- At a literal total particle number, `genericU_N_r` is still the source
projection sandwich, transported only along `r+(N-r)=N`. -/
theorem genericU_N_r_eq_sandwich (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    genericU_N_r N r hr A =
      castSymSectorOperator (Nat.add_sub_of_le hr)
        (((sandwichPlacement (r := r) (q := N - r) A).comp
          (SymSector ℂ H (r + (N - r))).subtypeL).codRestrict
            (SymSector ℂ H (r + (N - r))) (by
              intro x
              change symProj ℂ H (r + (N - r)) _ ∈
                SymSector ℂ H (r + (N - r))
              rw [symProj_eq_starProjection]
              exact Submodule.starProjection_apply_mem _ _)) := by
  unfold genericU_N_r
  exact congrArg (castSymSectorOperator (Nat.add_sub_of_le hr))
    (U_N_r_eq_sandwich (r := r) (q := N - r) A)

/-- The literal reciprocal-binomial average transported to the source's
total particle count `N`. -/
def genericSubsetPlacementAverage (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  castSymSectorOperator (Nat.add_sub_of_le hr)
    (((subsetPlacementAverage (q := N - r) A).comp
      (SymSector ℂ H (r + (N - r))).subtypeL).codRestrict
        (SymSector ℂ H (r + (N - r))) (subsetPlacementAverage_apply_mem A))

/-- Exact DEF-009 normalization at an arbitrary total particle number: the
source sandwich is the binomial-normalized sum over distinct coordinate
subsets, transported along `r+(N-r)=N`. -/
theorem genericU_N_r_eq_subsetPlacementAverage (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    genericU_N_r N r hr A = genericSubsetPlacementAverage N r hr A := by
  unfold genericU_N_r genericSubsetPlacementAverage
  exact congrArg (castSymSectorOperator (Nat.add_sub_of_le hr))
    (U_N_r_eq_subsetPlacementAverage (r := r) (q := N - r) A)

/-- Casting to a different particle-count index preserves operator norm. -/
theorem norm_castSymSectorOperator {m n : ℕ} (h : m = n)
    (A : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    ‖castSymSectorOperator h A‖ = ‖A‖ := by
  cases h
  rfl

/-- The arbitrary-N DEF-009 operator inherits the bounded-kernel norm
estimate. -/
theorem norm_genericU_N_r_le (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel H r) :
    ‖genericU_N_r N r hr A‖ ≤ ‖A‖ := by
  rw [genericU_N_r, norm_castSymSectorOperator]
  exact norm_U_N_r_le A

/-- The source product symbol of a bounded symmetric kernel.  The expression
is meaningful for every profile; unit norm is the qualification under which
it is also the expectation of the N-particle placement on a product state. -/
def kernelProductSymbol {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) : ℂ :=
  ⟪(htpow r u : HilbertTensorPower ℂ H r),
    ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r)⟫_ℂ

/-- Splitting a product tensor at the kernel degree gives the kernel factors
and the untouched spectator factors. -/
theorem split_htpow (r q : ℕ) (u : H) :
    splitIsometry (𝕜 := ℂ) (E := H) r q
      (htpow (r + q) u : HilbertTensorPower ℂ H (r + q)) =
      htmul (htpow r u : HilbertTensorPower ℂ H r)
        (htpow q u : HilbertTensorPower ℂ H q) := by
  have happend : Fin.append (fun _ : Fin r => u) (fun _ : Fin q => u) =
      (fun _ : Fin (r + q) => u) := by
    simpa using (Fin.append_castAdd_natAdd (f := fun _ : Fin (r + q) => u))
  simpa [htpow, ptprod, happend] using
    (splitIsometry_ptprod_append (𝕜 := ℂ) (E := H) (a := fun _ : Fin r => u)
      (b := fun _ : Fin q => u))

/-- On a product vector, the zero extension acts as the original symmetric
kernel; the projection on the input is therefore harmless. -/
theorem zeroExtendKernel_htpow {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    zeroExtendKernel A (htpow r u : HilbertTensorPower ℂ H r) =
      ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) :
        HilbertTensorPower ℂ H r) := by
  have hproj : symProj ℂ H r (htpow r u : HilbertTensorPower ℂ H r) = htpow r u := by
    change groupAverage (permRep ℂ H r) (htpow r u : HilbertTensorPower ℂ H r) = _
    exact groupAverage_apply_of_mem (permRep ℂ H r) (htpow_mem_symSector r u)
  have hsector : symProjToSector (H := H) r (htpow r u) =
      ⟨htpow r u, htpow_mem_symSector r u⟩ := by
    apply Subtype.ext
    exact hproj
  simp [zeroExtendKernel, extendSymKernel, hsector]

/-- Pairing the first-slot placement against a product vector separates into
the kernel product symbol and the norm square of the q spectator factors. -/
theorem inner_firstPlacement_htpow {r q : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    ⟪(htpow (r + q) u : HilbertTensorPower ℂ H (r + q)),
      firstPlacement (q := q) A (htpow (r + q) u)⟫_ℂ =
      kernelProductSymbol A u *
        ⟪(htpow q u : HilbertTensorPower ℂ H q), htpow q u⟫_ℂ := by
  let e := splitIsometry (𝕜 := ℂ) (E := H) r q
  have hformula (z : HilbertTensorPower ℂ H (r + q)) :
      e (firstPlacement (q := q) A z) =
        htmap (zeroExtendKernel A)
          (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)) (e z) := by
    change e (e.symm (htmap (zeroExtendKernel A)
      (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)) (e z))) =
      htmap (zeroExtendKernel A)
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H q)) (e z)
    rw [e.apply_symm_apply]
  have hplace : e (firstPlacement (q := q) A
      (htpow (r + q) u : HilbertTensorPower ℂ H (r + q))) =
      htmul
        ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) :
          HilbertTensorPower ℂ H r)
        (htpow q u : HilbertTensorPower ℂ H q) := by
    rw [hformula, split_htpow, htmap_htmul, zeroExtendKernel_htpow]
    simp
  calc
    _ = ⟪e (htpow (r + q) u : HilbertTensorPower ℂ H (r + q)),
          e (firstPlacement (q := q) A (htpow (r + q) u))⟫_ℂ :=
        (e.inner_map_map _ _).symm
    _ = ⟪htmul (htpow r u)
          (htpow q u : HilbertTensorPower ℂ H q),
          htmul
            ((A ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) :
              HilbertTensorPower ℂ H r)
            (htpow q u : HilbertTensorPower ℂ H q)⟫_ℂ := by
          rw [split_htpow, hplace]
    _ = kernelProductSymbol A u *
          ⟪(htpow q u : HilbertTensorPower ℂ H q), htpow q u⟫_ℂ := by
          rw [inner_htmul]
          rfl

/-- Orthogonal projection onto the symmetric sector can be dropped from the
second slot of an inner product whose first slot is symmetric. -/
theorem inner_symProj_of_mem {n : ℕ} (x : SymSector ℂ H n)
    (y : HilbertTensorPower ℂ H n) :
    ⟪x.1, symProj ℂ H n y⟫_ℂ = ⟪x.1, y⟫_ℂ := by
  rw [symProj_eq_starProjection,
    ← Submodule.inner_starProjection_left_eq_right (SymSector ℂ H n) x.1 y,
    Submodule.starProjection_eq_self_iff.mpr x.property]

/-- Exact DEF-009 product-symbol characterization on an N-fold product
vector.  For an arbitrary profile, the untouched q factors contribute
`⟪u^⊗q,u^⊗q⟫`; for a unit profile this factor is one, giving the source's
displayed symbol `⟪u^⊗r,A u^⊗r⟫`. -/
theorem inner_U_N_r_product {r q : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    ⟪(htpow (r + q) u : HilbertTensorPower ℂ H (r + q)),
      ((U_N_r (r := r) (q := q) A
        ⟨htpow (r + q) u, htpow_mem_symSector (r + q) u⟩ :
          SymSector ℂ H (r + q)) : HilbertTensorPower ℂ H (r + q))⟫_ℂ =
      kernelProductSymbol A u *
        ⟪(htpow q u : HilbertTensorPower ℂ H q), htpow q u⟫_ℂ := by
  let x : SymSector ℂ H (r + q) :=
    ⟨htpow (r + q) u, htpow_mem_symSector (r + q) u⟩
  have hUx : (U_N_r (r := r) (q := q) A x : SymSector ℂ H (r + q)) =
      symProj ℂ H (r + q) (firstPlacement (q := q) A x.1) := by
    rw [U_N_r_eq_Q_N_p]
    change symmetrizedPlacement (q := q) A x.1 = _
    exact symmetrizedPlacement_apply_symmetric A x
  calc
    _ = ⟪x.1, (U_N_r (r := r) (q := q) A x : SymSector ℂ H (r + q))⟫_ℂ := rfl
    _ = ⟪x.1, symProj ℂ H (r + q)
          (firstPlacement (q := q) A x.1)⟫_ℂ := by rw [hUx]
    _ = ⟪x.1, firstPlacement (q := q) A x.1⟫_ℂ := inner_symProj_of_mem x _
    _ = kernelProductSymbol A u *
          ⟪(htpow q u : HilbertTensorPower ℂ H q), htpow q u⟫_ℂ := by
          exact inner_firstPlacement_htpow A u

/-- Unit-profile specialization of the product-symbol clause. -/
theorem inner_U_N_r_product_of_unit {r q : ℕ} (A : BoundedSymmetricKernel H r)
    (u : H) (hu : ‖u‖ = 1) :
    ⟪(htpow (r + q) u : HilbertTensorPower ℂ H (r + q)),
      ((U_N_r (r := r) (q := q) A
        ⟨htpow (r + q) u, htpow_mem_symSector (r + q) u⟩ :
          SymSector ℂ H (r + q)) : HilbertTensorPower ℂ H (r + q))⟫_ℂ =
      kernelProductSymbol A u := by
  rw [inner_U_N_r_product]
  have hq : ⟪(htpow q u : HilbertTensorPower ℂ H q), htpow q u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, norm_htpow, hu]
    simp
  rw [hq, mul_one]

/-- Physical-carrier specialization of the same normalized placement. -/
def physicalU_N_r (L : ℝ) [Fact (0 < L)] (N r : ℕ) (hr : r ≤ N)
    (A : BoundedSymmetricKernel (PhysicalTensor.L2T L) r) :
    SymSector ℂ (PhysicalTensor.L2T L) N →L[ℂ] SymSector ℂ (PhysicalTensor.L2T L) N :=
  PhysicalPlacements.physicalQ_N_p L N r hr A

/-- On `L²(𝕋_L)`, the physical DEF-009 realization has exactly the source's
binomial subset normalization and particle-count cast. -/
theorem physicalU_N_r_eq_subsetAverage (L : ℝ) [Fact (0 < L)] (N r : ℕ)
    (hr : r ≤ N) (A : BoundedSymmetricKernel (PhysicalTensor.L2T L) r) :
    physicalU_N_r L N r hr A =
      PhysicalPlacements.physicalSubsetPlacementAverage L N r hr A :=
  PhysicalPlacements.physicalQ_N_p_eq_subsetPlacementAverage L N r hr A

/-- The physical realization retains the generic operator-norm bound. -/
theorem norm_physicalU_N_r_le (L : ℝ) [Fact (0 < L)] (N r : ℕ)
    (hr : r ≤ N) (A : BoundedSymmetricKernel (PhysicalTensor.L2T L) r) :
    ‖physicalU_N_r L N r hr A‖ ≤ ‖A‖ :=
  PhysicalPlacements.norm_physicalQ_N_p_le L N r hr A

end QuantumNLS.KernelDefinition

#print axioms QuantumNLS.KernelDefinition.symmetrizedPlacement_apply_symmetric
#print axioms QuantumNLS.KernelDefinition.U_N_r_eq_sandwich
#print axioms QuantumNLS.KernelDefinition.U_N_r_eq_Q_N_p
#print axioms QuantumNLS.KernelDefinition.U_N_r_eq_subsetPlacementAverage
#print axioms QuantumNLS.KernelDefinition.norm_U_N_r_le
#print axioms QuantumNLS.KernelDefinition.genericU_N_r_eq_sandwich
#print axioms QuantumNLS.KernelDefinition.genericU_N_r_eq_subsetPlacementAverage
#print axioms QuantumNLS.KernelDefinition.norm_genericU_N_r_le
#print axioms QuantumNLS.KernelDefinition.split_htpow
#print axioms QuantumNLS.KernelDefinition.zeroExtendKernel_htpow
#print axioms QuantumNLS.KernelDefinition.inner_firstPlacement_htpow
#print axioms QuantumNLS.KernelDefinition.inner_U_N_r_product
#print axioms QuantumNLS.KernelDefinition.inner_U_N_r_product_of_unit
#print axioms QuantumNLS.KernelDefinition.physicalU_N_r_eq_subsetAverage
#print axioms QuantumNLS.KernelDefinition.norm_physicalU_N_r_le
