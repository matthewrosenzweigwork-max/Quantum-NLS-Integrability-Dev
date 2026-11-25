import QuantumNLS.OccupationUnitary
import QuantumNLS.TensorPlacements

/-!
DEF-026, report 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
Source: chapters/definitions.tex:157–159; core/occupation_transfers.tex:2–9;
local/quantum_periods.tex:15–30 (normalized bounded placements).
Actual bounded one-body placements on the completed tensor carrier. The donor
is a and the receiver is b. The sector N=1+q covers every positive particle
number; no division-by-zero convention is used. OccupationUnitary and all
imported APIs are frozen. No Bethe U5 or gauge is asserted.
-/

open scoped InnerProductSpace ComplexConjugate Classical
open QuantumNLS.TensorCarrier QuantumNLS.OccupationUnitary

noncomputable section
namespace QuantumNLS.OccupationConjugacy

/-- The actual one-body matrix unit |b⟩⟨a|, with inner product linear on the right. -/
def matrixUnit (a b : ℤ) : OneParticle →L[ℂ] OneParticle :=
  InnerProductSpace.rankOne ℂ (oneBasis b) (oneBasis a)

theorem matrixUnit_basis (a b c : ℤ) :
    matrixUnit a b (oneBasis c) = if c = a then oneBasis b else 0 := by
  simp only [matrixUnit, InnerProductSpace.rankOne_apply,
    orthonormal_iff_ite.mp oneBasis.orthonormal]
  by_cases h : c = a
  · subst c; simp
  · simp [h, Ne.symm h]

/-- Relocate the first bounded tensor placement to slot i. -/
def slot (q : ℕ) (i : Fin (1 + q)) (A : OneParticle →L[ℂ] OneParticle) :
    Tensor (1 + q) →L[ℂ] Tensor (1 + q) :=
  (permHilbertIsometry (Equiv.swap 0 i)).conjStarAlgEquiv
    (TensorFourier.oneBodyPlacement q A)

theorem oneBodyPlacement_product (q : ℕ) (A : OneParticle →L[ℂ] OneParticle)
    (f : Fin (1 + q) → OneParticle) :
    TensorFourier.oneBodyPlacement q A (tensorMultilinear (1 + q) f) =
      tensorMultilinear (1 + q) (Function.update f 0 (A (f 0))) := by
  let g : Fin 1 → OneParticle := fun i => f (Fin.castAdd q i)
  let h : Fin q → OneParticle := fun i => f (Fin.natAdd 1 i)
  have hf : f = Fin.append g h := Fin.append_castAdd_natAdd.symm
  have hu : Function.update f 0 (A (f 0)) =
      Fin.append (fun _ : Fin 1 => A (f 0)) h := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change Function.update f 0 (A (f 0)) 0 = A (f 0)
      simp
    · simp [h, Function.update_of_ne (show Fin.natAdd 1 j ≠ (0 : Fin (1 + q)) by
        intro he; have := congrArg Fin.val he; simp at this)]
  apply (splitIsometry (𝕜 := ℂ) (E := OneParticle) 1 q).injective
  rw [hu]
  simp only [tensorMultilinear_apply]
  rw [splitIsometry_ptprod_append]
  rw [TensorFourier.oneBodyPlacement, TensorFourier.split_blockPlacement,
    hf, splitIsometry_ptprod_append, htmap_htmul]
  congr 1
  apply (TensorFourier.firstPowerIso (𝕜 := ℂ) (E := OneParticle)).injective
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    TensorFourier.firstPowerIso_ptprod]
  rfl

theorem perm_tensorMultilinear {N : ℕ} (σ : Equiv.Perm (Fin N))
    (f : Fin N → OneParticle) :
    permHilbertIsometry σ (tensorMultilinear N f) =
      tensorMultilinear N (f ∘ σ.symm) := by
  rw [tensorMultilinear_apply, permHilbertIsometry_coe, permLinearEquiv_ptprod]
  rfl

theorem slot_tensorMultilinear (q : ℕ) (i : Fin (1 + q))
    (A : OneParticle →L[ℂ] OneParticle) (f : Fin (1 + q) → OneParticle) :
    slot q i A (tensorMultilinear (1 + q) f) =
      tensorMultilinear (1 + q) (Function.update f i (A (f i))) := by
  have hswap : (permHilbertIsometry (𝕜 := ℂ) (E := OneParticle) (Equiv.swap 0 i)).symm =
      permHilbertIsometry (Equiv.swap 0 i) := by
    change ((permHom ℂ OneParticle (1 + q)) (Equiv.swap 0 i))⁻¹ = _
    rw [← map_inv]
    simp only [Equiv.swap_inv]
    rfl
  simp only [slot, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hswap,
    perm_tensorMultilinear, oneBodyPlacement_product]
  congr 1
  funext j
  by_cases hj : j = i
  · subst j; simp
  · have hs : Equiv.swap 0 i j ≠ 0 := by
      intro h
      have := congrArg (Equiv.swap 0 i) h
      exact hj (by simpa using this)
    simp [Function.comp_def, Equiv.symm_swap, Function.update_of_ne hj,
      Function.update_of_ne hs]

theorem slot_product (q : ℕ) (i : Fin (1 + q)) (a b : ℤ) (w : Word (1 + q)) :
    slot q i (matrixUnit a b) (productVector w) =
      if w i = a then productVector (Function.update w i b) else 0 := by
  rw [productVector, slot_tensorMultilinear, matrixUnit_basis]
  split_ifs with hi
  · congr 1
    funext j
    by_cases hj : j = i <;> simp [hj]
  · exact (tensorMultilinear (1 + q)).map_coord_zero i (by simp)

open Occupation

theorem occupation_sum {N : ℕ} (w : Word N) :
    occupation w = ∑ i, e (w i) := by
  ext a
  rw [occupation_apply, Fintype.card_subtype, Finset.card_filter]
  simp only [Finsupp.finsetSum_apply, e, Finsupp.single_apply]

theorem occupation_split {N : ℕ} (w : Word N) (i : Fin N) :
    occupation w = (∑ j ∈ Finset.univ.erase i, e (w j)) + e (w i) := by
  rw [occupation_sum]
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm

theorem occupation_update {N : ℕ} (w : Word N) (i : Fin N) (b : ℤ) :
    occupation (Function.update w i b) = shift (w i) b (occupation w) := by
  rw [occupation_split w i, shift, add_tsub_cancel_right,
    occupation_split (Function.update w i b) i]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem word_donor {N : ℕ} (w : Word N) (i : Fin N) :
    DonorOK (w i) (occupation w) := by
  rw [DonorOK, occupation_split w i]
  simp

/-- Adding a particle multiplies the multiplicity factorial by its new count. -/
theorem multiplicityFactorial_add_single (m : Occ) (a : ℤ) :
    multiplicityFactorial (m + e a) = (m a + 1) * multiplicityFactorial m := by
  let s := insert a m.support
  have hm : m.support ⊆ s := Finset.subset_insert _ _
  have hn : (m + e a).support ⊆ s := by
    apply (Finsupp.support_add).trans
    exact Finset.union_subset hm (by simp [e, s])
  rw [multiplicityFactorial, Finsupp.prod_of_support_subset _ hn _ (by simp),
    multiplicityFactorial, Finsupp.prod_of_support_subset _ hm _ (by simp)]
  rw [← Finset.mul_prod_erase _ _ (by simp [s] : a ∈ s),
    ← Finset.mul_prod_erase _ _ (by simp [s] : a ∈ s)]
  have he : (∏ x ∈ s.erase a, ((m + e a) x).factorial) =
      ∏ x ∈ s.erase a, (m x).factorial := by
    apply Finset.prod_congr rfl
    intro x hx
    simp [e, Ne.symm (Finset.ne_of_mem_erase hx)]
  rw [he]
  simp [e, Nat.factorial_succ, mul_assoc]

/-- The factorial ratio includes the depleted donor, including a=b. -/
theorem factorial_shift (m : Occ) (a b : ℤ) (h : DonorOK a m) :
    (m a) * multiplicityFactorial (shift a b m) =
      ((m - e a) b + 1) * multiplicityFactorial m := by
  have hm := shift_sub_add h
  have hd := multiplicityFactorial_add_single (m - e a) a
  have hr := multiplicityFactorial_add_single (m - e a) b
  rw [hm] at hd
  have ha : (m - e a) a + 1 = m a := by
    have hh : 1 ≤ m a := h
    simp only [Finsupp.coe_tsub, Pi.sub_apply, e, Finsupp.single_eq_same]
    omega
  rw [ha] at hd
  change m a * multiplicityFactorial (m - e a + e b) = _
  rw [hr, hd]
  ring


/-- Unnormalized sum of the actual bounded one-body placements. -/
def totalPlacement (q : ℕ) (a b : ℤ) : Tensor (1 + q) →L[ℂ] Tensor (1 + q) :=
  ∑ i, slot q i (matrixUnit a b)

/-- Projection used to compute the action before restricting to bosons. -/
def projectedTotal (q : ℕ) (a b : ℤ) : Tensor (1 + q) →L[ℂ] Tensor (1 + q) :=
  (symProj ℂ OneParticle (1 + q)).comp (totalPlacement q a b)

def rawAction {N : ℕ} (a b : ℤ) (m : Arr N) : Tensor N :=
  if h : DonorOK a m.1 then
    (m.1 a : ℂ) • symProduct (representative (shiftArr a b m h)) else 0

/-- Each occupied slot contributes the same symmetrized destination; there
are exactly m_a such slots. No factorial or particle-number normalization yet. -/
theorem projectedTotal_product (q : ℕ) (a b : ℤ) (w : Word (1 + q)) :
    projectedTotal q a b (productVector w) = rawAction a b (occupationArr w) := by
  have he (i : Fin (1 + q)) (hi : w i = a) (hd : DonorOK a (occupation w)) :
      symProduct (Function.update w i b) =
        symProduct (representative (shiftArr a b (occupationArr w) hd)) := by
    apply symProduct_eq_of_occupation
    rw [occupation_update, hi, occupation_representative]
    rfl
  simp only [projectedTotal, ContinuousLinearMap.comp_apply, totalPlacement,
    sum_apply, map_sum, slot_product, rawAction]
  by_cases hd : DonorOK a (occupationArr w).1
  · rw [dite_eq_left hd]
    have hs : (∑ i : Fin (1 + q),
        symProj ℂ OneParticle (1 + q)
          (if w i = a then productVector (Function.update w i b) else 0)) =
        ∑ i : Fin (1 + q), if w i = a then
          symProduct (representative (shiftArr a b (occupationArr w) hd)) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : w i = a
      · simp only [ite_eq_left hi]
        exact he i hi hd
      · simp [hi]
    rw [hs, ← Finset.sum_filter]
    simp only [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
    congr 1
    change ((Finset.univ.filter (fun i : Fin (1 + q) => w i = a)).card : ℂ) = ((occupation w) a : ℂ)
    rw [occupation_apply, Fintype.card_subtype]
  · rw [dite_eq_right hd]
    apply Finset.sum_eq_zero
    intro i _
    have hi : w i ≠ a := by
      intro hi
      exact hd (hi ▸ word_donor w i)
    simp [hi]

/-- Bounded operators are determined by ordered product basis vectors. -/
theorem ext_product {N : ℕ} {A B : Tensor N →L[ℂ] Tensor N}
    (h : ∀ w : Word N, A (productVector w) = B (productVector w)) : A = B := by
  have hs : Submodule.span ℂ (Set.range (productVector : Word N → Tensor N)) ≤
      LinearMap.ker (A - B).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    simpa using sub_eq_zero.mpr (h w)
  have hc := Submodule.topologicalClosure_minimal _ hs (A - B).isClosed_ker
  rw [productVector_dense] at hc
  ext x
  exact sub_eq_zero.mp (hc (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ (Tensor N))))

/-- The projected collective action depends only on the histogram. -/
theorem projectedTotal_perm (q : ℕ) (a b : ℤ) (σ : Equiv.Perm (Fin (1 + q))) :
    (projectedTotal q a b).comp
      (permHilbertIsometry σ).toContinuousLinearEquiv.toContinuousLinearMap =
      projectedTotal q a b := by
  apply ext_product
  intro w
  change projectedTotal q a b (permHilbertIsometry σ (productVector w)) =
    projectedTotal q a b (productVector w)
  have hp : permHilbertIsometry σ (productVector w) = productVector (w ∘ σ.symm) :=
    perm_productVector σ w
  rw [hp, projectedTotal_product, projectedTotal_product]
  congr 1
  apply Subtype.ext
  exact occupation_comp w σ.symm

/-- Computing on symmetrized inputs introduces no extra multiplicity. -/
theorem projectedTotal_symProduct (q : ℕ) (a b : ℤ) (w : Word (1 + q)) :
    projectedTotal q a b (symProduct w) = rawAction a b (occupationArr w) := by
  rw [symProduct, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, map_smul, map_sum]
  have he (σ : Equiv.Perm (Fin (1 + q))) :
      projectedTotal q a b
        ((permRep ℂ OneParticle (1 + q) σ : Tensor (1 + q) →L[ℂ] _) (productVector w)) =
      rawAction a b (occupationArr w) := by
    have ht := congrArg (fun T : Tensor (1 + q) →L[ℂ] Tensor (1 + q) => T (productVector w))
      (projectedTotal_perm q a b σ)
    exact ht.trans (projectedTotal_product q a b w)
  simp_rw [he]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp [Fintype.card_perm, Nat.factorial_ne_zero]

theorem normalization_sq {N : ℕ} (m : Arr N) :
    normalization m ^ 2 = (N.factorial : ℝ) / (multiplicityFactorial m.1 : ℝ) :=
  Real.sq_sqrt (by positivity)

/-- Exact coefficient obtained from the two factorial normalizations. -/
theorem normalization_shift {N : ℕ} (hN : 0 < N) (a b : ℤ) (m : Arr N)
    (hd : DonorOK a m.1) :
    normalization m * (m.1 a : ℝ) =
      (N : ℝ) * coef N a b m.1 * normalization (shiftArr a b m hd) := by
  let n := shiftArr a b m hd
  let r : ℝ := ((m.1 - e a) b + 1 : ℕ)
  have hmpos : (0 : ℝ) < multiplicityFactorial m.1 := by
    exact_mod_cast multiplicityFactorial_pos m.1
  have hnpos : (0 : ℝ) < multiplicityFactorial n.1 := by
    exact_mod_cast multiplicityFactorial_pos n.1
  have hf : (m.1 a : ℝ) * (multiplicityFactorial n.1 : ℝ) =
      r * (multiplicityFactorial m.1 : ℝ) := by
    dsimp [n, r, shiftArr]
    exact_mod_cast factorial_shift m.1 a b hd
  have hr : normalization m ^ 2 * (m.1 a : ℝ) = r * normalization n ^ 2 := by
    rw [normalization_sq, normalization_sq]
    field_simp
    nlinarith [hf]
  have hrnon : 0 ≤ r := Nat.cast_nonneg _
  have he : normalization m * (m.1 a : ℝ) =
      Real.sqrt ((m.1 a : ℝ) * r) * normalization n := by
    apply (sq_eq_sq₀
      (mul_nonneg (normalization_pos m).le (Nat.cast_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (normalization_pos n).le)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [hr]
  rw [he]
  have hcoef : (N : ℝ) * coef N a b m.1 = Real.sqrt ((m.1 a : ℝ) * r) := by
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
    by_cases hab : a = b
    · subst b
      have hd' : 1 ≤ m.1 a := hd
      have hr' : r = m.1 a := by
        dsimp [r]
        simp only [e, Finsupp.single_eq_same]
        exact_mod_cast Nat.sub_add_cancel hd'
      rw [coef_diag, hr', Real.sqrt_mul_self (Nat.cast_nonneg _)]
      field_simp
    · have hr' : r = (m.1 b : ℝ) + 1 := by simp [r, e, Ne.symm hab]
      rw [coef_offdiag hab, hr']
      field_simp
  rw [hcoef]


/-- Covariance of the literal sum of slot operators under all permutations. -/
theorem totalPlacement_perm (q : ℕ) (a b : ℤ) (σ : Equiv.Perm (Fin (1 + q))) :
    (permHilbertIsometry σ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (totalPlacement q a b) =
      (totalPlacement q a b).comp
        (permHilbertIsometry σ).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ext_product
  intro w
  change permHilbertIsometry σ (totalPlacement q a b (productVector w)) =
    totalPlacement q a b (permHilbertIsometry σ (productVector w))
  have hp : permHilbertIsometry σ (productVector w) = productVector (w ∘ σ.symm) :=
    perm_productVector σ w
  rw [hp]
  simp only [totalPlacement, sum_apply, map_sum, slot_product]
  apply Fintype.sum_equiv σ
  intro i
  have hu : (Function.update w i b) ∘ σ.symm =
      Function.update (w ∘ σ.symm) (σ i) b := by
    funext j
    by_cases hj : j = σ i
    · subst j; simp
    · have hk : σ.symm j ≠ i := by
        intro he
        apply hj
        rw [← he, σ.apply_symm_apply]
      simp [Function.comp_def, Function.update_of_ne hj, Function.update_of_ne hk]
  by_cases hi : w i = a
  · simp only [Function.comp_apply, σ.symm_apply_apply, ite_eq_left hi]
    exact (perm_productVector σ (Function.update w i b)).trans (congrArg productVector hu)
  · simp only [Function.comp_apply, σ.symm_apply_apply, ite_eq_right hi, map_zero]

theorem totalPlacement_mem (q : ℕ) (a b : ℤ) (ψ : Boson (1 + q)) :
    totalPlacement q a b ψ.1 ∈ SymSector ℂ OneParticle (1 + q) := by
  intro σ
  have h := congrArg (fun T : Tensor (1 + q) →L[ℂ] Tensor (1 + q) => T ψ.1)
    (totalPlacement_perm q a b σ)
  change permHilbertIsometry σ (totalPlacement q a b ψ.1) = _ at h
  change permHilbertIsometry σ (totalPlacement q a b ψ.1) = _
  rw [h]
  exact congrArg (totalPlacement q a b) (ψ.property σ)

theorem projectedTotal_eq (q : ℕ) (a b : ℤ) (ψ : Boson (1 + q)) :
    projectedTotal q a b ψ.1 = totalPlacement q a b ψ.1 := by
  change symProj ℂ OneParticle (1 + q) (totalPlacement q a b ψ.1) = _
  rw [symProj_eq_starProjection]
  exact Submodule.starProjection_eq_self_iff.mpr (totalPlacement_mem q a b ψ)

/-- The normalized actual collective one-body operator N⁻¹∑ᵢ |b⟩⟨a|ᵢ
restricted to the closed symmetric tensor sector, with no assumed transport. -/
def collective (q : ℕ) (a b : ℤ) : Boson (1 + q) →L[ℂ] Boson (1 + q) :=
  ((1 + q : ℕ) : ℂ)⁻¹ •
    ((totalPlacement q a b).comp (SymSector ℂ OneParticle (1 + q)).subtypeL).codRestrict
      (SymSector ℂ OneParticle (1 + q)) (totalPlacement_mem q a b)

/-- Normalized occupation basis action of the actual collective operator. -/
theorem collective_basisVector (q : ℕ) (a b : ℤ) (m : Arr (1 + q)) :
    collective q a b (basisVector m) =
      if hd : DonorOK a m.1 then
        (coef (1 + q) a b m.1 : ℂ) • basisVector (shiftArr a b m hd) else 0 := by
  apply Subtype.ext
  change (((1 + q : ℕ) : ℂ)⁻¹) • totalPlacement q a b (occupationVector m) = _
  have he : projectedTotal q a b (occupationVector m) =
      totalPlacement q a b (occupationVector m) := projectedTotal_eq q a b (basisVector m)
  rw [← he]
  change (((1 + q : ℕ) : ℂ)⁻¹) • projectedTotal q a b (occupationVector m) = _
  rw [occupationVector, map_smul, projectedTotal_symProduct,
    occupationArr_representative]
  unfold rawAction
  split_ifs with hd
  · change _ = (coef (1 + q) a b m.1 : ℂ) • occupationVector (shiftArr a b m hd)
    rw [occupationVector]
    simp only [smul_smul]
    congr 1
    have hr := normalization_shift (show 0 < 1 + q by omega) a b m hd
    have hc := congrArg Complex.ofReal hr
    simp only [Complex.ofReal_mul, Complex.ofReal_natCast] at hc
    have hn : (((1 + q : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast (show 1 + q ≠ 0 by omega)
    calc
      _ = (((1 + q : ℕ) : ℂ)⁻¹) *
          ((normalization m : ℂ) * (m.1 a : ℂ)) := by ring
      _ = _ := by rw [hc]; field_simp
  · simp

/-- U4 intertwines the actual collective placements and the constructed
bounded occupation shifts on every vector of the complete symmetric sector. -/
theorem U4_collective (q : ℕ) (a b : ℤ) (ψ : Boson (1 + q)) :
    U4 (1 + q) (collective q a b ψ) =
      OccupationHilbert.E (1 + q) a b (U4 (1 + q) ψ) := by
  have hh : ((U4 (1 + q)).conjStarAlgEquiv (collective q a b)) =
      OccupationHilbert.E (1 + q) a b := by
    apply OccupationHilbert.ext_core
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [map_add, hu, hv]
    | single m z =>
      have hz : (lp.single 2 m z : OccupationHilbert.H (1 + q)) = z • lp.single 2 m (1 : ℂ) := by
        rw [← lp.single_smul]
        simp only [smul_eq_mul, mul_one]
      simp only [OccupationHilbert.core_single, hz, map_smul,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, U4_symm_single,
        collective_basisVector, OccupationHilbert.E_single]
      split_ifs with hd
      · simp only [map_smul, U4_basisVector, ← lp.single_smul, smul_eq_mul, mul_one]
      · simp
  have h := congrArg (fun T : OccupationHilbert.H (1 + q) →L[ℂ]
      OccupationHilbert.H (1 + q) => T (U4 (1 + q) ψ)) hh
  simpa using h

theorem U4_conjugacy (q : ℕ) (a b : ℤ) :
    (U4 (1 + q)).conjStarAlgEquiv (collective q a b) =
      OccupationHilbert.E (1 + q) a b := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply] using U4_collective q a b ((U4 (1 + q)).symm v)


/-- Empty donors give zero in the actual symmetric tensor sector. -/
theorem collective_empty (q : ℕ) (a b : ℤ) (m : Arr (1 + q))
    (hd : ¬ DonorOK a m.1) : collective q a b (basisVector m) = 0 := by
  rw [collective_basisVector, dite_eq_right hd]

/-- Literal off-diagonal DEF-026 coefficient, with the receiver gaining one. -/
theorem collective_offdiag (q : ℕ) (a b : ℤ) (hab : a ≠ b) (m : Arr (1 + q))
    (hd : DonorOK a m.1) :
    collective q a b (basisVector m) =
      ((Real.sqrt ((m.1 a : ℝ) * ((m.1 b : ℝ) + 1)) / (1 + q : ℕ) : ℝ) : ℂ) •
        basisVector (shiftArr a b m hd) := by
  rw [collective_basisVector, dite_eq_left hd, coef_offdiag hab]

/-- The diagonal is the occupation fraction, including its zero-donor case. -/
theorem collective_diag (q : ℕ) (a : ℤ) (m : Arr (1 + q)) :
    collective q a a (basisVector m) =
      (((m.1 a : ℝ) / (1 + q : ℕ) : ℝ) : ℂ) • basisVector m := by
  rw [collective_basisVector]
  split_ifs with hd
  · have hs : shiftArr a a m hd = m := Subtype.ext (shift_self hd)
    rw [hs, coef_diag]
  · have hz : m.1 a = 0 := by
      have : ¬ 1 ≤ m.1 a := hd
      omega
    simp [hz]

/-- The complete collective operator has the source norm bound, transported
only after the conjugacy has been proved. -/
theorem collective_norm_le (q : ℕ) (a b : ℤ) : ‖collective q a b‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ψ
  calc
    ‖collective q a b ψ‖ = ‖U4 (1 + q) (collective q a b ψ)‖ :=
      ((U4 (1 + q)).norm_map _).symm
    _ = ‖OccupationHilbert.E (1 + q) a b (U4 (1 + q) ψ)‖ := by rw [U4_collective]
    _ ≤ ‖OccupationHilbert.E (1 + q) a b‖ * ‖U4 (1 + q) ψ‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖ψ‖ := by
      rw [(U4 (1 + q)).norm_map]
      exact mul_le_mul_of_nonneg_right (OccupationHilbert.E_norm_le _ _ _) (norm_nonneg _)

end QuantumNLS.OccupationConjugacy

/-! Kernel axiom audit for every declaration in this module. -/
#print axioms QuantumNLS.OccupationConjugacy.matrixUnit
#print axioms QuantumNLS.OccupationConjugacy.matrixUnit_basis
#print axioms QuantumNLS.OccupationConjugacy.slot
#print axioms QuantumNLS.OccupationConjugacy.oneBodyPlacement_product
#print axioms QuantumNLS.OccupationConjugacy.perm_tensorMultilinear
#print axioms QuantumNLS.OccupationConjugacy.slot_tensorMultilinear
#print axioms QuantumNLS.OccupationConjugacy.slot_product
#print axioms QuantumNLS.OccupationConjugacy.occupation_sum
#print axioms QuantumNLS.OccupationConjugacy.occupation_split
#print axioms QuantumNLS.OccupationConjugacy.occupation_update
#print axioms QuantumNLS.OccupationConjugacy.word_donor
#print axioms QuantumNLS.OccupationConjugacy.multiplicityFactorial_add_single
#print axioms QuantumNLS.OccupationConjugacy.factorial_shift
#print axioms QuantumNLS.OccupationConjugacy.totalPlacement
#print axioms QuantumNLS.OccupationConjugacy.projectedTotal
#print axioms QuantumNLS.OccupationConjugacy.rawAction
#print axioms QuantumNLS.OccupationConjugacy.projectedTotal_product
#print axioms QuantumNLS.OccupationConjugacy.ext_product
#print axioms QuantumNLS.OccupationConjugacy.projectedTotal_perm
#print axioms QuantumNLS.OccupationConjugacy.projectedTotal_symProduct
#print axioms QuantumNLS.OccupationConjugacy.normalization_sq
#print axioms QuantumNLS.OccupationConjugacy.normalization_shift
#print axioms QuantumNLS.OccupationConjugacy.totalPlacement_perm
#print axioms QuantumNLS.OccupationConjugacy.totalPlacement_mem
#print axioms QuantumNLS.OccupationConjugacy.projectedTotal_eq
#print axioms QuantumNLS.OccupationConjugacy.collective
#print axioms QuantumNLS.OccupationConjugacy.collective_basisVector
#print axioms QuantumNLS.OccupationConjugacy.U4_collective
#print axioms QuantumNLS.OccupationConjugacy.U4_conjugacy
#print axioms QuantumNLS.OccupationConjugacy.collective_empty
#print axioms QuantumNLS.OccupationConjugacy.collective_offdiag
#print axioms QuantumNLS.OccupationConjugacy.collective_diag
#print axioms QuantumNLS.OccupationConjugacy.collective_norm_le
