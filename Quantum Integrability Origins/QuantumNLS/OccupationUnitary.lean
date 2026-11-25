/-
U4: occupation vectors in the actual completed Hilbert tensor power of ℓ²(ℤ).
Owner: review record. Report pin 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f.
TensorFourier is frozen at 750d8753. No Bethe basis or U5 is assumed here.
-/
import QuantumNLS.TensorFourier
import QuantumNLS.OccupationHilbert
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.GroupTheory.Perm.DomMulAct

open scoped InnerProductSpace ComplexConjugate Classical
open QuantumNLS.TensorCarrier

noncomputable section
namespace QuantumNLS.OccupationUnitary

abbrev OneParticle := lp (fun _ : ℤ => ℂ) 2
abbrev Tensor (N : ℕ) := HilbertTensorPower ℂ OneParticle N
abbrev Boson (N : ℕ) := SymSector ℂ OneParticle N
abbrev Word (N : ℕ) := Fin N → ℤ

/-- The canonical one-particle basis, constructed from the ℓ² representation. -/
def oneBasis : HilbertBasis ℤ ℂ OneParticle :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem oneBasis_apply (a : ℤ) : oneBasis a = lp.single 2 a 1 := by
  convert! (oneBasis.repr_symm_single a).symm using 1

/-- Continuous elementary tensor map for the Hilbert tensor norm. -/
def tensorMultilinear (N : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N => OneParticle) (Tensor N) :=
  (((UniformSpace.Completion.toComplₗᵢ : AlgTensorPower ℂ OneParticle N →ₗᵢ[ℂ] _).toLinearMap).compMultilinearMap (PiTensorProduct.tprod ℂ)).mkContinuous 1 (by
      intro f
      change ‖((ptprod f : AlgTensorPower ℂ OneParticle N) : Tensor N)‖ ≤ 1 * _
      rw [UniformSpace.Completion.norm_coe, norm_ptprod, one_mul])

@[simp] theorem tensorMultilinear_apply (N : ℕ) (f : Fin N → OneParticle) :
    tensorMultilinear N f = ((ptprod f : AlgTensorPower ℂ OneParticle N) : Tensor N) := rfl

/-- Ordered product vectors, before symmetrization. -/
def productVector {N : ℕ} (w : Word N) : Tensor N :=
  tensorMultilinear N (fun i => oneBasis (w i))

theorem inner_productVector {N : ℕ} (v w : Word N) :
    ⟪productVector v, productVector w⟫_ℂ = if v = w then 1 else 0 := by
  classical
  change ⟪((ptprod _ : AlgTensorPower ℂ OneParticle N) : Tensor N),
    ((ptprod _ : AlgTensorPower ℂ OneParticle N) : Tensor N)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]
  simp_rw [orthonormal_iff_ite.mp oneBasis.orthonormal]
  split_ifs with h
  · subst w; simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem productVector_orthonormal (N : ℕ) :
    Orthonormal ℂ (productVector : Word N → Tensor N) :=
  orthonormal_iff_ite.mpr inner_productVector

/-- Separate density in every tensor slot. This does not assume a product basis. -/
theorem multilinear_mem_closed (N : ℕ) (R : Submodule ℂ (Tensor N))
    (hR : IsClosed (R : Set (Tensor N)))
    (h : ∀ w : Word N, productVector w ∈ R) (f : Fin N → OneParticle) :
    tensorMultilinear N f ∈ R := by
  classical
  have step : ∀ s : Finset (Fin N), ∀ g : Fin N → OneParticle,
      (∀ i, i ∉ s → ∃ a, g i = oneBasis a) → tensorMultilinear N g ∈ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro g hg
      choose a ha using (fun i => hg i (by simp))
      have he : g = fun i => oneBasis (a i) := funext ha
      rw [he]
      exact h a
    | @insert i s his ih =>
      intro g hg
      let L : OneParticle →ₗ[ℂ] Tensor N := (tensorMultilinear N).toMultilinearMap.toLinearMap g i
      have hL : Continuous L := ((tensorMultilinear N).toContinuousLinearMap g i).continuous
      have hb : Submodule.span ℂ (Set.range oneBasis) ≤ R.comap L := by
        apply Submodule.span_le.mpr
        rintro _ ⟨a, rfl⟩
        change tensorMultilinear N (Function.update g i (oneBasis a)) ∈ R
        apply ih
        intro j hj
        by_cases hji : j = i
        · subst j; exact ⟨a, by simp⟩
        · obtain ⟨b, hb⟩ := hg j (by simp [hj, hji])
          exact ⟨b, by simpa [Function.update_of_ne hji] using hb⟩
      have hc : (Submodule.span ℂ (Set.range oneBasis)).topologicalClosure ≤ R.comap L :=
        Submodule.topologicalClosure_minimal _ hb (hR.preimage hL)
      have hm := hc (oneBasis.dense_span ▸ (Submodule.mem_top : g i ∈ (⊤ : Submodule ℂ OneParticle)))
      simpa [L, MultilinearMap.toLinearMap] using hm
  exact step Finset.univ f (by simp)

/-- Completeness of the actual ordered product vectors, including N=0. -/
theorem productVector_dense (N : ℕ) :
    (Submodule.span ℂ (Set.range (productVector : Word N → Tensor N))).topologicalClosure = ⊤ := by
  let R := (Submodule.span ℂ (Set.range (productVector : Word N → Tensor N))).topologicalClosure
  have hp : ∀ f : Fin N → OneParticle, tensorMultilinear N f ∈ R :=
    multilinear_mem_closed N R (Submodule.isClosed_topologicalClosure _) (fun w =>
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩))
  have hall : ∀ x : Tensor N, x ∈ R := by
    intro x
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact Submodule.isClosed_topologicalClosure _
    | ih a =>
      induction a using AlgTensorPower.induction_on with
      | smul_ptprod c f =>
        simpa only [tensorMultilinear_apply, UniformSpace.Completion.coe_smul] using R.smul_mem c (hp f)
      | add a b ha hb =>
        simpa only [UniformSpace.Completion.coe_add] using R.add_mem ha hb
  exact top_unique (fun x _ => hall x)

/-- The product Hilbert basis is obtained from proved orthonormality and density. -/
def productBasis (N : ℕ) : HilbertBasis (Word N) ℂ (Tensor N) :=
  HilbertBasis.mk (productVector_orthonormal N) (productVector_dense N).ge

@[simp] theorem productBasis_apply (N : ℕ) (w : Word N) :
    productBasis N w = productVector w := by simp [productBasis]

/-! The multiplicity map and its permutation fibers. -/

/-- Histogram of an ordered word; every integer label is retained. -/
def occupation {N : ℕ} (w : Word N) : Occupation.Occ :=
  (Finset.univ.val.map w).toFinsupp

theorem occupation_apply {N : ℕ} (w : Word N) (a : ℤ) :
    occupation w a = Fintype.card {i : Fin N // w i = a} := by
  classical
  simp only [occupation, Multiset.toFinsupp_apply, Multiset.count_map]
  rw [Fintype.card_subtype]
  change (Finset.univ.filter (fun i : Fin N => a = w i)).card =
    (Finset.univ.filter (fun i : Fin N => w i = a)).card
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact eq_comm

theorem occupation_total {N : ℕ} (w : Word N) : Occupation.total (occupation w) = N := by
  change (Finset.univ.val.map w).toFinsupp.sum (fun _ => id) = N
  rw [Multiset.toFinsupp_sum_eq]
  simp

def occupationArr {N : ℕ} (w : Word N) : Occupation.Arr N :=
  ⟨occupation w, occupation_total w⟩

theorem occupation_support {N : ℕ} (w : Word N) :
    (occupation w).support = Finset.univ.image w := by
  classical
  ext a
  simp [occupation, Multiset.toFinsupp_support]

theorem occupation_surjective (N : ℕ) : Function.Surjective (occupationArr : Word N → Occupation.Arr N) := by
  intro m
  let l := m.val.toMultiset.toList
  have hl : l.length = N := by
    simpa [l, Finsupp.card_toMultiset, Occupation.IsArray, Occupation.total,
      Finsupp.degree_apply, Finsupp.sum] using m.property
  let w : Word N := fun i => l.get (Fin.cast hl.symm i)
  refine ⟨w, Subtype.ext ?_⟩
  change (Finset.univ.val.map w).toFinsupp = m.val
  rw [Fin.univ_val_map]
  have hw : List.ofFn w = l := by
    rw [show List.ofFn w = List.ofFn l.get from (List.ofFn_congr hl l.get).symm]
    exact List.ofFn_get l
  rw [hw]
  simp [l]

/-- A representative is chosen only after surjectivity of the histogram is proved. -/
def representative {N : ℕ} (m : Occupation.Arr N) : Word N :=
  (occupation_surjective N m).choose

@[simp] theorem occupationArr_representative {N : ℕ} (m : Occupation.Arr N) :
    occupationArr (representative m) = m := (occupation_surjective N m).choose_spec

theorem occupation_comp {N : ℕ} (w : Word N) (σ : Equiv.Perm (Fin N)) :
    occupation (w ∘ σ) = occupation w := by
  classical
  apply Finsupp.ext
  intro a
  rw [occupation_apply, occupation_apply]
  exact Fintype.card_congr (Equiv.subtypeEquiv σ (fun i => Iff.rfl))

theorem same_occupation_iff {N : ℕ} (v w : Word N) :
    occupation v = occupation w ↔ ∃ σ : Equiv.Perm (Fin N), w ∘ σ = v := by
  classical
  constructor
  · intro h
    have hc (a : ℤ) : Fintype.card {i // v i = a} = Fintype.card {i // w i = a} := by
      simpa only [occupation_apply] using congrArg (fun m : Occupation.Occ => m a) h
    let e : Equiv.Perm (Fin N) := Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hc a))
    exact ⟨e, funext (Equiv.ofFiberEquiv_map _)⟩
  · rintro ⟨σ, rfl⟩
    exact occupation_comp w σ

/-- The stabilizer size is exactly the product of multiplicity factorials. -/
def multiplicityFactorial (m : Occupation.Occ) : ℕ :=
  m.prod (fun _ k => k.factorial)

theorem multiplicityFactorial_pos (m : Occupation.Occ) : 0 < multiplicityFactorial m := by
  exact Finset.prod_pos (fun a _ => Nat.factorial_pos (m a))

theorem stabilizer_card {N : ℕ} (w : Word N) :
    Fintype.card {σ : Equiv.Perm (Fin N) // w ∘ σ = w} =
      multiplicityFactorial (occupation w) := by
  rw [DomMulAct.stabilizer_card']
  simp only [multiplicityFactorial, Finsupp.prod, occupation_support, occupation_apply]

theorem perm_productVector {N : ℕ} (σ : Equiv.Perm (Fin N)) (w : Word N) :
    (permRep ℂ OneParticle N σ : Tensor N →L[ℂ] Tensor N) (productVector w) =
      productVector (w ∘ σ.symm) := by
  rw [permRep_apply]
  change permHilbertIsometry σ ((ptprod _ : AlgTensorPower ℂ OneParticle N) : Tensor N) = _
  rw [permHilbertIsometry_coe, permLinearEquiv_ptprod]
  rfl

/-- Symmetrized ordered products in the completed tensor carrier. -/
def symProduct {N : ℕ} (w : Word N) : Tensor N :=
  symProj ℂ OneParticle N (productVector w)

theorem symProduct_mem {N : ℕ} (w : Word N) : symProduct w ∈ SymSector ℂ OneParticle N := by
  rw [symProduct, symProj_eq_starProjection]
  exact ((SymSector ℂ OneParticle N).orthogonalProjectionOnto _).property

theorem symProduct_perm {N : ℕ} (w : Word N) (σ : Equiv.Perm (Fin N)) :
    symProduct (w ∘ σ) = symProduct w := by
  have hp := congrArg (symProj ℂ OneParticle N) (perm_productVector σ.symm w)
  simp only [Equiv.symm_symm] at hp
  change (symProj ℂ OneParticle N) (productVector (w ∘ σ)) = _
  rw [← hp]
  exact congrArg (fun A : Tensor N →L[ℂ] Tensor N => A (productVector w))
    (groupAverage_mul_rep (permRep ℂ OneParticle N) σ.symm)

theorem symProduct_eq_of_occupation {N : ℕ} {v w : Word N}
    (h : occupation v = occupation w) : symProduct v = symProduct w := by
  obtain ⟨σ, rfl⟩ := (same_occupation_iff v w).mp h
  exact symProduct_perm w σ

theorem inner_productVector_symProduct {N : ℕ} (v w : Word N) :
    ⟪productVector v, symProduct w⟫_ℂ = (N.factorial : ℂ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin N), if v = w ∘ σ.symm then (1 : ℂ) else 0 := by
  rw [symProduct, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, inner_smul_right, inner_sum, perm_productVector,
    inner_productVector]

theorem inner_productVector_symProduct_self {N : ℕ} (w : Word N) :
    ⟪productVector w, symProduct w⟫_ℂ =
      (multiplicityFactorial (occupation w) : ℂ) / (N.factorial : ℂ) := by
  have hc : Fintype.card {σ : Equiv.Perm (Fin N) // w = w ∘ σ.symm} =
      multiplicityFactorial (occupation w) := by
    rw [← stabilizer_card w]
    exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.inv _) (fun σ => by
      change (w = w ∘ σ.symm) ↔ (w ∘ σ.symm = w)
      exact eq_comm))
  rw [inner_productVector_symProduct]
  have hs : (∑ σ : Equiv.Perm (Fin N), if w = w ∘ σ.symm then (1 : ℂ) else 0) =
      (Fintype.card {σ : Equiv.Perm (Fin N) // w = w ∘ σ.symm} : ℂ) := by simp [Fintype.card_subtype]
  rw [hs, hc]
  ring

theorem inner_productVector_symProduct_of_ne {N : ℕ} {v w : Word N}
    (h : occupation v ≠ occupation w) : ⟪productVector v, symProduct w⟫_ℂ = 0 := by
  rw [inner_productVector_symProduct]
  have hn (σ : Equiv.Perm (Fin N)) : v ≠ w ∘ σ.symm := by
    intro he
    exact h ((same_occupation_iff v w).mpr ⟨σ.symm, he.symm⟩)
  simp [hn]

theorem inner_symProduct {N : ℕ} (v w : Word N) :
    ⟪symProduct v, symProduct w⟫_ℂ = ⟪productVector v, symProduct w⟫_ℂ := by
  change ⟪symProj ℂ OneParticle N (productVector v), symProduct w⟫_ℂ = _
  rw [symProj_eq_starProjection, Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr (symProduct_mem w)]

/-! Factorial normalization and the complete symmetric occupation basis. -/

@[simp] theorem occupation_representative {N : ℕ} (m : Occupation.Arr N) :
    occupation (representative m) = m.val :=
  congrArg Subtype.val (occupationArr_representative m)

/-- The coefficient √(N! / ∏ₐ mₐ!) multiplying the averaged symmetric tensor. -/
def normalization {N : ℕ} (m : Occupation.Arr N) : ℝ :=
  Real.sqrt ((N.factorial : ℝ) / (multiplicityFactorial m.val : ℝ))

theorem normalization_pos {N : ℕ} (m : Occupation.Arr N) : 0 < normalization m := by
  apply Real.sqrt_pos.mpr
  exact div_pos (by exact_mod_cast Nat.factorial_pos N)
    (by exact_mod_cast multiplicityFactorial_pos m.val)

theorem normalization_identity {N : ℕ} (m : Occupation.Arr N) :
    (normalization m : ℂ) * ((normalization m : ℂ) *
      ((multiplicityFactorial m.val : ℂ) / (N.factorial : ℂ))) = 1 := by
  have hd : (multiplicityFactorial m.val : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast multiplicityFactorial_pos m.val)
  have hn : (N.factorial : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Nat.factorial_pos N)
  have hs : (normalization m) ^ 2 = (N.factorial : ℝ) / (multiplicityFactorial m.val : ℝ) :=
    Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hr : normalization m * (normalization m *
      ((multiplicityFactorial m.val : ℝ) / (N.factorial : ℝ))) = 1 := by
    calc
      _ = normalization m ^ 2 * ((multiplicityFactorial m.val : ℝ) / (N.factorial : ℝ)) := by ring
      _ = 1 := by rw [hs]; field_simp
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_one] using congrArg Complex.ofReal hr

/-- The normalized occupation vector in the actual completed tensor power. -/
def occupationVector {N : ℕ} (m : Occupation.Arr N) : Tensor N :=
  (normalization m : ℂ) • symProduct (representative m)

theorem occupationVector_mem {N : ℕ} (m : Occupation.Arr N) :
    occupationVector m ∈ SymSector ℂ OneParticle N :=
  (SymSector ℂ OneParticle N).smul_mem _ (symProduct_mem _)

/-- The same vector as an element of the closed symmetric sector. -/
def basisVector {N : ℕ} (m : Occupation.Arr N) : Boson N :=
  ⟨occupationVector m, occupationVector_mem m⟩

theorem inner_occupationVector_self {N : ℕ} (m : Occupation.Arr N) :
    ⟪occupationVector m, occupationVector m⟫_ℂ = 1 := by
  rw [occupationVector, inner_smul_left, inner_smul_right, inner_symProduct,
    inner_productVector_symProduct_self, occupation_representative]
  simpa using normalization_identity m

theorem inner_occupationVector_of_ne {N : ℕ} {m n : Occupation.Arr N} (h : m ≠ n) :
    ⟪occupationVector m, occupationVector n⟫_ℂ = 0 := by
  have ho : occupation (representative m) ≠ occupation (representative n) := by
    simpa only [occupation_representative, ne_eq, Subtype.val_inj] using h
  rw [occupationVector, occupationVector, inner_smul_left, inner_smul_right, inner_symProduct,
    inner_productVector_symProduct_of_ne ho, mul_zero, mul_zero]

theorem basisVector_orthonormal (N : ℕ) :
    Orthonormal ℂ (basisVector : Occupation.Arr N → Boson N) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro m n
  change ⟪occupationVector m, occupationVector n⟫_ℂ = _
  by_cases h : m = n
  · subst n
    simp only [ite_true, inner_occupationVector_self]
  · rw [ite_eq_right_iff.mpr (fun he => (h he).elim)]
    exact inner_occupationVector_of_ne h

/-- Averaged product vectors depend only on the complete occupation array. -/
theorem symProduct_eq_occupationVector {N : ℕ} (w : Word N) :
    symProduct w = (normalization (occupationArr w) : ℂ)⁻¹ •
      occupationVector (occupationArr w) := by
  have hn : (normalization (occupationArr w) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (normalization_pos (occupationArr w))
  rw [occupationVector, smul_smul, inv_mul_cancel₀ hn, one_smul]
  apply symProduct_eq_of_occupation
  exact (occupation_representative (occupationArr w)).symm

/-- No symmetric vector is missing from the occupation family. The proof uses the
constructed product Hilbert basis and the actual orthogonal symmetrizer. -/
theorem basisVector_orthogonal_eq_bot (N : ℕ) :
    (Submodule.span ℂ (Set.range (basisVector : Occupation.Arr N → Boson N)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  apply Subtype.ext
  apply (productBasis N).repr.injective
  apply lp.ext
  funext w
  simp only [HilbertBasis.repr_apply_apply, productBasis_apply]
  have hx0 (m : Occupation.Arr N) : ⟪occupationVector m, (x : Tensor N)⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hx (basisVector m) (Submodule.subset_span ⟨m, rfl⟩)
  have hp : ⟪symProduct w, (x : Tensor N)⟫_ℂ = 0 := by
    rw [symProduct_eq_occupationVector, inner_smul_left, hx0, mul_zero]
  have hfix : symProj ℂ OneParticle N (x : Tensor N) = x :=
    groupAverage_apply_of_mem (permRep ℂ OneParticle N) x.property
  rw [symProduct, symProj_eq_starProjection,
    Submodule.inner_starProjection_left_eq_right, ← symProj_eq_starProjection,
    hfix] at hp
  simpa using hp

/-- The normalized occupation Hilbert basis, constructed from proved vectors. -/
def occupationBasis (N : ℕ) : HilbertBasis (Occupation.Arr N) ℂ (Boson N) :=
  HilbertBasis.mkOfOrthogonalEqBot (basisVector_orthonormal N) (basisVector_orthogonal_eq_bot N)

@[simp] theorem occupationBasis_apply (N : ℕ) (m : Occupation.Arr N) :
    occupationBasis N m = basisVector m := by simp [occupationBasis]

/-- U4: the constructed unitary from the completed symmetric tensor sector to
unweighted ℓ² of all occupation arrays of total N. -/
def U4 (N : ℕ) : Boson N ≃ₗᵢ[ℂ] OccupationHilbert.H N :=
  (occupationBasis N).repr

@[simp] theorem U4_apply (N : ℕ) (ψ : Boson N) (m : Occupation.Arr N) :
    U4 N ψ m = ⟪occupationVector m, (ψ : Tensor N)⟫_ℂ := by
  rw [U4, HilbertBasis.repr_apply_apply, occupationBasis_apply]
  rfl

@[simp] theorem U4_basisVector (N : ℕ) (m : Occupation.Arr N) :
    U4 N (basisVector m) = lp.single 2 m 1 := by
  change (occupationBasis N).repr (basisVector m) = _
  rw [← occupationBasis_apply, HilbertBasis.repr_self]

@[simp] theorem U4_symm_single (N : ℕ) (m : Occupation.Arr N) :
    (U4 N).symm (lp.single 2 m 1) = basisVector m := by
  apply (U4 N).injective
  simp

/-- U3 followed by U4, retaining the frozen physical Fourier normalization. -/
def physicalOccupation (L : ℝ) [Fact (0 < L)] (N : ℕ) :
    PhysicalTensor.physSector L N ≃ₗᵢ[ℂ] OccupationHilbert.H N :=
  (TensorFourier.U3 L N).trans (U4 N)

/-- The literal factorial-weighted permutation sum for each normalized vector. -/
theorem occupationVector_factorial_average {N : ℕ} (m : Occupation.Arr N) :
    occupationVector m = ((normalization m : ℂ) / (N.factorial : ℂ)) •
      ∑ σ : Equiv.Perm (Fin N), productVector (representative m ∘ σ.symm) := by
  rw [occupationVector, symProduct, symProj_eq_factorial_average]
  simp only [smul_apply, sum_apply, perm_productVector, smul_smul, div_eq_mul_inv]

theorem occupationVector_norm {N : ℕ} (m : Occupation.Arr N) : ‖occupationVector m‖ = 1 := by
  exact (basisVector_orthonormal N).norm_eq_one m

theorem occupationBasis_dense (N : ℕ) :
    (Submodule.span ℂ (Set.range (basisVector : Occupation.Arr N → Boson N))).topologicalClosure = ⊤ := by
  have he : (⇑(occupationBasis N)) = (basisVector : Occupation.Arr N → Boson N) :=
    funext (occupationBasis_apply N)
  simpa only [he] using (occupationBasis N).dense_span

/-- Product coordinates with the inner product linear in its second argument. -/
theorem inner_productVector_htpow {N : ℕ} (w : Word N) (u : OneParticle) :
    ⟪productVector w, htpow N u⟫_ℂ = ∏ i, u (w i) := by
  change ⟪((ptprod _ : AlgTensorPower ℂ OneParticle N) : Tensor N),
    ((ptprod _ : AlgTensorPower ℂ OneParticle N) : Tensor N)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]
  apply Finset.prod_congr rfl
  intro i _
  rw [oneBasis_apply, lp.inner_single_left]
  simp

/-- Grouping repeated labels into occupation powers, without a finite-label cutoff. -/
theorem prod_occupation {N : ℕ} (w : Word N) (u : ℤ → ℂ) :
    (∏ i, u (w i)) = (occupation w).prod (fun a k => u a ^ k) := by
  have hs : ∀ s : Multiset ℤ, (s.map u).prod = s.toFinsupp.prod (fun a k => u a ^ k) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp [Multiset.toFinsupp_zero]
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
        Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      simp [mul_comm]
  simpa only [occupation, Multiset.map_map, Function.comp_def, Finset.prod] using
    hs (Finset.univ.val.map w)

/-- Normalized occupation coefficients of bosonic product states. -/
theorem U4_htpow (N : ℕ) (u : OneParticle) (m : Occupation.Arr N) :
    U4 N ⟨htpow N u, htpow_mem_symSector N u⟩ m =
      (normalization m : ℂ) * m.val.prod (fun a k => u a ^ k) := by
  rw [U4_apply, occupationVector, inner_smul_left]
  have hp : ⟪symProduct (representative m), htpow N u⟫_ℂ =
      ⟪productVector (representative m), htpow N u⟫_ℂ := by
    rw [symProduct, symProj_eq_starProjection,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (htpow_mem_symSector (𝕜 := ℂ) N u)]
  rw [hp, inner_productVector_htpow, prod_occupation, occupation_representative]
  simp

end QuantumNLS.OccupationUnitary

/-! Kernel axiom audit for every declaration in this module. -/
#print axioms QuantumNLS.OccupationUnitary.OneParticle
#print axioms QuantumNLS.OccupationUnitary.Tensor
#print axioms QuantumNLS.OccupationUnitary.Boson
#print axioms QuantumNLS.OccupationUnitary.Word
#print axioms QuantumNLS.OccupationUnitary.oneBasis
#print axioms QuantumNLS.OccupationUnitary.oneBasis_apply
#print axioms QuantumNLS.OccupationUnitary.tensorMultilinear
#print axioms QuantumNLS.OccupationUnitary.tensorMultilinear_apply
#print axioms QuantumNLS.OccupationUnitary.productVector
#print axioms QuantumNLS.OccupationUnitary.inner_productVector
#print axioms QuantumNLS.OccupationUnitary.productVector_orthonormal
#print axioms QuantumNLS.OccupationUnitary.multilinear_mem_closed
#print axioms QuantumNLS.OccupationUnitary.productVector_dense
#print axioms QuantumNLS.OccupationUnitary.productBasis
#print axioms QuantumNLS.OccupationUnitary.productBasis_apply
#print axioms QuantumNLS.OccupationUnitary.occupation
#print axioms QuantumNLS.OccupationUnitary.occupation_apply
#print axioms QuantumNLS.OccupationUnitary.occupation_total
#print axioms QuantumNLS.OccupationUnitary.occupationArr
#print axioms QuantumNLS.OccupationUnitary.occupation_support
#print axioms QuantumNLS.OccupationUnitary.occupation_surjective
#print axioms QuantumNLS.OccupationUnitary.representative
#print axioms QuantumNLS.OccupationUnitary.occupationArr_representative
#print axioms QuantumNLS.OccupationUnitary.occupation_comp
#print axioms QuantumNLS.OccupationUnitary.same_occupation_iff
#print axioms QuantumNLS.OccupationUnitary.multiplicityFactorial
#print axioms QuantumNLS.OccupationUnitary.multiplicityFactorial_pos
#print axioms QuantumNLS.OccupationUnitary.stabilizer_card
#print axioms QuantumNLS.OccupationUnitary.perm_productVector
#print axioms QuantumNLS.OccupationUnitary.symProduct
#print axioms QuantumNLS.OccupationUnitary.symProduct_mem
#print axioms QuantumNLS.OccupationUnitary.symProduct_perm
#print axioms QuantumNLS.OccupationUnitary.symProduct_eq_of_occupation
#print axioms QuantumNLS.OccupationUnitary.inner_productVector_symProduct
#print axioms QuantumNLS.OccupationUnitary.inner_productVector_symProduct_self
#print axioms QuantumNLS.OccupationUnitary.inner_productVector_symProduct_of_ne
#print axioms QuantumNLS.OccupationUnitary.inner_symProduct
#print axioms QuantumNLS.OccupationUnitary.occupation_representative
#print axioms QuantumNLS.OccupationUnitary.normalization
#print axioms QuantumNLS.OccupationUnitary.normalization_pos
#print axioms QuantumNLS.OccupationUnitary.normalization_identity
#print axioms QuantumNLS.OccupationUnitary.occupationVector
#print axioms QuantumNLS.OccupationUnitary.occupationVector_mem
#print axioms QuantumNLS.OccupationUnitary.basisVector
#print axioms QuantumNLS.OccupationUnitary.inner_occupationVector_self
#print axioms QuantumNLS.OccupationUnitary.inner_occupationVector_of_ne
#print axioms QuantumNLS.OccupationUnitary.basisVector_orthonormal
#print axioms QuantumNLS.OccupationUnitary.symProduct_eq_occupationVector
#print axioms QuantumNLS.OccupationUnitary.basisVector_orthogonal_eq_bot
#print axioms QuantumNLS.OccupationUnitary.occupationBasis
#print axioms QuantumNLS.OccupationUnitary.occupationBasis_apply
#print axioms QuantumNLS.OccupationUnitary.U4
#print axioms QuantumNLS.OccupationUnitary.U4_apply
#print axioms QuantumNLS.OccupationUnitary.U4_basisVector
#print axioms QuantumNLS.OccupationUnitary.U4_symm_single
#print axioms QuantumNLS.OccupationUnitary.physicalOccupation
#print axioms QuantumNLS.OccupationUnitary.occupationVector_factorial_average
#print axioms QuantumNLS.OccupationUnitary.occupationVector_norm
#print axioms QuantumNLS.OccupationUnitary.occupationBasis_dense
#print axioms QuantumNLS.OccupationUnitary.inner_productVector_htpow
#print axioms QuantumNLS.OccupationUnitary.prod_occupation
#print axioms QuantumNLS.OccupationUnitary.U4_htpow
