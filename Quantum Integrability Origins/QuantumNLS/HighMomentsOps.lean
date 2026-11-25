import QuantumNLS.RootOverlapLimit
import QuantumNLS.HighMomentsRank
import QuantumNLS.HighMomentsWord

/-!
# PROP-008 `lem:B4-high-moments`, stage B (operator layer)
(source/chapters/propagation/spectral_calculus.tex:24-60: "express each placement as an average over an
independently chosen uniform subset `S_j`"; the isolated-vertex step)

Placements are indexed by literal slot sets `s : Finset (Fin N)`: `Pl B N s` is the realized placement
`rawSubsetPlacement` of `B |s|` at `s` (ROC1/PlacementGrouping).  Proved:

* `rawAvg_eq_sum`: the full-tensor average is `C(N,r)⁻¹ Σ_{|s|=r} Pl B N s`;
* `Pl_commute_of_disjoint`: placements on disjoint slot sets commute (from ROC1);
* `raw_eq_conj`: every placement is a permutation conjugate of the standard first-block placement;
* `Pl_adj`: `⟨Pl B s x, y⟩ = ⟨x, Pl B† s y⟩` (so the adjoint of a placement is the placement of the adjoint
  kernel);
* the rank-one projection kernel `rk1 r u = |u^{⊗r}⟩⟨u^{⊗r}|` gives `Π_s = Pl (rk1) s` with
  `Π_s u^N = u^N`, `Π_s` self-adjoint, `Π_s (Pl B s u^N) = ⟨u^r, B u^r⟩ u^N`;
* `word_iso`: for a word of centered placements `T_i = Pl B_i s_i − a_i`, a position `j` whose slot set is
  disjoint from all the others kills the expectation `⟨u^N, T_0 ⋯ T_m u^N⟩` (printed isolated-vertex step).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping QuantumNLS.PlacementUnionReindex
  QuantumNLS.PlacementFiberOperator QuantumNLS.RootOverlapCommutator QuantumNLS.RootOverlapLimit
  QuantumNLS.HighMomentsWord

namespace QuantumNLS.HighMomentsOps

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bounded operators on the `N`-fold completed tensor power. -/
abbrev Op (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (N : ℕ) :=
  HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N

/-! ### Placements indexed by slot sets -/

section Slots

theorem castSlotSet_cancel {m n : ℕ} (h : m = n) (S : Finset (Fin n)) :
    castSlotSet h (castSlotSet h.symm S) = S := by
  subst h; ext x; simp [castSlotSet]

theorem castSlotSet_cancel' {m n : ℕ} (h : m = n) (S : Finset (Fin m)) :
    castSlotSet h.symm (castSlotSet h S) = S := by
  subst h; ext x; simp [castSlotSet]

theorem card_castSlotSet {m n : ℕ} (h : m = n) (S : Finset (Fin m)) :
    (castSlotSet h S).card = S.card := by
  simp [castSlotSet]

variable {N : ℕ}

theorem hcard (s : Finset (Fin N)) : s.card ≤ N := by
  simpa using Finset.card_le_univ s

/-- The slot set `s` as a placement subset of `s.card + (N - s.card)` slots. -/
def toPS (s : Finset (Fin N)) : PlacementSubset s.card (N - s.card) :=
  ⟨castSlotSet (Nat.add_sub_of_le (hcard s)).symm s, by rw [card_castSlotSet]⟩

theorem leftSlots_toPS (s t : Finset (Fin N)) :
    leftSlots (hcard s) ((toPS s, toPS t) : ActualPairPlacement N s.card t.card) = s :=
  castSlotSet_cancel _ s

theorem rightSlots_toPS (s t : Finset (Fin N)) :
    rightSlots (hcard t) ((toPS s, toPS t) : ActualPairPlacement N s.card t.card) = t :=
  castSlotSet_cancel _ t

/-- The placement of the kernel `B |s|` at the slot set `s`. -/
def Pl (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) (s : Finset (Fin N)) : Op H N :=
  rawSubsetPlacement N s.card (hcard s) (toPS s) (B s.card)

theorem norm_Pl_le (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (s : Finset (Fin N)) :
    ‖Pl B N s‖ ≤ ‖B s.card‖ :=
  norm_rawSubsetPlacement_le N s.card (hcard s) (toPS s) (B s.card)

theorem Pl_commute_of_disjoint (B B' : ∀ r : ℕ, BoundedSymmetricKernel H r)
    (s t : Finset (Fin N)) (hst : Disjoint s t) : Commute (Pl B N s) (Pl B' N t) := by
  have h := rawPlacement_commute_of_disjoint N s.card t.card (hcard s) (hcard t) (B s.card)
    (B' t.card) (toPS s, toPS t) (by rw [leftSlots_toPS, rightSlots_toPS]; exact hst)
  exact h

/-- Transport of a placement along a card equality. -/
theorem Pl_eq_raw (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (r : ℕ) (hr : r ≤ N)
    (S : PlacementSubset r (N - r)) (s : Finset (Fin N)) (hs : s.card = r)
    (hS : castSlotSet (Nat.add_sub_of_le hr) S.1 = s) :
    Pl B N s = rawSubsetPlacement N r hr S (B r) := by
  subst hs
  have hS' : toPS s = S := by
    apply Subtype.ext
    show castSlotSet (Nat.add_sub_of_le (hcard s)).symm s = S.1
    have := castSlotSet_cancel' (Nat.add_sub_of_le hr) S.1
    rw [hS] at this
    exact this
  unfold Pl
  rw [hS']

/-- The placement subset with slot set `s`. -/
def mkPS (r : ℕ) (hr : r ≤ N) (s : Finset (Fin N)) (hs : s.card = r) : PlacementSubset r (N - r) :=
  ⟨castSlotSet (Nat.add_sub_of_le hr).symm s, by rw [card_castSlotSet]; exact hs⟩

theorem rawAvg_eq_sum (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (r : ℕ) (hr : r ≤ N) :
    rawSubsetAverage N r hr (B r) =
      ((N.choose r : ℂ)⁻¹) • ∑ s ∈ Finset.powersetCard r (Finset.univ : Finset (Fin N)), Pl B N s := by
  rw [rawSubsetAverage_eq_rawSubsetPlacementSum]
  congr 1
  unfold rawSubsetPlacementSum
  symm
  refine Finset.sum_bij (fun s hs => mkPS r hr s (Finset.mem_powersetCard.mp hs).2) ?_ ?_ ?_ ?_
  · intro s _; exact Finset.mem_univ _
  · intro s hs t ht h
    have h1 := congrArg Subtype.val h
    have h2 := congrArg (castSlotSet (Nat.add_sub_of_le hr)) h1
    unfold mkPS at h2
    simp only at h2
    rwa [castSlotSet_cancel, castSlotSet_cancel] at h2
  · intro S _
    have hc : (castSlotSet (Nat.add_sub_of_le hr) S.1).card = r := by
      rw [card_castSlotSet]; exact S.2
    refine ⟨castSlotSet (Nat.add_sub_of_le hr) S.1, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hc⟩
    · apply Subtype.ext
      show castSlotSet (Nat.add_sub_of_le hr).symm (castSlotSet (Nat.add_sub_of_le hr) S.1) = S.1
      rw [castSlotSet_cancel']
  · intro s hs
    exact Pl_eq_raw B r hr (mkPS r hr s (Finset.mem_powersetCard.mp hs).2) s
      (Finset.mem_powersetCard.mp hs).2 (castSlotSet_cancel _ s)

end Slots

/-! ### Permutation-conjugate form and adjoints -/

section Conj

variable {N : ℕ}

/-- Transport a permutation forward along an equality of slot counts. -/
def castPermFwd {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin n) :=
  ((Equiv.cast (congrArg Fin h)).symm.trans σ).trans (Equiv.cast (congrArg Fin h))

theorem castPermBack_castPermFwd {m n : ℕ} (h : m = n) (σ : Equiv.Perm (Fin m)) :
    castPermBack h (castPermFwd h σ) = σ := by
  subst h; ext x; simp [castPermBack, castPermFwd]

/-- Every placement is a permutation conjugate of the standard first-block placement (the permutation
depends only on the slot set, not on the kernel). -/
theorem raw_eq_conj (r : ℕ) (hr : r ≤ N) (S : PlacementSubset r (N - r)) :
    ∃ σ : Equiv.Perm (Fin N), ∀ A : BoundedSymmetricKernel H r,
      rawSubsetPlacement N r hr S A =
        ((permRep ℂ H N σ : Op H N).comp
          (castTensorOperator (Nat.add_sub_of_le hr) (firstPlacement (q := N - r) A))).comp
          (permRep ℂ H N σ⁻¹ : Op H N) := by
  refine ⟨castPermFwd (Nat.add_sub_of_le hr) (subsetRepresentative S), fun A => ?_⟩
  rw [castTensorOperator_conjugate, castPermBack_castPermFwd]
  rfl

/-- `T'` is the inner-product adjoint of `T`. -/
def IsAdj {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (T T' : X →L[ℂ] X) : Prop :=
  ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T' y⟫_ℂ

theorem IsAdj.mul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {T T' S S' : X →L[ℂ] X}
    (h : IsAdj T T') (h' : IsAdj S S') : IsAdj (T * S) (S' * T') := by
  intro x y
  show ⟪T (S x), y⟫_ℂ = ⟪x, S' (T' y)⟫_ℂ
  rw [h, h']

theorem IsAdj.one {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] :
    IsAdj (1 : X →L[ℂ] X) 1 := fun _ _ => rfl

theorem IsAdj.add {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {T T' S S' : X →L[ℂ] X}
    (h : IsAdj T T') (h' : IsAdj S S') : IsAdj (T + S) (T' + S') := by
  intro x y
  simp only [ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, h x y, h' x y]

theorem IsAdj.sub {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {T T' S S' : X →L[ℂ] X}
    (h : IsAdj T T') (h' : IsAdj S S') : IsAdj (T - S) (T' - S') := by
  intro x y
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right, h x y, h' x y]

theorem IsAdj.smul {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {T T' : X →L[ℂ] X}
    (h : IsAdj T T') (c : ℂ) : IsAdj (c • T) ((starRingEnd ℂ) c • T') := by
  intro x y
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, h x y]

theorem IsAdj.pow {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {T T' : X →L[ℂ] X}
    (h : IsAdj T T') : ∀ k : ℕ, IsAdj (T ^ k) (T' ^ k) := by
  intro k
  induction k with
  | zero => simpa using (IsAdj.one : IsAdj (1 : X →L[ℂ] X) 1)
  | succ k ih =>
    rw [pow_succ, pow_succ']
    exact ih.mul h

theorem IsAdj.sum {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ι : Type*}
    (s : Finset ι) (T T' : ι → (X →L[ℂ] X)) (h : ∀ i ∈ s, IsAdj (T i) (T' i)) :
    IsAdj (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro x y; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem isAdj_extend {r : ℕ} (A : BoundedSymmetricKernel H r) :
    IsAdj (extendSymKernel A) (extendSymKernel (ContinuousLinearMap.adjoint A)) := by
  intro x y
  have h1 : ⟪extendSymKernel A x, y⟫_ℂ = ⟪A (symProjToSector r x), symProjToSector r y⟫_ℂ := by
    show ⟪((A (symProjToSector r x) : SymSector ℂ H r) : HilbertTensorPower ℂ H r), y⟫_ℂ = _
    rw [inner_symProj_right (A (symProjToSector r x)).2, ← Submodule.coe_inner]
  have h2 : ⟪x, extendSymKernel (ContinuousLinearMap.adjoint A) y⟫_ℂ =
      ⟪symProjToSector r x, (ContinuousLinearMap.adjoint A) (symProjToSector r y)⟫_ℂ := by
    show ⟪x, (((ContinuousLinearMap.adjoint A) (symProjToSector r y) : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r)⟫_ℂ = _
    rw [← inner_conj_symm, inner_symProj_right ((ContinuousLinearMap.adjoint A)
      (symProjToSector r y)).2, inner_conj_symm, ← Submodule.coe_inner]
  rw [h1, h2, ContinuousLinearMap.adjoint_inner_right]

theorem isAdj_htmap {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {S S' : E →L[ℂ] E} {T T' : F →L[ℂ] F} (hS : IsAdj S S') (hT : IsAdj T T') :
    IsAdj (htmap S T) (htmap S' T') := by
  have hS' : S = ContinuousLinearMap.adjoint S' := (ContinuousLinearMap.eq_adjoint_iff S S').mpr hS
  have hT' : T = ContinuousLinearMap.adjoint T' := (ContinuousLinearMap.eq_adjoint_iff T T').mpr hT
  intro x y
  rw [hS', hT', ← adjoint_htmap, ContinuousLinearMap.adjoint_inner_left]

theorem isAdj_firstPlacement {p m : ℕ} (A : BoundedSymmetricKernel H p) :
    IsAdj (firstPlacement (q := m) A) (firstPlacement (q := m) (ContinuousLinearMap.adjoint A)) := by
  intro x y
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap]
  set e := splitIsometry (𝕜 := ℂ) (E := H) p m with he
  have hM : IsAdj (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)))
      (htmap (extendSymKernel (ContinuousLinearMap.adjoint A))
        (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m))) :=
    isAdj_htmap (isAdj_extend A) (fun x y => rfl)
  calc ⟪e.symm (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x)), y⟫_ℂ
      = ⟪e (e.symm (htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x))),
          e y⟫_ℂ := (e.inner_map_map _ _).symm
    _ = ⟪htmap (extendSymKernel A) (ContinuousLinearMap.id ℂ _) (e x), e y⟫_ℂ := by
        rw [e.apply_symm_apply]
    _ = ⟪e x, htmap (extendSymKernel (ContinuousLinearMap.adjoint A))
          (ContinuousLinearMap.id ℂ _) (e y)⟫_ℂ := hM _ _
    _ = _ := by
        have := e.inner_map_map x (e.symm (htmap (extendSymKernel (ContinuousLinearMap.adjoint A))
          (ContinuousLinearMap.id ℂ _) (e y)))
        rw [e.apply_symm_apply] at this
        exact this

theorem isAdj_cast {m n : ℕ} (h : m = n) {T T' : HilbertTensorPower ℂ H m →L[ℂ] HilbertTensorPower ℂ H m}
    (hT : IsAdj T T') : IsAdj (castTensorOperator h T) (castTensorOperator h T') := by
  cases h
  exact hT

theorem isAdj_perm (σ : Equiv.Perm (Fin N)) :
    IsAdj (permRep ℂ H N σ : Op H N) (permRep ℂ H N σ⁻¹ : Op H N) := by
  intro x y
  have h1 : (permRep ℂ H N σ : Op H N) ((permRep ℂ H N σ⁻¹ : Op H N) y) = y := by
    have := permRep_cancel (H := H) σ⁻¹ y
    rwa [inv_inv] at this
  calc ⟪(permRep ℂ H N σ : Op H N) x, y⟫_ℂ
      = ⟪(permRep ℂ H N σ : Op H N) x, (permRep ℂ H N σ : Op H N)
          ((permRep ℂ H N σ⁻¹ : Op H N) y)⟫_ℂ := by rw [h1]
    _ = _ := (permHilbertIsometry (𝕜 := ℂ) (E := H) σ).inner_map_map _ _

theorem isAdj_conj (σ : Equiv.Perm (Fin N)) {T T' : Op H N} (hT : IsAdj T T') :
    IsAdj ((permRep ℂ H N σ : Op H N).comp (T.comp (permRep ℂ H N σ⁻¹ : Op H N)))
      ((permRep ℂ H N σ : Op H N).comp (T'.comp (permRep ℂ H N σ⁻¹ : Op H N))) := by
  have h1 := isAdj_perm (H := H) (N := N) σ
  have h2 := isAdj_perm (H := H) (N := N) σ⁻¹
  rw [inv_inv] at h2
  have := (h1.mul hT).mul h2
  exact this

/-- The adjoint family of kernels. -/
def adjFam (B : ∀ r : ℕ, BoundedSymmetricKernel H r) : ∀ r : ℕ, BoundedSymmetricKernel H r :=
  fun r => ContinuousLinearMap.adjoint (B r)

theorem Pl_adj (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (s : Finset (Fin N)) :
    IsAdj (Pl B N s) (Pl (adjFam B) N s) := by
  obtain ⟨σ, hσ⟩ := raw_eq_conj (H := H) s.card (hcard s) (toPS s)
  unfold Pl adjFam
  rw [hσ, hσ]
  exact isAdj_conj σ (isAdj_cast _ (isAdj_firstPlacement _))

end Conj

/-! ### Rank-one projections and the isolated-vertex step -/

section RankOne

variable {N : ℕ}

theorem extend_coe {r : ℕ} (A : BoundedSymmetricKernel H r) (z : SymSector ℂ H r) :
    extendSymKernel A (z : HilbertTensorPower ℂ H r) =
      ((A z : SymSector ℂ H r) : HilbertTensorPower ℂ H r) := by
  have : symProjToSector r (z : HilbertTensorPower ℂ H r) = z := by
    apply Subtype.ext
    change symProj ℂ H r _ = _
    change groupAverage (permRep ℂ H r) _ = _
    exact groupAverage_apply_of_mem (permRep ℂ H r) z.2
  show ((SymSector ℂ H r).subtypeL (A (symProjToSector r _))) = _
  rw [this]; rfl

/-- `u^{⊗r}` as a vector of the symmetric sector. -/
def wvec (r : ℕ) (u : H) : SymSector ℂ H r := ⟨htpow r u, htpow_mem_symSector r u⟩

theorem inner_wvec (r : ℕ) (u : H) (hu : ‖u‖ = 1) : ⟪wvec r u, wvec r u⟫_ℂ = 1 := by
  have hn : ‖wvec r u‖ = 1 := by
    rw [← Submodule.norm_coe]
    show ‖(htpow r u : HilbertTensorPower ℂ H r)‖ = 1
    rw [norm_htpow, hu, one_pow]
  rw [inner_self_eq_norm_sq_to_K, hn]; norm_num

/-- The rank-one projection kernel `|u^{⊗r}⟩⟨u^{⊗r}|`. -/
def rk1 (r : ℕ) (u : H) : BoundedSymmetricKernel H r :=
  (innerSL ℂ (wvec r u)).smulRight (wvec r u)

theorem rk1_apply (r : ℕ) (u : H) (x : SymSector ℂ H r) :
    rk1 r u x = ⟪wvec r u, x⟫_ℂ • wvec r u := by
  simp [rk1]

theorem rk1_adjoint (r : ℕ) (u : H) : ContinuousLinearMap.adjoint (rk1 r u) = rk1 r u := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [rk1_apply, rk1_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem rk1_wvec (r : ℕ) (u : H) (hu : ‖u‖ = 1) : rk1 r u (wvec r u) = wvec r u := by
  rw [rk1_apply, inner_wvec r u hu, one_smul]

theorem rk1_kernel (r : ℕ) (u : H) (B : BoundedSymmetricKernel H r) :
    rk1 r u (B (wvec r u)) = ⟪wvec r u, B (wvec r u)⟫_ℂ • wvec r u := rk1_apply _ _ _

/-- The family of rank-one projections. -/
def rkFam (u : H) : ∀ r : ℕ, BoundedSymmetricKernel H r := fun r => rk1 r u

theorem adjFam_rkFam (u : H) : adjFam (rkFam u) = rkFam u := by
  funext r
  exact rk1_adjoint r u

theorem cIso_htpow {m n : ℕ} (h : m = n) (u : H) :
    cIso h (htpow m u : HilbertTensorPower ℂ H m) = htpow n u := by
  subst h; rfl

theorem cIso_symm_htpow {m n : ℕ} (h : m = n) (u : H) :
    (cIso h).symm (htpow n u : HilbertTensorPower ℂ H n) = htpow m u := by
  subst h; rfl

theorem firstPlacement_split_htmul (p m : ℕ) (A : BoundedSymmetricKernel H p)
    (v : HilbertTensorPower ℂ H p) (y : HilbertTensorPower ℂ H m) :
    firstPlacement (q := m) A ((splitIsometry (𝕜 := ℂ) (E := H) p m).symm (htmul v y)) =
      (splitIsometry (𝕜 := ℂ) (E := H) p m).symm (htmul (extendSymKernel A v) y) := by
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.apply_symm_apply, htmap_htmul,
    ContinuousLinearMap.id_apply]

/-- The first-block placement on the literal `N`-fold power. -/
def Cop (N r : ℕ) (hr : r ≤ N) (A : BoundedSymmetricKernel H r) : Op H N :=
  castTensorOperator (Nat.add_sub_of_le hr) (firstPlacement (q := N - r) A)

theorem split_symm_htmul_htpow (r q : ℕ) (u : H) :
    (splitIsometry (𝕜 := ℂ) (E := H) r q).symm
      (htmul (htpow r u : HilbertTensorPower ℂ H r) (htpow q u : HilbertTensorPower ℂ H q)) =
      (htpow (r + q) u : HilbertTensorPower ℂ H (r + q)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, split_htpow]

theorem Cop_rk1_htpow (N r : ℕ) (hr : r ≤ N) (u : H) (hu : ‖u‖ = 1) :
    Cop N r hr (rk1 r u) (htpow N u : HilbertTensorPower ℂ H N) = htpow N u := by
  unfold Cop
  rw [castTensorOperator_eq_conj, cIso_symm_htpow, firstPlacement_htpow]
  have : ((rk1 r u ⟨htpow r u, htpow_mem_symSector r u⟩ : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r) = htpow r u := by
    have := rk1_wvec r u hu
    exact congrArg Subtype.val this
  rw [this, split_symm_htmul_htpow, cIso_htpow]

theorem Cop_rk1_Cop (N r : ℕ) (hr : r ≤ N) (u : H) (hu : ‖u‖ = 1) (B : BoundedSymmetricKernel H r) :
    Cop N r hr (rk1 r u) (Cop N r hr B (htpow N u : HilbertTensorPower ℂ H N)) =
      kernelProductSymbol B u • (htpow N u : HilbertTensorPower ℂ H N) := by
  unfold Cop
  rw [castTensorOperator_eq_conj, castTensorOperator_eq_conj, LinearIsometryEquiv.symm_apply_apply,
    cIso_symm_htpow, firstPlacement_htpow, firstPlacement_split_htmul, extend_coe]
  have h1 : ((rk1 r u (B ⟨htpow r u, htpow_mem_symSector r u⟩) : SymSector ℂ H r) :
      HilbertTensorPower ℂ H r) = kernelProductSymbol B u • (htpow r u : HilbertTensorPower ℂ H r) := by
    have := rk1_kernel r u B
    have h2 := congrArg Subtype.val this
    exact h2
  rw [h1, htmul_smul_left, map_smul, split_symm_htmul_htpow, map_smul, cIso_htpow]

theorem Pl_rk1_htpow (u : H) (hu : ‖u‖ = 1) (s : Finset (Fin N)) :
    Pl (rkFam u) N s (htpow N u : HilbertTensorPower ℂ H N) = htpow N u := by
  obtain ⟨σ, hσ⟩ := raw_eq_conj (H := H) s.card (hcard s) (toPS s)
  unfold Pl
  rw [hσ]
  simp only [ContinuousLinearMap.comp_apply]
  rw [permRep_htpow σ⁻¹ u]
  have := Cop_rk1_htpow N s.card (hcard s) u hu
  unfold Cop at this
  show (permRep ℂ H N σ : Op H N) (castTensorOperator _ _ (htpow N u)) = _
  rw [rkFam] at *
  rw [this, permRep_htpow]

theorem Pl_rk1_Pl (u : H) (hu : ‖u‖ = 1) (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (s : Finset (Fin N)) :
    Pl (rkFam u) N s (Pl B N s (htpow N u : HilbertTensorPower ℂ H N)) =
      kernelProductSymbol (B s.card) u • (htpow N u : HilbertTensorPower ℂ H N) := by
  obtain ⟨σ, hσ⟩ := raw_eq_conj (H := H) s.card (hcard s) (toPS s)
  unfold Pl
  rw [hσ, hσ]
  simp only [ContinuousLinearMap.comp_apply]
  rw [permRep_htpow σ⁻¹ u, permRep_cancel]
  have := Cop_rk1_Cop N s.card (hcard s) u hu (B s.card)
  unfold Cop at this
  show (permRep ℂ H N σ : Op H N) (castTensorOperator _ _ (castTensorOperator _ _ (htpow N u))) = _
  rw [rkFam]
  rw [this, map_smul, permRep_htpow]

theorem Pl_rk1_isAdj (u : H) (s : Finset (Fin N)) :
    IsAdj (Pl (rkFam u) N s) (Pl (rkFam u) N s) := by
  have := Pl_adj (rkFam u) s
  rwa [adjFam_rkFam] at this

end RankOne

section Word

variable {N : ℕ}

/-- The centered placement `Pl B s − ⟨u^r, B_r u^r⟩ · 1`, `r = |s|`. -/
def Tf (u : H) (B : ∀ r : ℕ, BoundedSymmetricKernel H r) (N : ℕ) (s : Finset (Fin N)) : Op H N :=
  Pl B N s - (QuantumNLS.HighMomentsRank.aa u B s.card) • (1 : Op H N)

theorem commute_center {X : Type*} [Ring X] [Algebra ℂ X] {x y : X} (h : Commute x y) (a b : ℂ) :
    Commute (x - a • 1) (y - b • 1) := by
  have h1 : Commute x (y - b • 1) := h.sub_right (Commute.smul_right (Commute.one_right x) b)
  exact h1.sub_left (Commute.smul_left (Commute.one_left (y - b • 1)) a)

theorem Tf_commute (u : H) (B B' : ∀ r : ℕ, BoundedSymmetricKernel H r) (s t : Finset (Fin N))
    (hst : Disjoint s t) : Commute (Tf u B N s) (Tf u B' N t) :=
  commute_center (Pl_commute_of_disjoint B B' s t hst) _ _

theorem Pl_Tf_commute (B B' : ∀ r : ℕ, BoundedSymmetricKernel H r) (u : H) (s t : Finset (Fin N))
    (hst : Disjoint s t) : Commute (Pl B N s) (Tf u B' N t) := by
  unfold Tf
  exact (Pl_commute_of_disjoint B B' s t hst).sub_right
    (Commute.smul_right (Commute.one_right _) _)

/-- **Isolated-vertex step.** In a word of centered placements, a position whose slot set is disjoint from
all the others has vanishing product-state expectation. -/
theorem word_iso {m : ℕ} (u : H) (hu : ‖u‖ = 1) (B : Fin (m + 1) → ∀ r : ℕ, BoundedSymmetricKernel H r)
    (s : Fin (m + 1) → Finset (Fin N)) (j : Fin (m + 1))
    (hj : ∀ i, i ≠ j → Disjoint (s j) (s i)) :
    ⟪(htpow N u : HilbertTensorPower ℂ H N),
      wprod (m + 1) (fun i => Tf u (B i) N (s i)) (htpow N u)⟫_ℂ = 0 := by
  refine wprod_inner_eq_zero (fun i => Tf u (B i) N (s i)) j (Pl (rkFam u) N (s j)) (htpow N u)
    (Pl_rk1_isAdj u (s j)) (Pl_rk1_htpow u hu (s j)) ?_ ?_ ?_
  · intro i hi
    exact (Tf_commute u (B j) (B i) (s j) (s i) (hj i hi)).symm
  · intro i hi
    exact Pl_Tf_commute (rkFam u) (B i) u (s j) (s i) (hj i hi)
  · show Pl (rkFam u) N (s j) (Tf u (B j) N (s j) (htpow N u)) = 0
    unfold Tf
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul]
    rw [Pl_rk1_Pl u hu (B j) (s j), Pl_rk1_htpow u hu (s j)]
    simp [QuantumNLS.HighMomentsRank.aa]

end Word

#print axioms word_iso
#print axioms Pl_adj
#print axioms rawAvg_eq_sum

end QuantumNLS.HighMomentsOps
