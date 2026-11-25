import QuantumNLS.Local014RealSymbol
import QuantumNLS.Ext025A12PartialTrace
import QuantumNLS.MixedTraceNorm

/-!
# LOCAL-014 stage E4b: normal states, reduced density matrices, and the trace-distance estimate

Source: `source-text/chapters/local/quantum_periods.tex:173-182` (conventions before LOCAL-014):
"A normal state below is a positive trace-class operator of trace one. Its `q`-body reduced
density matrix is normalized to have trace one, so that `Tr(γ_N^{(q)} B) = Tr(ρ_N Q_{N,q}(B))`."
and `:231-236` (proof of LOCAL-014): "For a positive trace-one matrix `γ` and rank-one `P_w`,
`‖γ − P_w‖₁ ≤ 2 √(1 − Tr(γ P_w))`."

Realized objects (frozen, read-only): GP-09 `Ext025A12PartialTrace.partialTrace` (partial trace
over the second Hilbert factor, with `partialTrace_duality`, `partialTrace_unique`,
`partialTrace_positive`, `partialTrace_trace`); DEF-041 `RadiusBound.Q`; `MixedTraceNorm.symKernel`
and `inner_U_eq_inner_htmap`; `IntrinsicContact.oneEquiv : H ≃ₗᵢ H^{⊗̂1}`; `Fidelity.fidelity_series`.

* `lift J T = J T J†` along a linear isometry `J`; `exists_basis_lift` (a Hilbert basis of the
  target extending `J(c)`), `posTrace_lift`, `traceNorm_lift`, `tr_mul_lift`
  (`Tr(X J T J†) = Tr(J†XJ T)` for positive trace-class `T`);
* `IsNormalState ρ`: positive, trace class, `Tr ρ = 1`;
* `reduced j m ρ`: the `j`-body reduced density matrix of `ρ` on `Sym^{j+m}`, the GP-09 partial
  trace of the ambient lift along `Sym^{j+m} ⊂ H^{⊗̂(j+m)} ≃ H^{⊗̂j} ⊗̂ H^{⊗̂m}`;
  `compress_eq_Q_N_p` (`J† (S ⊗̂ 1) J = Q(P S P)`), `tr_reduced_mul` (the line-176 normalization),
  `eq_reduced_of_duality` (uniqueness, by `partialTrace_unique`), positivity, trace one;
* `reducedN N j`, `oneBody N ρ : H →L H` (transported along `H ≃ H^{⊗̂1}`), `toSym1`;
  `tr_oneBody_mul` (`Tr(γ^{(1)}_N A) = Tr(ρ_N Q_{N,1}(A))`), `eq_oneBody_of_duality`
  (the line-176 normalization characterizes the one-body matrix, via `partialTrace_unique`),
  `oneBody_isPositive`, `oneBody_isTraceClass`, `tr_oneBody`;
* `traceNorm_oneBody_sub_le`: `‖γ^{(1)}_N − |w⟩⟨w|‖₁ ≤ 2√(1 − ⟨w, γ^{(1)}_N w⟩)` (frozen
  `Fidelity.fidelity_series`), and `re_inner_oneBody_eq` (`⟨w, γ^{(1)}_N w⟩ = Tr(ρ_N Q_{N,1}(P_w))`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal
open Filter Topology
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.Ext025B11TracePairing
  QuantumNLS.Ext025B11TraceBasis QuantumNLS.Ext025A12Trace QuantumNLS.Ext025A12Normal
  QuantumNLS.KernelDefinition QuantumNLS.TensorPlacements

namespace QuantumNLS.Local014OneBody

section Lift

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The lift `J T J†` of an operator along a linear isometry `J`. -/
def lift (J : E →ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : F →L[ℂ] F :=
  J.toContinuousLinearMap ∘L T ∘L J.toContinuousLinearMap.adjoint

theorem adjoint_iso_apply (J : E →ₗᵢ[ℂ] F) (x : E) :
    J.toContinuousLinearMap.adjoint (J x) = x := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact J.inner_map_map y x

theorem adjoint_comp_iso (J : E →ₗᵢ[ℂ] F) :
    J.toContinuousLinearMap.adjoint ∘L J.toContinuousLinearMap = ContinuousLinearMap.id ℂ E := by
  ext x
  exact adjoint_iso_apply J x

/-- A Hilbert basis of `F` extending the orthonormal family `J ∘ c`; every sum of a function
vanishing on `ker J†` over it reduces to the sum over `c`. -/
theorem exists_basis_lift (J : E →ₗᵢ[ℂ] F) {ι : Type*} (c : HilbertBasis ι ℂ E) :
    ∃ (w : Set F) (b : HilbertBasis w ℂ F), ∀ {α : Type} [AddCommMonoid α] [TopologicalSpace α]
      (f : F → α), (∀ y, J.toContinuousLinearMap.adjoint y = 0 → f y = 0) →
        ∑' x, f (b x) = ∑' i, f (J (c i)) := by
  have hJc : Orthonormal ℂ (J ∘ c) := c.orthonormal.comp_linearIsometry J
  have hinj : Function.Injective (J ∘ c) := hJc.linearIndependent.injective
  have hs : Orthonormal ℂ ((↑) : Set.range (J ∘ c) → F) := (orthonormal_subtype_range hinj).2 hJc
  obtain ⟨w, b, hsw, hb⟩ := hs.exists_hilbertBasis_extension
  refine ⟨w, b, fun {α} _ _ f hf => ?_⟩
  let g : ι → w := fun i => ⟨J (c i), hsw ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun i k h => hinj (congrArg Subtype.val h)
  have hbg : ∀ i, b (g i) = J (c i) := fun i => by rw [hb]
  have key : ∀ x : w, x ∉ Set.range g → J.toContinuousLinearMap.adjoint (b x) = 0 := by
    intro x hx
    set y := J.toContinuousLinearMap.adjoint (b x) with hy
    have h0 : ∀ i, ⟪c i, y⟫_ℂ = 0 := by
      intro i
      rw [hy, ContinuousLinearMap.adjoint_inner_right]
      have hne : g i ≠ x := fun h => hx ⟨i, h⟩
      have h1 : ⟪b (g i), b x⟫_ℂ = 0 := b.orthonormal.2 hne
      rw [hbg] at h1
      simpa using h1
    have hyy : ⟪y, y⟫_ℂ = 0 := by
      rw [← c.tsum_inner_mul_inner y y]
      simp [h0]
    exact inner_self_eq_zero.mp hyy
  have hsupp : Function.support (fun x : w => f (b x)) ⊆ Set.range g := by
    intro x hx
    by_contra h
    exact hx (hf _ (key x h))
  rw [← hg.tsum_eq hsupp]
  exact tsum_congr fun i => by rw [hbg]

theorem lift_isPositive (J : E →ₗᵢ[ℂ] F) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    (lift J T).IsPositive :=
  hT.conj_adjoint _

theorem posTrace_lift (J : E →ₗᵢ[ℂ] F) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    posTrace (lift J T) = posTrace T := by
  obtain ⟨w, b, hb⟩ := exists_basis_lift J (refBasis E)
  rw [posTrace_eq b (lift_isPositive J hT), posTrace_eq (refBasis E) hT]
  unfold traceIn
  rw [hb (fun y => ENNReal.ofReal (RCLike.re ⟪y, lift J T y⟫_ℂ)) ?_]
  · refine tsum_congr fun i => ?_
    simp only [lift, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      adjoint_iso_apply, LinearIsometry.inner_map_map]
  · intro y hy
    simp [lift, hy]

theorem traceNorm_lift (J : E →ₗᵢ[ℂ] F) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    traceNorm (lift J T) = traceNorm T := by
  rw [traceNorm_of_isPositive (lift_isPositive J hT), traceNorm_of_isPositive hT,
    posTrace_lift J hT]

theorem lift_isTraceClass (J : E →ₗᵢ[ℂ] F) {T : E →L[ℂ] E} (hT : T.IsPositive)
    (ht : IsTraceClass T) : IsTraceClass (lift J T) := by
  unfold IsTraceClass
  rw [traceNorm_lift J hT]
  exact ht

theorem isTraceClass_mul_left (K : E →L[ℂ] E) {T : E →L[ℂ] E} (ht : IsTraceClass T) :
    IsTraceClass (K * T) :=
  lt_top_iff_ne_top.mpr (finite_left K T ht.ne)

/-- Cyclicity of the trace against a trace-class factor. -/
theorem tr_comm (A : E →L[ℂ] E) {T : E →L[ℂ] E} (ht : IsTraceClass T) :
    tr (A * T) = tr (T * A) :=
  trace_cycle (refBasis E) A T ht

/-- `Tr(X J T J†) = Tr(J† X J T)` for positive trace-class `T`. -/
theorem tr_mul_lift (J : E →ₗᵢ[ℂ] F) {T : E →L[ℂ] E} (hT : T.IsPositive) (ht : IsTraceClass T)
    (X : F →L[ℂ] F) :
    tr (X * lift J T) =
      tr ((J.toContinuousLinearMap.adjoint ∘L X ∘L J.toContinuousLinearMap) * T) := by
  obtain ⟨w, b, hb⟩ := exists_basis_lift J (refBasis E)
  rw [tr_eq b _ (isTraceClass_mul_left X (lift_isTraceClass J hT ht)),
    tr_eq (refBasis E) _ (isTraceClass_mul_left _ ht)]
  unfold trace
  rw [hb (fun y => ⟪y, (X * lift J T) y⟫_ℂ) ?_]
  · refine tsum_congr fun i => ?_
    simp only [lift, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, adjoint_iso_apply]
    rw [ContinuousLinearMap.adjoint_inner_right]
    rfl
  · intro y hy
    simp [lift, hy]

end Lift

section States

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A normal state: a positive trace-class operator of trace one (source line 173). -/
def IsNormalState (ρ : E →L[ℂ] E) : Prop :=
  ρ.IsPositive ∧ IsTraceClass ρ ∧ tr ρ = 1

theorem posTrace_eq_one_of_tr {ρ : E →L[ℂ] E} (hp : ρ.IsPositive) (ht : IsTraceClass ρ)
    (h1 : tr ρ = 1) : posTrace ρ = 1 := by
  have h := trace_positive (refBasis E) ρ hp
  change tr ρ = _ at h
  rw [h1] at h
  have hr : (posTrace ρ).toReal = 1 := by exact_mod_cast h.symm
  have hf : posTrace ρ ≠ ⊤ := by rw [← traceNorm_of_isPositive hp]; exact ht.ne
  rw [← ENNReal.ofReal_toReal hf, hr, ENNReal.ofReal_one]

/-- The printed trace-distance estimate, from the frozen `Fidelity.fidelity_series`. -/
theorem traceNorm_sub_rankOne_le {γ : E →L[ℂ] E} (hγ : IsNormalState γ) (w : E) (hw : ‖w‖ = 1) :
    traceNorm (γ - InnerProductSpace.rankOne ℂ w w) ≤
      ENNReal.ofReal (2 * √(1 - RCLike.re ⟪w, γ w⟫_ℂ)) :=
  Fidelity.fidelity_series γ hγ.1 hγ.2.1 (posTrace_eq_one_of_tr hγ.1 hγ.2.1 hγ.2.2) w hw

theorem traceNorm_eq_one {ρ : E →L[ℂ] E} (hρ : IsNormalState ρ) : traceNorm ρ = 1 := by
  rw [traceNorm_of_isPositive hρ.1, posTrace_eq_one_of_tr hρ.1 hρ.2.1 hρ.2.2]

/-- `|Tr(ρ X)| ≤ ‖X‖` for a normal state. -/
theorem norm_tr_mul_le {ρ : E →L[ℂ] E} (hρ : IsNormalState ρ) (X : E →L[ℂ] E) :
    ‖tr (ρ * X)‖ ≤ ‖X‖ := by
  rw [← tr_comm X hρ.2.1]
  have h := pairing_bound (refBasis E) X ρ hρ.2.1.ne
  rw [traceNorm_eq_one hρ, ENNReal.toReal_one, mul_one] at h
  exact h

end States

section Reduced

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `Sym^{j+m} H ⊂ H^{⊗̂(j+m)} ≃ H^{⊗̂j} ⊗̂ H^{⊗̂m}`. -/
def splitSym (j m : ℕ) : SymSector ℂ H (j + m) →ₗᵢ[ℂ]
    HilbertTensor ℂ (HilbertTensorPower ℂ H j) (HilbertTensorPower ℂ H m) :=
  (splitIsometry (𝕜 := ℂ) (E := H) j m).toLinearIsometry.comp
    (SymSector ℂ H (j + m)).subtypeₗᵢ

open scoped Classical in
/-- The `j`-body reduced density matrix of `ρ` on `Sym^{j+m}`: the GP-09 partial trace (over the
last `m` factors) of the ambient lift of `ρ`. -/
def reduced (j m : ℕ) (ρ : SymSector ℂ H (j + m) →L[ℂ] SymSector ℂ H (j + m)) :
    HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j :=
  if h : IsTraceClass (lift (splitSym j m) ρ) then Ext025A12PartialTrace.partialTrace _ h else 0

/-- `J† (S ⊗̂ 1) J = Q(P S P)` on `Sym^{j+m}`. -/
theorem compress_eq_Q_N_p (j m : ℕ) (S : HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j) :
    (splitSym j m).toContinuousLinearMap.adjoint ∘L ampliate ℂ _ _ S ∘L
        (splitSym j m).toContinuousLinearMap =
      Q_N_p (q := m) (MixedTraceNorm.symKernel S) := by
  rw [← U_N_r_eq_Q_N_p]
  set D := (splitSym (H := H) j m).toContinuousLinearMap.adjoint ∘L ampliate ℂ _ _ S ∘L
        (splitSym j m).toContinuousLinearMap - U_N_r (r := j) (q := m) (MixedTraceNorm.symKernel S)
  have hD : D = 0 := by
    have h := (inner_map_self_eq_zero (D : SymSector ℂ H (j + m) →ₗ[ℂ] SymSector ℂ H (j + m))).1
    have h0 : (D : SymSector ℂ H (j + m) →ₗ[ℂ] SymSector ℂ H (j + m)) = 0 := by
      apply h
      intro x
      have hx := MixedTraceNorm.inner_U_eq_inner_htmap j m x S
      have e1 : ⟪x, ((splitSym (H := H) j m).toContinuousLinearMap.adjoint ∘L ampliate ℂ _ _ S ∘L
          (splitSym j m).toContinuousLinearMap) x⟫_ℂ =
          ⟪x, U_N_r (r := j) (q := m) (MixedTraceNorm.symKernel S) x⟫_ℂ := by
        rw [hx, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
        rfl
      change ⟪D x, x⟫_ℂ = 0
      rw [← inner_conj_symm]
      simp only [D, ContinuousLinearMap.sub_apply, inner_sub_right, e1, sub_self, map_zero]
    exact ContinuousLinearMap.coe_injective h0
  exact sub_eq_zero.mp hD

variable (j m : ℕ) {ρ : SymSector ℂ H (j + m) →L[ℂ] SymSector ℂ H (j + m)}

theorem lift_splitSym_isTraceClass (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    IsTraceClass (lift (splitSym (H := H) j m) ρ) :=
  lift_isTraceClass _ hp ht

theorem reduced_eq (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    reduced j m ρ = Ext025A12PartialTrace.partialTrace _ (lift_splitSym_isTraceClass j m hp ht) := by
  rw [reduced, dif_pos (lift_splitSym_isTraceClass j m hp ht)]

/-- The line-176 normalization: `Tr(γ^{(j)} S) = Tr(ρ Q_{j+m,j}(P S P))`. -/
theorem tr_reduced_mul (hp : ρ.IsPositive) (ht : IsTraceClass ρ)
    (S : HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j) :
    tr (reduced j m ρ * S) = tr (ρ * Q_N_p (q := m) (MixedTraceNorm.symKernel S)) := by
  have hL := lift_splitSym_isTraceClass j m hp ht
  rw [reduced_eq j m hp ht, Ext025A12PartialTrace.partialTrace_duality, ← tr_comm _ hL,
    tr_mul_lift _ hp ht, compress_eq_Q_N_p, tr_comm _ ht]

theorem reduced_isPositive (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    (reduced j m ρ).IsPositive := by
  rw [reduced_eq j m hp ht]
  exact Ext025A12PartialTrace.partialTrace_positive _ _ (lift_isPositive _ hp)

theorem reduced_isTraceClass (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    IsTraceClass (reduced j m ρ) := by
  rw [reduced_eq j m hp ht]
  exact Ext025A12PartialTrace.partialTrace_isTraceClass _ _

theorem tr_reduced (hp : ρ.IsPositive) (ht : IsTraceClass ρ) : tr (reduced j m ρ) = tr ρ := by
  have hL := lift_splitSym_isTraceClass j m hp ht
  rw [reduced_eq j m hp ht, Ext025A12PartialTrace.partialTrace_trace]
  have h := tr_mul_lift (splitSym (H := H) j m) hp ht 1
  rw [one_mul] at h
  rw [h, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, adjoint_comp_iso,
    ← ContinuousLinearMap.one_def, one_mul]

/-- Uniqueness of the line-176 normalization, via GP-09 `partialTrace_unique`. -/
theorem eq_reduced_of_duality (hp : ρ.IsPositive) (ht : IsTraceClass ρ)
    (S : HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j) (hS : IsTraceClass S)
    (h : ∀ A : HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j,
      tr (S * A) = tr (ρ * Q_N_p (q := m) (MixedTraceNorm.symKernel A))) :
    S = reduced j m ρ := by
  have hL := lift_splitSym_isTraceClass j m hp ht
  rw [reduced_eq j m hp ht]
  refine Ext025A12PartialTrace.partialTrace_unique _ hL S hS fun A => ?_
  rw [h A, ← compress_eq_Q_N_p, ← tr_comm _ ht, ← tr_mul_lift _ hp ht, tr_comm _ hL]

end Reduced

section Cast

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem cast_mul {a b : ℕ} (h : a = b) (A B : SymSector ℂ H a →L[ℂ] SymSector ℂ H a) :
    castSymSectorOperator h (A * B) = castSymSectorOperator h A * castSymSectorOperator h B := by
  subst h; rfl

theorem cast_symm_cast {a b : ℕ} (h : a = b) (A : SymSector ℂ H b →L[ℂ] SymSector ℂ H b) :
    castSymSectorOperator h (castSymSectorOperator h.symm A) = A := by
  subst h; rfl

theorem tr_cast {a b : ℕ} (h : a = b) (A : SymSector ℂ H a →L[ℂ] SymSector ℂ H a) :
    tr (castSymSectorOperator h A) = tr A := by
  subst h; rfl

theorem cast_isPositive {a b : ℕ} (h : a = b) {A : SymSector ℂ H a →L[ℂ] SymSector ℂ H a}
    (hA : A.IsPositive) : (castSymSectorOperator h A).IsPositive := by
  subst h; exact hA

theorem cast_isTraceClass {a b : ℕ} (h : a = b) {A : SymSector ℂ H a →L[ℂ] SymSector ℂ H a}
    (hA : IsTraceClass A) : IsTraceClass (castSymSectorOperator h A) := by
  subst h; exact hA

/-- `j`-body reduced density matrix of a state on `Sym^N`, `j ≤ N` (cast along `j+(N−j) = N`). -/
def reducedN (N j : ℕ) (hj : j ≤ N) (ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j :=
  reduced j (N - j) (castSymSectorOperator (Nat.add_sub_of_le hj).symm ρ)

variable {N j : ℕ} (hj : j ≤ N) {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N}

/-- `Tr(γ_N^{(j)} S) = Tr(ρ_N Q_{N,j}(P S P))` (source line 176). -/
theorem tr_reducedN_mul (hp : ρ.IsPositive) (ht : IsTraceClass ρ)
    (S : HilbertTensorPower ℂ H j →L[ℂ] HilbertTensorPower ℂ H j) :
    tr (reducedN N j hj ρ * S) = tr (ρ * RadiusBound.Q N j hj (MixedTraceNorm.symKernel S)) := by
  have h := Nat.add_sub_of_le hj
  rw [reducedN, tr_reduced_mul j (N - j) (cast_isPositive h.symm hp) (cast_isTraceClass h.symm ht),
    RadiusBound.Q, ← tr_cast h, cast_mul, cast_symm_cast]

theorem tr_mul_cast {a b : ℕ} (h : a = b) (ρ : SymSector ℂ H b →L[ℂ] SymSector ℂ H b)
    (X : SymSector ℂ H a →L[ℂ] SymSector ℂ H a) :
    tr (ρ * castSymSectorOperator h X) = tr (castSymSectorOperator h.symm ρ * X) := by
  subst h; rfl

theorem reducedN_isPositive (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    (reducedN N j hj ρ).IsPositive :=
  reduced_isPositive _ _ (cast_isPositive _ hp) (cast_isTraceClass _ ht)

theorem reducedN_isTraceClass (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    IsTraceClass (reducedN N j hj ρ) :=
  reduced_isTraceClass _ _ (cast_isPositive _ hp) (cast_isTraceClass _ ht)

theorem tr_reducedN (hp : ρ.IsPositive) (ht : IsTraceClass ρ) : tr (reducedN N j hj ρ) = tr ρ := by
  rw [reducedN, tr_reduced _ _ (cast_isPositive _ hp) (cast_isTraceClass _ ht), tr_cast]

theorem reducedN_isNormalState (hρ : IsNormalState ρ) : IsNormalState (reducedN N j hj ρ) :=
  ⟨reducedN_isPositive hj hρ.1 hρ.2.1, reducedN_isTraceClass hj hρ.1 hρ.2.1,
    (tr_reducedN hj hρ.1 hρ.2.1).trans hρ.2.2⟩

end Cast

section OneBody

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `H^{⊗̂1} → H`. -/
def fromOne : HilbertTensorPower ℂ H 1 →ₗᵢ[ℂ] H :=
  (IntrinsicContact.oneEquiv (E := H)).symm.toLinearIsometry

/-- An operator `A` on `H` as a kernel on `Sym^1 H` (`H ≃ H^{⊗̂1} = Sym^1 H`). -/
def toSym1 (A : H →L[ℂ] H) : BoundedSymmetricKernel H 1 :=
  MixedTraceNorm.symKernel
    ((fromOne (H := H)).toContinuousLinearMap.adjoint ∘L A ∘L (fromOne (H := H)).toContinuousLinearMap)

/-- The one-body matrix `γ_N^{(1)}` of `ρ` on `Sym^N`, as an operator on `H` (`0` for `N = 0`). -/
def oneBody (N : ℕ) (ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) : H →L[ℂ] H :=
  if hN : 1 ≤ N then lift fromOne (reducedN N 1 hN ρ) else 0

variable {N : ℕ} {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N}

theorem oneBody_eq (hN : 1 ≤ N) : oneBody N ρ = lift fromOne (reducedN N 1 hN ρ) := by
  rw [oneBody, dif_pos hN]

/-- **Source line 176** for `q = 1`: `Tr(γ_N^{(1)} A) = Tr(ρ_N Q_{N,1}(A))`. -/
theorem tr_oneBody_mul (hN : 1 ≤ N) (hp : ρ.IsPositive) (ht : IsTraceClass ρ) (A : H →L[ℂ] H) :
    tr (oneBody N ρ * A) = tr (ρ * RadiusBound.Q N 1 hN (toSym1 A)) := by
  have hr := reducedN_isPositive hN hp ht
  have hrt := reducedN_isTraceClass hN hp ht
  rw [oneBody_eq hN, ← tr_comm _ (lift_isTraceClass _ hr hrt), tr_mul_lift _ hr hrt,
    tr_comm _ hrt, tr_reducedN_mul hN hp ht]
  rfl

theorem oneBody_isPositive (hN : 1 ≤ N) (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    (oneBody N ρ).IsPositive := by
  rw [oneBody_eq hN]
  exact lift_isPositive _ (reducedN_isPositive hN hp ht)

theorem oneBody_isTraceClass (hN : 1 ≤ N) (hp : ρ.IsPositive) (ht : IsTraceClass ρ) :
    IsTraceClass (oneBody N ρ) := by
  rw [oneBody_eq hN]
  exact lift_isTraceClass _ (reducedN_isPositive hN hp ht) (reducedN_isTraceClass hN hp ht)

theorem tr_oneBody (hN : 1 ≤ N) (hp : ρ.IsPositive) (ht : IsTraceClass ρ) : tr (oneBody N ρ) = tr ρ := by
  have hr := reducedN_isPositive hN hp ht
  have hrt := reducedN_isTraceClass hN hp ht
  have h := tr_mul_lift (fromOne (H := H)) hr hrt 1
  rw [one_mul] at h
  rw [oneBody_eq hN, h, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, adjoint_comp_iso,
    ← ContinuousLinearMap.one_def, one_mul, tr_reducedN hN hp ht]

theorem oneBody_isNormalState (hN : 1 ≤ N) (hρ : IsNormalState ρ) : IsNormalState (oneBody N ρ) :=
  ⟨oneBody_isPositive hN hρ.1 hρ.2.1, oneBody_isTraceClass hN hρ.1 hρ.2.1,
    (tr_oneBody hN hρ.1 hρ.2.1).trans hρ.2.2⟩

/-- `⟨w, γ_N^{(1)} w⟩ = Tr(ρ_N Q_{N,1}(|w⟩⟨w|))`. -/
theorem inner_oneBody_eq (hN : 1 ≤ N) (hp : ρ.IsPositive) (ht : IsTraceClass ρ) (w : H) :
    ⟪w, oneBody N ρ w⟫_ℂ =
      tr (ρ * RadiusBound.Q N 1 hN (toSym1 (InnerProductSpace.rankOne ℂ w w))) := by
  rw [← tr_oneBody_mul hN hp ht]
  exact (trace_rankOne_left (refBasis H) (oneBody N ρ) w w).symm

/-- The symbol of `toSym1 A` is the quadratic form of `A`. -/
theorem kernelProductSymbol_toSym1 (A : H →L[ℂ] H) (u : H) :
    kernelProductSymbol (toSym1 A) u = ⟪u, A u⟫_ℂ := by
  unfold kernelProductSymbol toSym1 MixedTraceNorm.symKernel
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  change ⟪(htpow 1 u : HilbertTensorPower ℂ H 1), symProj ℂ H 1 _⟫_ℂ = _
  have hs : ∀ y : HilbertTensorPower ℂ H 1,
      ⟪(htpow 1 u : HilbertTensorPower ℂ H 1), symProj ℂ H 1 y⟫_ℂ =
        ⟪(htpow 1 u : HilbertTensorPower ℂ H 1), y⟫_ℂ := by
    intro y
    have h1 := ContinuousLinearMap.adjoint_inner_left (symProj ℂ H 1) y
      (htpow 1 u : HilbertTensorPower ℂ H 1)
    rw [MixedTraceNorm.symProj_adjoint, symProj_eq_starProjection,
      (Submodule.starProjection_eq_self_iff (K := SymSector ℂ H 1)).mpr
        (htpow_mem_symSector 1 u)] at h1
    rw [symProj_eq_starProjection]
    exact h1.symm
  rw [hs]
  refine (ContinuousLinearMap.adjoint_inner_right _ _ _).trans ?_
  simp only [fromOne, LinearIsometry.coe_toContinuousLinearMap,
    LinearIsometryEquiv.coe_toLinearIsometry, IntrinsicContact.oneEquiv_symm_htpow]

/-- **Line-176 normalization characterizes the one-body matrix**: a positive trace-class `γ` on
`H` with `Tr(γ A) = Tr(ρ_N Q_{N,1}(A))` for every bounded `A` is `oneBody N ρ`.  The proof
transports `γ` to `H^{⊗̂1}` and applies GP-09 `partialTrace_unique` (`eq_reduced_of_duality`). -/
theorem eq_oneBody_of_duality (hN : 1 ≤ N) (hp : ρ.IsPositive) (ht : IsTraceClass ρ)
    (γ : H →L[ℂ] H) (hγp : γ.IsPositive) (hγt : IsTraceClass γ)
    (h : ∀ A : H →L[ℂ] H, tr (γ * A) = tr (ρ * RadiusBound.Q N 1 hN (toSym1 A))) :
    γ = oneBody N ρ := by
  set e : H →ₗᵢ[ℂ] HilbertTensorPower ℂ H 1 :=
    (IntrinsicContact.oneEquiv (E := H)).toLinearIsometry with he
  have hfe : ∀ x, fromOne (e x) = x := fun x => (IntrinsicContact.oneEquiv (E := H)).symm_apply_apply x
  have hef : ∀ y, e (fromOne y) = y := fun y => (IntrinsicContact.oneEquiv (E := H)).apply_symm_apply y
  have hadj1 : (fromOne (H := H)).toContinuousLinearMap.adjoint = e.toContinuousLinearMap := by
    ext y
    apply ext_inner_left ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    rw [← e.inner_map_map, hef]
  have hadj2 : e.toContinuousLinearMap.adjoint = (fromOne (H := H)).toContinuousLinearMap := by
    ext y
    apply ext_inner_left ℂ
    intro x
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [LinearIsometry.coe_toContinuousLinearMap]
    rw [← (fromOne (H := H)).inner_map_map, hfe]
  have hNe := Nat.add_sub_of_le hN
  have hred : lift e γ = reducedN N 1 hN ρ := by
    refine eq_reduced_of_duality 1 (N - 1) (cast_isPositive hNe.symm hp)
      (cast_isTraceClass hNe.symm ht) (lift e γ) (lift_isTraceClass e hγp hγt) fun A => ?_
    rw [← tr_comm _ (lift_isTraceClass e hγp hγt), tr_mul_lift e hγp hγt, tr_comm _ hγt, h,
      RadiusBound.Q, tr_mul_cast]
    congr 3
    unfold toSym1
    congr 1
    ext y
    simp only [hadj1, hadj2, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
      hef]
  rw [oneBody_eq hN, ← hred]
  ext x
  simp only [lift, ContinuousLinearMap.comp_apply, hadj1, LinearIsometry.coe_toContinuousLinearMap,
    adjoint_iso_apply, hfe]

end OneBody

end QuantumNLS.Local014OneBody

#print axioms QuantumNLS.Local014OneBody.exists_basis_lift
#print axioms QuantumNLS.Local014OneBody.posTrace_lift
#print axioms QuantumNLS.Local014OneBody.traceNorm_lift
#print axioms QuantumNLS.Local014OneBody.lift_isTraceClass
#print axioms QuantumNLS.Local014OneBody.tr_mul_lift
#print axioms QuantumNLS.Local014OneBody.posTrace_eq_one_of_tr
#print axioms QuantumNLS.Local014OneBody.traceNorm_sub_rankOne_le
#print axioms QuantumNLS.Local014OneBody.traceNorm_eq_one
#print axioms QuantumNLS.Local014OneBody.norm_tr_mul_le
#print axioms QuantumNLS.Local014OneBody.compress_eq_Q_N_p
#print axioms QuantumNLS.Local014OneBody.tr_reduced_mul
#print axioms QuantumNLS.Local014OneBody.reduced_isPositive
#print axioms QuantumNLS.Local014OneBody.reduced_isTraceClass
#print axioms QuantumNLS.Local014OneBody.tr_reduced
#print axioms QuantumNLS.Local014OneBody.eq_reduced_of_duality
#print axioms QuantumNLS.Local014OneBody.tr_reducedN_mul
#print axioms QuantumNLS.Local014OneBody.reducedN_isNormalState
#print axioms QuantumNLS.Local014OneBody.tr_oneBody_mul
#print axioms QuantumNLS.Local014OneBody.oneBody_isNormalState
#print axioms QuantumNLS.Local014OneBody.inner_oneBody_eq
#print axioms QuantumNLS.Local014OneBody.kernelProductSymbol_toSym1
#print axioms QuantumNLS.Local014OneBody.eq_oneBody_of_duality
