import QuantumNLS.Local014OneBody

/-!
# LOCAL-014 stage E4c: condensed states evaluate symbols

Source: `source-text/chapters/local/quantum_periods.tex:227-245` (proof of LOCAL-014):
"If `P = |v⟩⟨v|`, commuting position projections give
`Tr(γ_N^{(q)} P^{⊗q}) ≥ 1 − q(1 − Tr(γ_N^{(1)} P))`. For a positive trace-one matrix `γ` and
rank-one `P_w`, `‖γ − P_w‖₁ ≤ 2√(1 − Tr(γ P_w))`. ... It follows that every fixed `q`-body matrix
tends in trace norm to `P^{⊗q}`. For a convergent kernel family the expectation therefore tends to
its symbol at `v`: truncate the degree sum first, use operator-norm convergence of its finitely
many kernels, then remove the uniformly small radius-weighted tail."

* abstract projections (`IsProj`): `proj_mul_ineq`, `‖x‖² − ‖EGx‖² ≤ (‖x‖² − ‖Ex‖²) + (‖x‖² − ‖Gx‖²)`
  for commuting orthogonal projections;
* on `H^{⊗̂N}`: `blockOp h S` (`S ⊗̂ 1` on the first `k` positions), `projT w N k` (the projection
  onto `w^{⊗k}` in the first `k` positions), the position projections `slot w N i` (`|w⟩⟨w|` in
  position `i`, a permutation conjugate of `projT w N 1`), and `projT = slot_0 ⋯ slot_{k−1}`
  (`projT_eq_slotProd`), all computed on product vectors;
* `condensation_vec`, `condensation_tr`: `1 − Tr(ρ Q_{N,k}(P^{⊗k})) ≤ k (1 − Tr(ρ Q_{N,1}(P)))`
  for every positive trace-class `ρ` of trace one on `Sym^N` (the printed inequality);
* `tendsto_qexp`: if `Tr(ρ_N Q_{N,1}(P_w)) → 1` then, for every fixed `p` and `K`,
  `Tr(ρ_N Q_{N,p}(K)) → ⟨w^{⊗p}, K w^{⊗p}⟩` (via the `p`-body reduced density matrix of E4b and the
  trace-distance estimate);
* `tendsto_tr_represented`: for every family converging on a radius `R > 1`,
  `Tr(ρ_N A_N) → a(w)` (Tannery, majorant `C R^{-p}`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal ComplexOrder
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.TraceClass QuantumNLS.Ext025B11TracePairing
  QuantumNLS.Ext025B11TraceBasis QuantumNLS.Ext025A12Trace QuantumNLS.Ext025A12Normal
  QuantumNLS.KernelDefinition QuantumNLS.TensorPlacements QuantumNLS.KernelConvergence
  QuantumNLS.Local014OneBody

namespace QuantumNLS.Local014StateLimits

/-! ## 1. Commuting orthogonal projections -/

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- An orthogonal projection. -/
def IsProj (P : V →L[ℂ] V) : Prop := IsSelfAdjoint P ∧ P * P = P

theorem IsProj.inner_left {P : V →L[ℂ] V} (hP : IsProj P) (x y : V) :
    ⟪P x, y⟫_ℂ = ⟪x, P y⟫_ℂ := by
  have h := ContinuousLinearMap.adjoint_inner_left P y x
  rwa [hP.1.adjoint_eq] at h

theorem IsProj.idem_apply {P : V →L[ℂ] V} (hP : IsProj P) (x : V) : P (P x) = P x := by
  have h := congrArg (fun T : V →L[ℂ] V => T x) hP.2
  simpa using h

theorem IsProj.inner_self {P : V →L[ℂ] V} (hP : IsProj P) (x : V) :
    ⟪x, P x⟫_ℂ = ((‖P x‖ ^ 2 : ℝ) : ℂ) := by
  rw [← hP.idem_apply x, ← hP.inner_left, hP.idem_apply x, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem IsProj.norm_sq {P : V →L[ℂ] V} (hP : IsProj P) (x : V) :
    ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
  have hPP : ⟪P x, P x⟫_ℂ = ⟪P x, x⟫_ℂ := by
    rw [hP.inner_left, hP.idem_apply, ← hP.inner_left]
  have h0 : ⟪P x, x - P x⟫_ℂ = 0 := by
    rw [inner_sub_right, hPP, sub_self]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (x - P x) h0
  rw [add_sub_cancel] at h
  nlinarith [h]

theorem IsProj.norm_le {P : V →L[ℂ] V} (hP : IsProj P) (x : V) : ‖P x‖ ≤ ‖x‖ := by
  have h := hP.norm_sq x
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg x, norm_nonneg (x - P x), norm_nonneg (P x)]

theorem IsProj.mul {E G : V →L[ℂ] V} (hE : IsProj E) (hG : IsProj G) (hc : E * G = G * E) :
    IsProj (E * G) := by
  refine ⟨?_, ?_⟩
  · show star (E * G) = E * G
    rw [star_mul, hG.1.star_eq, hE.1.star_eq, hc]
  · calc E * G * (E * G) = E * (G * E) * G := by simp only [mul_assoc]
      _ = E * (E * G) * G := by rw [hc]
      _ = (E * E) * (G * G) := by simp only [mul_assoc]
      _ = E * G := by rw [hE.2, hG.2]

theorem IsProj.conj {P : V →L[ℂ] V} (hP : IsProj P) (U : V →L[ℂ] V) (hU : star U * U = 1) :
    IsProj (U * P * star U) := by
  refine ⟨hP.1.conjugate U, ?_⟩
  calc U * P * star U * (U * P * star U) = U * P * (star U * U) * P * star U := by
        simp only [mul_assoc]
    _ = U * (P * P) * star U := by rw [hU]; simp only [mul_one, mul_assoc]
    _ = U * P * star U := by rw [hP.2]

/-- Commuting projections: `‖x‖² − ‖EGx‖² ≤ (‖x‖² − ‖Ex‖²) + (‖x‖² − ‖Gx‖²)`. -/
theorem proj_mul_ineq {E G : V →L[ℂ] V} (hE : IsProj E) (hG : IsProj G) (hc : E * G = G * E)
    (x : V) : ‖x‖ ^ 2 - ‖(E * G) x‖ ^ 2 ≤ (‖x‖ ^ 2 - ‖E x‖ ^ 2) + (‖x‖ ^ 2 - ‖G x‖ ^ 2) := by
  have hEG : (E * G) x = E (G x) := rfl
  have hGE : G (E x) = E (G x) := by
    have := congrArg (fun T : V →L[ℂ] V => T x) hc
    simpa using this.symm
  have hGE' : ∀ y, G (E y) = E (G y) := by
    intro y
    have := congrArg (fun T : V →L[ℂ] V => T y) hc
    simpa using this.symm
  have h0 : ⟪E (G x), E (x - G x)⟫_ℂ = 0 := by
    rw [hE.inner_left, hE.idem_apply, hG.inner_left, hGE', map_sub, hG.idem_apply, sub_self,
      map_zero, inner_zero_right]
  have hsplit := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [← map_add, add_sub_cancel] at hsplit
  have hle := hE.norm_le (x - G x)
  have hG2 := hG.norm_sq x
  rw [hEG]
  nlinarith [norm_nonneg (E (x - G x)), norm_nonneg (x - G x)]

end Abstract

/-! ## 2. Block and position projections on `H^{⊗̂N}` -/

section Slots

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The product vector `f 0 ⊗ ⋯ ⊗ f (a−1)` in `H^{⊗̂a}`. -/
def pt {a : ℕ} (f : Fin a → H) : HilbertTensorPower ℂ H a :=
  ((ptprod (𝕜 := ℂ) f : AlgTensorPower ℂ H a) : HilbertTensorPower ℂ H a)

/-- Bounded operators on `H^{⊗̂a}` agreeing on product vectors are equal. -/
theorem ext_pt {a : ℕ} {A B : HilbertTensorPower ℂ H a →L[ℂ] HilbertTensorPower ℂ H a}
    (h : ∀ f : Fin a → H, A (pt f) = B (pt f)) : A = B := by
  let L : AlgTensorPower ℂ H a →ₗ[ℂ] HilbertTensorPower ℂ H a :=
    (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := AlgTensorPower ℂ H a)).toLinearMap
  have hL : (A : HilbertTensorPower ℂ H a →ₗ[ℂ] HilbertTensorPower ℂ H a).comp L =
      (B : HilbertTensorPower ℂ H a →ₗ[ℂ] HilbertTensorPower ℂ H a).comp L :=
    PiTensorProduct.ext (MultilinearMap.ext fun f => h f)
  have h2 : ∀ x : AlgTensorPower ℂ H a, A (x : HilbertTensorPower ℂ H a) = B x :=
    fun x => LinearMap.congr_fun hL x
  ext z
  exact UniformSpace.Completion.induction_on z (isClosed_eq A.continuous B.continuous) h2

theorem pt_inner_htpow {a : ℕ} (w : H) (f : Fin a → H) :
    ⟪(htpow a w : HilbertTensorPower ℂ H a), pt f⟫_ℂ = ∏ i, ⟪w, f i⟫_ℂ := by
  simp only [htpow, pt]
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]

theorem htpow_eq_pt (a : ℕ) (w : H) :
    (htpow a w : HilbertTensorPower ℂ H a) = pt (fun _ : Fin a => w) := rfl

/-- The projection onto `w^{⊗k}` in `H^{⊗̂k}`. -/
def proj (w : H) (k : ℕ) : HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k :=
  InnerProductSpace.rankOne ℂ (htpow k w : HilbertTensorPower ℂ H k) (htpow k w)

theorem proj_isProj {w : H} (hw : ‖w‖ = 1) (k : ℕ) : IsProj (proj w k) := by
  have h1 : ‖(htpow k w : HilbertTensorPower ℂ H k)‖ = 1 := by
    rw [norm_htpow (𝕜 := ℂ) k w, hw, one_pow]
  have hs := InnerProductSpace.isStarProjection_rankOne_self (𝕜 := ℂ) h1
  exact ⟨hs.isSelfAdjoint, hs.isIdempotentElem⟩

/-- `S ⊗̂ 1` acting on the first `k` positions of `H^{⊗̂a}`, `k + m = a`. -/
def blockOp {k m a : ℕ} (h : k + m = a)
    (S : HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k) :
    HilbertTensorPower ℂ H a →L[ℂ] HilbertTensorPower ℂ H a := by
  subst h
  exact ((splitIsometry (𝕜 := ℂ) (E := H) k m).symm :
      HilbertTensor ℂ (HilbertTensorPower ℂ H k) (HilbertTensorPower ℂ H m) →L[ℂ]
        HilbertTensorPower ℂ H (k + m)) ∘L
    htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)) ∘L
      ((splitIsometry (𝕜 := ℂ) (E := H) k m : HilbertTensorPower ℂ H (k + m) →L[ℂ]
        HilbertTensor ℂ (HilbertTensorPower ℂ H k) (HilbertTensorPower ℂ H m)))

theorem blockOp_isProj {k m a : ℕ} (h : k + m = a)
    {S : HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k} (hS : IsProj S) :
    IsProj (blockOp h S) := by
  subst h
  refine ⟨?_, ?_⟩
  · show ContinuousLinearMap.adjoint _ = _
    simp only [blockOp, ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
      LinearIsometryEquiv.symm_symm, adjoint_htmap, ContinuousLinearMap.adjoint_id,
      hS.1.adjoint_eq, ContinuousLinearMap.comp_assoc]
  · have hS2 : htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)) ∘L
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)) =
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)) := by
      rw [← htmap_comp, ContinuousLinearMap.id_comp]
      congr 1
      exact hS.2
    have hM : ∀ y, htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m))
        (htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)) y) =
        htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m)) y :=
      fun y => congrArg (fun T => T y) hS2
    ext x
    simp only [blockOp, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply, hM]

/-- Product-vector formula for the block projection onto `w^{⊗k}`. -/
theorem blockOp_proj_pt {k m a : ℕ} (h : k + m = a) (w : H) (f : Fin a → H) :
    blockOp h (proj w k) (pt f) =
      (∏ i : Fin k, ⟪w, f ⟨i, by omega⟩⟫_ℂ) • pt (fun i : Fin a => if (i : ℕ) < k then w else f i) := by
  subst h
  have hf : f = Fin.append (fun i => f (Fin.castAdd m i)) (fun i => f (Fin.natAdd k i)) :=
    Fin.append_castAdd_natAdd.symm
  have hsplit : (splitIsometry (𝕜 := ℂ) (E := H) k m) (pt f) =
      htmul (pt (fun i => f (Fin.castAdd m i))) (pt (fun i => f (Fin.natAdd k i))) := by
    conv_lhs => rw [hf]
    exact splitIsometry_ptprod_append _ _
  have hback : (splitIsometry (𝕜 := ℂ) (E := H) k m).symm
      (htmul (pt (fun _ : Fin k => w)) (pt (fun i => f (Fin.natAdd k i)))) =
      pt (Fin.append (fun _ : Fin k => w) (fun i => f (Fin.natAdd k i))) := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    exact (splitIsometry_ptprod_append _ _).symm
  have hfun : Fin.append (fun _ : Fin k => w) (fun i => f (Fin.natAdd k i)) =
      fun i : Fin (k + m) => if (i : ℕ) < k then w else f i := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Fin.append_left]
    · simp only [Fin.append_right, Fin.coe_natAdd]
      rw [if_neg (by omega)]
  simp only [blockOp, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [hsplit, htmap_htmul, ContinuousLinearMap.id_apply, proj, InnerProductSpace.rankOne_apply,
    pt_inner_htpow, htmul_smul_left, map_smul, htpow_eq_pt, hback, hfun]
  rfl

variable (w : H) (N : ℕ)

/-- The projection onto `w^{⊗k}` in the first `k` positions of `H^{⊗̂N}`. -/
def projT (k : ℕ) (hk : k ≤ N) : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  blockOp (Nat.add_sub_of_le hk) (proj w k)

/-- The transposition of positions `0` and `i`. -/
def swapAt (i : Fin N) : Equiv.Perm (Fin N) := Equiv.swap ⟨0, Nat.zero_lt_of_lt i.isLt⟩ i

/-- The permutation unitary as an operator. -/
def permOp (σ : Equiv.Perm (Fin N)) : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  (permRep ℂ H N σ : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N)

/-- The position projection `|w⟩⟨w|` in position `i`. -/
def slot (i : Fin N) : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N :=
  permOp N (swapAt N i) * projT w N 1 (Nat.one_le_of_lt i.isLt) * star (permOp N (swapAt N i))

variable {w N}

theorem permOp_pt (σ : Equiv.Perm (Fin N)) (f : Fin N → H) :
    permOp N σ (pt f) = pt (fun i => f (σ.symm i)) := by
  simp only [permOp, permRep_apply, pt]
  rw [permHilbertIsometry_coe, permLinearEquiv_ptprod]

theorem star_permOp (σ : Equiv.Perm (Fin N)) :
    star (permOp (H := H) N σ) = permOp N σ⁻¹ := by
  simp only [permOp, map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]

theorem star_permOp_mul (σ : Equiv.Perm (Fin N)) :
    star (permOp (H := H) N σ) * permOp N σ = 1 :=
  Unitary.star_mul_self_of_mem (permRep ℂ H N σ).2

theorem projT_pt (k : ℕ) (hk : k ≤ N) (f : Fin N → H) :
    projT w N k hk (pt f) =
      (∏ i : Fin k, ⟪w, f ⟨i, by omega⟩⟫_ℂ) • pt (fun i : Fin N => if (i : ℕ) < k then w else f i) :=
  blockOp_proj_pt _ w f

theorem slot_pt (i : Fin N) (f : Fin N → H) :
    slot w N i (pt f) = ⟪w, f i⟫_ℂ • pt (Function.update f i w) := by
  set σ := swapAt N i with hσ
  set z : Fin N := ⟨0, Nat.zero_lt_of_lt i.isLt⟩ with hz
  have hσs : σ.symm = σ := Equiv.symm_swap _ _
  have hσi : σ⁻¹ = σ := by rw [Equiv.Perm.inv_def, hσs]
  have hσz : σ z = i := Equiv.swap_apply_left _ _
  have hσσ : ∀ l, σ (σ l) = l := fun l => Equiv.swap_apply_self _ _ _
  rw [slot, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, star_permOp, ← hσ, hσi,
    permOp_pt, projT_pt, map_smul, permOp_pt, Fin.prod_univ_one]
  refine congrArg₂ (fun (c : ℂ) (v : HilbertTensorPower ℂ H N) => c • v) ?_ ?_
  · simp only [hσs]
    have : (⟨((0 : Fin 1) : ℕ), Nat.zero_lt_of_lt i.isLt⟩ : Fin N) = z := rfl
    rw [this, hσz]
  · refine congrArg pt (funext fun l => ?_)
    simp only [hσs, hσσ]
    by_cases hl : l = i
    · subst hl
      have : σ l = z := by rw [← hσz, hσσ]
      rw [this, Function.update_self]
      simp [hz]
    · rw [Function.update_of_ne hl, if_neg]
      intro hlt
      apply hl
      have h0 : σ l = z := Fin.ext (by simp [hz]; omega)
      rw [← hσσ l, h0, hσz]

theorem slot_isProj (hw : ‖w‖ = 1) (i : Fin N) : IsProj (slot w N i) :=
  (blockOp_isProj _ (proj_isProj hw 1)).conj _ (star_permOp_mul _)

/-- `slot_0 ⋯ slot_{k−1}`. -/
def slotProd (w : H) (N : ℕ) : ℕ → (HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N)
  | 0 => 1
  | k + 1 => slotProd w N k * (if h : k < N then slot w N ⟨k, h⟩ else 1)

theorem slotProd_pt (k : ℕ) (hk : k ≤ N) (f : Fin N → H) :
    slotProd w N k (pt f) =
      (∏ i : Fin k, ⟪w, f ⟨i, by omega⟩⟫_ℂ) • pt (fun i : Fin N => if (i : ℕ) < k then w else f i) := by
  induction k generalizing f with
  | zero => simp [slotProd]
  | succ k ih =>
    have hk' : k < N := by omega
    rw [slotProd, ContinuousLinearMap.mul_apply, dif_pos hk', slot_pt, map_smul, ih (by omega),
      smul_smul, Fin.prod_univ_castSucc]
    congr 1
    · rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Function.update_of_ne]
      · rfl
      · intro he
        have := congrArg Fin.val he
        simp at this
        omega
    · congr 1
      funext i
      by_cases h1 : (i : ℕ) < k
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1]
        by_cases h2 : (i : ℕ) = k
        · rw [if_pos (by omega)]
          have : i = ⟨k, hk'⟩ := Fin.ext h2
          rw [this, Function.update_self]
        · rw [if_neg (by omega), Function.update_of_ne]
          intro he
          exact h2 (congrArg Fin.val he)

theorem projT_eq_slotProd (k : ℕ) (hk : k ≤ N) : projT w N k hk = slotProd w N k :=
  ext_pt fun f => by rw [projT_pt, slotProd_pt k hk]

theorem slotProd_comm (k : ℕ) (hk : k < N) :
    slotProd w N k * slot w N ⟨k, hk⟩ = slot w N ⟨k, hk⟩ * slotProd w N k := by
  apply ext_pt
  intro f
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, slotProd_pt k hk.le,
    map_smul, slot_pt, slot_pt, map_smul, slotProd_pt k hk.le, smul_smul, smul_smul]
  have hfk : (if ((⟨k, hk⟩ : Fin N) : ℕ) < k then w else f ⟨k, hk⟩) = f ⟨k, hk⟩ := by simp
  rw [hfk]
  refine congrArg₂ (fun (c : ℂ) (v : HilbertTensorPower ℂ H N) => c • v) ?_ ?_
  · rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Function.update_of_ne]
    intro he
    have := congrArg Fin.val he
    simp at this
    omega
  · refine congrArg pt (funext fun i => ?_)
    by_cases h1 : (i : ℕ) < k
    · rw [if_pos h1, Function.update_of_ne, if_pos h1]
      intro he; have := congrArg Fin.val he; simp at this; omega
    · rw [if_neg h1]
      by_cases h2 : i = ⟨k, hk⟩
      · rw [h2, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne h2, Function.update_of_ne h2, if_neg h1]

theorem slotProd_isProj (hw : ‖w‖ = 1) (k : ℕ) (hk : k ≤ N) : IsProj (slotProd w N k) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · show star (1 : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N) = 1
      exact star_one _
    · show (1 : HilbertTensorPower ℂ H N →L[ℂ] HilbertTensorPower ℂ H N) * 1 = 1
      exact one_mul 1
  | succ k ih =>
    have hk' : k < N := by omega
    show IsProj (slotProd w N k * (if h : k < N then slot w N ⟨k, h⟩ else 1))
    rw [dif_pos hk']
    exact (ih (by omega)).mul (slot_isProj hw _) (slotProd_comm k hk')

/-- For a symmetric vector every position projection has the same weight. -/
theorem norm_slot_sym (hN : 1 ≤ N) (ψ : SymSector ℂ H N) (i : Fin N) :
    ‖slot w N i (ψ : HilbertTensorPower ℂ H N)‖ =
      ‖projT w N 1 hN (ψ : HilbertTensorPower ℂ H N)‖ := by
  rw [slot, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, star_permOp]
  have hfix : permOp N (swapAt N i)⁻¹ (ψ : HilbertTensorPower ℂ H N) = ψ := ψ.2 _
  rw [hfix, permOp, permRep_apply, LinearIsometryEquiv.norm_map]

/-- Vector form of the printed inequality. -/
theorem condensation_vec (hw : ‖w‖ = 1) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) (ψ : SymSector ℂ H N) :
    ‖(ψ : HilbertTensorPower ℂ H N)‖ ^ 2 - ‖projT w N k hk ψ‖ ^ 2 ≤
      k * (‖(ψ : HilbertTensorPower ℂ H N)‖ ^ 2 - ‖projT w N 1 hN ψ‖ ^ 2) := by
  rw [projT_eq_slotProd]
  induction k with
  | zero => simp [slotProd]
  | succ k ih =>
    have hk' : k < N := by omega
    have h := proj_mul_ineq (slotProd_isProj hw k (by omega)) (slot_isProj hw ⟨k, hk'⟩)
      (slotProd_comm k hk') (ψ : HilbertTensorPower ℂ H N)
    have hs := norm_slot_sym (w := w) hN ψ ⟨k, hk'⟩
    have hih := ih (by omega)
    show _ - ‖(slotProd w N k * (if h : k < N then slot w N ⟨k, h⟩ else 1)) _‖ ^ 2 ≤ _
    rw [dif_pos hk']
    rw [hs] at h
    have hc : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hc]
    linarith

end Slots

/-! ## 3. From vectors to states: the printed inequality for normal states -/

section States

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inner_cast_Q {k m a : ℕ} (h : k + m = a) (ψ : SymSector ℂ H a)
    (S : HilbertTensorPower ℂ H k →L[ℂ] HilbertTensorPower ℂ H k) :
    ⟪ψ, castSymSectorOperator h (Q_N_p (q := m) (MixedTraceNorm.symKernel S)) ψ⟫_ℂ =
      ⟪(ψ : HilbertTensorPower ℂ H a), blockOp h S ψ⟫_ℂ := by
  subst h
  change ⟪ψ, Q_N_p (q := m) (MixedTraceNorm.symKernel S) ψ⟫_ℂ = _
  rw [← U_N_r_eq_Q_N_p, MixedTraceNorm.inner_U_eq_inner_htmap]
  simp only [blockOp, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  have e1 := (splitIsometry (𝕜 := ℂ) (E := H) k m).inner_map_map
    (ψ : HilbertTensorPower ℂ H (k + m))
    ((splitIsometry (𝕜 := ℂ) (E := H) k m).symm
      (htmap S (ContinuousLinearMap.id ℂ (HilbertTensorPower ℂ H m))
        (splitIsometry (𝕜 := ℂ) (E := H) k m (ψ : HilbertTensorPower ℂ H (k + m)))))
  rw [LinearIsometryEquiv.apply_symm_apply] at e1
  exact e1

/-- The kernel `P^{⊗k}`: the projection onto `w^{⊗k}` in `Sym^k`. -/
def P (w : H) (k : ℕ) : BoundedSymmetricKernel H k := MixedTraceNorm.symKernel (proj w k)

variable {w : H} {N : ℕ}

theorem inner_Q_P (hw : ‖w‖ = 1) (k : ℕ) (hk : k ≤ N) (ψ : SymSector ℂ H N) :
    ⟪ψ, RadiusBound.Q N k hk (P w k) ψ⟫_ℂ =
      ((‖projT w N k hk (ψ : HilbertTensorPower ℂ H N)‖ ^ 2 : ℝ) : ℂ) := by
  rw [RadiusBound.Q, P, inner_cast_Q]
  exact (blockOp_isProj _ (proj_isProj hw k)).inner_self _

theorem condensation_op_pos (hw : ‖w‖ = 1) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    ((k : ℂ) • (1 - RadiusBound.Q N 1 hN (P w 1)) - (1 - RadiusBound.Q N k hk (P w k))).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  set X := (k : ℂ) • (1 - RadiusBound.Q N 1 hN (P w 1)) - (1 - RadiusBound.Q N k hk (P w k))
  have hxx : ⟪x, x⟫_ℂ = ((‖(x : HilbertTensorPower ℂ H N)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hval : ⟪x, X x⟫_ℂ = (((k : ℝ) * (‖(x : HilbertTensorPower ℂ H N)‖ ^ 2 -
      ‖projT w N 1 hN (x : HilbertTensorPower ℂ H N)‖ ^ 2) - (‖(x : HilbertTensorPower ℂ H N)‖ ^ 2 -
      ‖projT w N k hk (x : HilbertTensorPower ℂ H N)‖ ^ 2) : ℝ) : ℂ) := by
    simp only [X, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right, inner_Q_P hw, hxx]
    push_cast
    ring
  have hX : ⟪X x, x⟫_ℂ = ⟪x, X x⟫_ℂ := by
    rw [← inner_conj_symm, hval, Complex.conj_ofReal]
  have hc := condensation_vec hw hN k hk x
  rw [hX, hval]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  exact ⟨trivial, by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem tr_sub_mul {ρ : E →L[ℂ] E} (ht : IsTraceClass ρ) (A B : E →L[ℂ] E) :
    tr ((A - B) * ρ) = tr (A * ρ) - tr (B * ρ) := by
  rw [sub_mul]
  exact trace_sub _ _ _ (finite_left A ρ ht.ne) (finite_left B ρ ht.ne)

theorem tr_smul_mul (ρ : E →L[ℂ] E) (c : ℂ) (A : E →L[ℂ] E) :
    tr ((c • A) * ρ) = c * tr (A * ρ) := by
  rw [smul_mul_assoc]
  exact trace_smul _ c _

/-- **The printed inequality** `Tr(γ^{(k)} P^{⊗k}) ≥ 1 − k(1 − Tr(γ^{(1)} P))`, in the
line-176 normalization `Tr(γ^{(k)} B) = Tr(ρ Q_{N,k}(B))`. -/
theorem condensation_tr (hw : ‖w‖ = 1) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N)
    {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N} (hρ : IsNormalState ρ) :
    1 - (tr (ρ * RadiusBound.Q N k hk (P w k))).re ≤
      k * (1 - (tr (ρ * RadiusBound.Q N 1 hN (P w 1))).re) := by
  have hpos := pairing_nonneg (refBasis _) _ ρ (condensation_op_pos hw hN k hk) hρ.1 hρ.2.1
  change 0 ≤ tr _ at hpos
  rw [tr_sub_mul hρ.2.1, tr_smul_mul, tr_sub_mul hρ.2.1, tr_sub_mul hρ.2.1, one_mul, hρ.2.2,
    tr_comm _ hρ.2.1, tr_comm _ hρ.2.1] at hpos
  have h := (Complex.nonneg_iff.mp hpos).1
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] at h
  linarith

/-! ## 4. Expectations of fixed-degree placements and of convergent families -/

/-- `Tr(ρ Q_{N,p}(K))`, and `0` when `p > N`. -/
def qexp {N : ℕ} (ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) (p : ℕ)
    (K : BoundedSymmetricKernel H p) : ℂ :=
  if h : p ≤ N then tr (ρ * RadiusBound.Q N p h K) else 0

theorem symProjToSector_sym {p : ℕ} (y : SymSector ℂ H p) :
    symProjToSector p (y : HilbertTensorPower ℂ H p) = y := by
  apply Subtype.ext
  change symProj ℂ H p (y : HilbertTensorPower ℂ H p) = y
  rw [symProj_eq_starProjection]
  exact (Submodule.starProjection_eq_self_iff (K := SymSector ℂ H p)).mpr y.2

theorem symKernel_extend {p : ℕ} (K : BoundedSymmetricKernel H p) :
    MixedTraceNorm.symKernel (extendSymKernel K) = K := by
  ext x : 1
  simp only [MixedTraceNorm.symKernel, extendSymKernel, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, symProjToSector_sym]

theorem kps_eq_tr {p : ℕ} (K : BoundedSymmetricKernel H p) (w : H) :
    kernelProductSymbol K w = tr (proj w p * extendSymKernel K) := by
  change _ = trace (refBasis _) (InnerProductSpace.rankOne ℂ _ _ * _)
  rw [trace_rankOne_right]
  unfold kernelProductSymbol extendSymKernel
  simp only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply]
  rw [show symProjToSector p (htpow p w : HilbertTensorPower ℂ H p) =
    ⟨htpow p w, htpow_mem_symSector p w⟩ from symProjToSector_sym ⟨htpow p w, htpow_mem_symSector p w⟩]

theorem proj_isTraceClass (w : H) (p : ℕ) : IsTraceClass (proj w p) :=
  lt_of_le_of_lt (Fidelity.traceNorm_rankOne_le _ _) ENNReal.ofReal_lt_top

/-- Quantitative fixed-degree estimate: `|Tr(ρ Q_{N,p}(K)) − ⟨w^{⊗p}, K w^{⊗p}⟩| ≤
‖K‖ · 2√(p(1 − Tr(ρ Q_{N,1}(P))))`. -/
theorem norm_tr_Q_sub_le (hw : ‖w‖ = 1) (hN : 1 ≤ N) {p : ℕ} (hp : p ≤ N)
    {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N} (hρ : IsNormalState ρ)
    (K : BoundedSymmetricKernel H p) :
    ‖tr (ρ * RadiusBound.Q N p hp K) - kernelProductSymbol K w‖ ≤
      ‖K‖ * (2 * √(p * (1 - (tr (ρ * RadiusBound.Q N 1 hN (P w 1))).re))) := by
  set γ := reducedN N p hp ρ
  have hγ : IsNormalState γ := reducedN_isNormalState hp hρ
  set Kt := extendSymKernel K
  have h1 : tr (ρ * RadiusBound.Q N p hp K) = tr (γ * Kt) := by
    rw [tr_reducedN_mul hp hρ.1 hρ.2.1, symKernel_extend]
  have hPt := proj_isTraceClass w p
  have hdtc : IsTraceClass (γ - proj w p) := finite_sub hγ.2.1 hPt
  have h3 : tr (γ * Kt) - tr (proj w p * Kt) = tr (Kt * (γ - proj w p)) := by
    rw [tr_comm Kt hdtc, sub_mul]
    exact (trace_sub _ _ _ (finite_right Kt γ hγ.2.1).ne (finite_right Kt _ hPt).ne).symm
  rw [h1, kps_eq_tr, h3]
  have hpb := pairing_bound (refBasis _) Kt (γ - proj w p) hdtc.ne
  change ‖tr (Kt * (γ - proj w p))‖ ≤ _ at hpb
  have hnorm : ‖(htpow p w : HilbertTensorPower ℂ H p)‖ = 1 := by
    rw [norm_htpow (𝕜 := ℂ) p w, hw, one_pow]
  have hfid := traceNorm_sub_rankOne_le hγ _ hnorm
  have hre : RCLike.re ⟪(htpow p w : HilbertTensorPower ℂ H p), γ (htpow p w)⟫_ℂ =
      (tr (ρ * RadiusBound.Q N p hp (P w p))).re := by
    have e : ⟪(htpow p w : HilbertTensorPower ℂ H p), γ (htpow p w)⟫_ℂ = tr (γ * proj w p) :=
      (trace_rankOne_left (refBasis _) γ _ _).symm
    rw [e, tr_reducedN_mul hp hρ.1 hρ.2.1]
    rfl
  rw [hre] at hfid
  have hcond := condensation_tr hw hN p hp hρ
  have hsq : √(1 - (tr (ρ * RadiusBound.Q N p hp (P w p))).re) ≤
      √(p * (1 - (tr (ρ * RadiusBound.Q N 1 hN (P w 1))).re)) :=
    Real.sqrt_le_sqrt (by linarith)
  have htr : (traceNorm (γ - proj w p)).toReal ≤
      2 * √(1 - (tr (ρ * RadiusBound.Q N p hp (P w p))).re) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hfid
  calc ‖tr (Kt * (γ - proj w p))‖ ≤ ‖Kt‖ * (traceNorm (γ - proj w p)).toReal := hpb
    _ ≤ ‖K‖ * (2 * √(p * (1 - (tr (ρ * RadiusBound.Q N 1 hN (P w 1))).re))) := by
      apply mul_le_mul (norm_extendSymKernel_le K) _ ENNReal.toReal_nonneg
        (norm_nonneg (K : SymSector ℂ H p →L[ℂ] SymSector ℂ H p))
      linarith

theorem qexp_one_of_le {N : ℕ} (hN : 1 ≤ N) (ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    qexp ρ 1 (P w 1) = tr (ρ * RadiusBound.Q N 1 hN (P w 1)) := by
  rw [qexp, dif_pos hN]

/-- **Fixed-degree limit.** If `Tr(ρ_N Q_{N,1}(P)) → 1`, then for every fixed `p` and `K`,
`Tr(ρ_N Q_{N,p}(K)) → ⟨w^{⊗p}, K w^{⊗p}⟩`. -/
theorem tendsto_qexp (hw : ‖w‖ = 1) (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (hρ : ∀ N, IsNormalState (ρ N))
    (h1 : Tendsto (fun N => qexp (ρ N) 1 (P w 1)) atTop (𝓝 1)) (p : ℕ)
    (K : BoundedSymmetricKernel H p) :
    Tendsto (fun N => qexp (ρ N) p K) atTop (𝓝 (kernelProductSymbol K w)) := by
  have hre : Tendsto (fun N => (qexp (ρ N) 1 (P w 1)).re) atTop (𝓝 1) := by
    have := (Complex.continuous_re.tendsto (1 : ℂ)).comp h1
    rw [Complex.one_re] at this
    exact this
  have hlim : Tendsto (fun N => ‖K‖ * (2 * √(p * (1 - (qexp (ρ N) 1 (P w 1)).re)))) atTop
      (𝓝 0) := by
    have hc : Continuous fun x : ℝ => ‖K‖ * (2 * √(p * (1 - x))) := by fun_prop
    have := (hc.tendsto 1).comp hre
    have h0 : ‖K‖ * (2 * √((p : ℝ) * (1 - 1))) = 0 := by simp
    rw [h0] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (max p 1)] with N hNp
  have hp : p ≤ N := le_of_max_le_left hNp
  have hN : 1 ≤ N := le_of_max_le_right hNp
  rw [qexp, dif_pos hp, qexp_one_of_le hN]
  exact norm_tr_Q_sub_le hw hN hp (hρ N) K

theorem norm_qexp_le {N : ℕ} {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N} (hρ : IsNormalState ρ)
    (p : ℕ) (K : BoundedSymmetricKernel H p) : ‖qexp ρ p K‖ ≤ ‖K‖ := by
  unfold qexp
  split_ifs with h
  · exact (norm_tr_mul_le hρ _).trans (RadiusBound.norm_Q_le N p h K)
  · rw [norm_zero]
    exact norm_nonneg (K : SymSector ℂ H p →L[ℂ] SymSector ℂ H p)

theorem Q_sub (N p : ℕ) (hp : p ≤ N) (A B : BoundedSymmetricKernel H p) :
    RadiusBound.Q N p hp (A - B) = RadiusBound.Q N p hp A - RadiusBound.Q N p hp B := by
  simp only [RadiusBound.Q_eq_genericU_N_r, sub_eq_add_neg, ← neg_one_smul ℂ B,
    RootOverlapLimit.genericU_add, RootOverlapLimit.genericU_smul]
  rw [neg_one_smul ℂ (genericU_N_r N p hp B)]

theorem qexp_sub {N : ℕ} {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N} (hρ : IsNormalState ρ)
    (p : ℕ) (A B : BoundedSymmetricKernel H p) : qexp ρ p A - qexp ρ p B = qexp ρ p (A - B) := by
  unfold qexp
  split_ifs with h
  · rw [Q_sub, mul_sub]
    exact (trace_sub _ _ _ (finite_right _ ρ hρ.2.1).ne (finite_right _ ρ hρ.2.1).ne).symm
  · simp

theorem isTraceClass_sum {ι : Type*} (s : Finset ι) (X : ι → E →L[ℂ] E)
    (hX : ∀ i, IsTraceClass (X i)) : IsTraceClass (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold IsTraceClass
    rw [Fidelity.traceNorm_zero]
    exact ENNReal.zero_lt_top
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hX a).add ih

/-- Additivity of the trace over a finite sum of trace-class operators. -/
theorem tr_sum {ι : Type*} (s : Finset ι) (X : ι → E →L[ℂ] E) (hX : ∀ i, IsTraceClass (X i)) :
    tr (∑ i ∈ s, X i) = ∑ i ∈ s, tr (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tr, trace]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact trace_add _ (hX a) (isTraceClass_sum s X hX)

theorem tr_mul_represented {N : ℕ} {ρ : SymSector ℂ H N →L[ℂ] SymSector ℂ H N}
    (hρ : IsNormalState ρ) (A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N) :
    tr (ρ * RadiusBound.represented (A N)) = ∑' p, qexp ρ p (coeffAt A N p) := by
  unfold RadiusBound.represented
  rw [Finset.mul_sum, tr_sum _ _ (fun i => finite_right _ ρ hρ.2.1),
    tsum_eq_sum (s := range (N + 1))]
  · rw [← Fin.sum_univ_eq_sum_range (fun p => qexp ρ p (coeffAt A N p))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [qexp, dif_pos (Nat.lt_succ_iff.mp p.2), Local014RealSymbol.coeffAt_fin A N p]
  · intro p hp
    rw [Finset.mem_range, not_lt] at hp
    rw [qexp, dif_neg (by omega)]

/-- **Convergent families**: for a family converging on a radius `R > 1` and states with
`Tr(ρ_N Q_{N,1}(P_w)) → 1`, `Tr(ρ_N A_N) → a(w)`. -/
theorem tendsto_tr_represented {R : ℝ} (hR : 1 < R)
    {A : ∀ N : ℕ, LocalPlacement.KernelList (H := H) N}
    {Alim : ∀ p : ℕ, BoundedSymmetricKernel H p} (hA : ConvergesOnRadius R A Alim)
    (hw : ‖w‖ = 1) (ρ : ∀ N : ℕ, SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (hρ : ∀ N, IsNormalState (ρ N))
    (h1 : Tendsto (fun N => qexp (ρ N) 1 (P w 1)) atTop (𝓝 1)) :
    Tendsto (fun N => tr (ρ N * RadiusBound.represented (A N))) atTop (𝓝 (symbol Alim w)) := by
  obtain ⟨⟨C, hC⟩, hl⟩ := hA
  have hR0 : 0 < R := by linarith
  simp_rw [fun N => tr_mul_represented (hρ N) A]
  have hbound : ∀ N p, ‖qexp (ρ N) p (coeffAt A N p)‖ ≤ C * (R⁻¹) ^ p := by
    intro N p
    refine (norm_qexp_le (hρ N) p _).trans ?_
    have h := (Local014RealSymbol.pow_mul_norm_coeffAt_le hR0.le A N p).trans (hC N)
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hR0 p), mul_comm]
    exact h
  have hsum : Summable fun p : ℕ => C * (R⁻¹) ^ p :=
    (summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hR)).mul_left C
  refine tendsto_tsum_of_dominated_convergence (bound := fun p => C * (R⁻¹) ^ p) hsum
    (fun p => ?_) (Eventually.of_forall fun N p => hbound N p)
  have hfix := tendsto_qexp hw ρ hρ h1 p (Alim p)
  have hdiff : Tendsto (fun N => qexp (ρ N) p (coeffAt A N p) - qexp (ρ N) p (Alim p)) atTop
      (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) (hl p)
    rw [qexp_sub (hρ N)]
    exact norm_qexp_le (hρ N) p _
  simpa using hdiff.add hfix

end States

end QuantumNLS.Local014StateLimits

#print axioms QuantumNLS.Local014StateLimits.proj_mul_ineq
#print axioms QuantumNLS.Local014StateLimits.ext_pt
#print axioms QuantumNLS.Local014StateLimits.blockOp_proj_pt
#print axioms QuantumNLS.Local014StateLimits.blockOp_isProj
#print axioms QuantumNLS.Local014StateLimits.slot_pt
#print axioms QuantumNLS.Local014StateLimits.slotProd_pt
#print axioms QuantumNLS.Local014StateLimits.projT_eq_slotProd
#print axioms QuantumNLS.Local014StateLimits.slotProd_comm
#print axioms QuantumNLS.Local014StateLimits.slotProd_isProj
#print axioms QuantumNLS.Local014StateLimits.norm_slot_sym
#print axioms QuantumNLS.Local014StateLimits.condensation_vec
#print axioms QuantumNLS.Local014StateLimits.inner_cast_Q
#print axioms QuantumNLS.Local014StateLimits.inner_Q_P
#print axioms QuantumNLS.Local014StateLimits.condensation_op_pos
#print axioms QuantumNLS.Local014StateLimits.condensation_tr
#print axioms QuantumNLS.Local014StateLimits.symKernel_extend
#print axioms QuantumNLS.Local014StateLimits.kps_eq_tr
#print axioms QuantumNLS.Local014StateLimits.norm_tr_Q_sub_le
#print axioms QuantumNLS.Local014StateLimits.tendsto_qexp
#print axioms QuantumNLS.Local014StateLimits.norm_qexp_le
#print axioms QuantumNLS.Local014StateLimits.Q_sub
#print axioms QuantumNLS.Local014StateLimits.qexp_sub
#print axioms QuantumNLS.Local014StateLimits.tr_sum
#print axioms QuantumNLS.Local014StateLimits.tr_mul_represented
#print axioms QuantumNLS.Local014StateLimits.tendsto_tr_represented
