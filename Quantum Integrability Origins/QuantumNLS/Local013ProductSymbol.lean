import QuantumNLS.TerraMultiRound21VaryingSurvivors
import QuantumNLS.RootOverlapLimit
import QuantumNLS.PlacementFiberCanonicalPrefix

/-!
# LOCAL-013 `reset:principal-calculus`, stage L1: the product symbol
(`source-text/chapters/local/quantum_periods.tex:118-140`)

Source sentence (proof of LOCAL-013): "The limiting order-`p+q` kernel is the symmetrized tensor
product, whose diagonal symbol is the product of the two diagonal symbols."

Proved here (standard axioms only):
* `zeroConfig p q`: the concrete zero-overlap configuration (`A` on the first `p` slots, `B` on the
  last `q` slots of the union `p + q`).
* `kps_zeroOverlap`: for the actual averaged zero-overlap kernel (DEF-041 placement algebra,
  `averagedOverlapKernel` with `s = 0`, which is the limiting order-`(p+q)` product kernel of
  `TerraMultiRound21VaryingSurvivors.varying_zero_overlap_term_limit`) and EVERY `v : H`,
  `⟨v^{⊗(p+q)}, K₀(A,B) v^{⊗(p+q)}⟩ = ⟨v^{⊗p}, A v^{⊗p}⟩ ⟨v^{⊗q}, B v^{⊗q}⟩`.
* `prodLim Alim Blim j = Σ_{p ≤ j} K₀(A_p, B_{j-p})` (transported to degree `j`), the limiting
  degree-`j` kernel of a product, and `symbol_prodLim`: on `‖v‖² ≤ R` with summable radius
  series, its DEF-042 symbol is the product of the two symbols (Cauchy product,
  `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace BigOperators
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementProduct QuantumNLS.RootOverlapCommutator
  QuantumNLS.RootOverlapLimit QuantumNLS.PlacementUnionReindex QuantumNLS.KernelConvergence

namespace QuantumNLS.Local013ProductSymbol

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### The zero-overlap configuration -/

theorem zeroSlots_eq (p q : ℕ) : q + (p - 0) = p + (q + 0) := by omega

/-- `A` on the first `p` of the `p + q` union slots. -/
def zeroLeft (p q : ℕ) : PlacementSubset p (q - 0) :=
  ⟨firstPositions, card_firstPositions p (q - 0)⟩

/-- `B` on the last `q` of the `p + q` union slots (in the `q + p` presentation). -/
def zeroRight (p q : ℕ) : PlacementSubset q (p - 0) :=
  ⟨castSlotSet (zeroSlots_eq p q).symm (slotsB p q 0), by
    simpa [castSlotSet] using card_slotsB p q 0⟩

theorem mem_zeroLeft (p q : ℕ) (x : Fin (p + (q - 0))) :
    x ∈ (zeroLeft p q).1 ↔ x.1 < p := by
  simp only [zeroLeft, mem_firstPositions]
  constructor
  · rintro ⟨i, rfl⟩
    simp
  · intro hx
    exact ⟨⟨x.1, hx⟩, Fin.ext (by simp)⟩

theorem val_cast_fin {m n : ℕ} (h : m = n) (x : Fin m) :
    (cast (congrArg Fin h) x : Fin n).1 = x.1 := by
  subst h; rfl

theorem mem_zeroRight (p q : ℕ) (x : Fin (p + (q - 0))) :
    x ∈ (zeroRight p q).1.map (overlapSlotEquiv (Nat.zero_le p) (Nat.zero_le q)).toEmbedding ↔
      p ≤ x.1 := by
  simp only [zeroRight, castSlotSet, slotsB, overlapSlotEquiv, Finset.mem_map,
    Finset.mem_image, Finset.mem_univ, true_and, Equiv.coe_toEmbedding, Equiv.cast_apply]
  constructor
  · rintro ⟨y, ⟨z, ⟨j, rfl⟩, rfl⟩, rfl⟩
    rw [val_cast_fin, val_cast_fin]
    · simp
    all_goals omega
  · intro hx
    refine ⟨cast (congrArg Fin (zeroSlots_eq p q).symm)
      (Fin.natAdd p (Fin.castAdd 0 (⟨x.1 - p, by omega⟩ : Fin q))), ⟨_, ⟨⟨x.1 - p, by omega⟩, rfl⟩, rfl⟩, ?_⟩
    apply Fin.ext
    rw [val_cast_fin, val_cast_fin]
    · simp; omega
    all_goals omega

/-- The concrete zero-overlap configuration. -/
def zeroConfig (p q : ℕ) : OverlapConfiguration p q 0 (Nat.zero_le p) (Nat.zero_le q) where
  left := zeroLeft p q
  right := zeroRight p q
  overlap_card := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro x hx
    rw [Finset.mem_inter, mem_zeroLeft, mem_zeroRight] at hx
    omega
  covers_union := by
    ext x
    simp only [Finset.mem_union, mem_zeroLeft, mem_zeroRight, Finset.mem_univ, iff_true]
    omega

theorem left_zeroConfig (p q : ℕ) (A : BoundedSymmetricKernel H p) :
    subsetPlacement (zeroConfig p q).left A = firstPlacement (q := q - 0) A :=
  subsetPlacement_first _ rfl A

theorem right_zeroConfig (p q : ℕ) (B : BoundedSymmetricKernel H q) :
    (rightPlacement (zeroConfig p q) B :
      HilbertTensorPower ℂ H (p + (q + 0)) →L[ℂ] HilbertTensorPower ℂ H (p + (q + 0))) =
      midPlacement p q 0 B :=
  rawMid p q 0 B (p - 0) (zeroSlots_eq p q) (zeroRight p q)
    (QuantumNLS.PlacementFiberTransport.castSlotSet_symm (zeroSlots_eq p q).symm _)

theorem inner_htpow_split_symm (k m : ℕ) (v : H) (a : HilbertTensorPower ℂ H k)
    (b : HilbertTensorPower ℂ H m) :
    ⟪(htpow (k + m) v : HilbertTensorPower ℂ H (k + m)),
      (splitIsometry (𝕜 := ℂ) (E := H) k m).symm (htmul a b)⟫_ℂ =
      ⟪(htpow k v : HilbertTensorPower ℂ H k), a⟫_ℂ *
        ⟪(htpow m v : HilbertTensorPower ℂ H m), b⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map (splitIsometry (𝕜 := ℂ) (E := H) k m),
    LinearIsometryEquiv.apply_symm_apply, split_htpow, inner_htmul]

theorem inner_first_mid (p q : ℕ) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (v : H) :
    ⟪(htpow (p + (q + 0)) v : HilbertTensorPower ℂ H (p + (q + 0))),
      firstPlacement (q := q + 0) A
        (midPlacement p q 0 B (htpow (p + (q + 0)) v))⟫_ℂ =
      kernelProductSymbol A v * kernelProductSymbol B v := by
  rw [midPlacement_htpow]
  unfold firstPlacement
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.apply_symm_apply, htmap_htmul,
    ContinuousLinearMap.id_apply]
  rw [extend_htpow, inner_htpow_split_symm, inner_htpow_split_symm]
  have h0 : ⟪(htpow 0 v : HilbertTensorPower ℂ H 0), htpow 0 v⟫_ℂ = 1 := by
    have hn : ‖(htpow 0 v : HilbertTensorPower ℂ H 0)‖ = 1 := by rw [norm_htpow, pow_zero]
    have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (htpow 0 v : HilbertTensorPower ℂ H 0)
    rw [hn] at h2
    exact h2.trans (by norm_num)
  rw [h0, mul_one]
  rfl

theorem kps_zeroFusion (p q : ℕ) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (v : H) :
    kernelProductSymbol (overlapFusionKernel (zeroConfig p q) A B) v =
      kernelProductSymbol A v * kernelProductSymbol B v := by
  unfold kernelProductSymbol
  rw [overlapFusionKernel_apply, ← inner_symProj_right (htpow_mem_symSector _ v),
    left_zeroConfig]
  have h := inner_first_mid p q A B v
  rw [← right_zeroConfig] at h
  exact h

/-- **The diagonal symbol of the zero-overlap product kernel** (every `v`, no normalization):
`⟨v^{⊗(p+q)}, K₀(A,B) v^{⊗(p+q)}⟩ = ⟨v^{⊗p}, A v^{⊗p}⟩ ⟨v^{⊗q}, B v^{⊗q}⟩`. -/
theorem kps_zeroOverlap (p q : ℕ) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (v : H) :
    kernelProductSymbol (averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A B) v =
      kernelProductSymbol A v * kernelProductSymbol B v := by
  rw [QuantumNLS.PlacementFiberCanonicalPrefix.averagedOverlapKernel_eq_overlapFusionKernel _ _
    (zeroConfig p q)]
  exact kps_zeroFusion p q A B v

/-! ### The limiting product kernels and their symbol -/

theorem kps_cast {m n : ℕ} (h : m = n) (K : BoundedSymmetricKernel H m) (v : H) :
    kernelProductSymbol (castSymSectorOperator h K) v = kernelProductSymbol K v := by
  subst h; rfl

theorem kps_zero {n : ℕ} (v : H) :
    kernelProductSymbol (0 : BoundedSymmetricKernel H n) v = 0 := by
  simp [kernelProductSymbol]

theorem kps_sum {n : ℕ} {ι : Type*} (s : Finset ι) (K : ι → BoundedSymmetricKernel H n)
    (v : H) :
    kernelProductSymbol (∑ i ∈ s, K i) v = ∑ i ∈ s, kernelProductSymbol (K i) v := by
  unfold kernelProductSymbol
  rw [_root_.sum_apply, Submodule.coe_sum, inner_sum]

theorem unionSize_zero_sub (j p : ℕ) (h : p ≤ j) : unionSize p (j - p) 0 = j := by
  unfold unionSize; omega

/-- The zero-overlap product kernel of `A_p` and `B_{j-p}`, transported to degree `j`
(zero for `p > j`). -/
def zeroTerm (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j p : ℕ) :
    BoundedSymmetricKernel H j :=
  if h : p ≤ j then
    castSymSectorOperator (unionSize_zero_sub j p h)
      (averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le (j - p)) (Alim p) (Blim (j - p)))
  else 0

/-- **The limiting degree-`j` kernel of a product**: `Σ_{p+q=j} K₀(A_p, B_q)`. -/
def prodLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) :
    BoundedSymmetricKernel H j :=
  ∑ p ∈ range (j + 1), zeroTerm Alim Blim j p

theorem kps_prodLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (j : ℕ) (v : H) :
    kernelProductSymbol (prodLim Alim Blim j) v =
      ∑ kl ∈ antidiagonal j, kernelProductSymbol (Alim kl.1) v *
        kernelProductSymbol (Blim kl.2) v := by
  rw [prodLim, kps_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : p ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  rw [zeroTerm, dif_pos hpj, kps_cast, kps_zeroOverlap]

/-- **Products have product symbols** (Cauchy product of two absolutely convergent series). -/
theorem symbol_prodLim (Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p) (v : H)
    (hA : Summable fun p => ‖kernelProductSymbol (Alim p) v‖)
    (hB : Summable fun p => ‖kernelProductSymbol (Blim p) v‖) :
    symbol (prodLim Alim Blim) v = symbol Alim v * symbol Blim v := by
  unfold symbol
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hA hB]
  exact tsum_congr fun j => kps_prodLim Alim Blim j v

/-- The product-symbol identity for two DEF-042 convergent families on radius `R ≥ 0`, at every
`v` with `‖v‖² ≤ R` (in particular on the source domain `‖v‖² < R`). -/
theorem symbol_prodLim_of_converges {R : ℝ} (hR : 0 ≤ R)
    {A B : ∀ N : ℕ, QuantumNLS.LocalPlacement.KernelList (H := H) N}
    {Alim Blim : ∀ p : ℕ, BoundedSymmetricKernel H p}
    (hA : ConvergesOnRadius R A Alim) (hB : ConvergesOnRadius R B Blim) (v : H)
    (hv : ‖v‖ ^ 2 ≤ R) :
    symbol (prodLim Alim Blim) v = symbol Alim v * symbol Blim v := by
  obtain ⟨_, _, _, _, hAv⟩ := kernel_convergence hR hA
  obtain ⟨_, _, _, _, hBv⟩ := kernel_convergence hR hB
  exact symbol_prodLim Alim Blim v (hAv v hv).1 (hBv v hv).1

end QuantumNLS.Local013ProductSymbol

#print axioms QuantumNLS.Local013ProductSymbol.zeroConfig
#print axioms QuantumNLS.Local013ProductSymbol.kps_zeroFusion
#print axioms QuantumNLS.Local013ProductSymbol.kps_zeroOverlap
#print axioms QuantumNLS.Local013ProductSymbol.kps_sum
#print axioms QuantumNLS.Local013ProductSymbol.kps_prodLim
#print axioms QuantumNLS.Local013ProductSymbol.symbol_prodLim
#print axioms QuantumNLS.Local013ProductSymbol.symbol_prodLim_of_converges
