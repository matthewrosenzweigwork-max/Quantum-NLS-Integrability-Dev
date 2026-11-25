/-
QuantumNLS.TensorCarrier — U2/U3 completed tensor / symmetric-sector chain (owner: opus_tensor).

Source anchors (pinned report commit 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f):
* DEF-004 `def:report-4`, chapters/definitions.tex:25 —
  "The N-particle sector is H_N = Sym^N L²(T_L), the permutation-invariant subspace of the
   ordinary tensor product. The orthogonal projection P_N is the average of the N! permutation
   operators. The zero-particle sector is ℂ."
* DEF-041 `def:local-normalized-placement`, chapters/local/quantum_periods.tex:15 —
  generic complex Hilbert space H, Sym^p H ⊂ H^{⊗p}, placements A_S.
* DEF-030 `def:report-30`, chapters/definitions.tex:181 — partial trace over the last N-k factors.

What this file does (no axioms, no sorry, no assumed target interfaces):
* §1  Generic finite-group averaging.  For any finite group acting by unitaries on a complex
      Hilbert space, the average of the unitaries is the orthogonal projection onto the invariant
      subspace.  This is proved, not assumed.
* §2  The completed binary Hilbert tensor product `HilbertTensor 𝕜 E F`.  It is the metric
      completion of mathlib's algebraic tensor product `E ⊗[𝕜] F`, which is only pre-Hilbert in
      infinite dimension.  Completeness comes from mathlib's `UniformSpace.Completion`, not from a
      hypothesis.
* §3  The N-fold Hilbert tensor power `HilbertTensorPower 𝕜 E n` (completion of `⨂[𝕜]^n E` with
      the inner product `⟪⊗f, ⊗g⟫ = ∏ ⟪f i, g i⟫`, constructed here), the unitary permutation
      representation `permRep`, `SymSector = Sym^n E` (permutation-invariant subspace), and
      `symProj = (n!)⁻¹ ∑_σ U_σ = (SymSector).starProjection`.  This is DEF-004 for a generic
      complex Hilbert space `E`.  The instance `E = L²(𝕋_L)` (DEF-001 carrier) is left to the
      Fourier/DEF-001 owner and is not claimed here.
* §4  `splitIsometry k m : E^{⊗̂(k+m)} ≃ₗᵢ E^{⊗̂k} ⊗̂ E^{⊗̂m}`.  Its proof establishes that
      `TensorPower.mulEquiv` is isometric and that `Completion (A ⊗ B) ≅ Â ⊗̂ B̂`.
* §5  Linearity, composition and adjoint of completed tensor maps:
      `(f ⊗̂ g)† = f† ⊗̂ g†`.
* §6  The reduced density `γ_ψ` of `ψ ∈ X ⊗̂ Y`, constructed basis-free by Riesz duality.  It
      satisfies `⟪γ_ψ φ, φ'⟫ = ⟪ψ, (|φ'⟩⟨φ| ⊗̂ 1) ψ⟫` and is self-adjoint and positive.
* §7  `reducedDensityPower`: the reduced density over the last `m` factors (the operator part
      of DEF-030).  Trace one and the trace norm are NOT asserted, because trace-class
      infrastructure is absent from the pinned mathlib.
-/
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap

open scoped TensorProduct InnerProductSpace

noncomputable section

namespace QuantumNLS.TensorCarrier

/-! ## §1 Finite-group averages of unitary representations are orthogonal projections -/

section GroupAverage

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {G : Type*} [Group G] [Fintype G]

/-- The average `|G|⁻¹ ∑_g ρ(g)` of a unitary representation of a finite group.
For `G = Equiv.Perm (Fin N)` this is the DEF-004 operator `P_N` (average of the `N!`
permutation operators). -/
def groupAverage (ρ : G →* unitary (H →L[𝕜] H)) : H →L[𝕜] H :=
  ((Fintype.card G : 𝕜)⁻¹) • ∑ g, (ρ g : H →L[𝕜] H)

/-- The subspace of vectors fixed by every `ρ g` (the "permutation-invariant subspace"). -/
def fixedSubmodule (ρ : G →* unitary (H →L[𝕜] H)) : Submodule 𝕜 H where
  carrier := {v | ∀ g, (ρ g : H →L[𝕜] H) v = v}
  add_mem' := by
    intro a b ha hb g
    simp [map_add, ha g, hb g]
  zero_mem' := by
    intro g
    simp
  smul_mem' := by
    intro c v hv g
    simp [hv g]

omit [Fintype G] in
lemma mem_fixedSubmodule {ρ : G →* unitary (H →L[𝕜] H)} {v : H} :
    v ∈ fixedSubmodule ρ ↔ ∀ g, (ρ g : H →L[𝕜] H) v = v := Iff.rfl

omit [Fintype G] in
lemma isClosed_fixedSubmodule (ρ : G →* unitary (H →L[𝕜] H)) :
    IsClosed (fixedSubmodule ρ : Set H) := by
  have : (fixedSubmodule ρ : Set H) = ⋂ g, {v | (ρ g : H →L[𝕜] H) v = v} := by
    ext v; simp [mem_fixedSubmodule]
  rw [this]
  exact isClosed_iInter fun g => isClosed_eq (ρ g : H →L[𝕜] H).continuous continuous_id

instance (ρ : G →* unitary (H →L[𝕜] H)) : CompleteSpace (fixedSubmodule ρ) :=
  (isClosed_fixedSubmodule ρ).completeSpace_coe

lemma card_ne_zero_rclike : (Fintype.card G : 𝕜) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

omit [Fintype G] in
lemma coe_rep_mul (ρ : G →* unitary (H →L[𝕜] H)) (g h : G) :
    (ρ g : H →L[𝕜] H) * (ρ h : H →L[𝕜] H) = (ρ (g * h) : H →L[𝕜] H) := by
  rw [map_mul]; rfl

theorem rep_mul_groupAverage (ρ : G →* unitary (H →L[𝕜] H)) (h : G) :
    (ρ h : H →L[𝕜] H) * groupAverage ρ = groupAverage ρ := by
  unfold groupAverage
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [coe_rep_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => rfl)

theorem groupAverage_mul_rep (ρ : G →* unitary (H →L[𝕜] H)) (h : G) :
    groupAverage ρ * (ρ h : H →L[𝕜] H) = groupAverage ρ := by
  unfold groupAverage
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp_rw [coe_rep_mul]
  exact Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => rfl)

theorem rep_groupAverage_apply (ρ : G →* unitary (H →L[𝕜] H)) (h : G) (v : H) :
    (ρ h : H →L[𝕜] H) (groupAverage ρ v) = groupAverage ρ v := by
  simpa using congrArg (fun T : H →L[𝕜] H => T v) (rep_mul_groupAverage ρ h)

theorem groupAverage_idempotent (ρ : G →* unitary (H →L[𝕜] H)) :
    IsIdempotentElem (groupAverage ρ) := by
  have e : groupAverage ρ = ((Fintype.card G : 𝕜)⁻¹) • ∑ g, (ρ g : H →L[𝕜] H) := rfl
  unfold IsIdempotentElem
  conv_lhs => arg 2; rw [e]
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [groupAverage_mul_rep]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ card_ne_zero_rclike, one_smul]

theorem groupAverage_isSelfAdjoint (ρ : G →* unitary (H →L[𝕜] H)) :
    IsSelfAdjoint (groupAverage ρ) := by
  unfold IsSelfAdjoint groupAverage
  rw [star_smul, star_sum]
  have hc : star ((Fintype.card G : 𝕜)⁻¹) = (Fintype.card G : 𝕜)⁻¹ := by
    rw [star_inv₀, star_natCast]
  rw [hc]
  congr 1
  have hs : ∀ g, star (ρ g : H →L[𝕜] H) = (ρ g⁻¹ : H →L[𝕜] H) := by
    intro g
    rw [← Unitary.coe_star, Unitary.star_eq_inv, map_inv]
  simp_rw [hs]
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun g => rfl)

theorem groupAverage_isStarProjection (ρ : G →* unitary (H →L[𝕜] H)) :
    IsStarProjection (groupAverage ρ) :=
  ⟨groupAverage_idempotent ρ, groupAverage_isSelfAdjoint ρ⟩

theorem groupAverage_apply_of_mem (ρ : G →* unitary (H →L[𝕜] H)) {v : H}
    (hv : v ∈ fixedSubmodule ρ) : groupAverage ρ v = v := by
  have hv' : ∀ g, (ρ g : H →L[𝕜] H) v = v := mem_fixedSubmodule.mp hv
  have : groupAverage ρ v = ((Fintype.card G : 𝕜)⁻¹) • ∑ g : G, (ρ g : H →L[𝕜] H) v := by
    simp [groupAverage]
  simp_rw [this, hv']
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ card_ne_zero_rclike, one_smul]

theorem range_groupAverage (ρ : G →* unitary (H →L[𝕜] H)) :
    (groupAverage ρ).range = fixedSubmodule ρ := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact fun g => rep_groupAverage_apply ρ g w
  · intro hv
    exact ⟨v, groupAverage_apply_of_mem ρ hv⟩

/-- **DEF-004 mechanism.** The average of the representing unitaries is *the* orthogonal
projection onto the invariant subspace. -/
theorem groupAverage_eq_starProjection (ρ : G →* unitary (H →L[𝕜] H)) :
    groupAverage ρ = (fixedSubmodule ρ).starProjection := by
  apply ContinuousLinearMap.IsStarProjection.ext (groupAverage_isStarProjection ρ)
    isStarProjection_starProjection
  rw [range_groupAverage, Submodule.range_starProjection]

end GroupAverage

/-! ## §2 The completed (Hilbert) binary tensor product -/

section HilbertTensor

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The Hilbert-space tensor product `E ⊗̂ F`: the completion of the algebraic tensor product
`E ⊗[𝕜] F` for the inner product `⟪a ⊗ b, c ⊗ d⟫ = ⟪a,c⟫⟪b,d⟫`.  This is a *construction*,
not an assumed interface; completeness comes from `UniformSpace.Completion`. -/
abbrev HilbertTensor : Type _ := UniformSpace.Completion (E ⊗[𝕜] F)

example : CompleteSpace (HilbertTensor 𝕜 E F) := inferInstance
example : InnerProductSpace 𝕜 (HilbertTensor 𝕜 E F) := inferInstance

variable {𝕜 E F}

/-- The elementary tensor `x ⊗ y` inside the completed tensor product. -/
def htmul (x : E) (y : F) : HilbertTensor 𝕜 E F :=
  ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : UniformSpace.Completion (E ⊗[𝕜] F))

theorem inner_htmul (x x' : E) (y y' : F) :
    ⟪(htmul x y : HilbertTensor 𝕜 E F), htmul x' y'⟫_𝕜 = ⟪x, x'⟫_𝕜 * ⟪y, y'⟫_𝕜 := by
  simp [htmul, UniformSpace.Completion.inner_coe]

theorem norm_htmul (x : E) (y : F) :
    ‖(htmul x y : HilbertTensor 𝕜 E F)‖ = ‖x‖ * ‖y‖ := by
  simp [htmul, UniformSpace.Completion.norm_coe]

/-- `htmul` is additive and homogeneous in each slot (it is the bilinear map
`(x, y) ↦ ↑(x ⊗ₜ y)`). -/
theorem htmul_add_left (x x' : E) (y : F) :
    (htmul (x + x') y : HilbertTensor 𝕜 E F) = htmul x y + htmul x' y := by
  simp [htmul, TensorProduct.add_tmul, UniformSpace.Completion.coe_add]

theorem htmul_add_right (x : E) (y y' : F) :
    (htmul x (y + y') : HilbertTensor 𝕜 E F) = htmul x y + htmul x y' := by
  simp [htmul, TensorProduct.tmul_add, UniformSpace.Completion.coe_add]

theorem htmul_smul_left (c : 𝕜) (x : E) (y : F) :
    (htmul (c • x) y : HilbertTensor 𝕜 E F) = c • htmul x y := by
  rw [htmul, htmul, ← TensorProduct.smul_tmul', UniformSpace.Completion.coe_smul]

theorem htmul_smul_right (c : 𝕜) (x : E) (y : F) :
    (htmul x (c • y) : HilbertTensor 𝕜 E F) = c • htmul x y := by
  rw [htmul, htmul, TensorProduct.tmul_smul, UniformSpace.Completion.coe_smul]

/-- The linear span of elementary tensors is dense in the completed tensor product. -/
theorem span_htmul_dense :
    (Submodule.span 𝕜 (Set.range fun p : E × F => (htmul p.1 p.2 : HilbertTensor 𝕜 E F))
      ).topologicalClosure = ⊤ := by
  let ι : (E ⊗[𝕜] F) →L[𝕜] HilbertTensor 𝕜 E F := UniformSpace.Completion.toComplL
  have hrange : (Set.range fun p : E × F => p.1 ⊗ₜ[𝕜] p.2) =
      { t : E ⊗[𝕜] F | ∃ m n, m ⊗ₜ n = t } := by
    ext t; simp
  have hspan : Submodule.span 𝕜 (Set.range fun p : E × F => (htmul p.1 p.2 :
      HilbertTensor 𝕜 E F)) = (ι : (E ⊗[𝕜] F) →ₗ[𝕜] _).range := by
    have : (Set.range fun p : E × F => (htmul p.1 p.2 : HilbertTensor 𝕜 E F)) =
        (ι : (E ⊗[𝕜] F) →ₗ[𝕜] _) '' (Set.range fun p : E × F => p.1 ⊗ₜ[𝕜] p.2) := by
      ext z; simp [htmul, ι]
    rw [this, Submodule.span_image, hrange, TensorProduct.span_tmul_eq_top, Submodule.map_top]
  rw [hspan, ← Submodule.dense_iff_topologicalClosure_eq_top]
  have hd : DenseRange ((↑) : E ⊗[𝕜] F → UniformSpace.Completion (E ⊗[𝕜] F)) :=
    UniformSpace.Completion.denseRange_coe
  have hset : ((LinearMap.range (ι : (E ⊗[𝕜] F) →ₗ[𝕜] HilbertTensor 𝕜 E F) :
      Submodule 𝕜 (HilbertTensor 𝕜 E F)) : Set (HilbertTensor 𝕜 E F)) =
      Set.range ((↑) : E ⊗[𝕜] F → UniformSpace.Completion (E ⊗[𝕜] F)) := by
    ext z; simp [ι]
  rw [hset]
  exact hd

variable {G K : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- Operator norm of the extension of a bounded operator to the completion does not exceed the
original norm. -/
theorem norm_completion_le {V W : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace 𝕜 W] (f : V →L[𝕜] W) :
    ‖f.completion‖ ≤ ‖f‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_le (continuous_norm.comp f.completion.continuous)
      (continuous_const.mul continuous_norm)
  | ih a =>
    rw [ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.norm_coe,
      UniformSpace.Completion.norm_coe]
    exact f.le_opNorm a

/-- `f ⊗̂ g` on completed tensor products: the continuous extension of `TensorProduct.mapL f g`. -/
def htmap (f : E →L[𝕜] G) (g : F →L[𝕜] K) : HilbertTensor 𝕜 E F →L[𝕜] HilbertTensor 𝕜 G K :=
  (TensorProduct.mapL f g).completion

@[simp] theorem htmap_htmul (f : E →L[𝕜] G) (g : F →L[𝕜] K) (x : E) (y : F) :
    htmap f g (htmul x y) = htmul (f x) (g y) := by
  simp [htmap, htmul, ContinuousLinearMap.completion_apply_coe]

theorem norm_htmap_le (f : E →L[𝕜] G) (g : F →L[𝕜] K) : ‖htmap f g‖ ≤ ‖f‖ * ‖g‖ :=
  (norm_completion_le _).trans (TensorProduct.norm_mapL_le f g)

variable (𝕜 E F) in
/-- The flip `E ⊗̂ F ≃ F ⊗̂ E` as a linear isometry, extending `TensorProduct.commIsometry`. -/
def htcommIsometry : HilbertTensor 𝕜 E F →ₗᵢ[𝕜] HilbertTensor 𝕜 F E :=
  (TensorProduct.commIsometry 𝕜 E F).toLinearIsometry.completion

@[simp] theorem htcommIsometry_htmul (x : E) (y : F) :
    htcommIsometry 𝕜 E F (htmul x y) = htmul y x := by
  simp [htcommIsometry, htmul, LinearIsometry.completion_apply_coe]

theorem htcommIsometry_htcommIsometry (z : HilbertTensor 𝕜 E F) :
    htcommIsometry 𝕜 F E (htcommIsometry 𝕜 E F z) = z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq ((htcommIsometry 𝕜 F E).continuous.comp (htcommIsometry 𝕜 E F).continuous)
      continuous_id
  | ih a =>
    simp only [htcommIsometry, LinearIsometry.completion_apply_coe]
    simp

end HilbertTensor

/-! ## §3 The N-fold Hilbert tensor power, permutation unitaries, `Sym^N` and `P_N`

The algebraic power `⨂[𝕜]^n E` (mathlib `TensorPower`, i.e. `PiTensorProduct` over `Fin n`)
carries the pre-Hilbert inner product `⟪⊗ f, ⊗ g⟫ = ∏ ⟪f i, g i⟫`.  Mathlib provides no such
instance (it provides an unrelated *projective* seminorm on `PiTensorProduct`), so we construct the
inner product by transport along `⨂^(n+1) ≃ ⨂^n ⊗ E` and work on a type synonym to avoid any
instance diamond.  The Hilbert power is the completion.  -/

section TensorPowerInner

variable (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Pull back an inner-product core along a linear equivalence into an inner product space. -/
@[instance_reducible]
def coreComap {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [NormedAddCommGroup W]
    [InnerProductSpace 𝕜 W] (e : V ≃ₗ[𝕜] W) : InnerProductSpace.Core 𝕜 V where
  inner x y := ⟪e x, e y⟫_𝕜
  conj_inner_symm x y := inner_conj_symm _ _
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by simp only [map_add, inner_add_left]
  smul_left x y r := by simp only [map_smul, inner_smul_left]
  definite x hx := e.injective (by rw [map_zero]; exact inner_self_eq_zero.mp hx)

/-- `⨂^n E ⊗ E ≃ ⨂^(n+1) E`, `(⊗ a) ⊗ x ↦ ⊗ (Fin.snoc a x)`. -/
def succEquiv (n : ℕ) : (⨂[𝕜]^n E) ⊗[𝕜] E ≃ₗ[𝕜] ⨂[𝕜]^(n + 1) E :=
  (TensorProduct.congr (LinearEquiv.refl 𝕜 _)
    (PiTensorProduct.subsingletonEquiv (R := 𝕜) (s := fun _ : Fin 1 => E) 0).symm).trans
    TensorPower.mulEquiv

theorem succEquiv_tmul (n : ℕ) (a : Fin n → E) (x : E) :
    succEquiv 𝕜 E n (PiTensorProduct.tprod 𝕜 a ⊗ₜ x) =
      PiTensorProduct.tprod 𝕜 (Fin.snoc a x : Fin (n + 1) → E) := by
  simp only [succEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    PiTensorProduct.subsingletonEquiv_symm_apply']
  rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod, Fin.append_right_eq_snoc]

theorem succEquiv_symm_tprod (n : ℕ) (f : Fin (n + 1) → E) :
    (succEquiv 𝕜 E n).symm (PiTensorProduct.tprod 𝕜 f) =
      PiTensorProduct.tprod 𝕜 (Fin.init f) ⊗ₜ f (Fin.last n) := by
  rw [LinearEquiv.symm_apply_eq, succEquiv_tmul, Fin.snoc_init_self]

/-- The inner-product core on `⨂[𝕜]^n E`, defined by recursion on `n`. -/
@[instance_reducible]
def powCore : (n : ℕ) → InnerProductSpace.Core 𝕜 (⨂[𝕜]^n E)
  | 0 => coreComap 𝕜 (PiTensorProduct.isEmptyEquiv (R := 𝕜) (s := fun _ : Fin 0 => E) (Fin 0))
  | n + 1 =>
    letI cd : InnerProductSpace.Core 𝕜 (⨂[𝕜]^n E) := powCore n
    letI : NormedAddCommGroup (⨂[𝕜]^n E) := cd.toNormedAddCommGroup
    letI : InnerProductSpace 𝕜 (⨂[𝕜]^n E) := .ofCore cd.toCore
    coreComap 𝕜 (succEquiv 𝕜 E n).symm

theorem powCore_inner_tprod : ∀ (n : ℕ) (f g : Fin n → E),
    (powCore 𝕜 E n).inner (PiTensorProduct.tprod 𝕜 f) (PiTensorProduct.tprod 𝕜 g) =
      ∏ i, ⟪f i, g i⟫_𝕜
  | 0, f, g => by
    show ⟪PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.tprod 𝕜 f),
      PiTensorProduct.isEmptyEquiv (Fin 0) (PiTensorProduct.tprod 𝕜 g)⟫_𝕜 = _
    simp [PiTensorProduct.isEmptyEquiv_apply_tprod]
  | n + 1, f, g => by
    let cd : InnerProductSpace.Core 𝕜 (⨂[𝕜]^n E) := powCore 𝕜 E n
    let _ : NormedAddCommGroup (⨂[𝕜]^n E) := cd.toNormedAddCommGroup
    let _ : InnerProductSpace 𝕜 (⨂[𝕜]^n E) := .ofCore cd.toCore
    show ⟪(succEquiv 𝕜 E n).symm (PiTensorProduct.tprod 𝕜 f),
      (succEquiv 𝕜 E n).symm (PiTensorProduct.tprod 𝕜 g)⟫_𝕜 = _
    rw [succEquiv_symm_tprod, succEquiv_symm_tprod, TensorProduct.inner_tmul,
      Fin.prod_univ_castSucc]
    congr 1
    exact powCore_inner_tprod n (Fin.init f) (Fin.init g)

/-- Type synonym for the algebraic tensor power carrying the Hilbert (not projective) inner
product.  It is only a pre-Hilbert space. -/
def AlgTensorPower (n : ℕ) : Type _ := ⨂[𝕜]^n E

-- Only the normed structure is declared; `AddCommGroup`/`Module` are derived from it so that a
-- single algebraic structure is in play (the underlying one is `PiTensorProduct`'s).
instance (n : ℕ) : NormedAddCommGroup (AlgTensorPower 𝕜 E n) :=
  (powCore 𝕜 E n : InnerProductSpace.Core 𝕜 (⨂[𝕜]^n E)).toNormedAddCommGroup

instance (n : ℕ) : InnerProductSpace 𝕜 (AlgTensorPower 𝕜 E n) :=
  .ofCore (powCore 𝕜 E n : InnerProductSpace.Core 𝕜 (⨂[𝕜]^n E)).toCore

variable {𝕜 E}

/-- The elementary tensor `f 0 ⊗ ⋯ ⊗ f (n-1)` in the algebraic power. -/
def ptprod {n : ℕ} (f : Fin n → E) : AlgTensorPower 𝕜 E n := PiTensorProduct.tprod 𝕜 f

/-- Induction principle on the synonym (scaled elementary tensors and sums). -/
@[elab_as_elim]
theorem AlgTensorPower.induction_on {n : ℕ} {motive : AlgTensorPower 𝕜 E n → Prop}
    (z : AlgTensorPower 𝕜 E n)
    (smul_ptprod : ∀ (r : 𝕜) (f : Fin n → E), motive (r • ptprod f))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  PiTensorProduct.induction_on (motive := motive) z smul_ptprod add

theorem inner_ptprod {n : ℕ} (f g : Fin n → E) :
    ⟪(ptprod f : AlgTensorPower 𝕜 E n), ptprod g⟫_𝕜 = ∏ i, ⟪f i, g i⟫_𝕜 :=
  powCore_inner_tprod 𝕜 E n f g

theorem norm_ptprod {n : ℕ} (f : Fin n → E) :
    ‖(ptprod f : AlgTensorPower 𝕜 E n)‖ = ∏ i, ‖f i‖ := by
  have h := inner_ptprod (𝕜 := 𝕜) f f
  rw [inner_self_eq_norm_sq_to_K] at h
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [Finset.prod_pow] at h
  have h' : ‖(ptprod f : AlgTensorPower 𝕜 E n)‖ ^ 2 = (∏ i, ‖f i‖) ^ 2 := by
    exact_mod_cast (by simpa using h : ((‖(ptprod f : AlgTensorPower 𝕜 E n)‖ : 𝕜)) ^ 2 =
      ((∏ i, ‖f i‖ : ℝ) : 𝕜) ^ 2)
  exact (sq_eq_sq₀ (norm_nonneg _) (Finset.prod_nonneg fun i _ => norm_nonneg _)).mp h'

/-- Permutation of tensor factors, `⊗ f ↦ ⊗ (f ∘ σ⁻¹)`, on the algebraic power. -/
def permLinearEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    AlgTensorPower 𝕜 E n ≃ₗ[𝕜] AlgTensorPower 𝕜 E n :=
  PiTensorProduct.reindex 𝕜 (fun _ : Fin n => E) σ

theorem permLinearEquiv_ptprod {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Fin n → E) :
    permLinearEquiv σ (ptprod f : AlgTensorPower 𝕜 E n) = ptprod (fun i => f (σ.symm i)) :=
  PiTensorProduct.reindex_tprod σ f

theorem permLinearEquiv_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (x : AlgTensorPower 𝕜 E n) :
    permLinearEquiv (σ * τ) x = permLinearEquiv σ (permLinearEquiv τ x) :=
  (PiTensorProduct.reindex_reindex (R := 𝕜) (s := fun _ : Fin n => E) τ σ x).symm

theorem permLinearEquiv_one {n : ℕ} (x : AlgTensorPower 𝕜 E n) :
    permLinearEquiv 1 x = x := by
  show PiTensorProduct.reindex 𝕜 (fun _ : Fin n => E) (Equiv.refl (Fin n)) x = x
  rw [PiTensorProduct.reindex_refl]
  rfl

theorem inner_permLinearEquiv {n : ℕ} (σ : Equiv.Perm (Fin n)) (x y : AlgTensorPower 𝕜 E n) :
    ⟪permLinearEquiv σ x, permLinearEquiv σ y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  induction x using AlgTensorPower.induction_on with
  | smul_ptprod r f =>
    induction y using AlgTensorPower.induction_on with
    | smul_ptprod r' g =>
      simp only [map_smul, inner_smul_left, inner_smul_right, permLinearEquiv_ptprod,
        inner_ptprod]
      congr 2
      exact Equiv.prod_comp σ.symm (fun i => ⟪f i, g i⟫_𝕜)
    | add y y' hy hy' => simp only [map_add, inner_add_right, hy, hy']
  | add x x' hx hx' => simp only [map_add, inner_add_left, hx, hx']

/-- Permutations act by linear isometries on the algebraic power. -/
def permIsometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    AlgTensorPower 𝕜 E n ≃ₗᵢ[𝕜] AlgTensorPower 𝕜 E n :=
  (permLinearEquiv σ).isometryOfInner (inner_permLinearEquiv σ)

end TensorPowerInner

section Completion

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Completion of a linear isometry equivalence. -/
def lieCompletion {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (e : V ≃ₗᵢ[𝕜] W) :
    UniformSpace.Completion V ≃ₗᵢ[𝕜] UniformSpace.Completion W :=
  LinearIsometryEquiv.ofSurjective e.toLinearIsometry.completion (by
    intro z
    refine ⟨e.symm.toLinearIsometry.completion z, ?_⟩
    induction z using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq (e.toLinearIsometry.completion.continuous.comp
        e.symm.toLinearIsometry.completion.continuous) continuous_id
    | ih a =>
      rw [LinearIsometry.completion_apply_coe, LinearIsometry.completion_apply_coe]
      simp)

theorem lieCompletion_coe {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (e : V ≃ₗᵢ[𝕜] W) (x : V) :
    lieCompletion e (x : UniformSpace.Completion V) = (e x : UniformSpace.Completion W) := by
  show e.toLinearIsometry.completion (x : UniformSpace.Completion V) = _
  rw [LinearIsometry.completion_apply_coe]
  rfl

end Completion

section HilbertTensorPower

variable (𝕜 : Type*) [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The completed (Hilbert) tensor power `E^{⊗̂ n}`. -/
abbrev HilbertTensorPower (n : ℕ) : Type _ := UniformSpace.Completion (AlgTensorPower 𝕜 E n)

example (n : ℕ) : CompleteSpace (HilbertTensorPower 𝕜 E n) := inferInstance

variable {𝕜 E}

/-- `u^{⊗ n}` in the completed tensor power. -/
def htpow (n : ℕ) (u : E) : HilbertTensorPower 𝕜 E n :=
  ((ptprod (fun _ : Fin n => u) : AlgTensorPower 𝕜 E n) : UniformSpace.Completion _)

theorem norm_htpow (n : ℕ) (u : E) : ‖(htpow n u : HilbertTensorPower 𝕜 E n)‖ = ‖u‖ ^ n := by
  simp [htpow, UniformSpace.Completion.norm_coe, norm_ptprod]

/-- Permutation unitaries on the completed tensor power. -/
def permHilbertIsometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    HilbertTensorPower 𝕜 E n ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 E n :=
  lieCompletion (permIsometry σ)

theorem permHilbertIsometry_coe {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : AlgTensorPower 𝕜 E n) :
    permHilbertIsometry σ (x : HilbertTensorPower 𝕜 E n) = ((permLinearEquiv σ x :
      AlgTensorPower 𝕜 E n) : HilbertTensorPower 𝕜 E n) := by
  rw [permHilbertIsometry, lieCompletion_coe]
  rfl

variable (𝕜 E) in
/-- The permutation representation `σ ↦ U_σ` as a group homomorphism into linear isometric
equivalences of the completed tensor power. -/
def permHom (n : ℕ) : Equiv.Perm (Fin n) →* (HilbertTensorPower 𝕜 E n ≃ₗᵢ[𝕜]
    HilbertTensorPower 𝕜 E n) where
  toFun := permHilbertIsometry
  map_one' := by
    ext z
    induction z using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_eq (permHilbertIsometry 1).continuous continuous_id
    | ih a =>
      rw [permHilbertIsometry_coe, permLinearEquiv_one]
      rfl
  map_mul' σ τ := by
    ext z
    induction z using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq (permHilbertIsometry (σ * τ)).continuous
        ((permHilbertIsometry σ).continuous.comp (permHilbertIsometry τ).continuous)
    | ih a =>
      rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, permHilbertIsometry_coe,
        permHilbertIsometry_coe, permHilbertIsometry_coe, permLinearEquiv_mul]

variable (𝕜 E) in
/-- The unitary permutation representation of `S_n` on `E^{⊗̂ n}`. -/
def permRep (n : ℕ) : Equiv.Perm (Fin n) →* unitary (HilbertTensorPower 𝕜 E n →L[𝕜]
    HilbertTensorPower 𝕜 E n) :=
  (Unitary.linearIsometryEquiv (𝕜 := 𝕜) (H := HilbertTensorPower 𝕜 E n)).symm.toMonoidHom.comp
    (permHom 𝕜 E n)

theorem permRep_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : HilbertTensorPower 𝕜 E n) :
    (permRep 𝕜 E n σ : HilbertTensorPower 𝕜 E n →L[𝕜] HilbertTensorPower 𝕜 E n) z =
      permHilbertIsometry σ z := rfl

variable (𝕜 E) in
/-- **DEF-004 carrier (generic Hilbert space).** `Sym^n E`: the permutation-invariant closed
subspace of the completed tensor power. -/
abbrev SymSector (n : ℕ) : Submodule 𝕜 (HilbertTensorPower 𝕜 E n) := fixedSubmodule (permRep 𝕜 E n)

variable (𝕜 E) in
/-- **DEF-004 projection.** `P_n`, the average of the `n!` permutation operators. -/
def symProj (n : ℕ) : HilbertTensorPower 𝕜 E n →L[𝕜] HilbertTensorPower 𝕜 E n :=
  groupAverage (permRep 𝕜 E n)

/-- `P_n = (n!)⁻¹ ∑_σ U_σ` — the literal DEF-004 formula. -/
theorem symProj_eq_factorial_average (n : ℕ) :
    symProj 𝕜 E n = ((n.factorial : 𝕜)⁻¹) •
      ∑ σ : Equiv.Perm (Fin n), (permRep 𝕜 E n σ : HilbertTensorPower 𝕜 E n →L[𝕜] _) := by
  rw [symProj, groupAverage, Fintype.card_perm, Fintype.card_fin]

/-- **DEF-004.** `P_n` is the orthogonal projection onto `Sym^n E`. -/
theorem symProj_eq_starProjection (n : ℕ) :
    symProj 𝕜 E n = (SymSector 𝕜 E n).starProjection :=
  groupAverage_eq_starProjection _

theorem symProj_isStarProjection (n : ℕ) : IsStarProjection (symProj 𝕜 E n) :=
  groupAverage_isStarProjection _

/-- `u^{⊗ n}` lies in the symmetric sector (DEF-003's bosonic product is a sector vector). -/
theorem htpow_mem_symSector (n : ℕ) (u : E) : (htpow n u : HilbertTensorPower 𝕜 E n) ∈
    SymSector 𝕜 E n := by
  intro σ
  rw [permRep_apply, htpow, permHilbertIsometry_coe]
  congr 1
  exact permLinearEquiv_ptprod σ _

end HilbertTensorPower

/-! ## §4 Splitting `E^{⊗̂(k+m)} ≅ E^{⊗̂k} ⊗̂ E^{⊗̂m}` (roadmap R1)

This is the factor placement used by "the last `N-k` physical factors" (DEF-030) and by the
placements `A_S` (DEF-041).  Two genuine steps:
(a) `TensorPower.mulEquiv` is isometric for the §3 inner products;
(b) `Completion (A ⊗ B) ≅ Â ⊗̂ B̂` for pre-Hilbert `A, B` (density + closed range). -/

section Split

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A linear map preserves inner products as soon as it does so on a spanning set. -/
theorem inner_map_map_of_span {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] (f : V →ₗ[𝕜] W) {s : Set V}
    (hs : Submodule.span 𝕜 s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜) (x y : V) :
    ⟪f x, f y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  have hx : x ∈ Submodule.span 𝕜 s := hs ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span 𝕜 s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy => exact h x hx y hy
    | zero => simp
    | add y y' _ _ h1 h2 => simp only [map_add, inner_add_right, h1, h2]
    | smul c y _ h1 => simp only [map_smul, inner_smul_right, h1]
  | zero => simp
  | add x x' _ _ h1 h2 => simp only [map_add, inner_add_left, h1 y hy, h2 y hy]
  | smul c x _ h1 => simp only [map_smul, inner_smul_left, h1 y hy]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem span_range_ptprod (n : ℕ) :
    Submodule.span 𝕜 (Set.range (ptprod : (Fin n → E) → AlgTensorPower 𝕜 E n)) = ⊤ :=
  PiTensorProduct.span_tprod_eq_top

theorem span_ptprod_tmul (k m : ℕ) :
    Submodule.span 𝕜 (Set.range fun p : (Fin k → E) × (Fin m → E) =>
      (ptprod p.1 : AlgTensorPower 𝕜 E k) ⊗ₜ[𝕜] (ptprod p.2 : AlgTensorPower 𝕜 E m)) = ⊤ := by
  rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
  rintro _ ⟨u, v, rfl⟩
  have hu : u ∈ Submodule.span 𝕜 (Set.range (ptprod : (Fin k → E) → AlgTensorPower 𝕜 E k)) := by
    rw [span_range_ptprod]; exact Submodule.mem_top
  have hv : v ∈ Submodule.span 𝕜 (Set.range (ptprod : (Fin m → E) → AlgTensorPower 𝕜 E m)) := by
    rw [span_range_ptprod]; exact Submodule.mem_top
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      exact Submodule.subset_span ⟨(a, b), rfl⟩
    | zero => rw [TensorProduct.tmul_zero]; exact zero_mem _
    | add v v' _ _ h1 h2 => rw [TensorProduct.tmul_add]; exact add_mem h1 h2
    | smul c v _ h1 => rw [TensorProduct.tmul_smul]; exact Submodule.smul_mem _ c h1
  | zero => rw [TensorProduct.zero_tmul]; exact zero_mem _
  | add u u' _ _ h1 h2 => rw [TensorProduct.add_tmul]; exact add_mem h1 h2
  | smul c u _ h1 => rw [← TensorProduct.smul_tmul']; exact Submodule.smul_mem _ c h1

/-- `⨂^k E ⊗ ⨂^m E ≃ ⨂^(k+m) E` (mathlib `TensorPower.mulEquiv`) on the synonyms. -/
def mulLinearEquiv (k m : ℕ) :
    (AlgTensorPower 𝕜 E k ⊗[𝕜] AlgTensorPower 𝕜 E m) ≃ₗ[𝕜] AlgTensorPower 𝕜 E (k + m) :=
  TensorPower.mulEquiv (R := 𝕜) (M := E) (n := k) (m := m)

theorem mulLinearEquiv_tmul {k m : ℕ} (a : Fin k → E) (b : Fin m → E) :
    mulLinearEquiv k m ((ptprod a : AlgTensorPower 𝕜 E k) ⊗ₜ[𝕜] (ptprod b : AlgTensorPower 𝕜 E m))
      = ptprod (Fin.append a b) := by
  show TensorPower.mulEquiv (PiTensorProduct.tprod 𝕜 a ⊗ₜ[𝕜] PiTensorProduct.tprod 𝕜 b) = _
  rw [← TensorPower.gMul_def, TensorPower.tprod_mul_tprod]
  rfl

theorem inner_mulLinearEquiv (k m : ℕ) (x y : AlgTensorPower 𝕜 E k ⊗[𝕜] AlgTensorPower 𝕜 E m) :
    ⟪mulLinearEquiv k m x, mulLinearEquiv k m y⟫_𝕜 = ⟪x, y⟫_𝕜 := by
  refine inner_map_map_of_span (mulLinearEquiv k m).toLinearMap (span_ptprod_tmul k m) ?_ x y
  rintro _ ⟨⟨a, b⟩, rfl⟩ _ ⟨⟨a', b'⟩, rfl⟩
  simp only [LinearEquiv.coe_coe, mulLinearEquiv_tmul, inner_ptprod, TensorProduct.inner_tmul,
    Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- (a) The algebraic splitting is a linear isometry equivalence. -/
def mulIsometry (k m : ℕ) :
    (AlgTensorPower 𝕜 E k ⊗[𝕜] AlgTensorPower 𝕜 E m) ≃ₗᵢ[𝕜] AlgTensorPower 𝕜 E (k + m) :=
  (mulLinearEquiv k m).isometryOfInner (inner_mulLinearEquiv k m)

variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
  [NormedAddCommGroup B] [InnerProductSpace 𝕜 B]

/-- The isometry `A ⊗ B → Â ⊗ B̂` induced by the completion embeddings. -/
abbrev complTensorIncl : (A ⊗[𝕜] B) →ₗᵢ[𝕜]
    (UniformSpace.Completion A ⊗[𝕜] UniformSpace.Completion B) :=
  TensorProduct.mapIsometry (UniformSpace.Completion.toComplₗᵢ : A →ₗᵢ[𝕜] _)
    (UniformSpace.Completion.toComplₗᵢ : B →ₗᵢ[𝕜] _)

/-- `A ⊗ B` is dense in `Â ⊗ B̂` (algebraic tensor product of the completions). -/
theorem denseRange_complTensorIncl : DenseRange (complTensorIncl (𝕜 := 𝕜) (A := A) (B := B)) := by
  set j := complTensorIncl (𝕜 := 𝕜) (A := A) (B := B)
  let R : Submodule 𝕜 (UniformSpace.Completion A ⊗[𝕜] UniformSpace.Completion B) :=
    (LinearMap.range j.toLinearMap).topologicalClosure
  have htm : ∀ x y, x ⊗ₜ[𝕜] y ∈ R := by
    intro x y
    refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
    · have hc : Continuous (fun p : UniformSpace.Completion A × UniformSpace.Completion B =>
          p.1 ⊗ₜ[𝕜] p.2) :=
        (TensorProduct.mkL 𝕜 (UniformSpace.Completion A) (UniformSpace.Completion B)).continuous₂
      exact (LinearMap.range j.toLinearMap).isClosed_topologicalClosure.preimage hc
    · intro a b
      apply Submodule.le_topologicalClosure
      exact ⟨a ⊗ₜ[𝕜] b, by simp [j]⟩
  have hR : R = ⊤ := by
    rw [eq_top_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨x, y, rfl⟩
    exact htm x y
  have hset : (R : Set (UniformSpace.Completion A ⊗[𝕜] UniformSpace.Completion B)) =
      closure (Set.range j) := by
    rw [Submodule.topologicalClosure_coe]
    congr 1
  rw [DenseRange, dense_iff_closure_eq, ← hset, hR, Submodule.top_coe]

/-- (b) `Completion (A ⊗ B) ≃ Â ⊗̂ B̂`: the extension of `A ⊗ B → Â ⊗ B̂ → Â ⊗̂ B̂`. -/
def complTensorIsometry : UniformSpace.Completion (A ⊗[𝕜] B) ≃ₗᵢ[𝕜]
    HilbertTensor 𝕜 (UniformSpace.Completion A) (UniformSpace.Completion B) :=
  let J0 : (A ⊗[𝕜] B) →ₗᵢ[𝕜] HilbertTensor 𝕜 (UniformSpace.Completion A)
      (UniformSpace.Completion B) :=
    (UniformSpace.Completion.toComplₗᵢ).comp complTensorIncl
  LinearIsometryEquiv.ofSurjective J0.fromCompletion (by
    have hclosed : IsClosed (Set.range J0.fromCompletion) :=
      J0.fromCompletion.isometry.isClosedEmbedding.isClosed_range
    have h1 : DenseRange (((↑) : (UniformSpace.Completion A ⊗[𝕜] UniformSpace.Completion B) →
        HilbertTensor 𝕜 (UniformSpace.Completion A) (UniformSpace.Completion B)) ∘
          complTensorIncl (𝕜 := 𝕜) (A := A) (B := B)) :=
      UniformSpace.Completion.denseRange_coe.comp denseRange_complTensorIncl
        (UniformSpace.Completion.continuous_coe _)
    have hdense : DenseRange J0.fromCompletion := by
      refine Dense.mono ?_ h1
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : UniformSpace.Completion (A ⊗[𝕜] B)), by
        rw [LinearIsometry.fromCompletion_apply_coe]; rfl⟩
    intro z
    have : z ∈ closure (Set.range J0.fromCompletion) := by
      rw [hdense.closure_range]; exact Set.mem_univ z
    rw [hclosed.closure_eq] at this
    exact this)

theorem complTensorIsometry_coe_tmul (a : A) (b : B) :
    complTensorIsometry (((a ⊗ₜ[𝕜] b : A ⊗[𝕜] B)) : UniformSpace.Completion (A ⊗[𝕜] B)) =
      htmul (a : UniformSpace.Completion A) (b : UniformSpace.Completion B) := by
  show LinearIsometry.fromCompletion _ _ = _
  rw [LinearIsometry.fromCompletion_apply_coe]
  rfl

/-- **R1.** `E^{⊗̂(k+m)} ≃ₗᵢ E^{⊗̂k} ⊗̂ E^{⊗̂m}`, sending `⊗(a ++ b) ↦ (⊗a) ⊗ (⊗b)`; the second
factor is "the last `m` positions". -/
def splitIsometry (k m : ℕ) : HilbertTensorPower 𝕜 E (k + m) ≃ₗᵢ[𝕜]
    HilbertTensor 𝕜 (HilbertTensorPower 𝕜 E k) (HilbertTensorPower 𝕜 E m) :=
  (lieCompletion (mulIsometry k m).symm).trans complTensorIsometry

theorem splitIsometry_ptprod_append {k m : ℕ} (a : Fin k → E) (b : Fin m → E) :
    splitIsometry k m (((ptprod (Fin.append a b) : AlgTensorPower 𝕜 E (k + m))) :
        HilbertTensorPower 𝕜 E (k + m)) =
      htmul ((ptprod a : AlgTensorPower 𝕜 E k) : HilbertTensorPower 𝕜 E k)
        ((ptprod b : AlgTensorPower 𝕜 E m) : HilbertTensorPower 𝕜 E m) := by
  have hsymm : (mulIsometry (𝕜 := 𝕜) (E := E) k m).symm (ptprod (Fin.append a b)) =
      (ptprod a : AlgTensorPower 𝕜 E k) ⊗ₜ[𝕜] (ptprod b : AlgTensorPower 𝕜 E m) := by
    rw [LinearIsometryEquiv.symm_apply_eq]
    exact (mulLinearEquiv_tmul a b).symm
  rw [splitIsometry, LinearIsometryEquiv.trans_apply, lieCompletion_coe, hsymm,
    complTensorIsometry_coe_tmul]

end Split

/-! ## §5 Algebra of completed tensor maps: linearity, composition, adjoint (roadmap R2)

Mathlib's `TensorProduct.adjoint_mapL` needs `CompleteSpace (E ⊗[𝕜] G)`, which fails for
the algebraic tensor product in infinite dimension; here the adjoint identity is proved on the
completion. -/

section HtmapAlgebra

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

theorem htmap_add_left (f₁ f₂ : E →L[𝕜] G) (g : F →L[𝕜] K) :
    htmap (f₁ + f₂) g = htmap f₁ g + htmap f₂ g := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (htmap _ _).continuous (htmap _ _ + htmap _ _).continuous
  | ih a =>
    simp only [htmap, ContinuousLinearMap.add_apply, ContinuousLinearMap.completion_apply_coe,
      TensorProduct.mapL_add_left, UniformSpace.Completion.coe_add]

theorem htmap_smul_left (c : 𝕜) (f : E →L[𝕜] G) (g : F →L[𝕜] K) :
    htmap (c • f) g = c • htmap f g := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (htmap _ _).continuous (c • htmap f g).continuous
  | ih a =>
    simp only [htmap, ContinuousLinearMap.smul_apply, ContinuousLinearMap.completion_apply_coe,
      TensorProduct.mapL_smul_left, UniformSpace.Completion.coe_smul]

theorem htmap_comp {E' F' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
    (f₁ : G →L[𝕜] E') (f₂ : E →L[𝕜] G) (g₁ : K →L[𝕜] F') (g₂ : F →L[𝕜] K) :
    htmap (f₁ ∘L f₂) (g₁ ∘L g₂) = htmap f₁ g₁ ∘L htmap f₂ g₂ := by
  ext z
  induction z using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (htmap _ _).continuous ((htmap f₁ g₁).continuous.comp (htmap f₂ g₂).continuous)
  | ih a =>
    simp only [htmap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.completion_apply_coe,
      TensorProduct.mapL_comp]

/-- **R2.** `(f ⊗̂ g)† = f† ⊗̂ g†` on completed tensor products of Hilbert spaces. -/
theorem adjoint_htmap [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] [CompleteSpace K]
    (f : E →L[𝕜] G) (g : F →L[𝕜] K) :
    ContinuousLinearMap.adjoint (htmap f g) = htmap (ContinuousLinearMap.adjoint f)
      (ContinuousLinearMap.adjoint g) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    exact isClosed_eq (((htmap _ _).continuous.comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((htmap f g).continuous.comp continuous_snd))
  | ih a b =>
    simp only [htmap, ContinuousLinearMap.completion_apply_coe, UniformSpace.Completion.inner_coe]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a₁ a₂ =>
      induction b using TensorProduct.induction_on with
      | zero => simp
      | tmul b₁ b₂ =>
        simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
          ContinuousLinearMap.adjoint_inner_left]
      | add b b' h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | add a a' h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]

end HtmapAlgebra

/-! ## §6 Reduced density of a vector in `X ⊗̂ Y` (roadmap R3, operator part of DEF-030)

For `ψ ∈ X ⊗̂ Y` the partial trace of `|ψ⟩⟨ψ|` over `Y` is the bounded operator `γ_ψ` on `X`
characterised, basis-free, by `⟪γ_ψ φ, φ'⟫ = ⟪ψ, (|φ'⟩⟨φ| ⊗̂ 1) ψ⟫`.  It is constructed here by
the Riesz/Lax–Milgram dualisation of a bounded sesquilinear form (mathlib
`continuousLinearMapOfBilin`), not assumed.  Proved: self-adjointness and positivity, with the
exact identity `⟪γ_ψ φ, φ⟫ = ‖(⟨φ| ⊗̂ 1) ψ‖²`.  The trace-one / trace-norm clauses of DEF-030 need
trace-class infrastructure absent from the pinned mathlib (roadmap R4). -/

section ReducedDensity

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

variable (𝕜 X Y) in
/-- Ampliation `T ↦ T ⊗̂ 1_Y` as a bounded linear map. -/
def ampliate : (X →L[𝕜] X) →L[𝕜] (HilbertTensor 𝕜 X Y →L[𝕜] HilbertTensor 𝕜 X Y) :=
  LinearMap.mkContinuous
    { toFun := fun T => htmap T (ContinuousLinearMap.id 𝕜 Y)
      map_add' := fun S T => htmap_add_left S T _
      map_smul' := fun c T => htmap_smul_left c T _ } 1
    (fun T => by
      refine (norm_htmap_le T _).trans ?_
      have h1 := ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := Y)
      have h2 := norm_nonneg T
      nlinarith)

omit [CompleteSpace X] [CompleteSpace Y] in
theorem ampliate_apply (T : X →L[𝕜] X) :
    ampliate 𝕜 X Y T = htmap T (ContinuousLinearMap.id 𝕜 Y) := rfl

/-- The bounded sesquilinear form `(φ, φ') ↦ ⟪ψ, (|φ'⟩⟨φ| ⊗̂ 1) ψ⟫`. -/
def densityForm (ψ : HilbertTensor 𝕜 X Y) : X →L⋆[𝕜] X →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.compL 𝕜 X (X →L[𝕜] X) 𝕜
      ((innerSL 𝕜 ψ).comp ((ContinuousLinearMap.apply 𝕜 _ ψ).comp (ampliate 𝕜 X Y)))).comp
    (InnerProductSpace.rankOne 𝕜 (E := X) (F := X)).flip

omit [CompleteSpace X] [CompleteSpace Y] in
theorem densityForm_apply (ψ : HilbertTensor 𝕜 X Y) (φ φ' : X) :
    densityForm ψ φ φ' =
      ⟪ψ, htmap (InnerProductSpace.rankOne 𝕜 φ' φ) (ContinuousLinearMap.id 𝕜 Y) ψ⟫_𝕜 := rfl

/-- The reduced density (partial trace over `Y` of `|ψ⟩⟨ψ|`), as a bounded operator on `X`. -/
def reducedDensity (ψ : HilbertTensor 𝕜 X Y) : X →L[𝕜] X :=
  InnerProductSpace.continuousLinearMapOfBilin (densityForm ψ)

omit [CompleteSpace Y] in
theorem inner_reducedDensity_left (ψ : HilbertTensor 𝕜 X Y) (φ φ' : X) :
    ⟪reducedDensity ψ φ, φ'⟫_𝕜 =
      ⟪ψ, htmap (InnerProductSpace.rankOne 𝕜 φ' φ) (ContinuousLinearMap.id 𝕜 Y) ψ⟫_𝕜 := by
  rw [reducedDensity, InnerProductSpace.continuousLinearMapOfBilin_apply, densityForm_apply]

/-- Elementary-tensor check: `γ_{u ⊗ v} = ‖v‖² |u⟩⟨u|`. -/
theorem inner_reducedDensity_htmul (u φ φ' : X) (v : Y) :
    ⟪reducedDensity (htmul u v : HilbertTensor 𝕜 X Y) φ, φ'⟫_𝕜 =
      ⟪φ, u⟫_𝕜 * ⟪u, φ'⟫_𝕜 * ⟪v, v⟫_𝕜 := by
  rw [inner_reducedDensity_left, htmap_htmul, inner_htmul, InnerProductSpace.rankOne_apply,
    inner_smul_right, ContinuousLinearMap.id_apply]

theorem reducedDensity_isSelfAdjoint (ψ : HilbertTensor 𝕜 X Y) :
    IsSelfAdjoint (reducedDensity ψ) := by
  have h : reducedDensity ψ = ContinuousLinearMap.adjoint (reducedDensity ψ) := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro φ φ'
    rw [inner_reducedDensity_left, ← inner_conj_symm φ, inner_reducedDensity_left,
      inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right, adjoint_htmap,
      InnerProductSpace.adjoint_rankOne, ContinuousLinearMap.adjoint_id]
  exact h.symm

/-- `⟪γ_ψ φ, φ⟫ = ‖(⟨φ| ⊗̂ 1) ψ‖²`, where `⟨φ| = rankOne 1 φ : X →L 𝕜`. -/
theorem inner_reducedDensity_self (ψ : HilbertTensor 𝕜 X Y) (φ : X) :
    ⟪reducedDensity ψ φ, φ⟫_𝕜 =
      (‖htmap (InnerProductSpace.rankOne 𝕜 (1 : 𝕜) φ) (ContinuousLinearMap.id 𝕜 Y) ψ‖ ^ 2 : ℝ) := by
  set A : X →L[𝕜] 𝕜 := InnerProductSpace.rankOne 𝕜 (1 : 𝕜) φ
  have hR : InnerProductSpace.rankOne 𝕜 φ φ = ContinuousLinearMap.adjoint A ∘L A := by
    simp only [A, InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_comp_rankOne]
    simp
  have hid : ContinuousLinearMap.id 𝕜 Y =
      ContinuousLinearMap.adjoint (ContinuousLinearMap.id 𝕜 Y) ∘L ContinuousLinearMap.id 𝕜 Y := by
    rw [ContinuousLinearMap.adjoint_id]; rfl
  rw [inner_reducedDensity_left, hR, hid, htmap_comp, ← adjoint_htmap,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  push_cast
  rw [← hid]

/-- **R3.** The reduced density is a positive operator. -/
theorem reducedDensity_isPositive (ψ : HilbertTensor 𝕜 X Y) :
    (reducedDensity ψ).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  refine ⟨reducedDensity_isSelfAdjoint ψ, fun φ => ?_⟩
  show 0 ≤ RCLike.re ⟪reducedDensity ψ φ, φ⟫_𝕜
  rw [inner_reducedDensity_self, RCLike.ofReal_re]
  positivity

end ReducedDensity

/-! ## §7 DEF-030 operator: reduced density over the last `m` factors of `E^{⊗̂(k+m)}` -/

section PowerReducedDensity

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `γ^{(k)}_ψ` for `ψ ∈ E^{⊗̂(k+m)}`: the partial trace of `|ψ⟩⟨ψ|` over the last `m` factors
(placement fixed by `splitIsometry`), as a bounded operator on `E^{⊗̂k}`.  Trace-one is NOT
asserted here (needs trace-class infrastructure, roadmap R4). -/
def reducedDensityPower (k m : ℕ) (ψ : HilbertTensorPower 𝕜 E (k + m)) :
    HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k :=
  reducedDensity (splitIsometry k m ψ)

theorem reducedDensityPower_isPositive (k m : ℕ) (ψ : HilbertTensorPower 𝕜 E (k + m)) :
    (reducedDensityPower k m ψ).IsPositive :=
  reducedDensity_isPositive _

end PowerReducedDensity

end QuantumNLS.TensorCarrier

/-! ## Axiom audit (kept in-file; output must list only propext, Classical.choice, Quot.sound) -/
#print axioms QuantumNLS.TensorCarrier.groupAverage_eq_starProjection
#print axioms QuantumNLS.TensorCarrier.span_htmul_dense
#print axioms QuantumNLS.TensorCarrier.norm_htmap_le
#print axioms QuantumNLS.TensorCarrier.htcommIsometry_htcommIsometry
#print axioms QuantumNLS.TensorCarrier.inner_ptprod
#print axioms QuantumNLS.TensorCarrier.norm_ptprod
#print axioms QuantumNLS.TensorCarrier.inner_permLinearEquiv
#print axioms QuantumNLS.TensorCarrier.permRep
#print axioms QuantumNLS.TensorCarrier.symProj_eq_factorial_average
#print axioms QuantumNLS.TensorCarrier.symProj_eq_starProjection
#print axioms QuantumNLS.TensorCarrier.htpow_mem_symSector
#print axioms QuantumNLS.TensorCarrier.norm_htpow
#print axioms QuantumNLS.TensorCarrier.splitIsometry
#print axioms QuantumNLS.TensorCarrier.splitIsometry_ptprod_append
#print axioms QuantumNLS.TensorCarrier.adjoint_htmap
#print axioms QuantumNLS.TensorCarrier.inner_reducedDensity_htmul
#print axioms QuantumNLS.TensorCarrier.reducedDensity_isSelfAdjoint
#print axioms QuantumNLS.TensorCarrier.reducedDensity_isPositive
#print axioms QuantumNLS.TensorCarrier.reducedDensityPower_isPositive
