import QuantumNLS.RealAnalyticDef

/-!
# DEF-017 (`def:report-17`), complexification clause: genuine complexification and the converse

Source: `source/chapters/definitions.tex`, lines 103-105 (sha256 `abe7643b…`):

> A Hilbert-space map is real analytic if, near each input, it has a norm-convergent series of
> continuous real homogeneous polynomials, or equivalently a local holomorphic extension after
> complexification. […]

The frozen `QuantumNLS.RealAnalyticDef` (sha256 `c13c7dd2…`, imported read-only) realizes the
polynomial-series clause (`IsRealAnalyticPoly`), the bridge to `AnalyticAt ℝ`, the extension
predicate `HasLocalHolomorphicExtension ι ιF f x` for arbitrary complexification data, and the
direction "extension ⇒ real analytic". Terra round 57 (C1) held DEF-017 because (a) the converse
was not proved and (b) the datum was not required to be a genuine complexification. This module
closes both points for real Hilbert spaces.

## 1. Genuine complexification `Cpx E` of a real inner product space `E`
* Carrier `Cpx E = {(a, b) : a b : E}` (`a + i b`), with the complex structure
  `(x + i y) • (a, b) = (x a - y b, x b + y a)`, so `i • (a, b) = (-b, a)` (`I_smul`).
* Hermitian inner product `⟪(a,b),(c,d)⟫ = ⟪a,c⟫ + ⟪b,d⟫ + i (⟪a,d⟫ - ⟪b,c⟫)` (`cinner`,
  `inner_eq`), conjugate-linear in the first slot (Mathlib convention). It is an
  `InnerProductSpace ℂ (Cpx E)` and, when `E` is complete, `CompleteSpace (Cpx E)`: a complex
  Hilbert space. Norm: `‖(a,b)‖² = ‖a‖² + ‖b‖²` (`norm_sq_eq`).
* Real embedding `ofRealCLM : E →L[ℝ] Cpx E`, `a ↦ (a, 0)`: real-linear, isometric
  (`norm_ofRealCLM`, `isometry_ofRealCLM`), with `⟪ι a, ι b⟫_ℂ = ⟪a, b⟫_ℝ` (`inner_ofRealCLM`).
* Real and imaginary parts `reCLM`, `imCLM : Cpx E →L[ℝ] E` with `reCLM ∘ ι = id` (`reCLM_ofRealCLM`)
  and `imCLM ∘ ι = 0`.
* Genuineness (`Cpx E = ι E ⊕ i·ι E` as real spaces): every `v = ι (re v) + i • ι (im v)`
  (`eq_ofReal_add_I_smul`), and `ι a + i • ι b = 0 ↔ a = 0 ∧ b = 0` (`ofReal_add_I_smul_eq_zero`).
  Equivalently `ι E ∩ i • ι E = 0` and `ι E + i • ι E = Cpx E`.
* Conjugation `conjCLM (a,b) = (a,-b)`: real-linear isometric involution, conjugate-linear for the
  complex structure (`conjCLM_smul`), whose fixed points are exactly `range ι`
  (`conjCLM_eq_self_iff`); `ι (re v) = 2⁻¹ • (v + conj v)` (`ofReal_re_eq`).
* Any two complex-linear maps out of `Cpx E` that agree on `ι E` are equal (`linearMap_ext_ofReal`).
* Bundled: `isGenuineComplexification` (isometric `ι`, `Re ∘ ι = id`, unique decomposition
  `v = ι a + i • ι b`, inner product restricts). The real structure on `Cpx E` used by the
  real-linear maps is the restriction of the complex scalars (Mathlib's `Module.complexToReal`),
  acting componentwise (`real_smul_re`, `real_smul_im`).

## 2. Complexification of continuous multilinear maps
For `A : E [×n]→L[ℝ] G` with `G` a complex normed space,
`cpxML A (v) = ∑_{S ⊆ Fin n} i^{|S|} • A (sel S v)` where `sel S v j = im (v j)` for `j ∈ S` and
`re (v j)` otherwise. `cpxML A : Cpx E [×n]→L[ℂ] G` is complex multilinear (the `i`-homogeneity is
the involution `S ↦ S ∆ {k}`, `realCpx_update_I`), extends `A` on real points
(`cpxML_ofReal : cpxML A (ι ∘ m) = A m`), and `‖cpxML A‖ ≤ 2ⁿ ‖A‖` (`norm_cpxML_le`).

## 3. The converse and the DEF-017 equivalence
* `cpxSeries p n = cpxML (ιF ∘ p n)`, `‖cpxSeries p n‖ ≤ 2ⁿ ‖p n‖`, so
  `p.radius > 0 ⇒ (cpxSeries p).radius > 0` (radius at least half).
* `exists_holomorphic_extension_of_analyticAt`: `AnalyticAt ℝ f x` (real inner product spaces,
  `F` complete) gives `g : Cpx E → Cpx F`, `g z = ∑ₙ cpxSeries p n (z - ι x, …)`, with
  `AnalyticAt ℂ g (ι x)` and `g (ι y) = ιF (f y)` for `y` near `x`.
* `analyticAt_iff_hasLocalHolomorphicExtension` (`F` complete) and
  **`isRealAnalyticPoly_iff_hasLocalHolomorphicExtension`** (`E`, `F` real Hilbert spaces):
  `IsRealAnalyticPoly f x ↔ HasLocalHolomorphicExtension ofRealCLM ofRealCLM f x`, i.e. the
  frozen predicate instantiated at the genuine complexifications constructed here. Map level:
  `isRealAnalyticMap_iff_hasLocalHolomorphicExtension`.

## Qualifications
* C2 (unchanged): "holomorphic" is read as `AnalyticAt ℂ` (locally a norm-convergent series of
  continuous complex homogeneous polynomials, the standard definition on complex Banach spaces).
  Its equivalence with complex Fréchet differentiability on an open set is not in Mathlib at the
  pin for Banach domains and is not proved here.
* Scope: real inner product (Hilbert) spaces, as in the source ("A Hilbert-space map"). The
  complexification of a general real Banach space (needing e.g. the Taylor norm) is not built.
* The extension direction asks `F` complete (the complex series must converge in `Cpx F`); this
  holds for Hilbert spaces.

No `sorry`, `admit`, new axioms or `native_decide`.
-/

set_option autoImplicit false

namespace QuantumNLS.RealAnalyticComplexify

open Complex (I I_sq)
open Filter Topology

/-! ### The carrier and its complex vector-space structure -/

/-- The complexification `E_ℂ = E × E` of a real vector space `E`; `⟨a, b⟩` stands for
`a + i b`. -/
@[ext] structure Cpx (E : Type*) where
  /-- Real part. -/
  re : E
  /-- Imaginary part. -/
  im : E

namespace Cpx

variable {E : Type*}

/-- The underlying pair. -/
def equivProd (E : Type*) : Cpx E ≃ E × E where
  toFun v := (v.re, v.im)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Algebra

variable [AddCommGroup E]

instance : AddCommGroup (Cpx E) := (equivProd E).addCommGroup

@[simp] lemma add_re (v w : Cpx E) : (v + w).re = v.re + w.re := rfl
@[simp] lemma add_im (v w : Cpx E) : (v + w).im = v.im + w.im := rfl
@[simp] lemma neg_re (v : Cpx E) : (-v).re = -v.re := rfl
@[simp] lemma neg_im (v : Cpx E) : (-v).im = -v.im := rfl
@[simp] lemma sub_re (v w : Cpx E) : (v - w).re = v.re - w.re := rfl
@[simp] lemma sub_im (v w : Cpx E) : (v - w).im = v.im - w.im := rfl
@[simp] lemma zero_re : (0 : Cpx E).re = 0 := rfl
@[simp] lemma zero_im : (0 : Cpx E).im = 0 := rfl

variable [Module ℝ E]

/-- Complex structure: `(x + i y) • (a, b) = (x a - y b, x b + y a)`. -/
instance : SMul ℂ (Cpx E) :=
  ⟨fun c v => ⟨c.re • v.re - c.im • v.im, c.re • v.im + c.im • v.re⟩⟩

@[simp] lemma smul_re (c : ℂ) (v : Cpx E) : (c • v).re = c.re • v.re - c.im • v.im := rfl
@[simp] lemma smul_im (c : ℂ) (v : Cpx E) : (c • v).im = c.re • v.im + c.im • v.re := rfl

instance : Module ℂ (Cpx E) where
  one_smul v := by ext <;> simp
  mul_smul c d v := by ext <;> simp <;> module
  smul_zero c := by ext <;> simp
  smul_add c v w := by ext <;> simp <;> module
  add_smul c d v := by ext <;> simp <;> module
  zero_smul v := by ext <;> simp

/-- The real structure induced by the complex one acts componentwise. -/
@[simp] lemma real_smul_re (r : ℝ) (v : Cpx E) : (r • v).re = r • v.re := by
  have : r • v = (r : ℂ) • v := rfl
  rw [this, smul_re]; simp
@[simp] lemma real_smul_im (r : ℝ) (v : Cpx E) : (r • v).im = r • v.im := by
  have : r • v = (r : ℂ) • v := rfl
  rw [this, smul_im]; simp

/-- `i • (a, b) = (-b, a)`. -/
lemma I_smul (v : Cpx E) : I • v = ⟨-v.im, v.re⟩ := by
  ext <;> simp

lemma smul_decomp (c : ℂ) (x : Cpx E) : c • x = c.re • x + c.im • (I • x) := by
  ext
  · simp [sub_eq_add_neg]
  · simp

end Algebra

/-! ### Hilbert structure -/

section Inner

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open scoped InnerProductSpace RealInnerProductSpace

/-- `⟪(a,b),(c,d)⟫ = ⟪a,c⟫ + ⟪b,d⟫ + i (⟪a,d⟫ - ⟪b,c⟫)`. -/
def cinner (v w : Cpx E) : ℂ :=
  ⟨⟪v.re, w.re⟫ + ⟪v.im, w.im⟫, ⟪v.re, w.im⟫ - ⟪v.im, w.re⟫⟩

instance innerCore : InnerProductSpace.Core ℂ (Cpx E) where
  inner := cinner
  conj_inner_symm v w := by
    apply Complex.ext <;> simp [cinner, real_inner_comm]
  re_inner_nonneg v := by
    simp only [cinner]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left u v w := by
    apply Complex.ext <;> simp [cinner, inner_add_left] <;> ring
  smul_left v w c := by
    apply Complex.ext <;>
      simp [cinner, inner_add_left, inner_sub_left, real_inner_smul_left] <;> ring
  definite v h := by
    have h1 : ⟪v.re, v.re⟫ + ⟪v.im, v.im⟫ = 0 := congrArg Complex.re h
    have h2 := real_inner_self_nonneg (x := v.re)
    have h3 := real_inner_self_nonneg (x := v.im)
    ext
    · exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)
    · exact (inner_self_eq_zero (𝕜 := ℝ)).1 (by linarith)

noncomputable instance : NormedAddCommGroup (Cpx E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

/-- `Cpx E` is a complex inner product space. -/
noncomputable instance : InnerProductSpace ℂ (Cpx E) :=
  InnerProductSpace.ofCore (innerCore (E := E)).toCore

lemma inner_eq (v w : Cpx E) : inner ℂ v w = cinner v w := rfl

lemma norm_sq_eq (v : Cpx E) : ‖v‖ ^ 2 = ‖v.re‖ ^ 2 + ‖v.im‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ, inner_eq]
  simp [cinner]

lemma norm_re_le (v : Cpx E) : ‖v.re‖ ≤ ‖v‖ := by
  nlinarith [norm_sq_eq v, norm_nonneg v.re, norm_nonneg v, sq_nonneg ‖v.im‖]

lemma norm_im_le (v : Cpx E) : ‖v.im‖ ≤ ‖v‖ := by
  nlinarith [norm_sq_eq v, norm_nonneg v.im, norm_nonneg v, sq_nonneg ‖v.re‖]

/-- The real part, real-linear. -/
def reLM : Cpx E →ₗ[ℝ] E where
  toFun := Cpx.re
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

/-- The imaginary part, real-linear. -/
def imLM : Cpx E →ₗ[ℝ] E where
  toFun := Cpx.im
  map_add' _ _ := rfl
  map_smul' _ _ := by simp

/-- The real part `Re : E_ℂ → E` as a continuous real-linear map. -/
noncomputable def reCLM : Cpx E →L[ℝ] E :=
  reLM.mkContinuous 1 (fun v => by rw [one_mul]; exact norm_re_le v)

/-- The imaginary part `Im : E_ℂ → E` as a continuous real-linear map. -/
noncomputable def imCLM : Cpx E →L[ℝ] E :=
  imLM.mkContinuous 1 (fun v => by rw [one_mul]; exact norm_im_le v)

@[simp] lemma reCLM_apply (v : Cpx E) : reCLM v = v.re := rfl
@[simp] lemma imCLM_apply (v : Cpx E) : imCLM v = v.im := rfl

lemma norm_mk_zero (a : E) : ‖(⟨a, 0⟩ : Cpx E)‖ = ‖a‖ := by
  have := norm_sq_eq (⟨a, 0⟩ : Cpx E)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero] at this
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- The real embedding `a ↦ (a, 0)`, real-linear. -/
def ofRealLM : E →ₗ[ℝ] Cpx E where
  toFun a := ⟨a, 0⟩
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp

/-- The real embedding `ι : E → E_ℂ`, `ι a = (a, 0)`, as a continuous real-linear map. -/
noncomputable def ofRealCLM : E →L[ℝ] Cpx E :=
  ofRealLM.mkContinuous 1 (fun a => by simp [ofRealLM, norm_mk_zero])

@[simp] lemma ofRealCLM_re (a : E) : (ofRealCLM a : Cpx E).re = a := rfl
@[simp] lemma ofRealCLM_im (a : E) : (ofRealCLM a : Cpx E).im = 0 := rfl

/-- `Re ∘ ι = id`. -/
lemma reCLM_ofRealCLM (a : E) : reCLM (ofRealCLM a : Cpx E) = a := rfl

/-- `Im ∘ ι = 0`. -/
lemma imCLM_ofRealCLM (a : E) : imCLM (ofRealCLM a : Cpx E) = 0 := rfl

/-- `ι` is norm preserving. -/
lemma norm_ofRealCLM (a : E) : ‖(ofRealCLM a : Cpx E)‖ = ‖a‖ := norm_mk_zero a

/-- `ι` is an isometric embedding. -/
lemma isometry_ofRealCLM : Isometry (ofRealCLM : E → Cpx E) :=
  AddMonoidHomClass.isometry_of_norm ofRealCLM norm_ofRealCLM

lemma injective_ofRealCLM : Function.Injective (ofRealCLM : E → Cpx E) :=
  isometry_ofRealCLM.injective

/-- The complex inner product restricts to the real one on `ι E`. -/
lemma inner_ofRealCLM (a b : E) :
    inner ℂ (ofRealCLM a : Cpx E) (ofRealCLM b) = ((inner ℝ a b : ℝ) : ℂ) := by
  rw [inner_eq]
  apply Complex.ext <;> simp [cinner]

/-- Every vector is `ι (Re v) + i • ι (Im v)`. -/
lemma eq_ofReal_add_I_smul (v : Cpx E) :
    v = ofRealCLM v.re + I • ofRealCLM v.im := by
  ext <;> simp

/-- Uniqueness of the decomposition: `ι E ∩ i • ι E = 0`. -/
lemma ofReal_add_I_smul_eq_zero (a b : E) :
    (ofRealCLM a : Cpx E) + I • ofRealCLM b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have h1 := congrArg Cpx.re h
    have h2 := congrArg Cpx.im h
    simp at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    ext <;> simp

/-- Complex-linear maps out of `E_ℂ` are determined by their values on `ι E`. -/
lemma linearMap_ext_ofReal {G : Type*} [AddCommGroup G] [Module ℂ G] {L L' : Cpx E →ₗ[ℂ] G}
    (h : ∀ a, L (ofRealCLM a) = L' (ofRealCLM a)) : L = L' := by
  ext v
  rw [eq_ofReal_add_I_smul v, map_add, map_add, map_smul, map_smul, h, h]

/-- Conjugation `(a, b) ↦ (a, -b)`, real-linear. -/
def conjLM : Cpx E →ₗ[ℝ] Cpx E where
  toFun v := ⟨v.re, -v.im⟩
  map_add' _ _ := by ext <;> simp [add_comm]
  map_smul' _ _ := by ext <;> simp

lemma norm_conj (v : Cpx E) : ‖(⟨v.re, -v.im⟩ : Cpx E)‖ = ‖v‖ := by
  have h1 := norm_sq_eq (⟨v.re, -v.im⟩ : Cpx E)
  have h2 := norm_sq_eq v
  simp only [norm_neg] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.trans h2.symm)

/-- Conjugation as a continuous real-linear map. -/
noncomputable def conjCLM : Cpx E →L[ℝ] Cpx E :=
  conjLM.mkContinuous 1 (fun v => by simp [conjLM, norm_conj])

@[simp] lemma conjCLM_re (v : Cpx E) : (conjCLM v).re = v.re := rfl
@[simp] lemma conjCLM_im (v : Cpx E) : (conjCLM v).im = -v.im := rfl

lemma norm_conjCLM (v : Cpx E) : ‖conjCLM v‖ = ‖v‖ := norm_conj v

lemma conjCLM_conjCLM (v : Cpx E) : conjCLM (conjCLM v) = v := by
  ext <;> simp

/-- Conjugation is conjugate-linear for the complex structure. -/
lemma conjCLM_smul (c : ℂ) (v : Cpx E) : conjCLM (c • v) = (starRingEnd ℂ c) • conjCLM v := by
  ext <;> simp
  abel

/-- The fixed points of conjugation are exactly the real vectors `ι E`. -/
lemma conjCLM_eq_self_iff (v : Cpx E) : conjCLM v = v ↔ ∃ a, v = ofRealCLM a := by
  constructor
  · intro h
    refine ⟨v.re, ?_⟩
    have h2 : -v.im = v.im := congrArg Cpx.im h
    have : v.im = 0 := by
      have : (2 : ℝ) • v.im = 0 := by rw [two_smul]; nth_rw 1 [← h2]; exact neg_add_cancel _
      exact (smul_eq_zero.1 this).resolve_left two_ne_zero
    ext <;> simp [this]
  · rintro ⟨a, rfl⟩
    ext <;> simp

/-- `ι (Re v) = 2⁻¹ • (v + conj v)`. -/
lemma ofReal_re_eq (v : Cpx E) : (ofRealCLM v.re : Cpx E) = (2⁻¹ : ℂ) • (v + conjCLM v) := by
  ext
  · simp only [ofRealCLM_re, smul_re, add_re, conjCLM_re, add_im, conjCLM_im]
    norm_num
    rw [← add_smul]; norm_num
  · simp

/-- The complexification of a real Hilbert space is a complex Hilbert space. -/
instance [CompleteSpace E] : CompleteSpace (Cpx E) := by
  let φ : Cpx E →+ WithLp 2 (E × E) :=
    AddMonoidHom.mk' (fun v => WithLp.toLp 2 (v.re, v.im)) (fun _ _ => rfl)
  have hφ : Isometry φ := AddMonoidHomClass.isometry_of_norm φ (fun v => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2, norm_sq_eq]
    rfl)
  rw [completeSpace_iff_isComplete_range hφ.isUniformInducing]
  have : Set.range φ = Set.univ :=
    Set.eq_univ_of_forall fun w => ⟨⟨(WithLp.ofLp w).1, (WithLp.ofLp w).2⟩, rfl⟩
  rw [this]; exact isComplete_univ

/-- `(Cpx E, ι)` is a genuine complexification of `E`: `ι` is an isometric real-linear embedding
with `Re ∘ ι = id`, every vector is uniquely `ι a + i • ι b`, and the complex inner product
restricts to the real one on `ι E`. -/
theorem isGenuineComplexification :
    Isometry (ofRealCLM : E → Cpx E) ∧ (∀ a : E, reCLM (ofRealCLM a : Cpx E) = a) ∧
      (∀ v : Cpx E, ∃! p : E × E, v = ofRealCLM p.1 + I • ofRealCLM p.2) ∧
      ∀ a b : E, inner ℂ (ofRealCLM a : Cpx E) (ofRealCLM b) = ((inner ℝ a b : ℝ) : ℂ) := by
  refine ⟨isometry_ofRealCLM, reCLM_ofRealCLM, fun v => ⟨(v.re, v.im), eq_ofReal_add_I_smul v,
    ?_⟩, inner_ofRealCLM⟩
  rintro ⟨a, b⟩ h
  have h1 := congrArg Cpx.re h
  have h2 := congrArg Cpx.im h
  simp at h1 h2
  exact Prod.ext h1.symm h2.symm

end Inner

/-! ### Complexification of continuous real multilinear maps -/

section Multi

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
open Finset

/-- Selection of real/imaginary parts: `sel S v j = Im (v j)` for `j ∈ S`, else `Re (v j)`. -/
def sel {n : ℕ} (S : Finset (Fin n)) (v : Fin n → Cpx E) : Fin n → E :=
  fun j => if j ∈ S then (v j).im else (v j).re

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma sel_empty {n : ℕ} (v : Fin n → Cpx E) : sel ∅ v = fun j => (v j).re := by
  funext j; simp [sel]

/-- One term of the complexification, a real multilinear map on `E_ℂ`. -/
noncomputable def cpxTerm {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G)
    (S : Finset (Fin n)) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Cpx E) G :=
  A.compContinuousLinearMap (fun j => if j ∈ S then imCLM else reCLM)

lemma cpxTerm_apply {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G)
    (S : Finset (Fin n)) (v : Fin n → Cpx E) : cpxTerm A S v = A (sel S v) := by
  simp only [cpxTerm, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1; funext j; by_cases h : j ∈ S <;> simp [sel, h]

/-- The complexification as a real multilinear map: `∑_S i^{|S|} • A (sel S v)`. -/
noncomputable def realCpx {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Cpx E) G :=
  ∑ S : Finset (Fin n), (I ^ S.card) • cpxTerm A S

lemma realCpx_apply {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G)
    (v : Fin n → Cpx E) : realCpx A v = ∑ S : Finset (Fin n), (I ^ S.card) • A (sel S v) := by
  simp [realCpx, cpxTerm_apply]

/-- `i`-homogeneity in each slot, via the involution `S ↦ S ∆ {k}`. -/
lemma realCpx_update_I {n : ℕ} [DecidableEq (Fin n)]
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) (v : Fin n → Cpx E) (k : Fin n) :
    realCpx A (Function.update v k (I • v k)) = I • realCpx A v := by
  rw [realCpx_apply, realCpx_apply, Finset.smul_sum]
  refine Fintype.sum_bijective (fun S => symmDiff S {k})
    (Function.Involutive.bijective fun S => symmDiff_symmDiff_cancel_right {k} S) _ _
    (fun S => ?_)
  by_cases hk : k ∈ S
  · have h1 : symmDiff S {k} = S.erase k := by
      ext j; by_cases hj : j = k <;> simp [Finset.mem_symmDiff, hj, hk]
    have h2 : sel S (Function.update v k (I • v k)) = sel (S.erase k) v := by
      funext j; by_cases hj : j = k
      · subst hj; simp [sel, hk]
      · simp [sel, hj]
    simp only [h1, h2, smul_smul]
    rw [← pow_succ', Finset.card_erase_add_one hk]
  · have h1 : symmDiff S {k} = insert k S := by
      ext j; by_cases hj : j = k <;> simp [Finset.mem_symmDiff, hj, hk]
    have h2 : sel S (Function.update v k (I • v k)) =
        Function.update (sel (insert k S) v) k ((-1 : ℝ) • sel (insert k S) v k) := by
      funext j; by_cases hj : j = k
      · subst hj; simp [sel, hk]
      · simp [sel, hj]
    simp only [h1, h2]
    rw [A.map_update_smul, Function.update_eq_self, Finset.card_insert_of_notMem hk, neg_one_smul,
      smul_neg, ← neg_smul, smul_smul]
    congr 1
    rw [pow_succ]; linear_combination (-(I ^ S.card)) * I_sq

lemma realCpx_update_smul {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G)
    [DecidableEq (Fin n)] (v : Fin n → Cpx E) (k : Fin n) (c : ℂ) (x : Cpx E) :
    realCpx A (Function.update v k (c • x)) = c • realCpx A (Function.update v k x) := by
  have hI : realCpx A (Function.update v k (I • x)) = I • realCpx A (Function.update v k x) := by
    have := realCpx_update_I A (Function.update v k x) k
    rwa [Function.update_self, Function.update_idem] at this
  rw [smul_decomp, (realCpx A).map_update_add, (realCpx A).map_update_smul,
    (realCpx A).map_update_smul, hI, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul,
    ← add_smul, Complex.re_add_im]

/-- **Complexification of a continuous real multilinear map** `A : Eⁿ → G` (`G` complex):
the complex multilinear map `A_ℂ (v) = ∑_{S ⊆ Fin n} i^{|S|} • A (sel S v)` on `E_ℂⁿ`. -/
noncomputable def cpxML {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Cpx E) G where
  toFun := realCpx A
  map_update_add' v k x y := (realCpx A).map_update_add v k x y
  map_update_smul' v k c x := realCpx_update_smul A v k c x
  cont := (realCpx A).cont

lemma cpxML_apply {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G)
    (v : Fin n → Cpx E) : cpxML A v = ∑ S : Finset (Fin n), (I ^ S.card) • A (sel S v) :=
  realCpx_apply A v

/-- Norm bound `‖A_ℂ‖ ≤ 2ⁿ ‖A‖`. -/
lemma norm_cpxML_le {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G) :
    ‖cpxML A‖ ≤ 2 ^ n * ‖A‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  calc ‖cpxML A v‖ = ‖∑ S : Finset (Fin n), (I ^ S.card) • A (sel S v)‖ := by rw [cpxML_apply]
    _ ≤ ∑ S : Finset (Fin n), ‖(I ^ S.card) • A (sel S v)‖ := norm_sum_le _ _
    _ ≤ ∑ _S : Finset (Fin n), ‖A‖ * ∏ j, ‖v j‖ := Finset.sum_le_sum fun S _ => by
        rw [norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul]
        refine (A.le_opNorm _).trans ?_
        gcongr with j
        simp only [sel]; split_ifs
        exacts [norm_im_le _, norm_re_le _]
    _ = 2 ^ n * ‖A‖ * ∏ j, ‖v j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast; ring

/-- `A_ℂ` extends `A`: on real points `A_ℂ (ι m₁, …, ι mₙ) = A (m₁, …, mₙ)`. -/
lemma cpxML_ofReal {n : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) G)
    (m : Fin n → E) : cpxML A (fun j => ofRealCLM (m j)) = A m := by
  rw [cpxML_apply, Finset.sum_eq_single ∅]
  · simp [sel_empty]
  · intro S _ hS
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hS
    rw [A.map_coord_zero j (by simp [sel, hj]), smul_zero]
  · simp

end Multi

end Cpx

/-! ### Real analytic ⇒ local holomorphic extension; the DEF-017 equivalence -/

section Extension

open Cpx RealAnalyticDef

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The complexified power series: `(cpxSeries p) n = (ιF ∘ p n)_ℂ`. -/
noncomputable def cpxSeries (p : FormalMultilinearSeries ℝ E F) :
    FormalMultilinearSeries ℂ (Cpx E) (Cpx F) :=
  fun n => cpxML ((ofRealCLM : F →L[ℝ] Cpx F).compContinuousMultilinearMap (p n))

lemma norm_ofRealCLM_le : ‖(ofRealCLM : F →L[ℝ] Cpx F)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma norm_cpxSeries_le (p : FormalMultilinearSeries ℝ E F) (n : ℕ) :
    ‖cpxSeries p n‖ ≤ 2 ^ n * ‖p n‖ := by
  refine (norm_cpxML_le _).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  calc ‖(ofRealCLM : F →L[ℝ] Cpx F)‖ * ‖p n‖ ≤ 1 * ‖p n‖ :=
        mul_le_mul_of_nonneg_right norm_ofRealCLM_le (norm_nonneg _)
    _ = ‖p n‖ := one_mul _

/-- The complexified series has positive radius (at least half the real one). -/
lemma cpxSeries_radius_pos (p : FormalMultilinearSeries ℝ E F) (hp : 0 < p.radius) :
    0 < (cpxSeries p).radius := by
  obtain ⟨ρ, hρ0, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp
  obtain ⟨C, -, hCb⟩ := p.norm_mul_pow_le_of_lt_radius hρ
  have hρpos : (0 : ℝ) < ρ := by exact_mod_cast ENNReal.coe_pos.1 hρ0
  refine lt_of_lt_of_le ?_ ((cpxSeries p).le_radius_of_bound C (r := ρ / 2) fun n => ?_)
  · have : (0 : NNReal) < ρ / 2 := by
      have : (0 : NNReal) < ρ := by exact_mod_cast hρpos
      positivity
    exact_mod_cast this
  · calc ‖cpxSeries p n‖ * (((ρ / 2 : NNReal)) : ℝ) ^ n
        ≤ (2 ^ n * ‖p n‖) * ((ρ : ℝ) / 2) ^ n := by
          push_cast
          exact mul_le_mul_of_nonneg_right (norm_cpxSeries_le p n) (by positivity)
      _ = ‖p n‖ * (ρ : ℝ) ^ n := by
          rw [div_pow]; field_simp
      _ ≤ C := hCb n

/-- **DEF-017 complexification clause, converse (C1).** A real analytic map between real inner
product spaces (codomain complete) has a local holomorphic extension through the genuine
complexifications: there is `g : E_ℂ → F_ℂ`, complex analytic at `ι x`, with
`g (ι y) = ιF (f y)` for all `y` near `x`. -/
theorem exists_holomorphic_extension_of_analyticAt [CompleteSpace F] {f : E → F} {x : E}
    (hf : AnalyticAt ℝ f x) :
    ∃ g : Cpx E → Cpx F, AnalyticAt ℂ g (ofRealCLM x) ∧
      ∀ᶠ y in 𝓝 x, g (ofRealCLM y) = ofRealCLM (f y) := by
  obtain ⟨p, r, hp⟩ := hf
  set q := cpxSeries p with hq_def
  have hq : 0 < q.radius := cpxSeries_radius_pos p (lt_of_lt_of_le hp.r_pos hp.r_le)
  refine ⟨fun z => q.sum (z - ofRealCLM x), ?_, ?_⟩
  · have h0 : AnalyticAt ℂ q.sum 0 := (q.hasFPowerSeriesOnBall hq).analyticAt
    have hsub : AnalyticAt ℂ (fun z : Cpx E => z - ofRealCLM x) (ofRealCLM x) :=
      analyticAt_id.sub analyticAt_const
    exact h0.comp_of_eq hsub (sub_self _)
  · have hev := hp.hasFPowerSeriesAt.eventually_hasSum
    have ht : Tendsto (fun y : E => y - x) (𝓝 x) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [ht.eventually hev] with y hy
    rw [add_sub_cancel] at hy
    have hs := hy.mapL (ofRealCLM : F →L[ℝ] Cpx F)
    simp only [FormalMultilinearSeries.sum]
    rw [← hs.tsum_eq]
    congr 1; funext n
    rw [← map_sub, hq_def, cpxSeries]
    exact cpxML_ofReal _ (fun _ => y - x)

/-- The converse, stated with the frozen predicate `HasLocalHolomorphicExtension` at the
constructed complexification data `(Cpx E, ofRealCLM)`, `(Cpx F, ofRealCLM)`. -/
theorem hasLocalHolomorphicExtension_of_analyticAt [CompleteSpace F] {f : E → F} {x : E}
    (hf : AnalyticAt ℝ f x) :
    HasLocalHolomorphicExtension (ofRealCLM : E →L[ℝ] Cpx E) (ofRealCLM : F →L[ℝ] Cpx F) f x :=
  exists_holomorphic_extension_of_analyticAt hf

/-- `AnalyticAt ℝ f x ↔` local holomorphic extension through the genuine complexifications. -/
theorem analyticAt_iff_hasLocalHolomorphicExtension [CompleteSpace F] (f : E → F) (x : E) :
    AnalyticAt ℝ f x ↔
      HasLocalHolomorphicExtension (ofRealCLM : E →L[ℝ] Cpx E) (ofRealCLM : F →L[ℝ] Cpx F) f x :=
  ⟨hasLocalHolomorphicExtension_of_analyticAt,
    analyticAt_of_hasLocalHolomorphicExtension ofRealCLM ofRealCLM reCLM reCLM_ofRealCLM⟩

/-- **DEF-017, "or equivalently", for real Hilbert spaces.** The literal polynomial-series
predicate holds at `x` iff `f` has a local holomorphic extension after (genuine)
complexification. -/
theorem isRealAnalyticPoly_iff_hasLocalHolomorphicExtension [CompleteSpace E] [CompleteSpace F]
    (f : E → F) (x : E) :
    IsRealAnalyticPoly f x ↔
      HasLocalHolomorphicExtension (ofRealCLM : E →L[ℝ] Cpx E) (ofRealCLM : F →L[ℝ] Cpx F) f x :=
  (analyticAt_iff_isRealAnalyticPoly f x).symm.trans
    (analyticAt_iff_hasLocalHolomorphicExtension f x)

/-- The same, unfolded: real analytic at `x` iff there is `g : E_ℂ → F_ℂ`, complex analytic at
`ι x`, with `g ∘ ι = ιF ∘ f` near `x`. -/
theorem isRealAnalyticPoly_iff_exists_holomorphic [CompleteSpace E] [CompleteSpace F]
    (f : E → F) (x : E) :
    IsRealAnalyticPoly f x ↔
      ∃ g : Cpx E → Cpx F, AnalyticAt ℂ g (ofRealCLM x) ∧
        ∀ᶠ y in 𝓝 x, g (ofRealCLM y) = ofRealCLM (f y) :=
  isRealAnalyticPoly_iff_hasLocalHolomorphicExtension f x

/-- Map level: `IsRealAnalyticMap f ↔` a local holomorphic extension near every input. -/
theorem isRealAnalyticMap_iff_hasLocalHolomorphicExtension [CompleteSpace E] [CompleteSpace F]
    (f : E → F) :
    IsRealAnalyticMap f ↔ ∀ x,
      HasLocalHolomorphicExtension (ofRealCLM : E →L[ℝ] Cpx E) (ofRealCLM : F →L[ℝ] Cpx F) f x :=
  forall_congr' fun x => isRealAnalyticPoly_iff_hasLocalHolomorphicExtension f x

end Extension

end QuantumNLS.RealAnalyticComplexify

/-! ### Axiom audit -/
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.innerCore
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.instInnerProductSpaceComplex
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.instCompleteSpace
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.norm_sq_eq
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.isometry_ofRealCLM
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.isGenuineComplexification
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.inner_ofRealCLM
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.reCLM_ofRealCLM
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.eq_ofReal_add_I_smul
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.ofReal_add_I_smul_eq_zero
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.linearMap_ext_ofReal
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.conjCLM_smul
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.conjCLM_eq_self_iff
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.ofReal_re_eq
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.realCpx_update_I
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.cpxML
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.norm_cpxML_le
#print axioms QuantumNLS.RealAnalyticComplexify.Cpx.cpxML_ofReal
#print axioms QuantumNLS.RealAnalyticComplexify.cpxSeries_radius_pos
#print axioms QuantumNLS.RealAnalyticComplexify.exists_holomorphic_extension_of_analyticAt
#print axioms QuantumNLS.RealAnalyticComplexify.hasLocalHolomorphicExtension_of_analyticAt
#print axioms QuantumNLS.RealAnalyticComplexify.analyticAt_iff_hasLocalHolomorphicExtension
#print axioms QuantumNLS.RealAnalyticComplexify.isRealAnalyticPoly_iff_hasLocalHolomorphicExtension
#print axioms QuantumNLS.RealAnalyticComplexify.isRealAnalyticPoly_iff_exists_holomorphic
#print axioms QuantumNLS.RealAnalyticComplexify.isRealAnalyticMap_iff_hasLocalHolomorphicExtension
