/-
QuantumNLS.PhysicalTensor — DEF-004 / DEF-030 on the actual physical carrier (owner: opus_tensor).

Source (pinned report 3b1f701a, chapters/definitions.tex):
* DEF-001 (:7)  "For a fixed L>0, set 𝕋_L = ℝ/Lℤ with Lebesgue measure of mass L. The physical
  Hilbert space is L²(𝕋_L;ℂ), with ⟨f,g⟩ = ∫₀^L conj f g linear in the second variable."
* DEF-004 (:25) "H_N = Sym^N L²(𝕋_L), the permutation-invariant subspace of the ordinary tensor
  product. The orthogonal projection P_N is the average of the N! permutation operators. The
  zero-particle sector is ℂ."
* DEF-030 (:181) "For a normalized symmetric N-body vector, γ^{(k)} is the partial trace of its
  rank-one density operator over the last N−k physical factors. It is positive with trace one."

Frozen imports (read-only): TensorCarrier 1b210cb0…, TraceClass e6a8fdd7….  `Fourier.lean`
is not imported (it is still moving).  The carrier `L2T L` is mathlib's
`Lp ℂ 2 (volume : Measure (AddCircle L))`, the same type `Fourier.lean` uses.

No carrier equivalence is assumed: the identification of the completed tensor power with
L²(𝕋_L^N) (U2 position bridge) is CONSTRUCTED and PROVED in §5–§7.  This file proves:
* §1 DEF-001 carrier facts: mass `L` and `⟪f,g⟫ = ∫₀^L conj f · g`.
* §2 Zero sector: `HilbertTensorPower 𝕜 E 0 ≃ₗᵢ 𝕜`, with `SymSector 𝕜 E 0 = ⊤` and `P_0 = id`.
* §3 `N = k + (N−k)` packaging of DEF-030: `reducedDensityN N k hk ψ`, positive, with trace
  `‖ψ‖²` in every Hilbert basis, product states, and the DEF-028 → DEF-030 transfer.
* §4 Instances at `E = L²(𝕋_L)`.
* §5 U2 bridge, isometric part: `physEmbed : (L²(𝕋_L))^{⊗̂N} →ₗᵢ L²(𝕋_L^N)`, `⊗f ↦ ∏ⱼ fⱼ(xⱼ)`,
  constructed (multilinear product map, Fubini inner-product identity, completion extension).
* §6 Density: the star-subalgebra spanned by continuous products separates points, so it is
  dense by Stone–Weierstrass; continuous functions are dense in L²; the range of an isometry is
  closed.  Hence `physEmbed_surjective`, and `physUnitary : (L²(𝕋_L))^{⊗̂N} ≃ₗᵢ L²(𝕋_L^N)`.
* §7 Permutations: `physEmbed ∘ U_σ = V_σ ∘ physEmbed` with `(V_σ F)(x) = F(x ∘ σ)`, and
  `mem_physSector_iff`: `ψ ∈ Sym^N L²(𝕋_L)` iff its wave function is permutation invariant.
-/
import QuantumNLS.TraceClass
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Fourier.AddCircle

open scoped InnerProductSpace ENNReal
open MeasureTheory QuantumNLS.TensorCarrier QuantumNLS.TraceClass

noncomputable section

namespace QuantumNLS.PhysicalTensor

/-! ## §1 DEF-001 carrier -/

section Carrier

variable (L : ℝ) [Fact (0 < L)]

/-- The physical Hilbert space `L²(𝕋_L; ℂ)`, `𝕋_L = ℝ/Lℤ` with Lebesgue (Haar) measure of mass `L`. -/
abbrev L2T : Type := Lp ℂ 2 (volume : Measure (AddCircle L))

/-- The measure on `𝕋_L` has mass `L` (not a probability normalization). -/
theorem torus_mass : (volume : Measure (AddCircle L)) Set.univ = ENNReal.ofReal L :=
  AddCircle.measure_univ L

/-- `⟪f, g⟫ = ∫₀^L conj f · g`, linear in the second variable. -/
theorem inner_L2T (f g : L2T L) :
    ⟪f, g⟫_ℂ = ∫ x in (0 : ℝ)..L,
      (starRingEnd ℂ) (f (x : AddCircle L)) * g (x : AddCircle L) := by
  rw [MeasureTheory.L2.inner_def]
  have h := AddCircle.intervalIntegral_preimage L 0 (fun a : AddCircle L =>
    (starRingEnd ℂ) (f a) * g a)
  rw [zero_add] at h
  rw [h]
  congr 1
  funext a
  exact RCLike.inner_apply' _ _

end Carrier

/-! ## §2 The zero-particle sector is the scalars -/

section ZeroSector

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `⨂^0 E ≃ 𝕜` (mathlib `PiTensorProduct.isEmptyEquiv`) on the Hilbert synonym. -/
def zeroAlgLinearEquiv : AlgTensorPower 𝕜 E 0 ≃ₗ[𝕜] 𝕜 :=
  PiTensorProduct.isEmptyEquiv (Fin 0)

theorem inner_zeroAlgLinearEquiv (x y : AlgTensorPower 𝕜 E 0) :
    ⟪zeroAlgLinearEquiv x, zeroAlgLinearEquiv y⟫_𝕜 = ⟪x, y⟫_𝕜 := rfl

/-- `⨂^0 E ≃ₗᵢ 𝕜` (pre-Hilbert level). -/
def zeroAlgIsometry : AlgTensorPower 𝕜 E 0 ≃ₗᵢ[𝕜] 𝕜 :=
  zeroAlgLinearEquiv.isometryOfInner inner_zeroAlgLinearEquiv

/-- The completion of a complete space is the space itself, isometrically. -/
def completionSelf (V : Type*) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [CompleteSpace V] : UniformSpace.Completion V ≃ₗᵢ[𝕜] V :=
  LinearIsometryEquiv.ofSurjective (LinearIsometry.id : V →ₗᵢ[𝕜] V).fromCompletion
    (fun v => ⟨(v : UniformSpace.Completion V), by
      rw [LinearIsometry.fromCompletion_apply_coe]; rfl⟩)

/-- **DEF-004, zero sector.** `E^{⊗̂0} ≃ₗᵢ 𝕜`. -/
def zeroSectorIso : HilbertTensorPower 𝕜 E 0 ≃ₗᵢ[𝕜] 𝕜 :=
  (lieCompletion zeroAlgIsometry).trans (completionSelf 𝕜)

theorem zeroSectorIso_htpow (u : E) : zeroSectorIso (htpow 0 u : HilbertTensorPower 𝕜 E 0) = 1 := by
  show completionSelf 𝕜 (lieCompletion zeroAlgIsometry _) = 1
  rw [htpow, lieCompletion_coe]
  show (LinearIsometry.id : 𝕜 →ₗᵢ[𝕜] 𝕜).fromCompletion _ = 1
  rw [LinearIsometry.fromCompletion_apply_coe]
  show PiTensorProduct.isEmptyEquiv (R := 𝕜) (s := fun _ : Fin 0 => E) (Fin 0)
    (PiTensorProduct.tprod 𝕜 (fun _ : Fin 0 => u)) = 1
  exact PiTensorProduct.isEmptyEquiv_apply_tprod (Fin 0) _

/-- Every vector of the zero sector is symmetric: `Sym^0 E = E^{⊗̂0}`. -/
theorem symSector_zero : SymSector 𝕜 E 0 = ⊤ := by
  rw [eq_top_iff]
  intro v _ σ
  rw [Subsingleton.elim σ 1, map_one]
  rfl

/-- `P_0 = id`. -/
theorem symProj_zero : symProj 𝕜 E 0 = ContinuousLinearMap.id 𝕜 _ := by
  ext v
  exact groupAverage_apply_of_mem _ (by rw [← SymSector, symSector_zero]; trivial)

end ZeroSector

/-! ## §3 `N = k + (N − k)` packaging of DEF-030 -/

section Packaging

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Transport along `n = m` (the identity after `subst`). -/
def castHTP {n m : ℕ} (h : n = m) :
    HilbertTensorPower 𝕜 E n ≃ₗᵢ[𝕜] HilbertTensorPower 𝕜 E m := by
  subst h; exact LinearIsometryEquiv.refl 𝕜 _

theorem castHTP_htpow {n m : ℕ} (h : n = m) (u : E) :
    castHTP h (htpow n u : HilbertTensorPower 𝕜 E n) = htpow m u := by
  subst h; rfl

theorem castHTP_mem_symSector {n m : ℕ} (h : n = m) {ψ : HilbertTensorPower 𝕜 E n}
    (hψ : ψ ∈ SymSector 𝕜 E n) : castHTP h ψ ∈ SymSector 𝕜 E m := by
  subst h; exact hψ

/-- **DEF-030.** `γ^{(k)}_ψ` for `ψ ∈ E^{⊗̂N}` and `k ≤ N`: the partial trace of `|ψ⟩⟨ψ|` over the
last `N − k` factors. -/
def reducedDensityN (N k : ℕ) (hk : k ≤ N) (ψ : HilbertTensorPower 𝕜 E N) :
    HilbertTensorPower 𝕜 E k →L[𝕜] HilbertTensorPower 𝕜 E k :=
  reducedDensityPower k (N - k) (castHTP (Nat.add_sub_cancel' hk).symm ψ)

theorem reducedDensityN_isPositive (N k : ℕ) (hk : k ≤ N) (ψ : HilbertTensorPower 𝕜 E N) :
    (reducedDensityN N k hk ψ).IsPositive :=
  reducedDensityPower_isPositive _ _ _

/-- Trace `‖ψ‖²` in every Hilbert basis; trace one for normalized `ψ`. -/
theorem traceIn_reducedDensityN {ι : Type*} (N k : ℕ) (hk : k ≤ N)
    (c : HilbertBasis ι 𝕜 (HilbertTensorPower 𝕜 E k)) (ψ : HilbertTensorPower 𝕜 E N) :
    traceIn c (reducedDensityN N k hk ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [reducedDensityN, traceIn_reducedDensityPower, LinearIsometryEquiv.norm_map]

theorem traceIn_reducedDensityN_eq_one {ι : Type*} (N k : ℕ) (hk : k ≤ N)
    (c : HilbertBasis ι 𝕜 (HilbertTensorPower 𝕜 E k)) (ψ : HilbertTensorPower 𝕜 E N)
    (hψ : ‖ψ‖ = 1) : traceIn c (reducedDensityN N k hk ψ) = 1 := by
  rw [traceIn_reducedDensityN, hψ]; simp

/-- Product states: `γ^{(k)}(u^{⊗N}) = ‖u‖^{2(N−k)} |u^{⊗k}⟩⟨u^{⊗k}|`. -/
theorem reducedDensityN_htpow (N k : ℕ) (hk : k ≤ N) (u : E) :
    reducedDensityN N k hk (htpow N u : HilbertTensorPower 𝕜 E N) =
      ((‖u‖ ^ (2 * (N - k)) : ℝ) : 𝕜) •
        InnerProductSpace.rankOne 𝕜 (htpow k u : HilbertTensorPower 𝕜 E k) (htpow k u) := by
  rw [reducedDensityN, castHTP_htpow, reducedDensityPower_htpow]

end Packaging

section PackagingComplex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `‖γ^{(k)}_ψ‖₁ = ‖ψ‖²` (trace class). -/
theorem traceNorm_reducedDensityN (N k : ℕ) (hk : k ≤ N) (ψ : HilbertTensorPower ℂ E N) :
    traceNorm (reducedDensityN N k hk ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [reducedDensityN, traceNorm_reducedDensityPower, LinearIsometryEquiv.norm_map]

omit [CompleteSpace E] in
/-- **DEF-028 → DEF-030 transfer in sector `N`.** For unit `u`:
`‖γ^{(k)}_ψ − |u^{⊗k}⟩⟨u^{⊗k}|‖₁ ≤ ‖ψ − u^{⊗N}‖ (‖ψ‖ + 1)`. -/
theorem traceNorm_reducedDensityN_sub_product_le (N k : ℕ) (hk : k ≤ N) (u : E) (hu : ‖u‖ = 1)
    (ψ : HilbertTensorPower ℂ E N) :
    traceNorm (reducedDensityN N k hk ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ E k) (htpow k u)) ≤
      ENNReal.ofReal (‖ψ - htpow N u‖ * (‖ψ‖ + 1)) := by
  have h := traceNorm_reducedDensityPower_sub_product_le k (N - k) u hu
    (castHTP (Nat.add_sub_cancel' hk).symm ψ)
  rw [← castHTP_htpow (𝕜 := ℂ) (Nat.add_sub_cancel' hk).symm u, ← map_sub,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map] at h
  exact h

end PackagingComplex

/-! ## §4 Instances on the physical carrier `E = L²(𝕋_L)` -/

section Physical

variable (L : ℝ) [Fact (0 < L)]

/-- **DEF-004.** `H_N = Sym^N L²(𝕋_L)` inside the completed tensor power. -/
abbrev physSector (N : ℕ) : Submodule ℂ (HilbertTensorPower ℂ (L2T L) N) :=
  SymSector ℂ (L2T L) N

/-- **DEF-004.** `P_N = (N!)⁻¹ Σ_σ U_σ` is the orthogonal projection onto `H_N`. -/
theorem physSymProj_eq (N : ℕ) :
    symProj ℂ (L2T L) N = (physSector L N).starProjection ∧
      symProj ℂ (L2T L) N = ((N.factorial : ℂ)⁻¹) •
        ∑ σ : Equiv.Perm (Fin N), (permRep ℂ (L2T L) N σ :
          HilbertTensorPower ℂ (L2T L) N →L[ℂ] _) :=
  ⟨symProj_eq_starProjection N, symProj_eq_factorial_average N⟩

/-- **DEF-004, zero-particle sector is ℂ.** -/
theorem physZeroSector : physSector L 0 = ⊤ ∧
    Nonempty (HilbertTensorPower ℂ (L2T L) 0 ≃ₗᵢ[ℂ] ℂ) :=
  ⟨symSector_zero, ⟨zeroSectorIso⟩⟩

/-- **DEF-030 on the physical carrier**, for a normalized `ψ ∈ H_N`: `γ^{(k)}_ψ` is positive,
has trace one in every Hilbert basis, and trace norm one. -/
theorem physReducedDensity_spec {ι : Type*} (N k : ℕ) (hk : k ≤ N)
    (ψ : HilbertTensorPower ℂ (L2T L) N) (_hsym : ψ ∈ physSector L N) (hψ : ‖ψ‖ = 1)
    (c : HilbertBasis ι ℂ (HilbertTensorPower ℂ (L2T L) k)) :
    (reducedDensityN N k hk ψ).IsPositive ∧ traceIn c (reducedDensityN N k hk ψ) = 1 ∧
      traceNorm (reducedDensityN N k hk ψ) = 1 := by
  refine ⟨reducedDensityN_isPositive N k hk ψ, traceIn_reducedDensityN_eq_one N k hk c ψ hψ, ?_⟩
  rw [traceNorm_reducedDensityN, hψ]; simp

end Physical

/-! ## §5 Physical product realization `E^{⊗̂N} → L²(𝕋_L^N)` (U2 bridge, isometric part)

`⊗ f ↦ [x ↦ ∏ⱼ fⱼ(xⱼ)]` is well defined (each product of L² functions of distinct coordinates is
in L² of the product measure), multilinear, and inner-product preserving by Fubini
(`integral_fintype_prod_eq_prod`).  Hence it extends to a linear ISOMETRY
`physEmbed : HilbertTensorPower ℂ (L2T L) N →ₗᵢ L²(𝕋_L^N)`.  Surjectivity (density of product
functions in `L²(𝕋_L^N)`) is NOT proved here and is not assumed. -/

section ProductRealization

variable (L : ℝ) [Fact (0 < L)] (N : ℕ)

/-- Product Lebesgue measure on `𝕋_L^N` (mass `L^N`). -/
abbrev torusPiMeasure : Measure (Fin N → AddCircle L) :=
  Measure.pi fun _ => (volume : Measure (AddCircle L))

/-- `L²(𝕋_L^N)`. -/
abbrev L2TN : Type := Lp ℂ 2 (torusPiMeasure L N)

variable {L N}

/-- `x ↦ ∏ⱼ fⱼ(xⱼ)`. -/
def prodFun (f : Fin N → L2T L) (x : Fin N → AddCircle L) : ℂ := ∏ j, f j (x j)

theorem aestronglyMeasurable_prodFun (f : Fin N → L2T L) :
    AEStronglyMeasurable (prodFun f) (torusPiMeasure L N) := by
  unfold prodFun
  exact Finset.aestronglyMeasurable_fun_prod _ fun j _ =>
    (Lp.aestronglyMeasurable (f j)).comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure (AddCircle L))) j)

theorem memLp_prodFun (f : Fin N → L2T L) : MemLp (prodFun f) 2 (torusPiMeasure L N) := by
  refine (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_prodFun f)).mpr ?_
  have h : Integrable (fun x : Fin N → AddCircle L => ∏ j, ‖f j (x j)‖ ^ 2)
      (torusPiMeasure L N) :=
    Integrable.fintype_prod (f := fun j y => ‖f j y‖ ^ 2) fun j =>
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (f j))).mp (Lp.memLp (f j))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [prodFun, norm_prod, Finset.prod_pow]

/-- The product vector `[∏ⱼ fⱼ(xⱼ)] ∈ L²(𝕋_L^N)`. -/
def prodLp (f : Fin N → L2T L) : L2TN L N := (memLp_prodFun f).toLp _

theorem prodFun_update [DecidableEq (Fin N)] (f : Fin N → L2T L) (j : Fin N) (c : L2T L)
    (x : Fin N → AddCircle L) :
    prodFun (Function.update f j c) x = c (x j) * ∏ i ∈ Finset.univ.erase j, f i (x i) := by
  unfold prodFun
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The product map is multilinear. -/
def prodMultilinear : MultilinearMap ℂ (fun _ : Fin N => L2T L) (L2TN L N) where
  toFun := prodLp
  map_update_add' f j a b := by
    unfold prodLp
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_eval
      (fun _ => (volume : Measure (AddCircle L))) j).ae (Lp.coeFn_add a b)] with x hx
    simp only [Pi.add_apply, prodFun_update]
    rw [hx, Pi.add_apply]
    ring
  map_update_smul' f j r a := by
    unfold prodLp
    rw [← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [(Measure.quasiMeasurePreserving_eval
      (fun _ => (volume : Measure (AddCircle L))) j).ae (Lp.coeFn_smul r a)] with x hx
    simp only [Pi.smul_apply, prodFun_update, smul_eq_mul]
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring

theorem inner_prodLp (f g : Fin N → L2T L) :
    ⟪prodLp f, prodLp g⟫_ℂ = ∏ j, ⟪f j, g j⟫_ℂ := by
  rw [MeasureTheory.L2.inner_def]
  have hf := (memLp_prodFun f).coeFn_toLp
  have hg := (memLp_prodFun g).coeFn_toLp
  have h1 : ∫ x, ⟪(prodLp f : L2TN L N) x, (prodLp g : L2TN L N) x⟫_ℂ ∂(torusPiMeasure L N) =
      ∫ x, ∏ j, (starRingEnd ℂ) (f j (x j)) * g j (x j) ∂(torusPiMeasure L N) := by
    refine integral_congr_ae ?_
    filter_upwards [hf, hg] with x hfx hgx
    rw [prodLp, prodLp, hfx, hgx, RCLike.inner_apply', prodFun, prodFun, map_prod,
      ← Finset.prod_mul_distrib]
  rw [h1, integral_fintype_prod_eq_prod
    (f := fun j (y : AddCircle L) => (starRingEnd ℂ) (f j y) * g j y)]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact (RCLike.inner_apply' _ _).symm

/-- The product map on the algebraic power. -/
def prodAlgLinear : AlgTensorPower ℂ (L2T L) N →ₗ[ℂ] L2TN L N :=
  PiTensorProduct.lift prodMultilinear

theorem prodAlgLinear_ptprod (f : Fin N → L2T L) :
    prodAlgLinear (ptprod f : AlgTensorPower ℂ (L2T L) N) = prodLp f :=
  PiTensorProduct.lift.tprod f

theorem inner_prodAlgLinear (x y : AlgTensorPower ℂ (L2T L) N) :
    ⟪prodAlgLinear x, prodAlgLinear y⟫_ℂ = ⟪x, y⟫_ℂ := by
  refine inner_map_map_of_span prodAlgLinear (span_range_ptprod N) ?_ x y
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  rw [prodAlgLinear_ptprod, prodAlgLinear_ptprod, inner_prodLp, inner_ptprod]

/-- **U2 bridge (isometric part).** `physEmbed : (L²(𝕋_L))^{⊗̂N} →ₗᵢ L²(𝕋_L^N)`,
`⊗ f ↦ ∏ⱼ fⱼ(xⱼ)`. -/
def physEmbed : HilbertTensorPower ℂ (L2T L) N →ₗᵢ[ℂ] L2TN L N :=
  (prodAlgLinear.isometryOfInner inner_prodAlgLinear).fromCompletion

theorem physEmbed_ptprod (f : Fin N → L2T L) :
    physEmbed ((ptprod f : AlgTensorPower ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N) =
      prodLp f := by
  rw [physEmbed, LinearIsometry.fromCompletion_apply_coe]
  exact prodAlgLinear_ptprod f

/-- `u^{⊗N} ↦ [x ↦ ∏ⱼ u(xⱼ)]`. -/
theorem physEmbed_htpow (u : L2T L) :
    physEmbed (htpow N u : HilbertTensorPower ℂ (L2T L) N) = prodLp (fun _ => u) :=
  physEmbed_ptprod _

theorem coeFn_physEmbed_htpow (u : L2T L) :
    (physEmbed (htpow N u : HilbertTensorPower ℂ (L2T L) N) : (Fin N → AddCircle L) → ℂ)
      =ᵐ[torusPiMeasure L N] fun x => ∏ j, u (x j) := by
  rw [physEmbed_htpow]
  exact (memLp_prodFun _).coeFn_toLp

end ProductRealization

/-! ## §6 Density of product functions: `physEmbed` is onto (U2 bridge, unitary)

Route: the star-subalgebra of `C(𝕋_L^N, ℂ)` spanned by products `x ↦ ∏ⱼ gⱼ(xⱼ)` of continuous
single-coordinate functions separates points (via the Fourier characters of `AddCircle L`), so it is
uniformly dense by Stone–Weierstrass; continuous functions are dense in `L²(𝕋_L^N)`
(`ContinuousMap.toLp_denseRange`); and the range of the isometry `physEmbed` is closed and
contains all such products. -/

section Density

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `x ↦ ∏ⱼ gⱼ(xⱼ)` as a continuous function on `𝕋_L^N`. -/
def prodCont (g : Fin N → C(AddCircle L, ℂ)) : C(Fin N → AddCircle L, ℂ) :=
  ⟨fun x => ∏ j, g j (x j),
    continuous_finset_prod _ fun j _ => (g j).continuous.comp (continuous_apply j)⟩

omit [Fact (0 < L)] in
theorem prodCont_apply (g : Fin N → C(AddCircle L, ℂ)) (x : Fin N → AddCircle L) :
    prodCont g x = ∏ j, g j (x j) := rfl

variable (L N) in
/-- The generating set of products. -/
def prodSet : Set C(Fin N → AddCircle L, ℂ) := Set.range (prodCont (L := L) (N := N))

omit [Fact (0 < L)] in
theorem prodCont_mul (g h : Fin N → C(AddCircle L, ℂ)) :
    prodCont g * prodCont h = prodCont (g * h) := by
  ext x
  simp [prodCont_apply, Finset.prod_mul_distrib]

omit [Fact (0 < L)] in
theorem star_prodCont (g : Fin N → C(AddCircle L, ℂ)) :
    star (prodCont g) = prodCont (star g) := by
  ext x
  simp [prodCont_apply]

omit [Fact (0 < L)] in
theorem prodCont_one : prodCont (1 : Fin N → C(AddCircle L, ℂ)) = 1 := by
  ext x
  simp [prodCont_apply]

variable (L N) in
/-- The star-subalgebra spanned by products of continuous single-coordinate functions. -/
def prodAlgebra : StarSubalgebra ℂ C(Fin N → AddCircle L, ℂ) where
  carrier := Submodule.span ℂ (prodSet L N)
  mul_mem' {a b} ha hb := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
      induction hb using Submodule.span_induction with
      | mem b hb =>
        obtain ⟨g, rfl⟩ := ha
        obtain ⟨h, rfl⟩ := hb
        exact Submodule.subset_span ⟨g * h, (prodCont_mul g h).symm⟩
      | zero => simp
      | add b b' _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
      | smul c b _ h1 => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h1
    | zero => simp
    | add a a' _ _ h1 h2 => rw [add_mul]; exact add_mem h1 h2
    | smul c a _ h1 => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h1
  add_mem' ha hb := add_mem ha hb
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨1, prodCont_one⟩)
  star_mem' {a} ha := by
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      exact Submodule.subset_span ⟨star g, (star_prodCont g).symm⟩
    | zero => simp
    | add a a' _ _ h1 h2 => rw [star_add]; exact add_mem h1 h2
    | smul c a _ h1 => rw [star_smul]; exact Submodule.smul_mem _ _ h1

theorem prodAlgebra_separatesPoints : (prodAlgebra L N).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  obtain ⟨_, ⟨g, -, rfl⟩, hg⟩ := fourierSubalgebra_separatesPoints (T := L) hj
  refine ⟨_, ⟨prodCont (Function.update (1 : Fin N → C(AddCircle L, ℂ)) j g),
    Submodule.subset_span ⟨_, rfl⟩, rfl⟩, ?_⟩
  have e : ∀ z : Fin N → AddCircle L,
      prodCont (Function.update (1 : Fin N → C(AddCircle L, ℂ)) j g) z = g (z j) := by
    intro z
    rw [prodCont_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      Function.update_self]
    rw [Finset.prod_eq_one fun i hi => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]; rfl, mul_one]
  simpa [e] using hg

theorem prodAlgebra_dense : (prodAlgebra L N).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    prodAlgebra_separatesPoints

/-- A continuous product function lies in the range of `physEmbed`. -/
theorem toLp_prodCont_mem_range (g : Fin N → C(AddCircle L, ℂ)) :
    ContinuousMap.toLp (E := ℂ) 2 (torusPiMeasure L N) ℂ (prodCont g) ∈
      Set.range (physEmbed (L := L) (N := N)) := by
  refine ⟨((ptprod (fun j => ContinuousMap.toLp (E := ℂ) 2
    (volume : Measure (AddCircle L)) ℂ (g j)) : AlgTensorPower ℂ (L2T L) N) :
      HilbertTensorPower ℂ (L2T L) N), ?_⟩
  rw [physEmbed_ptprod]
  refine Lp.ext ?_
  have h1 := (memLp_prodFun (fun j => ContinuousMap.toLp (E := ℂ) 2
    (volume : Measure (AddCircle L)) ℂ (g j))).coeFn_toLp
  have h2 := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (torusPiMeasure L N) (prodCont g)
  have h3 : ∀ᵐ x ∂(torusPiMeasure L N), ∀ j,
      (ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ (g j) :
        AddCircle L → ℂ) (x j) = g j (x j) := by
    rw [ae_all_iff]
    intro j
    exact (Measure.quasiMeasurePreserving_eval
      (fun _ => (volume : Measure (AddCircle L))) j).ae
      (ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (volume : Measure (AddCircle L)) (g j))
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [prodLp, hx1, hx2, prodFun, prodCont_apply]
  exact Finset.prod_congr rfl fun j _ => hx3 j

/-- **U2 bridge, density.** `physEmbed` is surjective. -/
theorem physEmbed_surjective : Function.Surjective (physEmbed (L := L) (N := N)) := by
  set R : Set (L2TN L N) := Set.range (physEmbed (L := L) (N := N)) with hR
  have hclosed : IsClosed R := physEmbed.isometry.isClosedEmbedding.isClosed_range
  set φ := ContinuousMap.toLp (E := ℂ) 2 (torusPiMeasure L N) ℂ with hφ
  -- the span of products maps into `R`
  have hspan : ∀ F ∈ (prodAlgebra L N : Set C(Fin N → AddCircle L, ℂ)), φ F ∈ R := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => obtain ⟨g, rfl⟩ := hF; exact toLp_prodCont_mem_range g
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add a b _ _ h1 h2 =>
      obtain ⟨u, hu⟩ := h1; obtain ⟨v, hv⟩ := h2
      exact ⟨u + v, by rw [map_add, hu, hv, map_add]⟩
    | smul c a _ h1 =>
      obtain ⟨u, hu⟩ := h1
      exact ⟨c • u, by rw [map_smul, hu, map_smul]⟩
  -- all continuous functions map into `R`
  have hcont : ∀ F : C(Fin N → AddCircle L, ℂ), φ F ∈ R := by
    intro F
    have hF : F ∈ closure (prodAlgebra L N : Set C(Fin N → AddCircle L, ℂ)) := by
      rw [← StarSubalgebra.topologicalClosure_coe, prodAlgebra_dense]; trivial
    have : φ F ∈ closure (φ '' (prodAlgebra L N : Set C(Fin N → AddCircle L, ℂ))) :=
      map_mem_closure φ.continuous hF (fun G hG => ⟨G, hG, rfl⟩)
    exact closure_minimal (by rintro _ ⟨G, hG, rfl⟩; exact hspan G hG) hclosed this
  -- continuous functions are dense in `L²`
  have hdense : DenseRange φ :=
    ContinuousMap.toLp_denseRange (E := ℂ) (𝕜 := ℂ) (μ := torusPiMeasure L N) (p := 2)
      (by norm_num)
  intro ψ
  have : ψ ∈ closure (Set.range φ) := hdense ψ
  exact closure_minimal (by rintro _ ⟨F, rfl⟩; exact hcont F) hclosed this

/-- **U2 bridge.** `(L²(𝕋_L))^{⊗̂N} ≃ₗᵢ L²(𝕋_L^N)`, `⊗f ↦ ∏ⱼ fⱼ(xⱼ)`. -/
def physUnitary : HilbertTensorPower ℂ (L2T L) N ≃ₗᵢ[ℂ] L2TN L N :=
  LinearIsometryEquiv.ofSurjective physEmbed physEmbed_surjective

theorem physUnitary_ptprod (f : Fin N → L2T L) :
    physUnitary ((ptprod f : AlgTensorPower ℂ (L2T L) N) : HilbertTensorPower ℂ (L2T L) N) =
      prodLp f :=
  physEmbed_ptprod f

end Density
/-! ## §7 Permutations: tensor-factor permutations are physical coordinate permutations -/

section Permutations

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- The coordinate permutation `x ↦ x ∘ σ` as a measurable equivalence of `𝕋_L^N`. -/
def coordPerm (σ : Equiv.Perm (Fin N)) : (Fin N → AddCircle L) ≃ᵐ (Fin N → AddCircle L) :=
  MeasurableEquiv.arrowCongr' σ.symm (MeasurableEquiv.refl _)

omit [Fact (0 < L)] in
theorem coordPerm_apply (σ : Equiv.Perm (Fin N)) (x : Fin N → AddCircle L) (i : Fin N) :
    coordPerm σ x i = x (σ i) := rfl

theorem measurePreserving_coordPerm (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (coordPerm (L := L) σ) (torusPiMeasure L N) (torusPiMeasure L N) :=
  measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) σ.symm
    (MeasurableEquiv.refl _) (fun _ => MeasurePreserving.id _)

/-- The physical permutation operator `(V_σ F)(x) = F(x ∘ σ)` on `L²(𝕋_L^N)`. -/
def physPerm (σ : Equiv.Perm (Fin N)) : L2TN L N →ₗᵢ[ℂ] L2TN L N :=
  Lp.compMeasurePreservingₗᵢ ℂ (coordPerm σ) (measurePreserving_coordPerm σ)

theorem coeFn_physPerm (σ : Equiv.Perm (Fin N)) (F : L2TN L N) :
    (physPerm σ F : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N] fun x => F (coordPerm σ x) :=
  Lp.coeFn_compMeasurePreserving F (measurePreserving_coordPerm σ)

theorem physEmbed_coe (a : AlgTensorPower ℂ (L2T L) N) :
    physEmbed (a : HilbertTensorPower ℂ (L2T L) N) = prodAlgLinear a := by
  rw [physEmbed, LinearIsometry.fromCompletion_apply_coe]; rfl

theorem prodLp_perm (σ : Equiv.Perm (Fin N)) (f : Fin N → L2T L) :
    prodLp (fun i => f (σ.symm i)) = physPerm σ (prodLp f) := by
  refine Lp.ext ?_
  have h1 := (memLp_prodFun (fun i => f (σ.symm i))).coeFn_toLp
  have h2 := coeFn_physPerm σ (prodLp f)
  have h3 : (fun x => (prodLp f : L2TN L N) (coordPerm σ x)) =ᵐ[torusPiMeasure L N]
      fun x => prodFun f (coordPerm σ x) :=
    (measurePreserving_coordPerm σ).quasiMeasurePreserving.ae_eq_comp
      (memLp_prodFun f).coeFn_toLp
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  rw [prodLp, hx1, hx2]
  show prodFun (fun i => f (σ.symm i)) x = (prodLp f : L2TN L N) (coordPerm σ x)
  rw [hx3]
  simp only [prodFun, coordPerm_apply]
  exact (Equiv.prod_comp σ (fun i => f (σ.symm i) (x i))).symm.trans
    (Finset.prod_congr rfl fun j _ => by simp)

/-- **Intertwining.** `physEmbed ∘ U_σ = V_σ ∘ physEmbed`. -/
theorem physEmbed_permRep (σ : Equiv.Perm (Fin N)) (ψ : HilbertTensorPower ℂ (L2T L) N) :
    physEmbed ((permRep ℂ (L2T L) N σ : HilbertTensorPower ℂ (L2T L) N →L[ℂ] _) ψ) =
      physPerm σ (physEmbed ψ) := by
  rw [permRep_apply]
  induction ψ using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (physEmbed.continuous.comp (permHilbertIsometry σ).continuous)
      ((physPerm σ).continuous.comp physEmbed.continuous)
  | ih a =>
    rw [permHilbertIsometry_coe, physEmbed_coe, physEmbed_coe]
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [map_smul, map_smul, map_smul, map_smul, permLinearEquiv_ptprod, prodAlgLinear_ptprod,
        prodAlgLinear_ptprod, prodLp_perm]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- **DEF-004 in the position model.** `ψ ∈ Sym^N L²(𝕋_L)` iff its position-space wave function is
invariant under every coordinate permutation. -/
theorem mem_physSector_iff (ψ : HilbertTensorPower ℂ (L2T L) N) :
    ψ ∈ physSector L N ↔ ∀ σ : Equiv.Perm (Fin N), physPerm σ (physUnitary ψ) = physUnitary ψ := by
  constructor
  · intro h σ
    have := congrArg physEmbed (h σ)
    rwa [physEmbed_permRep] at this
  · intro h σ
    apply physEmbed.injective
    rw [physEmbed_permRep]
    exact h σ

end Permutations

end QuantumNLS.PhysicalTensor

#print axioms QuantumNLS.PhysicalTensor.inner_L2T
#print axioms QuantumNLS.PhysicalTensor.zeroSectorIso
#print axioms QuantumNLS.PhysicalTensor.zeroSectorIso_htpow
#print axioms QuantumNLS.PhysicalTensor.symProj_zero
#print axioms QuantumNLS.PhysicalTensor.reducedDensityN_htpow
#print axioms QuantumNLS.PhysicalTensor.traceNorm_reducedDensityN_sub_product_le
#print axioms QuantumNLS.PhysicalTensor.physZeroSector
#print axioms QuantumNLS.PhysicalTensor.physReducedDensity_spec
#print axioms QuantumNLS.PhysicalTensor.inner_prodLp
#print axioms QuantumNLS.PhysicalTensor.physEmbed
#print axioms QuantumNLS.PhysicalTensor.coeFn_physEmbed_htpow
#print axioms QuantumNLS.PhysicalTensor.prodAlgebra_dense
#print axioms QuantumNLS.PhysicalTensor.physEmbed_surjective
#print axioms QuantumNLS.PhysicalTensor.physUnitary
#print axioms QuantumNLS.PhysicalTensor.physEmbed_permRep
#print axioms QuantumNLS.PhysicalTensor.mem_physSector_iff
