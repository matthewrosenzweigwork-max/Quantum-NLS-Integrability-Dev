/-
QuantumNLS.TraceClass — roadmap R4 (owner: opus_tensor).  Trace-class infrastructure absent from
the pinned mathlib (d13f23b7): no trace-class / Hilbert–Schmidt / Schatten API exists there.

Source scope served (pinned report 3b1f701a):
* DEF-030 `def:report-30` (chapters/definitions.tex:181): γ^{(k)} "is positive with trace one.
  The trace norm is ‖A‖₁ = Tr|A|."
* DEF-031 `def:report-31` (chapters/definitions.tex:187): energy trace norm ‖A_k^{1/2} D A_k^{1/2}‖₁
  "defined through the corresponding trace-class form realization" (later; needs unbounded A_k).

Everything is constructed and proved; no structure field or hypothesis asserts a trace property.

§A  Parseval in `ℝ≥0∞` and the Hilbert–Schmidt sum `∑ᵢ ‖S bᵢ‖²` over a `HilbertBasis`, with the
    swap identity `HS_b(S) = HS_c(S†)` and hence independence of the basis (generic `RCLike 𝕜`,
    complete spaces; no square roots needed).
§C  Trace of a positive operator over a `HilbertBasis`, valued in `ℝ≥0∞`, and its basis
    independence via `T = (√T)† √T` (continuous functional calculus; `𝕜 = ℂ`, as in DEF-001).
§B  Tensor products of Hilbert bases are Hilbert bases of the completed tensor product, and the
    reduced density of `ψ ∈ X ⊗̂ Y` has trace `‖ψ‖²` in EVERY Hilbert basis (generic `RCLike 𝕜`).
    Applied to `reducedDensityPower`, this is the "trace one" clause of DEF-030 for normalized ψ.
    Imports the frozen `QuantumNLS.TensorCarrier` (read-only).
§D  Trace norm `‖A‖₁ := Tr|A|` with `|A| = √(A†A)` (mathlib `CFC.abs`), basis-free via §C;
    `IsTraceClass`; homogeneity, faithfulness `‖A‖₁ = 0 ↔ A = 0`, additivity of the trace on the
    positive cone, and `‖γ^{(k)}_ψ‖₁ = ‖ψ‖²` (complex Hilbert spaces).
§E  Triangle inequality `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁` WITHOUT polar decomposition (absent from the
    pinned mathlib): an upper duality bound `|∑_{i∈s} ⟪X bᵢ, A bᵢ⟫| ≤ ‖A‖₁` for contractions `X`
    via the regularised factorisation `A = (A h(R)) R + A g(R)`, `R = √|A|`, and a lower bound via
    the contraction `C (R² + ε)⁻¹`.
§F  Duality bound `traceNorm_le_of_forall`; stability `‖γ_ψ − γ_φ‖₁ ≤ ‖ψ−φ‖(‖ψ‖+‖φ‖)`; product
    states `γ^{(k)}(u^{⊗(k+m)}) = ‖u‖^{2m}|u^{⊗k}⟩⟨u^{⊗k}|`; and the DEF-028 → DEF-030 transfer
    `‖γ^{(k)}_ψ − |u^{⊗k}⟩⟨u^{⊗k}|‖₁ ≤ ‖ψ − u^{⊗(k+m)}‖(‖ψ‖+1)` for unit `u`.
-/
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import QuantumNLS.TensorCarrier

open scoped InnerProductSpace ENNReal

noncomputable section

namespace QuantumNLS.TraceClass

/-! ## §A Parseval and Hilbert–Schmidt sums -/

section HS

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Parseval's identity over a Hilbert basis, in real form. -/
theorem hasSum_norm_inner_sq (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => ‖⟪b i, x⟫_𝕜‖ ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  rw [← RCLike.hasSum_ofReal (𝕜 := 𝕜)]
  convert h using 1
  · ext i
    rw [← inner_conj_symm x (b i), RCLike.conj_mul]
    push_cast
    rfl
  · rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl

/-- Parseval's identity over a Hilbert basis, in `ℝ≥0∞`. -/
theorem tsum_ofReal_norm_inner_sq (b : HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i, ENNReal.ofReal (‖⟪b i, x⟫_𝕜‖ ^ 2) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have h' := hasSum_norm_inner_sq b x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) h'.summable, h'.tsum_eq]

/-- The Hilbert–Schmidt sum `∑ᵢ ‖S bᵢ‖² ∈ [0, ∞]` of `S` computed in the Hilbert basis `b`. -/
def hsSq (b : HilbertBasis ι 𝕜 E) (S : E →L[𝕜] F) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2)

/-- Swap identity: `∑ᵢ ‖S bᵢ‖² = ∑ⱼ ‖S† cⱼ‖²` for any Hilbert bases `b` of `E`, `c` of `F`. -/
theorem hsSq_eq_hsSq_adjoint [CompleteSpace E] [CompleteSpace F] (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) (S : E →L[𝕜] F) :
    hsSq b S = hsSq c (ContinuousLinearMap.adjoint S) := by
  unfold hsSq
  calc ∑' i, ENNReal.ofReal (‖S (b i)‖ ^ 2)
      = ∑' i, ∑' j, ENNReal.ofReal (‖⟪c j, S (b i)⟫_𝕜‖ ^ 2) := by
        simp_rw [tsum_ofReal_norm_inner_sq]
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪c j, S (b i)⟫_𝕜‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖⟪b i, ContinuousLinearMap.adjoint S (c j)⟫_𝕜‖ ^ 2) := by
        congr 1; ext j; congr 1; ext i
        rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]
    _ = ∑' j, ENNReal.ofReal (‖ContinuousLinearMap.adjoint S (c j)‖ ^ 2) := by
        simp_rw [tsum_ofReal_norm_inner_sq]

/-- **Basis independence** of the Hilbert–Schmidt sum. -/
theorem hsSq_eq_of_basis [CompleteSpace E] [CompleteSpace F] {ι' : Type*}
    (b : HilbertBasis ι 𝕜 E) (b' : HilbertBasis ι' 𝕜 E) (S : E →L[𝕜] F) :
    hsSq b S = hsSq b' S := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [hsSq_eq_hsSq_adjoint b c, hsSq_eq_hsSq_adjoint b' c]

end HS

/-! ## §C Trace of a positive operator over a Hilbert basis -/

section PosTrace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The diagonal sum `∑ᵢ re ⟪bᵢ, T bᵢ⟫ ∈ [0, ∞]` (negative parts truncated by `ofReal`; for
positive `T` every term is nonnegative, so nothing is truncated). -/
def traceIn (b : HilbertBasis ι 𝕜 E) (T : E →L[𝕜] E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (RCLike.re ⟪b i, T (b i)⟫_𝕜)

/-- For `T = S† S` the diagonal sum is the Hilbert–Schmidt sum of `S`. -/
theorem traceIn_adjoint_comp_self [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (b : HilbertBasis ι 𝕜 E) (S : E →L[𝕜] F) :
    traceIn b (ContinuousLinearMap.adjoint S ∘L S) = hsSq b S := by
  unfold traceIn hsSq
  congr 1; ext i
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq]

end PosTrace

section PosTraceComplex

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For a positive operator `T` on a complex Hilbert space, the diagonal sum equals the
Hilbert–Schmidt sum of its square root. -/
theorem traceIn_eq_hsSq_sqrt (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    traceIn b T = hsSq b (CFC.sqrt T) := by
  have h0 : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr hT
  have hsa : IsSelfAdjoint (CFC.sqrt T) := (CFC.sqrt_nonneg T).isSelfAdjoint
  have hT' : T = ContinuousLinearMap.adjoint (CFC.sqrt T) ∘L CFC.sqrt T := by
    rw [← ContinuousLinearMap.star_eq_adjoint, hsa.star_eq]
    exact (CFC.sqrt_mul_sqrt_self T h0).symm
  conv_lhs => rw [hT']
  exact traceIn_adjoint_comp_self b _

/-- **Basis independence of the trace of a positive operator.** -/
theorem traceIn_eq_of_basis {ι' : Type*} (b : HilbertBasis ι ℂ E) (b' : HilbertBasis ι' ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) : traceIn b T = traceIn b' T := by
  rw [traceIn_eq_hsSq_sqrt b hT, traceIn_eq_hsSq_sqrt b' hT, hsSq_eq_of_basis b b']

end PosTraceComplex

/-! ## §B Tensor Hilbert bases and the trace of the reduced density -/

section TensorBasis

open QuantumNLS.TensorCarrier

variable {𝕜 X Y ι κ : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]

/-- A closed, linearly closed property holding on a Hilbert basis holds everywhere. -/
theorem forall_of_hilbertBasis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (b : HilbertBasis ι 𝕜 E) {P : E → Prop} (hc : IsClosed {x | P x}) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (a : 𝕜) x, P x → P (a • x))
    (hb : ∀ i, P (b i)) (x : E) : P x := by
  have hspan : ∀ z ∈ Submodule.span 𝕜 (Set.range b), P z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨i, rfl⟩ := hz; exact hb i
    | zero => exact h0
    | add x y _ _ hx hy => exact hadd x y hx hy
    | smul a x _ hx => exact hsmul a x hx
  have hx : x ∈ closure (Submodule.span 𝕜 (Set.range b) : Set E) := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]; exact Submodule.mem_top
  exact closure_minimal (fun z hz => hspan z hz) hc hx

theorem htmul_zero_left (y : Y) : (htmul (0 : X) y : HilbertTensor 𝕜 X Y) = 0 := by
  simpa using htmul_smul_left (0 : 𝕜) (0 : X) y

theorem htmul_zero_right (x : X) : (htmul x (0 : Y) : HilbertTensor 𝕜 X Y) = 0 := by
  simpa using htmul_smul_right (0 : 𝕜) x (0 : Y)

theorem continuous_htmul_left (y : Y) : Continuous fun x : X => (htmul x y : HilbertTensor 𝕜 X Y) :=
  (UniformSpace.Completion.continuous_coe _).comp ((TensorProduct.mkL 𝕜 X Y).flip y).continuous

theorem continuous_htmul_right (x : X) :
    Continuous fun y : Y => (htmul x y : HilbertTensor 𝕜 X Y) :=
  (UniformSpace.Completion.continuous_coe _).comp ((TensorProduct.mkL 𝕜 X Y) x).continuous

/-- `{cᵢ ⊗ dⱼ}` is a Hilbert basis of `X ⊗̂ Y` whenever `c`, `d` are Hilbert bases. -/
def htmulBasis (c : HilbertBasis ι 𝕜 X) (d : HilbertBasis κ 𝕜 Y) :
    HilbertBasis (ι × κ) 𝕜 (HilbertTensor 𝕜 X Y) :=
  HilbertBasis.mk (v := fun p : ι × κ => (htmul (c p.1) (d p.2) : HilbertTensor 𝕜 X Y))
    (by
      classical
      rw [orthonormal_iff_ite]
      rintro ⟨i, j⟩ ⟨i', j'⟩
      rw [inner_htmul, orthonormal_iff_ite.mp c.orthonormal, orthonormal_iff_ite.mp d.orthonormal]
      by_cases hi : i = i' <;> by_cases hj : j = j' <;> simp [hi, hj])
    (by
      let W := (Submodule.span 𝕜 (Set.range fun p : ι × κ =>
        (htmul (c p.1) (d p.2) : HilbertTensor 𝕜 X Y))).topologicalClosure
      have hW : IsClosed (W : Set (HilbertTensor 𝕜 X Y)) := Submodule.isClosed_topologicalClosure _
      have key : ∀ (x : X) (y : Y), htmul x y ∈ W := by
        intro x
        refine forall_of_hilbertBasis c (P := fun x => ∀ y : Y, htmul x y ∈ W) ?_ ?_ ?_ ?_ ?_ x
        · simp only [Set.ofPred_forall]
          exact isClosed_iInter fun y => hW.preimage (continuous_htmul_left y)
        · intro y; rw [htmul_zero_left]; exact zero_mem _
        · intro x x' hx hx' y; rw [htmul_add_left]; exact add_mem (hx y) (hx' y)
        · intro a x hx y; rw [htmul_smul_left]; exact Submodule.smul_mem _ a (hx y)
        · intro i y
          refine forall_of_hilbertBasis d (P := fun y => htmul (c i) y ∈ W)
            (hW.preimage (continuous_htmul_right _)) ?_ ?_ ?_ ?_ y
          · rw [htmul_zero_right]; exact zero_mem _
          · intro y y' hy hy'; rw [htmul_add_right]; exact add_mem hy hy'
          · intro a y hy; rw [htmul_smul_right]; exact Submodule.smul_mem _ a hy
          · intro j
            exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i, j), rfl⟩)
      rw [← span_htmul_dense (𝕜 := 𝕜) (E := X) (F := Y)]
      refine Submodule.topologicalClosure_minimal _ ?_ hW
      rw [Submodule.span_le]
      rintro _ ⟨⟨x, y⟩, rfl⟩
      exact key x y)

@[simp] theorem htmulBasis_apply (c : HilbertBasis ι 𝕜 X) (d : HilbertBasis κ 𝕜 Y) (p : ι × κ) :
    htmulBasis c d p = htmul (c p.1) (d p.2) := by
  simp [htmulBasis, HilbertBasis.coe_mk]

end TensorBasis

section ReducedTrace

open QuantumNLS.TensorCarrier

variable {𝕜 X Y ι : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
  [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]

/-- `⟪1 ⊗ y, (⟨φ| ⊗̂ 1) ψ⟫ = ⟪φ ⊗ y, ψ⟫`. -/
theorem inner_htmul_one_contract (φ : X) (y : Y) (ψ : HilbertTensor 𝕜 X Y) :
    ⟪(htmul (1 : 𝕜) y : HilbertTensor 𝕜 𝕜 Y),
      htmap (InnerProductSpace.rankOne 𝕜 (1 : 𝕜) φ) (ContinuousLinearMap.id 𝕜 Y) ψ⟫_𝕜 =
      ⟪htmul φ y, ψ⟫_𝕜 := by
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_htmap, InnerProductSpace.adjoint_rankOne,
    ContinuousLinearMap.adjoint_id, htmap_htmul, InnerProductSpace.rankOne_apply,
    ContinuousLinearMap.id_apply]
  simp

/-- **Trace of the reduced density.** In every Hilbert basis `c` of `X`,
`∑ᵢ re ⟪cᵢ, γ_ψ cᵢ⟫ = ‖ψ‖²`. -/
theorem traceIn_reducedDensity (c : HilbertBasis ι 𝕜 X) (ψ : HilbertTensor 𝕜 X Y) :
    traceIn c (reducedDensity ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis 𝕜 Y
  let one : HilbertBasis Unit 𝕜 𝕜 := (OrthonormalBasis.singleton Unit 𝕜).toHilbertBasis
  have hone : ∀ u, one u = 1 := by
    intro u; simp [one, OrthonormalBasis.coe_toHilbertBasis, OrthonormalBasis.singleton_apply]
  have h1 : ∀ i, ENNReal.ofReal (RCLike.re ⟪c i, reducedDensity ψ (c i)⟫_𝕜) =
      ENNReal.ofReal (‖htmap (InnerProductSpace.rankOne 𝕜 (1 : 𝕜) (c i))
        (ContinuousLinearMap.id 𝕜 Y) ψ‖ ^ 2) := by
    intro i
    congr 1
    rw [← inner_conj_symm, inner_reducedDensity_self, RCLike.conj_ofReal, RCLike.ofReal_re]
  have h2 : ∀ i, ENNReal.ofReal (‖htmap (InnerProductSpace.rankOne 𝕜 (1 : 𝕜) (c i))
        (ContinuousLinearMap.id 𝕜 Y) ψ‖ ^ 2) =
      ∑' j, ENNReal.ofReal (‖⟪(htmul (c i) (d j) : HilbertTensor 𝕜 X Y), ψ⟫_𝕜‖ ^ 2) := by
    intro i
    rw [← tsum_ofReal_norm_inner_sq (htmulBasis one d), ENNReal.tsum_prod']
    simp only [htmulBasis_apply, hone, inner_htmul_one_contract]
    simp
  unfold traceIn
  simp_rw [h1, h2]
  rw [← ENNReal.tsum_prod, ← tsum_ofReal_norm_inner_sq (htmulBasis c d) ψ]
  simp

/-- **DEF-030, trace clause.** For `ψ ∈ E^{⊗̂(k+m)}`, the reduced density over the last `m`
factors has trace `‖ψ‖²` in every Hilbert basis; in particular trace one when `‖ψ‖ = 1`. -/
theorem traceIn_reducedDensityPower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (k m : ℕ) (c : HilbertBasis ι 𝕜 (HilbertTensorPower 𝕜 E k))
    (ψ : HilbertTensorPower 𝕜 E (k + m)) :
    traceIn c (reducedDensityPower k m ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [reducedDensityPower, traceIn_reducedDensity, LinearIsometryEquiv.norm_map]

theorem traceIn_reducedDensityPower_eq_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (k m : ℕ) (c : HilbertBasis ι 𝕜 (HilbertTensorPower 𝕜 E k))
    (ψ : HilbertTensorPower 𝕜 E (k + m)) (hψ : ‖ψ‖ = 1) :
    traceIn c (reducedDensityPower k m ψ) = 1 := by
  rw [traceIn_reducedDensityPower, hψ]
  simp

end ReducedTrace

/-! ## §D Trace norm `‖A‖₁ = Tr|A|` -/

section HSZero

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The Hilbert–Schmidt sum vanishes only for the zero operator. -/
theorem hsSq_eq_zero_iff (b : HilbertBasis ι 𝕜 E) (S : E →L[𝕜] F) : hsSq b S = 0 ↔ S = 0 := by
  constructor
  · intro h
    have hb : ∀ i, S (b i) = 0 := by
      intro i
      have hi := ENNReal.tsum_eq_zero.mp h i
      rw [ENNReal.ofReal_eq_zero] at hi
      have : ‖S (b i)‖ ^ 2 = 0 := le_antisymm hi (by positivity)
      simpa using this
    ext x
    exact forall_of_hilbertBasis b (P := fun x => S x = 0)
      (isClosed_eq S.continuous continuous_const) (map_zero S)
      (fun x y hx hy => by rw [map_add, hx, hy, add_zero])
      (fun a x hx => by rw [map_smul, hx, smul_zero]) hb x
  · rintro rfl
    simp [hsSq]

end HSZero

section TraceNorm

open QuantumNLS.TensorCarrier

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem isPositive_of_nonneg {T : E →L[ℂ] E} (h : 0 ≤ T) : T.IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp h

variable (E) in
/-- Index set of a fixed reference Hilbert basis (every Hilbert space has one). -/
def RefIndex : Set E := Classical.choose (exists_hilbertBasis ℂ E)

variable (E) in
/-- A fixed reference Hilbert basis.  Only used to give basis-free definitions; every statement
below is transported to an arbitrary basis by §C. -/
def refBasis : HilbertBasis (RefIndex E) ℂ E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))

/-- Trace of an operator on the positive cone, `Tr T = ∑ᵢ ⟪bᵢ, T bᵢ⟫ ∈ [0, ∞]`.  Its value is
basis-independent for positive `T` (`posTrace_eq`). -/
def posTrace (T : E →L[ℂ] E) : ℝ≥0∞ := traceIn (refBasis E) T

theorem posTrace_eq (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    posTrace T = traceIn b T :=
  traceIn_eq_of_basis _ _ hT

/-- Additivity of the trace on the positive cone. -/
theorem posTrace_add {S T : E →L[ℂ] E} (hS : S.IsPositive) (hT : T.IsPositive) :
    posTrace (S + T) = posTrace S + posTrace T := by
  unfold posTrace traceIn
  rw [← ENNReal.tsum_add]
  congr 1; ext i
  rw [ContinuousLinearMap.add_apply, inner_add_right, map_add,
    ENNReal.ofReal_add (hS.re_inner_nonneg_right _) (hT.re_inner_nonneg_right _)]

/-- **Trace norm** `‖A‖₁ = Tr|A| ∈ [0, ∞]`, `|A| = √(A†A)` (DEF-030). -/
def traceNorm (A : E →L[ℂ] E) : ℝ≥0∞ := posTrace (CFC.abs A)

/-- Trace class: finite trace norm. -/
def IsTraceClass (A : E →L[ℂ] E) : Prop := traceNorm A < ⊤

theorem traceNorm_eq (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E) :
    traceNorm A = traceIn b (CFC.abs A) :=
  posTrace_eq b (isPositive_of_nonneg (CFC.abs_nonneg A))

theorem traceNorm_eq_hsSq (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E) :
    traceNorm A = hsSq b (CFC.sqrt (CFC.abs A)) := by
  rw [traceNorm_eq b, traceIn_eq_hsSq_sqrt b (isPositive_of_nonneg (CFC.abs_nonneg A))]

theorem traceNorm_of_isPositive {T : E →L[ℂ] E} (hT : T.IsPositive) :
    traceNorm T = posTrace T := by
  rw [traceNorm, CFC.abs_of_nonneg T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)]

/-- Faithfulness: `‖A‖₁ = 0 ↔ A = 0`. -/
theorem traceNorm_eq_zero_iff (A : E →L[ℂ] E) : traceNorm A = 0 ↔ A = 0 := by
  rw [traceNorm_eq_hsSq (refBasis E), hsSq_eq_zero_iff, CFC.sqrt_eq_zero_iff _ (CFC.abs_nonneg A),
    CFC.abs_eq_zero_iff]

/-- Homogeneity: `‖c • A‖₁ = |c| ‖A‖₁`. -/
theorem traceNorm_smul (c : ℂ) (A : E →L[ℂ] E) :
    traceNorm (c • A) = ENNReal.ofReal ‖c‖ * traceNorm A := by
  rw [traceNorm, traceNorm, CFC.abs_smul, posTrace, posTrace, traceIn, traceIn,
    ← ENNReal.tsum_mul_left]
  congr 1; ext i
  rw [ContinuousLinearMap.smul_apply, ← ENNReal.ofReal_mul (norm_nonneg c)]
  congr 1
  rw [← Complex.coe_smul, inner_smul_right]
  simp

/-- **DEF-030 (trace norm of γ).** For a complex Hilbert space `E` and `ψ ∈ E^{⊗̂(k+m)}`,
`‖γ^{(k)}_ψ‖₁ = Tr γ^{(k)}_ψ = ‖ψ‖²`; in particular `γ^{(k)}_ψ` is trace class. -/
theorem traceNorm_reducedDensityPower (k m : ℕ) (ψ : HilbertTensorPower ℂ E (k + m)) :
    traceNorm (reducedDensityPower k m ψ) = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [traceNorm_of_isPositive (reducedDensityPower_isPositive k m ψ), posTrace,
    traceIn_reducedDensityPower]

theorem isTraceClass_reducedDensityPower (k m : ℕ) (ψ : HilbertTensorPower ℂ E (k + m)) :
    IsTraceClass (reducedDensityPower k m ψ) := by
  rw [IsTraceClass, traceNorm_reducedDensityPower]
  exact ENNReal.ofReal_lt_top

end TraceNorm

/-! ## §E Toolkit for the triangle inequality (no polar decomposition)

All functional calculus is done on `R = √|A|`, so that `A†A = |A|² = R⁴`; the regularisers used
below are globally continuous rational functions of `R`, so no spectral support facts are needed. -/

section Toolkit

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `R_A := √|A|`. -/
def rootAbs (A : E →L[ℂ] E) : E →L[ℂ] E := CFC.sqrt (CFC.abs A)

theorem rootAbs_nonneg (A : E →L[ℂ] E) : 0 ≤ rootAbs A := CFC.sqrt_nonneg _

theorem rootAbs_mul_self (A : E →L[ℂ] E) : rootAbs A * rootAbs A = CFC.abs A :=
  CFC.sqrt_mul_sqrt_self _ (CFC.abs_nonneg A)

theorem abs_eq_cfc_sq (A : E →L[ℂ] E) :
    CFC.abs A = cfc (fun t : ℝ => t * t) (rootAbs A) := by
  have hR : IsSelfAdjoint (rootAbs A) := (rootAbs_nonneg A).isSelfAdjoint
  rw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t) (rootAbs A), cfc_id' ℝ (rootAbs A),
    rootAbs_mul_self]

theorem star_cfc_rootAbs (A : E →L[ℂ] E) (f : ℝ → ℝ) :
    star (cfc f (rootAbs A)) = cfc f (rootAbs A) := by
  rw [← cfc_star]
  simp

/-- `(A f(R))† (A g(R)) = (f · t⁴ · g)(R)`. -/
theorem star_mul_cfc (A : E →L[ℂ] E) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    star (A * cfc f (rootAbs A)) * (A * cfc g (rootAbs A)) =
      cfc (fun t => f t * (t * t * (t * t)) * g t) (rootAbs A) := by
  have hR : IsSelfAdjoint (rootAbs A) := (rootAbs_nonneg A).isSelfAdjoint
  have h4 : star A * A = cfc (fun t : ℝ => t * t * (t * t)) (rootAbs A) := by
    rw [← CFC.abs_mul_abs, abs_eq_cfc_sq, ← cfc_mul (fun t : ℝ => t * t) (fun t : ℝ => t * t)]
  rw [star_mul, star_cfc_rootAbs]
  calc cfc f (rootAbs A) * star A * (A * cfc g (rootAbs A))
      = cfc f (rootAbs A) * (star A * A) * cfc g (rootAbs A) := by noncomm_ring
    _ = _ := by
      rw [h4, ← cfc_mul f (fun t : ℝ => t * t * (t * t)) (rootAbs A),
        ← cfc_mul (fun t => f t * (t * t * (t * t))) g (rootAbs A)]

/-- Operator-norm bound `‖A f(R)‖ ≤ c` from the scalar bound `|f t| t² ≤ c`. -/
theorem norm_mul_cfc_le (A : E →L[ℂ] E) (f : ℝ → ℝ) (hf : Continuous f) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t, |f t| * (t * t) ≤ c) : ‖A * cfc f (rootAbs A)‖ ≤ c := by
  have hsq : ‖A * cfc f (rootAbs A)‖ * ‖A * cfc f (rootAbs A)‖ ≤ c * c := by
    rw [← CStarRing.norm_star_mul_self, star_mul_cfc A f f hf hf]
    refine norm_cfc_le (mul_nonneg hc hc) fun t _ => ?_
    have h1 : ‖f t * (t * t * (t * t)) * f t‖ = (|f t| * (t * t)) * (|f t| * (t * t)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (mul_self_nonneg (t * t))]
      ring
    rw [h1]
    exact mul_le_mul (h t) (h t) (mul_nonneg (abs_nonneg _) (mul_self_nonneg t)) hc
  exact (mul_self_le_mul_self_iff (norm_nonneg _) hc).mpr hsq

theorem inner_mul_eq (Y Z : E →L[ℂ] E) (x y : E) :
    ⟪Y x, Z y⟫_ℂ = ⟪x, (star Y * Z) y⟫_ℂ := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

/-- Monotonicity of the diagonal sum along the Loewner order. -/
theorem traceIn_mono (b : HilbertBasis ι ℂ E) {S T : E →L[ℂ] E} (h : S ≤ T) :
    traceIn b S ≤ traceIn b T := by
  refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
  have := (ContinuousLinearMap.le_def.mp h).re_inner_nonneg_right (b i)
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, map_sub] at this
  linarith

/-- Left multiplication by a contraction does not increase the Hilbert–Schmidt sum. -/
theorem hsSq_comp_le (b : HilbertBasis ι ℂ E) {X : E →L[ℂ] E} (hX : ‖X‖ ≤ 1) (Y : E →L[ℂ] E) :
    hsSq b (X ∘L Y) ≤ hsSq b Y := by
  refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
  have h1 : ‖X (Y (b i))‖ ≤ ‖Y (b i)‖ :=
    (X.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hX (norm_nonneg (Y (b i))))
  rw [ContinuousLinearMap.comp_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- A finite partial sum of a finite Hilbert–Schmidt sum, in real form. -/
theorem sum_norm_sq_le (b : HilbertBasis ι ℂ E) (S : E →L[ℂ] E) (hS : hsSq b S ≠ ⊤)
    (s : Finset ι) : ∑ i ∈ s, ‖S (b i)‖ ^ 2 ≤ (hsSq b S).toReal := by
  rw [← ENNReal.ofReal_le_iff_le_toReal hS, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  exact ENNReal.sum_le_tsum s

theorem traceNorm_eq_hsSq_rootAbs (b : HilbertBasis ι ℂ E) (A : E →L[ℂ] E) :
    traceNorm A = hsSq b (rootAbs A) :=
  traceNorm_eq_hsSq b A

/-- **Upper bound (duality, one direction).** For a contraction `X`, a Hilbert basis `b` and a
finite `s`, `|∑_{i∈s} ⟪X bᵢ, A bᵢ⟫| ≤ ‖A‖₁`.  Proof: `A = Y R + A g(R)` with `R = √|A|`,
`Y = A h(R)`, `h(t) = t/(t²+δ)`, `g(t) = δ/(t²+δ)`; `‖A g(R)‖ ≤ δ`, `Y†Y ≤ |A|`, then
Cauchy–Schwarz and the Hilbert–Schmidt swap identity. -/
theorem norm_sum_inner_le_traceNorm (b : HilbertBasis ι ℂ E) (A X : E →L[ℂ] E) (hX : ‖X‖ ≤ 1)
    (hA : traceNorm A ≠ ⊤) (s : Finset ι) :
    ‖∑ i ∈ s, ⟪X (b i), A (b i)⟫_ℂ‖ ≤ (traceNorm A).toReal := by
  set T := (traceNorm A).toReal with hT
  set R := rootAbs A with hRdef
  have hR : IsSelfAdjoint R := (rootAbs_nonneg A).isSelfAdjoint
  have hTn : 0 ≤ T := ENNReal.toReal_nonneg
  have hHS : hsSq b R = traceNorm A := (traceNorm_eq_hsSq_rootAbs b A).symm
  have hRsum : ∑ i ∈ s, ‖R (b i)‖ ^ 2 ≤ T := by
    have := sum_norm_sq_le b R (by rw [hHS]; exact hA) s
    rwa [hHS] at this
  have hbn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hXb : ∀ i, ‖X (b i)‖ ≤ 1 := fun i =>
    (X.le_opNorm _).trans (by rw [hbn, mul_one]; exact hX)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set δ' : ℝ := δ / (s.card + 1) with hδ'def
  have hδ' : 0 < δ' := by positivity
  have hden : ∀ t : ℝ, 0 < t * t + δ' := fun t => add_pos_of_nonneg_of_pos (mul_self_nonneg t) hδ'
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℝ, h = fun t => t / (t * t + δ') := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun t => δ' / (t * t + δ') := ⟨_, rfl⟩
  have hcont : Continuous h := by
    rw [hh]; exact continuous_id.div (by fun_prop) (fun t => (hden t).ne')
  have gcont : Continuous g := by
    rw [hg]; exact continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  set Y := A * cfc h R with hYdef
  have hdecomp : A = Y * R + A * cfc g R := by
    have hRid : cfc (fun t : ℝ => t) R = R := cfc_id' ℝ R
    have e1 : Y * R = A * cfc (fun t => h t * t) R := by
      rw [hYdef, mul_assoc, cfc_mul h (fun t : ℝ => t) R, hRid]
    have e2 : (fun t => h t * t + g t) = fun _ : ℝ => (1 : ℝ) := by
      funext t
      rw [hh, hg]
      simp only
      rw [div_mul_eq_mul_div, ← add_div, div_self (hden t).ne']
    rw [e1, ← mul_add, ← cfc_add (a := R) (fun t => h t * t) g, e2, cfc_const_one ℝ R, mul_one]
  have hgnorm : ‖A * cfc g R‖ ≤ δ' := by
    refine norm_mul_cfc_le A g gcont hδ'.le fun t => ?_
    rw [hg]
    simp only
    rw [abs_of_pos (div_pos hδ' (hden t)), div_mul_eq_mul_div, div_le_iff₀ (hden t)]
    nlinarith [mul_self_nonneg t]
  have hle : cfc (fun t => h t * (t * t * (t * t)) * h t) R ≤ CFC.abs A := by
    rw [abs_eq_cfc_sq]
    refine cfc_mono (fun t _ => ?_) ((hcont.mul (by fun_prop)).mul hcont).continuousOn
      (by fun_prop)
    have hD := hden t
    have hq0 : 0 ≤ t * t / (t * t + δ') := div_nonneg (mul_self_nonneg t) hD.le
    have hq1 : t * t / (t * t + δ') ≤ 1 := (div_le_one hD).mpr (by linarith)
    have e : h t * (t * t * (t * t)) * h t = (t * t) * ((t * t / (t * t + δ')) *
        (t * t / (t * t + δ'))) := by
      rw [hh]; simp only; field_simp
    rw [e]
    have : (t * t / (t * t + δ')) * (t * t / (t * t + δ')) ≤ 1 := by nlinarith
    nlinarith [mul_self_nonneg t]
  have hHSY : hsSq b Y ≤ traceNorm A := by
    rw [← traceIn_adjoint_comp_self b Y, traceNorm_eq b A]
    have e : ContinuousLinearMap.adjoint Y ∘L Y = star Y * Y := by
      rw [ContinuousLinearMap.star_eq_adjoint]; rfl
    rw [e, hYdef, star_mul_cfc A h h hcont hcont]
    exact traceIn_mono b hle
  have hswap : hsSq b (star Y * X) ≤ traceNorm A := by
    rw [hsSq_eq_hsSq_adjoint b b]
    have e : ContinuousLinearMap.adjoint (star Y * X) = star X ∘L Y := by
      rw [← ContinuousLinearMap.star_eq_adjoint, star_mul, star_star]; rfl
    rw [e]
    exact (hsSq_comp_le b (by rwa [norm_star]) Y).trans hHSY
  have hYX : ∑ i ∈ s, ‖(star Y * X) (b i)‖ ^ 2 ≤ T :=
    (sum_norm_sq_le b (star Y * X) (ne_top_of_le_ne_top hA hswap) s).trans
      (ENNReal.toReal_mono hA hswap)
  have hsplit : ∀ i, ⟪X (b i), A (b i)⟫_ℂ =
      ⟪(star Y * X) (b i), R (b i)⟫_ℂ + ⟪X (b i), (A * cfc g R) (b i)⟫_ℂ := by
    intro i
    conv_lhs => rw [hdecomp]
    rw [ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.mul_apply Y R,
      ContinuousLinearMap.mul_apply (star Y) X, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left]
  have hA1 : ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (b i)⟫_ℂ‖ ≤ T := by
    have h1 : ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (b i)⟫_ℂ‖ ≤
        ∑ i ∈ s, ‖(star Y * X) (b i)‖ * ‖R (b i)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_inner_le_norm _ _)
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖(star Y * X) (b i)‖)
      (fun i => ‖R (b i)‖)
    have h3 : 0 ≤ ∑ i ∈ s, ‖(star Y * X) (b i)‖ * ‖R (b i)‖ :=
      Finset.sum_nonneg fun i _ => by positivity
    have h4 : (∑ i ∈ s, ‖(star Y * X) (b i)‖ * ‖R (b i)‖) ^ 2 ≤ T * T :=
      h2.trans (mul_le_mul hYX hRsum (Finset.sum_nonneg fun i _ => by positivity) hTn)
    nlinarith
  have hA2 : ‖∑ i ∈ s, ⟪X (b i), (A * cfc g R) (b i)⟫_ℂ‖ ≤ s.card * δ' := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ i ∈ s, ‖⟪X (b i), (A * cfc g R) (b i)⟫_ℂ‖ ≤ δ' := by
      intro i _
      refine (norm_inner_le_norm _ _).trans ?_
      have hb2 : ‖(A * cfc g R) (b i)‖ ≤ δ' :=
        ((A * cfc g R).le_opNorm _).trans (by rw [hbn, mul_one]; exact hgnorm)
      nlinarith [hXb i, norm_nonneg (X (b i)), norm_nonneg ((A * cfc g R) (b i))]
    calc ∑ i ∈ s, ‖⟪X (b i), (A * cfc g R) (b i)⟫_ℂ‖ ≤ ∑ _i ∈ s, δ' := Finset.sum_le_sum this
      _ = s.card * δ' := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (s.card : ℝ) * δ' ≤ δ := by
    have hc : (0 : ℝ) < s.card + 1 := by
      have := Nat.cast_nonneg (α := ℝ) s.card; linarith
    have e : δ' * ((s.card : ℝ) + 1) = δ := div_mul_cancel₀ δ hc.ne'
    nlinarith
  calc ‖∑ i ∈ s, ⟪X (b i), A (b i)⟫_ℂ‖
      = ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (b i)⟫_ℂ +
          ∑ i ∈ s, ⟪X (b i), (A * cfc g R) (b i)⟫_ℂ‖ := by
        rw [← Finset.sum_add_distrib]; exact congrArg _ (Finset.sum_congr rfl fun i _ => hsplit i)
    _ ≤ ‖∑ i ∈ s, ⟪(star Y * X) (b i), R (b i)⟫_ℂ‖ +
          ‖∑ i ∈ s, ⟪X (b i), (A * cfc g R) (b i)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ T + δ := by linarith

/-- **Triangle inequality for the trace norm**: `‖A + B‖₁ ≤ ‖A‖₁ + ‖B‖₁`.
Lower bound for `C = A + B`: with `R = √|C|` and the contraction `X = C (R² + ε)⁻¹`,
`⟪bᵢ, |C| bᵢ⟫ ≤ re ⟪X bᵢ, C bᵢ⟫ + ε`; then split `C = A + B` and apply the upper bound. -/
theorem traceNorm_add_le (A B : E →L[ℂ] E) : traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  by_cases hA : traceNorm A = ⊤
  · simp [hA]
  by_cases hB : traceNorm B = ⊤
  · simp [hB]
  set C := A + B with hCdef
  set b := refBasis E
  have hCpos : (CFC.abs C).IsPositive := isPositive_of_nonneg (CFC.abs_nonneg C)
  rw [traceNorm_eq b C, traceIn, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hCpos.re_inner_nonneg_right (b i)),
    ← ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨hA, hB⟩), ENNReal.toReal_add hA hB]
  apply ENNReal.ofReal_le_ofReal
  have hbn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set ε' : ℝ := ε / (s.card + 1) with hε'def
  have hε' : 0 < ε' := by
    have hc : (0 : ℝ) < s.card + 1 := by
      have := Nat.cast_nonneg (α := ℝ) s.card; linarith
    exact div_pos hε hc
  have hden : ∀ t : ℝ, 0 < t * t + ε' := fun t => add_pos_of_nonneg_of_pos (mul_self_nonneg t) hε'
  set R := rootAbs C with hRdef
  have hR : IsSelfAdjoint R := (rootAbs_nonneg C).isSelfAdjoint
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, k = fun t => 1 / (t * t + ε') := ⟨_, rfl⟩
  have kcont : Continuous k := by
    rw [hk]; exact continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  set X := C * cfc k R with hXdef
  have hXnorm : ‖X‖ ≤ 1 := by
    refine norm_mul_cfc_le C k kcont zero_le_one fun t => ?_
    rw [hk]; simp only
    rw [abs_of_pos (div_pos one_pos (hden t)), one_div_mul_eq_div, div_le_one (hden t)]
    linarith
  have hXC : star X * C = cfc (fun t => k t * (t * t * (t * t)) * 1) R := by
    have hC1 : C = C * cfc (fun _ : ℝ => (1 : ℝ)) R := by rw [cfc_const_one ℝ R, mul_one]
    conv_lhs => rw [hC1]
    rw [hXdef, star_mul_cfc C k (fun _ => 1) kcont continuous_const]
  have hD : ‖CFC.abs C - star X * C‖ ≤ ε' := by
    rw [hXC, abs_eq_cfc_sq, ← cfc_sub (a := R) (fun t : ℝ => t * t)
      (fun t => k t * (t * t * (t * t)) * 1) (by fun_prop)
      ((kcont.mul (by fun_prop)).mul continuous_const).continuousOn]
    refine norm_cfc_le hε'.le fun t _ => ?_
    have e : t * t - k t * (t * t * (t * t)) * 1 = ε' * (t * t / (t * t + ε')) := by
      rw [hk]; simp only; field_simp; ring
    rw [e, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε'.le
      (div_nonneg (mul_self_nonneg t) (hden t).le))]
    have : t * t / (t * t + ε') ≤ 1 := (div_le_one (hden t)).mpr (by linarith)
    nlinarith
  have key : ∀ i, RCLike.re ⟪b i, CFC.abs C (b i)⟫_ℂ ≤ RCLike.re ⟪X (b i), C (b i)⟫_ℂ + ε' := by
    intro i
    have h1 : RCLike.re ⟪b i, CFC.abs C (b i)⟫_ℂ - RCLike.re ⟪X (b i), C (b i)⟫_ℂ =
        RCLike.re ⟪b i, (CFC.abs C - star X * C) (b i)⟫_ℂ := by
      rw [inner_mul_eq, ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
    have h2 : RCLike.re ⟪b i, (CFC.abs C - star X * C) (b i)⟫_ℂ ≤ ε' := by
      refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      rw [hbn, one_mul]
      exact ((CFC.abs C - star X * C).le_opNorm _).trans (by rw [hbn, mul_one]; exact hD)
    linarith
  have hsplit : ∑ i ∈ s, RCLike.re ⟪X (b i), C (b i)⟫_ℂ =
      RCLike.re (∑ i ∈ s, ⟪X (b i), A (b i)⟫_ℂ) + RCLike.re (∑ i ∈ s, ⟪X (b i), B (b i)⟫_ℂ) := by
    rw [map_sum, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hCdef, ContinuousLinearMap.add_apply, inner_add_right, map_add]
  have hUA := norm_sum_inner_le_traceNorm b A X hXnorm hA s
  have hUB := norm_sum_inner_le_traceNorm b B X hXnorm hB s
  have hcard : (s.card : ℝ) * ε' ≤ ε := by
    have hc : (0 : ℝ) < s.card + 1 := by
      have := Nat.cast_nonneg (α := ℝ) s.card; linarith
    have e : ε' * ((s.card : ℝ) + 1) = ε := div_mul_cancel₀ ε hc.ne'
    nlinarith
  calc ∑ i ∈ s, RCLike.re ⟪b i, CFC.abs C (b i)⟫_ℂ
      ≤ ∑ i ∈ s, (RCLike.re ⟪X (b i), C (b i)⟫_ℂ + ε') := Finset.sum_le_sum fun i _ => key i
    _ = RCLike.re (∑ i ∈ s, ⟪X (b i), A (b i)⟫_ℂ) +
          RCLike.re (∑ i ∈ s, ⟪X (b i), B (b i)⟫_ℂ) + s.card * ε' := by
        rw [Finset.sum_add_distrib, hsplit, Finset.sum_const, nsmul_eq_mul]
    _ ≤ (traceNorm A).toReal + (traceNorm B).toReal + ε := by
        have := RCLike.re_le_norm (∑ i ∈ s, ⟪X (b i), A (b i)⟫_ℂ)
        have := RCLike.re_le_norm (∑ i ∈ s, ⟪X (b i), B (b i)⟫_ℂ)
        linarith

/-- Trace-class operators are closed under addition. -/
theorem IsTraceClass.add {A B : E →L[ℂ] E} (hA : IsTraceClass A) (hB : IsTraceClass B) :
    IsTraceClass (A + B) :=
  lt_of_le_of_lt (traceNorm_add_le A B) (ENNReal.add_lt_top.mpr ⟨hA, hB⟩)

end Toolkit

/-! ## §F Duality bound; stability of reduced densities; product states -/

section Duality

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- For every `ε > 0` there is a contraction `X` with `re⟪x, |C| x⟫ ≤ re⟪X x, C x⟫ + ε‖x‖²`. -/
theorem exists_contraction_abs_le (C : E →L[ℂ] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ X : E →L[ℂ] E, ‖X‖ ≤ 1 ∧ ∀ x : E,
      RCLike.re ⟪x, CFC.abs C x⟫_ℂ ≤ RCLike.re ⟪X x, C x⟫_ℂ + ε * ‖x‖ ^ 2 := by
  have hden : ∀ t : ℝ, 0 < t * t + ε := fun t => add_pos_of_nonneg_of_pos (mul_self_nonneg t) hε
  set R := rootAbs C with hRdef
  have hR : IsSelfAdjoint R := (rootAbs_nonneg C).isSelfAdjoint
  obtain ⟨k, hk⟩ : ∃ k : ℝ → ℝ, k = fun t => 1 / (t * t + ε) := ⟨_, rfl⟩
  have kcont : Continuous k := by
    rw [hk]; exact continuous_const.div (by fun_prop) (fun t => (hden t).ne')
  refine ⟨C * cfc k R, ?_, ?_⟩
  · refine norm_mul_cfc_le C k kcont zero_le_one fun t => ?_
    rw [hk]; simp only
    rw [abs_of_pos (div_pos one_pos (hden t)), one_div_mul_eq_div, div_le_one (hden t)]
    linarith
  · have hXC : star (C * cfc k R) * C = cfc (fun t => k t * (t * t * (t * t)) * 1) R := by
      have hC1 : star (C * cfc k R) * C =
          star (C * cfc k R) * (C * cfc (fun _ : ℝ => (1 : ℝ)) R) := by
        rw [cfc_const_one ℝ R, mul_one]
      rw [hC1, star_mul_cfc C k (fun _ => 1) kcont continuous_const]
    have hD : ‖CFC.abs C - star (C * cfc k R) * C‖ ≤ ε := by
      rw [hXC, abs_eq_cfc_sq, ← cfc_sub (a := R) (fun t : ℝ => t * t)
        (fun t => k t * (t * t * (t * t)) * 1) (by fun_prop)
        ((kcont.mul (by fun_prop)).mul continuous_const).continuousOn]
      refine norm_cfc_le hε.le fun t _ => ?_
      have e : t * t - k t * (t * t * (t * t)) * 1 = ε * (t * t / (t * t + ε)) := by
        rw [hk]; simp only; field_simp; ring
      rw [e, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hε.le
        (div_nonneg (mul_self_nonneg t) (hden t).le))]
      have : t * t / (t * t + ε) ≤ 1 := (div_le_one (hden t)).mpr (by linarith)
      nlinarith
    intro x
    have h1 : RCLike.re ⟪x, CFC.abs C x⟫_ℂ - RCLike.re ⟪(C * cfc k R) x, C x⟫_ℂ =
        RCLike.re ⟪x, (CFC.abs C - star (C * cfc k R) * C) x⟫_ℂ := by
      rw [inner_mul_eq, ContinuousLinearMap.sub_apply, inner_sub_right, map_sub]
    have h2 : RCLike.re ⟪x, (CFC.abs C - star (C * cfc k R) * C) x⟫_ℂ ≤ ε * ‖x‖ ^ 2 := by
      refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
      have := (CFC.abs C - star (C * cfc k R) * C).le_opNorm x
      have h3 : ‖(CFC.abs C - star (C * cfc k R) * C) x‖ ≤ ε * ‖x‖ :=
        this.trans (mul_le_mul_of_nonneg_right hD (norm_nonneg x))
      nlinarith [norm_nonneg x]
    linarith

/-- **Duality bound.** If `re ∑_{i∈s} ⟪X bᵢ, C bᵢ⟫ ≤ c` for every contraction `X` and every
finite `s`, then `‖C‖₁ ≤ c`. -/
theorem traceNorm_le_of_forall (b : HilbertBasis ι ℂ E) (C : E →L[ℂ] E) {c : ℝ}
    (h : ∀ X : E →L[ℂ] E, ‖X‖ ≤ 1 → ∀ s : Finset ι,
      RCLike.re (∑ i ∈ s, ⟪X (b i), C (b i)⟫_ℂ) ≤ c) :
    traceNorm C ≤ ENNReal.ofReal c := by
  have hCpos : (CFC.abs C).IsPositive := isPositive_of_nonneg (CFC.abs_nonneg C)
  have hbn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  rw [traceNorm_eq b C, traceIn, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hCpos.re_inner_nonneg_right (b i))]
  apply ENNReal.ofReal_le_ofReal
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : (0 : ℝ) < s.card + 1 := by
    have := Nat.cast_nonneg (α := ℝ) s.card; linarith
  obtain ⟨X, hX, hXC⟩ := exists_contraction_abs_le C (div_pos hε hc)
  have hcard : (s.card : ℝ) * (ε / (s.card + 1)) ≤ ε := by
    have e : ε / (s.card + 1) * ((s.card : ℝ) + 1) = ε := div_mul_cancel₀ ε hc.ne'
    nlinarith [div_pos hε hc]
  calc ∑ i ∈ s, RCLike.re ⟪b i, CFC.abs C (b i)⟫_ℂ
      ≤ ∑ i ∈ s, (RCLike.re ⟪X (b i), C (b i)⟫_ℂ + ε / (s.card + 1)) :=
        Finset.sum_le_sum fun i _ => by simpa [hbn] using hXC (b i)
    _ = RCLike.re (∑ i ∈ s, ⟪X (b i), C (b i)⟫_ℂ) + s.card * (ε / (s.card + 1)) := by
        rw [Finset.sum_add_distrib, map_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ c + ε := by linarith [h X hX s]

/-- The finite "partial projection" `x ↦ ∑_{i∈s} ⟪bᵢ, x⟫ bᵢ` is a contraction (Bessel). -/
theorem norm_sum_inner_smul_le (b : HilbertBasis ι ℂ E) (s : Finset ι) (x : E) :
    ‖∑ i ∈ s, ⟪b i, x⟫_ℂ • b i‖ ≤ ‖x‖ := by
  set y := ∑ i ∈ s, ⟪b i, x⟫_ℂ • b i with hy
  have hyy : ⟪y, y⟫_ℂ = ⟪y, x⟫_ℂ := by
    rw [hy, sum_inner, sum_inner]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [inner_smul_left, inner_smul_left, ← hy,
      b.orthonormal.inner_right_sum (fun j => ⟪b j, x⟫_ℂ) hi]
  have h1 : ‖y‖ ^ 2 ≤ ‖y‖ * ‖x‖ := by
    have : (‖y‖ ^ 2 : ℝ) = RCLike.re ⟪y, x⟫_ℂ := by
      rw [← hyy, inner_self_eq_norm_sq]
    rw [this]
    exact (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  nlinarith [norm_nonneg y, norm_nonneg x]

/-- **Operator norm ≤ trace norm**: `‖A‖ ≤ ‖A‖₁`. -/
theorem norm_le_traceNorm (A : E →L[ℂ] E) : ENNReal.ofReal ‖A‖ ≤ traceNorm A := by
  by_cases hA : traceNorm A = ⊤
  · simp [hA]
  rw [← ENNReal.ofReal_toReal hA]
  apply ENNReal.ofReal_le_ofReal
  have key : ∀ e : E, ‖e‖ = 1 → ‖A e‖ ≤ (traceNorm A).toReal := by
    intro e he
    classical
    have hs : Orthonormal ℂ ((↑) : ({e} : Set E) → E) := by
      rw [orthonormal_subtype_iff_ite]
      intro v hv w hw
      rw [Set.mem_singleton_iff] at hv hw
      subst hv; subst hw
      simp [inner_self_eq_norm_sq_to_K, he]
    obtain ⟨w, b, hsw, hb⟩ := hs.exists_hilbertBasis_extension
    let i₀ : w := ⟨e, hsw (Set.mem_singleton e)⟩
    have hbi : b i₀ = e := by rw [hb]
    by_cases hAe : A e = 0
    · rw [hAe, norm_zero]; exact ENNReal.toReal_nonneg
    have hn : 0 < ‖A e‖ := norm_pos_iff.mpr hAe
    set Xop : E →L[ℂ] E := ((‖A e‖⁻¹ : ℝ) : ℂ) • InnerProductSpace.rankOne ℂ (A e) e with hXop
    have hX : ‖Xop‖ ≤ 1 := by
      rw [hXop, norm_smul, InnerProductSpace.norm_rankOne, he, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
    have h := norm_sum_inner_le_traceNorm b A Xop hX hA {i₀}
    rw [Finset.sum_singleton, hbi] at h
    have hval : ⟪Xop e, A e⟫_ℂ = ((‖A e‖ : ℝ) : ℂ) := by
      rw [hXop, ContinuousLinearMap.smul_apply, InnerProductSpace.rankOne_apply,
        inner_self_eq_norm_sq_to_K, he, inner_smul_left, inner_smul_left,
        inner_self_eq_norm_sq_to_K]
      simp only [one_pow, map_one, one_mul]
      have hn' : ((‖A e‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      try simp only [Complex.conj_ofReal]
      push_cast
      field_simp
      rfl
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] at h
    exact h
  refine ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set e : E := ((‖x‖⁻¹ : ℝ) : ℂ) • x with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hxn,
      inv_mul_cancel₀ hxn.ne']
  have hxe : x = ((‖x‖ : ℝ) : ℂ) • e := by
    rw [he_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hxn.ne', Complex.ofReal_one,
      one_smul]
  have hAx : ‖A x‖ = ‖A e‖ * ‖x‖ := by
    conv_lhs => rw [hxe]
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxn, mul_comm]
  rw [hAx]
  exact mul_le_mul_of_nonneg_right (key e he) hxn.le

end Duality

section Stability

open QuantumNLS.TensorCarrier

variable {X Y ι : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

theorem htmap_sum_left {κ : Type*} (t : Finset κ) (T : κ → X →L[ℂ] X) :
    htmap (∑ j ∈ t, T j) (ContinuousLinearMap.id ℂ Y) =
      ∑ j ∈ t, htmap (T j) (ContinuousLinearMap.id ℂ Y) := by
  calc htmap (∑ j ∈ t, T j) (ContinuousLinearMap.id ℂ Y) = ampliate ℂ X Y (∑ j ∈ t, T j) := rfl
    _ = ∑ j ∈ t, ampliate ℂ X Y (T j) := map_sum _ _ _
    _ = ∑ j ∈ t, htmap (T j) (ContinuousLinearMap.id ℂ Y) := rfl

/-- **Stability of reduced densities (DEF-028 → DEF-030).**
`‖γ_ψ − γ_φ‖₁ ≤ ‖ψ − φ‖ (‖ψ‖ + ‖φ‖)`. -/
theorem traceNorm_reducedDensity_sub_le (ψ φ : HilbertTensor ℂ X Y) :
    traceNorm (reducedDensity ψ - reducedDensity φ) ≤
      ENNReal.ofReal (‖ψ - φ‖ * (‖ψ‖ + ‖φ‖)) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ X
  refine traceNorm_le_of_forall b _ fun Xop hX s => ?_
  set M : X →L[ℂ] X := ∑ i ∈ s, InnerProductSpace.rankOne ℂ (Xop (b i)) (b i) with hM
  have hMnorm : ‖M‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have e : M x = Xop (∑ i ∈ s, ⟪b i, x⟫_ℂ • b i) := by
      rw [hM, ContinuousLinearMap.sum_apply, map_sum]
      simp [InnerProductSpace.rankOne_apply, map_smul]
    rw [e, one_mul]
    exact (Xop.le_opNorm _).trans ((mul_le_mul hX (norm_sum_inner_smul_le b s x)
      (norm_nonneg _) zero_le_one).trans (by rw [one_mul]))
  set Z := htmap M (ContinuousLinearMap.id ℂ Y) with hZ
  have hZnorm : ‖Z‖ ≤ 1 :=
    (norm_htmap_le _ _).trans (by
      have := ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := Y)
      nlinarith [norm_nonneg M, norm_nonneg (ContinuousLinearMap.id ℂ Y)])
  have hsum : ∀ χ : HilbertTensor ℂ X Y,
      ∑ i ∈ s, ⟪Xop (b i), reducedDensity χ (b i)⟫_ℂ = (starRingEnd ℂ) ⟪χ, Z χ⟫_ℂ := by
    intro χ
    have e1 : ∀ i, ⟪Xop (b i), reducedDensity χ (b i)⟫_ℂ = (starRingEnd ℂ)
        ⟪χ, htmap (InnerProductSpace.rankOne ℂ (Xop (b i)) (b i))
          (ContinuousLinearMap.id ℂ Y) χ⟫_ℂ := by
      intro i
      rw [← inner_reducedDensity_left, inner_conj_symm]
    simp_rw [e1]
    rw [← map_sum, ← inner_sum, ← ContinuousLinearMap.sum_apply, ← htmap_sum_left, ← hM]
  have hdiff : ∑ i ∈ s, ⟪Xop (b i), (reducedDensity ψ - reducedDensity φ) (b i)⟫_ℂ =
      (starRingEnd ℂ) (⟪ψ - φ, Z ψ⟫_ℂ + ⟪φ, Z (ψ - φ)⟫_ℂ) := by
    simp_rw [ContinuousLinearMap.sub_apply, inner_sub_right]
    rw [Finset.sum_sub_distrib, hsum, hsum, ← map_sub]
    congr 1
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  rw [hdiff]
  refine (RCLike.re_le_norm _).trans ?_
  rw [RCLike.norm_conj]
  refine (norm_add_le _ _).trans ?_
  have hZψ : ‖Z ψ‖ ≤ ‖ψ‖ := (Z.le_opNorm ψ).trans (by nlinarith [norm_nonneg ψ])
  have hZd : ‖Z (ψ - φ)‖ ≤ ‖ψ - φ‖ :=
    (Z.le_opNorm _).trans (by nlinarith [norm_nonneg (ψ - φ)])
  have a1 := norm_inner_le_norm (𝕜 := ℂ) (ψ - φ) (Z ψ)
  have a2 := norm_inner_le_norm (𝕜 := ℂ) φ (Z (ψ - φ))
  nlinarith [norm_nonneg (ψ - φ), norm_nonneg φ, norm_nonneg (Z ψ), norm_nonneg ψ]

end Stability

section ProductState

open QuantumNLS.TensorCarrier

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Reduced density of an elementary tensor: `γ_{a⊗c} = ‖c‖² |a⟩⟨a|`. -/
theorem reducedDensity_htmul {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [CompleteSpace Y]
    (a : X) (c : Y) :
    reducedDensity (htmul a c : HilbertTensor 𝕜 X Y) =
      ((‖c‖ ^ 2 : ℝ) : 𝕜) • InnerProductSpace.rankOne 𝕜 a a := by
  ext φ
  refine ext_inner_right 𝕜 fun φ' => ?_
  rw [inner_reducedDensity_htmul, inner_self_eq_norm_sq_to_K, ContinuousLinearMap.smul_apply,
    inner_smul_left, InnerProductSpace.rankOne_apply, inner_smul_left, inner_conj_symm,
    RCLike.conj_ofReal]
  push_cast
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- `u^{⊗(k+m)} ↦ u^{⊗k} ⊗ u^{⊗m}` under the splitting isometry. -/
theorem splitIsometry_htpow (k m : ℕ) (u : E) :
    splitIsometry k m (htpow (k + m) u : HilbertTensorPower 𝕜 E (k + m)) =
      htmul (htpow k u : HilbertTensorPower 𝕜 E k) (htpow m u : HilbertTensorPower 𝕜 E m) := by
  have h : (fun _ : Fin (k + m) => u) = Fin.append (fun _ : Fin k => u) (fun _ : Fin m => u) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
    · rw [Fin.append_right]
  unfold htpow
  rw [h, splitIsometry_ptprod_append]

/-- **Product states.** `γ^{(k)}(u^{⊗(k+m)}) = ‖u‖^{2m} |u^{⊗k}⟩⟨u^{⊗k}|`. -/
theorem reducedDensityPower_htpow (k m : ℕ) (u : E) :
    reducedDensityPower k m (htpow (k + m) u : HilbertTensorPower 𝕜 E (k + m)) =
      ((‖u‖ ^ (2 * m) : ℝ) : 𝕜) •
        InnerProductSpace.rankOne 𝕜 (htpow k u : HilbertTensorPower 𝕜 E k) (htpow k u) := by
  rw [reducedDensityPower, splitIsometry_htpow, reducedDensity_htmul, norm_htpow, ← pow_mul,
    mul_comm m 2]

end ProductState

section Correspondence

open QuantumNLS.TensorCarrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **DEF-028 → DEF-030 transfer.** For a unit vector `u` and any `ψ ∈ E^{⊗̂(k+m)}`,
`‖γ^{(k)}_ψ − |u^{⊗k}⟩⟨u^{⊗k}|‖₁ ≤ ‖ψ − u^{⊗(k+m)}‖ (‖ψ‖ + 1)`.  Hence norm-close preparations
(`‖ψ_N − u^{⊗N}‖ → 0`, `‖ψ_N‖ = 1`) have reduced densities converging in trace norm to the
pure product state, for each fixed `k`. -/
theorem traceNorm_reducedDensityPower_sub_product_le (k m : ℕ) (u : E) (hu : ‖u‖ = 1)
    (ψ : HilbertTensorPower ℂ E (k + m)) :
    traceNorm (reducedDensityPower k m ψ -
        InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ E k) (htpow k u)) ≤
      ENNReal.ofReal (‖ψ - htpow (k + m) u‖ * (‖ψ‖ + 1)) := by
  have h := traceNorm_reducedDensity_sub_le (splitIsometry k m ψ)
    (splitIsometry k m (htpow (k + m) u : HilbertTensorPower ℂ E (k + m)))
  have hprod : reducedDensity (splitIsometry k m (htpow (k + m) u :
      HilbertTensorPower ℂ E (k + m))) =
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ E k) (htpow k u) := by
    have := reducedDensityPower_htpow (𝕜 := ℂ) k m u
    rw [reducedDensityPower, hu, one_pow] at this
    rw [this]
    simp
  rw [hprod, ← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, norm_htpow, hu, one_pow] at h
  exact h

end Correspondence

end QuantumNLS.TraceClass

#print axioms QuantumNLS.TraceClass.hsSq_eq_of_basis
#print axioms QuantumNLS.TraceClass.traceIn_eq_of_basis
#print axioms QuantumNLS.TraceClass.htmulBasis
#print axioms QuantumNLS.TraceClass.traceIn_reducedDensity
#print axioms QuantumNLS.TraceClass.traceIn_reducedDensityPower_eq_one
#print axioms QuantumNLS.TraceClass.hsSq_eq_zero_iff
#print axioms QuantumNLS.TraceClass.posTrace_add
#print axioms QuantumNLS.TraceClass.traceNorm_eq_zero_iff
#print axioms QuantumNLS.TraceClass.traceNorm_smul
#print axioms QuantumNLS.TraceClass.traceNorm_reducedDensityPower
#print axioms QuantumNLS.TraceClass.isTraceClass_reducedDensityPower
#print axioms QuantumNLS.TraceClass.norm_sum_inner_le_traceNorm
#print axioms QuantumNLS.TraceClass.traceNorm_add_le
#print axioms QuantumNLS.TraceClass.IsTraceClass.add
#print axioms QuantumNLS.TraceClass.traceNorm_le_of_forall
#print axioms QuantumNLS.TraceClass.traceNorm_reducedDensity_sub_le
#print axioms QuantumNLS.TraceClass.reducedDensityPower_htpow
#print axioms QuantumNLS.TraceClass.traceNorm_reducedDensityPower_sub_product_le
#print axioms QuantumNLS.TraceClass.norm_le_traceNorm
