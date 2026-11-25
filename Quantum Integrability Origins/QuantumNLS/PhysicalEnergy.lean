import QuantumNLS.OccupationUnitary
import QuantumNLS.EnergyMultiplier

/-!
# The physical carrier of the energy multiplier: `L²(T_L^k) ≃ ℓ²(ℤ^k)`, `A_k`, `H¹`, symmetric restriction

Source anchors (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`):
* DEF-001 (`definitions.tex:7`), DEF-004 (`:25`, `Sym^N L²(T_L)`, `P_N` = average of `N!` permutations),
* DEF-005 (`:31`): the contact form lives on `H¹_sym(T_L^N)`, kinetic part `Σ_j ‖∂_jψ‖²`,
* DEF-031 (`:189`): `A_k = 1 - Σ_{j≤k} ∂_{x_j}²`.

Frozen imports (read-only): `EnergyMultiplier` `7394da58…` (positive Fourier multiplier on `ℓ²(ℤ^k)`),
`OccupationUnitary` `1c30d382…` (product Hilbert basis of the completed tensor power of `ℓ²(ℤ)`),
`TensorFourier` `750d8753…` (`positionFourier : L²(T_L^N) ≃ₗᵢ (ℓ²(ℤ))^{⊗̂N}`), `PhysicalTensor`
`e774c776…` (U2 position carrier, `physPerm`), `Fourier` `f0c07d6f…`.

Nothing is assumed: the carrier unitary is the composite `positionFourier` followed by the
representation of the completed tensor power in its product Hilbert basis.
-/

set_option autoImplicit false

noncomputable section

open scoped InnerProductSpace ENNReal ComplexConjugate
open MeasureTheory QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.TensorFourier
  QuantumNLS.OccupationUnitary QuantumNLS.Energy

namespace QuantumNLS.PhysicalEnergy

/-! ## §1 The carrier unitary `L²(T_L^k) ≃ₗᵢ ℓ²(ℤ^k)` -/

section Carrier

variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- **The Fourier carrier unitary** `F ↦ (F̂(w))_{w ∈ ℤ^k}`: `L²(T_L^k)` (mass-`L^k` product measure)
onto `ℓ²(Fin k → ℤ)`, as `U1^{⊗k}` (`positionFourier`) followed by the product Hilbert basis. -/
def momUnitary : L2TN L k ≃ₗᵢ[ℂ] L2 (Mom k) :=
  (positionFourier L k).trans (productBasis k).repr

variable {L k}

theorem momUnitary_apply (F : L2TN L k) (w : Mom k) :
    (momUnitary L k F : Mom k → ℂ) w = ⟪productVector w, positionFourier L k F⟫_ℂ := by
  show ((productBasis k).repr (positionFourier L k F)) w = _
  rw [HilbertBasis.repr_apply_apply, productBasis_apply]

/-- On product functions the coefficients factorize: `\widehat{⊗ f_j}(w) = ∏ f̂_j(w_j)`. -/
theorem momUnitary_prodLp (f : Fin k → L2T L) (w : Mom k) :
    (momUnitary L k (prodLp f) : Mom k → ℂ) w =
      ∏ j, QuantumNLS.Fourier.fourierL2 L (f j) (w j) := by
  rw [momUnitary_apply, positionFourier_prodLp]
  change ⟪((ptprod _ : AlgTensorPower ℂ OneParticle k) : Tensor k),
    ((ptprod _ : AlgTensorPower ℂ FourierFiber k) : Tensor k)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe, inner_ptprod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [oneBasis_apply, lp.inner_single_left]
  simp

/-- `⟪e_n, f⟫ = f̂(n)`: the `L²(T_L)` inner product with the report mode `e_n`. -/
theorem inner_modeLp (n : ℤ) (f : L2T L) :
    ⟪QuantumNLS.Fourier.modeLp L n, f⟫_ℂ = QuantumNLS.Fourier.fourierL2 L f n := by
  have h := (QuantumNLS.Fourier.fourierL2 L).inner_map_map (QuantumNLS.Fourier.modeLp L n) f
  rw [← h, QuantumNLS.Fourier.fourierL2_modeLp, lp.inner_single_left]
  simp

variable (L k)

/-- The product mode `E_w(x) = ∏_j e_{w_j}(x_j)`, `e_n(x) = L^{-1/2} e^{2πinx/L}`. -/
def prodMode (w : Mom k) : L2TN L k := prodLp (fun j => QuantumNLS.Fourier.modeLp L (w j))

variable {L k}

/-- **The `k`-dimensional Fourier coefficient is the `L²(T_L^k)` pairing with the product mode**:
`F̂(w) = ⟪E_w, F⟫` for every `F ∈ L²(T_L^k)`. -/
theorem momUnitary_apply_eq_inner (F : L2TN L k) (w : Mom k) :
    (momUnitary L k F : Mom k → ℂ) w = ⟪prodMode L k w, F⟫_ℂ := by
  rw [momUnitary_apply]
  obtain ⟨ψ, rfl⟩ := (physUnitary (L := L) (N := k)).surjective F
  induction ψ using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (continuous_const.inner ((positionFourier L k).continuous.comp physUnitary.continuous))
      (continuous_const.inner physUnitary.continuous)
  | ih a =>
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f =>
      rw [UniformSpace.Completion.coe_smul, map_smul, map_smul, physUnitary_ptprod,
        inner_smul_right, inner_smul_right]
      congr 1
      have h := momUnitary_prodLp f w
      rw [momUnitary_apply] at h
      rw [h, prodMode, inner_prodLp]
      exact Finset.prod_congr rfl fun j _ => (inner_modeLp _ _).symm
    | add x y hx hy =>
      rw [UniformSpace.Completion.coe_add, map_add, map_add, inner_add_right, inner_add_right, hx, hy]

end Carrier

/-! ## §2 Transport of unbounded operators along a unitary -/

section Transport

open scoped LinearPMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Abstract self-adjointness criterion**: a symmetric operator `T` with a bounded, symmetric,
right inverse `S` (`T (S y) = y`, `S y ∈ D(T)`) is self-adjoint.  (The argument used for
`mulOp` in `EnergyMultiplier`, now on an arbitrary Hilbert space.) -/
theorem isSelfAdjoint_of_inverse (T : E →ₗ.[ℂ] E) (S : E →L[ℂ] E)
    (hS : ∀ x y, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ) (hmem : ∀ y, S y ∈ T.domain)
    (hTS : ∀ y, T ⟨S y, hmem y⟩ = y)
    (hsym : ∀ x y : T.domain, ⟪T x, (y : E)⟫_ℂ = ⟪(x : E), T y⟫_ℂ) : IsSelfAdjoint T := by
  have hd : Dense (T.domain : Set E) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    have h0 : ∀ w : E, ⟪w, S y⟫_ℂ = 0 := fun w => by
      rw [← hS]; exact hy _ (hmem w)
    have h1 : S y = 0 := inner_self_eq_zero.1 (h0 _)
    have h2 := hTS y
    have h3 : (⟨S y, hmem y⟩ : T.domain) = 0 := Subtype.ext h1
    rw [h3] at h2
    exact h2.symm.trans T.toFun.map_zero
  have hle : T ≤ T† := LinearPMap.IsFormalAdjoint.le_adjoint hd hsym
  have hdom : T†.domain ≤ T.domain := by
    intro y hy
    set z := T† ⟨y, hy⟩ with hz
    have key : ∀ w : E, ⟪S z, w⟫_ℂ = ⟪y, w⟫_ℂ := fun w => by
      rw [hS]
      have h2 := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ ⟨S w, hmem w⟩
      rw [hTS w] at h2
      exact h2
    have hy' : y = S z := (ext_inner_right ℂ key).symm
    rw [hy']
    exact hmem z
  exact (LinearPMap.isSelfAdjoint_def).2
    (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

variable {ι : Type*} (U : E ≃ₗᵢ[ℂ] L2 ι)

/-- The conjugate `U⁻¹ T U` of an operator on `ℓ²(ι)`: domain `U⁻¹ D(T)`. -/
def conjPMap (T : L2 ι →ₗ.[ℂ] L2 ι) : E →ₗ.[ℂ] E where
  domain := T.domain.comap U.toLinearEquiv.toLinearMap
  toFun :=
    { toFun := fun x => U.symm (T ⟨U x, x.2⟩)
      map_add' := fun x y => by
        have : (⟨U ((x : E) + y), (x + y).2⟩ : T.domain) = ⟨U x, x.2⟩ + ⟨U y, y.2⟩ :=
          Subtype.ext (map_add U _ _)
        show U.symm (T ⟨U ((x : E) + y), (x + y).2⟩) = _
        rw [this, T.map_add, map_add]
      map_smul' := fun c x => by
        have : (⟨U (c • (x : E)), (c • x).2⟩ : T.domain) = c • ⟨U x, x.2⟩ :=
          Subtype.ext (map_smul U _ _)
        show U.symm (T ⟨U (c • (x : E)), (c • x).2⟩) = _
        rw [this, T.map_smul, map_smul]
        rfl }

omit [CompleteSpace E] in
theorem mem_conjPMap_domain (T : L2 ι →ₗ.[ℂ] L2 ι) (x : E) :
    x ∈ (conjPMap U T).domain ↔ U x ∈ T.domain := Iff.rfl

omit [CompleteSpace E] in
theorem conjPMap_apply (T : L2 ι →ₗ.[ℂ] L2 ι) (x : (conjPMap U T).domain) :
    (conjPMap U T x : E) = U.symm (T ⟨U x, x.2⟩) := rfl

/-- **Self-adjointness transports along a unitary** (for the multiplier operators `mulOp m`, `m ≥ 1`):
`U⁻¹ (mulOp m) U` is self-adjoint on `E`. -/
theorem conj_mulOp_isSelfAdjoint {m : ι → ℝ} (hm : ∀ n, 1 ≤ m n) :
    IsSelfAdjoint (conjPMap U (mulOp m)) := by
  let S : E →L[ℂ] E :=
    U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (invCLM m hm) ∘L
      U.toContinuousLinearEquiv.toContinuousLinearMap
  have hSapp : ∀ y, S y = U.symm (invCLM m hm (U y)) := fun y => rfl
  have hmem : ∀ y, S y ∈ (conjPMap U (mulOp m)).domain := fun y => by
    show U (S y) ∈ mulDomain m
    rw [hSapp, U.apply_symm_apply]
    exact invCLM_mem hm _
  refine isSelfAdjoint_of_inverse (conjPMap U (mulOp m)) S ?_ hmem ?_ ?_
  · intro x y
    calc ⟪S x, y⟫_ℂ = ⟪U.symm (invCLM m hm (U x)), U.symm (U y)⟫_ℂ := by
          rw [hSapp, U.symm_apply_apply]
      _ = ⟪invCLM m hm (U x), U y⟫_ℂ := U.symm.inner_map_map _ _
      _ = ⟪U x, invCLM m hm (U y)⟫_ℂ := inner_invCLM hm _ _
      _ = ⟪U.symm (U x), U.symm (invCLM m hm (U y))⟫_ℂ := (U.symm.inner_map_map _ _).symm
      _ = ⟪x, S y⟫_ℂ := by rw [U.symm_apply_apply, hSapp]
  · intro y
    have e : (⟨U (S y), hmem y⟩ : (mulOp m).domain) =
        ⟨invCLM m hm (U y), invCLM_mem hm _⟩ :=
      Subtype.ext (by
        show U (S y) = invCLM m hm (U y)
        rw [hSapp, U.apply_symm_apply])
    have h2 : mulOp m ⟨U (S y), hmem y⟩ = mulOp m ⟨invCLM m hm (U y), invCLM_mem hm _⟩ :=
      congrArg (fun z => mulOp m z) e
    rw [conjPMap_apply]
    show U.symm (mulOp m ⟨U (S y), hmem y⟩) = y
    rw [h2, mulOp_invCLM hm, U.symm_apply_apply]
  · intro x y
    rw [conjPMap_apply, conjPMap_apply]
    calc ⟪U.symm (mulOp m ⟨U x, x.2⟩), (y : E)⟫_ℂ
        = ⟪U.symm (mulOp m ⟨U x, x.2⟩), U.symm (U y)⟫_ℂ := by rw [U.symm_apply_apply]
      _ = ⟪mulOp m ⟨U x, x.2⟩, U y⟫_ℂ := U.symm.inner_map_map _ _
      _ = ⟪U x, mulOp m ⟨U y, y.2⟩⟫_ℂ := mulOp_formalAdjoint (m := m) ⟨U x, x.2⟩ ⟨U y, y.2⟩
      _ = ⟪U.symm (U x), U.symm (mulOp m ⟨U y, y.2⟩)⟫_ℂ := (U.symm.inner_map_map _ _).symm
      _ = ⟪(x : E), U.symm (mulOp m ⟨U y, y.2⟩)⟫_ℂ := by rw [U.symm_apply_apply]

theorem conj_mulOp_isClosed {m : ι → ℝ} (hm : ∀ n, 1 ≤ m n) : (conjPMap U (mulOp m)).IsClosed :=
  (conj_mulOp_isSelfAdjoint U hm).isClosed

end Transport

/-! ## §3 The physical operators `A_k`, `A_k^{1/2}` on `L²(T_L^k)` and the physical `H¹` -/

section Physical

open scoped LinearPMap

variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- `A_k = 1 - Σ_{j≤k} ∂_{x_j}²` on `L²(T_L^k)` (DEF-031): the Fourier multiplier `a_k(w)` conjugated
by the carrier unitary; domain `{F | Σ a_k² |F̂|² < ∞}` (`mem_physAk_domain_iff`). -/
def physAk : L2TN L k →ₗ.[ℂ] L2TN L k := conjPMap (momUnitary L k) (Ak L k)

/-- `A_k^{1/2}` on `L²(T_L^k)`. -/
def physAhalf : L2TN L k →ₗ.[ℂ] L2TN L k := conjPMap (momUnitary L k) (Ahalf L k)

/-- **`A_k` is self-adjoint on `L²(T_L^k)`** (transported, not assumed). -/
theorem physAk_isSelfAdjoint : IsSelfAdjoint (physAk L k) :=
  conj_mulOp_isSelfAdjoint (momUnitary L k) (one_le_kinWeight L k)

/-- **`A_k^{1/2}` is self-adjoint on `L²(T_L^k)`.** -/
theorem physAhalf_isSelfAdjoint : IsSelfAdjoint (physAhalf L k) :=
  conj_mulOp_isSelfAdjoint (momUnitary L k) (one_le_kinSqrt L k)

theorem physAk_isClosed : (physAk L k).IsClosed := (physAk_isSelfAdjoint L k).isClosed

theorem physAhalf_isClosed : (physAhalf L k).IsClosed := (physAhalf_isSelfAdjoint L k).isClosed

variable {L k}

/-- **Domain of `A_k`**: `F ∈ D(A_k) ⟺ Σ_w a_k(w)² |F̂(w)|² < ∞` (`H²`-type condition). -/
theorem mem_physAk_domain_iff (F : L2TN L k) :
    F ∈ (physAk L k).domain ↔
      Summable fun w => kinWeight L k w ^ 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 :=
  mem_mulDomain_iff (kinWeight L k) (momUnitary L k F)

/-- **Domain of `A_k^{1/2}` = form domain `H¹(T_L^k)`**:
`F ∈ D(A_k^{1/2}) ⟺ Σ_w a_k(w) |F̂(w)|² < ∞`. -/
theorem mem_physAhalf_domain_iff (F : L2TN L k) :
    F ∈ (physAhalf L k).domain ↔
      Summable fun w => kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 := by
  show momUnitary L k F ∈ mulDomain (kinSqrt L k) ↔ _
  rw [mem_mulDomain_iff]
  exact summable_congr fun w => by rw [kinSqrt_sq]

/-- **`A_k` acts diagonally on the Fourier coefficients**: `\widehat{A_k F}(w) = a_k(w) F̂(w)`. -/
theorem momUnitary_physAk (F : (physAk L k).domain) (w : Mom k) :
    (momUnitary L k (physAk L k F) : Mom k → ℂ) w =
      (kinWeight L k w : ℂ) * (momUnitary L k (F : L2TN L k) : Mom k → ℂ) w := by
  have h : (physAk L k F : L2TN L k) =
      (momUnitary L k).symm (Ak L k ⟨momUnitary L k (F : L2TN L k), F.2⟩) := rfl
  rw [h, LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem momUnitary_physAhalf (F : (physAhalf L k).domain) (w : Mom k) :
    (momUnitary L k (physAhalf L k F) : Mom k → ℂ) w =
      (kinSqrt L k w : ℂ) * (momUnitary L k (F : L2TN L k) : Mom k → ℂ) w := by
  have h : (physAhalf L k F : L2TN L k) =
      (momUnitary L k).symm (Ahalf L k ⟨momUnitary L k (F : L2TN L k), F.2⟩) := rfl
  rw [h, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- **Positivity of `A_k`** on `L²(T_L^k)`: `⟪F, A_k F⟫ = Σ a_k |F̂|²`, real, `≥ ‖F‖²`. -/
theorem inner_physAk_self (F : (physAk L k).domain) :
    ⟪(F : L2TN L k), physAk L k F⟫_ℂ =
      ((∑' w, kinWeight L k w * ‖(momUnitary L k (F : L2TN L k) : Mom k → ℂ) w‖ ^ 2 : ℝ) : ℂ) := by
  have h := inner_mulOp_self (m := kinWeight L k) ⟨momUnitary L k (F : L2TN L k), F.2⟩
  rw [← (momUnitary L k).inner_map_map]
  rw [show (momUnitary L k) (physAk L k F) = mulOp (kinWeight L k) ⟨momUnitary L k (F : L2TN L k), F.2⟩ from
    (momUnitary L k).apply_symm_apply _]
  exact h

theorem norm_sq_le_physAk (F : (physAk L k).domain) :
    ‖(F : L2TN L k)‖ ^ 2 ≤ ∑' w, kinWeight L k w * ‖(momUnitary L k (F : L2TN L k) : Mom k → ℂ) w‖ ^ 2 := by
  have h := norm_sq_le_form (one_le_kinWeight L k) ⟨momUnitary L k (F : L2TN L k), F.2⟩
  rw [← (momUnitary L k).norm_map]
  exact h

/-- **`A_k^{1/2}` is a square root of `A_k` on `L²(T_L^k)`, with domains.** -/
theorem mem_physAk_domain_iff_comp (F : L2TN L k) :
    F ∈ (physAk L k).domain ↔
      ∃ hF : F ∈ (physAhalf L k).domain,
        (physAhalf L k ⟨F, hF⟩ : L2TN L k) ∈ (physAhalf L k).domain := by
  have h := mem_Ak_domain_iff L k (momUnitary L k F)
  constructor
  · intro hF
    obtain ⟨hx, hy⟩ := h.1 hF
    refine ⟨hx, ?_⟩
    show momUnitary L k (physAhalf L k ⟨F, hx⟩) ∈ mulDomain (kinSqrt L k)
    have e : momUnitary L k (physAhalf L k ⟨F, hx⟩) = Ahalf L k ⟨momUnitary L k F, hx⟩ :=
      (momUnitary L k).apply_symm_apply _
    rw [e]; exact hy
  · rintro ⟨hx, hy⟩
    refine h.2 ⟨hx, ?_⟩
    have e : momUnitary L k (physAhalf L k ⟨F, hx⟩) = Ahalf L k ⟨momUnitary L k F, hx⟩ :=
      (momUnitary L k).apply_symm_apply _
    have hy' : momUnitary L k (physAhalf L k ⟨F, hx⟩) ∈ mulDomain (kinSqrt L k) := hy
    rw [e] at hy'; exact hy'

theorem physAk_eq_comp (F : (physAk L k).domain) :
    physAk L k F = physAhalf L k ⟨physAhalf L k ⟨(F : L2TN L k),
      ((mem_physAk_domain_iff_comp (F : L2TN L k)).1 F.2).1⟩,
      ((mem_physAk_domain_iff_comp (F : L2TN L k)).1 F.2).2⟩ := by
  apply (momUnitary L k).injective
  apply Subtype.ext; funext w
  rw [momUnitary_physAk, momUnitary_physAhalf, momUnitary_physAhalf]
  show (kinWeight L k w : ℂ) * _ = (kinSqrt L k w : ℂ) * ((kinSqrt L k w : ℂ) * _)
  rw [← mul_assoc, ← Complex.ofReal_mul, ← pow_two, kinSqrt_sq]

end Physical

/-! ## §4 The physical `H¹(T_L^k)`: form domain, energy norm, kinetic characterization -/

section H1

open scoped LinearPMap

variable (L : ℝ) [Fact (0 < L)] (k : ℕ)

/-- `H¹(T_L^k)` as a Hilbert space with the energy norm `‖F‖_{H¹} = ‖A_k^{1/2} F‖`.  (A `def` over the
Fourier-side `H1Dom`, so that the `L²` norm is not inherited; the elements are realized as
functions on `T_L^k` by `PhysH1.val`.) -/
def PhysH1 : Type := H1Dom L k

instance : NormedAddCommGroup (PhysH1 L k) := inferInstanceAs (NormedAddCommGroup (H1Dom L k))
instance : InnerProductSpace ℂ (PhysH1 L k) := inferInstanceAs (InnerProductSpace ℂ (H1Dom L k))
instance : CompleteSpace (PhysH1 L k) := inferInstanceAs (CompleteSpace (H1Dom L k))

variable {L k}

/-- The `L²(T_L^k)` function represented by an element of `H¹`. -/
def PhysH1.val (x : PhysH1 L k) : L2TN L k :=
  (momUnitary L k).symm (show H1Dom L k from x).val

/-- Build an element from the Fourier-side `H¹` vector. -/
def PhysH1.mk (z : H1Dom L k) : PhysH1 L k := z

theorem PhysH1.val_mk (z : H1Dom L k) : (PhysH1.mk z).val = (momUnitary L k).symm z.val := rfl

theorem PhysH1.momUnitary_val (x : PhysH1 L k) :
    momUnitary L k x.val = (show H1Dom L k from x).val :=
  (momUnitary L k).apply_symm_apply _

theorem PhysH1.val_injective : Function.Injective (PhysH1.val : PhysH1 L k → L2TN L k) := by
  intro x y h
  have h2 : (show H1Dom L k from x).val = (show H1Dom L k from y).val := by
    rw [← PhysH1.momUnitary_val, ← PhysH1.momUnitary_val, h]
  exact Mult.DomSpace.ext h2

/-- **Kinetic characterization of the form domain**: the functions of `H¹(T_L^k)` are exactly the
`F ∈ L²(T_L^k)` with `Σ_w (1 + Σ_j (2πw_j/L)²) |F̂(w)|² < ∞`; equivalently `F ∈ D(A_k^{1/2})`. -/
theorem PhysH1.range_val :
    Set.range (PhysH1.val : PhysH1 L k → L2TN L k) =
      {F | Summable fun w => kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2} := by
  ext F
  constructor
  · rintro ⟨x, rfl⟩
    show Summable fun w => kinWeight L k w *
      ‖(momUnitary L k (PhysH1.val x) : Mom k → ℂ) w‖ ^ 2
    rw [PhysH1.momUnitary_val]
    exact summable_kin_form (show H1Dom L k from x)
  · intro hF
    have hmem : momUnitary L k F ∈ mulDomain (kinSqrtMult L k).m := by
      rw [mem_mulDomain_iff]
      refine hF.congr fun w => ?_
      show kinWeight L k w * _ = kinSqrt L k w ^ 2 * _
      rw [kinSqrt_sq]
    refine ⟨PhysH1.mk (Mult.DomSpace.mk (M := kinSqrtMult L k) (momUnitary L k F) hmem), ?_⟩
    rw [PhysH1.val_mk, Mult.DomSpace.val_mk (M := kinSqrtMult L k), LinearIsometryEquiv.symm_apply_apply]

/-- ... and the range is the domain of `A_k^{1/2}` (the closed form's domain). -/
theorem PhysH1.range_val_eq_domain :
    Set.range (PhysH1.val : PhysH1 L k → L2TN L k) = ((physAhalf L k).domain : Set (L2TN L k)) := by
  rw [PhysH1.range_val]
  ext F
  exact (mem_physAhalf_domain_iff F).symm

/-- **Energy norm** `‖F‖²_{H¹} = Σ_w a_k(w) |F̂(w)|²`. -/
theorem PhysH1.norm_sq_eq (x : PhysH1 L k) :
    ‖x‖ ^ 2 = ∑' w, kinWeight L k w * ‖(momUnitary L k x.val : Mom k → ℂ) w‖ ^ 2 := by
  rw [PhysH1.momUnitary_val]
  exact H1Dom.norm_sq_eq (show H1Dom L k from x)

/-- **`‖F‖²_{H¹} = ‖F‖²_{L²} + Σ_j ‖∂_{x_j}F‖²`** with `‖∂_{x_j}F‖² = Σ_w (2πw_j/L)² |F̂(w)|²`
(the source's `A_k = 1 - Σ ∂²`; Plancherel for the carrier unitary). -/
theorem PhysH1.kinetic_split (x : PhysH1 L k) :
    ‖x‖ ^ 2 = ‖x.val‖ ^ 2 +
      ∑ j, ∑' w, QuantumNLS.Fourier.freq L (w j) ^ 2 * ‖(momUnitary L k x.val : Mom k → ℂ) w‖ ^ 2 := by
  have h := H1Dom.kinetic_split (show H1Dom L k from x)
  rw [PhysH1.momUnitary_val]
  rw [show ‖x.val‖ = ‖(show H1Dom L k from x).val‖ by
    rw [← PhysH1.momUnitary_val, (momUnitary L k).norm_map]]
  exact h

/-- Continuous inclusion `H¹ ↪ L²`, norm `≤ 1`. -/
theorem PhysH1.norm_val_le (x : PhysH1 L k) : ‖x.val‖ ≤ ‖x‖ := by
  have h := H1Dom.norm_val_le (show H1Dom L k from x)
  rw [show ‖x.val‖ = ‖(show H1Dom L k from x).val‖ by
    rw [← PhysH1.momUnitary_val, (momUnitary L k).norm_map]]
  exact h

/-- **`A_k^{1/2} : H¹(T_L^k) ≃ₗᵢ L²(T_L^k)`**, the physical energy unitary. -/
def PhysH1.unitary : PhysH1 L k ≃ₗᵢ[ℂ] L2TN L k :=
  (Mult.DomSpace.unitary (kinSqrtMult L k)).trans (momUnitary L k).symm

theorem PhysH1.unitary_apply (x : PhysH1 L k) :
    momUnitary L k (PhysH1.unitary x) =
      Mult.DomSpace.unitary (kinSqrtMult L k) (show H1Dom L k from x) :=
  (momUnitary L k).apply_symm_apply _

/-- Its action in Fourier coefficients is the multiplier: `\widehat{A^{1/2}F}(w) = √a_k(w) F̂(w)`. -/
theorem PhysH1.unitary_coeff (x : PhysH1 L k) (w : Mom k) :
    (momUnitary L k (PhysH1.unitary x) : Mom k → ℂ) w =
      (kinSqrt L k w : ℂ) * (momUnitary L k x.val : Mom k → ℂ) w := by
  rw [PhysH1.unitary_apply, PhysH1.momUnitary_val]
  rfl

end H1

/-! ## §5 Permutations and the symmetric restriction (DEF-004 / DEF-005) -/

section Perm

open scoped LinearPMap

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- **The carrier unitary intertwines coordinate permutations with index permutations**:
`\widehat{V_σ F}(w) = F̂(w ∘ σ)` where `(V_σ F)(x) = F(x ∘ σ)`. -/
theorem momUnitary_physPerm (σ : Equiv.Perm (Fin k)) (F : L2TN L k) (w : Mom k) :
    (momUnitary L k (physPerm σ F) : Mom k → ℂ) w = (momUnitary L k F : Mom k → ℂ) (w ∘ σ) := by
  rw [momUnitary_apply_eq_inner, momUnitary_apply_eq_inner]
  have key : prodMode L k w = physPerm σ (prodMode L k (w ∘ σ)) := by
    have h := prodLp_perm σ (fun j => QuantumNLS.Fourier.modeLp L ((w ∘ σ) j))
    unfold prodMode
    rw [← h]
    congr 1
    funext i
    simp
  rw [key]
  exact (physPerm σ).inner_map_map _ _

/-- Permutation invariance of a wave function ⟺ invariance of its Fourier coefficients. -/
theorem isSymm_iff_coeff (F : L2TN L k) :
    (∀ σ : Equiv.Perm (Fin k), physPerm σ F = F) ↔
      ∀ (σ : Equiv.Perm (Fin k)) (w : Mom k),
        (momUnitary L k F : Mom k → ℂ) (w ∘ σ) = (momUnitary L k F : Mom k → ℂ) w := by
  constructor
  · intro h σ w
    have := momUnitary_physPerm σ F w
    rw [h σ] at this
    exact this.symm
  · intro h σ
    apply (momUnitary L k).injective
    apply Subtype.ext; funext w
    rw [momUnitary_physPerm]
    exact h σ w

/-- **DEF-004 in momentum space**: `ψ ∈ Sym^k L²(T_L)` iff the Fourier coefficients of its wave function
`F = physUnitary ψ` are invariant under permuting the indices. -/
theorem mem_physSector_iff_coeff (ψ : HilbertTensorPower ℂ (L2T L) k) :
    ψ ∈ physSector L k ↔
      ∀ (σ : Equiv.Perm (Fin k)) (w : Mom k),
        (momUnitary L k (physUnitary ψ) : Mom k → ℂ) (w ∘ σ) =
          (momUnitary L k (physUnitary ψ) : Mom k → ℂ) w :=
  (mem_physSector_iff ψ).trans (isSymm_iff_coeff _)

omit [Fact (0 < L)] in
/-- The kinetic symbol `a_k(w) = 1 + Σ_j (2πw_j/L)²` is invariant under permuting the particles. -/
theorem kinWeight_comp (σ : Equiv.Perm (Fin k)) (w : Mom k) :
    kinWeight L k (w ∘ σ) = kinWeight L k w := by
  unfold kinWeight
  congr 1
  exact Equiv.sum_comp σ (fun j => QuantumNLS.Fourier.freq L (w j) ^ 2)

/-- Reindexing `w ↦ w ∘ σ` of the momentum lattice. -/
def permEquiv (σ : Equiv.Perm (Fin k)) : Mom k ≃ Mom k where
  toFun w := w ∘ σ
  invFun w := w ∘ σ.symm
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

/-- **`H¹`-membership (finite energy) is permutation invariant.** -/
theorem physPerm_mem_physAhalf_domain_iff (σ : Equiv.Perm (Fin k)) (F : L2TN L k) :
    physPerm σ F ∈ (physAhalf L k).domain ↔ F ∈ (physAhalf L k).domain := by
  rw [mem_physAhalf_domain_iff, mem_physAhalf_domain_iff]
  have h := (permEquiv σ).summable_iff
    (f := fun w => kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2)
  simp_rw [momUnitary_physPerm]
  rw [← h]
  refine summable_congr fun w => ?_
  show _ = kinWeight L k (w ∘ σ) * _
  rw [kinWeight_comp]
  rfl

/-- ... and the energy form is permutation invariant. -/
theorem form_physPerm (σ : Equiv.Perm (Fin k)) (F : L2TN L k) :
    ∑' w, kinWeight L k w * ‖(momUnitary L k (physPerm σ F) : Mom k → ℂ) w‖ ^ 2 =
      ∑' w, kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 := by
  simp_rw [momUnitary_physPerm]
  rw [← (permEquiv σ).tsum_eq (fun w => kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2)]
  refine tsum_congr fun w => ?_
  show _ = kinWeight L k (w ∘ σ) * _
  rw [kinWeight_comp]
  rfl

/-- Domain of `A_k` is permutation invariant. -/
theorem physPerm_mem_physAk_domain_iff (σ : Equiv.Perm (Fin k)) (F : L2TN L k) :
    physPerm σ F ∈ (physAk L k).domain ↔ F ∈ (physAk L k).domain := by
  rw [mem_physAk_domain_iff, mem_physAk_domain_iff]
  have h := (permEquiv σ).summable_iff
    (f := fun w => kinWeight L k w ^ 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2)
  simp_rw [momUnitary_physPerm]
  rw [← h]
  refine summable_congr fun w => ?_
  show _ = kinWeight L k (w ∘ σ) ^ 2 * _
  rw [kinWeight_comp]
  rfl

/-- **`A_k^{1/2}` commutes with the coordinate permutations** (on `D(A_k^{1/2})`). -/
theorem physAhalf_comm_perm (σ : Equiv.Perm (Fin k)) (F : (physAhalf L k).domain) :
    physAhalf L k ⟨physPerm σ (F : L2TN L k), (physPerm_mem_physAhalf_domain_iff σ _).2 F.2⟩ =
      physPerm σ (physAhalf L k F) := by
  apply (momUnitary L k).injective
  apply Subtype.ext; funext w
  rw [momUnitary_physAhalf, momUnitary_physPerm, momUnitary_physPerm, momUnitary_physAhalf]
  have h : kinSqrt L k (w ∘ σ) = kinSqrt L k w := by
    unfold kinSqrt; rw [kinWeight_comp]
  rw [h]

/-- **`A_k` commutes with the coordinate permutations** (on `D(A_k)`): in particular it preserves
the symmetric sector. -/
theorem physAk_comm_perm (σ : Equiv.Perm (Fin k)) (F : (physAk L k).domain) :
    physAk L k ⟨physPerm σ (F : L2TN L k), (physPerm_mem_physAk_domain_iff σ _).2 F.2⟩ =
      physPerm σ (physAk L k F) := by
  apply (momUnitary L k).injective
  apply Subtype.ext; funext w
  rw [momUnitary_physAk, momUnitary_physPerm, momUnitary_physPerm, momUnitary_physAk]
  have h : kinWeight L k (w ∘ σ) = kinWeight L k w := kinWeight_comp σ w
  rw [h]

end Perm

/-! ## §6 `H¹_sym(T_L^k)` (DEF-005): the permutation-invariant finite-energy subspace -/

section H1sym

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- The linear map `H¹ → L²`, `x ↦ val x`. -/
def PhysH1.valₗ : PhysH1 L k →ₗ[ℂ] L2TN L k where
  toFun := PhysH1.val
  map_add' x y := by
    unfold PhysH1.val
    rw [show (show H1Dom L k from x + y).val =
      (show H1Dom L k from x).val + (show H1Dom L k from y).val from rfl, map_add]
  map_smul' c x := by
    unfold PhysH1.val
    rw [show (show H1Dom L k from c • x).val = c • (show H1Dom L k from x).val from rfl, map_smul]
    rfl

/-- Continuous (norm `≤ 1`): the inclusion `H¹ ↪ L²`. -/
def PhysH1.valCLM : PhysH1 L k →L[ℂ] L2TN L k :=
  (PhysH1.valₗ).mkContinuous 1 (fun x => by
    have h := PhysH1.norm_val_le x
    rw [one_mul]
    exact h)

@[simp] theorem PhysH1.valCLM_apply (x : PhysH1 L k) : PhysH1.valCLM x = x.val := rfl

/-- `H¹_sym(T_L^k)`: the finite-energy wave functions invariant under every coordinate permutation. -/
def PhysH1.sym : Submodule ℂ (PhysH1 L k) :=
  ⨅ σ : Equiv.Perm (Fin k),
    LinearMap.ker (((physPerm (L := L) σ).toLinearMap).comp (PhysH1.valₗ) - PhysH1.valₗ)

theorem PhysH1.mem_sym_iff (x : PhysH1 L k) :
    x ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L k)) ↔ ∀ σ : Equiv.Perm (Fin k), physPerm σ x.val = x.val := by
  unfold PhysH1.sym
  rw [Submodule.mem_iInf]
  refine forall_congr' fun σ => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  rfl

/-- `H¹_sym` is closed in `H¹`, hence complete: a Hilbert space with the energy norm. -/
theorem PhysH1.isClosed_sym : IsClosed ((PhysH1.sym : Submodule ℂ (PhysH1 L k)) : Set (PhysH1 L k)) := by
  have : ((PhysH1.sym : Submodule ℂ (PhysH1 L k)) : Set (PhysH1 L k)) =
      ⋂ σ : Equiv.Perm (Fin k), {x : PhysH1 L k | physPerm σ x.val = x.val} := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iInter]
    exact PhysH1.mem_sym_iff x
  rw [this]
  refine isClosed_iInter fun σ => isClosed_eq ?_ ?_
  · exact (physPerm σ).continuous.comp (PhysH1.valCLM (L := L) (k := k)).continuous
  · exact (PhysH1.valCLM (L := L) (k := k)).continuous

instance : CompleteSpace (PhysH1.sym : Submodule ℂ (PhysH1 L k)) :=
  PhysH1.isClosed_sym.completeSpace_coe

/-- **Kinetic characterization of `H¹_sym`**: its functions are exactly the `F ∈ L²(T_L^k)` with
permutation-invariant Fourier coefficients and `Σ_w a_k(w)|F̂(w)|² < ∞`. -/
theorem PhysH1.range_val_sym :
    PhysH1.val '' ((PhysH1.sym : Submodule ℂ (PhysH1 L k)) : Set (PhysH1 L k)) =
      {F : L2TN L k | (∀ (σ : Equiv.Perm (Fin k)) (w : Mom k),
          (momUnitary L k F : Mom k → ℂ) (w ∘ σ) = (momUnitary L k F : Mom k → ℂ) w) ∧
        Summable fun w => kinWeight L k w * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2} := by
  ext F
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(isSymm_iff_coeff _).1 ((PhysH1.mem_sym_iff x).1 hx), ?_⟩
    have : PhysH1.val x ∈ Set.range (PhysH1.val : PhysH1 L k → L2TN L k) := ⟨x, rfl⟩
    rw [PhysH1.range_val] at this
    exact this
  · rintro ⟨hs, hf⟩
    have hr : F ∈ Set.range (PhysH1.val : PhysH1 L k → L2TN L k) := by
      rw [PhysH1.range_val]; exact hf
    obtain ⟨x, rfl⟩ := hr
    exact ⟨x, (PhysH1.mem_sym_iff x).2 ((isSymm_iff_coeff _).2 hs), rfl⟩

end H1sym

end QuantumNLS.PhysicalEnergy
