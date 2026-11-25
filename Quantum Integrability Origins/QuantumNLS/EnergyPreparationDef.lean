/-
QuantumNLS.EnergyPreparationDef — DEF-031 (definitions.tex:187-189) stated and connected on the
actual physical carriers (owner: opus_tensor).

Source (sha256 `definitions.tex` abe7643b…, `core/model.tex` 1dec8385…,
`energy_prepared/energy_trace.tex` e8f8ae09…):
* DEF-031: "In addition to norm closeness, energy preparation requires `ψ_N ∈ H¹_sym` and
  `limsup_N 𝔥_N[ψ_N]/N ≤ I₃(u)`. For fixed `k`, set `A_k = 1 − Σ_{j≤k} ∂²_{x_j}`. The additive energy
  trace norm of a difference `D` is `‖A_k^{1/2} D A_k^{1/2}‖₁`, defined through the corresponding
  trace-class form realization."
* model.tex:3-15: `𝔥_N[F,G] = Σ_j ⟨∂_jF, ∂_jG⟩ + (2κ/N) Σ_{j<k} ∫ conj F G|_{x_k=x_j} ∏_{ℓ≠k} dx_ℓ`;
  `I₃(u) = ‖u'‖² + κ ∫|u|⁴` (model.tex:64-70 context).
* energy_trace.tex:15-26: `A_k = 1 + Σ D_j²`; for positive `ρ` with `Tr(A_kρ) < ∞` the realization is
  positive trace class and equals `Σ_j λ_j |A_k^{1/2}f_j⟩⟨A_k^{1/2}f_j|` (trace norm) for a
  decomposition `ρ = Σ λ_j|f_j⟩⟨f_j|`; no range-in-`dom(A_k)` hypothesis.
Gate specification: `implementation/review records/terra_review-def031-trusted-spec.md` (not narrowed).

Proved here (standard axioms only):
* §1 `I3`, `I3_eq`: `I₃(u) = ‖u'‖²₂ + κ∫|u|⁴`, `u'` the periodic weak derivative; `charge_three_eq_I3`.
* §2 `hN_literal` (`𝔥_N = Σ‖∂_jψ‖² + (2κ/N)Σ_{i<j}‖T_ijψ‖²_{L²(dy_ij)}`, weak partials, Sol's trace on
  the coordinate diagonal measure), `contact_form_operator` (closed form ⇒ self-adjoint `H`, compact
  resolvent, variational domain), **`EnergyPreparation`** (literal predicate), `limsup_le_iff`,
  `energy_iff_energyPrepared`, **`product_energyPreparation`** (check).
* §3 `AkT`/`AhalfT` on the `k`-particle carrier: **`AkT_isSelfAdjoint`**, `mem_AkT_domain_iff` (weak
  `∂_j²`), `mem_AhalfT_domain_iff` (weak `H¹`), `eK_AkT` (multiplier `1 + Σ_j(2πw_j/L)²`),
  `W = A_k^{-1/2}`: `AhalfT_W`, `W_AhalfT`, `W_W_AkT`, `W_inner`.
* §4 **`IsFormRealization`** (`⟨f,Tg⟩ = ⟨A_k^{1/2}f, D A_k^{1/2}g⟩` on the form domain),
  **`isFormRealization_iff`** (`⟺ D = W T W`), `formRealization_unique`, `additiveEnergyTraceNorm`,
  **`exists_traceClass_formRealization_iff`** (exact domain for an arbitrary bounded difference `D`:
  trace-class realization exists ⟺ norm `< ⊤` ⟺ `D = W T W`, `T` trace class), `traceNorm_le_additive`.
* §5 positive finite-energy `ρ`: `positive_formRealization`, **`energyTrace_eq_series`**
  (`Tr(A_kρ) = Σ_j λ_j‖A_k^{1/2}f_j‖²` for every decomposition), **`realization_series`** (series →
  realization in trace norm, no range-in-`dom(A_k)` hypothesis), `positive_realization_spectral`.
* §6 `product_marginal_check` (actual marginal of `u^{⊗N}` minus projector: realization `0`).
-/
import QuantumNLS.SymmetricAkSpectrum
import QuantumNLS.PhysicalProductPreparation
import QuantumNLS.StrongSymbolDef

open scoped InnerProductSpace ENNReal ComplexConjugate LinearPMap
open MeasureTheory Filter Topology

noncomputable section

namespace QuantumNLS.EnergyPreparationDef

open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.Energy
  QuantumNLS.TensorCarrier QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)]

/-! ## §1 `I₃(u) = ‖u'‖²₂ + κ ∫ |u|⁴` with the distributional derivative -/

/-- `I₃(u)` (the energy `E_κ(u) = K(u) + κ Q(u)` of `ChargeEnergy`). -/
def I3 (κ : ℝ) (u : L2T L) : ℝ := QuantumNLS.ChargeEnergy.energyH1 κ (u : AddCircle L → ℂ)

theorem norm_sq_eq_tsum_coeff (g : L2T L) :
    ‖g‖ ^ 2 = ∑' n : ℤ, ‖coeff L (g : AddCircle L → ℂ) n‖ ^ 2 := by
  rw [← (fourierL2 L).norm_map, QuantumNLS.Energy.norm_sq_eq_tsum]
  congr 1; funext n
  rw [fourierL2_apply]

/-- `K(u) = ‖u'‖²` for the weak (distributional, periodic) derivative `u'`. -/
theorem kinetic_eq_norm_sq_deriv {u g : L2T L} (h : QuantumNLS.WeakDerivatives.HasWeakDeriv u g) :
    QuantumNLS.ChargeEnergy.kinetic (u : AddCircle L → ℂ) = ‖g‖ ^ 2 := by
  rw [norm_sq_eq_tsum_coeff]
  unfold QuantumNLS.ChargeEnergy.kinetic
  congr 1; funext n
  rw [QuantumNLS.WeakDerivatives.coeff_of_hasWeakDeriv h n,
    QuantumNLS.WeakDerivatives.norm_ikn_mul_sq]

/-- **`I₃(u) = ‖u'‖²₂ + κ∫|u|⁴`** literally, `u'` the weak derivative. -/
theorem I3_eq {κ : ℝ} {u g : L2T L} (h : QuantumNLS.WeakDerivatives.HasWeakDeriv u g) :
    I3 κ u = ‖g‖ ^ 2 + κ * ∫ x, ‖(u : AddCircle L → ℂ) x‖ ^ 4 := by
  unfold I3 QuantumNLS.ChargeEnergy.energyH1 QuantumNLS.ChargeEnergy.quartic
  rw [kinetic_eq_norm_sq_deriv h]

/-- For smooth profiles `I₃` is the DEF-022 charge `I₃ = charge L κ ũ 3`. -/
theorem charge_three_eq_I3 (κ : ℝ) {ũ : ℝ → ℂ}
    (hs : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ) :
    QuantumNLS.ClassicalCharges.charge L κ ũ 3 =
      ((I3 κ (QuantumNLS.PhysicalProductPreparation.smoothClass hs) : ℝ) : ℂ) :=
  QuantumNLS.ProductEnergyPreparation.energyH1_smooth_class κ hs

/-! ## §2 The contact form `𝔥_N` and the energy-preparation predicate -/

/-- `𝔥_N[x] = Re q_{κ/N}(x,x)` (DEF-005 with `c = κ/N`, coefficient `2κ/N`). -/
abbrev hN (κ : ℝ) (N : ℕ) (x : PhysH1 L N) : ℝ := QuantumNLS.ProductEnergyPreparation.hN κ N x

/-- The weak partial of an `H¹` element is `gradientCLM`. -/
theorem gradientCLM_hasWeakPartial {N : ℕ} (j : Fin N) (x : PhysH1 L N) :
    QuantumNLS.ProductWeakDerivatives.HasWeakPartial j x.val
      (QuantumNLS.CollisionIdentification.gradientCLM j x) := by
  obtain ⟨G, hG⟩ := (QuantumNLS.ProductWeakDerivatives.mem_range_physH1_iff x.val).1 ⟨x, rfl⟩ j
  rwa [QuantumNLS.CollisionIdentification.gradientCLM_eq_of_weak j x G hG]

/-- **`𝔥_N` literally**: `Σ_j ‖∂_jψ‖² + (2κ/N) Σ_{i<j} ‖T_ijψ‖²_{L²(dy_ij)}` with `∂_j` the weak
periodic partial and `T_ij` Sol's collision trace into `L²` of the coordinate diagonal measure
`dy_ij` (no `√2`); on smooth tests `T_ij` is the literal restriction (`productTrace_smooth`). -/
theorem hN_literal (κ : ℝ) {N : ℕ} (x : PhysH1 L N) :
    hN κ N x = ∑ j, ‖QuantumNLS.CollisionIdentification.gradientCLM j x‖ ^ 2 +
      2 * (κ / N) * ∑ p : QuantumNLS.ContactForm.Pair N,
        ‖QuantumNLS.CollisionIdentification.productTrace p.1.1 p.1.2 (ne_of_lt p.2) x‖ ^ 2 ∧
    ∀ j, QuantumNLS.ProductWeakDerivatives.HasWeakPartial j x.val
      (QuantumNLS.CollisionIdentification.gradientCLM j x) :=
  ⟨QuantumNLS.PhysicalProductPreparation.hN_physical κ x, fun j => gradientCLM_hasWeakPartial j x⟩

/-- **The closed contact form defines the Hamiltonian** (frozen ContactOperator, `c = κ/N ≥ 0`):
the associated operator is self-adjoint with compact resolvent, and its domain is exactly the
variational one. -/
theorem contact_form_operator {κ : ℝ} (hκ : 0 ≤ κ) (N : ℕ) :
    IsSelfAdjoint (QuantumNLS.ContactOperator.Hop (L := L) (N := N) (κ / N)
      (div_nonneg hκ (Nat.cast_nonneg N))) ∧
    IsCompactOperator (QuantumNLS.ContactOperator.Rop (L := L) (N := N) (κ / N)
      (div_nonneg hκ (Nat.cast_nonneg N))) ∧
    ∀ (x : QuantumNLS.ContactOperator.VSym L N) (f : QuantumNLS.ContactOperator.SymL2 L N),
      (∀ φ : QuantumNLS.ContactOperator.VSym L N,
        QuantumNLS.ContactForm.q (κ / N) φ.1 x.1 =
          ⟪(QuantumNLS.ContactOperator.valSym φ : QuantumNLS.ContactOperator.SymL2 L N), f⟫_ℂ) →
      ∃ h : (QuantumNLS.ContactOperator.valSym x : QuantumNLS.ContactOperator.SymL2 L N) ∈
          (QuantumNLS.ContactOperator.Hop (L := L) (N := N) (κ / N)
            (div_nonneg hκ (Nat.cast_nonneg N))).domain,
        QuantumNLS.ContactOperator.Hop (κ / N) (div_nonneg hκ (Nat.cast_nonneg N))
          ⟨QuantumNLS.ContactOperator.valSym x, h⟩ = f :=
  ⟨QuantumNLS.ContactOperator.Hop_isSelfAdjoint _, QuantumNLS.ContactOperator.Hop_compact_resolvent _,
    fun x f hq => QuantumNLS.ContactOperator.mem_domain_of_variational _ x f hq⟩

/-- `limsup` in `EReal` versus the `ε`–eventually formulation. -/
theorem limsup_le_iff (f : ℕ → ℝ) (c : ℝ) :
    limsup (fun N => (f N : EReal)) atTop ≤ (c : EReal) ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, f N ≤ c + ε := by
  constructor
  · intro h ε hε
    have hlt : limsup (fun N => (f N : EReal)) atTop < ((c + ε : ℝ) : EReal) :=
      h.trans_lt (by exact_mod_cast (by linarith : c < c + ε))
    filter_upwards [Filter.eventually_lt_of_limsup_lt hlt] with N hN
    exact_mod_cast hN.le
  · intro h
    refine le_of_forall_gt_imp_ge_of_dense fun c' hc' => ?_
    induction c' using EReal.rec with
    | bot => exact absurd hc' not_lt_bot
    | coe r =>
        have hr : c < r := by exact_mod_cast hc'
        refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
        filter_upwards [h (r - c) (by linarith)] with N hN
        exact_mod_cast (by linarith : f N ≤ r)
    | top => exact le_top

/-- **DEF-031 energy preparation** (with DEF-028 norm closeness), literally: `ψ_N` normalized in the
DEF-004 sector `H_N = Sym^N L²(𝕋_L)`, `‖ψ_N − u^{⊗N}‖ → 0`, the wave function of `ψ_N` is an element
`x_N ∈ H¹_sym(𝕋_L^N)`, and `limsup_N 𝔥_N[x_N]/N ≤ I₃(u)` (in `EReal`). -/
structure EnergyPreparation (κ : ℝ) (u : L2T L) (ψ : ∀ N : ℕ, HilbertTensorPower ℂ (L2T L) N) :
    Prop where
  normClose : QuantumNLS.StrongSymbolDef.IsNormClosePrep ψ
    (fun N => (htpow N u : HilbertTensorPower ℂ (L2T L) N))
  mem_sector : ∀ N, ψ N ∈ physSector L N
  energy : ∃ x : ∀ N, PhysH1 L N, (∀ N, (x N).val = physUnitary (ψ N)) ∧
    (∀ N, x N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) ∧
    limsup (fun N : ℕ => ((hN κ N (x N) / N : ℝ) : EReal)) atTop ≤ ((I3 κ u : ℝ) : EReal)

/-- The `H¹` element in the energy clause is unique (it is the wave function). -/
theorem energy_witness_unique {ψ : ∀ N, HilbertTensorPower ℂ (L2T L) N}
    {x y : ∀ N, PhysH1 L N} (hx : ∀ N, (x N).val = physUnitary (ψ N))
    (hy : ∀ N, (y N).val = physUnitary (ψ N)) : x = y :=
  funext fun N => PhysH1.val_injective (L := L) (k := N) ((hx N).trans (hy N).symm)

/-- The energy clause agrees with the frozen `ProductEnergyPreparation.EnergyPrepared`. -/
theorem energy_iff_energyPrepared (κ : ℝ) (u : L2T L) (x : ∀ N, PhysH1 L N) :
    ((∀ N, x N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) ∧
      limsup (fun N : ℕ => ((hN κ N (x N) / N : ℝ) : EReal)) atTop ≤ ((I3 κ u : ℝ) : EReal)) ↔
    QuantumNLS.ProductEnergyPreparation.EnergyPrepared κ u x := by
  unfold QuantumNLS.ProductEnergyPreparation.EnergyPrepared
  rw [limsup_le_iff]
  rfl

/-- **Product check** (not a substitute): `ψ_N = u^{⊗N}` for unit `u ∈ H¹` is an energy
preparation (frozen `PhysicalProductPreparation`). -/
theorem product_energyPreparation {u : L2T L} (hu : ‖u‖ = 1)
    (hH : QuantumNLS.ProductEnergyPreparation.OneH1 u) (κ : ℝ) :
    EnergyPreparation κ u (fun N => (htpow N u : HilbertTensorPower ℂ (L2T L) N)) := by
  obtain ⟨hn, hsec, hval, -, hprep, -, -⟩ :=
    QuantumNLS.PhysicalProductPreparation.def031_product_preparation hu hH κ
  refine ⟨⟨hn, ?_⟩, hsec, ⟨QuantumNLS.ProductEnergyPreparation.productH1 hu hH,
    fun N => (hval N).1.symm, fun N => (hval N).2, ?_⟩⟩
  · simp only [sub_self, norm_zero]; exact tendsto_const_nhds
  · exact ((energy_iff_energyPrepared κ u _).2 hprep).2

/-! ## §3 `A_k`, `A_k^{1/2}`, `W = A_k^{-1/2}` on the `k`-particle carrier `(L²(𝕋_L))^{⊗̂k}` -/

section Carrier

variable (L) (k : ℕ)

/-- The `k`-particle physical carrier (DEF-030 marginals act here). -/
abbrev Xk : Type := HilbertTensorPower ℂ (L2T L) k

/-- Carrier unitary to momentum space `ℓ²(ℤ^k)` (physical product modes `∏ L^{-1/2}e^{2πiw_jx_j/L}`). -/
abbrev eK : Xk L k ≃ₗᵢ[ℂ] L2 (Mom k) := QuantumNLS.PhysicalEnergyTrace.tensorMomUnitary L k

/-- **`A_k = 1 − Σ_{j≤k} ∂²_{x_j}`** on the `k`-particle carrier (the self-adjoint `physAk`,
transported through the position unitary). -/
def AkT : Xk L k →ₗ.[ℂ] Xk L k :=
  QuantumNLS.SymmetricAkSpectrum.transportPMap physUnitary (physAk L k)

/-- `A_k^{1/2}` on the `k`-particle carrier. -/
def AhalfT : Xk L k →ₗ.[ℂ] Xk L k :=
  QuantumNLS.SymmetricAkSpectrum.transportPMap physUnitary (physAhalf L k)

/-- `W = A_k^{-1/2}` (the multiplier `(1 + Σ_j(2πw_j/L)²)^{-1/2}`, additive weight). -/
abbrev W : Xk L k →L[ℂ] Xk L k := QuantumNLS.PhysicalEnergyTrace.physW L k (eK L k)

variable {L k}

theorem AkT_isSelfAdjoint : IsSelfAdjoint (AkT L k) :=
  QuantumNLS.SymmetricAkSpectrum.transportPMap_isSelfAdjoint _ (physAk_isSelfAdjoint L k)

theorem AhalfT_isSelfAdjoint : IsSelfAdjoint (AhalfT L k) :=
  QuantumNLS.SymmetricAkSpectrum.transportPMap_isSelfAdjoint _ (physAhalf_isSelfAdjoint L k)

theorem eK_apply (x : Xk L k) : eK L k x = momUnitary L k (physUnitary x) := rfl

theorem eK_AkT (x : (AkT L k).domain) (w : Mom k) :
    (eK L k (AkT L k x) : Mom k → ℂ) w =
      (kinWeight L k w : ℂ) * (eK L k (x : Xk L k) : Mom k → ℂ) w := by
  change (momUnitary L k (physUnitary (physUnitary.symm
    (physAk L k ⟨physUnitary (x : Xk L k), x.2⟩))) : Mom k → ℂ) w = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact momUnitary_physAk ⟨physUnitary (x : Xk L k), x.2⟩ w

theorem eK_AhalfT (x : (AhalfT L k).domain) (w : Mom k) :
    (eK L k (AhalfT L k x) : Mom k → ℂ) w =
      (kinSqrt L k w : ℂ) * (eK L k (x : Xk L k) : Mom k → ℂ) w := by
  change (momUnitary L k (physUnitary (physUnitary.symm
    (physAhalf L k ⟨physUnitary (x : Xk L k), x.2⟩))) : Mom k → ℂ) w = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact momUnitary_physAhalf ⟨physUnitary (x : Xk L k), x.2⟩ w

/-- **Domain of `A_k`**: all weak second partials `∂_j²` of the wave function in `L²`. -/
theorem mem_AkT_domain_iff (x : Xk L k) :
    x ∈ (AkT L k).domain ↔ ∀ j, ∃ H,
      QuantumNLS.ProductSecondDerivatives.HasWeakSecondPartial j j (physUnitary x) H :=
  QuantumNLS.ProductSecondDerivatives.mem_physAk_domain_iff_second _

/-- **Form domain `D(A_k^{1/2})`** = periodic weak `H¹`: all weak first partials in `L²`. -/
theorem mem_AhalfT_domain_iff (x : Xk L k) :
    x ∈ (AhalfT L k).domain ↔ ∀ j, ∃ G,
      QuantumNLS.ProductWeakDerivatives.HasWeakPartial j (physUnitary x) G := by
  show physUnitary x ∈ (physAhalf L k).domain ↔ _
  rw [← SetLike.mem_coe, ← PhysH1.range_val_eq_domain]
  exact QuantumNLS.ProductWeakDerivatives.mem_range_physH1_iff _

theorem eK_W (y : Xk L k) (w : Mom k) :
    (eK L k (W L k y) : Mom k → ℂ) w = (((kinSqrt L k w)⁻¹ : ℝ) : ℂ) * (eK L k y : Mom k → ℂ) w := by
  change (eK L k ((eK L k).symm (AhalfInv L k (eK L k y))) : Mom k → ℂ) w = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact invCLM_apply (one_le_kinSqrt L k) _ w

theorem W_mem (y : Xk L k) : W L k y ∈ (AhalfT L k).domain := by
  change (eK L k) ((eK L k).symm (AhalfInv L k (eK L k y))) ∈ (Ahalf L k).domain
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact invCLM_mem (one_le_kinSqrt L k) _

theorem AhalfT_W (y : Xk L k) : AhalfT L k ⟨W L k y, W_mem y⟩ = y := by
  apply (eK L k).injective
  ext w
  rw [eK_AhalfT]
  erw [eK_W]
  have h := m_ne_zero (one_le_kinSqrt L k) w
  push_cast
  field_simp

theorem W_AhalfT (f : (AhalfT L k).domain) : W L k (AhalfT L k f) = f := by
  apply (eK L k).injective
  ext w
  rw [eK_W, eK_AhalfT]
  have h := m_ne_zero (one_le_kinSqrt L k) w
  push_cast
  field_simp

/-- `W² A_k = 1` on `D(A_k)`: `W` is the inverse square root of `A_k`. -/
theorem W_W_AkT (x : (AkT L k).domain) : W L k (W L k (AkT L k x)) = x := by
  apply (eK L k).injective
  ext w
  rw [eK_W, eK_W, eK_AkT, ← kinSqrt_sq L k w]
  have h := m_ne_zero (one_le_kinSqrt L k) w
  push_cast
  field_simp

theorem W_inner (x y : Xk L k) : ⟪W L k x, y⟫_ℂ = ⟪x, W L k y⟫_ℂ := by
  change ⟪(eK L k).symm (AhalfInv L k (eK L k x)), y⟫_ℂ =
    ⟪x, (eK L k).symm (AhalfInv L k (eK L k y))⟫_ℂ
  rw [QuantumNLS.PhysicalEnergyTrace.inner_symm_left, QuantumNLS.PhysicalEnergyTrace.inner_symm_right]
  exact inner_invCLM (one_le_kinSqrt L k) _ _

/-! ## §4 The trace-class form realization of `A_k^{1/2} D A_k^{1/2}` -/

/-- **Form realization**: a bounded `T` with `⟨f, T g⟩ = ⟨A_k^{1/2} f, D A_k^{1/2} g⟩` for all
`f, g` in the form domain `D(A_k^{1/2})` (no operator-domain restriction). -/
def IsFormRealization (D T : Xk L k →L[ℂ] Xk L k) : Prop :=
  ∀ f g : (AhalfT L k).domain, ⟪(f : Xk L k), T g⟫_ℂ = ⟪AhalfT L k f, D (AhalfT L k g)⟫_ℂ

/-- **Characterization (both directions):** `T` is a form realization of `D` iff `D = W T W`. -/
theorem isFormRealization_iff (D T : Xk L k →L[ℂ] Xk L k) :
    IsFormRealization D T ↔ D = W L k * T * W L k := by
  constructor
  · intro h
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
    have hxy := h ⟨W L k x, W_mem x⟩ ⟨W L k y, W_mem y⟩
    rw [AhalfT_W, AhalfT_W] at hxy
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, ← W_inner]
    exact hxy.symm
  · rintro rfl f g
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, W_AhalfT g, ← W_inner, W_AhalfT f]

/-- **Uniqueness** of the form realization. -/
theorem formRealization_unique {D T₁ T₂ : Xk L k →L[ℂ] Xk L k} (h₁ : IsFormRealization D T₁)
    (h₂ : IsFormRealization D T₂) : T₁ = T₂ :=
  QuantumNLS.EnergyForm.eq_of_mul_mul_eq
    (QuantumNLS.PhysicalEnergyTrace.physW_injective L k (eK L k))
    (QuantumNLS.PhysicalEnergyTrace.physW_denseRange L k (eK L k))
    (((isFormRealization_iff D T₁).1 h₁).symm.trans ((isFormRealization_iff D T₂).1 h₂))

/-- **The additive energy trace norm** `‖A_k^{1/2} D A_k^{1/2}‖₁` (infimum of `‖T‖₁` over form
realizations, `⊤` if none; by uniqueness it is the trace norm of the realization). -/
def additiveEnergyTraceNorm (D : Xk L k →L[ℂ] Xk L k) : ℝ≥0∞ :=
  QuantumNLS.EnergyForm.energyTraceNorm (W L k) D

theorem additiveEnergyTraceNorm_eq {D T : Xk L k →L[ℂ] Xk L k} (h : IsFormRealization D T) :
    additiveEnergyTraceNorm D = QuantumNLS.TraceClass.traceNorm T :=
  QuantumNLS.EnergyForm.energyTraceNorm_eq
    (QuantumNLS.PhysicalEnergyTrace.physW_injective L k (eK L k))
    (QuantumNLS.PhysicalEnergyTrace.physW_denseRange L k (eK L k))
    ((isFormRealization_iff D T).1 h)

theorem additiveEnergyTraceNorm_eq_top {D : Xk L k →L[ℂ] Xk L k}
    (h : ∀ T, ¬ IsFormRealization D T) : additiveEnergyTraceNorm D = ⊤ :=
  QuantumNLS.EnergyForm.energyTraceNorm_eq_top fun T hT => h T ((isFormRealization_iff D T).2 hT)

/-- **Exact domain for differences (no positivity/finite-energy decomposition assumed):** a bounded
`D` admits a trace-class form realization iff its additive energy trace norm is finite, iff
`D = W T W` for a (unique) trace-class `T`. -/
theorem exists_traceClass_formRealization_iff (D : Xk L k →L[ℂ] Xk L k) :
    (∃ T, QuantumNLS.TraceClass.IsTraceClass T ∧ IsFormRealization D T) ↔
      additiveEnergyTraceNorm D < ⊤ := by
  constructor
  · rintro ⟨T, hT, hr⟩
    rw [additiveEnergyTraceNorm_eq hr]; exact hT
  · intro h
    by_cases hex : ∃ T, IsFormRealization D T
    · obtain ⟨T, hT⟩ := hex
      refine ⟨T, ?_, hT⟩
      show QuantumNLS.TraceClass.traceNorm T < ⊤
      rw [← additiveEnergyTraceNorm_eq hT]; exact h
    · simp only [not_exists] at hex
      rw [additiveEnergyTraceNorm_eq_top hex] at h
      exact absurd h (lt_irrefl _)

theorem exists_traceClass_formRealization_iff' (D : Xk L k →L[ℂ] Xk L k) :
    (∃ T, QuantumNLS.TraceClass.IsTraceClass T ∧ IsFormRealization D T) ↔
      ∃ T, QuantumNLS.TraceClass.IsTraceClass T ∧ D = W L k * T * W L k := by
  simp_rw [isFormRealization_iff]

/-- `‖D‖₁ ≤ ‖A_k^{1/2} D A_k^{1/2}‖₁`. -/
theorem traceNorm_le_additive (D : Xk L k →L[ℂ] Xk L k) :
    QuantumNLS.TraceClass.traceNorm D ≤ additiveEnergyTraceNorm D := by
  refine (QuantumNLS.EnergyForm.traceNorm_le_energyTraceNorm
    (QuantumNLS.PhysicalEnergyTrace.physW_injective L k (eK L k))
    (QuantumNLS.PhysicalEnergyTrace.physW_denseRange L k (eK L k)) D).trans ?_
  have h1 : ENNReal.ofReal (‖W L k‖ ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have := QuantumNLS.PhysicalEnergyTrace.norm_physW_le (L := L) (k := k) (eK L k)
    nlinarith [norm_nonneg (W L k)]
  calc ENNReal.ofReal (‖W L k‖ ^ 2) * additiveEnergyTraceNorm D
      ≤ 1 * additiveEnergyTraceNorm D := by gcongr
    _ = _ := one_mul _

/-- `Tr(A_k ρ) = Σ_w a_k(w) ⟨E_w, ρ E_w⟩` (physical product modes, additive weight). -/
abbrev energyTrace (ρ : Xk L k →L[ℂ] Xk L k) : ℝ≥0∞ :=
  QuantumNLS.PhysicalEnergyTrace.physTrace L k (eK L k) ρ

/-- **Positive finite-energy `ρ`**: the form realization exists, is positive trace class, and
`‖A_k^{1/2} ρ A_k^{1/2}‖₁ = Tr(A_k ρ)`. -/
theorem positive_formRealization {ρ : Xk L k →L[ℂ] Xk L k} (hρ : ρ.IsPositive)
    (hE : energyTrace ρ ≠ ⊤) :
    ∃ T, T.IsPositive ∧ QuantumNLS.TraceClass.IsTraceClass T ∧ IsFormRealization ρ T ∧
      QuantumNLS.TraceClass.posTrace T = energyTrace ρ ∧ additiveEnergyTraceNorm ρ = energyTrace ρ := by
  obtain ⟨T, hT, htc, hs, htr⟩ := QuantumNLS.PhysicalEnergyTrace.phys_realization hρ hE
  exact ⟨T, hT, htc, (isFormRealization_iff ρ T).2 hs, htr,
    QuantumNLS.PhysicalEnergyTrace.phys_energyTraceNorm hρ hE⟩

/-! ## §5 Positive finite-energy `ρ`: the spectral series, for every decomposition -/

/-- Energy of a vector, `Σ_w a_k(w)|f̂(w)|² ∈ [0,∞]` (`= ‖A_k^{1/2}f‖²` on the form domain). -/
def vecEnergy (f : Xk L k) : ℝ≥0∞ :=
  ∑' w, ENNReal.ofReal (kinWeight L k w * ‖(eK L k f : Mom k → ℂ) w‖ ^ 2)

theorem tsum_ofReal_ne_top_iff {ι : Type*} {g : ι → ℝ} (hg : ∀ i, 0 ≤ g i) :
    (∑' i, ENNReal.ofReal (g i)) ≠ ⊤ ↔ Summable g := by
  change (∑' i, ((g i).toNNReal : ℝ≥0∞)) ≠ ⊤ ↔ _
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
  simp_rw [Real.coe_toNNReal _ (hg _)]

/-- `f` lies in the form domain iff its energy is finite. -/
theorem vecEnergy_ne_top_iff (f : Xk L k) : vecEnergy f ≠ ⊤ ↔ f ∈ (AhalfT L k).domain := by
  rw [vecEnergy, tsum_ofReal_ne_top_iff (fun w => mul_nonneg
    (zero_le_one.trans (one_le_kinWeight L k w)) (sq_nonneg _))]
  show _ ↔ physUnitary f ∈ (physAhalf L k).domain
  rw [mem_physAhalf_domain_iff]
  rfl

/-- On the form domain, `vecEnergy f = ‖A_k^{1/2} f‖²`. -/
theorem vecEnergy_eq (f : (AhalfT L k).domain) :
    vecEnergy (f : Xk L k) = ENNReal.ofReal (‖AhalfT L k f‖ ^ 2) := by
  have hsum : Summable fun w => kinWeight L k w * ‖(eK L k (f : Xk L k) : Mom k → ℂ) w‖ ^ 2 :=
    (tsum_ofReal_ne_top_iff (fun w => mul_nonneg
      (zero_le_one.trans (one_le_kinWeight L k w)) (sq_nonneg _))).1
      ((vecEnergy_ne_top_iff _).2 f.2)
  rw [vecEnergy, ← ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg
    (zero_le_one.trans (one_le_kinWeight L k w)) (sq_nonneg _)) hsum,
    ← (eK L k).norm_map, QuantumNLS.Energy.norm_sq_eq_tsum]
  congr 1; congr 1; funext w
  rw [eK_AhalfT, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, kinSqrt_sq]

/-- `⟨E_w, x⟩ = x̂(w)` for the physical product mode `E_w` on the carrier. -/
theorem inner_mode (w : Mom k) (x : Xk L k) :
    ⟪(eK L k).symm (QuantumNLS.EnergyRealization.ev w), x⟫_ℂ = (eK L k x : Mom k → ℂ) w := by
  rw [QuantumNLS.PhysicalEnergyTrace.inner_symm_left, QuantumNLS.EnergyRealization.inner_ev_left]

/-- A (strongly convergent) decomposition `ρ x = Σ_j λ_j ⟨f_j, x⟩ f_j`. -/
def IsDecomposition (ρ : Xk L k →L[ℂ] Xk L k) (lam : ℕ → ℝ) (fs : ℕ → Xk L k) : Prop :=
  (∀ j, 0 ≤ lam j) ∧ ∀ x, HasSum (fun j => ((lam j : ℂ) * ⟪fs j, x⟫_ℂ) • fs j) (ρ x)

theorem isPositive_of_decomposition {ρ : Xk L k →L[ℂ] Xk L k} {lam : ℕ → ℝ} {fs : ℕ → Xk L k}
    (h : IsDecomposition ρ lam fs) : ρ.IsPositive := by
  obtain ⟨hlam, hdec⟩ := h
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · show ⟪ρ u, v⟫_ℂ = ⟪u, ρ v⟫_ℂ
    have h1 := Complex.hasSum_conj'.2 ((hdec u).mapL (innerSL ℂ v))
    have h2 := (hdec v).mapL (innerSL ℂ u)
    rw [← inner_conj_symm]
    refine h1.unique (h2.congr_fun fun j => ?_)
    simp only [innerSL_apply_apply, inner_smul_right, map_mul, Complex.conj_ofReal,
      inner_conj_symm]
    ring
  · show 0 ≤ RCLike.re ⟪ρ u, u⟫_ℂ
    have h2 := Complex.reCLM.hasSum ((hdec u).mapL (innerSL ℂ u))
    rw [← inner_conj_symm, RCLike.conj_re]
    refine h2.nonneg fun j => ?_
    simp only [innerSL_apply_apply, inner_smul_right, Complex.reCLM_apply]
    rw [← inner_conj_symm (fs j) u, mul_assoc, Complex.conj_mul']
    rw [show ((lam j : ℂ) * ((‖⟪u, fs j⟫_ℂ‖ : ℂ) ^ 2)) = ((lam j * ‖⟪u, fs j⟫_ℂ‖ ^ 2 : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
    exact mul_nonneg (hlam j) (sq_nonneg _)

/-- **`Tr(A_k ρ) = Σ_j λ_j ‖A_k^{1/2} f_j‖²`** for every decomposition (basis independence of the
energy trace; `‖A_k^{1/2} f‖²` read as `vecEnergy f`, `⊤` off the form domain). -/
theorem energyTrace_eq_series {ρ : Xk L k →L[ℂ] Xk L k} {lam : ℕ → ℝ} {fs : ℕ → Xk L k}
    (h : IsDecomposition ρ lam fs) :
    energyTrace ρ = ∑' j, ENNReal.ofReal (lam j) * vecEnergy (fs j) := by
  obtain ⟨hlam, hdec⟩ := h
  unfold energyTrace
  rw [QuantumNLS.PhysicalEnergyTrace.physTrace_eq_modes]
  set E : Mom k → Xk L k := fun w => (eK L k).symm (QuantumNLS.EnergyRealization.ev w)
  have hw : ∀ w, HasSum (fun j => lam j * ‖(eK L k (fs j) : Mom k → ℂ) w‖ ^ 2)
      (RCLike.re ⟪E w, ρ (E w)⟫_ℂ) := by
    intro w
    have h2 := Complex.reCLM.hasSum ((hdec (E w)).mapL (innerSL ℂ (E w)))
    refine h2.congr_fun fun j => ?_
    simp only [innerSL_apply_apply, inner_smul_right, Complex.reCLM_apply]
    rw [← inner_conj_symm (fs j) (E w), mul_assoc, Complex.conj_mul', inner_mode]
    rw [show ((lam j : ℂ) * ((‖(eK L k (fs j) : Mom k → ℂ) w‖ : ℂ) ^ 2)) =
      ((lam j * ‖(eK L k (fs j) : Mom k → ℂ) w‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  have hterm : ∀ w, ENNReal.ofReal (kinWeight L k w * RCLike.re ⟪E w, ρ (E w)⟫_ℂ) =
      ∑' j, ENNReal.ofReal (lam j) *
        ENNReal.ofReal (kinWeight L k w * ‖(eK L k (fs j) : Mom k → ℂ) w‖ ^ 2) := by
    intro w
    have hk : 0 ≤ kinWeight L k w := zero_le_one.trans (one_le_kinWeight L k w)
    have hs := (hw w).mul_left (kinWeight L k w)
    rw [← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg hk
      (mul_nonneg (hlam j) (sq_nonneg _))) hs.summable]
    congr 1; funext j
    rw [← ENNReal.ofReal_mul (hlam j)]
    congr 1; ring
  refine (tsum_congr fun w => hterm w).trans ?_
  rw [ENNReal.tsum_comm]
  congr 1; funext j
  rw [ENNReal.tsum_mul_left]
  rfl

/-- Positive-mass terms of a finite-energy decomposition lie in the form domain. -/
theorem mem_domain_of_decomposition {ρ : Xk L k →L[ℂ] Xk L k} {lam : ℕ → ℝ}
    {fs : ℕ → Xk L k} (h : IsDecomposition ρ lam fs) (hE : energyTrace ρ ≠ ⊤) {j : ℕ}
    (hj : 0 < lam j) : fs j ∈ (AhalfT L k).domain := by
  rw [← vecEnergy_ne_top_iff]
  intro htop
  apply hE
  rw [energyTrace_eq_series h, eq_top_iff]
  calc ⊤ = ENNReal.ofReal (lam j) * vecEnergy (fs j) := by
        rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hj).ne']
    _ ≤ ∑' j, ENNReal.ofReal (lam j) * vecEnergy (fs j) :=
        ENNReal.le_tsum (f := fun j => ENNReal.ofReal (lam j) * vecEnergy (fs j)) j

open Classical in
/-- `A_k^{1/2} f_j` (set to `0` off the form domain; such terms carry `λ_j = 0`). -/
def halfVec (f : Xk L k) : Xk L k :=
  if h : f ∈ (AhalfT L k).domain then AhalfT L k ⟨f, h⟩ else 0

theorem W_rankOne (g : Xk L k) :
    W L k * InnerProductSpace.rankOne ℂ g g * W L k =
      InnerProductSpace.rankOne ℂ (W L k g) (W L k g) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, InnerProductSpace.rankOne_apply,
    InnerProductSpace.rankOne_apply, map_smul, ← W_inner]

/-- **Spectral series (energy_trace.tex:15-26).** Let `ρ` be given by ANY decomposition
`ρ = Σ_j λ_j |f_j⟩⟨f_j|` (`λ_j ≥ 0`, strong convergence) with `Tr(A_kρ) < ∞`, and let `T` be the
(unique) form realization of `ρ`. Then every `f_j` with `λ_j > 0` lies in the form domain and
`Σ_{j<n} λ_j |A_k^{1/2}f_j⟩⟨A_k^{1/2}f_j| → T` in trace norm. No range-in-`dom(A_k)` hypothesis;
the limit is independent of the decomposition. -/
theorem realization_series {ρ : Xk L k →L[ℂ] Xk L k} {lam : ℕ → ℝ} {fs : ℕ → Xk L k}
    (h : IsDecomposition ρ lam fs) (hE : energyTrace ρ ≠ ⊤) {T : Xk L k →L[ℂ] Xk L k}
    (hT : IsFormRealization ρ T) :
    Tendsto (fun n => QuantumNLS.TraceClass.traceNorm (T - ∑ j ∈ Finset.range n,
        (lam j : ℂ) • InnerProductSpace.rankOne ℂ (halfVec (fs j)) (halfVec (fs j))))
      atTop (𝓝 0) := by
  obtain ⟨hlam, hdec⟩ := h
  set a : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (lam j) * vecEnergy (fs j) with ha
  have hsum : ∑' j, a j ≠ ⊤ := by rw [← energyTrace_eq_series ⟨hlam, hdec⟩]; exact hE
  set term : Xk L k → ℕ → Xk L k := fun x j => ((lam j : ℂ) * ⟪fs j, x⟫_ℂ) • fs j
  have hWg : ∀ j, (lam j : ℂ) • InnerProductSpace.rankOne ℂ (W L k (halfVec (fs j)))
      (W L k (halfVec (fs j))) = (lam j : ℂ) • InnerProductSpace.rankOne ℂ (fs j) (fs j) := by
    intro j
    rcases (hlam j).lt_or_eq with hj | hj
    · have hm := mem_domain_of_decomposition ⟨hlam, hdec⟩ hE hj
      have : W L k (halfVec (fs j)) = fs j := by
        have hv : halfVec (fs j) = AhalfT L k ⟨fs j, hm⟩ := by unfold halfVec; simp [hm]
        rw [hv, W_AhalfT]
      rw [this]
    · rw [← hj]; simp
  have hn : ∀ n, QuantumNLS.TraceClass.traceNorm (T - ∑ j ∈ Finset.range n,
      (lam j : ℂ) • InnerProductSpace.rankOne ℂ (halfVec (fs j)) (halfVec (fs j))) =
      ∑' i, a (i + n) := by
    intro n
    set S := ∑ j ∈ Finset.range n,
      (lam j : ℂ) • InnerProductSpace.rankOne ℂ (halfVec (fs j)) (halfVec (fs j))
    set ρn := ∑ j ∈ Finset.range n, (lam j : ℂ) • InnerProductSpace.rankOne ℂ (fs j) (fs j)
    have hWS : W L k * S * W L k = ρn := by
      simp only [S, ρn, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, W_rankOne,
        hWg]
    have hρn : ∀ x, ρn x = ∑ j ∈ Finset.range n, term x j := by
      intro x
      simp only [ρn, term, FunLike.coe_sum, Finset.sum_apply,
        FunLike.coe_smul, Pi.smul_apply, InnerProductSpace.rankOne_apply, smul_smul]
    have htail : IsDecomposition (ρ - ρn) (fun i => lam (i + n)) (fun i => fs (i + n)) := by
      refine ⟨fun i => hlam _, fun x => ?_⟩
      have := (hasSum_nat_add_iff' n).2 (hdec x)
      rw [FunLike.coe_sub, Pi.sub_apply, hρn]
      exact this
    have hpos := isPositive_of_decomposition htail
    have hEt : energyTrace (ρ - ρn) = ∑' i, a (i + n) := energyTrace_eq_series htail
    have hEt' : energyTrace (ρ - ρn) ≠ ⊤ := by
      rw [hEt]
      exact ne_top_of_le_ne_top hsum
        (ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective n) a)
    have hreal : IsFormRealization (ρ - ρn) (T - S) := by
      rw [isFormRealization_iff, mul_sub, sub_mul, ← (isFormRealization_iff ρ T).1 hT, hWS]
    rw [← additiveEnergyTraceNorm_eq hreal]
    obtain ⟨_, _, _, _, _, hval⟩ := positive_formRealization hpos hEt'
    rw [hval, hEt]
  simp_rw [hn]
  exact ENNReal.tendsto_sum_nat_add a hsum

/-- **Existence, positivity, value and decomposition-independence** for positive finite-energy `ρ`:
the realization `T` exists, is positive trace class, is unique, `Tr T = Tr(A_kρ) = ‖A_k^{1/2}ρA_k^{1/2}‖₁`,
and for EVERY decomposition the series converges to this same `T` in trace norm. -/
theorem positive_realization_spectral {ρ : Xk L k →L[ℂ] Xk L k} {lam : ℕ → ℝ}
    {fs : ℕ → Xk L k} (h : IsDecomposition ρ lam fs) (hE : energyTrace ρ ≠ ⊤) :
    ∃ T, T.IsPositive ∧ QuantumNLS.TraceClass.IsTraceClass T ∧ IsFormRealization ρ T ∧
      (∀ T', IsFormRealization ρ T' → T' = T) ∧
      QuantumNLS.TraceClass.posTrace T = energyTrace ρ ∧
      additiveEnergyTraceNorm ρ = energyTrace ρ ∧
      energyTrace ρ = ∑' j, ENNReal.ofReal (lam j) * vecEnergy (fs j) ∧
      Tendsto (fun n => QuantumNLS.TraceClass.traceNorm (T - ∑ j ∈ Finset.range n,
        (lam j : ℂ) • InnerProductSpace.rankOne ℂ (halfVec (fs j)) (halfVec (fs j))))
        atTop (𝓝 0) := by
  obtain ⟨T, hT, htc, hr, htr, hval⟩ :=
    positive_formRealization (isPositive_of_decomposition h) hE
  exact ⟨T, hT, htc, hr, fun T' hT' => formRealization_unique hT' hr, htr, hval,
    energyTrace_eq_series h, realization_series h hE hr⟩

/-! ## §6 The product instance (check) and the DEF-030 marginal difference -/

/-- **Product check:** for unit `u ∈ H¹`, the actual marginal `γ_N^{(k)}(u^{⊗N})` minus the
projector onto `u^{⊗k}` has additive energy trace norm `0` (a form realization exists: `T = 0`). -/
theorem product_marginal_check {u : L2T L} (hu : ‖u‖ = 1)
    (hH : QuantumNLS.ProductEnergyPreparation.OneH1 u) {N : ℕ} (hk : k ≤ N) :
    IsFormRealization (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) 0 ∧
    additiveEnergyTraceNorm (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) = 0 := by
  obtain ⟨-, -, -, hD, h0, -⟩ := QuantumNLS.PhysicalProductPreparation.def031_marginal_product hu hH hk
  refine ⟨?_, h0⟩
  rw [isFormRealization_iff, hD]
  simp

end Carrier

end QuantumNLS.EnergyPreparationDef

#print axioms QuantumNLS.EnergyPreparationDef.I3_eq
#print axioms QuantumNLS.EnergyPreparationDef.hN_literal
#print axioms QuantumNLS.EnergyPreparationDef.contact_form_operator
#print axioms QuantumNLS.EnergyPreparationDef.energy_iff_energyPrepared
#print axioms QuantumNLS.EnergyPreparationDef.product_energyPreparation
#print axioms QuantumNLS.EnergyPreparationDef.AkT_isSelfAdjoint
#print axioms QuantumNLS.EnergyPreparationDef.mem_AkT_domain_iff
#print axioms QuantumNLS.EnergyPreparationDef.mem_AhalfT_domain_iff
#print axioms QuantumNLS.EnergyPreparationDef.W_W_AkT
#print axioms QuantumNLS.EnergyPreparationDef.isFormRealization_iff
#print axioms QuantumNLS.EnergyPreparationDef.formRealization_unique
#print axioms QuantumNLS.EnergyPreparationDef.exists_traceClass_formRealization_iff
#print axioms QuantumNLS.EnergyPreparationDef.positive_formRealization
#print axioms QuantumNLS.EnergyPreparationDef.energyTrace_eq_series
#print axioms QuantumNLS.EnergyPreparationDef.realization_series
#print axioms QuantumNLS.EnergyPreparationDef.positive_realization_spectral
#print axioms QuantumNLS.EnergyPreparationDef.product_marginal_check
