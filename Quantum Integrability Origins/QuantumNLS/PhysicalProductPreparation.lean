import QuantumNLS.ProductEnergyPreparation
import QuantumNLS.CollisionIdentification
import QuantumNLS.PhysicalEnergyTrace

/-!
# DEF-031 for product states on the physical carriers: real diagonal term, smooth class, marginals

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`): DEF-031 (`definitions.tex:189`),
`A01.tex:13` (collision trace on `dy_ij`), `energy_trace.tex:15–26` (additive energy trace norm,
`A_k = 1 + Σ D_j²`), DEF-003/005.

Frozen imports (read-only): `ProductEnergyPreparation` (`ee167ded…`: energy half, `productH1`,
`EnergyPrepared`), `CollisionIdentification` (`ffd608f4…`: `productTrace` into the literal
`L²(dy_ij)`, `gradientCLM`, `q_eq_physical_pairings`), `PhysicalEnergyTrace` (`67f87c5d…`:
`physTrace`, `physW`, `energyTraceNorm`), and through them `ChargeEnergy` (`8b11b1df…`),
`ContactForm`, `CollisionTrace`, `ClassicalCharges`.

What is proved (no general preparation, no dynamics/conservation assumed):
* `norm_sq_productTrace_product`, `hN_physical(_product)`: the contact term of `u^{⊗N}` is the
  `L²(dy_ij)` norm of Sol's literal trace, `‖T_ijΨ_N‖²_{L²(dy_ij)} = ∫|u|⁴`; `h_N[Ψ_N]` in the
  physical real-space form `Σ_j ‖∂_jΨ_N‖² + (2κ/N) Σ_{i<j} ‖T_ijΨ_N‖²_{L²(dy_ij)}`, kinetic part
  `K(u)` per coordinate.
* `smoothClass`, `oneH1_smooth`, `norm_smoothClass_eq_one`: packaging of `OneH1` for the class of a
  smooth periodic profile; `smooth_def031`: DEF-022 `I₃ = charge L κ ũ 3 = E_κ`, limit, exact
  correction and `EnergyPrepared` for smooth unit profiles.
* `physTrace_proj`: `Tr(A_k |u^{⊗k}⟩⟨u^{⊗k}|) = 1 + k K(u)`; `marginal_product`:
  `γ_N^{(k)}(u^{⊗N}) = |u^{⊗k}⟩⟨u^{⊗k}|`; `def031_marginal_product`: both terms positive with finite
  energy, difference `0`, additive energy trace norm `‖A_k^{1/2} D A_k^{1/2}‖₁ = 0`, trace norm `0`
  (via `PhysicalEnergyTrace`); `def031_marginal_tendsto`; `marginal_trace_one`.
* `def031_product_preparation`: bundled norm-close + `H¹_sym` + energy + marginal parts.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal
open MeasureTheory

namespace QuantumNLS.PhysicalProductPreparation

open QuantumNLS.PhysicalEnergy QuantumNLS.PhysicalTensor QuantumNLS.Energy
  QuantumNLS.CollisionTrace QuantumNLS.Fourier QuantumNLS.ContactForm QuantumNLS.ChargeEnergy
  QuantumNLS.TensorCarrier QuantumNLS.ProductEnergyPreparation QuantumNLS.CollisionIdentification

variable {L : ℝ} [Fact (0 < L)]

/-! ## Part 1: `OneH1` for the class of a smooth profile -/

/-- The `L²(𝕋_L)` class of a smooth periodic profile. -/
def smoothClass {ũ : ℝ → ℂ} (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ) : L2T L :=
  ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
    (QuantumNLS.WeakDerivatives.liftC hu.smooth.continuous hu.periodic)

theorem smoothClass_ae {ũ : ℝ → ℂ} (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ) :
    (smoothClass hu : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))]
      (QuantumNLS.WeakDerivatives.liftC hu.smooth.continuous hu.periodic : AddCircle L → ℂ) :=
  ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (volume : Measure (AddCircle L)) _

/-- **`OneH1` for a smooth profile class**: the report Fourier coefficients of a smooth periodic
profile have finite `H¹` weight. -/
theorem oneH1_smooth {ũ : ℝ → ℂ} (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ) :
    OneH1 (smoothClass hu) := by
  have h := QuantumNLS.ChargeEnergy.smooth_h04 hu
  have hco : ∀ n, fourierL2 L (smoothClass hu) n =
      coeff L (QuantumNLS.WeakDerivatives.liftC hu.smooth.continuous hu.periodic :
        AddCircle L → ℂ) n := fun n => by
    rw [fourierL2_apply]; exact coeff_congr_ae L (smoothClass_ae hu) n
  unfold OneH1
  simp_rw [hco]
  exact h.2

/-- `‖class‖² = ∫₀^L |ũ|²` (DEF-022 `I₁`). -/
theorem norm_sq_smoothClass {ũ : ℝ → ℂ} (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ) :
    ‖smoothClass hu‖ ^ 2 = ∫ x in (0 : ℝ)..L, ‖ũ x‖ ^ 2 := by
  have h1 := QuantumNLS.ClassicalCharges.charge_one_L2 (L := L) 0 hu
  have h2 := QuantumNLS.ClassicalCharges.charge_one L 0 ũ
  have : (((‖smoothClass hu‖ ^ 2 : ℝ)) : ℂ) = (((∫ x in (0 : ℝ)..L, ‖ũ x‖ ^ 2 : ℝ)) : ℂ) :=
    h1.symm.trans h2
  exact_mod_cast this

theorem norm_smoothClass_eq_one {ũ : ℝ → ℂ} (hu : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ)
    (hm : ∫ x in (0 : ℝ)..L, ‖ũ x‖ ^ 2 = 1) : ‖smoothClass hu‖ = 1 := by
  have h := norm_sq_smoothClass hu
  rw [hm] at h
  nlinarith [norm_nonneg (smoothClass hu)]

/-! ## Part 2: the real-space diagonal contact term -/

section Diagonal

variable {N : ℕ}

/-- **Real diagonal contact term.**  The collision trace of `u^{⊗N}` as an element of the literal
`L²(dy_{ij})` (common coordinate × the other `N−2` circles, mass `L` each; Sol's
`productTrace`, the continuous extension of the restriction of smooth functions) has
`‖T_ij Ψ_N‖²_{L²(dy_ij)} = ∫|u|⁴`. -/
theorem norm_sq_productTrace_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u)
    (i j : Fin N) (hij : i ≠ j) :
    ‖productTrace i j hij (productH1 hu hH N)‖ ^ 2 = quartic (u : AddCircle L → ℂ) := by
  rw [productTrace_norm, traceCLM_apply]
  exact norm_sq_trace_product i j hij hu hH

theorem norm_gradientCLM (i : Fin N) (x : PhysH1 L N) : ‖gradientCLM i x‖ = ‖Dj i x‖ := by
  have h := gradientCLM_inner i x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have : ‖gradientCLM i x‖ ^ 2 = ‖Dj i x‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this

/-- `h_N` in the physical real-space form: kinetic part `Σ_j ‖∂_jψ‖²_{L²(𝕋_L^N)}` plus
`(2κ/N) Σ_{i<j} ‖T_ijψ‖²_{L²(dy_ij)}`. -/
theorem hN_physical (κ : ℝ) (x : PhysH1 L N) :
    hN κ N x = ∑ j, ‖gradientCLM j x‖ ^ 2 +
      2 * (κ / N) * ∑ p : Pair N, ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) x‖ ^ 2 := by
  unfold hN
  rw [q_self, Complex.ofReal_re]
  have h1 : ∀ j, ‖gradientCLM j x‖ = ‖Dj j x‖ := fun j => norm_gradientCLM j x
  have h2 : ∀ p : Pair N, ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) x‖ = ‖Tpair p x‖ :=
    fun p => by unfold Tpair; rw [productTrace_norm]
  simp_rw [h1, h2]

/-- **`h_N` on `u^{⊗N}` in real-space form:** kinetic `N K(u)` and diagonal
`(2κ/N)·(N(N−1)/2)·∫|u|⁴` with each collision term the `L²(dy_ij)` norm of the restriction. -/
theorem hN_physical_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (κ : ℝ) :
    hN κ N (productH1 hu hH N) =
      ∑ j, ‖gradientCLM j (productH1 hu hH N)‖ ^ 2 +
        2 * (κ / N) * ∑ p : Pair N,
          ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) (productH1 hu hH N)‖ ^ 2 ∧
      (∀ j, ‖gradientCLM j (productH1 hu hH N)‖ ^ 2 = kinetic (u : AddCircle L → ℂ)) ∧
      (∀ p : Pair N, ‖productTrace p.1.1 p.1.2 (ne_of_lt p.2) (productH1 hu hH N)‖ ^ 2 =
        quartic (u : AddCircle L → ℂ)) :=
  ⟨hN_physical κ _, fun j => by rw [norm_gradientCLM, norm_sq_Dj_product hu hH],
    fun p => norm_sq_productTrace_product hu hH _ _ _⟩

end Diagonal

/-! ## Part 3: the marginal / energy-trace-norm part of DEF-031 for `u^{⊗N}` -/

section Marginal

open QuantumNLS.PhysicalEnergyTrace QuantumNLS.TraceClass QuantumNLS.EnergyForm

variable {k : ℕ}

theorem tensorMom_htpow (u : L2T L) (k : ℕ) :
    tensorMomUnitary L k (htpow k u : HilbertTensorPower ℂ (L2T L) k) =
      momUnitary L k (prodState u k) := by
  show momUnitary L k (physEmbed (htpow k u : HilbertTensorPower ℂ (L2T L) k)) = _
  rw [physEmbed_htpow]
  rfl

/-- **Finite kinetic energy of the projector onto `u^{⊗k}`**:
`Tr(A_k |u^{⊗k}⟩⟨u^{⊗k}|) = 1 + k K(u)` (`< ∞` for `u ∈ H¹`), on the tensor carrier of the
marginals. -/
theorem physTrace_proj {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (k : ℕ) :
    physTrace L k (tensorMomUnitary L k)
        (InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) =
      ENNReal.ofReal (1 + k * kinetic (u : AddCircle L → ℂ)) := by
  rw [physTrace_eq_modes]
  have hterm : ∀ w : Mom k, kinWeight L k w * RCLike.re
      ⟪(tensorMomUnitary L k).symm (EnergyRealization.ev w),
        InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)
          ((tensorMomUnitary L k).symm (EnergyRealization.ev w))⟫_ℂ =
      kinWeight L k w * ‖(momUnitary L k (prodState u k) : Mom k → ℂ) w‖ ^ 2 := fun w => by
    rw [InnerProductSpace.rankOne_apply, inner_smul_right, inner_symm_right,
      ← inner_conj_symm, EnergyRealization.inner_ev_left, inner_symm_left,
      EnergyRealization.inner_ev_left, tensorMom_htpow, Complex.conj_mul',
      ← Complex.ofReal_pow, RCLike.re_to_complex, Complex.ofReal_re]
  simp_rw [hterm]
  have h := hasSum_kinWeight_prod hu hH k
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun w => mul_nonneg (by linarith [one_le_kinWeight L k w]) (sq_nonneg _)) h.summable, h.tsum_eq]

/-- The actual `k`-marginal of `u^{⊗N}` is the projector onto `u^{⊗k}` (unit `u`). -/
theorem marginal_product {u : L2T L} (hu : ‖u‖ = 1) {N k : ℕ} (hk : k ≤ N) :
    reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) =
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u) := by
  rw [reducedDensityN_htpow, hu]
  simp

/-- **DEF-031 marginal/trace-norm part for `u^{⊗N}`** (unit `u ∈ H¹`, `k ≤ N`), on the tensor
carrier of the marginals, through `PhysicalEnergyTrace`: both the actual marginal `γ_N^{(k)}` and the
projector onto `u^{⊗k}` are positive with finite kinetic energy `Tr(A_k ·) = 1 + k K(u)`, their
difference is `0`, and its additive energy trace norm `‖A_k^{1/2} D A_k^{1/2}‖₁` and trace norm
are `0`. -/
theorem def031_marginal_product {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) {N k : ℕ} (hk : k ≤ N) :
    physTrace L k (tensorMomUnitary L k)
        (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N)) =
      ENNReal.ofReal (1 + k * kinetic (u : AddCircle L → ℂ)) ∧
    physTrace L k (tensorMomUnitary L k)
        (InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) =
      ENNReal.ofReal (1 + k * kinetic (u : AddCircle L → ℂ)) ∧
    (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N)).IsPositive ∧
    reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
        InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u) = 0 ∧
    energyTraceNorm (physW L k (tensorMomUnitary L k))
      (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
        InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) = 0 ∧
    traceNorm (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
        InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) = 0 := by
  have hm := marginal_product hu hk
  have hD : reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
      InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u) = 0 := by
    rw [hm, sub_self]
  refine ⟨by rw [hm]; exact physTrace_proj hu hH k, physTrace_proj hu hH k,
    reducedDensityN_isPositive N k hk _, hD, ?_, ?_⟩
  · rw [hD]
    exact energyTraceNorm_zero (physW_injective L k _) (physW_denseRange L k _)
  · rw [hD]
    exact (traceNorm_eq_zero_iff 0).mpr rfl

/-- Fixed `k`: the energy-trace distance of the marginals of `u^{⊗N}` to the projector tends to `0`
(it vanishes for all `N ≥ k`). -/
theorem def031_marginal_tendsto {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (k : ℕ) :
    Filter.Tendsto (fun N : ℕ => if hk : k ≤ N then
        energyTraceNorm (physW L k (tensorMomUnitary L k))
          (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
            InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u))
      else 0) Filter.atTop (nhds 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop k] with N hk
  simp only [hk, ↓reduceDIte]
  exact (def031_marginal_product hu hH hk).2.2.2.2.1.symm

end Marginal

/-! ## Part 4: bundled DEF-031 statement for the product preparation -/

section Bundle

open QuantumNLS.PhysicalEnergyTrace QuantumNLS.TraceClass QuantumNLS.EnergyForm

/-- **DEF-031 (norm-close + energy + marginal parts) for `ψ_N = u^{⊗N}`**, unit `u ∈ H¹`:
* `ψ_N` is normalized, symmetric (`physSector`) and its wave function is the `H¹_sym` element
  `productH1` (so `ψ_N ∈ H¹_sym`), and `‖ψ_N − u^{⊗N}‖ = 0`;
* the energy half: `EnergyPrepared κ u` (`limsup h_N[ψ_N]/N ≤ I₃(u)`, in fact `→ I₃(u)`), from
  `ProductEnergyPreparation` (the energy source is preserved, not reproved);
* the marginal part: for every `k ≤ N` the actual marginal and the projector onto `u^{⊗k}` have
  finite energy and their additive energy-trace-norm difference is `0`. -/
theorem def031_product_preparation {u : L2T L} (hu : ‖u‖ = 1) (hH : OneH1 u) (κ : ℝ) :
    (∀ N, ‖(htpow N u : HilbertTensorPower ℂ (L2T L) N)‖ = 1) ∧
    (∀ N, (htpow N u : HilbertTensorPower ℂ (L2T L) N) ∈ physSector L N) ∧
    (∀ N, physUnitary (htpow N u : HilbertTensorPower ℂ (L2T L) N) = (productH1 hu hH N).val ∧
      productH1 hu hH N ∈ (PhysH1.sym : Submodule ℂ (PhysH1 L N))) ∧
    (∀ N, ‖(htpow N u : HilbertTensorPower ℂ (L2T L) N) - htpow N u‖ = 0) ∧
    EnergyPrepared κ u (productH1 hu hH) ∧
    Filter.Tendsto (fun N : ℕ => hN κ N (productH1 hu hH N) / N) Filter.atTop
      (nhds (energyH1 κ (u : AddCircle L → ℂ))) ∧
    (∀ {N k : ℕ} (hk : k ≤ N),
      physTrace L k (tensorMomUnitary L k)
          (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N)) ≠ ⊤ ∧
      physTrace L k (tensorMomUnitary L k)
          (InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) ≠ ⊤ ∧
      energyTraceNorm (physW L k (tensorMomUnitary L k))
        (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N) -
          InnerProductSpace.rankOne ℂ (htpow k u : HilbertTensorPower ℂ (L2T L) k) (htpow k u)) = 0) := by
  have hval : ∀ N, physUnitary (htpow N u : HilbertTensorPower ℂ (L2T L) N) =
      (productH1 hu hH N).val := fun N => by
    rw [productH1_val]
    show physEmbed (htpow N u : HilbertTensorPower ℂ (L2T L) N) = _
    rw [physEmbed_htpow]; rfl
  obtain ⟨-, -, -, hlim, -, hprep⟩ := ProductEnergyPreparation.product_energyPrepared hu hH κ
  refine ⟨fun N => by rw [norm_htpow, hu]; simp, fun N => ?_, fun N => ⟨hval N, productH1_sym hu hH N⟩,
    fun N => by simp, hprep, hlim, fun {N k} hk => ?_⟩
  · rw [mem_physSector_iff, hval N]
    exact (PhysH1.mem_sym_iff _).1 (productH1_sym hu hH N)
  · obtain ⟨h1, h2, -, -, h5, -⟩ := def031_marginal_product hu hH hk
    exact ⟨by rw [h1]; exact ENNReal.ofReal_ne_top, by rw [h2]; exact ENNReal.ofReal_ne_top, h5⟩

/-- Normalization of the actual marginals of `u^{⊗N}`: `Tr γ_N^{(k)} = 1` in every Hilbert basis. -/
theorem marginal_trace_one {u : L2T L} (hu : ‖u‖ = 1) {N k : ℕ} (hk : k ≤ N) {ι : Type}
    (c : HilbertBasis ι ℂ (HilbertTensorPower ℂ (L2T L) k)) :
    traceIn c (reducedDensityN N k hk (htpow N u : HilbertTensorPower ℂ (L2T L) N)) = 1 :=
  traceIn_reducedDensityN_eq_one N k hk c _ (by rw [norm_htpow, hu]; simp)

/-- **Smooth profiles, all parts packaged.**  For a smooth periodic `ũ` with `∫₀^L |ũ|² = 1` (DEF-022
`I₁ = 1`), the class `u = smoothClass` is a unit `H¹` profile, `OneH1` holds, the DEF-022 charge
`I₃ = charge L κ ũ 3` equals the real `E_κ(u)`, and `h_N[u^{⊗N}]/N → I₃^{(κ)}(ũ)` with the
exact finite-`N` correction `I₃ − κ Q/N`. -/
theorem smooth_def031 {ũ : ℝ → ℂ} (hs : QuantumNLS.ClassicalCharges.SmoothPeriodic L ũ)
    (hm : ∫ x in (0 : ℝ)..L, ‖ũ x‖ ^ 2 = 1) (κ : ℝ) :
    QuantumNLS.ClassicalCharges.charge L κ ũ 3 =
      ((energyH1 κ (smoothClass hs : AddCircle L → ℂ) : ℝ) : ℂ) ∧
    Filter.Tendsto (fun N : ℕ => hN κ N
      (productH1 (norm_smoothClass_eq_one hs hm) (oneH1_smooth hs) N) / N) Filter.atTop
      (nhds (QuantumNLS.ClassicalCharges.charge L κ ũ 3).re) ∧
    (∀ N : ℕ, 1 ≤ N → hN κ N
      (productH1 (norm_smoothClass_eq_one hs hm) (oneH1_smooth hs) N) / N =
        (QuantumNLS.ClassicalCharges.charge L κ ũ 3).re -
          κ * quartic (smoothClass hs : AddCircle L → ℂ) / N) ∧
    EnergyPrepared κ (smoothClass hs) (productH1 (norm_smoothClass_eq_one hs hm) (oneH1_smooth hs)) := by
  have hc : QuantumNLS.ClassicalCharges.charge L κ ũ 3 =
      ((energyH1 κ (smoothClass hs : AddCircle L → ℂ) : ℝ) : ℂ) :=
    QuantumNLS.ProductEnergyPreparation.energyH1_smooth_class κ hs
  have hre : (QuantumNLS.ClassicalCharges.charge L κ ũ 3).re =
      energyH1 κ (smoothClass hs : AddCircle L → ℂ) := by rw [hc, Complex.ofReal_re]
  obtain ⟨-, -, hex, hlim, -, hprep⟩ :=
    ProductEnergyPreparation.product_energyPrepared (norm_smoothClass_eq_one hs hm)
      (oneH1_smooth hs) κ
  refine ⟨hc, ?_, ?_, hprep⟩
  · rw [hre]; exact hlim
  · intro N hN1; rw [hre]; exact hex N hN1

end Bundle

/-! Kernel axiom audit. -/
#print axioms oneH1_smooth
#print axioms norm_sq_smoothClass
#print axioms norm_smoothClass_eq_one
#print axioms norm_sq_productTrace_product
#print axioms norm_gradientCLM
#print axioms hN_physical
#print axioms hN_physical_product
#print axioms tensorMom_htpow
#print axioms physTrace_proj
#print axioms marginal_product
#print axioms def031_marginal_product
#print axioms def031_marginal_tendsto
#print axioms def031_product_preparation
#print axioms marginal_trace_one
#print axioms smooth_def031

end QuantumNLS.PhysicalProductPreparation
