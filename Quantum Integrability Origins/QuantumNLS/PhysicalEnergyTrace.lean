/-
QuantumNLS.PhysicalEnergyTrace — DEF-031 on the PHYSICAL k-particle carriers (owner: opus_tensor).

Source: DEF-031 (definitions.tex:187): "For fixed k, set A_k = 1 − Σ_{j≤k} ∂²_{x_j}.  The additive
energy trace norm of a difference D is ‖A_k^{1/2} D A_k^{1/2}‖₁, defined through the corresponding
trace-class form realization."  energy_trace.tex:18–26: positive ρ with Tr(A_k ρ) < ∞ has a positive
trace-class realization A_k^{1/2} ρ A_k^{1/2}, without requiring range(ρ) ⊆ dom(A_k).

Frozen imports, read-only:
* PhysicalEnergy (the formalization), sha256 01370715…ee072: the carrier unitary
  `momUnitary L k : L²(𝕋_L^k) ≃ₗᵢ ℓ²(ℤ^k)` and the product modes `prodMode L k w = ∏ⱼ e_{wⱼ}(xⱼ)`.
* EnergyDifferences ED1 (sha256 f4a2b782…982f) and EnergyRealization ER1 (sha256 d6805d9d…40f6):
  the Fourier-representation realization, difference bounds and comparison.

Transport principle (proved, generic):  for a unitary `e : X ≃ₗᵢ ℓ²(ℤ^k)` the pull-back
`T ↦ e⁻¹ T e` preserves products, differences and positivity, and it preserves the trace norm.
Trace-norm invariance is proved by TC6 duality with the transported Hilbert basis `e ∘ b`; no
functional calculus is run on `ℓ²`.  Instances:
* `X = L²(𝕋_L^k)`, `e = momUnitary` (position carrier; modes `E_w`);
* `X = (L²(𝕋_L))^{⊗̂k}`, `e = physUnitary ∘ momUnitary` (the carrier of the marginals `γ^{(k)}`
  of PhysicalTensor `reducedDensityN`).

On each carrier: `W := e⁻¹ A_k^{-1/2} e` (physical `A_k^{-1/2}`) and
`Tr(A_k ρ) := Σ_w a_k(w) ⟨e⁻¹e_w, ρ e⁻¹e_w⟩`, which is `Σ_w a_k(w)⟨E_w, ρ E_w⟩` on `L²(𝕋_L^k)`.
Proved: existence and uniqueness of the positive trace-class realization; energy trace norm
`= Tr(A_k ρ)`; differences `D = ρ₁ − ρ₂` with realization `T₁ − T₂`,
`‖A_k^{1/2}DA_k^{1/2}‖₁ ≤ Tr(A_kρ₁) + Tr(A_kρ₂)`, comparison `‖D‖₁ ≤ ‖A_k^{1/2}DA_k^{1/2}‖₁`;
energy-trace convergence implies trace-norm convergence.

NOT claimed: ENERGY-008 (the dynamical energy-trace convergence `eq:A1R-weighted-limit`).
The R-828C5F7E S2 hold is unchanged.
-/
import QuantumNLS.EnergyDifferences
import QuantumNLS.PhysicalEnergy

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass QuantumNLS.EnergyForm QuantumNLS.EnergyRealization QuantumNLS.Energy
open Filter Topology

noncomputable section

namespace QuantumNLS.PhysicalEnergyTrace

/-! ## §1 Generic unitary transport of operators and trace norms -/

section Transport

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] (e : G ≃ₗᵢ[ℂ] F)

/-- Pull-back `e⁻¹ T e` of an operator on `F` to `G`. -/
def pull (T : F →L[ℂ] F) : G →L[ℂ] G :=
  (e.symm.toContinuousLinearEquiv : F →L[ℂ] G) ∘L T ∘L (e.toContinuousLinearEquiv : G →L[ℂ] F)

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_apply (T : F →L[ℂ] F) (x : G) : pull e T x = e.symm (T (e x)) := rfl

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_mul (A B : F →L[ℂ] F) : pull e (A * B) = pull e A * pull e B := by
  ext x; simp [pull_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_sub (A B : F →L[ℂ] F) : pull e (A - B) = pull e A - pull e B := by
  ext x; simp [pull_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_symm_pull (T : F →L[ℂ] F) : pull e.symm (pull e T) = T := by
  ext x; simp [pull_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_pull_symm (T : G →L[ℂ] G) : pull e (pull e.symm T) = T := by
  ext x; simp [pull_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem inner_symm_left (a : F) (y : G) : ⟪e.symm a, y⟫_ℂ = ⟪a, e y⟫_ℂ := by
  rw [← e.inner_map_map, e.apply_symm_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem inner_symm_right (x : G) (a : F) : ⟪x, e.symm a⟫_ℂ = ⟪e x, a⟫_ℂ := by
  rw [← e.inner_map_map, e.apply_symm_apply]

omit [CompleteSpace F] [CompleteSpace G] in
theorem norm_pull_le (T : F →L[ℂ] F) : ‖pull e T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  rw [pull_apply, LinearIsometryEquiv.norm_map]
  exact (T.le_opNorm _).trans (by rw [LinearIsometryEquiv.norm_map])

omit [CompleteSpace F] [CompleteSpace G] in
/-- Positivity is preserved. -/
theorem isPositive_pull {T : F →L[ℂ] F} (hT : T.IsPositive) : (pull e T).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · show ⟪pull e T x, y⟫_ℂ = ⟪x, pull e T y⟫_ℂ
    rw [pull_apply, pull_apply, inner_symm_left, inner_symm_right]
    exact hT.isSymmetric (e x) (e y)
  · rw [ContinuousLinearMap.reApplyInnerSelf_apply, pull_apply, inner_symm_left]
    exact hT.re_inner_nonneg_left (e x)

/-- `‖e⁻¹ T e‖₁ ≤ ‖T‖₁` (TC6 duality, transported basis). -/
theorem traceNorm_pull_le (T : F →L[ℂ] F) : traceNorm (pull e T) ≤ traceNorm T := by
  classical
  by_cases hT : traceNorm T = ⊤
  · rw [hT]; exact le_top
  rw [← ENNReal.ofReal_toReal hT]
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ G
  let c : HilbertBasis w ℂ F := HilbertBasis.ofRepr (e.symm.trans b.repr)
  have hc : ∀ i, c i = e (b i) := fun i => by
    rw [← c.repr_symm_single]
    show (e.symm.trans b.repr).symm (lp.single 2 i (1 : ℂ)) = e (b i)
    rw [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.symm_symm, b.repr_symm_single]
  refine traceNorm_le_of_forall b _ fun X hX s => ?_
  have hY : ‖pull e.symm X‖ ≤ 1 := (norm_pull_le e.symm X).trans hX
  have heq : ∑ i ∈ s, ⟪X (b i), pull e T (b i)⟫_ℂ =
      ∑ i ∈ s, ⟪pull e.symm X (c i), T (c i)⟫_ℂ := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pull_apply, inner_symm_right, hc, pull_apply]
    simp
  rw [heq]
  exact (RCLike.re_le_norm _).trans (norm_sum_inner_le_traceNorm c T _ hY hT s)

/-- **Unitary invariance of the trace norm:** `‖e⁻¹ T e‖₁ = ‖T‖₁`. -/
theorem traceNorm_pull (T : F →L[ℂ] F) : traceNorm (pull e T) = traceNorm T := by
  refine le_antisymm (traceNorm_pull_le e T) ?_
  have h := traceNorm_pull_le e.symm (pull e T)
  rwa [pull_symm_pull] at h

theorem posTrace_pull {T : F →L[ℂ] F} (hT : T.IsPositive) : posTrace (pull e T) = posTrace T := by
  rw [← traceNorm_of_isPositive (isPositive_pull e hT), ← traceNorm_of_isPositive hT,
    traceNorm_pull]

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_injective {W : F →L[ℂ] F} (hW : Function.Injective W) :
    Function.Injective (pull e W) := fun x y h => by
  rw [pull_apply, pull_apply] at h
  exact e.injective (hW (e.symm.injective h))

omit [CompleteSpace F] [CompleteSpace G] in
theorem pull_denseRange {W : F →L[ℂ] F} (hW : DenseRange W) : DenseRange (pull e W) := by
  have h1 : DenseRange (fun x : G => W (e x)) :=
    hW.comp e.surjective.denseRange W.continuous
  exact e.symm.surjective.denseRange.comp h1 e.symm.continuous

end Transport

/-! ## §2 DEF-031 on an abstract carrier `X ≃ₗᵢ ℓ²(ℤ^k)` -/

section Carrier

variable (L : ℝ) (k : ℕ) {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [CompleteSpace X] (e : X ≃ₗᵢ[ℂ] L2 (Mom k))

/-- The physical `A_k^{-1/2} = e⁻¹ A_k^{-1/2} e` on the carrier `X`. -/
def physW : X →L[ℂ] X := pull e (AhalfInv L k)

/-- `Tr(A_k ρ)` on the carrier `X` (via the Fourier representation). -/
def physTrace (ρ : X →L[ℂ] X) : ℝ≥0∞ := kinTrace L k (pull e.symm ρ)

omit [CompleteSpace X] in
/-- Mode form: `Tr(A_k ρ) = Σ_w a_k(w) ⟨e⁻¹e_w, ρ e⁻¹e_w⟩`. -/
theorem physTrace_eq_modes (ρ : X →L[ℂ] X) :
    physTrace L k e ρ = ∑' w, ENNReal.ofReal (kinWeight L k w *
      RCLike.re ⟪e.symm (EnergyRealization.ev w), ρ (e.symm (EnergyRealization.ev w))⟫_ℂ) := by
  unfold physTrace kinTrace
  congr 1; funext w
  rw [pull_apply, LinearIsometryEquiv.symm_symm, ← inner_symm_left]

omit [CompleteSpace X] in
theorem physW_injective : Function.Injective (physW L k e) :=
  pull_injective e (invCLM_injective (kinSqrt L k) (one_le_kinSqrt L k))

omit [CompleteSpace X] in
theorem physW_denseRange : DenseRange (physW L k e) :=
  pull_denseRange e (invCLM_denseRange (kinSqrt L k) (one_le_kinSqrt L k))

omit [CompleteSpace X] in
theorem norm_physW_le : ‖physW L k e‖ ≤ 1 :=
  (norm_pull_le e _).trans (norm_AhalfInv_le L k)

variable {L k e}

/-- **Existence of the realization on the carrier** (source hypotheses). -/
theorem phys_realization {ρ : X →L[ℂ] X} (hρ : ρ.IsPositive) (hE : physTrace L k e ρ ≠ ⊤) :
    ∃ T : X →L[ℂ] X, T.IsPositive ∧ IsTraceClass T ∧
      ρ = physW L k e * T * physW L k e ∧ posTrace T = physTrace L k e ρ := by
  obtain ⟨⟨T', hT'pos, hT'tc, hT'spec, hT'tr⟩, -⟩ :=
    kinetic_realization L k (isPositive_pull e.symm hρ) hE
  refine ⟨pull e T', isPositive_pull e hT'pos, ?_, ?_, ?_⟩
  · rw [IsTraceClass, traceNorm_pull]; exact hT'tc
  · conv_lhs => rw [← pull_pull_symm e ρ, hT'spec]
    rw [pull_mul, pull_mul]; rfl
  · rw [posTrace_pull e hT'pos, hT'tr]; rfl

/-- **Uniqueness and value:** `‖A_k^{1/2} ρ A_k^{1/2}‖₁ = Tr(A_k ρ)` for positive finite-energy `ρ`. -/
theorem phys_energyTraceNorm {ρ : X →L[ℂ] X} (hρ : ρ.IsPositive) (hE : physTrace L k e ρ ≠ ⊤) :
    energyTraceNorm (physW L k e) ρ = physTrace L k e ρ := by
  obtain ⟨T, hTpos, -, hspec, htr⟩ := phys_realization hρ hE
  rw [energyTraceNorm_eq (physW_injective L k e) (physW_denseRange L k e) hspec,
    traceNorm_of_isPositive hTpos, htr]

/-- **DEF-031 for differences on the carrier.** -/
theorem phys_difference {ρ₁ ρ₂ : X →L[ℂ] X} (h₁ : ρ₁.IsPositive) (hE₁ : physTrace L k e ρ₁ ≠ ⊤)
    (h₂ : ρ₂.IsPositive) (hE₂ : physTrace L k e ρ₂ ≠ ⊤) :
    ∃ T : X →L[ℂ] X, IsTraceClass T ∧ ρ₁ - ρ₂ = physW L k e * T * physW L k e ∧
      energyTraceNorm (physW L k e) (ρ₁ - ρ₂) = traceNorm T ∧
      energyTraceNorm (physW L k e) (ρ₁ - ρ₂) ≤ physTrace L k e ρ₁ + physTrace L k e ρ₂ ∧
      traceNorm (ρ₁ - ρ₂) ≤ energyTraceNorm (physW L k e) (ρ₁ - ρ₂) := by
  obtain ⟨T₁, hT₁, -, hs₁, ht₁⟩ := phys_realization h₁ hE₁
  obtain ⟨T₂, hT₂, -, hs₂, ht₂⟩ := phys_realization h₂ hE₂
  have hsub : ρ₁ - ρ₂ = physW L k e * (T₁ - T₂) * physW L k e := by
    rw [hs₁, hs₂, mul_sub, sub_mul]
  have heq : energyTraceNorm (physW L k e) (ρ₁ - ρ₂) = traceNorm (T₁ - T₂) :=
    energyTraceNorm_eq (physW_injective L k e) (physW_denseRange L k e) hsub
  have hneg : traceNorm (-T₂) = traceNorm T₂ := by
    rw [show -T₂ = (-1 : ℂ) • T₂ from (neg_one_smul ℂ _).symm, traceNorm_smul]; simp
  have hbound : traceNorm (T₁ - T₂) ≤ physTrace L k e ρ₁ + physTrace L k e ρ₂ := by
    rw [sub_eq_add_neg]
    refine (traceNorm_add_le _ _).trans (le_of_eq ?_)
    rw [hneg, traceNorm_of_isPositive hT₁, traceNorm_of_isPositive hT₂, ht₁, ht₂]
  refine ⟨T₁ - T₂, ?_, hsub, heq, heq ▸ hbound, ?_⟩
  · exact lt_of_le_of_lt hbound (ENNReal.add_lt_top.mpr
      ⟨lt_top_iff_ne_top.mpr hE₁, lt_top_iff_ne_top.mpr hE₂⟩)
  · refine (traceNorm_le_energyTraceNorm (physW_injective L k e) (physW_denseRange L k e) _).trans ?_
    have h1 : ENNReal.ofReal (‖physW L k e‖ ^ 2) ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have := norm_physW_le (L := L) (k := k) e
      nlinarith [norm_nonneg (physW L k e)]
    calc ENNReal.ofReal (‖physW L k e‖ ^ 2) * energyTraceNorm (physW L k e) (ρ₁ - ρ₂)
        ≤ 1 * energyTraceNorm (physW L k e) (ρ₁ - ρ₂) := by gcongr
      _ = _ := one_mul _

/-- **Energy-trace convergence implies trace-norm convergence on the carrier.** -/
theorem phys_tendsto_traceNorm {α : Type*} {l : Filter α} {ρN : α → X →L[ℂ] X}
    {ρ : X →L[ℂ] X}
    (h : Tendsto (fun a => energyTraceNorm (physW L k e) (ρN a - ρ)) l (𝓝 0)) :
    Tendsto (fun a => traceNorm (ρN a - ρ)) l (𝓝 0) :=
  tendsto_traceNorm_of_energy (physW_injective L k e) (physW_denseRange L k e) h

end Carrier

/-! ## §3 Instances: the position carrier `L²(𝕋_L^k)` and the tensor carrier of `γ^{(k)}` -/

section Instances

open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-- `momUnitary⁻¹ e_w = E_w`, the physical product mode `∏ⱼ e_{wⱼ}(xⱼ)`. -/
theorem momUnitary_symm_ev (w : Mom k) :
    (momUnitary L k).symm (EnergyRealization.ev w) = prodMode L k w := by
  refine ext_inner_left ℂ fun F => ?_
  rw [inner_symm_right, ← inner_conj_symm, EnergyRealization.inner_ev_left,
    momUnitary_apply_eq_inner, inner_conj_symm]

/-- **Position carrier:** `Tr(A_k ρ) = Σ_w a_k(w) ⟨E_w, ρ E_w⟩` on `L²(𝕋_L^k)`, where
`E_w(x) = ∏ⱼ L^{-1/2} e^{2πi wⱼ xⱼ/L}` and `a_k(w) = 1 + Σⱼ(2πwⱼ/L)²`. -/
theorem physTrace_position (ρ : L2TN L k →L[ℂ] L2TN L k) :
    physTrace L k (momUnitary L k) ρ = ∑' w, ENNReal.ofReal (kinWeight L k w *
      RCLike.re ⟪prodMode L k w, ρ (prodMode L k w)⟫_ℂ) := by
  rw [physTrace_eq_modes]
  simp_rw [momUnitary_symm_ev]

variable (L k)

/-- The carrier unitary of the `k`-particle tensor power: `(L²(𝕋_L))^{⊗̂k} ≃ L²(𝕋_L^k) ≃ ℓ²(ℤ^k)`. -/
def tensorMomUnitary : HilbertTensorPower ℂ (L2T L) k ≃ₗᵢ[ℂ] L2 (Mom k) :=
  (physUnitary (L := L) (N := k)).trans (momUnitary L k)

variable {L k}

/-- **DEF-031 for the marginal difference `D = γ^{(k)}_ψ − |v^{⊗k}⟩⟨v^{⊗k}|`** on the tensor carrier,
under finite kinetic energy of both terms (`Tr(A_k ·) < ∞`).  `γ^{(k)}` is PhysicalTensor's
`reducedDensityN`; its positivity is proved there. -/
theorem def031_marginal_difference {N : ℕ} (hk : k ≤ N)
    (ψ : HilbertTensorPower ℂ (L2T L) N) (v : L2T L)
    (hE₁ : physTrace L k (tensorMomUnitary L k) (reducedDensityN N k hk ψ) ≠ ⊤)
    (hE₂ : physTrace L k (tensorMomUnitary L k)
      (InnerProductSpace.rankOne ℂ (htpow k v : HilbertTensorPower ℂ (L2T L) k) (htpow k v)) ≠ ⊤) :
    ∃ T, IsTraceClass T ∧
      reducedDensityN N k hk ψ - InnerProductSpace.rankOne ℂ (htpow k v) (htpow k v) =
        physW L k (tensorMomUnitary L k) * T * physW L k (tensorMomUnitary L k) ∧
      energyTraceNorm (physW L k (tensorMomUnitary L k))
          (reducedDensityN N k hk ψ - InnerProductSpace.rankOne ℂ (htpow k v) (htpow k v)) =
        traceNorm T ∧
      traceNorm (reducedDensityN N k hk ψ - InnerProductSpace.rankOne ℂ (htpow k v) (htpow k v)) ≤
        energyTraceNorm (physW L k (tensorMomUnitary L k))
          (reducedDensityN N k hk ψ - InnerProductSpace.rankOne ℂ (htpow k v) (htpow k v)) := by
  obtain ⟨T, hT, hs, he, -, hc⟩ := phys_difference (reducedDensityN_isPositive N k hk ψ) hE₁
    (InnerProductSpace.isPositive_rankOne_self _) hE₂
  exact ⟨T, hT, hs, he, hc⟩

end Instances

end QuantumNLS.PhysicalEnergyTrace

#print axioms QuantumNLS.PhysicalEnergyTrace.traceNorm_pull
#print axioms QuantumNLS.PhysicalEnergyTrace.isPositive_pull
#print axioms QuantumNLS.PhysicalEnergyTrace.phys_realization
#print axioms QuantumNLS.PhysicalEnergyTrace.phys_energyTraceNorm
#print axioms QuantumNLS.PhysicalEnergyTrace.phys_difference
#print axioms QuantumNLS.PhysicalEnergyTrace.phys_tendsto_traceNorm
#print axioms QuantumNLS.PhysicalEnergyTrace.momUnitary_symm_ev
#print axioms QuantumNLS.PhysicalEnergyTrace.physTrace_position
#print axioms QuantumNLS.PhysicalEnergyTrace.def031_marginal_difference
