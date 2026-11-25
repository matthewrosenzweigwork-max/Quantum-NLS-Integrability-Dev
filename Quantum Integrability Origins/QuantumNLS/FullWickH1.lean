import QuantumNLS.BalancedWickDefinition
import QuantumNLS.WickBounds
import QuantumNLS.WickSpectralBridge

/-! FullWickH1 (haiku_inventory, R-140AE34B `thm:full-wick`, source-text/chapters/core/wick_calculus.tex:49-203).

Stage 1 is the algebraic part of the printed theorem for the DEF-032 Bethe-chart operator
`BalancedWickDefinition.wick b G f = J_N^* W_N(f) J_N` (the full occupation gauge enters through
the gauged basis `gaugedBasis b G`, and `J_N = occupationCoefficient (gaugedBasis b G)` is a linear
isometric equivalence, because a `BetheBasis` is a `HilbertBasis`).

Printed items covered (labels as in wick_calculus.tex):
  eq:full-coefficient-bound  ‖W_N^q(f)‖ ≤ ‖f‖_coeff                        (quantization_coeff_bound)
  eq:full-product            W(f)W(g) = Σ_γ N^{-|γ|}/γ! W((∂_z^γ f)(∂_{z̄}^γ g))   (quantization_product)
  eq:full-product-bound      ‖W(f)W(g) − W(fg) − N^{-1}W(S_1 + i{f,g}/2)‖ ≤ C(f,g)N^{-2}
                                                                             (quantization_product_bound)
  eq:full-Dirac-bound        ‖−iN[W(f),W(g)] − W({f,g})‖ ≤ (C(f,g)+C(g,f))N^{-1}
                                                                             (quantization_Dirac_bound)
The bundled statement is `fullWick_stage1`.

Predecessors used by this stage: DEF-032 (BalancedWickDefinition, realized parametric) and the
accepted/support algebra of WickSymbols, WickBounds and WickSpectralBridge (which carry the exact
monomial product identity and the Hilbert-level bounds). No external contract (EXT-025) and no
unaccepted predecessor (R-D2F4CE8F, R-8362E5EB) is used by Stage 1. The printed proof's commutator
identity eq:full-CCR is used only in the norm-limit half (Stage 2), not here.

Only the standard axioms (propext, Classical.choice, Quot.sound) occur; see the #print audit at the end of the file.
-/

noncomputable section
open scoped BigOperators InnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace QuantumNLS.FullWickH1

open QuantumNLS.Occupation QuantumNLS.WickSymbols QuantumNLS.WickBounds
open QuantumNLS.WickSpectralBridge QuantumNLS.OccupationHilbert
open QuantumNLS.BalancedWickDefinition QuantumNLS.BetheCoefficientTransform

/-! ### Conjugation by a linear isometric equivalence -/

section Conj

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- `e⁻¹ ∘ X ∘ e` for a linear isometric equivalence `e : E ≃ₗᵢ F`. -/
def conjBy (e : E ≃ₗᵢ[ℂ] F) (X : F →L[ℂ] F) : E →L[ℂ] E :=
  e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (X.comp e.toContinuousLinearEquiv.toContinuousLinearMap)

lemma conjBy_apply (e : E ≃ₗᵢ[ℂ] F) (X : F →L[ℂ] F) (x : E) :
    conjBy e X x = e.symm (X (e x)) := rfl

lemma conjBy_mul (e : E ≃ₗᵢ[ℂ] F) (X Y : F →L[ℂ] F) :
    conjBy e X * conjBy e Y = conjBy e (X * Y) := by
  ext x
  simp [conjBy_apply, ContinuousLinearMap.mul_apply]

lemma conjBy_sub (e : E ≃ₗᵢ[ℂ] F) (X Y : F →L[ℂ] F) :
    conjBy e (X - Y) = conjBy e X - conjBy e Y := by
  ext x
  simp [conjBy_apply]

lemma conjBy_smul (e : E ≃ₗᵢ[ℂ] F) (c : ℂ) (X : F →L[ℂ] F) :
    conjBy e (c • X) = c • conjBy e X := by
  ext x
  simp [conjBy_apply]

lemma conjBy_sum {ι : Type*} (s : Finset ι) (e : E ≃ₗᵢ[ℂ] F) (c : ι → ℂ)
    (X : ι → F →L[ℂ] F) :
    conjBy e (∑ i ∈ s, c i • X i) = ∑ i ∈ s, c i • conjBy e (X i) := by
  ext x
  simp [conjBy_apply, ContinuousLinearMap.sum_apply]

lemma conjBy_norm_le (e : E ≃ₗᵢ[ℂ] F) (X : F →L[ℂ] F) : ‖conjBy e X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg X) (fun x => ?_)
  rw [conjBy_apply, LinearIsometryEquiv.norm_map]
  calc ‖X (e x)‖ ≤ ‖X‖ * ‖e x‖ := X.le_opNorm _
    _ = ‖X‖ * ‖x‖ := by rw [LinearIsometryEquiv.norm_map]

lemma conjBy_norm_eq (e : E ≃ₗᵢ[ℂ] F) (X : F →L[ℂ] F) : ‖conjBy e X‖ = ‖X‖ := by
  apply le_antisymm (conjBy_norm_le e X)
  refine ContinuousLinearMap.opNorm_le_bound X (norm_nonneg _) (fun y => ?_)
  have h := (conjBy e X).le_opNorm (e.symm y)
  simpa [conjBy_apply, LinearIsometryEquiv.norm_map] using h

end Conj

/-! ### The sector-level and Hilbert-level exact product (`eq:full-product`) -/

section Product

/-- Sector-level exact product: `W_N(f) W_N(g) = Σ_γ N^{-|γ|}/γ! W_N(∂^γ f ∂̄^γ g)` on the
finitely supported occupation sector, for balanced `f, g`. -/
theorem sector_product {N : ℕ} {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    (Γ : Finset (ℤ →₀ ℕ)) (hΓ : ∀ p ∈ f.coeff.support, Finset.Iic p.1 ⊆ Γ) (v : Sector N) :
    WS N f (WS N g v) = ∑ γ ∈ Γ, wickWeight N γ • WS N (dz γ f * dzb γ g) v := by
  have hb : ∀ γ, Balanced (dz γ f * dzb γ g) := fun γ => hf.dz_mul_dzb hg γ
  apply Occupation.emb_injective N
  rw [emb_WS hf, emb_WS hg, map_sum]
  have h2 := LinearMap.congr_fun (wick_product N f g Γ hΓ) (emb N v)
  simp only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h2
  rw [h2]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [map_smul, emb_WS (hb γ)]

/-- Hilbert-level exact product on `ℓ²(𝓜_N)` for `N ≥ 1` (ungauged auxiliary operator). -/
theorem hilbert_product {N : ℕ} (hN : 0 < N) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    (Γ : Finset (ℤ →₀ ℕ)) (hΓ : ∀ p ∈ f.coeff.support, Finset.Iic p.1 ⊆ Γ) :
    WHil N f * WHil N g = ∑ γ ∈ Γ, wickWeight N γ • WHil N (dz γ f * dzb γ g) := by
  have hb : ∀ γ, Balanced (dz γ f * dzb γ g) := fun γ => hf.dz_mul_dzb hg γ
  apply ext_core N
  intro v
  rw [ContinuousLinearMap.mul_apply, WHil_core hN hg v, WHil_core hN hf (WS N g v),
    sector_product hf hg Γ hΓ v, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [ContinuousLinearMap.smul_apply, WHil_core hN (hb γ) v, map_smul]

end Product

/-! ### The DEF-032 operator is the conjugate of the Hilbert Wick operator -/

section Quantization

variable {L : ℝ} [Fact (0 < L)]

/-- `quantization b G f = J_N^* (W_N(f)) J_N` with `J_N = occupationCoefficient (gaugedBasis b G)`,
for `N ≥ 1` (the `if N = 0` branch of `auxiliaryWick` is not taken). -/
theorem quantization_eq_conj {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (f : Sym) :
    quantization b G f
      = conjBy (occupationCoefficient (BetheOccupationGauge.gaugedBasis b G)) (WHil N f) := by
  have hN0 : N ≠ 0 := hN.ne'
  simp only [quantization, conjBy, auxiliaryWick, hN0, ↓reduceIte]

/-- Exact norm preservation of the DEF-032 operator: the Bethe coefficient map is isometric. -/
theorem quantization_norm_eq {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (f : Sym) :
    ‖quantization b G f‖ = ‖WHil N f‖ := by
  rw [quantization_eq_conj hN b G f, conjBy_norm_eq]

/-- **`eq:full-coefficient-bound`** for the DEF-032 operator: `‖W_N(f)‖ ≤ ‖f‖_coeff`. -/
theorem quantization_coeff_bound {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) {f : Sym} (hf : Balanced f) :
    ‖quantization b G f‖ ≤ coeffNorm f :=
  (quantization_norm_eq hN b G f).trans_le (WHil_norm_le hN hf)

/-- **`eq:full-product`** for the DEF-032 operator, for any finite `Γ` containing `γ ≤ α` for
every monomial `z^α z̄^β` of `f` (the remaining terms vanish). -/
theorem quantization_product {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) {f f' : Sym} (hf : Balanced f) (hf' : Balanced f')
    (Γ : Finset (ℤ →₀ ℕ)) (hΓ : ∀ p ∈ f.coeff.support, Finset.Iic p.1 ⊆ Γ) :
    quantization b G f * quantization b G f'
      = ∑ γ ∈ Γ, wickWeight N γ • quantization b G (dz γ f * dzb γ f') := by
  simp only [quantization_eq_conj hN, conjBy_mul, hilbert_product hN hf hf' Γ hΓ, conjBy_sum]

/-- **`eq:full-product-bound`** for the DEF-032 operator, with the source constant `C(f,g)` of
`eq:full-Cfg` (as `WickBounds.Cfg`) and the source bracket `S_1 + i{f,g}/2` on any label set `S`
containing the labels of `f`. -/
theorem quantization_product_bound {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {S : Finset ℤ} (hS : labelsOf f ⊆ S) :
    ‖quantization b G f * quantization b G g - quantization b G (f * g)
        - (N : ℂ)⁻¹ • quantization b G (S1 S f g + (Complex.I / 2) • pb S f g)‖
      ≤ Cfg f g * ((N : ℝ)⁻¹) ^ 2 := by
  have key : quantization b G f * quantization b G g - quantization b G (f * g)
        - (N : ℂ)⁻¹ • quantization b G (S1 S f g + (Complex.I / 2) • pb S f g)
      = conjBy (occupationCoefficient (BetheOccupationGauge.gaugedBasis b G))
          (WHil N f * WHil N g - WHil N (f * g)
            - (N : ℂ)⁻¹ • WHil N (S1 S f g + (Complex.I / 2) • pb S f g)) := by
    simp only [quantization_eq_conj hN, conjBy_mul, conjBy_sub, conjBy_smul]
  rw [key, conjBy_norm_eq]
  exact hilbert_product_bound hN hf hg hS

/-- **`eq:full-Dirac-bound`** for the DEF-032 operator, bracket convention `{w_a, w̄_b} = −iδ_ab`:
`‖−iN[W_N(f), W_N(g)] − W_N({f,g})‖ ≤ (C(f,g) + C(g,f)) N^{-1}`. -/
theorem quantization_Dirac_bound {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) {f g : Sym} (hf : Balanced f) (hg : Balanced g)
    {S : Finset ℤ} (hSf : labelsOf f ⊆ S) (hSg : labelsOf g ⊆ S) :
    ‖(-(Complex.I) * (N : ℂ)) • (quantization b G f * quantization b G g
          - quantization b G g * quantization b G f)
        - quantization b G (pb S f g)‖
      ≤ (Cfg f g + Cfg g f) * (N : ℝ)⁻¹ := by
  have key : (-(Complex.I) * (N : ℂ)) • (quantization b G f * quantization b G g
          - quantization b G g * quantization b G f)
        - quantization b G (pb S f g)
      = conjBy (occupationCoefficient (BetheOccupationGauge.gaugedBasis b G))
          ((-(Complex.I) * (N : ℂ)) • (WHil N f * WHil N g - WHil N g * WHil N f)
            - WHil N (pb S f g)) := by
    simp only [quantization_eq_conj hN, conjBy_mul, conjBy_sub, conjBy_smul]
  rw [key, conjBy_norm_eq]
  exact hilbert_Dirac_bound hN hf hg hSf hSg

/-- The labels of a `Polynomial` symbol lie in its declared coordinate set. -/
lemma labelsOf_polynomial (f : BalancedWickDefinition.Polynomial) :
    labelsOf f.symbol ⊆ f.coordinates := by
  intro a ha
  simp only [labelsOf, Finset.mem_biUnion] at ha
  obtain ⟨p, hp, ha⟩ := ha
  exact (f.labels p hp).1 ha

/-- `wick` on a `Polynomial` is the DEF-032 operator on its symbol (definitional). -/
theorem wick_eq_quantization {N : ℕ} (b : BetheBasis L N) (G : BetheOccupationGauge.Gauge)
    (f : BalancedWickDefinition.Polynomial) :
    wick b G f = quantization b G f.symbol := rfl

/-- **Stage 1 bundle** of `thm:full-wick` (algebraic items) for the DEF-032 operator at `N ≥ 1`
and balanced polynomial cylinders `f, f'`: the exact product identity for every admissible finite
`Γ`, the coefficient bound, the product bound and the scaled Dirac bound with the source constants. -/
theorem fullWick_stage1 {N : ℕ} (hN : 0 < N) (b : BetheBasis L N)
    (G : BetheOccupationGauge.Gauge) (f f' : BalancedWickDefinition.Polynomial) :
    (∀ Γ : Finset (ℤ →₀ ℕ), (∀ p ∈ f.symbol.coeff.support, Finset.Iic p.1 ⊆ Γ) →
        wick b G f * wick b G f'
          = ∑ γ ∈ Γ, wickWeight N γ • quantization b G (dz γ f.symbol * dzb γ f'.symbol))
    ∧ ‖wick b G f‖ ≤ coeffNorm f.symbol
    ∧ (∀ S : Finset ℤ, labelsOf f.symbol ⊆ S →
        ‖wick b G f * wick b G f' - quantization b G (f.symbol * f'.symbol)
            - (N : ℂ)⁻¹ • quantization b G
                (S1 S f.symbol f'.symbol + (Complex.I / 2) • pb S f.symbol f'.symbol)‖
          ≤ Cfg f.symbol f'.symbol * ((N : ℝ)⁻¹) ^ 2)
    ∧ (∀ S : Finset ℤ, labelsOf f.symbol ⊆ S → labelsOf f'.symbol ⊆ S →
        ‖(-(Complex.I) * (N : ℂ)) • (wick b G f * wick b G f' - wick b G f' * wick b G f)
            - quantization b G (pb S f.symbol f'.symbol)‖
          ≤ (Cfg f.symbol f'.symbol + Cfg f'.symbol f.symbol) * (N : ℝ)⁻¹) := by
  refine ⟨fun Γ hΓ => quantization_product hN b G f.balanced f'.balanced Γ hΓ,
    quantization_coeff_bound hN b G f.balanced, fun S hS => ?_,
    fun S hS hS' => ?_⟩
  · exact quantization_product_bound hN b G f.balanced f'.balanced hS
  · exact quantization_Dirac_bound hN b G f.balanced f'.balanced hS hS'

end Quantization

end QuantumNLS.FullWickH1

#print axioms QuantumNLS.FullWickH1.conjBy_norm_eq
#print axioms QuantumNLS.FullWickH1.sector_product
#print axioms QuantumNLS.FullWickH1.hilbert_product
#print axioms QuantumNLS.FullWickH1.quantization_eq_conj
#print axioms QuantumNLS.FullWickH1.quantization_norm_eq
#print axioms QuantumNLS.FullWickH1.quantization_coeff_bound
#print axioms QuantumNLS.FullWickH1.quantization_product
#print axioms QuantumNLS.FullWickH1.quantization_product_bound
#print axioms QuantumNLS.FullWickH1.quantization_Dirac_bound
#print axioms QuantumNLS.FullWickH1.labelsOf_polynomial
#print axioms QuantumNLS.FullWickH1.wick_eq_quantization
#print axioms QuantumNLS.FullWickH1.fullWick_stage1
