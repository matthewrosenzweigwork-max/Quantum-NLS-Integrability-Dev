/-
QuantumNLS.ProductSecondDerivatives — weak second partial derivatives on `𝕋_L^k` and the
distributional characterization of `A_k = 1 − Σⱼ ∂²_{x_j}` (owner: opus_tensor).

Source: DEF-031 (definitions.tex:187) `A_k = 1 − Σ_{j≤k} ∂²_{x_j}` on `L²(𝕋_L^k)`; DEF-005
kinetic form; DEF-001/002 normalization (mass-`L` per coordinate, `E_w = ∏ⱼ e_{wⱼ}`).

Definition (genuinely distributional; no `L²` first derivative is presupposed):
`HasWeakSecondPartial i j F H` iff `∫ F · ∂ᵢ∂ⱼφ = ∫ H · φ` for every smooth lattice-periodic `φ`.

Frozen imports, read-only: ProductWeakDerivatives PWD1 91ec7338 (tests, `pderiv`, `liftK`,
`HasWeakPartial`, Parseval pairing, slice integration by parts); PhysicalEnergy 01370715
(`physAk`, `mem_physAk_domain_iff`, `momUnitary_physAk`, `inner_physAk_self`).
No contact/Bethe/collision edits; no S2 work; no dynamics (ENERGY-008) claimed.

Results (all proved, standard axioms only):
* `pderiv_isTest`: `∂ⱼ` preserves smooth lattice-periodic tests.
* `hasWeakSecondPartial_iff`: `∂ᵢ∂ⱼF = H` weakly ⇔ `Ĥ(w) = (i2πwᵢ/L)(i2πwⱼ/L) F̂(w)`;
  `hasWeakSecondPartial_unique`; `hasWeakSecondPartial_iff_iterated` (consistency with
  `∂ᵢ(∂ⱼF)` whenever `∂ⱼF ∈ L²`).
* `mem_physAk_domain_iff_second`: `F ∈ D(A_k)` ⇔ every pure `∂ⱼ²F ∈ L²` (weakly);
  `mem_physAk_domain_iff_mixed`: ⇔ every mixed `∂ᵢ∂ⱼF ∈ L²`.
* `physAk_eq_sub_sum`: `A_k F = F − Σⱼ ∂ⱼ²F`; `mem_graph_physAk_iff`: graph of `A_k` described
  purely by weak second partials.
* `inner_secondPartial`: `⟪F, ∂ⱼ²F⟫ = −‖∂ⱼF‖²`; `inner_physAk_self_eq`:
  `⟪F, A_k F⟫ = ‖F‖² + Σⱼ ‖∂ⱼF‖²`.
-/
import QuantumNLS.ProductWeakDerivatives

open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier QuantumNLS.PhysicalTensor QuantumNLS.PhysicalEnergy
  QuantumNLS.Energy QuantumNLS.WeakDerivatives QuantumNLS.ProductWeakDerivatives

noncomputable section

namespace QuantumNLS.ProductSecondDerivatives

variable {L : ℝ} [Fact (0 < L)] {k : ℕ}

/-! ## Derivatives of tests are tests -/

omit [Fact (0 < L)] in
/-- `∂ⱼ` maps smooth lattice-periodic tests to smooth lattice-periodic tests. -/
theorem pderiv_isTest {φ : (Fin k → ℝ) → ℂ} (hφ : IsTorusTest L φ) (j : Fin k) :
    IsTorusTest L (pderiv j φ) := by
  obtain ⟨hd, hfd⟩ := contDiff_infty_iff_fderiv.1 hφ.smooth
  have e : pderiv j φ = fun x => fderiv ℝ φ x (Pi.single j 1) :=
    funext (pderiv_eq_fderiv hd j)
  refine ⟨?_, ?_⟩
  · rw [e]
    exact hfd.clm_apply contDiff_const
  · intro x m
    rw [e]
    have hc : (fun y => φ (y + fun i => (m i : ℝ) * L)) = φ := funext fun y => hφ.periodic y m
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) (fun i => (m i : ℝ) * L)
    rw [hc] at h
    show fderiv ℝ φ (x + fun i => (m i : ℝ) * L) (Pi.single j 1) = fderiv ℝ φ x (Pi.single j 1)
    rw [← h]

omit [Fact (0 < L)] in
theorem pderiv_const_mul (c : ℂ) (f : (Fin k → ℝ) → ℂ) (i : Fin k) (x : Fin k → ℝ) :
    pderiv i (fun y => c * f y) x = c * pderiv i f x := by
  show deriv (fun t => c * f (Function.update x i t)) (x i) =
    c * deriv (fun t => f (Function.update x i t)) (x i)
  rw [deriv_const_mul_field']

/-! ## Weak second partial derivatives -/

/-- **Weak second partial derivative** `∂ᵢ∂ⱼF = H` (distributional; `F, H ∈ L²(𝕋_L^k)`). -/
def HasWeakSecondPartial (i j : Fin k) (F H : L2TN L k) : Prop :=
  ∀ φ : (Fin k → ℝ) → ℂ, IsTorusTest L φ →
    ∫ y, (F : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) (pderiv i (pderiv j φ)) y
        ∂(torusPiMeasure L k) =
      ∫ y, (H : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) φ y ∂(torusPiMeasure L k)

/-- **(A)** weak `∂ᵢ∂ⱼF = H` ⇒ `Ĥ(w) = ikn(wᵢ)·ikn(wⱼ)·F̂(w)`. -/
theorem momUnitary_of_hasWeakSecondPartial {i j : Fin k} {F H : L2TN L k}
    (h : HasWeakSecondPartial i j F H) (w : Mom k) :
    (momUnitary L k H : Mom k → ℂ) w =
      ikn L (w i) * (ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w) := by
  have hw := h (chiK L w) (chiK_isTest w)
  have e1 : pderiv j (chiK L w) = fun x => -(ikn L (w j)) * chiK L w x :=
    funext (pderiv_chiK w j)
  have hl : liftK (L := L) (pderiv i (pderiv j (chiK L w))) =
      fun y => ikn L (w i) * ikn L (w j) * liftK (L := L) (chiK L w) y := by
    funext y; unfold liftK; rw [e1, pderiv_const_mul, pderiv_chiK]; ring
  rw [hl] at hw
  have e2 : ∫ y, (F : (Fin k → AddCircle L) → ℂ) y *
      (ikn L (w i) * ikn L (w j) * liftK (L := L) (chiK L w) y) ∂(torusPiMeasure L k) =
      ikn L (w i) * ikn L (w j) *
      ∫ y, liftK (L := L) (chiK L w) y * (F : (Fin k → AddCircle L) → ℂ) y ∂(torusPiMeasure L k) := by
    rw [← integral_const_mul]; congr 1; funext y; ring
  have e3 : ∫ y, (H : (Fin k → AddCircle L) → ℂ) y * liftK (L := L) (chiK L w) y
      ∂(torusPiMeasure L k) =
      ∫ y, liftK (L := L) (chiK L w) y * (H : (Fin k → AddCircle L) → ℂ) y ∂(torusPiMeasure L k) := by
    congr 1; funext y; ring
  rw [e2, e3] at hw
  rw [momUnitary_eq_integral, momUnitary_eq_integral, ← hw]
  ring

/-- **(B)** `Ĥ(w) = ikn(wᵢ)·ikn(wⱼ)·F̂(w)` ⇒ weak `∂ᵢ∂ⱼF = H`. -/
theorem hasWeakSecondPartial_of_momUnitary {i j : Fin k} {F H : L2TN L k}
    (h : ∀ w, (momUnitary L k H : Mom k → ℂ) w =
      ikn L (w i) * (ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w)) :
    HasWeakSecondPartial i j F H := by
  intro φ hφ
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := j.pos; omega⟩
  rw [integral_mul_eq_tsumK F (memLp_liftK (continuous_pderiv (pderiv_isTest hφ j) i)),
    integral_mul_eq_tsumK H (memLp_liftK hφ.smooth.continuous)]
  congr 1; funext w
  rw [pairK_pderiv i (pderiv_isTest hφ j) w, pairK_pderiv j hφ w, h w]
  ring

/-- **Identification.** `∂ᵢ∂ⱼF = H` weakly iff `Ĥ(w) = (i2πwᵢ/L)(i2πwⱼ/L) F̂(w)` for all `w`. -/
theorem hasWeakSecondPartial_iff (i j : Fin k) (F H : L2TN L k) :
    HasWeakSecondPartial i j F H ↔
      ∀ w, (momUnitary L k H : Mom k → ℂ) w =
        ikn L (w i) * (ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w) :=
  ⟨momUnitary_of_hasWeakSecondPartial, hasWeakSecondPartial_of_momUnitary⟩

theorem hasWeakSecondPartial_unique {i j : Fin k} {F H₁ H₂ : L2TN L k}
    (h₁ : HasWeakSecondPartial i j F H₁) (h₂ : HasWeakSecondPartial i j F H₂) : H₁ = H₂ := by
  apply (momUnitary L k).injective
  ext w
  rw [momUnitary_of_hasWeakSecondPartial h₁, momUnitary_of_hasWeakSecondPartial h₂]

/-- **Consistency with iterated first partials.** If `∂ⱼF = G ∈ L²` weakly, then
`∂ᵢ∂ⱼF = H` weakly iff `∂ᵢG = H` weakly. -/
theorem hasWeakSecondPartial_iff_iterated {i j : Fin k} {F G H : L2TN L k}
    (hG : HasWeakPartial j F G) :
    HasWeakSecondPartial i j F H ↔ HasWeakPartial i G H := by
  rw [hasWeakSecondPartial_iff, hasWeakPartial_iff]
  simp only [momUnitary_of_hasWeakPartial hG]

omit [Fact (0 < L)] in
theorem norm_ikn_ikn_mul_sq (a b : ℤ) (c : ℂ) :
    ‖ikn L a * (ikn L b * c)‖ ^ 2 = freq L a ^ 2 * freq L b ^ 2 * ‖c‖ ^ 2 := by
  rw [norm_ikn_mul_sq, norm_ikn_mul_sq]; ring

/-- `∂ᵢ∂ⱼF ∈ L²` exists weakly iff `Σ_w (2πwᵢ/L)²(2πwⱼ/L)²|F̂(w)|² < ∞`. -/
theorem exists_hasWeakSecondPartial_iff (i j : Fin k) (F : L2TN L k) :
    (∃ H, HasWeakSecondPartial i j F H) ↔
      Summable fun w => freq L (w i) ^ 2 * freq L (w j) ^ 2 *
        ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 := by
  constructor
  · rintro ⟨H, hH⟩
    refine (summable_sq (momUnitary L k H)).congr fun w => ?_
    rw [momUnitary_of_hasWeakSecondPartial hH w, norm_ikn_ikn_mul_sq]
  · intro hs
    have hm : Memℓp (fun w : Mom k =>
        ikn L (w i) * (ikn L (w j) * (momUnitary L k F : Mom k → ℂ) w)) 2 :=
      memL2_iff.2 (hs.congr fun w => (norm_ikn_ikn_mul_sq _ _ _).symm)
    refine ⟨(momUnitary L k).symm ⟨_, hm⟩, hasWeakSecondPartial_of_momUnitary fun w => ?_⟩
    rw [LinearIsometryEquiv.apply_symm_apply]

/-! ## Weight comparisons -/

omit [Fact (0 < L)] in
theorem freq_sq_le_kinWeight (w : Mom k) (j : Fin k) : freq L (w j) ^ 2 ≤ kinWeight L k w := by
  unfold kinWeight
  have : freq L (w j) ^ 2 ≤ ∑ i, freq L (w i) ^ 2 :=
    Finset.single_le_sum (f := fun i => freq L (w i) ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  linarith

omit [Fact (0 < L)] in
theorem kinWeight_nonneg (w : Mom k) : 0 ≤ kinWeight L k w :=
  zero_le_one.trans (one_le_kinWeight L k w)

omit [Fact (0 < L)] in
/-- `a_k(w)² ≤ 2 + 2k Σⱼ (2πwⱼ/L)⁴` (Cauchy–Schwarz). -/
theorem kinWeight_sq_le (w : Mom k) :
    kinWeight L k w ^ 2 ≤ 2 + 2 * (k : ℝ) * ∑ j, freq L (w j) ^ 2 * freq L (w j) ^ 2 := by
  have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => freq L (w j) ^ 2)
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  have e : ∑ j, (freq L (w j) ^ 2) ^ 2 = ∑ j, freq L (w j) ^ 2 * freq L (w j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => sq _
  rw [e] at h1
  unfold kinWeight
  nlinarith [h1, sq_nonneg (∑ j, freq L (w j) ^ 2 - 1)]

/-! ## The domain of `A_k` -/

/-- **`D(A_k)` = pure weak second partials in `L²`.** -/
theorem mem_physAk_domain_iff_second (F : L2TN L k) :
    F ∈ (physAk L k).domain ↔ ∀ j, ∃ H, HasWeakSecondPartial j j F H := by
  rw [mem_physAk_domain_iff]
  simp_rw [exists_hasWeakSecondPartial_iff]
  constructor
  · intro hs j
    refine Summable.of_nonneg_of_le (fun w => by positivity) (fun w => ?_) hs
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [sq (kinWeight L k w)]
    exact mul_le_mul (freq_sq_le_kinWeight w j) (freq_sq_le_kinWeight w j) (by positivity)
      (kinWeight_nonneg w)
  · intro hs
    have hg := ((summable_sq (momUnitary L k F)).mul_left 2).add
      ((summable_sum (s := Finset.univ) fun j _ => hs j).mul_left (2 * (k : ℝ)))
    refine Summable.of_nonneg_of_le (fun w => by positivity) (fun w => ?_) hg
    have hb := mul_le_mul_of_nonneg_right (kinWeight_sq_le (L := L) w)
      (sq_nonneg ‖(momUnitary L k F : Mom k → ℂ) w‖)
    have e : 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 + 2 * (k : ℝ) *
        ∑ j, freq L (w j) ^ 2 * freq L (w j) ^ 2 * ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 =
        (2 + 2 * (k : ℝ) * ∑ j, freq L (w j) ^ 2 * freq L (w j) ^ 2) *
          ‖(momUnitary L k F : Mom k → ℂ) w‖ ^ 2 := by
      rw [← Finset.sum_mul]; ring
    simp only
    rw [e]
    exact hb

/-- **`D(A_k)` = all mixed weak second partials in `L²`.** -/
theorem mem_physAk_domain_iff_mixed (F : L2TN L k) :
    F ∈ (physAk L k).domain ↔ ∀ i j, ∃ H, HasWeakSecondPartial i j F H := by
  constructor
  · intro hF i j
    rw [exists_hasWeakSecondPartial_iff]
    refine Summable.of_nonneg_of_le (fun w => by positivity) (fun w => ?_)
      ((mem_physAk_domain_iff F).1 hF)
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [sq (kinWeight L k w)]
    exact mul_le_mul (freq_sq_le_kinWeight w i) (freq_sq_le_kinWeight w j) (by positivity)
      (kinWeight_nonneg w)
  · intro h
    exact (mem_physAk_domain_iff_second F).2 fun j => h j j

/-- `D(A_k) ⊆ H¹`: every `F ∈ D(A_k)` has all first weak partials in `L²`. -/
theorem exists_hasWeakPartial_of_mem_domain {F : L2TN L k} (hF : F ∈ (physAk L k).domain)
    (j : Fin k) : ∃ G, HasWeakPartial j F G := by
  refine (mem_range_physH1_iff F).1 ?_ j
  rw [PhysH1.range_val]
  refine Summable.of_nonneg_of_le (fun w => mul_nonneg (kinWeight_nonneg w) (by positivity))
    (fun w => ?_)
    ((mem_physAk_domain_iff F).1 hF)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  nlinarith [one_le_kinWeight L k w]

/-! ## The operator and form identities -/

/-- **`A_k F = F − Σⱼ ∂ⱼ²F`** with the weak second partials. -/
theorem physAk_eq_sub_sum (F : (physAk L k).domain) (H : Fin k → L2TN L k)
    (hH : ∀ j, HasWeakSecondPartial j j (F : L2TN L k) (H j)) :
    physAk L k F = (F : L2TN L k) - ∑ j, H j := by
  apply (momUnitary L k).injective
  ext w
  rw [momUnitary_physAk, map_sub, map_sum, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum,
    Finset.sum_apply]
  simp_rw [fun j => momUnitary_of_hasWeakSecondPartial (hH j) w]
  set c := (momUnitary L k (F : L2TN L k) : Mom k → ℂ) w
  have e : ∀ j, ikn L (w j) * (ikn L (w j) * c) = -((freq L (w j) : ℂ) ^ 2 * c) := by
    intro j
    unfold ikn
    linear_combination ((freq L (w j) : ℂ) ^ 2 * c) * Complex.I_sq
  simp_rw [e]
  rw [Finset.sum_neg_distrib, sub_neg_eq_add]
  unfold kinWeight
  push_cast
  rw [add_mul, one_mul, Finset.sum_mul]

/-- **Graph of `A_k` via weak second partials.** `F ∈ D(A_k)` with `A_k F = K` iff there are
weak `∂ⱼ²F = Hⱼ ∈ L²` for every `j` and `K = F − Σⱼ Hⱼ`. -/
theorem mem_graph_physAk_iff (F K : L2TN L k) :
    (∃ hF : F ∈ (physAk L k).domain, physAk L k ⟨F, hF⟩ = K) ↔
      ∃ H : Fin k → L2TN L k, (∀ j, HasWeakSecondPartial j j F (H j)) ∧ K = F - ∑ j, H j := by
  constructor
  · rintro ⟨hF, rfl⟩
    choose H hH using (mem_physAk_domain_iff_second F).1 hF
    exact ⟨H, hH, physAk_eq_sub_sum ⟨F, hF⟩ H hH⟩
  · rintro ⟨H, hH, rfl⟩
    have hF : F ∈ (physAk L k).domain := (mem_physAk_domain_iff_second F).2 fun j => ⟨H j, hH j⟩
    exact ⟨hF, physAk_eq_sub_sum ⟨F, hF⟩ H hH⟩

/-- **`⟪F, ∂ⱼ²F⟫ = −‖∂ⱼF‖²`** (`L²` integration by parts, via Parseval). -/
theorem inner_secondPartial {j : Fin k} {F G H : L2TN L k} (hG : HasWeakPartial j F G)
    (hH : HasWeakSecondPartial j j F H) : ⟪F, H⟫_ℂ = -((‖G‖ ^ 2 : ℝ) : ℂ) := by
  rw [← (momUnitary L k).inner_map_map, lp.inner_eq_tsum, norm_sq_of_hasWeakPartial hG,
    Complex.ofReal_tsum, ← tsum_neg]
  congr 1; funext w
  rw [RCLike.inner_apply', momUnitary_of_hasWeakSecondPartial hH w]
  set c := (momUnitary L k F : Mom k → ℂ) w
  have e : conj c * (ikn L (w j) * (ikn L (w j) * c)) =
      (Complex.I * Complex.I) * (freq L (w j) : ℂ) ^ 2 * (conj c * c) := by
    unfold ikn; ring
  rw [e, Complex.conj_mul', Complex.I_mul_I]
  push_cast
  ring

/-- **Form identity on `D(A_k)`:** `⟪F, A_k F⟫ = ‖F‖² + Σⱼ ‖∂ⱼF‖²`. -/
theorem inner_physAk_self_eq (F : (physAk L k).domain) (G : Fin k → L2TN L k)
    (hG : ∀ j, HasWeakPartial j (F : L2TN L k) (G j)) :
    ⟪(F : L2TN L k), physAk L k F⟫_ℂ = ((‖(F : L2TN L k)‖ ^ 2 + ∑ j, ‖G j‖ ^ 2 : ℝ) : ℂ) := by
  rw [inner_physAk_self, kinetic_norm_identity _ G hG]

/-- **Form identity, second-partial form:** `⟪F, A_k F⟫ = ‖F‖² − Σⱼ ⟪F, ∂ⱼ²F⟫`. -/
theorem inner_physAk_self_eq_second (F : (physAk L k).domain) (H : Fin k → L2TN L k)
    (hH : ∀ j, HasWeakSecondPartial j j (F : L2TN L k) (H j)) :
    ⟪(F : L2TN L k), physAk L k F⟫_ℂ =
      ((‖(F : L2TN L k)‖ ^ 2 : ℝ) : ℂ) - ∑ j, ⟪(F : L2TN L k), H j⟫_ℂ := by
  rw [physAk_eq_sub_sum F H hH, inner_sub_right, inner_sum, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_pow]
  rfl

end QuantumNLS.ProductSecondDerivatives

#print axioms QuantumNLS.ProductSecondDerivatives.pderiv_isTest
#print axioms QuantumNLS.ProductSecondDerivatives.hasWeakSecondPartial_iff
#print axioms QuantumNLS.ProductSecondDerivatives.hasWeakSecondPartial_iff_iterated
#print axioms QuantumNLS.ProductSecondDerivatives.mem_physAk_domain_iff_second
#print axioms QuantumNLS.ProductSecondDerivatives.mem_physAk_domain_iff_mixed
#print axioms QuantumNLS.ProductSecondDerivatives.physAk_eq_sub_sum
#print axioms QuantumNLS.ProductSecondDerivatives.mem_graph_physAk_iff
#print axioms QuantumNLS.ProductSecondDerivatives.inner_secondPartial
#print axioms QuantumNLS.ProductSecondDerivatives.inner_physAk_self_eq
#print axioms QuantumNLS.ProductSecondDerivatives.inner_physAk_self_eq_second
