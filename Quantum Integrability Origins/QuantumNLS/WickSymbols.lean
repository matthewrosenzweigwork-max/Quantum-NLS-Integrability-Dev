import QuantumNLS.Occupation
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Balanced polynomial symbols and the linear Wick map `W_N`

Source: `wick_calculus.tex` (`eq:full-balanced`, `eq:full-Wick`, `thm:full-wick`
`eq:full-product`), `coordinate_conventions.tex` `eq:birkhoff`.

Symbols are finite polynomials `f = ∑ f_{αβ} z^α z̄^β` in the commuting variables `z_a, z̄_a`
(`a ∈ ℤ`), represented as `AddMonoidAlgebra ℂ ((ℤ →₀ ℕ) × (ℤ →₀ ℕ))` (monomial `(α,β)`).
`W_N` is the linear extension of the ungauged Wick monomial `N^{-|α|} (b^*)^β b^α`
(`Occupation.WMono`).  No Bethe gauge or physical identification is asserted: this is the
finite-support algebraic layer.
-/

namespace QuantumNLS.WickSymbols

open QuantumNLS.Occupation

noncomputable section

/-- Monomial exponent pair `(α, β)` standing for `z^α z̄^β`. -/
abbrev Mon := (ℤ →₀ ℕ) × (ℤ →₀ ℕ)

/-- Polynomial symbols in `z_a, z̄_a`. -/
abbrev Sym := AddMonoidAlgebra ℂ Mon

/-- The monomial `z^α z̄^β`. -/
def zm (α β : ℤ →₀ ℕ) : Sym := AddMonoidAlgebra.single (α, β) (1 : ℂ)

lemma zm_mul (α β α' β' : ℤ →₀ ℕ) : zm α β * zm α' β' = zm (α + α') (β + β') := by
  unfold zm
  rw [AddMonoidAlgebra.single_mul_single]
  simp [Prod.mk_add_mk]

/-- Balanced symbols: only monomials with `|α| = |β|` occur (`eq:full-balanced`). -/
def Balanced (f : Sym) : Prop := ∀ p ∈ f.coeff.support, p.1.degree = p.2.degree

/-- A linear map out of `Sym` from its values on monomials. -/
def symLin {M : Type*} [AddCommMonoid M] [Module ℂ M] (v : Mon → M) : Sym →ₗ[ℂ] M :=
  (Finsupp.linearCombination ℂ v) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

lemma symLin_single {M : Type*} [AddCommMonoid M] [Module ℂ M] (v : Mon → M) (p : Mon) (c : ℂ) :
    symLin v (AddMonoidAlgebra.single p c) = c • v p := by
  simp [symLin]

/-- Every symbol is the finite sum of its monomials. -/
lemma sym_expand (f : Sym) :
    f = ∑ p ∈ f.coeff.support, AddMonoidAlgebra.single p (f.coeff p) := by
  calc f = AddMonoidAlgebra.ofCoeff f.coeff := (AddMonoidAlgebra.ofCoeff_coeff f).symm
    _ = AddMonoidAlgebra.ofCoeff (∑ p ∈ f.coeff.support, Finsupp.single p (f.coeff p)) :=
        congrArg AddMonoidAlgebra.ofCoeff (Finsupp.sum_single f.coeff).symm
    _ = ∑ p ∈ f.coeff.support, AddMonoidAlgebra.single p (f.coeff p) :=
        AddMonoidAlgebra.ofCoeff_sum _ _

/-- The linear Wick map `W_N(z^α z̄^β) = N^{-|α|} (b^*)^β b^α` extended linearly. -/
def WN (N : ℕ) : Sym →ₗ[ℂ] Module.End ℂ FS := symLin (fun p : Mon => WMono N p.1 p.2)

lemma WN_single (N : ℕ) (p : Mon) (c : ℂ) :
    WN N (AddMonoidAlgebra.single p c) = c • WMono N p.1 p.2 := symLin_single _ p c

lemma WN_zm (N : ℕ) (α β : ℤ →₀ ℕ) : WN N (zm α β) = WMono N α β := by
  unfold zm; rw [WN_single, one_smul]

/-! ### Derivatives -/

/-- `∂_z^γ`: `z^α z̄^β ↦ (α)_γ z^{α−γ} z̄^β` with the falling factorial `(α)_γ = ∏ α_b!/(α_b−γ_b)!`
(zero unless `γ ≤ α`). -/
def dz (γ : ℤ →₀ ℕ) : Sym →ₗ[ℂ] Sym :=
  symLin (fun p : Mon => (mdesc p.1 γ : ℂ) • AddMonoidAlgebra.single (p.1 - γ, p.2) (1 : ℂ))

/-- `∂_{z̄}^γ`: `z^α z̄^β ↦ (β)_γ z^α z̄^{β−γ}`. -/
def dzb (γ : ℤ →₀ ℕ) : Sym →ₗ[ℂ] Sym :=
  symLin (fun p : Mon => (mdesc p.2 γ : ℂ) • AddMonoidAlgebra.single (p.1, p.2 - γ) (1 : ℂ))

lemma dz_zm (γ α β : ℤ →₀ ℕ) : dz γ (zm α β) = (mdesc α γ : ℂ) • zm (α - γ) β := by
  unfold dz zm; rw [symLin_single, one_smul]

lemma dzb_zm (γ α β : ℤ →₀ ℕ) : dzb γ (zm α β) = (mdesc β γ : ℂ) • zm α (β - γ) := by
  unfold dzb zm; rw [symLin_single, one_smul]

lemma mdesc_eq_zero {α γ : ℤ →₀ ℕ} (h : ¬ γ ≤ α) : mdesc α γ = 0 := by
  unfold mdesc Finsupp.prod
  obtain ⟨b, hb⟩ := not_forall.mp h
  have hb' : α b < γ b := by simpa using hb
  apply Finset.prod_eq_zero (i := b)
  · rw [Finsupp.mem_support_iff]; omega
  · exact Nat.descFactorial_eq_zero_iff_lt.mpr hb'

lemma mfac_pos (γ : ℤ →₀ ℕ) : 0 < mfac γ := by
  unfold mfac Finsupp.prod
  exact Finset.prod_pos (fun b _ => Nat.factorial_pos _)

lemma dz_mul_dzb_zm (γ α β α' β' : ℤ →₀ ℕ) :
    dz γ (zm α β) * dzb γ (zm α' β')
      = ((mdesc α γ * mdesc β' γ : ℕ) : ℂ) • zm (α - γ + α') (β + (β' - γ)) := by
  rw [dz_zm, dzb_zm, smul_mul_assoc, mul_smul_comm, smul_smul, zm_mul, Nat.cast_mul]

/-! ### The exact product formula (`eq:full-product`) -/

/-- Source weight `N^{-|γ|}/γ!`. -/
def wickWeight (N : ℕ) (γ : ℤ →₀ ℕ) : ℂ := (N : ℂ)⁻¹ ^ γ.degree * ((mfac γ : ℕ) : ℂ)⁻¹

/-- Monomial case of `eq:full-product`; the sum may run over any finite set containing every
`γ ≤ α` (the remaining terms vanish). -/
theorem wick_product_zm (N : ℕ) (α β α' β' : ℤ →₀ ℕ) (Γ : Finset (ℤ →₀ ℕ))
    (hΓ : Finset.Iic α ⊆ Γ) :
    WN N (zm α β) * WN N (zm α' β')
      = ∑ γ ∈ Γ, wickWeight N γ • WN N (dz γ (zm α β) * dzb γ (zm α' β')) := by
  rw [WN_zm, WN_zm, WMono_mul]
  have hterm : ∀ γ : ℤ →₀ ℕ, wickWeight N γ • WN N (dz γ (zm α β) * dzb γ (zm α' β'))
      = if γ ≤ α then ((N : ℂ)⁻¹ ^ γ.degree * (mcoef α β' γ : ℂ)) •
          WMono N (α - γ + α') (β + (β' - γ)) else 0 := by
    intro γ
    by_cases hγ : γ ≤ α
    · simp only [hγ, ↓reduceIte]
      rw [dz_mul_dzb_zm, map_smul, WN_zm, smul_smul]
      congr 1
      have h1 := mcoef_mul_mfac α β' γ
      have h2 : ((mfac γ : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (mfac_pos γ).ne'
      unfold wickWeight
      have h3 : ((mdesc α γ * mdesc β' γ : ℕ) : ℂ) = (mcoef α β' γ : ℂ) * ((mfac γ : ℕ) : ℂ) := by
        rw [← h1]; push_cast; ring
      rw [h3]
      field_simp
    · simp only [hγ, ↓reduceIte]
      rw [dz_mul_dzb_zm, mdesc_eq_zero hγ]
      simp
  simp only [hterm]
  have hf : Γ.filter (fun γ => γ ≤ α) = Finset.Iic α := by
    ext γ
    simp only [Finset.mem_filter, Finset.mem_Iic]
    exact ⟨fun h => h.2, fun h => ⟨hΓ (Finset.mem_Iic.mpr h), h⟩⟩
  rw [← Finset.sum_filter, hf]

lemma symLin_expand {M : Type*} [AddCommMonoid M] [Module ℂ M] (v : Mon → M) (h : Sym) :
    symLin v h = ∑ p ∈ h.coeff.support, h.coeff p • v p := by
  conv_lhs => rw [sym_expand h]
  rw [map_sum]
  exact Finset.sum_congr rfl (fun p _ => symLin_single v p _)

lemma symLin_zm {M : Type*} [AddCommMonoid M] [Module ℂ M] (v : Mon → M) (α β : ℤ →₀ ℕ) :
    symLin v (zm α β) = v (α, β) := by
  unfold zm; rw [symLin_single, one_smul]

/-- **Exact polynomial product** (`eq:full-product`, `thm:full-wick`): for balanced or arbitrary
finite polynomial symbols `f, g` and any finite `Γ` containing every `γ ≤ α` for `z^α z̄^β ∈ f`,
`W_N(f) W_N(g) = ∑_{γ∈Γ} N^{-|γ|}/γ! · W_N((∂_z^γ f)(∂_{z̄}^γ g))`. -/
theorem wick_product (N : ℕ) (f g : Sym) (Γ : Finset (ℤ →₀ ℕ))
    (hΓ : ∀ p ∈ f.coeff.support, Finset.Iic p.1 ⊆ Γ) :
    WN N f * WN N g = ∑ γ ∈ Γ, wickWeight N γ • WN N (dz γ f * dzb γ g) := by
  have hL : WN N f * WN N g = ∑ p ∈ f.coeff.support, ∑ q ∈ g.coeff.support,
      (f.coeff p * g.coeff q) • (WN N (zm p.1 p.2) * WN N (zm q.1 q.2)) := by
    have e1 : ∀ h : Sym, WN N h = ∑ p ∈ h.coeff.support, h.coeff p • WN N (zm p.1 p.2) := by
      intro h
      exact (symLin_expand _ h).trans (Finset.sum_congr rfl (fun p _ => by rw [WN_zm]))
    rw [e1 f, e1 g, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [smul_mul_smul_comm]
  have hR : ∀ γ : ℤ →₀ ℕ, dz γ f * dzb γ g = ∑ p ∈ f.coeff.support, ∑ q ∈ g.coeff.support,
      (f.coeff p * g.coeff q) • (dz γ (zm p.1 p.2) * dzb γ (zm q.1 q.2)) := by
    intro γ
    have e1 : dz γ f = ∑ p ∈ f.coeff.support, f.coeff p • dz γ (zm p.1 p.2) := by
      exact (symLin_expand _ f).trans (Finset.sum_congr rfl (fun p _ => by rw [dz]; rw [symLin_zm]))
    have e2 : dzb γ g = ∑ q ∈ g.coeff.support, g.coeff q • dzb γ (zm q.1 q.2) := by
      exact (symLin_expand _ g).trans (Finset.sum_congr rfl (fun q _ => by rw [dzb]; rw [symLin_zm]))
    rw [e1, e2, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [smul_mul_smul_comm]
  rw [hL]
  simp only [hR, map_sum, map_smul, Finset.smul_sum]
  have key : ∀ p ∈ f.coeff.support, ∀ q ∈ g.coeff.support,
      (f.coeff p * g.coeff q) • (WN N (zm p.1 p.2) * WN N (zm q.1 q.2))
        = ∑ γ ∈ Γ, wickWeight N γ • (f.coeff p * g.coeff q) •
            WN N (dz γ (zm p.1 p.2) * dzb γ (zm q.1 q.2)) := by
    intro p hp q _
    rw [wick_product_zm N p.1 p.2 q.1 q.2 Γ (hΓ p hp), Finset.smul_sum]
    exact Finset.sum_congr rfl (fun γ _ => smul_comm _ _ _)
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (key p hp))]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_comm]

/-! ### Balancedness -/

open Classical in
/-- A finite combination of monomials is balanced if every monomial with nonzero coefficient is. -/
lemma balanced_of_sum {ι : Type*} (I : Finset ι) (c : ι → ℂ) (a b : ι → ℤ →₀ ℕ)
    (h : ∀ i ∈ I, c i ≠ 0 → (a i).degree = (b i).degree) :
    Balanced (∑ i ∈ I, c i • zm (a i) (b i)) := by
  intro p hp
  have hc : (∑ i ∈ I, c i • zm (a i) (b i)).coeff
      = ∑ i ∈ I, Finsupp.single (a i, b i) (c i) := by
    rw [AddMonoidAlgebra.coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [zm, AddMonoidAlgebra.coeff_single]
  rw [hc] at hp
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp (Finsupp.support_finsetSum hp)
  have hne : c i ≠ 0 := by
    intro h0; rw [h0, Finsupp.single_zero] at hpi; simp at hpi
  rw [Finsupp.support_single _ hne, Finset.mem_singleton] at hpi
  subst hpi
  exact h i hi hne

lemma coeff_zm_support (f : Sym) (p : Mon) (hp : p ∈ f.coeff.support) : f.coeff p ≠ 0 :=
  Finsupp.mem_support_iff.mp hp

/-- `f * g` as a double sum over monomials. -/
lemma mul_expand (f g : Sym) :
    f * g = ∑ pq ∈ f.coeff.support ×ˢ g.coeff.support,
      (f.coeff pq.1 * g.coeff pq.2) • zm (pq.1.1 + pq.2.1) (pq.1.2 + pq.2.2) := by
  conv_lhs => rw [sym_expand f, sym_expand g]
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  rw [AddMonoidAlgebra.single_mul_single]
  unfold zm
  rw [AddMonoidAlgebra.smul_single', mul_one]
  rfl

lemma dz_expand (γ : ℤ →₀ ℕ) (f : Sym) :
    dz γ f = ∑ p ∈ f.coeff.support, f.coeff p • dz γ (zm p.1 p.2) :=
  (symLin_expand _ f).trans (Finset.sum_congr rfl (fun p _ => by rw [dz]; rw [symLin_zm]))

lemma dzb_expand (γ : ℤ →₀ ℕ) (g : Sym) :
    dzb γ g = ∑ q ∈ g.coeff.support, g.coeff q • dzb γ (zm q.1 q.2) :=
  (symLin_expand _ g).trans (Finset.sum_congr rfl (fun q _ => by rw [dzb]; rw [symLin_zm]))

theorem Balanced.mul {f g : Sym} (hf : Balanced f) (hg : Balanced g) : Balanced (f * g) := by
  rw [mul_expand]
  apply balanced_of_sum
  intro pq hpq _
  rw [Finset.mem_product] at hpq
  have h1 := hf pq.1 hpq.1
  have h2 := hg pq.2 hpq.2
  simp only [map_add]
  omega

/-- The contraction terms of `eq:full-product` are again balanced symbols. -/
theorem Balanced.dz_mul_dzb {f g : Sym} (hf : Balanced f) (hg : Balanced g) (γ : ℤ →₀ ℕ) :
    Balanced (dz γ f * dzb γ g) := by
  have e : dz γ f * dzb γ g = ∑ pq ∈ f.coeff.support ×ˢ g.coeff.support,
      ((f.coeff pq.1 * g.coeff pq.2) * ((mdesc pq.1.1 γ * mdesc pq.2.2 γ : ℕ) : ℂ)) •
        zm (pq.1.1 - γ + pq.2.1) (pq.1.2 + (pq.2.2 - γ)) := by
    rw [dz_expand, dzb_expand, Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [smul_mul_smul_comm, dz_mul_dzb_zm, smul_smul]
  rw [e]
  apply balanced_of_sum
  intro pq hpq hc
  rw [Finset.mem_product] at hpq
  have h1 := hf pq.1 hpq.1
  have h2 := hg pq.2 hpq.2
  have hm : mdesc pq.1.1 γ * mdesc pq.2.2 γ ≠ 0 := by
    intro h0; apply hc; rw [h0]; simp
  have hγ1 : γ ≤ pq.1.1 := by
    by_contra h; exact hm (by rw [mdesc_eq_zero h]; simp)
  have hγ2 : γ ≤ pq.2.2 := by
    by_contra h; exact hm (by rw [mdesc_eq_zero h]; simp)
  have d1 := degree_tsub_add hγ1
  have d2 := degree_tsub_add hγ2
  simp only [map_add]
  omega

/-! ### First-order contraction, symmetrisation and the bracket (`eq:birkhoff`) -/

/-- `C_1(f,g) = ∑_a ∂_{z_a} f ∂_{z̄_a} g` over a finite label set `S`. -/
def C1 (S : Finset ℤ) (f g : Sym) : Sym :=
  ∑ a ∈ S, dz (Finsupp.single a 1) f * dzb (Finsupp.single a 1) g

/-- `S_1(f,g) = ½ (C_1(f,g) + C_1(g,f))`. -/
def S1 (S : Finset ℤ) (f g : Sym) : Sym := (1 / 2 : ℂ) • (C1 S f g + C1 S g f)

/-- The Poisson bracket in the convention `{w_a, w̄_b} = −i δ_{ab}`, `{w_a, w_b} = 0`
(`eq:birkhoff`): `{f,g} = −i ∑_a (∂_{z_a} f ∂_{z̄_a} g − ∂_{z̄_a} f ∂_{z_a} g)`. -/
def pb (S : Finset ℤ) (f g : Sym) : Sym := (-Complex.I) • (C1 S f g - C1 S g f)

/-- `C_1(f,g) = S_1(f,g) + i{f,g}/2` (source, just before `eq:full-product-bound`). -/
theorem C1_eq_S1_add_pb (S : Finset ℤ) (f g : Sym) :
    C1 S f g = S1 S f g + (Complex.I / 2) • pb S f g := by
  unfold S1 pb
  rw [smul_smul]
  have h : (Complex.I / 2) * (-Complex.I) = 1 / 2 := by
    have : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc (Complex.I / 2) * (-Complex.I) = -(Complex.I * Complex.I) / 2 := by ring
      _ = 1 / 2 := by rw [this]; ring
  rw [h, ← smul_add, add_add_sub_cancel, ← two_smul ℂ (C1 S f g), smul_smul]
  norm_num

lemma mdesc_single_one (α : ℤ →₀ ℕ) (c : ℤ) : mdesc α (Finsupp.single c 1) = α c := by
  unfold mdesc
  rw [Finsupp.prod_single_index (by simp)]
  simp

/-- The coordinate `z_a`. -/
def zv (a : ℤ) : Sym := zm (Finsupp.single a 1) 0

/-- The coordinate `z̄_a`. -/
def zbv (a : ℤ) : Sym := zm 0 (Finsupp.single a 1)

lemma zm_zero_zero : zm 0 0 = (1 : Sym) := by
  unfold zm; rw [AddMonoidAlgebra.one_def]; rfl

lemma C1_zv_zbv {S : Finset ℤ} {a : ℤ} (ha : a ∈ S) (b : ℤ) :
    C1 S (zv a) (zbv b) = (if a = b then (1 : ℂ) else 0) • (1 : Sym) := by
  unfold C1 zv zbv
  have hterm : ∀ c ∈ S, dz (Finsupp.single c 1) (zm (Finsupp.single a 1) 0)
      * dzb (Finsupp.single c 1) (zm 0 (Finsupp.single b 1))
      = (if c = a ∧ c = b then (1 : ℂ) else 0) • (1 : Sym) := by
    intro c _
    rw [dz_mul_dzb_zm, mdesc_single_one, mdesc_single_one, ← zm_zero_zero]
    by_cases hca : c = a
    · by_cases hcb : c = b
      · subst hca; subst hcb; simp
      · subst hca; simp [hcb]
    · simp [Finsupp.single_apply, hca]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul]
  congr 1
  by_cases hab : a = b
  · subst hab; simp [ha]
  · simp [hab]; intro c _ hca; exact fun h => hab (hca.symm.trans h) |>.elim

lemma C1_eq_zero_of_term {S : Finset ℤ} {f g : Sym}
    (h : ∀ c ∈ S, dz (Finsupp.single c 1) f * dzb (Finsupp.single c 1) g = 0) : C1 S f g = 0 :=
  Finset.sum_eq_zero h

lemma C1_zbv_zv (S : Finset ℤ) (a b : ℤ) : C1 S (zbv b) (zv a) = 0 :=
  C1_eq_zero_of_term (fun c _ => by
    unfold zbv zv; rw [dz_mul_dzb_zm, mdesc_single_one]; simp)

lemma C1_zv_zv (S : Finset ℤ) (a b : ℤ) : C1 S (zv a) (zv b) = 0 :=
  C1_eq_zero_of_term (fun c _ => by
    unfold zv; rw [dz_mul_dzb_zm, mdesc_single_one]
    simp [mdesc, Finsupp.prod_single_index])

lemma C1_zbv_zbv (S : Finset ℤ) (a b : ℤ) : C1 S (zbv a) (zbv b) = 0 :=
  C1_eq_zero_of_term (fun c _ => by
    unfold zbv; rw [dz_mul_dzb_zm, mdesc_single_one]; simp)

/-- `{w_a, w̄_b} = −i δ_{ab}` (`eq:birkhoff`), for `a ∈ S`. -/
theorem pb_zv_zbv {S : Finset ℤ} {a : ℤ} (ha : a ∈ S) (b : ℤ) :
    pb S (zv a) (zbv b) = (-Complex.I * (if a = b then (1 : ℂ) else 0)) • (1 : Sym) := by
  unfold pb
  rw [C1_zv_zbv ha b, C1_zbv_zv, sub_zero, smul_smul]

/-- `{w_a, w_b} = 0` and `{w̄_a, w̄_b} = 0` (`eq:birkhoff`). -/
theorem pb_zv_zv (S : Finset ℤ) (a b : ℤ) : pb S (zv a) (zv b) = 0 := by
  unfold pb; rw [C1_zv_zv, C1_zv_zv, sub_self, smul_zero]

theorem pb_zbv_zbv (S : Finset ℤ) (a b : ℤ) : pb S (zbv a) (zbv b) = 0 := by
  unfold pb; rw [C1_zbv_zbv, C1_zbv_zbv, sub_self, smul_zero]

/-! ### Splitting off `|γ| = 0, 1` -/

lemma mdesc_zero (α : ℤ →₀ ℕ) : mdesc α 0 = 1 := by simp [mdesc]

lemma dz_zero (f : Sym) : dz 0 f = f := by
  rw [dz_expand]
  conv_rhs => rw [sym_expand f]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [dz_zm, mdesc_zero]
  unfold zm
  simp

lemma dzb_zero (g : Sym) : dzb 0 g = g := by
  rw [dzb_expand]
  conv_rhs => rw [sym_expand g]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [dzb_zm, mdesc_zero]
  unfold zm
  simp

lemma wickWeight_zero (N : ℕ) : wickWeight N 0 = 1 := by simp [wickWeight, mfac]

lemma wickWeight_single (N : ℕ) (a : ℤ) : wickWeight N (Finsupp.single a 1) = (N : ℂ)⁻¹ := by
  simp [wickWeight, mfac, Finsupp.prod_single_index]

lemma WN_one (N : ℕ) : WN N 1 = 1 := by
  rw [← zm_zero_zero, WN_zm]
  simp [WMono, CreMono_zero, AnnMono_zero]

/-- A multi-index of degree one is a single unit vector. -/
lemma exists_single_of_degree_one {γ : ℤ →₀ ℕ} (h : γ.degree = 1) : ∃ a, γ = Finsupp.single a 1 := by
  rw [Finsupp.degree_apply] at h
  have hne : γ.support.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    rw [hc] at h; simp at h
  obtain ⟨a, ha⟩ := hne
  have hpos : 0 < γ a := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp ha)
  have hsum := Finset.add_sum_erase γ.support γ ha
  have hrest : ∑ i ∈ γ.support.erase a, γ i = 0 := by omega
  have hga : γ a = 1 := by omega
  refine ⟨a, ?_⟩
  ext b
  by_cases hb : b = a
  · subst hb; simp [hga]
  · have : γ b = 0 := by
      by_contra hne
      have hbm : b ∈ γ.support.erase a := Finset.mem_erase.mpr ⟨hb, Finsupp.mem_support_iff.mpr hne⟩
      have := Finset.single_le_sum (f := γ) (fun _ _ => Nat.zero_le _) hbm
      have hp : 0 < γ b := Nat.pos_of_ne_zero hne
      omega
    simp [this, hb]

/-- **Product formula with the `|γ| ≤ 1` terms displayed** (the exact identity behind
`eq:full-product-bound`):
`W_N(f) W_N(g) = W_N(fg) + N⁻¹ W_N(C_1(f,g)) + ∑_{|γ|≥2} N^{-|γ|}/γ! W_N(∂_z^γ f ∂_{z̄}^γ g)`,
where `S` contains every label `a` with `e_a ≤ α` for some `z^α z̄^β ∈ f`, and `R` is a finite set
of multi-indices of degree `≥ 2` containing all such `γ ≤ α`. -/
theorem wick_product_split (N : ℕ) (f g : Sym) (S : Finset ℤ) (R : Finset (ℤ →₀ ℕ))
    (hS : ∀ p ∈ f.coeff.support, ∀ a, Finsupp.single a 1 ≤ p.1 → a ∈ S)
    (hR : ∀ p ∈ f.coeff.support, ∀ γ ∈ Finset.Iic p.1, 2 ≤ γ.degree → γ ∈ R)
    (hR2 : ∀ γ ∈ R, 2 ≤ γ.degree) :
    WN N f * WN N g = WN N (f * g) + (N : ℂ)⁻¹ • WN N (C1 S f g)
      + ∑ γ ∈ R, wickWeight N γ • WN N (dz γ f * dzb γ g) := by
  classical
  set T : Finset (ℤ →₀ ℕ) := S.image (fun a => Finsupp.single a 1) with hT
  have hΓ : ∀ p ∈ f.coeff.support, Finset.Iic p.1 ⊆ insert 0 (T ∪ R) := by
    intro p hp γ hγ
    have hγ' : γ ≤ p.1 := Finset.mem_Iic.mp hγ
    rw [Finset.mem_insert, Finset.mem_union]
    by_cases h0 : γ.degree = 0
    · left; exact (Finsupp.degree_eq_zero_iff γ).mp h0
    · by_cases h1 : γ.degree = 1
      · right; left
        obtain ⟨a, rfl⟩ := exists_single_of_degree_one h1
        exact Finset.mem_image.mpr ⟨a, hS p hp a hγ', rfl⟩
      · right; right; exact hR p hp γ hγ (by omega)
  rw [wick_product N f g _ hΓ]
  have hT0 : (0 : ℤ →₀ ℕ) ∉ T ∪ R := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      have := congrArg Finsupp.degree ha
      simp at this
    · have := hR2 0 h; simp at this
  have hdisj : Disjoint T R := by
    rw [Finset.disjoint_left]
    intro γ h1 h2
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
    have := hR2 _ h2
    simp at this
  rw [Finset.sum_insert hT0, Finset.sum_union hdisj, Finset.sum_image
    (fun a _ b _ hab => (Finsupp.single_left_injective one_ne_zero) hab)]
  rw [dz_zero, dzb_zero, wickWeight_zero, one_smul]
  have hC : ∑ a ∈ S, wickWeight N ((fun a => Finsupp.single a 1) a) •
      WN N (dz ((fun a => Finsupp.single a 1) a) f * dzb ((fun a => Finsupp.single a 1) a) g)
      = (N : ℂ)⁻¹ • WN N (C1 S f g) := by
    unfold C1
    rw [map_sum (WN N), Finset.smul_sum]
    exact Finset.sum_congr rfl (fun a _ => by simp only [wickWeight_single])
  rw [hC, add_assoc]

/-! ### Norm of the finite-support carrier and the coefficient bound -/

lemma ip_eq_sum (u v : FS) (s : Finset Occ) (hs : u.support ⊆ s) :
    ip u v = ∑ m ∈ s, (starRingEnd ℂ) (u m) * v m :=
  Finsupp.sum_of_support_subset u hs _ (by simp)

lemma ip_conj_symm (x y : FS) : (starRingEnd ℂ) (ip y x) = ip x y := by
  classical
  have hx : x.support ⊆ x.support ∪ y.support := Finset.subset_union_left
  have hy : y.support ⊆ x.support ∪ y.support := Finset.subset_union_right
  rw [ip_eq_sum y x _ hy, ip_eq_sum x y _ hx, map_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [map_mul, Complex.conj_conj]; ring

/-- `ip` as a pre-inner-product core on the finite-support space (positive semidefinite). -/
@[instance_reducible] def ipCore : PreInnerProductSpace.Core ℂ FS where
  inner := ip
  conj_inner_symm := ip_conj_symm
  re_inner_nonneg := fun x => by
    show 0 ≤ (ip x x).re
    rw [ip_self_re]; exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)
  add_left := ip_add_left
  smul_left := fun x y r => ip_smul_left r x y

/-- The seminorm `‖v‖ = √(Re ⟨v,v⟩) = (∑ |v_m|²)^{1/2}`. -/
def nrm (v : FS) : ℝ := Real.sqrt (ip v v).re

lemma nrm_nonneg (v : FS) : 0 ≤ nrm v := Real.sqrt_nonneg _

lemma nrm_sq (v : FS) : nrm v ^ 2 = (ip v v).re := by
  unfold nrm
  rw [Real.sq_sqrt]
  rw [ip_self_re]; exact Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

lemma nrm_smul (c : ℂ) (v : FS) : nrm (c • v) = ‖c‖ * nrm v := by
  have h : (ip (c • v) (c • v)).re = ‖c‖ ^ 2 * (ip v v).re := by
    rw [ip_smul_left, ip_smul_right, ← mul_assoc, ← Complex.normSq_eq_conj_mul_self,
      Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
  unfold nrm
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg c)]

lemma nrm_zero : nrm 0 = 0 := by simp [nrm, ip_zero_left]

/-- Triangle inequality for `nrm` (Cauchy–Schwarz from Mathlib's `PreInnerProductSpace.Core`). -/
lemma nrm_add_le (u v : FS) : nrm (u + v) ≤ nrm u + nrm v := by
  let _ : SeminormedAddCommGroup FS := InnerProductSpace.Core.toSeminormedAddCommGroup (c := ipCore)
  exact norm_add_le u v

lemma nrm_sum_le {ι : Type*} (s : Finset ι) (f : ι → FS) : nrm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nrm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nrm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (nrm_add_le _ _).trans (by linarith)

/-- `‖f‖_coeff = ∑ |f_{αβ}|`. -/
def coeffNorm (h : Sym) : ℝ := ∑ p ∈ h.coeff.support, ‖h.coeff p‖

/-- **`eq:full-coefficient-bound`** (finite-support, ungauged): for a balanced symbol `h`, `N > 0`
and a vector supported on arrays of total `N`, `‖W_N(h) v‖ ≤ ‖h‖_coeff ‖v‖`. -/
theorem WN_norm_le {N : ℕ} (hN : 0 < N) {h : Sym} (hb : Balanced h) {v : FS}
    (hv : InSector N v) : nrm (WN N h v) ≤ coeffNorm h * nrm v := by
  have e : WN N h v = ∑ p ∈ h.coeff.support, h.coeff p • WMono N p.1 p.2 v := by
    have : WN N h = ∑ p ∈ h.coeff.support, h.coeff p • WMono N p.1 p.2 :=
      (symLin_expand _ h)
    rw [this, LinearMap.sum_apply]
    rfl
  rw [e]
  refine (nrm_sum_le _ _).trans ?_
  unfold coeffNorm
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun p hp => ?_)
  rw [nrm_smul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have := WMono_norm_le hN (α := p.1) (β := p.2) (hb p hp).symm hv
  unfold nrm
  exact Real.sqrt_le_sqrt this

/-! Axiom audit (printed at compile time). -/
#print axioms zm_mul
#print axioms symLin_single
#print axioms sym_expand
#print axioms WN_one
#print axioms dz_mul_dzb_zm
#print axioms mdesc_eq_zero
#print axioms wick_product_zm
#print axioms wick_product
#print axioms Balanced.mul
#print axioms Balanced.dz_mul_dzb
#print axioms C1_eq_S1_add_pb
#print axioms C1_zv_zbv
#print axioms pb_zv_zbv
#print axioms pb_zv_zv
#print axioms pb_zbv_zbv
#print axioms dz_zero
#print axioms exists_single_of_degree_one
#print axioms wick_product_split
#print axioms ip_conj_symm
#print axioms nrm_add_le
#print axioms WN_norm_le

end

end QuantumNLS.WickSymbols
