import Mathlib
import QuantumNLS.TranslatedCorrelation

/-!
# REG-006 stage (a): Fourier bridge for translated correlations (`CC:G04:correlation`)

Source: `source/chapters/regularity/integer_moments.tex`, lines 159--173 (the formula `C(h) = ∫∏ f_j(x+h_j)`).
Stage (a) of the split REG-006 work: the Fourier-series formula for `C`, with absolute summability of the
constrained family. Stages (b) lattice estimate and (c) differentiation/Taylor are NOT in this file.

Realized objects used read-only:
* `QuantumNLS.TranslatedCorrelation` (checkpoint 8d5aecb3): `Hk`, `toF1`, `contRep`, `Cfun`, `Cfun_eq_cont`;
* `QuantumNLS.Sobolev`: `WField.summable_norm_f04`, `sobolevEmbedding_apply`, `sobolevSeries_apply`;
* `QuantumNLS.Fourier`: `mode`, `coeff`, `coeff_mode`, `torus_mass`, `fourierL2`, `seriesRep`;
* Mathlib `AddCircle.fourier` (continuous characters), `fourier_apply`, `fourier_zero`, `toCircle_add`.

Route: the Fourier route of the integrator's suggestion. The coefficients are the realized
`fourierL2 L (toF1 hk f).val n`, and no new Sobolev space is introduced.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle Filter
open scoped BigOperators ENNReal ComplexConjugate

namespace QuantumNLS.CorrelationFourierBridge

open QuantumNLS.Sobolev QuantumNLS.Fourier QuantumNLS.TranslatedCorrelation

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. Characters: norms, point and index additivity -/

theorem norm_fourier_apply (n : ℤ) (x : AddCircle L) : ‖fourier n x‖ = 1 :=
  Circle.norm_coe _

theorem fourier_add_point (n : ℤ) (x y : AddCircle L) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp_rw [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

theorem fourier_prod_eq {q : ℕ} (x : AddCircle L) : ∀ n : Fin q → ℤ,
    ∏ j, fourier (n j) x = fourier (∑ j, n j) x := by
  induction q with
  | zero => intro n; simp [fourier_zero]
  | succ q ih =>
    intro n
    rw [Fin.prod_univ_succ, ih (fun j => n j.succ), Fin.sum_univ_succ, fourier_add]

/-! ## 2. The integral of a Fourier character (from `coeff_mode`)

`∫ fourier m = L · [m = 0]`. This is proved from `coeff_mode` at frequency `0`, where `mode 0 = L^{-1/2}`
is constant. Nothing is assumed. -/

theorem integral_fourier_eq (m : ℤ) :
    ∫ x : AddCircle L, fourier m x ∂(volume : Measure (AddCircle L)) =
      if m = 0 then (L : ℂ) else 0 := by
  have hL : (0 : ℝ) < L := Fact.out
  have h := coeff_mode (L := L) m 0
  unfold coeff at h
  have hs : (Real.sqrt L)⁻¹ * (Real.sqrt L)⁻¹ = (L : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hL.le]
  have hc : (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) = (((L : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hs]
  have hpt : ∀ x : AddCircle L, conj (mode L 0 x) * mode L m x =
      (((L : ℝ)⁻¹ : ℝ) : ℂ) * fourier m x := by
    intro x
    unfold mode
    rw [fourier_zero, mul_one, Complex.conj_ofReal, ← mul_assoc, hc]
  simp_rw [hpt] at h
  rw [integral_const_mul] at h
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have key : (((L : ℝ)⁻¹ : ℝ) : ℂ) * (L : ℂ) = 1 := by
    push_cast
    field_simp
  by_cases hm : m = 0
  · subst hm
    simp only [if_true, eq_self_iff_true] at h ⊢
    linear_combination (L : ℂ) * h - (∫ x : AddCircle L, fourier 0 x ∂(volume : Measure (AddCircle L))) * key
  · have hm' : (0 : ℤ) ≠ m := fun e => hm e.symm
    simp only [if_neg hm', if_neg hm] at h ⊢
    have hinv : (((L : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := by
      have : (L : ℝ)⁻¹ ≠ 0 := inv_ne_zero hL.ne'
      exact_mod_cast this
    exact (mul_eq_zero.1 h).resolve_left hinv

/-! ## 3. Product of absolutely summable families over `Fin (q+1) → ℤ` -/

/-- Summability of a product of two nonnegative summable real families on a product index set. -/
theorem summable_pair_mul {ι ι' : Type} (f : ι → ℝ) (g : ι' → ℝ) (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ a, 0 ≤ f a) (hg0 : ∀ b, 0 ≤ g b) : Summable fun x : ι × ι' => f x.1 * g x.2 :=
  Summable.mul_of_nonneg hf hg (fun a => hf0 a) (fun b => hg0 b)

set_option maxHeartbeats 1000000 in
theorem prod_tsum_aux (q : ℕ) : ∀ u : Fin (q + 1) → ℤ → ℂ, (∀ j, Summable fun n => ‖u j n‖) →
    Summable (fun n : Fin (q + 1) → ℤ => ‖∏ j, u j (n j)‖) ∧
      ∏ j, (∑' n, u j n) = ∑' n : Fin (q + 1) → ℤ, ∏ j, u j (n j) := by
  induction q with
  | zero =>
    intro u hu
    let E : (Fin 1 → ℤ) ≃ ℤ := Equiv.funUnique (Fin 1) ℤ
    have hf : (fun n : Fin (0 + 1) → ℤ => ‖∏ j, u j (n j)‖) = (fun m => ‖u 0 m‖) ∘ E := by
      funext n
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, Function.comp_apply]
      rfl
    refine ⟨?_, ?_⟩
    · rw [hf]
      exact (E.summable_iff).2 (hu 0)
    · simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
      exact (E.tsum_eq (fun m => u 0 m)).symm
  | succ q ih =>
    intro u hu
    let E : ℤ × (Fin (q + 1) → ℤ) ≃ (Fin (q + 1 + 1) → ℤ) :=
      { toFun := fun p => (Fin.cons (α := fun _ : Fin (q + 1 + 1) => ℤ) p.1 p.2 : Fin (q + 1 + 1) → ℤ)
        invFun := fun n => (n 0, Fin.tail n)
        left_inv := fun p => by simp
        right_inv := fun n => Fin.cons_self_tail n }
    have he0 : ∀ p : ℤ × (Fin (q + 1) → ℤ), E p 0 = p.1 := fun p => by
      show (Fin.cons (α := fun _ : Fin (q + 1 + 1) => ℤ) p.1 p.2 : Fin (q + 1 + 1) → ℤ) 0 = p.1
      exact Fin.cons_zero _ _
    have he1 : ∀ (p : ℤ × (Fin (q + 1) → ℤ)) (j : Fin (q + 1)), E p j.succ = p.2 j := fun p j => by
      show (Fin.cons (α := fun _ : Fin (q + 1 + 1) => ℤ) p.1 p.2 : Fin (q + 1 + 1) → ℤ) j.succ = p.2 j
      exact Fin.cons_succ _ _ _
    obtain ⟨hsumG, hprodG⟩ := ih (fun j => u j.succ) (fun j => hu j.succ)
    have hsum0 : Summable (fun a : ℤ => ‖u 0 a‖) := hu 0
    obtain ⟨G, hG⟩ : ∃ G : (Fin (q + 1) → ℤ) → ℝ, G = fun f => ‖∏ j, u j.succ (f j)‖ := ⟨_, rfl⟩
    have hGsum : Summable G := by rw [hG]; exact hsumG
    have hG0 : ∀ f, 0 ≤ G f := by intro f; rw [hG]; exact norm_nonneg _
    have hpair : Summable (fun p : ℤ × (Fin (q + 1) → ℤ) => ‖u 0 p.1‖ * G p.2) :=
      summable_pair_mul (fun a : ℤ => ‖u 0 a‖) G hsum0 hGsum (fun a => norm_nonneg _) hG0
    have hcongr : ∀ p : ℤ × (Fin (q + 1) → ℤ),
        ∏ j : Fin (q + 1 + 1), u j (E p j) = u 0 p.1 * ∏ j : Fin (q + 1), u j.succ (p.2 j) := by
      intro p
      rw [Fin.prod_univ_succ, he0]
      congr 1
    have hnorm_eq : (fun p : ℤ × (Fin (q + 1) → ℤ) => ‖∏ j, u j (E p j)‖) =
        fun p => ‖u 0 p.1‖ * G p.2 := by
      funext p
      rw [hcongr, norm_mul, hG]
    refine ⟨?_, ?_⟩
    · have h1 : Summable (fun p : ℤ × (Fin (q + 1) → ℤ) => ‖∏ j, u j (E p j)‖) := by
        rw [hnorm_eq]
        exact hpair
      exact (E.summable_iff).1 h1
    · rw [Fin.prod_univ_succ, hprodG, tsum_mul_tsum_of_summable_norm hsum0 hsumG]
      rw [← E.tsum_eq (fun n => ∏ j, u j (n j))]
      exact tsum_congr (fun p => (hcongr p).symm)

/-! ## 4. The realized coefficients and the series representation -/

/-- The realized Fourier coefficients `û(n) = ⟨e_n, f⟩` of `f ∈ H^k` (through its F04 `H^1` image). -/
def coefH {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) : ℤ → ℂ :=
  fun n => fourierL2 L (toF1 hk f).val n

theorem summable_norm_coefH {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) :
    Summable fun n => ‖coefH hk f n‖ :=
  WField.summable_norm_f04 (toF1 hk f)

/-- The continuous representative is the realized series `Σ û(n) e_n`, pointwise. -/
theorem contRep_apply_series {k : ℕ} (hk : 1 ≤ k) (f : Hk L k) (x : AddCircle L) :
    contRep hk f x = seriesRep L (coefH hk f) x := by
  unfold contRep
  rw [sobolevEmbedding_apply, sobolevSeries_apply]
  rfl

theorem norm_mode (n : ℤ) (x : AddCircle L) : ‖mode L n x‖ = (Real.sqrt L)⁻¹ := by
  have hL : (0 : ℝ) < L := Fact.out
  unfold mode
  rw [norm_mul, norm_fourier_apply, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]

theorem mode_add_point (n : ℤ) (x y : AddCircle L) :
    mode L n (x + y) = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * (fourier n x * fourier n y) := by
  unfold mode
  rw [fourier_add_point]

/-- The constant of the bridge: `((√L)⁻¹)^q · L = L^{1−q/2}`. -/
theorem const_identity (q : ℕ) :
    (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ q * (L : ℂ) = (((L : ℝ) ^ (1 - (q : ℝ) / 2) : ℝ) : ℂ) := by
  have hL : (0 : ℝ) < L := Fact.out
  have h1 : (Real.sqrt L) ^ q = (L : ℝ) ^ ((q : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have h2 : (L : ℝ) ^ (1 - (q : ℝ) / 2) = L / (L : ℝ) ^ ((q : ℝ) / 2) := by
    rw [Real.rpow_sub hL, Real.rpow_one]
  have h3 : ((Real.sqrt L)⁻¹) ^ q * L = (L : ℝ) ^ (1 - (q : ℝ) / 2) := by
    rw [h2, ← h1, inv_pow]
    ring
  exact_mod_cast h3

/-! ## 5. The Fourier bridge (stage (a)) -/

/-- **Stage (a): Fourier bridge.** For `k ≥ 1`, `q ≥ 1` and `f_j ∈ H^k`, every `h`:
`C(h) = L^{1−q/2} Σ'_{n : Σ n_j = 0} ∏_j û_j(n_j) ∏_j e_{n_j}(h_j)`, with the realized coefficients `û_j` and
the translation phases `e_{n}(h) = fourier n h`. The sum is over the constrained lattice `{n | Σ n_j = 0}`. -/
theorem Cfun_eq_fourier {k q : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) (f : Fin q → Hk L k) (h : Fin q → ℝ) :
    Cfun f h = ∑' n : {n : Fin q → ℤ // ∑ j, n j = 0},
      (((L : ℝ) ^ (1 - (q : ℝ) / 2) : ℝ) : ℂ) *
        ((∏ j, coefH hk (f j) (n.1 j)) * ∏ j, fourier (n.1 j) ((h j : ℝ) : AddCircle L)) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let c : (Fin (q' + 1) → ℤ) → ℂ := fun n =>
    (∏ j, coefH hk (f j) (n j)) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) ^ (q' + 1) *
      ∏ j, fourier (n j) ((h j : ℝ) : AddCircle L)
  -- summability of the twisted coefficient families `n ↦ û_j(n) e_n(y)`
  have hsu : ∀ (j : Fin (q' + 1)) (y : AddCircle L),
      Summable (fun n => ‖coefH hk (f j) n * mode L n y‖) := by
    intro j y
    have h0 := (summable_norm_coefH hk (f j)).mul_right ((Real.sqrt L)⁻¹)
    refine h0.congr (fun n => ?_)
    rw [norm_mul, norm_mode]
  -- pointwise series identity: the product of series is the series of products
  have hpt : ∀ x : AddCircle L, ∏ j, contRep hk (f j) (x + ((h j : ℝ) : AddCircle L)) =
      ∑' n : Fin (q' + 1) → ℤ, c n * fourier (∑ j, n j) x := by
    intro x
    have hser : ∀ j : Fin (q' + 1), contRep hk (f j) (x + ((h j : ℝ) : AddCircle L)) =
        ∑' n, coefH hk (f j) n * mode L n (x + ((h j : ℝ) : AddCircle L)) := by
      intro j
      rw [contRep_apply_series]
      rfl
    simp only [hser]
    have hP := (prod_tsum_aux q' (fun j n => coefH hk (f j) n *
      mode L n (x + ((h j : ℝ) : AddCircle L))) (fun j => hsu j _)).2
    rw [hP]
    refine tsum_congr (fun n => ?_)
    simp only [c, mode_add_point, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, fourier_prod_eq]
    ring
  -- norms of the coefficients of `c`
  have hnorm_c : ∀ n, ‖c n‖ = ‖∏ j, coefH hk (f j) (n j)‖ * (Real.sqrt L)⁻¹ ^ (q' + 1) := by
    intro n
    simp only [c]
    have hf1 : ‖∏ j, fourier (n j) ((h j : ℝ) : AddCircle L)‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one (fun j _ => norm_fourier_apply _ _)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)), norm_prod, hf1, mul_one]
  have hsumc : Summable (fun n => ‖c n‖) := by
    have h0 := (prod_tsum_aux q' (fun j n => coefH hk (f j) n)
      (fun j => summable_norm_coefH hk (f j))).1
    simp only [hnorm_c]
    exact h0.mul_right ((Real.sqrt L)⁻¹ ^ (q' + 1))
  have hcont : ∀ n : Fin (q' + 1) → ℤ, Continuous fun x : AddCircle L => c n * fourier (∑ j, n j) x :=
    fun n => continuous_const.mul (fourier _).continuous
  -- the integrability hypothesis of `integral_tsum`
  have hfin : ∑' n, ∫⁻ x, ‖c n * fourier (∑ j, n j) x‖ₑ ∂(volume : Measure (AddCircle L)) ≠ ∞ := by
    have hL0 : (0 : ℝ) ≤ L := (Fact.out : (0 : ℝ) < L).le
    have hpt2 : ∀ n, ∫⁻ x, ‖c n * fourier (∑ j, n j) x‖ₑ ∂(volume : Measure (AddCircle L)) =
        ENNReal.ofReal (‖c n‖ * L) := by
      intro n
      have hx : ∀ x : AddCircle L, ‖c n * fourier (∑ j, n j) x‖ₑ = ENNReal.ofReal ‖c n‖ := by
        intro x
        rw [← ofReal_norm, norm_mul, norm_fourier_apply, mul_one]
      simp_rw [hx]
      rw [lintegral_const, torus_mass (L := L), ENNReal.ofReal_mul (norm_nonneg _)]
    simp_rw [hpt2]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (norm_nonneg _) hL0) (hsumc.mul_right L)]
    exact ENNReal.ofReal_ne_top
  -- `C(h)` as a sum over the whole lattice, then over the constraint
  have hC : Cfun f h = ∑' n, c n * (if ∑ j, n j = 0 then (L : ℂ) else 0) := by
    rw [Cfun_eq_cont hk f h]
    simp_rw [hpt]
    rw [integral_tsum (fun n => (hcont n).aestronglyMeasurable) hfin]
    refine tsum_congr (fun n => ?_)
    rw [integral_const_mul, integral_fourier_eq]
  have hind : ∀ n : Fin (q' + 1) → ℤ, c n * (if ∑ j, n j = 0 then (L : ℂ) else 0) =
      Set.indicator {n : Fin (q' + 1) → ℤ | ∑ j, n j = 0} (fun n => c n * (L : ℂ)) n := by
    intro n
    by_cases hn : ∑ j, n j = 0
    · simp [Set.indicator, hn]
    · simp [Set.indicator, hn]
  rw [hC]
  simp_rw [hind]
  rw [← tsum_subtype]
  refine tsum_congr (fun n => ?_)
  show c n.1 * (L : ℂ) = _
  simp only [c]
  linear_combination ((∏ j, coefH hk (f j) (n.1 j)) * ∏ j, fourier (n.1 j) ((h j : ℝ) : AddCircle L)) *
    const_identity (L := L) (q' + 1)

/-- **Absolute summability of the constrained family** of the bridge: the norms of the terms of
`Cfun_eq_fourier` are summable over `{n | Σ n_j = 0}`. -/
theorem summable_constrained {k q : ℕ} (hq : 1 ≤ q) (hk : 1 ≤ k) (f : Fin q → Hk L k)
    (h : Fin q → ℝ) :
    Summable fun n : {n : Fin q → ℤ // ∑ j, n j = 0} =>
      ‖(((L : ℝ) ^ (1 - (q : ℝ) / 2) : ℝ) : ℂ) *
        ((∏ j, coefH hk (f j) (n.1 j)) * ∏ j, fourier (n.1 j) ((h j : ℝ) : AddCircle L))‖ := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hS := (prod_tsum_aux q' (fun j n => coefH hk (f j) n)
    (fun j => summable_norm_coefH hk (f j))).1
  have hfull : Summable fun n : Fin (q' + 1) → ℤ =>
      ‖(((L : ℝ) ^ (1 - ((q' + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ) *
        ((∏ j, coefH hk (f j) (n j)) * ∏ j, fourier (n j) ((h j : ℝ) : AddCircle L))‖ := by
    refine (hS.mul_left ‖(((L : ℝ) ^ (1 - ((q' + 1 : ℕ) : ℝ) / 2) : ℝ) : ℂ)‖).congr (fun n => ?_)
    have hf1 : ‖∏ j, fourier (n j) ((h j : ℝ) : AddCircle L)‖ = 1 := by
      rw [norm_prod]
      exact Finset.prod_eq_one (fun j _ => norm_fourier_apply _ _)
    rw [norm_mul, norm_mul, hf1, mul_one]
  exact hfull.subtype {n : Fin (q' + 1) → ℤ | ∑ j, n j = 0}

end QuantumNLS.CorrelationFourierBridge

/-! Axiom audit (every declaration of stage (a)). -/
#print axioms QuantumNLS.CorrelationFourierBridge.Cfun_eq_fourier
#print axioms QuantumNLS.CorrelationFourierBridge.integral_fourier_eq
#print axioms QuantumNLS.CorrelationFourierBridge.fourier_prod_eq
#print axioms QuantumNLS.CorrelationFourierBridge.fourier_add_point
#print axioms QuantumNLS.CorrelationFourierBridge.norm_fourier_apply
#print axioms QuantumNLS.CorrelationFourierBridge.summable_pair_mul
#print axioms QuantumNLS.CorrelationFourierBridge.prod_tsum_aux
#print axioms QuantumNLS.CorrelationFourierBridge.summable_norm_coefH
#print axioms QuantumNLS.CorrelationFourierBridge.contRep_apply_series
#print axioms QuantumNLS.CorrelationFourierBridge.norm_mode
#print axioms QuantumNLS.CorrelationFourierBridge.mode_add_point
#print axioms QuantumNLS.CorrelationFourierBridge.const_identity
#print axioms QuantumNLS.CorrelationFourierBridge.summable_constrained
