import Mathlib
import QuantumNLS.BulkResponseForm
import QuantumNLS.QuantileForm
import QuantumNLS.QuantileCore
import QuantumNLS.QuantileTransport

/-!
# R-8F7E0394 (`CC:F03:deterministic`), stage (R): completeness of the form domain and the Riesz response

Source: the paragraph after `CC:F03:limit-form`: "The form domain is complete for `(L‖F‖₂² + κ𝓔(F))^{1/2}` ... The Riesz representation theorem in this real Hilbert space therefore supplies a unique
`F ∈ 𝒟` with `L⟨F,H⟩ + κ∬ … = ⟨Q,H⟩ (H ∈ 𝒟)`."

The form domain is realized as the graph `G` of `a ↦ (√κ/√L) · [(a(t)-a(s))/(Q(t)-Q(s))]` in the Hilbert space `L²(0,1) × L²((0,1)²)` (`WithLp 2`): `F ↦ (√L F, √κ DF)`.
Objects of `BulkResponseForm` are used read-only (`quot`, `formEnergy`, `bulkForm`, `IsBulkResponse`, `L2Unit`); no competing definitions.

* `isClosed_G`: `G` is closed (a.e.-convergent subsequences);
* `exists_response`: for measurable `Q ∈ L²(0,1)` (the finite second moment, carried as the printed hypothesis) there is `W` with `IsBulkResponse L κ Q W` (orthogonal projection onto `G`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.BulkResponseRiesz

open QuantumNLS.BulkResponseForm (quot formEnergy bulkForm L2Unit IsBulkResponse formDomain)
open QuantumNLS.QuantileForm (uI)

/-- The square `(0,1)²` with Lebesgue measure. -/
abbrev mu2 : Measure (ℝ × ℝ) := uI.prod uI

/-- `L²((0,1)²)`. -/
abbrev L2P : Type := Lp ℝ 2 mu2

/-- The ambient Hilbert space `L²(0,1) × L²((0,1)²)`. -/
abbrev HH : Type := WithLp 2 (L2Unit × L2P)

theorem ae_fst {P : ℝ → Prop} (h : ∀ᵐ t ∂uI, P t) : ∀ᵐ p ∂mu2, P p.1 :=
  (Measure.quasiMeasurePreserving_fst (μ := uI) (ν := uI)).ae h

theorem ae_snd {P : ℝ → Prop} (h : ∀ᵐ t ∂uI, P t) : ∀ᵐ p ∂mu2, P p.2 :=
  (Measure.quasiMeasurePreserving_snd (μ := uI) (ν := uI)).ae h

/-- A subsequence converging a.e. -/
theorem ae_subseq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : ℕ → Lp ℝ 2 ν} {g : Lp ℝ 2 ν}
    (h : Tendsto f atTop (𝓝 g)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂ν, Tendsto (fun i => (f (ns i) : α → ℝ) x) atTop (𝓝 (g x)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have h1 := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' f g).1 h
  have h2 := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (μ := ν) (p := 2) (by norm_num) (by simp)
    (f := fun n => (f n : α → ℝ)) (g := (g : α → ℝ)) h1
  exact h2.exists_seq_tendsto_ae

variable (L κ : ℝ) (Q : ℝ → ℝ)

/-- The graph relation: `b = (√κ/√L) D a`. -/
def Gset : Set HH :=
  {x | (((WithLp.ofLp x).2 : L2P) : ℝ × ℝ → ℝ) =ᵐ[mu2]
    fun p => (Real.sqrt κ / Real.sqrt L) * quot Q (((WithLp.ofLp x).1 : L2Unit) : ℝ → ℝ) p.1 p.2}

theorem quot_add (F G : ℝ → ℝ) (p : ℝ × ℝ) :
    quot Q (fun t => F t + G t) p.1 p.2 = quot Q F p.1 p.2 + quot Q G p.1 p.2 := by
  unfold quot; ring

theorem quot_smul (c : ℝ) (F : ℝ → ℝ) (p : ℝ × ℝ) :
    quot Q (fun t => c * F t) p.1 p.2 = c * quot Q F p.1 p.2 := by
  unfold quot; ring

/-- `G` as a submodule. -/
def Gsub : Submodule ℝ HH where
  carrier := Gset L κ Q
  add_mem' := by
    intro x y hx hy
    simp only [Gset, mem_setOf_eq] at hx hy ⊢
    simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add]
    filter_upwards [Lp.coeFn_add (WithLp.ofLp x).2 (WithLp.ofLp y).2, hx, hy,
      ae_fst (Lp.coeFn_add (WithLp.ofLp x).1 (WithLp.ofLp y).1),
      ae_snd (Lp.coeFn_add (WithLp.ofLp x).1 (WithLp.ofLp y).1)] with p a b c d e
    rw [a, Pi.add_apply, b, c]
    unfold quot
    rw [d, e]
    simp only [Pi.add_apply]
    ring
  zero_mem' := by
    simp only [Gset, mem_setOf_eq]
    simp only [WithLp.ofLp_zero, Prod.fst_zero, Prod.snd_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 mu2, ae_fst (Lp.coeFn_zero ℝ 2 uI), ae_snd (Lp.coeFn_zero ℝ 2 uI)]
      with p a b c
    rw [a]
    unfold quot
    simp [b, c]
  smul_mem' := by
    intro r x hx
    simp only [Gset, mem_setOf_eq] at hx ⊢
    simp only [WithLp.ofLp_smul, Prod.smul_fst, Prod.smul_snd]
    filter_upwards [Lp.coeFn_smul r (WithLp.ofLp x).2, hx,
      ae_fst (Lp.coeFn_smul r (WithLp.ofLp x).1), ae_snd (Lp.coeFn_smul r (WithLp.ofLp x).1)]
      with p a b c d
    rw [a, Pi.smul_apply, b]
    unfold quot
    rw [c, d]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring


theorem isClosed_G : IsClosed (Gsub L κ Q : Set HH) := by
  rw [← isSeqClosed_iff_isClosed]
  intro xs x hxs hlim
  have he := (WithLp.prodContinuousLinearEquiv 2 ℝ L2Unit L2P).continuous.tendsto x |>.comp hlim
  have hfst : Tendsto (fun n => (WithLp.ofLp (xs n)).1) atTop (𝓝 (WithLp.ofLp x).1) :=
    (continuous_fst.tendsto _).comp he
  have hsnd : Tendsto (fun n => (WithLp.ofLp (xs n)).2) atTop (𝓝 (WithLp.ofLp x).2) :=
    (continuous_snd.tendsto _).comp he
  obtain ⟨n1, hn1, hae1⟩ := ae_subseq hfst
  obtain ⟨n2, hn2, hae2⟩ := ae_subseq (hsnd.comp hn1.tendsto_atTop)
  have hns : StrictMono (n1 ∘ n2) := hn1.comp hn2
  have A : ∀ᵐ t ∂uI, Tendsto (fun k => (((WithLp.ofLp (xs (n1 (n2 k)))).1 : L2Unit) : ℝ → ℝ) t) atTop
      (𝓝 (((WithLp.ofLp x).1 : L2Unit) t)) := hae1.mono fun t ht => ht.comp hn2.tendsto_atTop
  have C : ∀ᵐ p ∂mu2, ∀ k, (((WithLp.ofLp (xs (n1 (n2 k)))).2 : L2P) : ℝ × ℝ → ℝ) p =
      (Real.sqrt κ / Real.sqrt L) * quot Q (((WithLp.ofLp (xs (n1 (n2 k)))).1 : L2Unit) : ℝ → ℝ) p.1 p.2 :=
    ae_all_iff.2 fun k => hxs (n1 (n2 k))
  show (((WithLp.ofLp x).2 : L2P) : ℝ × ℝ → ℝ) =ᵐ[mu2]
    fun p => (Real.sqrt κ / Real.sqrt L) * quot Q (((WithLp.ofLp x).1 : L2Unit) : ℝ → ℝ) p.1 p.2
  filter_upwards [ae_fst A, ae_snd A, hae2, C] with p h1 h2 h3 h4
  have hlimq : Tendsto (fun k => (Real.sqrt κ / Real.sqrt L) *
      quot Q (((WithLp.ofLp (xs (n1 (n2 k)))).1 : L2Unit) : ℝ → ℝ) p.1 p.2) atTop
      (𝓝 ((Real.sqrt κ / Real.sqrt L) * quot Q (((WithLp.ofLp x).1 : L2Unit) : ℝ → ℝ) p.1 p.2)) := by
    unfold quot
    exact ((h1.sub h2).div_const (Q p.1 - Q p.2)).const_mul _
  have h3' : Tendsto (fun k => (Real.sqrt κ / Real.sqrt L) *
      quot Q (((WithLp.ofLp (xs (n1 (n2 k)))).1 : L2Unit) : ℝ → ℝ) p.1 p.2) atTop
      (𝓝 ((((WithLp.ofLp x).2 : L2P) : ℝ × ℝ → ℝ) p)) :=
    h3.congr fun k => h4 k
  exact tendsto_nhds_unique h3' hlimq


theorem inner_eq_integral {α : Type*} [MeasurableSpace α] {ν : Measure α} (f g : Lp ℝ 2 ν) :
    inner ℝ f g = ∫ x, (f : α → ℝ) x * (g : α → ℝ) x ∂ν := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [inner, mul_comm]

theorem ofReal_norm_sq' {α : Type*} [MeasurableSpace α] {ν : Measure α} (F : Lp ℝ 2 ν) :
    ENNReal.ofReal (‖F‖ ^ 2) = ∫⁻ x, ENNReal.ofReal ((F : α → ℝ) x ^ 2) ∂ν := by
  have h1 : ‖F‖ ^ 2 = ∫ x, (F : α → ℝ) x ^ 2 ∂ν := by
    rw [← real_inner_self_eq_norm_sq, inner_eq_integral]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [sq])
  rw [h1]
  have hi : Integrable (fun x => (F : α → ℝ) x ^ 2) ν := (Lp.memLp F).integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)]

theorem aesm_quot (hQm : Measurable Q) (H : ℝ → ℝ) (hH : AEStronglyMeasurable H uI) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => quot Q H p.1 p.2) mu2 := by
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => H p.1) mu2 :=
    hH.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_fst (μ := uI) (ν := uI))
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => H p.2) mu2 :=
    hH.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd (μ := uI) (ν := uI))
  have hq : Measurable fun p : ℝ × ℝ => (Q p.1 - Q p.2)⁻¹ :=
    ((hQm.comp measurable_fst).sub (hQm.comp measurable_snd)).inv
  have : (fun p : ℝ × ℝ => quot Q H p.1 p.2) = fun p => (H p.1 - H p.2) * (Q p.1 - Q p.2)⁻¹ := by
    funext p; simp [quot, div_eq_mul_inv]
  rw [this]
  exact (h1.sub h2).mul hq.aestronglyMeasurable

theorem memLp_quot (hQm : Measurable Q) (H : L2Unit) (hH : formEnergy Q H < ⊤) :
    MemLp (fun p : ℝ × ℝ => quot Q H p.1 p.2) 2 mu2 := by
  have hm := aesm_quot Q hQm H (Lp.aestronglyMeasurable H)
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  have hsq : AEStronglyMeasurable (fun p : ℝ × ℝ => (quot Q H p.1 p.2) ^ 2) mu2 := by
    exact (hm.mul hm).congr (Eventually.of_forall fun p => by simp [sq])
  exact (lintegral_ofReal_ne_top_iff_integrable hsq (Eventually.of_forall fun p => sq_nonneg _)).1 hH.ne

end QuantumNLS.BulkResponseRiesz

namespace QuantumNLS.BulkResponseRiesz

open MeasureTheory Filter Topology Set
open scoped ENNReal
open QuantumNLS.BulkResponseForm (quot formEnergy bulkForm L2Unit IsBulkResponse formDomain
  BulkMeasure BulkResponseData bulkQuantile IsFormCore IsSmoothQuantilePullback)
open QuantumNLS.QuantileForm (uI formEnergy_congr quantile_ae_qm)
open QuantumNLS.QuantileTransport (qm HasFiniteSecondMoment)

variable {L κ : ℝ} {Q : ℝ → ℝ}

theorem quot_congr {F G : ℝ → ℝ} (h : F =ᵐ[uI] G) :
    (fun p : ℝ × ℝ => quot Q F p.1 p.2) =ᵐ[mu2] fun p => quot Q G p.1 p.2 := by
  filter_upwards [ae_fst h, ae_snd h] with p h1 h2
  simp only [quot, h1, h2]

theorem quot_congrQ {Q' : ℝ → ℝ} (hQ : Q =ᵐ[uI] Q') (F : ℝ → ℝ) :
    (fun p : ℝ × ℝ => quot Q F p.1 p.2) =ᵐ[mu2] fun p => quot Q' F p.1 p.2 := by
  filter_upwards [ae_fst hQ, ae_snd hQ] with p h1 h2
  simp only [quot, h1, h2]

/-! ### Membership in the form domain, differences -/

theorem mem_formDomain_iff (hQm : Measurable Q) (F : L2Unit) :
    F ∈ formDomain Q ↔ MemLp (fun p : ℝ × ℝ => quot Q F p.1 p.2) 2 mu2 := by
  constructor
  · intro h; exact memLp_quot Q hQm F h
  · intro h
    have hm := aesm_quot Q hQm F (Lp.aestronglyMeasurable F)
    have hi := (memLp_two_iff_integrable_sq hm).1 h
    have hsq : AEStronglyMeasurable (fun p : ℝ × ℝ => (quot Q F p.1 p.2) ^ 2) mu2 := hi.1
    show formEnergy Q F < ⊤
    exact lt_top_iff_ne_top.2
      ((lintegral_ofReal_ne_top_iff_integrable hsq (Eventually.of_forall fun p => sq_nonneg _)).2 hi)

theorem sub_mem (hQm : Measurable Q) {F G : L2Unit} (hF : F ∈ formDomain Q) (hG : G ∈ formDomain Q) :
    F - G ∈ formDomain Q := by
  rw [mem_formDomain_iff hQm] at hF hG ⊢
  refine MemLp.ae_eq ?_ (hF.sub hG)
  filter_upwards [quot_congr (Q := Q) (Lp.coeFn_sub F G)] with p h
  have h' : quot Q ((F - G : L2Unit) : ℝ → ℝ) p.1 p.2 = quot Q (⇑F - ⇑G) p.1 p.2 := h
  show quot Q F p.1 p.2 - quot Q G p.1 p.2 = quot Q ((F - G : L2Unit) : ℝ → ℝ) p.1 p.2
  rw [h']
  simp only [quot, Pi.sub_apply]
  ring

/-! ### The embedding `ι : F ↦ (√L F, √κ DF)` of the form domain into `HH` -/

/-- `DF ∈ L²((0,1)²)`: the difference quotient. -/
def D2 (hQm : Measurable Q) (F : L2Unit) (hF : F ∈ formDomain Q) : L2P :=
  (memLp_quot Q hQm F hF).toLp _

theorem D2_ae (hQm : Measurable Q) (F : L2Unit) (hF : F ∈ formDomain Q) :
    ((D2 hQm F hF : L2P) : ℝ × ℝ → ℝ) =ᵐ[mu2] fun p => quot Q F p.1 p.2 :=
  (memLp_quot Q hQm F hF).coeFn_toLp

/-- The embedding of the form domain: `F ↦ (√L F, √κ DF)`. -/
def iota (L κ : ℝ) (hQm : Measurable Q) (F : L2Unit) (hF : F ∈ formDomain Q) : HH :=
  WithLp.toLp 2 (Real.sqrt L • F, Real.sqrt κ • D2 hQm F hF)

theorem aux1 (a s A B d : ℝ) (hs : s ≠ 0) :
    a * ((A - B) / d) = a / s * ((s * A - s * B) / d) := by
  rw [← mul_sub, mul_div_assoc, ← mul_assoc, div_mul_cancel₀ _ hs]

theorem iota_mem (hL : 0 < L) (hQm : Measurable Q) (F : L2Unit) (hF : F ∈ formDomain Q) :
    iota L κ hQm F hF ∈ Gsub L κ Q := by
  show (((WithLp.ofLp (iota L κ hQm F hF)).2 : L2P) : ℝ × ℝ → ℝ) =ᵐ[mu2]
    fun p => (Real.sqrt κ / Real.sqrt L) *
      quot Q (((WithLp.ofLp (iota L κ hQm F hF)).1 : L2Unit) : ℝ → ℝ) p.1 p.2
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  simp only [iota, WithLp.ofLp_toLp]
  filter_upwards [Lp.coeFn_smul (Real.sqrt κ) (D2 hQm F hF), D2_ae hQm F hF,
    quot_congr (Q := Q) (Lp.coeFn_smul (Real.sqrt L) F)] with p a b c
  rw [a, Pi.smul_apply, smul_eq_mul, b]
  rw [show quot Q (⇑(Real.sqrt L • F)) p.1 p.2 = quot Q (Real.sqrt L • ⇑F) p.1 p.2 from c]
  simp only [quot, Pi.smul_apply, smul_eq_mul]
  exact aux1 _ _ _ _ _ hs

/-- **Well-definedness and integrability of the full bilinear form**: for `F, H` in the form domain,
`bulkForm L κ Q F H = ⟨ι F, ι H⟩` in `L²(0,1) × L²((0,1)²)`. -/
theorem bulkForm_eq_inner (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hQm : Measurable Q) (F H : L2Unit)
    (hF : F ∈ formDomain Q) (hH : H ∈ formDomain Q) :
    bulkForm L κ Q F H = inner ℝ (iota L κ hQm F hF) (iota L κ hQm H hH) := by
  simp only [iota, WithLp.prod_inner_apply, WithLp.ofLp_toLp, real_inner_smul_left,
    real_inner_smul_right]
  rw [inner_eq_integral F H, inner_eq_integral (D2 hQm F hF) (D2 hQm H hH)]
  have h2 : ∫ p, ((D2 hQm F hF : L2P) : ℝ × ℝ → ℝ) p * ((D2 hQm H hH : L2P) : ℝ × ℝ → ℝ) p ∂mu2 =
      ∫ p, quot Q F p.1 p.2 * quot Q H p.1 p.2 ∂mu2 := by
    refine integral_congr_ae ?_
    filter_upwards [D2_ae hQm F hF, D2_ae hQm H hH] with p a b
    rw [a, b]
  rw [h2]
  unfold bulkForm
  rw [← mul_assoc, ← mul_assoc, Real.mul_self_sqrt hL, Real.mul_self_sqrt hκ]

theorem bulkForm_symm (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hQm : Measurable Q) (F H : L2Unit)
    (hF : F ∈ formDomain Q) (hH : H ∈ formDomain Q) :
    bulkForm L κ Q F H = bulkForm L κ Q H F := by
  rw [bulkForm_eq_inner hL hκ hQm F H hF hH, bulkForm_eq_inner hL hκ hQm H F hH hF, real_inner_comm]

/-- Coercivity: `L‖F‖² ≤ bulkForm L κ Q F F`. -/
theorem bulkForm_coercive (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hQm : Measurable Q) (F : L2Unit)
    (hF : F ∈ formDomain Q) : L * ‖F‖ ^ 2 ≤ bulkForm L κ Q F F := by
  rw [bulkForm_eq_inner hL hκ hQm F F hF hF, real_inner_self_eq_norm_sq]
  have h : ‖iota L κ hQm F hF‖ ^ 2 = ‖Real.sqrt L • F‖ ^ 2 + ‖Real.sqrt κ • D2 hQm F hF‖ ^ 2 := by
    unfold iota; exact WithLp.prod_norm_sq_eq_of_L2 _
  rw [h, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    Real.sq_sqrt hL, Real.sq_sqrt hκ]
  have : 0 ≤ κ * ‖D2 hQm F hF‖ ^ 2 := by positivity
  linarith

/-- Nonnegativity of the form. -/
theorem bulkForm_nonneg (hL : 0 ≤ L) (hκ : 0 ≤ κ) (hQm : Measurable Q) (F : L2Unit)
    (hF : F ∈ formDomain Q) : 0 ≤ bulkForm L κ Q F F := by
  have := bulkForm_coercive hL hκ hQm F hF
  have h0 : 0 ≤ L * ‖F‖ ^ 2 := by positivity
  linarith

/-- Every point of the graph is `ι F`: `ι` maps the form domain onto `G`. -/
theorem exists_iota (hL : 0 < L) (hκ : 0 < κ) (hQm : Measurable Q) {x : HH}
    (hx : x ∈ Gsub L κ Q) :
    ∃ F : L2Unit, ∃ hF : F ∈ formDomain Q, iota L κ hQm F hF = x := by
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  have hs' : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  obtain ⟨⟨a, b⟩⟩ := x
  have hx' : (b : ℝ × ℝ → ℝ) =ᵐ[mu2]
      fun p => (Real.sqrt κ / Real.sqrt L) * quot Q (a : ℝ → ℝ) p.1 p.2 := hx
  let F : L2Unit := (1 / Real.sqrt L) • a
  have hq : (fun p : ℝ × ℝ => quot Q F p.1 p.2) =ᵐ[mu2]
      fun p => (1 / Real.sqrt κ) * (b : ℝ × ℝ → ℝ) p := by
    filter_upwards [quot_congr (Q := Q) (Lp.coeFn_smul (1 / Real.sqrt L) a), hx'] with p c d
    rw [show quot Q F p.1 p.2 = quot Q ((1 / Real.sqrt L) • ⇑a) p.1 p.2 from c, d]
    simp only [quot, Pi.smul_apply, smul_eq_mul]
    rw [← mul_sub, mul_div_assoc]
    field_simp
  have hF : F ∈ formDomain Q := by
    rw [mem_formDomain_iff hQm]
    exact MemLp.ae_eq hq.symm ((Lp.memLp b).const_mul (1 / Real.sqrt κ))
  refine ⟨F, hF, ?_⟩
  have h1 : Real.sqrt L • F = a := by
    show Real.sqrt L • ((1 / Real.sqrt L) • a) = a
    rw [smul_smul, mul_one_div_cancel hs, one_smul]
  have h2 : Real.sqrt κ • D2 hQm F hF = b := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (Real.sqrt κ) (D2 hQm F hF), D2_ae hQm F hF, hq] with p c d e
    rw [c, Pi.smul_apply, smul_eq_mul, d, e]
    field_simp
  have : iota L κ hQm F hF = WithLp.toLp 2 (a, b) := by
    unfold iota; rw [h1, h2]
  rw [this]

/-- The form domain is complete for the form norm: if `ι F_n` converges in `HH` (e.g. `F_n` Cauchy for the form
norm `(L‖F‖² + κ𝓔(F))^{1/2} = ‖ι F‖`), the limit is `ι F` for some `F` in the form domain. -/
theorem formDomain_complete (hL : 0 < L) (hκ : 0 < κ) (hQm : Measurable Q) (Fs : ℕ → L2Unit)
    (hFs : ∀ n, Fs n ∈ formDomain Q) {x : HH}
    (hx : Tendsto (fun n => iota L κ hQm (Fs n) (hFs n)) atTop (𝓝 x)) :
    ∃ F : L2Unit, ∃ hF : F ∈ formDomain Q, iota L κ hQm F hF = x :=
  exists_iota hL hκ hQm
    ((isClosed_G L κ Q).mem_of_tendsto hx (Eventually.of_forall fun n => iota_mem hL hQm _ _))

theorem iota_sub (hQm : Measurable Q) {F G : L2Unit} (hF : F ∈ formDomain Q) (hG : G ∈ formDomain Q) :
    iota L κ hQm (F - G) (sub_mem hQm hF hG) = iota L κ hQm F hF - iota L κ hQm G hG := by
  have h2 : D2 hQm (F - G) (sub_mem hQm hF hG) = D2 hQm F hF - D2 hQm G hG := by
    apply Lp.ext
    filter_upwards [D2_ae hQm (F - G) (sub_mem hQm hF hG),
      Lp.coeFn_sub (D2 hQm F hF) (D2 hQm G hG), D2_ae hQm F hF, D2_ae hQm G hG,
      quot_congr (Q := Q) (Lp.coeFn_sub F G)] with p a b c d e
    rw [a, b, Pi.sub_apply, c, d]
    have e' : quot Q ((F - G : L2Unit) : ℝ → ℝ) p.1 p.2 = quot Q (⇑F - ⇑G) p.1 p.2 := e
    rw [e']
    simp only [quot, Pi.sub_apply]
    ring
  unfold iota
  rw [h2, smul_sub, smul_sub]
  rfl

/-- **Uniqueness of the response**: two solutions of the form equation coincide (no moment hypothesis needed). -/
theorem response_unique (hL : 0 < L) (hκ : 0 < κ) (hQm : Measurable Q) {W W' : L2Unit}
    (h : IsBulkResponse L κ Q W) (h' : IsBulkResponse L κ Q W') : W = W' := by
  obtain ⟨hW, hWe⟩ := h
  obtain ⟨hW', hWe'⟩ := h'
  have hD := sub_mem hQm hW hW'
  have e1 := hWe _ hD
  have e2 := hWe' _ hD
  rw [bulkForm_eq_inner hL.le hκ.le hQm W _ hW hD] at e1
  rw [bulkForm_eq_inner hL.le hκ.le hQm W' _ hW' hD] at e2
  have hsub : inner ℝ (iota L κ hQm W hW - iota L κ hQm W' hW') (iota L κ hQm (W - W') hD) = 0 := by
    rw [inner_sub_left, e1, e2, sub_self]
  rw [← iota_sub hQm hW hW'] at hsub
  have h0 : iota L κ hQm (W - W') hD = 0 := inner_self_eq_zero.1 hsub
  have h1 : Real.sqrt L • (W - W') = 0 := by
    have := congrArg (fun z : HH => (WithLp.ofLp z).1) h0
    simpa [iota] using this
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_left hs)

/-- **Existence of the response** (Riesz on the closed graph `G`, written as an orthogonal projection):
for measurable `Q ∈ L²(0,1)` the form equation `L⟨W,H⟩ + κ∬… = ⟨Q,H⟩` (`H ∈ 𝒟`) has a solution `W ∈ 𝒟`. -/
theorem exists_response (hL : 0 < L) (hκ : 0 < κ) (hQm : Measurable Q) (hQ2 : MemLp Q 2 uI) :
    ∃ W : L2Unit, IsBulkResponse L κ Q W := by
  haveI : CompleteSpace (Gsub L κ Q) := (isClosed_G L κ Q).completeSpace_coe
  haveI : (Gsub L κ Q).HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace _
  let y : HH := WithLp.toLp 2 ((1 / Real.sqrt L) • hQ2.toLp Q, (0 : L2P))
  let x₀ := (Gsub L κ Q).starProjection y
  have hx₀ : x₀ ∈ Gsub L κ Q := Submodule.starProjection_apply_mem _ _
  have hkey : ∀ x ∈ Gsub L κ Q, inner ℝ x₀ x = inner ℝ y x := by
    intro x hx
    have := Submodule.starProjection_inner_eq_zero y x hx
    rw [inner_sub_left, sub_eq_zero] at this
    exact this.symm
  obtain ⟨W, hW, hWx⟩ := exists_iota hL hκ hQm hx₀
  refine ⟨W, hW, fun H hH => ?_⟩
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.2 hL).ne'
  rw [bulkForm_eq_inner hL.le hκ.le hQm W H hW hH, hWx, hkey _ (iota_mem hL hQm H hH)]
  simp only [iota, y, WithLp.prod_inner_apply, WithLp.ofLp_toLp, inner_zero_left, add_zero,
    real_inner_smul_left, real_inner_smul_right]
  rw [inner_eq_integral]
  have e : ∫ t, (hQ2.toLp Q : ℝ → ℝ) t * (H : ℝ → ℝ) t ∂uI = ∫ t, Q t * (H : ℝ → ℝ) t ∂uI := by
    refine integral_congr_ae ?_
    filter_upwards [hQ2.coeFn_toLp] with t h
    rw [h]
  rw [e]
  field_simp

/-! ### Transfer along `Q =ᵐ Q'` and the DEF-052 statement -/

theorem isBulkResponse_congr {Q' : ℝ → ℝ} (hQ : Q =ᵐ[uI] Q') {W : L2Unit} :
    IsBulkResponse L κ Q W ↔ IsBulkResponse L κ Q' W := by
  have hdom : ∀ F : L2Unit, F ∈ formDomain Q ↔ F ∈ formDomain Q' := fun F => by
    show formEnergy Q F < ⊤ ↔ formEnergy Q' F < ⊤
    rw [formEnergy_congr hQ (Eventually.of_forall fun _ => rfl)]
  have hform : ∀ F H : L2Unit, bulkForm L κ Q F H = bulkForm L κ Q' F H := fun F H => by
    unfold bulkForm
    congr 2
    refine integral_congr_ae ?_
    filter_upwards [quot_congrQ hQ F, quot_congrQ hQ H] with p a b
    rw [a, b]
  have hrhs : ∀ H : L2Unit, ∫ t, Q t * (H : ℝ → ℝ) t ∂uI = ∫ t, Q' t * (H : ℝ → ℝ) t ∂uI := fun H =>
    integral_congr_ae (by filter_upwards [hQ] with t h; rw [h])
  unfold IsBulkResponse
  constructor
  · rintro ⟨hW, h⟩
    exact ⟨(hdom W).1 hW, fun H hH => by rw [← hform, ← hrhs]; exact h H ((hdom H).2 hH)⟩
  · rintro ⟨hW, h⟩
    exact ⟨(hdom W).2 hW, fun H hH => by rw [hform, hrhs]; exact h H ((hdom H).1 hH)⟩

theorem hasFiniteSecondMoment_of_moment {μ : Measure ℝ}
    (h : QuantumNLS.RapidityTransport.HasFiniteMoment 2 μ) : HasFiniteSecondMoment μ := by
  refine ⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ x : ℝ, ‖x ^ 2‖ₑ = ‖x‖ₑ ^ (2 : ℝ) := fun x => by
    rw [enorm_pow]; exact (ENNReal.rpow_two _).symm
  simp_rw [this]
  exact h

/-- **DEF-052 discharged**: for the standing data (`BulkMeasure`, `L, κ > 0`) the form equation has exactly one
solution in the form domain (existence by the Riesz projection, `Q ∈ L²(0,1)` being the printed second-moment
hypothesis; uniqueness by coercivity). -/
theorem _root_.QuantumNLS.BulkResponseForm.BulkResponseData.existsUnique_response (D : BulkResponseData) :
    ∃! W : L2Unit, D.IsResponse W := by
  haveI := D.hμ.isProbability
  have hQ : D.Q =ᵐ[uI] qm D.μ := quantile_ae_qm D.μ
  have hm : MemLp (qm D.μ) 2 uI :=
    QuantumNLS.QuantileTransport.memLp_qm D.μ (hasFiniteSecondMoment_of_moment D.hμ.finiteSecondMoment)
  have hmeas : Measurable (qm D.μ) := QuantumNLS.QuantileTransport.measurable_qm D.μ
  obtain ⟨W, hW⟩ := exists_response D.hL D.hκ hmeas hm
  refine ⟨W, (isBulkResponse_congr hQ).2 hW, fun W' hW' => ?_⟩
  exact response_unique D.hL D.hκ hmeas ((isBulkResponse_congr hQ).1 hW') hW

/-- The core and the response together: the quantile pullbacks of `C_c^∞` are a core of the form, and the form
equation has a unique solution. -/
theorem _root_.QuantumNLS.BulkResponseForm.BulkResponseData.core_and_response (D : BulkResponseData) :
    IsFormCore D.L D.κ D.Q {F | IsSmoothQuantilePullback D.Q F} ∧ ∃! W : L2Unit, D.IsResponse W :=
  ⟨QuantumNLS.QuantileCore.isFormCore_bulk D.L D.κ D.hL D.hκ D.μ D.hμ, D.existsUnique_response⟩

end QuantumNLS.BulkResponseRiesz

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.BulkResponseRiesz.isClosed_G
#print axioms QuantumNLS.BulkResponseRiesz.bulkForm_eq_inner
#print axioms QuantumNLS.BulkResponseRiesz.bulkForm_coercive
#print axioms QuantumNLS.BulkResponseRiesz.formDomain_complete
#print axioms QuantumNLS.BulkResponseRiesz.response_unique
#print axioms QuantumNLS.BulkResponseRiesz.exists_response
#print axioms QuantumNLS.BulkResponseForm.BulkResponseData.existsUnique_response
#print axioms QuantumNLS.BulkResponseForm.BulkResponseData.core_and_response
