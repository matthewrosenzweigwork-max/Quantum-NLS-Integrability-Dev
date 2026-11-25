import NlsGge.NLS38.CutoffFlow38
import NlsGge.NLS38.Functionals38

/-! # GWP piece A6a (part a): truncated-weight machinery

Plan: `campaign/GWP_PLAN.md` §5.1 item 4 and §7 Part A, piece A6a (review note N2, risk R4).

* `TK38 m K : h¹ →L[ℝ] h⁰`, the diagonal multiplier by the frequency-truncated weight
  `wK m K n = min(⟨n⟩, K)^m` (bounded by `K^m` on `h⁰`; composed with `incl01`).  Risk R4 is resolved
  with the existing `multC38`; `‖TK38 m K x‖ = wl2 (wK m K) x` (`norm_TK38`).
* `hasDerivAt_TKsq38`: derivative of `s ↦ ‖TK38 m K (γ s)‖²` along a `C¹` curve of the carrier.
* `scalar_gronwall_two_sided38`: two-sided Gronwall for a scalar function with `|S'| ≤ c |S|`
  (note N2), obtained from `dist_le_two_sided38` of A5b.
* `mem_and_hn_le_of_wK38`: the monotone limit `K → ∞`.
* `cutSol_wK_bound38`: the `K`-uniform estimate `wl2 (wK m K) (u t)² ≤ wl2 (wK m K) (u 0)² e^{c |t|}`
  for cutoff solutions.

Cast convention (§6.0): every Sobolev index is a natural cast.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set
open scoped ComplexConjugate NNReal InnerProductSpace

/-! ## Generic scalar Gronwall (two-sided, on `|S'|`) -/

/-- Two-sided Gronwall for a differentiable scalar function with `|S'(t)| ≤ c |S(t)|` (note N2). -/
theorem scalar_gronwall_two_sided38 {S S' : ℝ → ℝ} {c : ℝ≥0} (hS : ∀ t, HasDerivAt S (S' t) t)
    (hb : ∀ t, |S' t| ≤ c * |S t|) (t : ℝ) : |S t| ≤ |S 0| * Real.exp (c * |t|) := by
  classical
  let f : ℝ → ℝ → ℝ := fun t x => if S t = 0 then 0 else S' t / S t * x
  have hK : ∀ t, LipschitzWith c (f t) := fun t => by
    by_cases h : S t = 0
    · simp only [f, h, ↓reduceIte]
      exact (LipschitzWith.const 0).weaken bot_le
    · simp only [f, h, ↓reduceIte]
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_div]
      have h1 : |S' t| / |S t| ≤ c := by
        rw [div_le_iff₀ (abs_pos.2 h)]; exact hb t
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have hg : ∀ t, HasDerivAt S (f t (S t)) t := fun t => by
    by_cases h : S t = 0
    · have h0 : S' t = 0 := by
        have := hb t
        rw [h, abs_zero, mul_zero] at this
        exact abs_nonpos_iff.1 this
      simp only [f, h, ↓reduceIte]
      rw [← h0]; exact hS t
    · simp only [f, h, ↓reduceIte]
      rw [div_mul_cancel₀ _ h]; exact hS t
  have hh : ∀ t, HasDerivAt (fun _ : ℝ => (0 : ℝ)) (f t 0) t := fun t => by
    simp only [f, mul_zero, ite_self]
    exact hasDerivAt_const t 0
  have := dist_le_two_sided38 hK hg hh t
  simpa [Real.dist_eq] using this

/-! ## The truncated-weight multiplier -/

/-- `h¹ → h⁰`, `x ↦ (wK m K n · x_n)`. -/
def TK38 (m K : ℕ) : H1C38 →L[ℝ] H0C38 :=
  (multC38 ((0 : ℕ) : ℝ) (fun n => ((wK m K n : ℝ) : ℂ)) ((K : ℝ) ^ m) (fun n => by
    rw [Complex.norm_real, Real.norm_of_nonneg (wK_nonneg m K n)]; exact wK_le_K m K n)).comp incl01

theorem coe_TK38 (m K : ℕ) (x : H1C38) (n : ℤ) :
    carrierCoe38 ((0 : ℕ) : ℝ) (TK38 m K x) n = ((wK m K n : ℝ) : ℂ) * carrierCoe38 ((1 : ℕ) : ℝ) x n := by
  unfold TK38
  simp only [ContinuousLinearMap.comp_apply]
  rw [multC38_coe, coe_incl01]

theorem norm_TK38 (m K : ℕ) (x : H1C38) :
    ‖TK38 m K x‖ = wl2 (wK m K) (carrierCoe38 ((1 : ℕ) : ℝ) x) := by
  have h := (carrier_hasSum_norm_sq_zero38 (TK38 m K x)).tsum_eq
  have e : (fun n : ℤ => ‖carrierCoe38 ((0 : ℕ) : ℝ) (TK38 m K x) n‖ ^ 2) =
      fun n => wK m K n ^ 2 * ‖carrierCoe38 ((1 : ℕ) : ℝ) x n‖ ^ 2 := by
    funext n
    rw [coe_TK38, norm_mul, Complex.norm_real, Real.norm_of_nonneg (wK_nonneg m K n), mul_pow]
  rw [e] at h
  unfold wl2
  rw [h, Real.sqrt_sq (norm_nonneg _)]

theorem TK38_sub (m K : ℕ) (x y : H1C38) : TK38 m K (x - y) = TK38 m K x - TK38 m K y :=
  map_sub _ _ _

/-- Derivative of `s ↦ ‖TK(γ s)‖²` along a `C¹` curve of `h¹`. -/
theorem hasDerivAt_TKsq38 (m K : ℕ) {γ : ℝ → H1C38} {γ' : H1C38} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => ‖TK38 m K (γ s)‖ ^ 2) (2 * ⟪TK38 m K (γ t), TK38 m K γ'⟫_ℝ) t :=
  ((TK38 m K).hasFDerivAt.comp_hasDerivAt t h).norm_sq

theorem hasDerivAt_TK38 (m K : ℕ) {γ : ℝ → H1C38} {γ' : H1C38} {t : ℝ} (h : HasDerivAt γ γ' t) :
    HasDerivAt (fun s => TK38 m K (γ s)) (TK38 m K γ') t :=
  (TK38 m K).hasFDerivAt.comp_hasDerivAt t h

theorem abs_two_inner_le38 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) :
    |2 * ⟪a, b⟫_ℝ| ≤ 2 * ‖a‖ * ‖b‖ := by
  rw [abs_mul, abs_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm a b) (by norm_num)

/-! ## `wl2` with phases, and domination by `hn` -/

theorem wl2_phase38 (ω : ℤ → ℝ) (t : ℝ) (x : ℤ → ℂ) : wl2 ω (phase t x) = wl2 ω x := by
  unfold wl2
  simp only [norm_phase_apply]

theorem wl2_wK_le_hn38 (m K : ℕ) (hm : 1 ≤ m) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ)) :
    wl2 (wK m K) x ≤ hn m x := by
  have h1 : Summable fun n => japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 := (mem_seqSobolev_nat_iff38 m x).1 hx
  have h0 : Summable fun n => wK m K n ^ 2 * ‖x n‖ ^ 2 :=
    summable_wK_of_h1 m K (mem_h1_of_mem_nat m hm hx)
  unfold wl2 hn
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun n => ?_) h0 h1)
  have := wK_le_pow m K n
  have hw : wK m K n ^ 2 ≤ (japaneseBracket n ^ m) ^ 2 := pow_le_pow_left₀ (wK_nonneg m K n) this 2
  rw [pow_sq_eq38] at hw
  exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)

/-! ## The limit `K → ∞` -/

/-- Monotone limit `K → ∞`: a `K`-uniform bound on the truncated norms of an `h¹` sequence gives
membership in `h^m` and the same bound on `hn m`. -/
theorem mem_and_hn_le_of_wK38 (m : ℕ) {x : ℤ → ℂ} {B : ℝ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (h : ∀ K : ℕ, wl2 (wK m K) x ≤ B) : x ∈ seqSobolev38 (m : ℝ) ∧ hn m x ≤ B := by
  have hB : 0 ≤ B := (wl2_nonneg38 _ _).trans (h 0)
  have hf0 : ∀ n : ℤ, 0 ≤ japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 := fun n => by
    have := japaneseBracket_pos n
    positivity
  have hfin : ∀ F : Finset ℤ, ∑ n ∈ F, japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 ≤ B ^ 2 := by
    intro F
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ n ∈ F, japaneseBracket n ≤ K :=
      ⟨∑ n ∈ F, ⌈japaneseBracket n⌉₊, fun n hn =>
        (Nat.le_ceil _).trans (by
          exact_mod_cast Finset.single_le_sum (f := fun n => ⌈japaneseBracket n⌉₊)
            (fun _ _ => Nat.zero_le _) hn)⟩
    calc ∑ n ∈ F, japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2
        = ∑ n ∈ F, wK m K n ^ 2 * ‖x n‖ ^ 2 := by
          refine Finset.sum_congr rfl fun n hn => ?_
          unfold wK
          rw [min_eq_left (hK n hn), pow_sq_eq38]
      _ ≤ ∑' n, wK m K n ^ 2 * ‖x n‖ ^ 2 :=
          (summable_wK_of_h1 m K hx).sum_le_tsum F (fun n _ => by
            have := wK_nonneg m K n
            positivity)
      _ = wl2 (wK m K) x ^ 2 := by
          unfold wl2
          rw [Real.sq_sqrt (tsum_nonneg fun n => by
            have := wK_nonneg m K n
            positivity)]
      _ ≤ B ^ 2 := pow_le_pow_left₀ (wl2_nonneg38 _ _) (h K) 2
  have hs : Summable fun n : ℤ => japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 :=
    summable_of_sum_le hf0 hfin
  refine ⟨(mem_seqSobolev_nat_iff38 m x).2 hs, ?_⟩
  unfold hn
  rw [← Real.sqrt_sq hB]
  exact Real.sqrt_le_sqrt (Real.tsum_le_of_sum_le (fun n => hf0 n) hfin)

/-! ## The interaction-picture field in coordinates -/

theorem coe_Gc1_38 (R s : ℝ) (v : H1C38) :
    carrierCoe38 ((1 : ℕ) : ℝ) (Gc 1 le_rfl R s v) =
      phase (-s) ((-(Complex.I * ((cutoff R (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) v)) : ℝ) : ℂ))) •
        nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) v))) := by
  funext n
  rw [Gc_eq_Gchi, carrierCoe38_Gchi, norm_inclOne38_eq_hn]
  simp only [phase, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_TK_Gc38 (m K : ℕ) (R s : ℝ) (v : H1C38) :
    ‖TK38 m K (Gc 1 le_rfl R s v)‖ =
      cutoff R (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) v)) *
        wl2 (wK m K) (nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) v))) := by
  rw [norm_TK38, coe_Gc1_38, wl2_phase38, wl2_smul38, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (cutoff_nonneg _ _)]

theorem cutoff_mul_sq_le38 {R : ℝ} (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) :
    cutoff R r * r ^ 2 ≤ 4 * R ^ 2 := by
  by_cases h : 2 * R ≤ r
  · rw [cutoff_eq_zero hR h, zero_mul]; positivity
  · rw [not_le] at h
    have h1 := cutoff_le_one R r
    have h2 := cutoff_nonneg R r
    have h3 : r ^ 2 ≤ 4 * R ^ 2 := by nlinarith
    calc cutoff R r * r ^ 2 ≤ 1 * r ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      _ ≤ 4 * R ^ 2 := by linarith

/-- The key bound on the truncated norm of the interaction-picture field along a cutoff solution,
with the constant `C` of `hnK_nonlin_le`. -/
theorem norm_TK_Gc_le38 (m K : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (K : ℕ) (x : ℤ → ℂ), x ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      wl2 (wK m K) (nonlin x) ≤ C * hn 1 x ^ 2 * wl2 (wK m K) x)
    {R : ℝ} (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hu1 : ∀ t, u t ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    {v : ℝ → H1C38} (hv : ∀ t, carrierCoe38 ((1 : ℕ) : ℝ) (v t) = phase (-t) (u t)) (t : ℝ) :
    ‖TK38 m K (Gc 1 le_rfl R t (v t))‖ ≤ 4 * R ^ 2 * C * wl2 (wK m K) (u t) := by
  have hph : phase t (carrierCoe38 ((1 : ℕ) : ℝ) (v t)) = u t := by
    rw [hv, phase_phase_neg_apply]
  have hn1 : hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) (v t)) = hn 1 (u t) := by
    rw [hv, hn_phase38]
  rw [norm_TK_Gc38, hph, hn1]
  have h1 := hC K (u t) (hu1 t)
  have hχ := cutoff_nonneg R (hn 1 (u t))
  have hw := wl2_nonneg38 (wK m K) (u t)
  calc cutoff R (hn 1 (u t)) * wl2 (wK m K) (nonlin (u t))
      ≤ cutoff R (hn 1 (u t)) * (C * hn 1 (u t) ^ 2 * wl2 (wK m K) (u t)) :=
        mul_le_mul_of_nonneg_left h1 hχ
    _ = C * (cutoff R (hn 1 (u t)) * hn 1 (u t) ^ 2) * wl2 (wK m K) (u t) := by ring
    _ ≤ C * (4 * R ^ 2) * wl2 (wK m K) (u t) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (cutoff_mul_sq_le38 hR _ (hn_nonneg38 1 _)) hC0) hw
    _ = 4 * R ^ 2 * C * wl2 (wK m K) (u t) := by ring

/-! ## The `K`-uniform estimate for cutoff solutions -/

/-- `K`-uniform persistence estimate (two-sided Gronwall on `|S_K'|`, note N2):
`wl2 (wK m K) (u t) ≤ wl2 (wK m K) (u 0) e^{C R² |t|}`. -/
theorem cutSol_wK_bound38 (m : ℕ) (hm : 1 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
    ∀ (u : ℝ → ℤ → ℂ), IsCutSol R u → ∀ (K : ℕ) (t : ℝ),
      wl2 (wK m K) (u t) ≤ wl2 (wK m K) (u 0) * Real.exp (C * R ^ 2 * |t|) := by
  obtain ⟨C0, hC0, hC⟩ := hnK_nonlin_le m hm
  refine ⟨4 * C0, by positivity, fun R hR u hu K t => ?_⟩
  obtain ⟨v, hv1, hv2⟩ := cutSol_interaction38 hu
  have hnorm : ∀ s, ‖TK38 m K (v s)‖ = wl2 (wK m K) (u s) := fun s => by
    rw [norm_TK38, hv1, wl2_phase38]
  have hGb := fun s => norm_TK_Gc_le38 m K hC0.le (fun K x hx => (hC K x hx).2) hR hu.mem hv1 s
  set S : ℝ → ℝ := fun s => ‖TK38 m K (v s)‖ ^ 2 with hSdef
  set S' : ℝ → ℝ := fun s => 2 * ⟪TK38 m K (v s), TK38 m K (Gc 1 le_rfl R s (v s))⟫_ℝ with hS'def
  have hS : ∀ s, HasDerivAt S (S' s) s := fun s => hasDerivAt_TKsq38 m K (hv2 s)
  have hb : ∀ s, |S' s| ≤ ((8 * C0 * R ^ 2).toNNReal : ℝ) * |S s| := by
    intro s
    have h1 := abs_two_inner_le38 (TK38 m K (v s)) (TK38 m K (Gc 1 le_rfl R s (v s)))
    have h2 := hGb s
    rw [hnorm s] at h1
    have hw := wl2_nonneg38 (wK m K) (u s)
    have hc : (0 : ℝ) ≤ 8 * C0 * R ^ 2 := by positivity
    rw [Real.coe_toNNReal _ hc]
    have hSs : |S s| = wl2 (wK m K) (u s) ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), hSdef]; simp only [hnorm s]
    rw [hSs]
    calc |S' s| ≤ 2 * wl2 (wK m K) (u s) * ‖TK38 m K (Gc 1 le_rfl R s (v s))‖ := h1
      _ ≤ 2 * wl2 (wK m K) (u s) * (4 * R ^ 2 * C0 * wl2 (wK m K) (u s)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 * C0 * R ^ 2 * wl2 (wK m K) (u s) ^ 2 := by ring
  have hG := scalar_gronwall_two_sided38 hS hb t
  have hSt : |S t| = wl2 (wK m K) (u t) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), hSdef]; simp only [hnorm t]
  have hS0 : |S 0| = wl2 (wK m K) (u 0) ^ 2 := by
    rw [abs_of_nonneg (sq_nonneg _), hSdef]; simp only [hnorm 0]
  rw [hSt, hS0, Real.coe_toNNReal _ (show (0 : ℝ) ≤ 8 * C0 * R ^ 2 by positivity)] at hG
  have hex : Real.exp (8 * C0 * R ^ 2 * |t|) = Real.exp (4 * C0 * R ^ 2 * |t|) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [hex, ← mul_pow] at hG
  exact (pow_le_pow_iff_left₀ (wl2_nonneg38 _ _) (mul_nonneg (wl2_nonneg38 _ _) (Real.exp_nonneg _)) (by norm_num)).1 hG

end NlsGge.NLS38
