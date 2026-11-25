import NlsGge.NLS38.SeqConv38a

/-! # GWP piece A0 (part b): adjointness, `ℓ¹ ≤ C₁ h¹`, carrier norm, probes

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A0.  Part a is `NlsGge.NLS38.SeqConv38a`
(definitions, real core, `ℓ¹` calculus); this file imports it and is the public entry point
`NlsGge.NLS38.SeqConv38` for the A0 API.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate ENNReal

/-! ## Adjointness -/

/-- The change of variables `(n,a) ↦ (a, a-n)`. -/
def shiftEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.2 - p.1)
  invFun q := (q.1 - q.2, q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

theorem summable_adjoint_majorant {f g y : ℤ → ℂ} (hf : Summable fun n => ‖f n‖ ^ 2)
    (hg : IsL1 g) (hy : Summable fun n => ‖y n‖ ^ 2) :
    Summable fun p : ℤ × ℤ => ‖f p.1‖ * (‖g p.2‖ * ‖y (p.1 - p.2)‖) := by
  have hg0 : Summable fun k => ‖g k‖ := hg
  have hslice : ∀ a, Summable fun k => ‖g k‖ * ‖y (a - k)‖ := fun a =>
    (young_convR (a := fun k => ‖g k‖) (b := fun k => ‖y k‖) hg0 (norm_nonneg_fun g)
      (norm_nonneg_fun y) hy a).1
  have hC2 := (young_convR_sq (a := fun k => ‖g k‖) (b := fun k => ‖y k‖) hg0
    (norm_nonneg_fun g) (norm_nonneg_fun y) hy).1
  have hC0 : ∀ a, 0 ≤ convR (fun k => ‖g k‖) (fun k => ‖y k‖) a := fun a =>
    convR_nonneg (norm_nonneg_fun g) (norm_nonneg_fun y) a
  have hG0 : (0 : ℤ × ℤ → ℝ) ≤ fun p : ℤ × ℤ => ‖f p.1‖ * (‖g p.2‖ * ‖y (p.1 - p.2)‖) :=
    fun p => by positivity
  rw [summable_prod_of_nonneg hG0]
  refine ⟨fun a => (hslice a).mul_left ‖f a‖, ?_⟩
  have e : ∀ a, ∑' k, ‖f a‖ * (‖g k‖ * ‖y (a - k)‖) =
      ‖f a‖ * convR (fun k => ‖g k‖) (fun k => ‖y k‖) a := fun a => by
    unfold convR
    exact tsum_mul_left
  simp only [e]
  refine Summable.of_nonneg_of_le (fun a => mul_nonneg (norm_nonneg _) (hC0 a))
    (fun a => ?_) ((hf.add hC2).mul_left (1 / 2))
  nlinarith [sq_nonneg (‖f a‖ - convR (fun k => ‖g k‖) (fun k => ‖y k‖) a)]

/-- Adjointness: `⟨f * g̃, y⟩ = ⟨f, g * y⟩`, for `f, y ∈ ℓ²`, `g ∈ ℓ¹`. -/
theorem inner_conv_cstar {f g y : ℤ → ℂ} (hf : Summable fun n => ‖f n‖ ^ 2) (hg : IsL1 g)
    (hy : Summable fun n => ‖y n‖ ^ 2) :
    ∑' n, conj (conv f (cstar g) n) * y n = ∑' n, conj (f n) * conv g y n := by
  have hGs := summable_adjoint_majorant hf hg hy
  set F : ℤ × ℤ → ℂ := fun p => conj (f p.1) * (g p.2 * y (p.1 - p.2)) with hF
  have hFs : Summable F := by
    refine Summable.of_norm (hGs.congr fun p => ?_)
    simp only [hF, norm_mul, Complex.norm_conj]
  have hH : Summable (F ∘ shiftEquiv) := shiftEquiv.summable_iff.2 hFs
  -- right side
  have hR : ∑' p, F p = ∑' n, conj (f n) * conv g y n := by
    rw [hFs.tsum_prod]
    refine tsum_congr fun a => ?_
    simp only [hF, conv]
    rw [tsum_mul_left]
  -- left side
  have hL : ∑' p, (F ∘ shiftEquiv) p = ∑' n, conj (conv f (cstar g) n) * y n := by
    rw [hH.tsum_prod]
    refine tsum_congr fun n => ?_
    have h1 : conj (conv f (cstar g) n) =
        ∑' a, conj (f a) * g (a - n) := by
      unfold conv
      rw [Complex.conj_tsum]
      refine tsum_congr fun a => ?_
      simp only [cstar, map_mul, Complex.conj_conj, neg_sub]
    rw [h1, ← tsum_mul_right]
    refine tsum_congr fun a => ?_
    simp only [Function.comp, shiftEquiv, Equiv.coe_fn_mk, hF, sub_sub_cancel]
    ring
  rw [← hL, ← hR]
  exact shiftEquiv.tsum_eq F

/-! ## `ℓ¹ ≤ C₁ h¹` and the carrier norm -/

section Sobolev

theorem l1_core (x : ℤ → ℂ) (hs : Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2) :
    IsL1 x ∧ l1 x ≤ C1 * Real.sqrt (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2) := by
  have hw : ∀ p : ℤ, 0 ≤ 1 + (p : ℝ) ^ 2 := fun p => by positivity
  let e : lp (fun _ : ℤ => ℂ) 2 := weightedL2Element (fun p : ℤ => 1 + (p : ℝ) ^ 2) hw x hs
  have hprod : ∀ p : ℤ, ‖e p‖ * ‖NlsGge.Analysis.reciprocalBracketL2 p‖ = ‖x p‖ := by
    intro p
    have hf : ‖e p‖ ^ 2 = (1 + (p : ℝ) ^ 2) * ‖x p‖ ^ 2 := by
      change ‖weightedCoordinates (fun q : ℤ => 1 + (q : ℝ) ^ 2) x p‖ ^ 2 = _
      exact weightedCoordinates_norm_sq _ hw x p
    have hg : ‖NlsGge.Analysis.reciprocalBracketL2 p‖ ^ 2 = 1 / (1 + (p : ℝ) ^ 2) := by
      change ‖weightedCoordinates (fun q => 1 / (1 + (q : ℝ) ^ 2))
        (fun _ => (1 : ℂ)) p‖ ^ 2 = _
      rw [weightedCoordinates_norm_sq _ (fun q => by positivity)]
      simp
    apply (sq_eq_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).1
    rw [mul_pow, hf, hg]
    have hden : 1 + (p : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hden]
  have hHC : (ENNReal.toReal 2).HolderConjugate (ENNReal.toReal 2) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hsm := lp.summable_mul hHC e NlsGge.Analysis.reciprocalBracketL2
  have hle := lp.tsum_mul_le_mul_norm' hHC e NlsGge.Analysis.reciprocalBracketL2
  simp only [hprod] at hsm hle
  have hnorm : ‖e‖ = Real.sqrt (∑' n : ℤ, (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2) := by
    have h := weightedL2Element_norm_sq (fun p : ℤ => 1 + (p : ℝ) ^ 2) hw x hs
    change ‖e‖ ^ 2 = _ at h
    rw [← h, Real.sqrt_sq (norm_nonneg _)]
  exact ⟨hsm, by rw [← hnorm, C1, mul_comm]; exact hle⟩

/-- The carrier norm in coordinates. -/
theorem norm_carrierMk38_eq_sqrt (r : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 r) :
    ‖carrierMk38 r x hx‖ = Real.sqrt (∑' n : ℤ, sobolevModeWeight r n * ‖x n‖ ^ 2) := by
  have h := carrier_hasSum_norm_sq38 r (carrierMk38 r x hx)
  simp only [carrierCoe38_mk] at h
  rw [h.tsum_eq, Real.sqrt_sq (norm_nonneg _)]

theorem sobolevModeWeight_natCast_eq (m : ℕ) (n : ℤ) :
    sobolevModeWeight (m : ℝ) n = japaneseBracket n ^ (2 * m) := by
  unfold sobolevModeWeight
  have : (2 : ℝ) * (m : ℝ) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
  rw [this]
  exact Real.rpow_natCast _ _

theorem sobolevModeWeight_one_eq (n : ℤ) : sobolevModeWeight 1 n = 1 + (n : ℝ) ^ 2 :=
  NlsGge.Analysis.japaneseBracket_h1_weight n

theorem norm_carrierMk38_eq_hn (m : ℕ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 (m : ℝ)) :
    ‖carrierMk38 (m : ℝ) x hx‖ = hn m x := by
  rw [norm_carrierMk38_eq_sqrt]
  unfold hn
  simp only [sobolevModeWeight_natCast_eq]

theorem summable_hn_of_mem (m : ℕ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 (m : ℝ)) :
    Summable fun n : ℤ => japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 := by
  have h : Summable fun n : ℤ => sobolevModeWeight (m : ℝ) n * ‖x n‖ ^ 2 :=
    (mem_seqSobolev38_iff _ x).1 hx
  simpa only [sobolevModeWeight_natCast_eq] using h

theorem hn_sq (m : ℕ) (x : ℤ → ℂ) :
    hn m x ^ 2 = ∑' n : ℤ, japaneseBracket n ^ (2 * m) * ‖x n‖ ^ 2 := by
  unfold hn
  rw [Real.sq_sqrt (tsum_nonneg fun n =>
    mul_nonneg (pow_nonneg (japaneseBracket_pos n).le _) (sq_nonneg _))]

/-- `ℓ¹ ≤ C₁ h¹`, in the form of the plan. -/
theorem isL1_of_h1 (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 1) :
    IsL1 x ∧ l1 x ≤ C1 * ‖carrierMk38 1 x hx‖ := by
  have hs : Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) * ‖x n‖ ^ 2 := by
    have h := (mem_seqSobolev38_iff 1 x).1 hx
    simpa only [SobolevSquareSummable, NlsGge.Analysis.japaneseBracket_h1_weight] using h
  obtain ⟨h1, h2⟩ := l1_core x hs
  refine ⟨h1, ?_⟩
  rw [norm_carrierMk38_eq_sqrt]
  simpa only [sobolevModeWeight_one_eq] using h2

/-- The same with `hn 1` and the cast `((1 : ℕ) : ℝ)` used by `IsNLSSol`. -/
theorem isL1_of_hn_one (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    IsL1 x ∧ l1 x ≤ C1 * hn 1 x := by
  have hx' : x ∈ seqSobolev38 1 := by simpa using hx
  obtain ⟨h1, h2⟩ := isL1_of_h1 x hx'
  refine ⟨h1, ?_⟩
  rw [← norm_carrierMk38_eq_hn 1 x hx]
  have : ‖carrierMk38 ((1 : ℕ) : ℝ) x hx‖ = ‖carrierMk38 1 x hx'‖ := by
    rw [norm_carrierMk38_eq_sqrt, norm_carrierMk38_eq_sqrt]
    simp only [Nat.cast_one]
  rw [this]; exact h2

end Sobolev

/-! ## Regression probes (kept as theorems) -/

section Probes

theorem conv_single_single (j k : ℤ) (α β : ℂ) :
    conv (Pi.single j α) (Pi.single k β) = Pi.single (j + k) (α * β) := by
  funext n
  unfold conv
  rw [tsum_eq_single j (fun a ha => by simp [Pi.single_apply, ha])]
  by_cases h : n = j + k
  · have : n - j = k := by omega
    simp [h]
  · have : ¬ (n - j = k) := by omega
    simp [h, this]

theorem cstar_single (k : ℤ) (a : ℂ) : cstar (Pi.single k a) = Pi.single (-k) (conj a) := by
  funext n
  unfold cstar
  by_cases h : n = -k
  · have : -n = k := by omega
    simp [h]
  · have : ¬ (-n = k) := by omega
    simp [h, this]

/-- `conv (δ₁) (δ₂) = δ₃`. -/
theorem conv_delta_one_two :
    conv (Pi.single (1 : ℤ) (1 : ℂ)) (Pi.single (2 : ℤ) (1 : ℂ)) = Pi.single (3 : ℤ) (1 : ℂ) := by
  rw [conv_single_single]; norm_num

/-- Plane wave: `nonlin (a e_k) = 2 |a|² a e_k`. -/
theorem nonlin_single (k : ℤ) (a : ℂ) :
    nonlin (Pi.single k a) = Pi.single k (2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * a) := by
  funext n
  unfold nonlin
  rw [conv_single_single, cstar_single, conv_single_single]
  have hk : k + k + -k = k := by ring
  have hc : a * a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) * a := by
    have := Complex.mul_conj' a
    push_cast
    calc a * a * conj a = a * (a * conj a) := by ring
      _ = _ := by rw [this]; ring
  rw [hk, hc]
  by_cases h : n = k
  · subst h; simp [mul_assoc]
  · simp [h]

end Probes

end NlsGge.NLS38
