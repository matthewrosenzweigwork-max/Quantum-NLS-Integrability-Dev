import NlsGge.Birkhoff.BirkhoffAPI38
import NlsGge.Analysis.H1Fourier

/-! # GWP piece A0 (part a): sequence convolution on `ℤ`, `ℓ¹ * ℓ²` Young (pointwise), `ℓ¹` calculus

Plan: `campaign/GWP_PLAN.md` §6.1 (definitions) and §7 Part A, piece A0.

Equation (v2 `eq:nls`): `i uₜ = -uₓₓ + 2|u|² u` on `ℝ/ℤ`.  With `u_n = physicalFourier u n`
(`u(x) = ∑ u_n e^{2πinx}`) the Fourier side is
`u_n' = -i ((2πn)² u_n + nonlin u n)`, `nonlin u = 2 ((u * u) * u~)`,
`(f * g)_n = ∑_a f_a g_{n-a}` (`conv`), `u~_k = conj (u_{-k})` (`cstar`, coefficients of `ū`).

All `tsum`s in `conv` are totalised; every identity below carries the summability it needs
(`IsL1` hypotheses), and summability is proved before the value of the sum is used.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate ENNReal

/-! ## Definitions (§6.1) -/

/-- Symbol of `-∂ₓ²` on `ℝ/ℤ`. -/
def disp (n : ℤ) : ℝ := (2 * Real.pi * n) ^ 2

/-- Convolution of two sequences on `ℤ`; totalised, used only on `ℓ¹`/`h¹` data. -/
def conv (f g : ℤ → ℂ) (n : ℤ) : ℂ := ∑' a : ℤ, f a * g (n - a)

/-- Coefficients of `ū`. -/
def cstar (f : ℤ → ℂ) (n : ℤ) : ℂ := conj (f (-n))

/-- `𝓕` on sequences: `fourierSeq38 u = refl (physicalFourier u)`. -/
def refl (f : ℤ → ℂ) (n : ℤ) : ℂ := - f (-n)

/-- Coefficients of `2|u|²u`. -/
def nonlin (x : ℤ → ℂ) (n : ℤ) : ℂ := 2 * conv (conv x x) (cstar x) n

/-- The `h^m` norm of a coefficient sequence (total; meaningful when the sum converges). -/
def hn (m : ℕ) (x : ℤ → ℂ) : ℝ :=
  Real.sqrt (∑' n, (japaneseBracket n) ^ (2 * m) * ‖x n‖ ^ 2)

/-- Absolute summability (`ℓ¹`). -/
def IsL1 (f : ℤ → ℂ) : Prop := Summable fun n => ‖f n‖

/-- The `ℓ¹` norm (meaningful under `IsL1`). -/
def l1 (f : ℤ → ℂ) : ℝ := ∑' n, ‖f n‖

/-- The constant of `ℓ¹ ≤ C₁ h¹`. -/
def C1 : ℝ := ‖NlsGge.Analysis.reciprocalBracketL2‖

/-! ## Real nonnegative core -/

/-- Convolution of real sequences (helper for the nonnegative majorants). -/
def convR (a b : ℤ → ℝ) (n : ℤ) : ℝ := ∑' k : ℤ, a k * b (n - k)

section RealCore

variable {a b : ℤ → ℝ}

/-- The change of variables `(n,k) ↦ (k, n-k)`. -/
def pairEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

theorem summable_pair (ha : Summable a) (hb : Summable b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    Summable fun p : ℤ × ℤ => a p.2 * b (p.1 - p.2) := by
  have h := Summable.mul_of_nonneg ha hb ha0 hb0
  exact (pairEquiv.summable_iff (f := fun q : ℤ × ℤ => a q.1 * b q.2)).2 h

theorem summable_convR_slice (ha : Summable a) (hb : Summable b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (n : ℤ) : Summable fun k => a k * b (n - k) :=
  (summable_pair ha hb ha0 hb0).prod_factor n

theorem summable_convR (ha : Summable a) (hb : Summable b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    Summable (convR a b) :=
  (summable_pair ha hb ha0 hb0).prod

theorem tsum_convR (ha : Summable a) (hb : Summable b) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) :
    ∑' n, convR a b n = (∑' k, a k) * ∑' k, b k := by
  have hp := summable_pair ha hb ha0 hb0
  have h1 : ∑' n, convR a b n = ∑' p : ℤ × ℤ, a p.2 * b (p.1 - p.2) := by
    rw [hp.tsum_prod]; rfl
  rw [h1, Summable.tsum_mul_tsum ha hb (Summable.mul_of_nonneg ha hb ha0 hb0)]
  exact pairEquiv.tsum_eq (fun q : ℤ × ℤ => a q.1 * b q.2)

theorem convR_nonneg (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (n : ℤ) : 0 ≤ convR a b n :=
  tsum_nonneg fun k => mul_nonneg (ha0 k) (hb0 _)

/-- Cauchy-Schwarz for a `tsum`: `(∑ u v)² ≤ (∑ u)(∑ u v²)`, with the summability of `u v`. -/
theorem cs_tsum {u v : ℤ → ℝ} (hu : Summable u) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v)
    (huv2 : Summable fun k => u k * v k ^ 2) :
    Summable (fun k => u k * v k) ∧
      (∑' k, u k * v k) ^ 2 ≤ (∑' k, u k) * ∑' k, u k * v k ^ 2 := by
  have hs : Summable fun k => u k * v k := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hu0 k) (hv0 k)) (fun k => ?_)
      ((hu.add huv2).mul_left (1 / 2))
    have h : v k ≤ (1 + v k ^ 2) / 2 := by nlinarith [sq_nonneg (v k - 1)]
    have := mul_le_mul_of_nonneg_left h (hu0 k)
    nlinarith [this]
  refine ⟨hs, ?_⟩
  set A := ∑' k, u k
  set B := ∑' k, u k * v k ^ 2
  have hA0 : 0 ≤ A := tsum_nonneg hu0
  have hB0 : 0 ≤ B := tsum_nonneg fun k => mul_nonneg (hu0 k) (sq_nonneg _)
  have hfin : ∀ s : Finset ℤ, ∑ k ∈ s, u k * v k ≤ Real.sqrt (A * B) := by
    intro s
    apply Real.le_sqrt_of_sq_le
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq s (fun k => Real.sqrt (u k))
      (fun k => Real.sqrt (u k) * v k)
    have e1 : ∀ k, Real.sqrt (u k) * (Real.sqrt (u k) * v k) = u k * v k := fun k => by
      rw [← mul_assoc, Real.mul_self_sqrt (hu0 k)]
    have e2 : ∀ k, Real.sqrt (u k) ^ 2 = u k := fun k => Real.sq_sqrt (hu0 k)
    have e3 : ∀ k, (Real.sqrt (u k) * v k) ^ 2 = u k * v k ^ 2 := fun k => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at h1
    have hA : ∑ k ∈ s, u k ≤ A := hu.sum_le_tsum s (fun k _ => hu0 k)
    have hB : ∑ k ∈ s, u k * v k ^ 2 ≤ B :=
      huv2.sum_le_tsum s (fun k _ => mul_nonneg (hu0 k) (sq_nonneg _))
    calc (∑ k ∈ s, u k * v k) ^ 2 ≤ (∑ k ∈ s, u k) * ∑ k ∈ s, u k * v k ^ 2 := h1
      _ ≤ A * B := mul_le_mul hA hB (Finset.sum_nonneg fun k _ => mul_nonneg (hu0 k) (sq_nonneg _))
          hA0
  have h2 : ∑' k, u k * v k ≤ Real.sqrt (A * B) := hs.tsum_le_of_sum_le hfin
  have h3 : 0 ≤ ∑' k, u k * v k := tsum_nonneg fun k => mul_nonneg (hu0 k) (hv0 k)
  calc (∑' k, u k * v k) ^ 2 ≤ (Real.sqrt (A * B)) ^ 2 := pow_le_pow_left₀ h3 h2 2
    _ = A * B := Real.sq_sqrt (mul_nonneg hA0 hB0)

/-- Young `ℓ¹ * ℓ²` for nonnegative real sequences, pointwise in `n`. -/
theorem young_convR (ha : Summable a) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hb2 : Summable fun k => b k ^ 2) (n : ℤ) :
    Summable (fun k => a k * b (n - k)) ∧
      (convR a b n) ^ 2 ≤ (∑' k, a k) * convR a (fun k => b k ^ 2) n := by
  have hsq : Summable fun k => a k * b (n - k) ^ 2 :=
    summable_convR_slice ha hb2 ha0 (fun k => sq_nonneg _) n
  exact cs_tsum (v := fun k => b (n - k)) ha ha0 (fun k => hb0 (n - k)) hsq

/-- Young `ℓ¹ * ℓ²` for nonnegative real sequences, summed over `n`. -/
theorem young_convR_sq (ha : Summable a) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (hb2 : Summable fun k => b k ^ 2) :
    Summable (fun n => (convR a b n) ^ 2) ∧
      ∑' n, (convR a b n) ^ 2 ≤ (∑' k, a k) ^ 2 * ∑' k, b k ^ 2 := by
  have hc : Summable (convR a fun k => b k ^ 2) :=
    summable_convR ha hb2 ha0 (fun k => sq_nonneg _)
  have hbound : ∀ n, (convR a b n) ^ 2 ≤ (∑' k, a k) * convR a (fun k => b k ^ 2) n :=
    fun n => (young_convR ha ha0 hb0 hb2 n).2
  have hsum : Summable fun n => (convR a b n) ^ 2 :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hbound (hc.mul_left _)
  refine ⟨hsum, ?_⟩
  calc ∑' n, (convR a b n) ^ 2 ≤ ∑' n, (∑' k, a k) * convR a (fun k => b k ^ 2) n :=
        hsum.tsum_le_tsum hbound (hc.mul_left _)
    _ = (∑' k, a k) * ((∑' k, a k) * ∑' k, b k ^ 2) := by
        rw [tsum_mul_left, tsum_convR ha hb2 ha0 (fun k => sq_nonneg _)]
    _ = (∑' k, a k) ^ 2 * ∑' k, b k ^ 2 := by ring

end RealCore

/-! ## `ℓ¹` calculus for `conv` -/

section L1Calculus

variable {f f' g g' x : ℤ → ℂ}

theorem isL1_iff : IsL1 f ↔ Summable fun n => ‖f n‖ := Iff.rfl

theorem norm_nonneg_fun (f : ℤ → ℂ) : (0 : ℤ → ℝ) ≤ fun n => ‖f n‖ := fun _ => norm_nonneg _

/-- The slice `a ↦ f a * g (n - a)` is absolutely summable for `ℓ¹ * ℓ¹`. -/
theorem summable_norm_conv_term (hf : IsL1 f) (hg : IsL1 g) (n : ℤ) :
    Summable fun a => ‖f a * g (n - a)‖ := by
  have := summable_convR_slice (a := fun k => ‖f k‖) (b := fun k => ‖g k‖) hf hg
    (norm_nonneg_fun f) (norm_nonneg_fun g) n
  simpa only [norm_mul] using this

theorem summable_conv_term (hf : IsL1 f) (hg : IsL1 g) (n : ℤ) :
    Summable fun a => f a * g (n - a) :=
  (summable_norm_conv_term hf hg n).of_norm

/-- The slice for `ℓ¹ * ℓ²` (absolutely summable). -/
theorem summable_norm_conv_term_l2 (hf : IsL1 f) (hg : Summable fun n => ‖g n‖ ^ 2) (n : ℤ) :
    Summable fun a => ‖f a * g (n - a)‖ := by
  have := (young_convR (a := fun k => ‖f k‖) (b := fun k => ‖g k‖) hf (norm_nonneg_fun f)
    (norm_nonneg_fun g) hg n).1
  simpa only [norm_mul] using this

theorem summable_conv_term_l2 (hf : IsL1 f) (hg : Summable fun n => ‖g n‖ ^ 2) (n : ℤ) :
    Summable fun a => f a * g (n - a) :=
  (summable_norm_conv_term_l2 hf hg n).of_norm

/-- `‖(f*g)_n‖` is majorised by the real convolution of the moduli. -/
theorem norm_conv_le {n : ℤ} (h : Summable fun a => ‖f a * g (n - a)‖) :
    ‖conv f g n‖ ≤ convR (fun k => ‖f k‖) (fun k => ‖g k‖) n := by
  unfold conv convR
  refine (norm_tsum_le_tsum_norm h).trans (le_of_eq ?_)
  simp only [norm_mul]

theorem isL1_conv (hf : IsL1 f) (hg : IsL1 g) :
    IsL1 (conv f g) ∧ l1 (conv f g) ≤ l1 f * l1 g := by
  have hc : Summable (convR (fun k => ‖f k‖) (fun k => ‖g k‖)) :=
    summable_convR hf hg (norm_nonneg_fun f) (norm_nonneg_fun g)
  have hb : ∀ n, ‖conv f g n‖ ≤ convR (fun k => ‖f k‖) (fun k => ‖g k‖) n :=
    fun n => norm_conv_le (summable_norm_conv_term hf hg n)
  have hs : IsL1 (conv f g) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hc
  refine ⟨hs, ?_⟩
  calc l1 (conv f g) ≤ ∑' n, convR (fun k => ‖f k‖) (fun k => ‖g k‖) n :=
        hs.tsum_le_tsum hb hc
    _ = l1 f * l1 g := tsum_convR hf hg (norm_nonneg_fun f) (norm_nonneg_fun g)

theorem conv_comm (f g : ℤ → ℂ) : conv f g = conv g f := by
  funext n
  unfold conv
  rw [← (Equiv.subLeft n).tsum_eq (fun a => g a * f (n - a))]
  refine tsum_congr fun a => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

/-- Young `ℓ¹ * ℓ²`. -/
theorem summable_sq_conv (hf : IsL1 f) (hg : Summable fun n => ‖g n‖ ^ 2) :
    Summable (fun n => ‖conv f g n‖ ^ 2) ∧
      ∑' n, ‖conv f g n‖ ^ 2 ≤ l1 f ^ 2 * ∑' n, ‖g n‖ ^ 2 := by
  obtain ⟨hs, hle⟩ := young_convR_sq (a := fun k => ‖f k‖) (b := fun k => ‖g k‖) hf
    (norm_nonneg_fun f) (norm_nonneg_fun g) hg
  have hb : ∀ n, ‖conv f g n‖ ^ 2 ≤ (convR (fun k => ‖f k‖) (fun k => ‖g k‖) n) ^ 2 := fun n =>
    pow_le_pow_left₀ (norm_nonneg _)
      (norm_conv_le (summable_norm_conv_term_l2 hf hg n)) 2
  have hs' : Summable (fun n => ‖conv f g n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun _ => sq_nonneg _) hb hs
  exact ⟨hs', (hs'.tsum_le_tsum hb hs).trans hle⟩

/-! ### Linearity -/

theorem conv_add_left_of_summable (h : ∀ n, Summable fun a => f a * g (n - a))
    (h' : ∀ n, Summable fun a => f' a * g (n - a)) : conv (f + f') g = conv f g + conv f' g := by
  funext n
  simp only [conv, Pi.add_apply, add_mul]
  exact (h n).tsum_add (h' n)

theorem conv_add_right_of_summable (h : ∀ n, Summable fun a => f a * g (n - a))
    (h' : ∀ n, Summable fun a => f a * g' (n - a)) : conv f (g + g') = conv f g + conv f g' := by
  funext n
  simp only [conv, Pi.add_apply, mul_add]
  exact (h n).tsum_add (h' n)

theorem conv_sub_left_of_summable (h : ∀ n, Summable fun a => f a * g (n - a))
    (h' : ∀ n, Summable fun a => f' a * g (n - a)) : conv (f - f') g = conv f g - conv f' g := by
  funext n
  simp only [conv, Pi.sub_apply, sub_mul]
  exact (h n).tsum_sub (h' n)

theorem conv_sub_right_of_summable (h : ∀ n, Summable fun a => f a * g (n - a))
    (h' : ∀ n, Summable fun a => f a * g' (n - a)) : conv f (g - g') = conv f g - conv f g' := by
  funext n
  simp only [conv, Pi.sub_apply, mul_sub]
  exact (h n).tsum_sub (h' n)

theorem conv_add_left (hf : IsL1 f) (hf' : IsL1 f') (hg : IsL1 g) :
    conv (f + f') g = conv f g + conv f' g :=
  conv_add_left_of_summable (summable_conv_term hf hg) (summable_conv_term hf' hg)

theorem conv_add_right (hf : IsL1 f) (hg : IsL1 g) (hg' : IsL1 g') :
    conv f (g + g') = conv f g + conv f g' :=
  conv_add_right_of_summable (summable_conv_term hf hg) (summable_conv_term hf hg')

theorem conv_sub_left (hf : IsL1 f) (hf' : IsL1 f') (hg : IsL1 g) :
    conv (f - f') g = conv f g - conv f' g :=
  conv_sub_left_of_summable (summable_conv_term hf hg) (summable_conv_term hf' hg)

theorem conv_sub_right (hf : IsL1 f) (hg : IsL1 g) (hg' : IsL1 g') :
    conv f (g - g') = conv f g - conv f g' :=
  conv_sub_right_of_summable (summable_conv_term hf hg) (summable_conv_term hf hg')

/-- Scalars pass through `conv` (no summability needed: `tsum_mul_left`). -/
theorem conv_smul_left (c : ℂ) (f g : ℤ → ℂ) : conv (c • f) g = c • conv f g := by
  funext n
  simp only [conv, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact tsum_mul_left

theorem conv_smul_right (c : ℂ) (f g : ℤ → ℂ) : conv f (c • g) = c • conv f g := by
  funext n
  simp only [conv, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun a => by ring

/-! ### `cstar` and `ℓ¹` closure -/

theorem cstar_cstar (f : ℤ → ℂ) : cstar (cstar f) = f := by
  funext n
  simp [cstar]

theorem l1_cstar (f : ℤ → ℂ) : l1 (cstar f) = l1 f ∧ cstar (cstar f) = f := by
  refine ⟨?_, cstar_cstar f⟩
  unfold l1 cstar
  simp only [Complex.norm_conj]
  exact (Equiv.neg ℤ).tsum_eq (fun n => ‖f n‖)

theorem isL1_cstar_iff (f : ℤ → ℂ) : IsL1 (cstar f) ↔ IsL1 f := by
  unfold IsL1 cstar
  simp only [Complex.norm_conj]
  exact (Equiv.neg ℤ).summable_iff (f := fun n => ‖f n‖)

theorem cstar_add (f g : ℤ → ℂ) : cstar (f + g) = cstar f + cstar g := by
  funext n; simp [cstar]

theorem cstar_sub (f g : ℤ → ℂ) : cstar (f - g) = cstar f - cstar g := by
  funext n; simp [cstar]

theorem cstar_smul (c : ℂ) (f : ℤ → ℂ) : cstar (c • f) = conj c • cstar f := by
  funext n; simp [cstar]

theorem isL1_add (hf : IsL1 f) (hg : IsL1 g) : IsL1 (f + g) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_add_le (f n) (g n))
    (hf.add hg)

theorem isL1_sub (hf : IsL1 f) (hg : IsL1 g) : IsL1 (f - g) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_sub_le (f n) (g n))
    (hf.add hg)

theorem isL1_smul (c : ℂ) (hf : IsL1 f) : IsL1 (c • f) := by
  simpa only [IsL1, Pi.smul_apply, norm_smul] using hf.mul_left ‖c‖

theorem isL1_nonlin (hx : IsL1 x) : IsL1 (nonlin x) ∧ l1 (nonlin x) ≤ 2 * l1 x ^ 3 := by
  obtain ⟨h1, b1⟩ := isL1_conv hx hx
  obtain ⟨h2, b2⟩ := isL1_conv h1 ((isL1_cstar_iff x).2 hx)
  have e : nonlin x = (2 : ℂ) • conv (conv x x) (cstar x) := by
    funext n; simp [nonlin]
  rw [e]
  refine ⟨isL1_smul 2 h2, ?_⟩
  have hl : l1 ((2 : ℂ) • conv (conv x x) (cstar x)) = 2 * l1 (conv (conv x x) (cstar x)) := by
    unfold l1
    simp only [Pi.smul_apply, norm_smul]
    rw [tsum_mul_left]; norm_num
  rw [hl]
  have hx0 : 0 ≤ l1 x := tsum_nonneg fun _ => norm_nonneg _
  have : l1 (conv (conv x x) (cstar x)) ≤ l1 x ^ 3 := by
    calc _ ≤ l1 (conv x x) * l1 (cstar x) := b2
      _ ≤ (l1 x * l1 x) * l1 x := by
        rw [(l1_cstar x).1]
        exact mul_le_mul_of_nonneg_right b1 hx0
      _ = l1 x ^ 3 := by ring
  linarith

end L1Calculus

end NlsGge.NLS38
