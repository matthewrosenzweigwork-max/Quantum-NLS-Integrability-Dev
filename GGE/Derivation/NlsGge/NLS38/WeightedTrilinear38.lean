import NlsGge.NLS38.WeightedTrilinear38b

/-! # GWP piece A1 (entry point): bounds for `nonlin` with admissible weights, `h^m` and truncated

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A1.  Parts a/b: `WeightedTrilinear38a`
(real core), `WeightedTrilinear38b` (complex `wl2_trilinear`, weights, cast bridge).  Here: the
splitting `N(x) - N(y) = 2 [T(d,x,x) + T(y,d,x) + T(y,y,d)]`, the generic `wl2` bounds for
`nonlin`, the corollaries `hn_nonlin_le`, `hn_nonlin_sub_le` in `h^m`, the truncated versions
`hnK_nonlin_le`, `hnK_nonlin_sub_le` (constants independent of `K`), and probes.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate ENNReal

/-! ## The nonlinearity -/

theorem nonlin_eq_smul38 (x : ℤ → ℂ) : nonlin x = (2 : ℂ) • conv (conv x x) (cstar x) := by
  funext n; simp [nonlin]

/-- Generic bound for `nonlin` with an admissible weight. -/
theorem wl2_nonlin_le {C : ℝ} {ω : ℤ → ℝ} (hω : AdmWeight C ω) {x : ℤ → ℂ} (hx : IsL1 x)
    (hx2 : Summable fun n => ω n ^ 2 * ‖x n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖nonlin x n‖ ^ 2) ∧
      wl2 ω (nonlin x) ≤ 6 * C * l1 x ^ 2 * wl2 ω x := by
  obtain ⟨hs, hb⟩ := wl2_trilinear hω hx hx hx hx2 hx2 hx2
  rw [nonlin_eq_smul38]
  refine ⟨summable_wsq_smul38 ω 2 hs, ?_⟩
  rw [wl2_smul38]
  simp only [Complex.norm_ofNat]
  nlinarith [hb]

/-- The algebraic splitting `N(x) - N(y) = 2 [T(d,x,x) + T(y,d,x) + T(y,y,d)]`. -/
theorem conv_tri_sub38 {x y : ℤ → ℂ} (hx : IsL1 x) (hy : IsL1 y) :
    conv (conv x x) (cstar x) - conv (conv y y) (cstar y) =
      conv (conv (x - y) x) (cstar x) + conv (conv y (x - y)) (cstar x) +
        conv (conv y y) (cstar (x - y)) := by
  have hkx : IsL1 (cstar x) := (isL1_cstar_iff x).2 hx
  have hky : IsL1 (cstar y) := (isL1_cstar_iff y).2 hy
  have e1 : conv (conv (x - y) x) (cstar x) =
      conv (conv x x) (cstar x) - conv (conv y x) (cstar x) := by
    rw [conv_sub_left hx hy hx,
      conv_sub_left (isL1_conv hx hx).1 (isL1_conv hy hx).1 hkx]
  have e2 : conv (conv y (x - y)) (cstar x) =
      conv (conv y x) (cstar x) - conv (conv y y) (cstar x) := by
    rw [conv_sub_right hy hx hy,
      conv_sub_left (isL1_conv hy hx).1 (isL1_conv hy hy).1 hkx]
  have e3 : conv (conv y y) (cstar (x - y)) =
      conv (conv y y) (cstar x) - conv (conv y y) (cstar y) := by
    rw [cstar_sub, conv_sub_right (isL1_conv hy hy).1 hkx hky]
  rw [e1, e2, e3]
  abel

/-- Generic difference bound for `nonlin` with an admissible weight. -/
theorem wl2_nonlin_sub_le {C : ℝ} {ω : ℤ → ℝ} (hC : 0 ≤ C) (hω : AdmWeight C ω)
    {x y : ℤ → ℂ} (hx : IsL1 x) (hy : IsL1 y)
    (hx2 : Summable fun n => ω n ^ 2 * ‖x n‖ ^ 2) (hy2 : Summable fun n => ω n ^ 2 * ‖y n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖(nonlin x - nonlin y) n‖ ^ 2) ∧
      wl2 ω (nonlin x - nonlin y) ≤
        2 * C * (wl2 ω (x - y) * (l1 x + l1 y) ^ 2 +
          2 * l1 (x - y) * (l1 x + l1 y) * (wl2 ω x + wl2 ω y)) := by
  have hd : IsL1 (x - y) := isL1_sub hx hy
  have hd2 := summable_wsq_sub38 hω.1 hx2 hy2
  obtain ⟨s1, b1⟩ := wl2_trilinear hω hd hx hx hd2 hx2 hx2
  obtain ⟨s2, b2⟩ := wl2_trilinear hω hy hd hx hy2 hd2 hx2
  obtain ⟨s3, b3⟩ := wl2_trilinear hω hy hy hd hy2 hy2 hd2
  have hsplit : nonlin x - nonlin y = (2 : ℂ) • (conv (conv (x - y) x) (cstar x) +
      conv (conv y (x - y)) (cstar x) + conv (conv y y) (cstar (x - y))) := by
    rw [← conv_tri_sub38 hx hy, nonlin_eq_smul38, nonlin_eq_smul38, smul_sub]
  have hdom := wl2_of_le_add3_38 hω.1 (F := conv (conv (x - y) x) (cstar x) +
      conv (conv y (x - y)) (cstar x) + conv (conv y y) (cstar (x - y)))
    (f1 := conv (conv (x - y) x) (cstar x)) (f2 := conv (conv y (x - y)) (cstar x))
    (f3 := conv (conv y y) (cstar (x - y))) (fun n => by
      simpa using norm_add₃_le) s1 s2 s3
  obtain ⟨hdS, hdB⟩ := hdom
  rw [hsplit]
  refine ⟨summable_wsq_smul38 ω 2 hdS, ?_⟩
  rw [wl2_smul38]
  simp only [Complex.norm_ofNat]
  have hlx := l1_nonneg38 x
  have hly := l1_nonneg38 y
  have hle := l1_nonneg38 (x - y)
  have hwx := wl2_nonneg38 ω x
  have hwy := wl2_nonneg38 ω y
  have hwd := wl2_nonneg38 ω (x - y)
  have hsum : wl2 ω (conv (conv (x - y) x) (cstar x)) + wl2 ω (conv (conv y (x - y)) (cstar x)) +
      wl2 ω (conv (conv y y) (cstar (x - y))) ≤
      C * (wl2 ω (x - y) * (l1 x + l1 y) ^ 2 +
          2 * l1 (x - y) * (l1 x + l1 y) * (wl2 ω x + wl2 ω y)) := by
    have h0 := mul_nonneg hwd (mul_nonneg hlx hly)
    have h1 := mul_nonneg hle (mul_nonneg hlx hwy)
    have h2 := mul_nonneg hle (mul_nonneg hly hwx)
    nlinarith [b1, b2, b3, h0, h1, h2, mul_le_mul_of_nonneg_left (show 0 ≤ wl2 ω (x - y) *
      (l1 x * l1 y) from mul_nonneg hwd (mul_nonneg hlx hly)) hC]
  nlinarith [hdB, hsum]

/-! ## `h^1` data: constants in terms of `hn 1` -/

theorem sub_mem_h1_38 {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ)) : x - y ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
  (mem_seqSobolev_nat_iff_wsq38 1 (x - y)).2
    (summable_wsq_sub38 (ω := fun n => japaneseBracket n ^ 1) (fun n => pow_nonneg (japaneseBracket_pos n).le 1)
      ((mem_seqSobolev_nat_iff_wsq38 1 x).1 hx) ((mem_seqSobolev_nat_iff_wsq38 1 y).1 hy))

theorem hn_nonneg38 (m : ℕ) (x : ℤ → ℂ) : 0 ≤ hn m x := Real.sqrt_nonneg _

/-- `nonlin` bound for an admissible weight and `h^1` data. -/
theorem wl2_nonlin_le_h1 {C : ℝ} {ω : ℤ → ℝ} (hC : 0 ≤ C) (hω : AdmWeight C ω) {x : ℤ → ℂ}
    (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (hx2 : Summable fun n => ω n ^ 2 * ‖x n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖nonlin x n‖ ^ 2) ∧
      wl2 ω (nonlin x) ≤ (6 * C * C1 ^ 2 + 1) * hn 1 x ^ 2 * wl2 ω x := by
  obtain ⟨hL, hLb⟩ := isL1_of_hn_one x hx
  obtain ⟨hs, hb⟩ := wl2_nonlin_le hω hL hx2
  refine ⟨hs, hb.trans ?_⟩
  have hw := wl2_nonneg38 ω x
  have hl0 := l1_nonneg38 x
  have hh1 := hn_nonneg38 1 x
  have hsq : l1 x ^ 2 ≤ C1 ^ 2 * hn 1 x ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ hl0 hLb 2
  have step : 6 * C * l1 x ^ 2 * wl2 ω x ≤ 6 * C * (C1 ^ 2 * hn 1 x ^ 2) * wl2 ω x :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) hw
  have hq : 0 ≤ hn 1 x ^ 2 * wl2 ω x := by positivity
  nlinarith [step, hq]

/-- Difference bound for an admissible weight and `h^1` data. -/
theorem wl2_nonlin_sub_le_h1 {C : ℝ} {ω : ℤ → ℝ} (hC : 0 ≤ C) (hω : AdmWeight C ω)
    {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hx2 : Summable fun n => ω n ^ 2 * ‖x n‖ ^ 2) (hy2 : Summable fun n => ω n ^ 2 * ‖y n‖ ^ 2) :
    Summable (fun n => ω n ^ 2 * ‖(nonlin x - nonlin y) n‖ ^ 2) ∧
      wl2 ω (nonlin x - nonlin y) ≤ (4 * C * C1 ^ 2 + 1) *
        ((hn 1 x + hn 1 y) ^ 2 * wl2 ω (x - y) +
          (hn 1 x + hn 1 y) * (wl2 ω x + wl2 ω y) * hn 1 (x - y)) := by
  obtain ⟨hLx, hLxb⟩ := isL1_of_hn_one x hx
  obtain ⟨hLy, hLyb⟩ := isL1_of_hn_one y hy
  obtain ⟨hLd, hLdb⟩ := isL1_of_hn_one (x - y) (sub_mem_h1_38 hx hy)
  obtain ⟨hs, hb⟩ := wl2_nonlin_sub_le hC hω hLx hLy hx2 hy2
  refine ⟨hs, hb.trans ?_⟩
  have hlx := l1_nonneg38 x
  have hly := l1_nonneg38 y
  have hn1x := hn_nonneg38 1 x
  have hn1y := hn_nonneg38 1 y
  have hn1d := hn_nonneg38 1 (x - y)
  have hwx := wl2_nonneg38 ω x
  have hwy := wl2_nonneg38 ω y
  have hwd := wl2_nonneg38 ω (x - y)
  set H := hn 1 x + hn 1 y with hH
  set σ := wl2 ω x + wl2 ω y with hσ
  set δ := wl2 ω (x - y) with hδ
  set hd := hn 1 (x - y) with hhd
  have hs1 : l1 x + l1 y ≤ C1 * H := by rw [hH]; nlinarith
  have hs0 : 0 ≤ l1 x + l1 y := by positivity
  have hH0 : 0 ≤ H := by positivity
  have hC1 : 0 ≤ C1 := by unfold C1; exact norm_nonneg _
  have hσ0 : 0 ≤ σ := by positivity
  have h_ss : (l1 x + l1 y) ^ 2 ≤ (C1 * H) ^ 2 := pow_le_pow_left₀ hs0 hs1 2
  have h_es : l1 (x - y) * (l1 x + l1 y) ≤ (C1 * hd) * (C1 * H) :=
    mul_le_mul hLdb hs1 hs0 (by positivity)
  have i1 : δ * (l1 x + l1 y) ^ 2 ≤ δ * (C1 * H) ^ 2 := mul_le_mul_of_nonneg_left h_ss hwd
  have i2 : (l1 (x - y) * (l1 x + l1 y)) * σ ≤ ((C1 * hd) * (C1 * H)) * σ :=
    mul_le_mul_of_nonneg_right h_es hσ0
  have i3 : δ * (l1 x + l1 y) ^ 2 + 2 * l1 (x - y) * (l1 x + l1 y) * σ ≤
      δ * (C1 * H) ^ 2 + 2 * (((C1 * hd) * (C1 * H)) * σ) := by nlinarith [i1, i2]
  have i4 := mul_le_mul_of_nonneg_left i3 (show 0 ≤ 2 * C by positivity)
  have ha : 0 ≤ C * C1 ^ 2 * (δ * H ^ 2) := by positivity
  have hb' : 0 ≤ δ * H ^ 2 := by positivity
  have hc : 0 ≤ hd * H * σ := by positivity
  nlinarith [i4, ha, hb', hc]

/-! ## Corollaries in `h^m` -/

theorem hn_nonlin_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C > 0, ∀ x ∈ seqSobolev38 (m : ℝ),
      nonlin x ∈ seqSobolev38 (m : ℝ) ∧ hn m (nonlin x) ≤ C * hn 1 x ^ 2 * hn m x := by
  refine ⟨6 * 3 ^ (m - 1) * C1 ^ 2 + 1, by positivity, fun x hx => ?_⟩
  have hω := admWeight_pow m hm
  obtain ⟨hs, hb⟩ := wl2_nonlin_le_h1 (by positivity) hω (mem_h1_of_mem_nat m hm hx)
    ((mem_seqSobolev_nat_iff_wsq38 m x).1 hx)
  refine ⟨(mem_seqSobolev_nat_iff_wsq38 m _).2 hs, ?_⟩
  simpa only [← hn_eq_wl2_38] using hb

theorem hn_nonlin_sub_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C > 0, ∀ x ∈ seqSobolev38 (m : ℝ), ∀ y ∈ seqSobolev38 (m : ℝ),
      hn m (fun n => nonlin x n - nonlin y n) ≤
        C * ((hn 1 x + hn 1 y) ^ 2 * hn m (fun n => x n - y n) +
          (hn 1 x + hn 1 y) * (hn m x + hn m y) * hn 1 (fun n => x n - y n)) := by
  refine ⟨4 * 3 ^ (m - 1) * C1 ^ 2 + 1, by positivity, fun x hx y hy => ?_⟩
  have hω := admWeight_pow m hm
  obtain ⟨-, hb⟩ := wl2_nonlin_sub_le_h1 (by positivity) hω (mem_h1_of_mem_nat m hm hx)
    (mem_h1_of_mem_nat m hm hy) ((mem_seqSobolev_nat_iff_wsq38 m x).1 hx)
    ((mem_seqSobolev_nat_iff_wsq38 m y).1 hy)
  simp only [← hn_eq_wl2_38] at hb
  exact hb

/-! ## Corollaries with the truncated weights (constants independent of `K`) -/

theorem hnK_nonlin_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C > 0, ∀ (K : ℕ) (x : ℤ → ℂ), x ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      Summable (fun n => wK m K n ^ 2 * ‖nonlin x n‖ ^ 2) ∧
        wl2 (wK m K) (nonlin x) ≤ C * hn 1 x ^ 2 * wl2 (wK m K) x := by
  refine ⟨6 * 3 ^ (m - 1) * C1 ^ 2 + 1, by positivity, fun K x hx => ?_⟩
  exact wl2_nonlin_le_h1 (by positivity) (admWeight_wK m K hm) hx (summable_wK_of_h1 m K hx)

theorem hnK_nonlin_sub_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C > 0, ∀ (K : ℕ) (x y : ℤ → ℂ), x ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      y ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      Summable (fun n => wK m K n ^ 2 * ‖(fun n => nonlin x n - nonlin y n) n‖ ^ 2) ∧
      wl2 (wK m K) (fun n => nonlin x n - nonlin y n) ≤
        C * ((hn 1 x + hn 1 y) ^ 2 * wl2 (wK m K) (fun n => x n - y n) +
          (hn 1 x + hn 1 y) * (wl2 (wK m K) x + wl2 (wK m K) y) *
            hn 1 (fun n => x n - y n)) := by
  refine ⟨4 * 3 ^ (m - 1) * C1 ^ 2 + 1, by positivity, fun K x y hx hy => ?_⟩
  exact wl2_nonlin_sub_le_h1 (by positivity) (admWeight_wK m K hm) hx hy
    (summable_wK_of_h1 m K hx) (summable_wK_of_h1 m K hy)

/-! ## Regression probes -/

section Probes

theorem wl2_single38 (ω : ℤ → ℝ) (hω : ∀ n, 0 ≤ ω n) (k : ℤ) (a : ℂ) :
    wl2 ω (Pi.single k a) = ω k * ‖a‖ := by
  unfold wl2
  rw [tsum_eq_single k (fun n hn => by simp [hn])]
  simp only [Pi.single_eq_same]
  rw [← mul_pow, Real.sqrt_sq (mul_nonneg (hω k) (norm_nonneg _))]

/-- Plane wave: `wl2 ω (nonlin δ_k a) = 2 ω_k ‖a‖³`, consistent with `wl2_nonlin_le`. -/
theorem wl2_nonlin_single (ω : ℤ → ℝ) (hω : ∀ n, 0 ≤ ω n) (k : ℤ) (a : ℂ) :
    wl2 ω (nonlin (Pi.single k a)) = 2 * (ω k * ‖a‖ ^ 3) := by
  rw [nonlin_single, wl2_single38 ω hω]
  have : ‖2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * a‖ = 2 * ‖a‖ ^ 3 := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, norm_pow, norm_norm]
    ring
  rw [this]; ring

/-- The `m`-th plane-wave instance of the bound of `hn_nonlin_le`. -/
theorem planeWave_instance (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (a : ℂ) :
    ∃ C > 0, hn m (nonlin (Pi.single k a)) ≤ C * hn 1 (Pi.single k a) ^ 2 * hn m (Pi.single k a) := by
  have hmem : ∀ r : ℕ, (Pi.single k a : ℤ → ℂ) ∈ seqSobolev38 (r : ℝ) := by
    intro r
    rw [mem_seqSobolev_nat_iff38]
    refine summable_of_ne_finset_zero (s := {k}) (fun n hn => ?_)
    simp at hn
    simp [hn]
  obtain ⟨C, hC, h⟩ := hn_nonlin_le m hm
  exact ⟨C, hC, (h _ (hmem m)).2⟩

/-- Exact value: `AdmWeight` at `m = 1` is the triangle inequality `⟨a+b-c⟩ ≤ ⟨a⟩+⟨b⟩+⟨c⟩`
with constant `3^0 = 1`. -/
theorem admWeight_pow_one : AdmWeight 1 (fun n => japaneseBracket n ^ 1) := by
  simpa using admWeight_pow 1 le_rfl

end Probes

end NlsGge.NLS38
