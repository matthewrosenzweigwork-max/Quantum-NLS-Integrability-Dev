import NlsGge.Spectral.ActualSpectralRemainderE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # F04.01-.03 literal bounds, uniform on H¹ balls, and bracket-weighted action summability (campaign 38)

Literal versions of the three intermediate inequalities in the proof of v2 `B:lem:spectral`:

* F04.01: `|W_m'(r)| ≤ (2m/|r|) W_m(r)`;
* F04.02: `|W_m(2λ) - a_{m,n}| ≤ C_{m,B} a_{m,n} ⟨n⟩^{-2}` on `\overline{g_n}`, uniformly on `‖w‖_{H¹} ≤ B`;
* F04.03: the `n`-th term of `R_m` is at most `C'_{m,B} ⟨n⟩^{2m-2} I_n`, with `|Φ_n|²` read as the gap action
  `I_n` (user decision D2).

Finally `Σ_n ⟨n⟩^{2k} I_n < ∞` on `H^k`, `k ≥ 1`. Constants depend on `m`, `β`, and `B` only through the
localization constant `K_B` of E03. -/

/-! ## F04.01 -/

theorem finiteWeight_term_logDeriv_le38 (m j : ℕ) (hj : j ≤ m) (b r : ℝ) (hb : 0 ≤ b) :
    |b * (((2*j : ℕ) : ℝ) * r^(2*j - 1))| * |r| ≤ 2 * m * (b * r^(2*j)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hjp
  · simp
    positivity
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have h1 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
    have h2 : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
    rw [h1, abs_mul, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg hb, h2]
    have hr : r ^ ((2 * i + 1) + 1) = |r| ^ (2 * i + 1) * |r| := by
      rw [← pow_succ]; exact (Even.pow_abs (even_two_mul (i+1)) r).symm
    rw [hr]
    have hm : (((2 * i + 1) + 1 : ℕ) : ℝ) ≤ 2 * m := by
      have : (2 * i + 1) + 1 ≤ 2 * m := by omega
      exact_mod_cast this
    have hp : 0 ≤ |r| ^ (2 * i + 1) * |r| := by positivity
    nlinarith [mul_nonneg hb hp, mul_le_mul_of_nonneg_left hm (mul_nonneg hb hp)]

/-- F04.01: `|W_m'(r)| ≤ (2m/|r|) W_m(r)` for `r ≠ 0` (so for `|r| ≥ 1`), `β_j ≥ 0`. -/
theorem finiteWeight_logDeriv_le38 (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (r : ℝ) (hr : r ≠ 0) :
    |deriv (finiteWeightE02_38 m β) r| ≤ (2 * m / |r|) * finiteWeightE02_38 m β r := by
  rw [(hasDerivAt_finiteWeight_E02_38 m β r).deriv]
  have hr0 : 0 < |r| := abs_pos.mpr hr
  rw [div_mul_eq_mul_div, le_div_iff₀ hr0]
  unfold finiteWeightE02_38
  rw [Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hr0.le).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j hj =>
    finiteWeight_term_logDeriv_le38 m j (by simp at hj; omega) _ r (hβ j (by simp at hj; omega))

/-! ## Elementary facts on `⟨n⟩` -/

theorem abs_le_japaneseBracket38 (n : ℤ) : |(n:ℝ)| ≤ japaneseBracket n := by
  unfold japaneseBracket
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (n:ℝ)])

theorem japaneseBracket_le_one_add_abs38 (n : ℤ) : japaneseBracket n ≤ 1 + |(n:ℝ)| := by
  unfold japaneseBracket
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_abs (n:ℝ), abs_nonneg (n:ℝ)]

theorem japaneseBracket_le_two_pi_abs38 (n : ℤ) (hn : n ≠ 0) :
    japaneseBracket n ≤ 2 * Real.pi * |(n:ℝ)| := by
  have hpi := Real.pi_gt_three
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have : (1:ℤ) ≤ |n| := Int.one_le_abs hn
    have h := (Int.cast_le (R := ℝ)).mpr this
    simpa using h
  unfold japaneseBracket
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have e : ((n:ℝ))^2 = |(n:ℝ)|^2 := (sq_abs _).symm
  rw [e]
  have h6 : 6 * |(n:ℝ)| ≤ 2 * Real.pi * |(n:ℝ)| := by nlinarith
  have h36 : (6 * |(n:ℝ)|)^2 ≤ (2 * Real.pi * |(n:ℝ)|)^2 := pow_le_pow_left₀ (by positivity) h6 2
  nlinarith

/-! ## F04.02 -/

/-- Mean value bound for `W_m` on a closed ball: `|W(y) - W(x)| ≤ D |y - x|`. -/
theorem finiteWeight_mvt38 (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (R : ℝ) (_hR : 0 ≤ R)
    (x y : ℝ) (hx : |x| ≤ R) (hy : |y| ≤ R) :
    |finiteWeightE02_38 m β y - finiteWeightE02_38 m β x| ≤
      (∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * R^(2*j - 1))) * |y - x| := by
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (finiteWeightE02_38 m β) t :=
    fun t => (hasDerivAt_finiteWeight_E02_38 m β t).differentiableAt
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := finiteWeightE02_38 m β)
    (C := ∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * R^(2*j - 1)))
    (s := Set.Icc (-R) R) (x := x) (y := y)
    (fun t _ => hdiff t)
    (fun t ht => by
      rw [(hasDerivAt_finiteWeight_E02_38 m β t).deriv, Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
      have hj' : j ≤ m := by simp at hj; omega
      have htR : |t| ≤ R := abs_le.mpr ⟨ht.1, ht.2⟩
      rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast, abs_of_nonneg (hβ j hj')]
      apply mul_le_mul_of_nonneg_left _ (hβ j hj')
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (abs_nonneg t) htR _)
    (convex_Icc _ _) (abs_le.mp hx |> fun h => ⟨h.1, h.2⟩) (abs_le.mp hy |> fun h => ⟨h.1, h.2⟩)
  simpa [Real.norm_eq_abs] using this

theorem finiteWeight_at_zero38 (m : ℕ) (β : ℕ → ℝ) :
    finiteWeightE02_38 m β (2 * Real.pi * ((0:ℤ):ℝ)) = β 0 := by
  unfold finiteWeightE02_38
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    have : 2 * j ≠ 0 := by omega
    simp [this]
  · intro h; simp at h

theorem finiteWeight_nonneg38 (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (r : ℝ) :
    0 ≤ finiteWeightE02_38 m β r := by
  unfold finiteWeightE02_38
  exact Finset.sum_nonneg fun j hj => mul_nonneg (hβ j (by simp at hj; omega))
    ((Even.pow_nonneg (even_two_mul j) r))

/-- The core F04.02 estimate for a single localization constant `K`:
`|l - nπ| ≤ K/⟨n⟩` implies `|W(2l) - W(2πn)| ≤ C W(2πn)/⟨n⟩²`. -/
theorem finiteWeight_gap_core38 (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℤ) (l : ℝ), |l - (n:ℝ) * Real.pi| ≤ K / japaneseBracket n →
      |finiteWeightE02_38 m β (2*l) - finiteWeightE02_38 m β (2*Real.pi*n)| ≤
        C * finiteWeightE02_38 m β (2*Real.pi*n) / japaneseBracket n ^ 2 := by
  have hpi := Real.pi_gt_three
  have hβ0 : ∀ j ≤ m, 0 ≤ β j := fun j hj => (hβ j hj).le
  set lam : ℝ := 1 + K / Real.pi with hlam
  have hlam1 : 1 ≤ lam := by simp only [hlam]; have : 0 ≤ K / Real.pi := by positivity
                             linarith
  set D0 : ℝ := ∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * (2*K)^(2*j - 1)) with hD0
  have hD0nn : 0 ≤ D0 := Finset.sum_nonneg fun j hj => mul_nonneg (hβ0 j (by simp at hj; omega))
    (by positivity)
  have hb0 : 0 < β 0 := hβ 0 (Nat.zero_le _)
  refine ⟨4 * m * K * lam ^ (2*m) + 2 * K * D0 / β 0, by positivity, fun n l hl => ?_⟩
  have hjb := japaneseBracket_pos n
  have hjb1 := japaneseBracket_one_le n
  have hlK : |l - (n:ℝ) * Real.pi| ≤ K := le_trans hl (by
    rw [div_le_iff₀ hjb]; nlinarith)
  set s : ℝ := 2 * Real.pi * |(n:ℝ)| with hs
  have hWn : finiteWeightE02_38 m β (2*Real.pi*n) = finiteWeightE02_38 m β s := by
    unfold finiteWeightE02_38
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have h1 : (2*Real.pi*(n:ℝ))^(2*j) = |2*Real.pi*(n:ℝ)|^(2*j) :=
      (Even.pow_abs (even_two_mul j) _).symm
    rw [h1, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
  have hWnn := finiteWeight_nonneg38 m β hβ0 (2*Real.pi*n)
  have hdist : |2 * l - 2 * Real.pi * n| ≤ 2 * K / japaneseBracket n := by
    have : 2 * l - 2 * Real.pi * n = 2 * (l - n * Real.pi) := by ring
    rw [this, abs_mul, abs_two, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hl (by norm_num)
  by_cases hn : n = 0
  · subst hn
    have hjb0 : japaneseBracket 0 = 1 := by simp [japaneseBracket]
    rw [hjb0] at hdist
    rw [hjb0, finiteWeight_at_zero38] at *
    have hx : |2 * Real.pi * ((0:ℤ):ℝ)| ≤ 2 * K := by simp; positivity
    have hy : |2 * l| ≤ 2 * K := by
      have : |l| ≤ K := by simpa using hlK
      rw [abs_mul, abs_two]; linarith
    have := finiteWeight_mvt38 m β hβ0 (2*K) (by positivity) _ _ hx hy
    rw [← hD0] at this
    have hd2 : |2 * l - 2 * Real.pi * ((0:ℤ):ℝ)| ≤ 2 * K := by simpa using hdist
    have h3 : |finiteWeightE02_38 m β (2*l) - finiteWeightE02_38 m β (2*Real.pi*((0:ℤ):ℝ))| ≤
        D0 * (2 * K) := this.trans (mul_le_mul_of_nonneg_left hd2 hD0nn)
    rw [finiteWeight_at_zero38] at h3
    have h4 : D0 * (2 * K) = (2 * K * D0 / β 0) * β 0 := by field_simp
    have h5 : 0 ≤ 4 * (m:ℝ) * K * lam ^ (2*m) := by positivity
    have h6 : (2 * K * D0 / β 0) * β 0 ≤ (4 * m * K * lam ^ (2*m) + 2 * K * D0 / β 0) * β 0 :=
      mul_le_mul_of_nonneg_right (by linarith) hb0.le
    calc _ ≤ D0 * (2 * K) := h3
      _ = (2 * K * D0 / β 0) * β 0 := h4
      _ ≤ _ := h6
      _ = _ := by simp
  · have hs2 : 2 * Real.pi ≤ s := by
      have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
        have : (1:ℤ) ≤ |n| := Int.one_le_abs hn
        have h := (Int.cast_le (R := ℝ)).mpr this
        simpa using h
      simp only [hs]; nlinarith
    have hjs : japaneseBracket n ≤ s := japaneseBracket_le_two_pi_abs38 n hn
    set R : ℝ := s + 2 * K with hR
    have hRs : R ≤ lam * s := by
      have : K * s / Real.pi ≥ 2 * K := by
        rw [ge_iff_le, le_div_iff₀ Real.pi_pos]; nlinarith
      simp only [hR, hlam]
      have e : (1 + K / Real.pi) * s = s + K * s / Real.pi := by ring
      rw [e]; linarith
    have hx : |2 * Real.pi * (n:ℝ)| ≤ R := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]; simp only [hR]; nlinarith
    have hy : |2 * l| ≤ R := by
      have h1 : |2 * l| ≤ |2 * Real.pi * (n:ℝ)| + |2 * l - 2 * Real.pi * n| := by
        have := abs_add_le (2 * Real.pi * (n:ℝ)) (2 * l - 2 * Real.pi * n)
        simpa using this
      have h2 : |2 * l - 2 * Real.pi * n| ≤ 2 * K := hdist.trans (by
        rw [div_le_iff₀ hjb]; nlinarith)
      have h3 : |2 * Real.pi * (n:ℝ)| = s := by
        rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
      simp only [hR]; linarith
    have hmvt := finiteWeight_mvt38 m β hβ0 R (by positivity) _ _ hx hy
    -- bound the derivative constant
    have hD : (∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * R^(2*j - 1))) * japaneseBracket n ≤
        2 * m * lam ^ (2*m) * finiteWeightE02_38 m β s := by
      unfold finiteWeightE02_38
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j ≤ m := by simp at hj; omega
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · simp; positivity
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have h1 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
        have h2 : 2 * (i + 1) = (2 * i + 1) + 1 := by omega
        rw [h1, h2]
        have hRl : R ^ (2 * i + 1) ≤ lam ^ (2*m) * s ^ (2 * i + 1) := by
          calc R ^ (2*i+1) ≤ (lam * s) ^ (2*i+1) := pow_le_pow_left₀ (by positivity) hRs _
            _ = lam ^ (2*i+1) * s ^ (2*i+1) := mul_pow _ _ _
            _ ≤ lam ^ (2*m) * s ^ (2*i+1) :=
                mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hlam1 (by omega)) (by positivity)
        have hjm : ((2 * (i + 1) : ℕ) : ℝ) ≤ 2 * m := by
          have : 2 * (i + 1) ≤ 2 * m := by omega
          exact_mod_cast this
        have hbj := hβ0 (i+1) hj'
        have hsp : 0 < s := by linarith
        have hspow : s ^ (2 * i + 1) * japaneseBracket n ≤ s ^ (2 * i + 1 + 1) := by
          rw [pow_succ]; exact mul_le_mul_of_nonneg_left hjs (by positivity)
        calc β (i+1) * (((2 * (i + 1) : ℕ) : ℝ) * R ^ (2 * i + 1)) * japaneseBracket n
            ≤ β (i+1) * ((2 * m) * (lam ^ (2*m) * s ^ (2 * i + 1))) * japaneseBracket n := by
              apply mul_le_mul_of_nonneg_right _ hjb.le
              apply mul_le_mul_of_nonneg_left _ hbj
              exact mul_le_mul hjm hRl (by positivity) (by positivity)
          _ = (2 * m * lam ^ (2*m)) * β (i+1) * (s ^ (2 * i + 1) * japaneseBracket n) := by ring
          _ ≤ (2 * m * lam ^ (2*m)) * β (i+1) * s ^ (2 * i + 1 + 1) := by
              apply mul_le_mul_of_nonneg_left hspow
              have : 0 ≤ lam ^ (2*m) := by positivity
              positivity
          _ = _ := by ring
    have hfin : |finiteWeightE02_38 m β (2*l) - finiteWeightE02_38 m β (2*Real.pi*n)| *
        japaneseBracket n ^ 2 ≤ (4 * m * K * lam ^ (2*m)) * finiteWeightE02_38 m β s := by
      have hd : 0 ≤ ∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * R^(2*j - 1)) :=
        Finset.sum_nonneg fun j hj => mul_nonneg (hβ0 j (by simp at hj; omega)) (by positivity)
      have hdist' : |2 * l - 2 * Real.pi * n| * japaneseBracket n ≤ 2 * K := by
        calc _ ≤ (2 * K / japaneseBracket n) * japaneseBracket n :=
              mul_le_mul_of_nonneg_right hdist hjb.le
          _ = 2 * K := by field_simp
      calc |finiteWeightE02_38 m β (2*l) - finiteWeightE02_38 m β (2*Real.pi*n)| * japaneseBracket n ^ 2
          ≤ ((∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * R^(2*j - 1))) *
              |2 * l - 2 * Real.pi * n|) * japaneseBracket n ^ 2 :=
            mul_le_mul_of_nonneg_right hmvt (by positivity)
        _ = ((∑ j ∈ Finset.range (m + 1), β j * (((2*j : ℕ) : ℝ) * R^(2*j - 1))) * japaneseBracket n) *
              (|2 * l - 2 * Real.pi * n| * japaneseBracket n) := by ring
        _ ≤ (2 * m * lam ^ (2*m) * finiteWeightE02_38 m β s) * (2 * K) := by
            apply mul_le_mul hD hdist' (by positivity)
            have : 0 ≤ finiteWeightE02_38 m β s := finiteWeight_nonneg38 m β hβ0 s
            positivity
        _ = _ := by ring
    rw [hWn] at hfin ⊢
    have hnn : 0 ≤ 2 * K * D0 / β 0 * finiteWeightE02_38 m β s :=
      mul_nonneg (by positivity) (finiteWeight_nonneg38 m β hβ0 s)
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hnn]

/-- F04.02: `|W_m(2λ) - a_{m,n}| ≤ C_{m,B} a_{m,n} ⟨n⟩^{-2}` on `\overline{g_n}`, uniformly on H¹ balls. -/
theorem finiteWeight_gap_rel_le38 (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j) (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : WeightedHilbert (sobolevModeWeight (1:ℝ)), ‖w‖ ≤ B → ∀ n : ℤ,
      ∀ l ∈ Set.Icc (actualGapLowerAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n)
        (actualGapUpperAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n),
      |finiteWeightE02_38 m β (2*l) - finiteWeightE02_38 m β (2*Real.pi*n)| ≤
        C * finiteWeightE02_38 m β (2*Real.pi*n) / japaneseBracket n ^ 2 := by
  obtain ⟨K, hK, hloc⟩ := actualGapLocalization_E02_38 B hB
  obtain ⟨C, hC, hCb⟩ := finiteWeight_gap_core38 m β hβ K hK
  exact ⟨C, hC, fun w hw n l hl => hCb n l (hloc w hw n l hl)⟩

/-! ## F04.03 -/

theorem finiteWeight_le_bracket_pow38 (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (n : ℤ) :
    finiteWeightE02_38 m β (2*Real.pi*n) ≤
      (∑ j ∈ Finset.range (m + 1), β j * (2 * Real.pi)^(2*j)) * japaneseBracket n ^ (2*m) := by
  have hjb1 := japaneseBracket_one_le n
  have hnb := abs_le_japaneseBracket38 n
  unfold finiteWeightE02_38
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j ≤ m := by simp at hj; omega
  have hbj := hβ j hj'
  have h1 : (2*Real.pi*(n:ℝ))^(2*j) = (2 * Real.pi * |(n:ℝ)|)^(2*j) := by
    rw [← Even.pow_abs (even_two_mul j) (2*Real.pi*(n:ℝ)), abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos Real.pi_pos]
  rw [h1]
  have h2 : (2 * Real.pi * |(n:ℝ)|)^(2*j) ≤ (2 * Real.pi)^(2*j) * japaneseBracket n ^ (2*m) := by
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc |(n:ℝ)|^(2*j) ≤ japaneseBracket n ^ (2*j) := pow_le_pow_left₀ (abs_nonneg _) hnb _
      _ ≤ japaneseBracket n ^ (2*m) := pow_le_pow_right₀ hjb1 (by omega)
  calc β j * (2 * Real.pi * |(n:ℝ)|)^(2*j) ≤ β j * ((2 * Real.pi)^(2*j) * japaneseBracket n ^ (2*m)) :=
        mul_le_mul_of_nonneg_left h2 hbj
    _ = _ := by ring

theorem actualGapLower_le_upper_F04_38 (u : PhysicalL2) (n : ℤ) :
    actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
  obtain ⟨⟨y, hy⟩, hset⟩ := actualGapLevelSet_eq_Icc_E02_38 u n
  rw [hset] at hy
  exact hy.1.trans hy.2

theorem actualGapAction_nonneg_F04_38 (u : PhysicalL2) (n : ℤ) : 0 ≤ actualGapActionAllE02_38 u n := by
  unfold actualGapActionAllE02_38
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (actualGapLower_le_upper_F04_38 u n)
    fun x _ => actualGapHeightE02_38_nonneg u x)

/-- F04.03: `|n-th term| ≤ C'_{m,B} ⟨n⟩^{2m-2} I_n`. -/
theorem gapRemainderTerm_le_action38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 < β j)
    (B : ℝ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : WeightedHilbert (sobolevModeWeight (1:ℝ)), ‖w‖ ≤ B → ∀ n : ℤ,
      |gapRemainderTermE02_38 (finiteWeightE02_38 m β) (physicalH1ComplexCarrierToL2Actual22 w) n| ≤
        C * japaneseBracket n ^ (2*m-2) *
          actualGapActionAllE02_38 (physicalH1ComplexCarrierToL2Actual22 w) n := by
  have hβ0 : ∀ j ≤ m, 0 ≤ β j := fun j hj => (hβ j hj).le
  obtain ⟨C₂, hC₂, hC₂b⟩ := finiteWeight_gap_rel_le38 m β hβ B hB
  set c₃ : ℝ := ∑ j ∈ Finset.range (m + 1), β j * (2 * Real.pi)^(2*j) with hc₃
  have hc₃nn : 0 ≤ c₃ := Finset.sum_nonneg fun j hj => mul_nonneg (hβ0 j (by simp at hj; omega))
    (by positivity)
  refine ⟨C₂ * c₃, by positivity, fun w hw n => ?_⟩
  set u := physicalH1ComplexCarrierToL2Actual22 w with hu
  have hjb := japaneseBracket_pos n
  have hjb1 := japaneseBracket_one_le n
  set a : ℝ := finiteWeightE02_38 m β (2*Real.pi*n) with ha
  have ha_le : a ≤ c₃ * japaneseBracket n ^ (2*m) := finiteWeight_le_bracket_pow38 m β hβ0 n
  have hann : 0 ≤ a := finiteWeight_nonneg38 m β hβ0 _
  have hpow : japaneseBracket n ^ (2*m) = japaneseBracket n ^ (2*m-2) * japaneseBracket n ^ 2 := by
    rw [← pow_add]; congr 1; omega
  -- the sup bound `C₂ a / ⟨n⟩² ≤ C₂ c₃ ⟨n⟩^{2m-2}`
  have hsup : C₂ * a / japaneseBracket n ^ 2 ≤ C₂ * c₃ * japaneseBracket n ^ (2*m-2) := by
    rw [div_le_iff₀ (by positivity)]
    calc C₂ * a ≤ C₂ * (c₃ * japaneseBracket n ^ (2*m)) := mul_le_mul_of_nonneg_left ha_le hC₂
      _ = _ := by rw [hpow]; ring
  have hab := actualGapLower_le_upper_F04_38 u n
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hII : IntervalIntegrable (actualGapHeightE02_38 u) volume (actualGapLowerAllE02_38 u n)
      (actualGapUpperAllE02_38 u n) := hvc.intervalIntegrable _ _
  have hbd : ‖∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (finiteWeightE02_38 m β (2*x) - a) * actualGapHeightE02_38 u x‖ ≤
      ∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (C₂ * a / japaneseBracket n ^ 2) * actualGapHeightE02_38 u x := by
    refine intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall fun x hx => ?_) (hII.const_mul _)
    have hxI : x ∈ Set.Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
      ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (actualGapHeightE02_38_nonneg u x)]
    exact mul_le_mul_of_nonneg_right (hC₂b w hw n x hxI) (actualGapHeightE02_38_nonneg u x)
  unfold gapRemainderTermE02_38
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / Real.pi)]
  have h1 : (2 / Real.pi) * |∫ x in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (finiteWeightE02_38 m β (2*x) - a) * actualGapHeightE02_38 u x| ≤
      (2 / Real.pi) * ((C₂ * a / japaneseBracket n ^ 2) * ∫ x in (actualGapLowerAllE02_38 u n)..
        (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← intervalIntegral.integral_const_mul]
    simpa [Real.norm_eq_abs] using hbd
  have hIn : actualGapActionAllE02_38 u n = (2 / Real.pi) * ∫ x in (actualGapLowerAllE02_38 u n)..
        (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x := rfl
  have hI0 := actualGapAction_nonneg_F04_38 u n
  calc _ ≤ (2 / Real.pi) * ((C₂ * a / japaneseBracket n ^ 2) * ∫ x in (actualGapLowerAllE02_38 u n)..
        (actualGapUpperAllE02_38 u n), actualGapHeightE02_38 u x) := h1
    _ = (C₂ * a / japaneseBracket n ^ 2) * actualGapActionAllE02_38 u n := by rw [hIn]; ring
    _ ≤ (C₂ * c₃ * japaneseBracket n ^ (2*m-2)) * actualGapActionAllE02_38 u n :=
        mul_le_mul_of_nonneg_right hsup hI0

/-! ## Summability of the bracket-weighted action -/

/-- Bracket bound inside a gap: `⟨n⟩^{2k} ≤ C (1 + (2x)^{2k})` for `x ∈ \overline{g_n}`. -/
theorem bracket_pow_le_on_gap38 (k : ℕ) (K : ℝ) (hK : 0 < K) (n : ℤ) (x : ℝ)
    (hx : |x - (n:ℝ) * Real.pi| ≤ K / japaneseBracket n) :
    japaneseBracket n ^ (2*k) ≤ ((1 + K)^(2*k) * 2^(2*k)) * (1 + (2*x)^(2*k)) := by
  have hpi := Real.pi_gt_three
  have hjb := japaneseBracket_pos n
  have hjb1 := japaneseBracket_one_le n
  have hxK : |x - (n:ℝ) * Real.pi| ≤ K := hx.trans (by
    rw [div_le_iff₀ hjb]; nlinarith)
  have hn : |(n:ℝ)| ≤ |x| + K := by
    have h1 : |(n:ℝ) * Real.pi| ≤ |x| + K := by
      have := abs_sub_abs_le_abs_sub ((n:ℝ) * Real.pi) x
      rw [abs_sub_comm] at this
      linarith
    rw [abs_mul, abs_of_pos Real.pi_pos] at h1
    nlinarith [abs_nonneg (n:ℝ)]
  have hb : japaneseBracket n ≤ (1 + K) * (1 + |2*x|) := by
    have := japaneseBracket_le_one_add_abs38 n
    rw [abs_mul, abs_two]
    nlinarith [abs_nonneg x]
  calc japaneseBracket n ^ (2*k) ≤ ((1 + K) * (1 + |2*x|)) ^ (2*k) :=
        pow_le_pow_left₀ hjb.le hb _
    _ = (1 + K)^(2*k) * (1 + |2*x|)^(2*k) := mul_pow _ _ _
    _ ≤ (1 + K)^(2*k) * (2^(2*k) * (1 + |2*x|^(2*k))) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le_E02_38 _ (abs_nonneg _) _) (by positivity)
    _ = _ := by
        rw [Even.pow_abs (even_two_mul k)]; ring

/-- Summability of the bracket-weighted gap actions on `H^k`, `k ≥ 1` (Lemma A + localization). -/
theorem summable_bracket_action38 (k : ℕ) (hk : 1 ≤ k) (u : PhysicalL2)
    (hu : SobolevSquareSummable (k:ℝ) (physicalFourier u)) :
    Summable (fun n : ℤ => japaneseBracket n ^ (2*k) * actualGapActionAllE02_38 u n) := by
  have hu1 : SobolevSquareSummable 1 (physicalFourier u) :=
    sobolevSquareSummable_restrict 1 k (by exact_mod_cast hk) _ hu
  obtain ⟨K, hK, hloc⟩ := gapLocalization_of_sobolev_E02_38 u hu1
  have hvi : Integrable (actualGapHeightE02_38 u) :=
    (actualGapHeight_integral_eq_normSq_E02_38 u hu1).1
  have hvk : Integrable (fun t => (2*t)^(2*k) * actualGapHeightE02_38 u t) :=
    actualMoment_integrable_of_sobolev38 k hk u hu
  set f : ℝ → ℝ := fun x => (1 + (2*x)^(2*k)) * actualGapHeightE02_38 u x with hf
  have hfi : Integrable f := by
    have := hvi.add hvk
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, hf]; ring
  set s : ℤ → Set ℝ := fun n => actualGapLevelSetE02_38 u n with hsdef
  have hs : ∀ n, s n = Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    fun n => (actualGapLevelSet_eq_Icc_E02_38 u n).2
  have hm : ∀ n, MeasurableSet (s n) := fun n => by rw [hs n]; exact measurableSet_Icc
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hxn hxm => hnm ?_
    have e1 : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := hxn
    have e2 : actualQuasimomentumRealPartE02_38 u x = (m:ℝ) * Real.pi := hxm
    have : (n:ℝ) = m := mul_right_cancel₀ Real.pi_pos.ne' (e1.symm.trans e2)
    exact_mod_cast this
  have hU := hasSum_integral_iUnion hm hd hfi.integrableOn
  have hsum : Summable (fun n : ℤ => ∫ x in s n, f x) := hU.summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by have := japaneseBracket_pos n; positivity)
    (actualGapAction_nonneg_F04_38 u n)) (fun n => ?_)
    (hsum.mul_left (((1 + K)^(2*k) * 2^(2*k)) * (2 / Real.pi)))
  set Cb : ℝ := (1 + K)^(2*k) * 2^(2*k) with hCb
  have hab := actualGapLower_le_upper_F04_38 u n
  have hvc : Continuous (actualGapHeightE02_38 u) := continuous_actualGapHeightE02_38 u
  have hIn : actualGapActionAllE02_38 u n = (2 / Real.pi) * ∫ x in s n, actualGapHeightE02_38 u x := by
    unfold actualGapActionAllE02_38
    congr 1
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc, ← hs n]
  have hvon : IntegrableOn (actualGapHeightE02_38 u) (s n) := hvi.integrableOn
  have hfon : IntegrableOn f (s n) := hfi.integrableOn
  have hle : ∫ x in s n, japaneseBracket n ^ (2*k) * actualGapHeightE02_38 u x ≤
      ∫ x in s n, Cb * f x := by
    refine setIntegral_mono_on (hvon.const_mul _) (hfon.const_mul _) (hm n) (fun x hx => ?_)
    rw [hs n] at hx
    have h1 := bracket_pow_le_on_gap38 k K hK n x (hloc n x hx)
    have h2 := actualGapHeightE02_38_nonneg u x
    calc japaneseBracket n ^ (2*k) * actualGapHeightE02_38 u x
        ≤ (Cb * (1 + (2*x)^(2*k))) * actualGapHeightE02_38 u x := mul_le_mul_of_nonneg_right h1 h2
      _ = Cb * f x := by simp only [hf]; ring
  rw [hIn, ← mul_assoc, mul_comm (japaneseBracket n ^ (2*k)), mul_assoc, ← integral_const_mul]
  calc (2 / Real.pi) * ∫ x in s n, japaneseBracket n ^ (2*k) * actualGapHeightE02_38 u x
      ≤ (2 / Real.pi) * ∫ x in s n, Cb * f x := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = Cb * (2 / Real.pi) * ∫ x in s n, f x := by rw [integral_const_mul]; ring

end NlsGge.SpectralFoundations
end
