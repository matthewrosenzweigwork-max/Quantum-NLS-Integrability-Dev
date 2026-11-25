import NlsGge.NLS38.Persistence38

/-! # GWP piece A6b (part a): helpers for `h^m` Lipschitz dependence

Plan: `campaign/GWP_PLAN.md` §7, piece A6b (review note N2).

* `abs_hn_one_sub_le38`: `|‖x‖_{h¹} - ‖y‖_{h¹}| ≤ ‖x - y‖_{h¹}`.
* `wl2_cutfield_sub38`: the truncated norm of `χ_R(‖x‖) N(x) - χ_R(‖y‖) N(y)`, via the splitting
  `χ_x (N x - N y) + (χ_x - χ_y) N y` (note N2), with constants independent of `K`, `R ≥ 0`-scaled.
* `gronwall_two_sided_vec38`: the two-sided inhomogeneous Gronwall estimate for a vector-valued
  `C¹` function, from `norm_le_gronwallBound_of_norm_deriv_right_le` on `[0, T]` and its reflection.
* `norm_TK_Gc_sub38`: `‖TK (Gc v - Gc w)‖` is the truncated norm of the difference of cutoff fields.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set
open scoped ComplexConjugate NNReal InnerProductSpace

/-! ## `h¹` norms of differences -/

theorem sub_mem_nat38 (m : ℕ) {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ))
    (hy : y ∈ seqSobolev38 (m : ℝ)) : (fun n => x n - y n) ∈ seqSobolev38 (m : ℝ) :=
  carrierCoe38_mem _ (carrierMk38 (m : ℝ) x hx - carrierMk38 (m : ℝ) y hy)

theorem carrierMk_sub38 (m : ℕ) {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ))
    (hy : y ∈ seqSobolev38 (m : ℝ)) :
    carrierMk38 (m : ℝ) (fun n => x n - y n) (sub_mem_nat38 m hx hy) =
      carrierMk38 (m : ℝ) x hx - carrierMk38 (m : ℝ) y hy := rfl

theorem abs_hn_one_sub_le38 {x y : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ))
    (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ)) : |hn 1 x - hn 1 y| ≤ hn 1 (fun n => x n - y n) := by
  have h := abs_norm_sub_norm_le (carrierMk38 ((1 : ℕ) : ℝ) x hx) (carrierMk38 ((1 : ℕ) : ℝ) y hy)
  rw [← carrierMk_sub38 1 hx hy, norm_carrierMk38_eq_hn, norm_carrierMk38_eq_hn,
    norm_carrierMk38_eq_hn] at h
  exact h

/-! ## The difference of two cutoff fields in a truncated norm -/

/-- One-sided version: assumes `‖y‖_{h¹} < 2R`. -/
theorem wl2_cutfield_sub_aux38 (m : ℕ) (hm : 1 ≤ m) : ∃ M : ℝ, 0 < M ∧ ∀ (R : ℝ), 0 < R →
    ∀ (K : ℕ) (x y : ℤ → ℂ), x ∈ seqSobolev38 ((1 : ℕ) : ℝ) → y ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      hn 1 y < 2 * R →
      wl2 (wK m K) (fun n => ((cutoff R (hn 1 x) : ℝ) : ℂ) * nonlin x n -
          ((cutoff R (hn 1 y) : ℝ) : ℂ) * nonlin y n) ≤
        M * (R ^ 2 * wl2 (wK m K) (fun n => x n - y n) +
          R * (wl2 (wK m K) x + wl2 (wK m K) y) * hn 1 (fun n => x n - y n)) := by
  obtain ⟨C0, hC0, hC⟩ := hnK_nonlin_le m hm
  obtain ⟨C1', hC1, hC'⟩ := hnK_nonlin_sub_le m hm
  refine ⟨20 * C1' + 4 * C0, by positivity, fun R hR K x y hx hy hyR => ?_⟩
  have hxy : (fun n => x n - y n) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := sub_mem_nat38 1 hx hy
  obtain ⟨hsd, hbd⟩ := hC' K x y hx hy
  obtain ⟨hsy, hby⟩ := hC K y hy
  set χx := cutoff R (hn 1 x) with hχx
  set χy := cutoff R (hn 1 y) with hχy
  set δ := wl2 (wK m K) (fun n => x n - y n) with hδ
  set h1d := hn 1 (fun n => x n - y n) with hh1d
  set wx := wl2 (wK m K) x
  set wy := wl2 (wK m K) y
  have hδ0 : 0 ≤ δ := wl2_nonneg38 _ _
  have hwx0 : 0 ≤ wx := wl2_nonneg38 _ _
  have hwy0 : 0 ≤ wy := wl2_nonneg38 _ _
  have hh0 : 0 ≤ h1d := hn_nonneg38 _ _
  have hx0 := hn_nonneg38 1 x
  have hy0 := hn_nonneg38 1 y
  have hχx0 : 0 ≤ χx := cutoff_nonneg R (hn 1 x)
  have hχx1 : χx ≤ 1 := cutoff_le_one R (hn 1 x)
  have hRpos := hR.le
  -- the splitting
  have hsplit : ∀ n, ((χx : ℝ) : ℂ) * nonlin x n - ((χy : ℝ) : ℂ) * nonlin y n =
      (((χx : ℝ) : ℂ) • (fun n => nonlin x n - nonlin y n)) n +
        ((((χx - χy : ℝ)) : ℂ) • nonlin y) n := by
    intro n
    simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub]
    ring
  have hs1 : Summable fun n => wK m K n ^ 2 * ‖(((χx : ℝ) : ℂ) • (fun n => nonlin x n - nonlin y n)) n‖ ^ 2 :=
    summable_wsq_smul38 _ _ hsd
  have hs2 : Summable fun n => wK m K n ^ 2 * ‖((((χx - χy : ℝ)) : ℂ) • nonlin y) n‖ ^ 2 :=
    summable_wsq_smul38 _ _ hsy
  obtain ⟨-, hF⟩ := wl2_of_le_add2_38 (fun n => wK_nonneg m K n) (F := fun n => ((χx : ℝ) : ℂ) * nonlin x n -
      ((χy : ℝ) : ℂ) * nonlin y n) (fun n => by rw [hsplit n]; exact norm_add_le _ _) hs1 hs2
  refine hF.trans ?_
  rw [wl2_smul38, wl2_smul38, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hχx0,
    Real.norm_eq_abs]
  -- bound the two terms
  have hT1 : χx * wl2 (wK m K) (fun n => nonlin x n - nonlin y n) ≤
      C1' * (16 * R ^ 2 * δ + 4 * R * (wx + wy) * h1d) := by
    by_cases hc : 2 * R ≤ hn 1 x
    · have : χx = 0 := cutoff_eq_zero hR hc
      rw [this, zero_mul]; positivity
    · rw [not_le] at hc
      have ha : hn 1 x + hn 1 y ≤ 4 * R := by linarith
      have ha0 : 0 ≤ hn 1 x + hn 1 y := by positivity
      have h2 : (hn 1 x + hn 1 y) ^ 2 ≤ 16 * R ^ 2 := by nlinarith
      calc χx * wl2 (wK m K) (fun n => nonlin x n - nonlin y n)
          ≤ 1 * wl2 (wK m K) (fun n => nonlin x n - nonlin y n) :=
            mul_le_mul_of_nonneg_right hχx1 (wl2_nonneg38 _ _)
        _ ≤ C1' * ((hn 1 x + hn 1 y) ^ 2 * δ + (hn 1 x + hn 1 y) * (wx + wy) * h1d) := by
            rw [one_mul]; exact hbd
        _ ≤ C1' * (16 * R ^ 2 * δ + 4 * R * (wx + wy) * h1d) := by
            refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC1.le
            · exact mul_le_mul_of_nonneg_right (by linarith) hδ0
            · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (by positivity)) hh0
  have hT2 : |χx - χy| * wl2 (wK m K) (nonlin y) ≤ 4 * C0 * (R * (wx + wy) * h1d) := by
    have hl := cutoff_lip hR (hn 1 x) (hn 1 y)
    have hl2 : |χx - χy| ≤ R⁻¹ * h1d := hl.trans (mul_le_mul_of_nonneg_left
      ((abs_hn_one_sub_le38 hx hy)) (inv_nonneg.2 hRpos))
    have hy2 : hn 1 y ^ 2 ≤ 4 * R ^ 2 := by nlinarith
    calc |χx - χy| * wl2 (wK m K) (nonlin y)
        ≤ (R⁻¹ * h1d) * (C0 * hn 1 y ^ 2 * wy) :=
          mul_le_mul hl2 hby (wl2_nonneg38 _ _) (by positivity)
      _ ≤ (R⁻¹ * h1d) * (C0 * (4 * R ^ 2) * wy) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hy2 hC0.le) hwy0
      _ = 4 * C0 * (R * wy * h1d) := by field_simp
      _ ≤ 4 * C0 * (R * (wx + wy) * h1d) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hRpos) hh0
  have hq : 0 ≤ R * (wx + wy) * h1d := by positivity
  have hq2 : 0 ≤ R ^ 2 * δ := by positivity
  nlinarith [hT1, hT2, hq, hq2, hC1, hC0]

/-- The truncated norm of the difference of two cutoff fields. -/
theorem wl2_cutfield_sub38 (m : ℕ) (hm : 1 ≤ m) : ∃ M : ℝ, 0 < M ∧ ∀ (R : ℝ), 0 < R →
    ∀ (K : ℕ) (x y : ℤ → ℂ), x ∈ seqSobolev38 ((1 : ℕ) : ℝ) → y ∈ seqSobolev38 ((1 : ℕ) : ℝ) →
      wl2 (wK m K) (fun n => ((cutoff R (hn 1 x) : ℝ) : ℂ) * nonlin x n -
          ((cutoff R (hn 1 y) : ℝ) : ℂ) * nonlin y n) ≤
        M * (R ^ 2 * wl2 (wK m K) (fun n => x n - y n) +
          R * (wl2 (wK m K) x + wl2 (wK m K) y) * hn 1 (fun n => x n - y n)) := by
  obtain ⟨M, hM, h⟩ := wl2_cutfield_sub_aux38 m hm
  refine ⟨M, hM, fun R hR K x y hx hy => ?_⟩
  by_cases hyR : hn 1 y < 2 * R
  · exact h R hR K x y hx hy hyR
  · rw [not_lt] at hyR
    by_cases hxR : hn 1 x < 2 * R
    · -- swap the roles
      have := h R hR K y x hy hx hxR
      have e1 : (fun n => ((cutoff R (hn 1 x) : ℝ) : ℂ) * nonlin x n -
          ((cutoff R (hn 1 y) : ℝ) : ℂ) * nonlin y n) =
          (-1 : ℂ) • (fun n => ((cutoff R (hn 1 y) : ℝ) : ℂ) * nonlin y n -
          ((cutoff R (hn 1 x) : ℝ) : ℂ) * nonlin x n) := by
        funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring
      have e2 : (fun n => y n - x n) = (-1 : ℂ) • (fun n => x n - y n) := by
        funext n; simp only [Pi.smul_apply, smul_eq_mul]; ring
      have e3 : hn 1 (fun n => y n - x n) = hn 1 (fun n => x n - y n) := by
        have : hn 1 (fun n => y n - x n) = hn 1 ((-1 : ℂ) • (fun n => x n - y n)) := by rw [← e2]
        rw [this, hn_eq_wl2_38, hn_eq_wl2_38, wl2_smul38]; simp
      rw [e1, wl2_smul38]
      rw [e3, e2, wl2_smul38] at this
      simp only [norm_neg, norm_one, one_mul] at this ⊢
      linarith
    · rw [not_lt] at hxR
      have h1 : cutoff R (hn 1 x) = 0 := cutoff_eq_zero hR hxR
      have h2 : cutoff R (hn 1 y) = 0 := cutoff_eq_zero hR hyR
      simp only [h1, h2, Complex.ofReal_zero, zero_mul, sub_zero]
      have : wl2 (wK m K) (fun _ : ℤ => (0 : ℂ)) = 0 := by simp [wl2]
      rw [this]
      have := wl2_nonneg38 (wK m K) x
      have := wl2_nonneg38 (wK m K) y
      have := wl2_nonneg38 (wK m K) (fun n => x n - y n)
      have := hn_nonneg38 1 (fun n => x n - y n)
      positivity

/-! ## Two-sided inhomogeneous Gronwall for vector-valued functions -/

theorem gronwallBound_le38 {δ K ε x : ℝ} (hK : 0 < K) (hε : 0 ≤ ε) (_hx : 0 ≤ x) :
    gronwallBound δ K ε x ≤ δ * Real.exp (K * x) + ε * x * Real.exp (K * x) := by
  rw [gronwallBound_of_K_ne_0 hK.ne']
  show δ * Real.exp (K * x) + ε / K * (Real.exp (K * x) - 1) ≤ _
  have h1 : Real.exp (K * x) - 1 ≤ K * x * Real.exp (K * x) := by
    have := Real.add_one_le_exp (-(K * x))
    rw [Real.exp_neg] at this
    have hpos := Real.exp_pos (K * x)
    have h2 : 1 - K * x ≤ (Real.exp (K * x))⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at h3
    nlinarith
  have h4 : ε / K * (Real.exp (K * x) - 1) ≤ ε / K * (K * x * Real.exp (K * x)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h5 : ε / K * (K * x * Real.exp (K * x)) = ε * x * Real.exp (K * x) := by field_simp
  linarith

/-- One direction of time: `‖F b‖` for `b ≥ 0`. -/
theorem gronwall_nonneg_vec38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F F' : ℝ → E}
    {K ε δ b : ℝ} (hF : ∀ s, HasDerivAt F (F' s) s) (hK : 0 < K) (hε : 0 ≤ ε) (hb : 0 ≤ b)
    (hbd : ∀ s, 0 ≤ s → s ≤ b → ‖F' s‖ ≤ K * ‖F s‖ + ε) (h0 : ‖F 0‖ ≤ δ) :
    ‖F b‖ ≤ δ * Real.exp (K * b) + ε * b * Real.exp (K * b) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le (f := F) (f' := F') (a := 0) (b := b)
    (fun s _ => (hF s).continuousAt.continuousWithinAt) (fun s _ => (hF s).hasDerivWithinAt) h0
    (fun s hs => hbd s hs.1 hs.2.le) b ⟨hb, le_rfl⟩
  rw [sub_zero] at h
  exact h.trans (gronwallBound_le38 hK hε hb)

/-- Two-sided Gronwall with a constant inhomogeneity on `|s| ≤ T`. -/
theorem gronwall_two_sided_vec38 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F F' : ℝ → E}
    {K ε δ T : ℝ} (hF : ∀ s, HasDerivAt F (F' s) s) (hK : 0 < K) (hε : 0 ≤ ε)
    (hbd : ∀ s, |s| ≤ T → ‖F' s‖ ≤ K * ‖F s‖ + ε) (h0 : ‖F 0‖ ≤ δ) (t : ℝ) (ht : |t| ≤ T) :
    ‖F t‖ ≤ δ * Real.exp (K * |t|) + ε * |t| * Real.exp (K * |t|) := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact gronwall_nonneg_vec38 hF hK hε h (fun s hs0 hsb => hbd s (by
      rw [abs_of_nonneg hs0]; rw [abs_of_nonneg h] at ht; linarith)) h0
  · rw [abs_of_nonpos h]
    have hG : ∀ s, HasDerivAt (fun r => F (-r)) (-F' (-s)) s := fun s => by
      have := (hF (-s)).scomp s (hasDerivAt_neg s)
      exact this.congr_deriv (by simp)
    have := gronwall_nonneg_vec38 (F := fun r => F (-r)) (F' := fun s => -F' (-s)) (K := K) (ε := ε)
      (δ := δ) (b := -t) hG hK hε (by linarith)
      (fun s hs0 hsb => by
        have := hbd (-s) (by rw [abs_neg, abs_of_nonneg hs0]; rw [abs_of_nonpos h] at ht; linarith)
        simpa using this) (by simpa using h0)
    simpa using this

/-! ## The interaction-picture difference in coordinates -/

theorem phase_sub38 (t : ℝ) (x y : ℤ → ℂ) :
    phase t (fun n => x n - y n) = fun n => phase t x n - phase t y n := by
  funext n; simp only [phase]; ring

theorem norm_TK_sub_vs38 (m K : ℕ) {u w : ℤ → ℂ} {vu vw : H1C38} (s : ℝ)
    (hu : carrierCoe38 ((1 : ℕ) : ℝ) vu = phase (-s) u) (hw : carrierCoe38 ((1 : ℕ) : ℝ) vw = phase (-s) w) :
    ‖TK38 m K (vu - vw)‖ = wl2 (wK m K) (fun n => u n - w n) := by
  rw [norm_TK38, carrierCoe38_sub', hu, hw, ← phase_sub38, wl2_phase38]

theorem norm_TK_Gc_sub38 (m K : ℕ) (R s : ℝ) (v w : H1C38) :
    ‖TK38 m K (Gc 1 le_rfl R s v - Gc 1 le_rfl R s w)‖ =
      wl2 (wK m K) (fun n => ((cutoff R (hn 1 (phase s (carrierCoe38 ((1 : ℕ) : ℝ) v))) : ℝ) : ℂ) *
          nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) v)) n -
        ((cutoff R (hn 1 (phase s (carrierCoe38 ((1 : ℕ) : ℝ) w))) : ℝ) : ℂ) *
          nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) w)) n) := by
  rw [norm_TK38, carrierCoe38_sub', coe_Gc1_38, coe_Gc1_38, hn_phase38, hn_phase38]
  have e : (fun n => (phase (-s) ((-(Complex.I * ((cutoff R (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) v)) : ℝ) : ℂ))) •
        nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) v)))) n -
      (phase (-s) ((-(Complex.I * ((cutoff R (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) w)) : ℝ) : ℂ))) •
        nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) w)))) n) =
      phase (-s) ((-Complex.I) • (fun n =>
        ((cutoff R (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) v)) : ℝ) : ℂ) *
          nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) v)) n -
        ((cutoff R (hn 1 (carrierCoe38 ((1 : ℕ) : ℝ) w)) : ℝ) : ℂ) *
          nonlin (phase s (carrierCoe38 ((1 : ℕ) : ℝ) w)) n)) := by
    funext n
    simp only [phase, Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, wl2_phase38, wl2_smul38, norm_neg, Complex.norm_I, one_mul]

end NlsGge.NLS38
