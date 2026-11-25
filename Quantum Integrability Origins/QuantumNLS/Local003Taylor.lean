import Mathlib

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110), stage H1: Cauchy estimates for the
complexified reduced matrix.

Source (end of the proof): "One can make this last step explicit by complexifying ... the Neumann and inverse-square-root
series are bounded on a common complex ball, so their homogeneous coefficients obey a common geometric bound.  Summing
the odd terms of degree at least three gives `C‖u‖³`, and differentiating gives `C'‖u‖²`."

This module is pure complex analysis, independent of the operator theory: if `𝔟 : X → ℂ` is complex analytic and bounded by
`M` on the ball `‖Y‖ < q0` of a complex Banach space, and is odd along the real lines of interest, then
* `cubic_line`: `‖𝔟 Y - d/dζ 𝔟(ζ Y)|₀‖ ≤ 32 M ‖Y‖³/q0³`  (`‖Y‖ ≤ q0/4`), the Taylor series of an odd function, Cauchy bounds
  `‖𝔟^{(n)}‖/n! ≤ M/R^n` on the Taylor coefficients;
* `even_deriv`: the derivative `A(ζ) = ∂_ξ 𝔟(ζ Y + ξ Z)|₀` is even in `ζ`, so `‖A(1) - A(0)‖ ≤ 128 M ‖Y‖²‖Z‖/q0³`.
Oddness is only assumed on a short real interval and extended to the complex disc by the identity theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Metric Filter Topology Set
open scoped Nat
namespace QuantumNLS.Local003Taylor

/-! ### Taylor tails with Cauchy bounds -/

lemma taylor_tail {ψ : ℂ → ℂ} {R R' M : ℝ} (hR' : 0 < R') (hRR : R' < R)
    (hd : DifferentiableOn ℂ ψ (ball 0 R)) (hM : ∀ ζ ∈ ball (0 : ℂ) R, ‖ψ ζ‖ ≤ M) (k : ℕ) {ζ : ℂ}
    (hζ : ‖ζ‖ < R') :
    ‖ψ ζ - ∑ j ∈ Finset.range k, (j ! : ℂ)⁻¹ • ζ ^ j • iteratedDeriv j ψ 0‖ ≤
      M * (‖ζ‖ / R') ^ k / (1 - ‖ζ‖ / R') := by
  have hζR : ζ ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
  have hsum := Complex.hasSum_taylorSeries_on_ball hd hζR
  simp only [sub_zero] at hsum
  set t : ℕ → ℂ := fun n => (n ! : ℂ)⁻¹ • ζ ^ n • iteratedDeriv n ψ 0 with ht
  have hR0 : 0 < R := lt_trans hR' hRR
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR0
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0)
  have hq0 : 0 ≤ ‖ζ‖ / R' := by positivity
  have hq1 : ‖ζ‖ / R' < 1 := by rw [div_lt_one hR']; exact hζ
  have hcoef : ∀ n, ‖t n‖ ≤ M * (‖ζ‖ / R') ^ n := by
    intro n
    have hdc : DiffContOnCl ℂ ψ (ball 0 R') := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hR'.ne']
      exact hd.mono (closedBall_subset_ball hRR)
    have hC : ∀ z ∈ sphere (0 : ℂ) R', ‖ψ z‖ ≤ M := fun z hz =>
      hM z (by rw [mem_ball_zero_iff]; rw [mem_sphere_zero_iff_norm] at hz; linarith)
    have hn := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR' hdc hC
    have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    calc ‖t n‖ = ((n ! : ℝ))⁻¹ * (‖ζ‖ ^ n * ‖iteratedDeriv n ψ 0‖) := by
          simp only [ht, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
      _ ≤ ((n ! : ℝ))⁻¹ * (‖ζ‖ ^ n * ((n ! : ℝ) * M / R' ^ n)) := by gcongr
      _ = M * (‖ζ‖ / R') ^ n := by
          rw [div_pow]; field_simp
  have hsplit := hsum.summable.sum_add_tsum_nat_add k
  rw [hsum.tsum_eq] at hsplit
  have hrem : ψ ζ - ∑ j ∈ Finset.range k, t j = ∑' i, t (i + k) := by
    rw [← hsplit]; abel
  have hgeom : HasSum (fun i : ℕ => M * (‖ζ‖ / R') ^ k * (‖ζ‖ / R') ^ i)
      (M * (‖ζ‖ / R') ^ k * (1 - ‖ζ‖ / R')⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hb : ‖∑' i, t (i + k)‖ ≤ M * (‖ζ‖ / R') ^ k * (1 - ‖ζ‖ / R')⁻¹ := by
    refine tsum_of_norm_bounded hgeom (fun i => ?_)
    calc ‖t (i + k)‖ ≤ M * (‖ζ‖ / R') ^ (i + k) := hcoef _
      _ = M * (‖ζ‖ / R') ^ k * (‖ζ‖ / R') ^ i := by rw [pow_add]; ring
  have hfinal : ψ ζ - ∑ j ∈ Finset.range k, (j ! : ℂ)⁻¹ • ζ ^ j • iteratedDeriv j ψ 0 =
      ∑' i, t (i + k) := hrem
  rw [hfinal]
  calc ‖∑' i, t (i + k)‖ ≤ M * (‖ζ‖ / R') ^ k * (1 - ‖ζ‖ / R')⁻¹ := hb
    _ = M * (‖ζ‖ / R') ^ k / (1 - ‖ζ‖ / R') := (div_eq_mul_inv _ _).symm

/-- Tail constant: for `‖ζ‖ ≤ R/4` and `R' = R/2`, `q = 2‖ζ‖/R ≤ 1/2`. -/
lemma tail_const {ζ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) (hζ : ‖ζ‖ ≤ R / 4) (k : ℕ) :
    M * (‖ζ‖ / (R / 2)) ^ k / (1 - ‖ζ‖ / (R / 2)) ≤ 2 * M * (2 * ‖ζ‖ / R) ^ k := by
  have hq : ‖ζ‖ / (R / 2) = 2 * ‖ζ‖ / R := by field_simp
  rw [hq]
  have hq0 : 0 ≤ 2 * ‖ζ‖ / R := by positivity
  have hq1 : 2 * ‖ζ‖ / R ≤ 1 / 2 := by
    rw [div_le_iff₀ hR]; linarith
  have hpos : 0 < 1 - 2 * ‖ζ‖ / R := by linarith
  rw [div_le_iff₀ hpos]
  have hp : 0 ≤ M * (2 * ‖ζ‖ / R) ^ k := by positivity
  nlinarith [hp]

/-! ### Odd and even functions -/

lemma odd_taylor {ψ : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ ψ (ball 0 R))
    (hM : ∀ ζ ∈ ball (0 : ℂ) R, ‖ψ ζ‖ ≤ M) (hodd : ∀ ζ ∈ ball (0 : ℂ) R, ψ (-ζ) = -ψ ζ)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ R / 4) :
    ‖ψ ζ - deriv ψ 0 * ζ‖ ≤ 32 * M * ‖ζ‖ ^ 3 / R ^ 3 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0)
  have hψ0 : ψ 0 = 0 := by
    have := hodd 0 h0
    simp only [neg_zero] at this
    have h2 : (2 : ℂ) * ψ 0 = 0 := by linear_combination this
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have hR2 : R / 2 < R := by linarith
  have hR2p : 0 < R / 2 := by linarith
  have hζ' : ‖ζ‖ < R / 2 := by linarith
  have hζ'' : ‖-ζ‖ < R / 2 := by rw [norm_neg]; exact hζ'
  have t1 := taylor_tail hR2p hR2 hd hM 3 hζ'
  have t2 := taylor_tail hR2p hR2 hd hM 3 hζ''
  have c := tail_const (ζ := ζ) hR hMnn hζ 3
  rw [norm_neg] at t2
  have hn : ‖-ζ‖ = ‖ζ‖ := norm_neg ζ
  have hS : ∀ w : ℂ, ∑ j ∈ Finset.range 3, (j ! : ℂ)⁻¹ • w ^ j • iteratedDeriv j ψ 0 =
      iteratedDeriv 0 ψ 0 + w * deriv ψ 0 + (1 / 2 : ℂ) * w ^ 2 * iteratedDeriv 2 ψ 0 := by
    intro w
    simp [Finset.sum_range_succ, iteratedDeriv_one, Nat.factorial]
    ring
  rw [hS] at t1 t2
  have hψ0' : iteratedDeriv 0 ψ 0 = 0 := by rw [iteratedDeriv_zero]; exact hψ0
  rw [hψ0'] at t1 t2
  have ho := hodd ζ (by rw [mem_ball_zero_iff]; linarith)
  set d1 := deriv ψ 0
  set d2 := iteratedDeriv 2 ψ 0
  set T := 2 * M * (2 * ‖ζ‖ / R) ^ 3 with hT
  -- e(ζ) = ψ ζ - (0 + ζ d1 + 1/2 ζ² d2), e(-ζ) = ψ(-ζ) - (0 + (-ζ) d1 + 1/2 ζ² d2)
  have hsumE : (ψ ζ - (0 + ζ * d1 + (1 / 2 : ℂ) * ζ ^ 2 * d2)) +
      (ψ (-ζ) - (0 + (-ζ) * d1 + (1 / 2 : ℂ) * (-ζ) ^ 2 * d2)) = -(ζ ^ 2 * d2) := by
    rw [ho]; ring
  have h1 : ‖ζ ^ 2 * d2‖ ≤ 2 * (M * (‖ζ‖ / (R / 2)) ^ 3 / (1 - ‖ζ‖ / (R / 2))) := by
    calc ‖ζ ^ 2 * d2‖ = ‖(ψ ζ - (0 + ζ * d1 + (1 / 2 : ℂ) * ζ ^ 2 * d2)) +
          (ψ (-ζ) - (0 + (-ζ) * d1 + (1 / 2 : ℂ) * (-ζ) ^ 2 * d2))‖ := by rw [hsumE, norm_neg]
      _ ≤ ‖ψ ζ - (0 + ζ * d1 + (1 / 2 : ℂ) * ζ ^ 2 * d2)‖ +
          ‖ψ (-ζ) - (0 + (-ζ) * d1 + (1 / 2 : ℂ) * (-ζ) ^ 2 * d2)‖ := norm_add_le _ _
      _ ≤ _ := by
          have a1 := t1
          have a2 := t2
          simp only [zero_add] at a1 a2 ⊢
          linarith
  have h2 : ‖(1 / 2 : ℂ) * ζ ^ 2 * d2‖ ≤ M * (‖ζ‖ / (R / 2)) ^ 3 / (1 - ‖ζ‖ / (R / 2)) := by
    have : ‖(1 / 2 : ℂ) * ζ ^ 2 * d2‖ = (1 / 2) * ‖ζ ^ 2 * d2‖ := by
      rw [mul_assoc, norm_mul]; simp
    rw [this]; linarith
  have key : ψ ζ - d1 * ζ = (ψ ζ - (0 + ζ * d1 + (1 / 2 : ℂ) * ζ ^ 2 * d2)) + (1 / 2 : ℂ) * ζ ^ 2 * d2 := by ring
  rw [key]
  calc ‖(ψ ζ - (0 + ζ * d1 + (1 / 2 : ℂ) * ζ ^ 2 * d2)) + (1 / 2 : ℂ) * ζ ^ 2 * d2‖
      ≤ ‖ψ ζ - (0 + ζ * d1 + (1 / 2 : ℂ) * ζ ^ 2 * d2)‖ + ‖(1 / 2 : ℂ) * ζ ^ 2 * d2‖ := norm_add_le _ _
    _ ≤ 2 * (M * (‖ζ‖ / (R / 2)) ^ 3 / (1 - ‖ζ‖ / (R / 2))) := by
        have a1 := t1
        simp only [zero_add] at a1 ⊢
        linarith
    _ ≤ 2 * T := by linarith
    _ = 32 * M * ‖ζ‖ ^ 3 / R ^ 3 := by rw [hT]; field_simp; ring

lemma even_taylor {ψ : ℂ → ℂ} {R M : ℝ} (hR : 0 < R) (hd : DifferentiableOn ℂ ψ (ball 0 R))
    (hM : ∀ ζ ∈ ball (0 : ℂ) R, ‖ψ ζ‖ ≤ M) (heven : ∀ ζ ∈ ball (0 : ℂ) R, ψ (-ζ) = ψ ζ)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ R / 4) :
    ‖ψ ζ - ψ 0‖ ≤ 16 * M * ‖ζ‖ ^ 2 / R ^ 2 := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hMnn : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 h0)
  have hR2 : R / 2 < R := by linarith
  have hR2p : 0 < R / 2 := by linarith
  have hζ' : ‖ζ‖ < R / 2 := by linarith
  have hζ'' : ‖-ζ‖ < R / 2 := by rw [norm_neg]; exact hζ'
  have t1 := taylor_tail hR2p hR2 hd hM 2 hζ'
  have t2 := taylor_tail hR2p hR2 hd hM 2 hζ''
  have c := tail_const (ζ := ζ) hR hMnn hζ 2
  have hn : ‖-ζ‖ = ‖ζ‖ := norm_neg ζ
  rw [hn] at t2
  have hS : ∀ w : ℂ, ∑ j ∈ Finset.range 2, (j ! : ℂ)⁻¹ • w ^ j • iteratedDeriv j ψ 0 =
      ψ 0 + w * deriv ψ 0 := by
    intro w
    simp [Finset.sum_range_succ, iteratedDeriv_one, Nat.factorial, iteratedDeriv_zero]
  rw [hS] at t1 t2
  have he := heven ζ (by rw [mem_ball_zero_iff]; linarith)
  set d1 := deriv ψ 0
  set T := 2 * M * (2 * ‖ζ‖ / R) ^ 2 with hT
  have hdiff : (ψ ζ - (ψ 0 + ζ * d1)) - (ψ (-ζ) - (ψ 0 + (-ζ) * d1)) = -(2 * ζ * d1) := by
    rw [he]; ring
  have h1 : ‖2 * ζ * d1‖ ≤ 2 * (M * (‖ζ‖ / (R / 2)) ^ 2 / (1 - ‖ζ‖ / (R / 2))) := by
    calc ‖2 * ζ * d1‖ = ‖(ψ ζ - (ψ 0 + ζ * d1)) - (ψ (-ζ) - (ψ 0 + (-ζ) * d1))‖ := by
          rw [hdiff, norm_neg]
      _ ≤ ‖ψ ζ - (ψ 0 + ζ * d1)‖ + ‖ψ (-ζ) - (ψ 0 + (-ζ) * d1)‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have h2 : ‖ζ * d1‖ ≤ M * (‖ζ‖ / (R / 2)) ^ 2 / (1 - ‖ζ‖ / (R / 2)) := by
    have : ‖2 * ζ * d1‖ = 2 * ‖ζ * d1‖ := by
      rw [mul_assoc, norm_mul]; simp
    rw [this] at h1; linarith
  have key : ψ ζ - ψ 0 = (ψ ζ - (ψ 0 + ζ * d1)) + ζ * d1 := by ring
  rw [key]
  calc ‖(ψ ζ - (ψ 0 + ζ * d1)) + ζ * d1‖ ≤ ‖ψ ζ - (ψ 0 + ζ * d1)‖ + ‖ζ * d1‖ := norm_add_le _ _
    _ ≤ 2 * (M * (‖ζ‖ / (R / 2)) ^ 2 / (1 - ‖ζ‖ / (R / 2))) := by linarith
    _ ≤ 2 * T := by linarith
    _ = 16 * M * ‖ζ‖ ^ 2 / R ^ 2 := by rw [hT]; field_simp; ring

/-! ### Real symmetry extends to the disc -/

lemma eq_of_real {f g : ℂ → ℂ} {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (ball 0 R)) (hg : DifferentiableOn ℂ g (ball 0 R))
    (h : ∀ t : ℝ, |t| < ε → f (t : ℂ) = g (t : ℂ)) : ∀ ζ ∈ ball (0 : ℂ) R, f ζ = g ζ := by
  have hfa : AnalyticOnNhd ℂ f (ball 0 R) := hf.analyticOnNhd isOpen_ball
  have hga : AnalyticOnNhd ℂ g (ball 0 R) := hg.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    let f : ℕ → ℝ := fun n => (ε / 2) * (1 / ((n : ℝ) + 1))
    let u : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ)
    have hu : Tendsto u atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h1 : Tendsto f atTop (𝓝 0) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε / 2)
          simpa [f] using this
        have := (Complex.continuous_ofReal.tendsto 0).comp h1
        rw [Complex.ofReal_zero] at this
        exact this
      · simp only [u, f, mem_compl_iff, mem_singleton_iff]
        have : (0 : ℝ) < (ε / 2) * (1 / ((n : ℝ) + 1)) := by positivity
        exact_mod_cast this.ne'
    refine hu.frequently (Frequently.of_forall fun n => ?_)
    refine h _ ?_
    have : (0 : ℝ) < (ε / 2) * (1 / ((n : ℝ) + 1)) := by positivity
    show |(ε / 2) * (1 / ((n : ℝ) + 1))| < ε
    rw [abs_of_pos this]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc (ε / 2) * (1 / ((n : ℝ) + 1)) ≤ (ε / 2) * 1 := by gcongr
      _ < ε := by linarith
  exact fun ζ hζ => hfa.eqOn_of_preconnected_of_frequently_eq hga (convex_ball _ _).isPreconnected h0 hfreq hζ

/-! ### Lines in a complex Banach space -/

section Line
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma cubic_line (𝔟 : X → ℂ) {q0 M : ℝ} (hq0 : 0 < q0)
    (hana : AnalyticOnNhd ℂ 𝔟 (ball 0 q0)) (hM : ∀ Y ∈ ball (0 : X) q0, ‖𝔟 Y‖ ≤ M)
    {Y : X} (hY : ‖Y‖ ≤ q0 / 4) {ε : ℝ} (hε : 0 < ε)
    (hodd : ∀ t : ℝ, |t| < ε → 𝔟 ((-t : ℝ) • Y) = - 𝔟 (t • Y)) :
    ‖𝔟 Y - deriv (fun ζ : ℂ => 𝔟 (ζ • Y)) 0‖ ≤ 32 * M * ‖Y‖ ^ 3 / q0 ^ 3 := by
  by_cases hY0 : Y = 0
  · subst hY0
    have h := hodd 0 (by rw [abs_zero]; exact hε)
    simp only [neg_zero, zero_smul] at h
    have h2 : (2 : ℂ) * 𝔟 0 = 0 := by linear_combination h
    have h0 : 𝔟 0 = 0 := (mul_eq_zero.mp h2).resolve_left two_ne_zero
    simp [h0]
  · have hYpos : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
    set R : ℝ := q0 / ‖Y‖ with hRdef
    have hR : 0 < R := by positivity
    have hmem : ∀ ζ ∈ ball (0 : ℂ) R, ζ • Y ∈ ball (0 : X) q0 := by
      intro ζ hζ
      rw [mem_ball_zero_iff] at hζ ⊢
      rw [norm_smul]
      calc ‖ζ‖ * ‖Y‖ < R * ‖Y‖ := by gcongr
        _ = q0 := by rw [hRdef]; field_simp
    set ψ : ℂ → ℂ := fun ζ => 𝔟 (ζ • Y) with hψ
    have hd : DifferentiableOn ℂ ψ (ball 0 R) := by
      intro ζ hζ
      exact (((hana _ (hmem ζ hζ)).differentiableAt).comp ζ
        (differentiableAt_id.smul_const Y)).differentiableWithinAt
    have hMψ : ∀ ζ ∈ ball (0 : ℂ) R, ‖ψ ζ‖ ≤ M := fun ζ hζ => hM _ (hmem ζ hζ)
    have hoddψ : ∀ ζ ∈ ball (0 : ℂ) R, ψ (-ζ) = -ψ ζ := by
      have hneg : DifferentiableOn ℂ (fun ζ => ψ (-ζ)) (ball 0 R) := by
        refine hd.comp differentiable_neg.differentiableOn (fun ζ hζ => ?_)
        rw [mem_ball_zero_iff] at hζ ⊢; rwa [norm_neg]
      refine eq_of_real hR (lt_min hε hR) hneg hd.neg (fun t ht => ?_)
      have ht' : |t| < ε := lt_of_lt_of_le ht (min_le_left _ _)
      have := hodd t ht'
      simp only [hψ, Pi.neg_apply]
      rw [show (-(t : ℂ)) = ((-t : ℝ) : ℂ) by push_cast; ring, Complex.coe_smul, Complex.coe_smul]
      exact this
    have hR4 : ‖(1 : ℂ)‖ ≤ R / 4 := by
      have h4 : 4 ≤ q0 / ‖Y‖ := by rw [le_div_iff₀ hYpos]; linarith
      rw [norm_one, hRdef]; linarith
    have := odd_taylor hR hd hMψ hoddψ hR4
    simp only [hψ, one_smul, mul_one, norm_one, one_pow] at this
    calc ‖𝔟 Y - deriv (fun ζ : ℂ => 𝔟 (ζ • Y)) 0‖ ≤ 32 * M / R ^ 3 := this
      _ = 32 * M * ‖Y‖ ^ 3 / q0 ^ 3 := by rw [hRdef]; field_simp

lemma even_deriv (𝔟 : X → ℂ) {q0 M : ℝ} (hq0 : 0 < q0)
    (hana : AnalyticOnNhd ℂ 𝔟 (ball 0 q0)) (hM : ∀ Y ∈ ball (0 : X) q0, ‖𝔟 Y‖ ≤ M)
    {Y Z : X} (hY : ‖Y‖ ≤ q0 / 8) {ε : ℝ} (hε : 0 < ε)
    (hodd : ∀ t s : ℝ, |t| < ε → |s| < ε →
      𝔟 ((-t : ℝ) • Y + (-s : ℝ) • Z) = - 𝔟 (t • Y + s • Z)) :
    ‖deriv (fun ξ : ℂ => 𝔟 (Y + ξ • Z)) 0 - deriv (fun ξ : ℂ => 𝔟 (ξ • Z)) 0‖ ≤
      128 * M * ‖Y‖ ^ 2 * ‖Z‖ / q0 ^ 3 := by
  by_cases hY0 : Y = 0
  · subst hY0
    simp
  by_cases hZ0 : Z = 0
  · subst hZ0
    simp
  have hYpos : 0 < ‖Y‖ := norm_pos_iff.mpr hY0
  have hZpos : 0 < ‖Z‖ := norm_pos_iff.mpr hZ0
  set R : ℝ := q0 / (2 * ‖Y‖) with hRdef
  set δ : ℝ := q0 / (2 * ‖Z‖) with hδdef
  have hR : 0 < R := by positivity
  have hδ : 0 < δ := by positivity
  have hmem : ∀ ζ ∈ ball (0 : ℂ) R, ζ • Y ∈ ball (0 : X) q0 := by
    intro ζ hζ
    rw [mem_ball_zero_iff] at hζ ⊢
    rw [norm_smul]
    have : ‖ζ‖ * ‖Y‖ < R * ‖Y‖ := by gcongr
    have h2 : R * ‖Y‖ = q0 / 2 := by rw [hRdef]; field_simp
    linarith
  have hmem2 : ∀ ζ ∈ ball (0 : ℂ) R, ∀ ξ ∈ closedBall (0 : ℂ) δ, ζ • Y + ξ • Z ∈ ball (0 : X) q0 := by
    intro ζ hζ ξ hξ
    rw [mem_ball_zero_iff] at hζ ⊢
    rw [mem_closedBall_zero_iff] at hξ
    calc ‖ζ • Y + ξ • Z‖ ≤ ‖ζ • Y‖ + ‖ξ • Z‖ := norm_add_le _ _
      _ = ‖ζ‖ * ‖Y‖ + ‖ξ‖ * ‖Z‖ := by rw [norm_smul, norm_smul]
      _ < q0 := by
        have h1 : ‖ζ‖ * ‖Y‖ < R * ‖Y‖ := by gcongr
        have h2 : R * ‖Y‖ = q0 / 2 := by rw [hRdef]; field_simp
        have h3 : ‖ξ‖ * ‖Z‖ ≤ δ * ‖Z‖ := by gcongr
        have h4 : δ * ‖Z‖ = q0 / 2 := by rw [hδdef]; field_simp
        linarith
  set A : ℂ → ℂ := fun ζ => deriv (fun ξ : ℂ => 𝔟 (ζ • Y + ξ • Z)) 0 with hAdef
  have hA : ∀ ζ ∈ ball (0 : ℂ) R, HasDerivAt (fun ξ : ℂ => 𝔟 (ζ • Y + ξ • Z))
      (fderiv ℂ 𝔟 (ζ • Y) Z) 0 := by
    intro ζ hζ
    have h𝔟 : DifferentiableAt ℂ 𝔟 (ζ • Y) := (hana _ (hmem ζ hζ)).differentiableAt
    have hline : HasDerivAt (fun ξ : ℂ => ζ • Y + ξ • Z) ((1 : ℂ) • Z) 0 :=
      ((hasDerivAt_id (0 : ℂ)).smul_const Z).const_add (ζ • Y)
    have := h𝔟.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hline (by simp)
    simp only [one_smul] at this
    exact this
  have hAeq : ∀ ζ ∈ ball (0 : ℂ) R, A ζ = fderiv ℂ 𝔟 (ζ • Y) Z := fun ζ hζ => (hA ζ hζ).deriv
  have hfd : AnalyticOnNhd ℂ (fderiv ℂ 𝔟) (ball 0 q0) := hana.fderiv
  have hdA : DifferentiableOn ℂ A (ball 0 R) := by
    intro ζ hζ
    have : DifferentiableAt ℂ (fun ζ : ℂ => (fderiv ℂ 𝔟 (ζ • Y)) Z) ζ :=
      (((hfd _ (hmem ζ hζ)).differentiableAt).comp ζ
        (differentiableAt_id.smul_const Y)).clm_apply (differentiableAt_const Z)
    refine (this.differentiableWithinAt).congr (fun w hw => hAeq w hw) (hAeq ζ hζ)
  have hbound : ∀ ζ ∈ ball (0 : ℂ) R, ‖A ζ‖ ≤ M / δ := by
    intro ζ hζ
    have hdc : DiffContOnCl ℂ (fun ξ : ℂ => 𝔟 (ζ • Y + ξ • Z)) (ball 0 δ) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hδ.ne']
      intro ξ hξ
      exact (((hana _ (hmem2 ζ hζ ξ hξ)).differentiableAt).comp ξ
        ((differentiableAt_const _).add (differentiableAt_id.smul_const Z))).differentiableWithinAt
    have hC : ∀ ξ ∈ sphere (0 : ℂ) δ, ‖𝔟 (ζ • Y + ξ • Z)‖ ≤ M := fun ξ hξ =>
      hM _ (hmem2 ζ hζ ξ (sphere_subset_closedBall hξ))
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc hC
  -- evenness
  have hevenA : ∀ ζ ∈ ball (0 : ℂ) R, A (-ζ) = A ζ := by
    have hneg : DifferentiableOn ℂ (fun ζ => A (-ζ)) (ball 0 R) := by
      refine hdA.comp differentiable_neg.differentiableOn (fun ζ hζ => ?_)
      rw [mem_ball_zero_iff] at hζ ⊢; rwa [norm_neg]
    refine eq_of_real hR (lt_min hε hR) hneg hdA (fun t ht => ?_)
    have ht1 : |t| < ε := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 : |t| < R := lt_of_lt_of_le ht (min_le_right _ _)
    have hmt : ((t : ℂ)) ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact ht2
    have hmnt : (-(t : ℂ)) ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs]; exact ht2
    -- real-line derivatives
    have d1 : HasDerivAt (fun s : ℝ => 𝔟 ((-(t : ℂ)) • Y + (s : ℂ) • Z)) (A (-(t : ℂ))) 0 := by
      have h := (hA _ hmnt)
      rw [← hAeq _ hmnt] at h
      exact HasDerivAt.comp_ofReal (e := fun ξ : ℂ => 𝔟 ((-(t : ℂ)) • Y + ξ • Z)) (z := 0)
        (by rw [Complex.ofReal_zero]; exact h)
    have d2 : HasDerivAt (fun s : ℝ => 𝔟 ((t : ℂ) • Y + (s : ℂ) • Z)) (A (t : ℂ)) 0 := by
      have h := (hA _ hmt)
      rw [← hAeq _ hmt] at h
      exact HasDerivAt.comp_ofReal (e := fun ξ : ℂ => 𝔟 ((t : ℂ) • Y + ξ • Z)) (z := 0)
        (by rw [Complex.ofReal_zero]; exact h)
    have d1' : HasDerivAt (fun s : ℝ => 𝔟 ((-(t : ℂ)) • Y + ((-s : ℝ) : ℂ) • Z)) (-(A (-(t : ℂ)))) 0 := by
      have h := d1.scomp_of_eq (0 : ℝ) (hasDerivAt_neg (0 : ℝ)) (by simp)
      have h' : (-1 : ℝ) • A (-(t : ℂ)) = -(A (-(t : ℂ))) := by simp
      rw [h'] at h
      exact h
    have d2' : HasDerivAt (fun s : ℝ => -𝔟 ((t : ℂ) • Y + (s : ℂ) • Z)) (-(A (t : ℂ))) 0 := d2.neg
    have hev : (fun s : ℝ => 𝔟 ((-(t : ℂ)) • Y + ((-s : ℝ) : ℂ) • Z)) =ᶠ[𝓝 0]
        (fun s : ℝ => -𝔟 ((t : ℂ) • Y + (s : ℂ) • Z)) := by
      have hlt : ∀ᶠ s : ℝ in 𝓝 0, |s| < ε := by
        have : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
        filter_upwards [this] with s hs
        simpa [Real.dist_eq] using hs
      filter_upwards [hlt] with s hs
      have := hodd t s ht1 hs
      have e : (-(t : ℂ)) = ((-t : ℝ) : ℂ) := by push_cast; ring
      rw [e]
      simp only [Complex.coe_smul]
      exact this
    have := d1'.unique (d2'.congr_of_eventuallyEq hev)
    simpa using this
  have hR4 : ‖(1 : ℂ)‖ ≤ R / 4 := by
    have h4 : 4 ≤ q0 / (2 * ‖Y‖) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [norm_one, hRdef]; linarith
  have hM0 : 0 ≤ M / δ := le_trans (norm_nonneg _) (hbound 0 (mem_ball_self hR))
  have := even_taylor hR hdA hbound hevenA hR4
  have e1 : A 1 = deriv (fun ξ : ℂ => 𝔟 (Y + ξ • Z)) 0 := by simp [hAdef]
  have e0 : A 0 = deriv (fun ξ : ℂ => 𝔟 (ξ • Z)) 0 := by simp [hAdef]
  rw [e1, e0] at this
  calc ‖deriv (fun ξ : ℂ => 𝔟 (Y + ξ • Z)) 0 - deriv (fun ξ : ℂ => 𝔟 (ξ • Z)) 0‖
      ≤ 16 * (M / δ) * ‖(1 : ℂ)‖ ^ 2 / R ^ 2 := this
    _ = 128 * M * ‖Y‖ ^ 2 * ‖Z‖ / q0 ^ 3 := by
        rw [hRdef, hδdef, norm_one]; field_simp; ring

end Line

end QuantumNLS.Local003Taylor
#print axioms QuantumNLS.Local003Taylor.taylor_tail
#print axioms QuantumNLS.Local003Taylor.odd_taylor
#print axioms QuantumNLS.Local003Taylor.even_taylor
#print axioms QuantumNLS.Local003Taylor.eq_of_real
#print axioms QuantumNLS.Local003Taylor.cubic_line
#print axioms QuantumNLS.Local003Taylor.even_deriv
