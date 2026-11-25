import NlsGge.GK38.Lib.InterpolationHermite

/-!
# L4b, part 8: the Interpolation Lemma (book Lemma F.4)

Source: Grébert–Kappeler book, Appendix F, Lemma F.4 (GKP Lemma 22.4).

**Erratum (book Lemma F.4).**  The book states the growth hypothesis as
`sup_{λ ∈ C_n} |φ(λ)/sin λ| = O(1)`.  This cannot suffice: for `φ = sin`, `σ_n = nπ` the hypothesis
holds, but `φ(σ_n) = 0` for all `n` while `φ(z) ≠ 0` (`interpolation_fails_of_bounded`, in
`InterpolationProbe`).  The book's own proof needs `sup_{C_n} |(λ - z) g(λ)| → 0`, i.e. the ratio is
`o(1)`, and all the applications (book proofs of Lemma 14.8, 18.1, 18.4) establish
`sup_{C_ν} |φ/sin| → 0` explicitly.  The statement proved here has the hypothesis `o(1)`
(`hdecay`), which is what the proof uses; the plan's `O(1)` form is false.

The residue theorem of the book proof is replaced by the Lagrange partial-fraction identity and
Cauchy's integral formula (`hermite_remainder`); the estimate of the contour integral uses
`product_growth` (book Lemma C.5).
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric Complex

namespace NlsGge.GK38.Lib

noncomputable section

/-- Bound of the remainder integral. -/
theorem norm_hermiteJ_le {φ : ℂ → ℂ} {σ : ℤ → ℂ} {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R / 2)
    {ε₁ : ℝ} (hε₁ : 0 ≤ ε₁) (h : ∀ l : ℂ, ‖l‖ = R → ‖φ l‖ ≤ 2 * ε₁ * ‖psiProd σ l‖) :
    ‖hermiteJ φ σ R z‖ ≤ 4 * ε₁ := by
  have hg : ∀ l ∈ sphere (0 : ℂ) R, ‖φ l / (psiProd σ l * (l - z))‖ ≤ 4 * ε₁ / R := by
    intro l hl
    have hlR : ‖l‖ = R := mem_sphere_zero_iff_norm.mp hl
    have hlz : R / 2 ≤ ‖l - z‖ := by
      have := norm_sub_norm_le l z
      linarith
    by_cases hψ : psiProd σ l = 0
    · rw [hψ]; simp; positivity
    · have hψn : 0 < ‖psiProd σ l‖ := norm_pos_iff.mpr hψ
      rw [norm_div, norm_mul, div_le_div_iff₀ (mul_pos hψn (by linarith)) hR]
      have h1 := h l hlR
      have h2 : 0 ≤ ‖psiProd σ l‖ * ‖l - z‖ := by positivity
      calc ‖φ l‖ * R ≤ 2 * ε₁ * ‖psiProd σ l‖ * R := by gcongr
        _ ≤ 4 * ε₁ * (‖psiProd σ l‖ * ‖l - z‖) := by nlinarith [mul_nonneg hε₁ hψn.le]
  have hI := circleIntegral.norm_integral_le_of_norm_le_const hR.le hg
  unfold hermiteJ
  rw [norm_mul, norm_inv]
  have h2π : ‖(2 * Real.pi * Complex.I)‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2π]
  have hpi := Real.pi_pos
  calc (2 * Real.pi)⁻¹ * ‖∮ l in C((0 : ℂ), R), φ l / (psiProd σ l * (l - z))‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * R * (4 * ε₁ / R)) := by gcongr
    _ = 4 * ε₁ := by field_simp

/-- Multipliability and the value of the Lagrange coefficients for any `N ≥ N₁` with `n` in the
window. -/
theorem hasProd_cfam_of_sep {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) {N : ℕ}
    (hin : ∀ m ∈ win N, ‖σ m‖ < N * Real.pi + Real.pi / 2)
    (hout : ∀ m, m ∉ win N → N * Real.pi + Real.pi / 2 < ‖σ m‖) {n : ℤ} (hn : n ∈ win N) (z : ℂ) :
    HasProd (cfam σ z n) (cFin σ N z n * (tailProd σ N z / tailProd σ N (σ n))) (symmetricIcc ℤ) :=
  hasProd_cfam hσ z hn (tail_diff_ne hσ N hout (hin n hn).le).2

/-- The Lagrange coefficients are multipliable (first conclusion of the interpolation lemma). -/
theorem multipliable_cfam {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (z : ℂ)
    (n : ℤ) : Multipliable (cfam σ z n) (symmetricIcc ℤ) := by
  obtain ⟨N₁, hN₁⟩ := exists_window_sep hσ
  set N := max N₁ n.natAbs with hN
  have hn : n ∈ win N := by
    rw [mem_win]
    have : n.natAbs ≤ N := le_max_right _ _
    omega
  have hs := hN₁ N (le_max_left _ _)
  exact (hasProd_cfam_of_sep hσ hs.1 hs.2 hn z).multipliable

/-- A function on `ℤ` vanishing off `k` is symmetric-summable with sum `f k`. -/
theorem hasSum_symmetricIcc_single {f : ℤ → ℂ} (k : ℤ) (h : ∀ n, n ≠ k → f n = 0) :
    HasSum f (f k) (symmetricIcc ℤ) := by
  rw [hasSum_symmetricIcc_iff]
  refine tendsto_atTop_of_eventually_const (i₀ := k.natAbs) fun M hM => ?_
  rw [Finset.sum_eq_single k]
  · intro n _ hnk
    exact h n hnk
  · intro hk
    exfalso
    apply hk
    rw [Finset.mem_Icc]
    omega

theorem mem_win_of_natAbs_le {n : ℤ} {N : ℕ} (h : n.natAbs ≤ N) : n ∈ win N := by
  rw [mem_win]; omega

/-- **Book Lemma F.4 (Interpolation Lemma), corrected hypothesis.**  Let `φ` be entire with
`sup_{|λ| = nπ + π/2} |φ(λ)/sin λ| → 0` (`hdecay`; the book prints `O(1)`, see the module
docstring), and `σ_n = nπ + ℓ²_n` injective.  Then for every `z`, the Lagrange coefficients
`∏_{m≠n} (σ_m - z)/(σ_m - σ_n)` are symmetric-multipliable and
`φ(z) = Σ_n φ(σ_n) ∏_{m≠n} (σ_m - z)/(σ_m - σ_n)` as a symmetric sum over `ℤ`. -/
theorem interpolation_lemma {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hdecay : ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ = n * Real.pi + Real.pi / 2 →
      ‖φ z‖ ≤ ε * ‖Complex.sin z‖)
    {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖σ n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2)
    (hinj : Function.Injective σ) (z : ℂ) :
    (∀ n : ℤ, Multipliable (fun m : ℤ => if m = n then 1 else (σ m - z) / (σ m - σ n))
        (symmetricIcc ℤ)) ∧
    Summable (fun n : ℤ => φ (σ n) *
        ∏'[symmetricIcc ℤ] m : ℤ, (if m = n then 1 else (σ m - z) / (σ m - σ n)))
      (symmetricIcc ℤ) ∧
    φ z = ∑'[symmetricIcc ℤ] n : ℤ, φ (σ n) *
        ∏'[symmetricIcc ℤ] m : ℤ, (if m = n then 1 else (σ m - z) / (σ m - σ n)) := by
  have hσ' : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2 := hσ
  have hpi := Real.pi_pos
  obtain ⟨N₁, hN₁⟩ := exists_window_sep hσ'
  -- the coefficients
  set c : ℤ → ℂ := fun n => ∏'[symmetricIcc ℤ] m : ℤ, cfam σ z n m with hc
  have hcm : ∀ n, Multipliable (cfam σ z n) (symmetricIcc ℤ) := multipliable_cfam hσ' z
  have hcN : ∀ N : ℕ, N₁ ≤ N → ∀ n ∈ win N,
      c n = cFin σ N z n * (tailProd σ N z / tailProd σ N (σ n)) := fun N hN n hn =>
    (hasProd_cfam_of_sep hσ' (hN₁ N hN).1 (hN₁ N hN).2 hn z).tprod_eq
  -- the main claim
  have hmain : HasSum (fun n : ℤ => φ (σ n) * c n) (φ z) (symmetricIcc ℤ) := by
    by_cases hzσ : ∃ k, σ k = z
    · -- `z` is a node: the sum has the single term `n = k`
      obtain ⟨k, rfl⟩ := hzσ
      have hck : ∀ n, n ≠ k → c n = 0 := by
        intro n hnk
        set N := max N₁ (max n.natAbs k.natAbs) with hN
        have hn : n ∈ win N :=
          mem_win_of_natAbs_le (le_trans (le_max_left _ _) (le_max_right _ _))
        have hk : k ∈ (win N).erase n :=
          Finset.mem_erase.mpr ⟨hnk.symm,
            mem_win_of_natAbs_le (le_trans (le_max_right _ _) (le_max_right _ _))⟩
        rw [hcN N (le_max_left _ _) n hn, cFin, Finset.prod_eq_zero hk (by simp), zero_mul]
      have hckk : c k = 1 := by
        set N := max N₁ k.natAbs with hN
        have hk : k ∈ win N := mem_win_of_natAbs_le (le_max_right _ _)
        have hs := hN₁ N (le_max_left _ _)
        have hT : tailProd σ N (σ k) ≠ 0 := (tail_diff_ne hσ' N hs.2 (hs.1 k hk).le).2
        rw [hcN N (le_max_left _ _) k hk, div_self hT, mul_one, cFin]
        refine Finset.prod_eq_one fun m hm => ?_
        have hmk : σ m ≠ σ k := fun h => (Finset.ne_of_mem_erase hm) (hinj h)
        exact div_self (sub_ne_zero.mpr hmk)
      have := hasSum_symmetricIcc_single (f := fun n => φ (σ n) * c n) k
        (fun n hn => by rw [hck n hn, mul_zero])
      simpa [hckk] using this
    · push Not at hzσ
      rw [hasSum_symmetricIcc_iff, Metric.tendsto_atTop]
      intro ε hε
      have hψz : 0 ≤ ‖psiProd σ z‖ := norm_nonneg _
      set ε₁ : ℝ := ε / (8 * (‖psiProd σ z‖ + 1)) with hε₁def
      have hε₁ : 0 < ε₁ := by positivity
      obtain ⟨Nφ, hNφ⟩ := hdecay ε₁ hε₁
      obtain ⟨Nψ, hNψ⟩ := product_growth σ hσ (1 / 2) (by norm_num)
      refine ⟨max (max N₁ Nφ) (max Nψ ⌈2 * ‖z‖ / Real.pi⌉₊), fun N hN => ?_⟩
      have hN₁N : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
      have hNφN : Nφ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
      have hNψN : Nψ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
      have hNzN : ⌈2 * ‖z‖ / Real.pi⌉₊ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
      have hs := hN₁ N hN₁N
      have hR : 0 < (N : ℝ) * Real.pi + Real.pi / 2 := by positivity
      have hzR2 : ‖z‖ ≤ ((N : ℝ) * Real.pi + Real.pi / 2) / 2 := by
        have h1 : 2 * ‖z‖ / Real.pi ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hNzN)
        rw [div_le_iff₀ hpi] at h1
        nlinarith
      have hzR : ‖z‖ < (N : ℝ) * Real.pi + Real.pi / 2 := by linarith
      have hrem := hermite_remainder hφ hσ' hinj N hR hs.1 hs.2 hzR hzσ
      have hsum_eq : ∑ n ∈ Finset.Icc (-(N : ℤ)) N, φ (σ n) * c n
          = ∑ n ∈ win N, φ (σ n) * (cFin σ N z n * (tailProd σ N z / tailProd σ N (σ n))) :=
        Finset.sum_congr rfl fun n hn => by rw [hcN N hN₁N n hn]
      have hJ : ‖hermiteJ φ σ ((N : ℝ) * Real.pi + Real.pi / 2) z‖ ≤ 4 * ε₁ := by
        refine norm_hermiteJ_le hR hzR2 hε₁.le fun l hl => ?_
        have h1 := hNφ N hNφN l hl
        have h2 := hNψ N hNψN l hl
        have h3 : ‖Complex.sin l‖ ≤ ‖psiProd σ l‖ + ‖psiProd σ l + Complex.sin l‖ := by
          have := norm_sub_le (psiProd σ l + Complex.sin l) (psiProd σ l)
          rw [add_sub_cancel_left] at this
          linarith
        have h4 : ‖Complex.sin l‖ ≤ 2 * ‖psiProd σ l‖ := by
          have : ‖psiProd σ l + Complex.sin l‖ ≤ 1 / 2 * ‖Complex.sin l‖ := h2
          linarith
        calc ‖φ l‖ ≤ ε₁ * ‖Complex.sin l‖ := h1
          _ ≤ ε₁ * (2 * ‖psiProd σ l‖) := mul_le_mul_of_nonneg_left h4 hε₁.le
          _ = 2 * ε₁ * ‖psiProd σ l‖ := by ring
      rw [dist_eq_norm, hsum_eq, ← norm_neg, neg_sub]
      rw [hrem, norm_mul]
      calc ‖psiProd σ z‖ * ‖hermiteJ φ σ ((N : ℝ) * Real.pi + Real.pi / 2) z‖
          ≤ ‖psiProd σ z‖ * (4 * ε₁) := mul_le_mul_of_nonneg_left hJ hψz
        _ < ε := by
            rw [hε₁def]
            have hpos : 0 < ‖psiProd σ z‖ + 1 := by positivity
            have : ‖psiProd σ z‖ * (4 * (ε / (8 * (‖psiProd σ z‖ + 1))))
                = ε / 2 * (‖psiProd σ z‖ / (‖psiProd σ z‖ + 1)) := by
              field_simp; ring
            rw [this]
            have h5 : ‖psiProd σ z‖ / (‖psiProd σ z‖ + 1) < 1 := by
              rw [div_lt_one hpos]; linarith
            have h6 : 0 ≤ ‖psiProd σ z‖ / (‖psiProd σ z‖ + 1) := by positivity
            nlinarith
  refine ⟨fun n => hcm n, hmain.summable, ?_⟩
  exact hmain.tsum_eq.symm

end

end NlsGge.GK38.Lib
