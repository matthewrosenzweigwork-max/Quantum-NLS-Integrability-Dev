import NlsGge.GK38.Lib.EntireProducts

/-!
# L4b, part 5: tail products and the separation of the roots by the circles `|λ| = Nπ + π/2`

Source: proof of Grébert–Kappeler book Lemma F.4 (GKP Lemma 22.4).  For `σ = nπ + ℓ²` and the
symmetric product `ψ(w) = ∏'[symmetricIcc ℤ] (σ_m - w)/π_m` (`psiProd`, the book's `-ψ`) write
`ψ = P_N · T_N` with the finite part `P_N(w) = ∏_{|m|≤N} (σ_m - w)/π_m` and the *tail product*
`T_N(w) = ∏'[sym] (if |m| ≤ N then 1 else (σ_m - w)/π_m)` (`tailProd`).  The point used by the
interpolation proof is that for `N` large `T_N` is holomorphic and zero-free on the closed disc
`|w| ≤ R_N := Nπ + π/2`, which contains exactly the roots `σ_m`, `|m| ≤ N`.

* `exists_window_sep`: for `N ≥ N₁` the roots `σ_m`, `|m| ≤ N`, lie inside the circle and the other
  roots outside.
* `psiProd_eq`: `ψ = P_N · T_N`.
* `tail_diff_ne`: `T_N` is differentiable and nonzero at every `w` with `‖w‖ ≤ R` provided
  `R < ‖σ_m‖` for all `|m| > N`.  (Proof: `T_N = ψ''/Q` where `ψ''` is the product of the
  sequence with the roots `σ_m`, `|m| ≤ N`, moved outside the disc; this uses `product_entire`.)
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The symmetric window `{-N, …, N}`. -/
def win (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) N

theorem mem_win {N : ℕ} {m : ℤ} : m ∈ win N ↔ -(N : ℤ) ≤ m ∧ m ≤ N := Finset.mem_Icc

theorem prod_Icc_eq_prod_win (f : ℤ → ℂ) (N : ℕ) :
    ∏ n ∈ Finset.Icc (-(N : ℤ)) N, f n = ∏ n ∈ win N, f n := rfl

theorem win_mono {N M : ℕ} (h : N ≤ M) : win N ⊆ win M := by
  intro m hm
  rw [mem_win] at hm ⊢
  omega

/-- Factors of the tail product: `1` on the window, `(σ_m - w)/π_m` outside. -/
def tailFam (σ : ℤ → ℂ) (N : ℕ) (w : ℂ) (m : ℤ) : ℂ :=
  if m ∈ win N then 1 else prodFactor σ w m

/-- The tail product `T_N(w)`. -/
def tailProd (σ : ℤ → ℂ) (N : ℕ) (w : ℂ) : ℂ := ∏'[symmetricIcc ℤ] m : ℤ, tailFam σ N w m

/-- The full product `ψ(w) = ∏'[sym] (σ_m - w)/π_m` (the book's `-ψ`). -/
def psiProd (σ : ℤ → ℂ) (w : ℂ) : ℂ := ∏'[symmetricIcc ℤ] m : ℤ, prodFactor σ w m

theorem tailFam_pair (σ : ℤ → ℂ) (N : ℕ) (w : ℂ) (m : ℕ) :
    tailFam σ N w ((m : ℤ) + 1) * tailFam σ N w (-((m : ℤ) + 1)) - 1
      = if m + 1 ≤ N then 0 else pairTerm σ w m := by
  have h1 : ((m : ℤ) + 1 ∈ win N) ↔ m + 1 ≤ N := by rw [mem_win]; omega
  have h2 : (-((m : ℤ) + 1) ∈ win N) ↔ m + 1 ≤ N := by rw [mem_win]; omega
  by_cases h : m + 1 ≤ N
  · unfold tailFam
    simp only [h1, h2, h, ↓reduceIte]
    norm_num
  · unfold tailFam pairTerm
    simp only [h1, h2, h, ↓reduceIte]

theorem hasProd_tail {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (N : ℕ) (w : ℂ) :
    HasProd (tailFam σ N w) (tailProd σ N w) (symmetricIcc ℤ) := by
  have hm : Multipliable (tailFam σ N w) (symmetricIcc ℤ) := by
    refine multipliable_symm_pair
      ((summable_norm_pairTerm hσ w).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_)
    rw [tailFam_pair]
    split_ifs <;> simp
  exact hm.hasProd

theorem prod_win_split (f : ℤ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    ∏ m ∈ win M, f m = (∏ m ∈ win N, f m) * ∏ m ∈ win M \ win N, f m := by
  rw [mul_comm, Finset.prod_sdiff (win_mono hNM)]

theorem prod_win_tail (σ : ℤ → ℂ) (N : ℕ) (w : ℂ) {M : ℕ} (hNM : N ≤ M) :
    ∏ m ∈ win M, tailFam σ N w m = ∏ m ∈ win M \ win N, prodFactor σ w m := by
  rw [prod_win_split _ hNM]
  have h1 : ∏ m ∈ win N, tailFam σ N w m = 1 :=
    Finset.prod_eq_one fun m hm => by simp [tailFam, hm]
  have h2 : ∏ m ∈ win M \ win N, tailFam σ N w m = ∏ m ∈ win M \ win N, prodFactor σ w m :=
    Finset.prod_congr rfl fun m hm => by simp [tailFam, (Finset.mem_sdiff.mp hm).2]
  rw [h1, h2, one_mul]

/-- `ψ = P_N · T_N`. -/
theorem psiProd_eq {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (N : ℕ) (w : ℂ) :
    psiProd σ w = (∏ m ∈ win N, prodFactor σ w m) * tailProd σ N w := by
  have h1 := (multipliable_prodFactor hσ w).hasProd
  rw [hasProd_symmetricIcc_iff] at h1
  have h2 := hasProd_tail hσ N w
  rw [hasProd_symmetricIcc_iff] at h2
  have h3 := h2.const_mul (∏ m ∈ win N, prodFactor σ w m)
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [eventually_ge_atTop N] with M hM
  simp only [prod_Icc_eq_prod_win]
  rw [prod_win_tail σ N w hM, ← prod_win_split (prodFactor σ w) hM]

/-! ### Separation of the roots -/

theorem norm_cast_mul_pi (m : ℤ) : ‖(m : ℂ) * (Real.pi : ℂ)‖ = |(m : ℝ)| * Real.pi := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  congr 1
  rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]

/-- For `N ≥ N₁` the roots `σ_m`, `|m| ≤ N`, lie strictly inside `|λ| = Nπ + π/2` and all the
other roots strictly outside. -/
theorem exists_window_sep {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      (∀ m ∈ win N, ‖σ m‖ < N * Real.pi + Real.pi / 2) ∧
      (∀ m, m ∉ win N → N * Real.pi + Real.pi / 2 < ‖σ m‖) := by
  have hpi := Real.pi_pos
  -- the deviations are eventually small
  have hlim := hσ.tendsto_cofinite_zero
  have hev : ∀ᶠ n : ℤ in cofinite, ‖prodDev σ n‖ ^ 2 < (Real.pi / 2) ^ 2 :=
    hlim.eventually (gt_mem_nhds (by positivity))
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ m : ℤ, K ≤ |m| → ‖prodDev σ m‖ < Real.pi / 2 := by
    obtain ⟨K, hK⟩ := (hev.image (fun m : ℤ => |m|)).bddAbove
    refine ⟨K.toNat + 1, fun m hm => ?_⟩
    by_contra hcon
    have : m ∈ {x : ℤ | ¬ ‖prodDev σ x‖ ^ 2 < (Real.pi / 2) ^ 2} := by
      simp only [Set.mem_ofPred_eq, not_lt]
      have h0 := not_lt.mp hcon
      exact pow_le_pow_left₀ (by positivity) h0 2
    have h5 : |m| ≤ K := hK ⟨m, this, rfl⟩
    omega
  -- bound on the finitely many remaining roots
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ m : ℤ, |m| < K → ‖σ m‖ ≤ B := by
    refine ⟨∑ m ∈ win K, ‖σ m‖, fun m hm => ?_⟩
    have : m ∈ win K := by
      have h := abs_lt.mp hm
      rw [mem_win]; omega
    exact Finset.single_le_sum (f := fun m => ‖σ m‖) (fun _ _ => norm_nonneg _) this
  refine ⟨max K (⌈B / Real.pi⌉₊ + 1), fun N hN => ⟨fun m hm => ?_, fun m hm => ?_⟩⟩
  · have hmN : |m| ≤ N := by rw [mem_win] at hm; rw [abs_le]; constructor <;> omega
    have hNK : K ≤ N := (le_max_left _ _).trans hN
    have hNB : B / Real.pi < N := by
      have := (le_max_right _ _).trans hN
      have h2 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
      exact (Nat.le_ceil _).trans_lt (by exact_mod_cast h2)
    by_cases hmK : K ≤ |m|
    · have h1 := hK m hmK
      have h2 : σ m = prodDev σ m + (m : ℂ) * (Real.pi : ℂ) := by unfold prodDev; ring
      have h3 : ‖σ m‖ ≤ ‖prodDev σ m‖ + |(m : ℝ)| * Real.pi := by
        rw [h2]; refine (norm_add_le _ _).trans (le_of_eq ?_); rw [norm_cast_mul_pi]
      have h4 : |(m : ℝ)| ≤ N := by exact_mod_cast hmN
      nlinarith
    · have hmK' : |m| < K := not_le.mp hmK
      have := hB m hmK'
      have h5 : B < N * Real.pi := by
        rw [div_lt_iff₀ hpi] at hNB; exact hNB
      linarith
  · have hNK : K ≤ N := (le_max_left _ _).trans hN
    have hmN : (N : ℤ) + 1 ≤ |m| := by
      rw [mem_win] at hm
      rcases le_or_gt 0 m with h | h
      · rw [abs_of_nonneg h]; omega
      · rw [abs_of_neg h]; omega
    have h1 := hK m (by omega)
    have h2 : (m : ℂ) * (Real.pi : ℂ) = σ m - prodDev σ m := by unfold prodDev; ring
    have h3 : |(m : ℝ)| * Real.pi ≤ ‖σ m‖ + ‖prodDev σ m‖ := by
      rw [← norm_cast_mul_pi, h2]; exact norm_sub_le _ _
    have h4 : ((N : ℝ) + 1) ≤ |(m : ℝ)| := by exact_mod_cast hmN
    nlinarith

/-! ### The tail product is holomorphic and zero-free on the disc -/

/-- On `‖w‖ ≤ R`, where all roots with `|m| > N` lie outside, `T_N` is differentiable and nonzero. -/
theorem tail_diff_ne {σ : ℤ → ℂ} (hσ : Summable fun n : ℤ => ‖prodDev σ n‖ ^ 2) (N : ℕ) {R : ℝ}
    (hout : ∀ m, m ∉ win N → R < ‖σ m‖) {w : ℂ} (hw : ‖w‖ ≤ R) :
    DifferentiableAt ℂ (tailProd σ N) w ∧ tailProd σ N w ≠ 0 := by
  classical
  have hR : 0 ≤ R := (norm_nonneg _).trans hw
  set ρ : ℂ := ((R + 1 : ℝ) : ℂ) with hρdef
  have hρ : ‖ρ‖ = R + 1 := by
    rw [hρdef, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  set σ' : ℤ → ℂ := fun m => if m ∈ win N then ρ else σ m with hσ'def
  have hσ' : Summable fun n : ℤ => ‖prodDev σ' n‖ ^ 2 := by
    refine hσ.congr_cofinite (Filter.eventually_cofinite.mpr ?_)
    refine (win N).finite_toSet.subset fun n hn => ?_
    by_contra hnN
    have hnN' : n ∉ win N := fun h => hnN (Finset.mem_coe.mpr h)
    apply hn
    simp [prodDev, hσ'def, hnN']
  have htail : tailProd σ' N = tailProd σ N := by
    funext u
    unfold tailProd
    congr 1
    funext m
    unfold tailFam
    by_cases h : m ∈ win N
    · simp [h]
    · simp [h, prodFactor, hσ'def]
  set Q : ℂ → ℂ := fun u => ∏ m ∈ win N, prodFactor σ' u m with hQdef
  have hψ : ∀ u, psiProd σ' u = Q u * tailProd σ N u := by
    intro u
    rw [psiProd_eq hσ' N u, htail]
  obtain ⟨_, hdiff, hord⟩ := product_entire σ' hσ'
  have hwρ : w ≠ ρ := by
    intro h
    have := hρ
    rw [← h] at this
    linarith
  have hQ0 : Q w ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
    have hc : (piN m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero m)
    simp only [prodFactor, hσ'def, hm, ite_true]
    exact div_ne_zero (sub_ne_zero.mpr hwρ.symm) hc
  have hQd : Differentiable ℂ Q :=
    Differentiable.fun_finsetProd fun n _ => differentiable_prodFactor σ' n
  constructor
  · have hnb : ∀ᶠ u in 𝓝 w, u ≠ ρ := isOpen_ne.mem_nhds hwρ
    have heq : tailProd σ N =ᶠ[𝓝 w] fun u => psiProd σ' u / Q u := by
      filter_upwards [hnb] with u hu
      have hQu : Q u ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun m hm => ?_
        have hc : (piN m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero m)
        simp only [prodFactor, hσ'def, hm, ite_true]
        exact div_ne_zero (sub_ne_zero.mpr hu.symm) hc
      rw [hψ u, mul_div_cancel_left₀ _ hQu]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ heq
    exact (hdiff w).div (hQd w) hQ0
  · have hempty : {n : ℤ | σ' n = w} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      by_cases hn : n ∈ win N
      · have : σ' n = ρ := by simp [hσ'def, hn]
        rw [this] at h
        have := hρ; rw [h] at this; linarith
      · have : σ' n = σ n := by simp [hσ'def, hn]
        rw [this] at h
        have := hout n hn; rw [h] at this; linarith
    have h0 := hord w
    rw [hempty, Set.encard_empty] at h0
    have hne : psiProd σ' w ≠ 0 := by
      rcases analyticOrderAt_eq_zero.mp h0 with h | h
      · exact absurd (hdiff.analyticAt w) h
      · exact h
    intro h
    apply hne
    rw [hψ, h, mul_zero]

end

end NlsGge.GK38.Lib
