import NlsGge.GK38.Lib.EntireProductsParam
import NlsGge.GK38.Lib.Interpolation

/-!
# L4c part 2b, module a: ratio products and the circle bound for `f_n`

Plan section 6.1, piece L4c part 2b; Grébert–Kappeler book, Appendix C (Lemma C.3, C.4, and the
growth estimate of Lemma C.5 for the omitted-factor product).

* `Dn n = {|λ - nπ| < π/4}` (the book's `D_n`), `sincAt n λ` (`sin λ / (λ - nπ)`, with the value
  `cos nπ` at `λ = nπ`).
* `ratioFam σ ρ n λ m = if m = n then 1 else (σ_m - λ)/(ρ_m - λ)` and `ratioProd`: the product
  `∏_{m ≠ n} (σ_m - λ)/(ρ_m - λ)` of Lemma C.3.
* `omitProd_eq_ratio`: `f_n(λ, σ̃) = f_n(λ, 0) · ∏_{m≠n} (σ_m - λ)/(mπ - λ)` for `λ ∉ {mπ : m ≠ n}`
  (the identity at the start of the proof of Lemma C.4).
* The circle bound (the content that P4's Interpolation-Lemma step needs, review N2b): for
  `‖σ̃‖ ≤ K`, `‖z‖ = Nπ + π/2`: `‖f_n(z, σ̃)‖ · ‖z - nπ‖ ≤ C ‖sin z‖` with `C = exp(K √(2K₀)/π)` uniform in
  `n`, `N` and `σ̃`.  Corollaries: `O(1)` growth `‖f_n‖ ≤ (2C/π) ‖sin z‖` (the plan's
  `omitProd_circle_bound`) and the `o(1)` form for each fixed `n` (the form which Lemma F.4 =
  `interpolation_lemma` actually needs, after the L4b review).
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-- The book's `D_n = {λ : |λ - nπ| < π/4}`. -/
def Dn (n : ℤ) : Set ℂ := Metric.ball ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 4)

/-- `sin λ / (λ - nπ)`, continuously extended by `cos nπ` at `λ = nπ`. -/
def sincAt (n : ℤ) (lam : ℂ) : ℂ :=
  if lam = (n : ℂ) * (Real.pi : ℂ) then (Real.cos ((n : ℝ) * Real.pi) : ℂ)
  else Complex.sin lam / (lam - (n : ℂ) * (Real.pi : ℂ))

/-- The factor family of Lemma C.3: `1` at `m = n`, `(σ_m - λ)/(ρ_m - λ)` otherwise. -/
def ratioFam (σ ρ : ℤ → ℂ) (n : ℤ) (lam : ℂ) (m : ℤ) : ℂ :=
  if m = n then 1 else (σ m - lam) / (ρ m - lam)

/-- The product `∏_{m ≠ n} (σ_m - λ)/(ρ_m - λ)` (symmetric limit). -/
def ratioProd (σ ρ : ℤ → ℂ) (n : ℤ) (lam : ℂ) : ℂ :=
  ∏'[symmetricIcc ℤ] m : ℤ, ratioFam σ ρ n lam m

/-- The perturbation `ratioFam = 1 + ratioU`. -/
def ratioU (σ ρ : ℤ → ℂ) (n : ℤ) (lam : ℂ) (m : ℤ) : ℂ :=
  if m = n then 0 else (σ m - ρ m) / (ρ m - lam)

theorem ratioFam_eq_one_add {σ ρ : ℤ → ℂ} {n : ℤ} {lam : ℂ} (hne : ∀ m, m ≠ n → ρ m ≠ lam) (m : ℤ) :
    ratioFam σ ρ n lam m = 1 + ratioU σ ρ n lam m := by
  unfold ratioFam ratioU
  by_cases h : m = n
  · simp [h]
  · have h1 : ρ m - lam ≠ 0 := sub_ne_zero.mpr (hne m h)
    simp only [h, ite_false]
    field_simp
    ring

theorem sigmaOf_zero_eq : sigmaOf (0 : L2Seq) = sigmaZero := by
  funext n; simp [sigmaOf, sigmaZero]

/-! ### `f_n(λ, 0) = sinc` (book (C.1) with one factor removed) -/

theorem entProdJ_zero (z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf (0 : L2Seq)) z m = -Complex.sin z := by
  simp only [sigmaOf_zero_eq]
  exact (hasProd_sinProd z).tprod_eq

/-- `f_n(z, 0) = -sin z / (nπ - z)` off the lattice point. -/
theorem omitProd_zero_of_ne (n : ℤ) {z : ℂ} (hz : (n : ℂ) * (Real.pi : ℂ) ≠ z) :
    omitProd n 0 z = -Complex.sin z / ((n : ℂ) * (Real.pi : ℂ) - z) := by
  have h := entProd_eq_mul_omitProd n 0 z
  rw [entProdJ_zero] at h
  have hne : (n : ℂ) * (Real.pi : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
  rw [eq_div_iff hne]
  simp only [sigmaOf, lp.coeFn_zero, Pi.zero_apply, add_zero] at h
  linear_combination -h

/-- `f_n(nπ, 0) = cos nπ`: derivative of the sine product at its root. -/
theorem omitProd_zero_at_root (n : ℤ) :
    omitProd n 0 ((n : ℂ) * (Real.pi : ℂ)) = Complex.cos ((n : ℂ) * (Real.pi : ℂ)) := by
  have hn : sigmaOf (0 : L2Seq) n = (n : ℂ) * (Real.pi : ℂ) := by simp [sigmaOf_zero_eq, sigmaZero]
  have h1 := hasDerivAt_entProd_root n 0
  rw [hn] at h1
  have e : (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf (0 : L2Seq)) z m)
      = fun z => -Complex.sin z := funext entProdJ_zero
  rw [e] at h1
  have h2 : HasDerivAt (fun z : ℂ => -Complex.sin z) (-Complex.cos ((n : ℂ) * (Real.pi : ℂ)))
      ((n : ℂ) * (Real.pi : ℂ)) := (Complex.hasDerivAt_sin _).neg
  exact neg_injective (h1.unique h2)

/-- `f_n(λ, 0) = sincAt n λ` for every `λ`. -/
theorem omitProd_zero_eq_sincAt (n : ℤ) (lam : ℂ) : omitProd n 0 lam = sincAt n lam := by
  unfold sincAt
  by_cases h : lam = (n : ℂ) * (Real.pi : ℂ)
  · rw [h, omitProd_zero_at_root]
    simp only [ite_true]
    rw [Complex.ofReal_cos]
    push_cast
    rfl
  · simp only [h, ite_false]
    rw [omitProd_zero_of_ne n (Ne.symm h)]
    have : (n : ℂ) * (Real.pi : ℂ) - lam ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have h' : lam - (n : ℂ) * (Real.pi : ℂ) ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

/-! ### The factorisation `f_n(λ, σ̃) = f_n(λ, 0) · ratio` -/

/-- **Start of the proof of Lemma C.4.**  If `mπ ≠ λ` for all `m ≠ n` and the ratio family is
multipliable, `f_n(λ, σ̃) = f_n(λ, 0) ∏_{m≠n} (σ_m - λ)/(mπ - λ)`. -/
theorem omitProd_eq_ratio (n : ℤ) (s : L2Seq) {z : ℂ}
    (hz : ∀ m : ℤ, m ≠ n → (m : ℂ) * (Real.pi : ℂ) ≠ z)
    (hm : Multipliable (ratioFam (sigmaOf s) sigmaZero n z) (symmetricIcc ℤ)) :
    omitProd n s z = omitProd n 0 z * ratioProd (sigmaOf s) sigmaZero n z := by
  have hG := multipliable_omit n (0 : L2Seq) z
  have hGR := hG.hasProd.mul hm.hasProd
  have hfun : (fun m : ℤ => (if m = n then (1 : ℂ) else prodFactor (sigmaOf (0 : L2Seq)) z m)
        * ratioFam (sigmaOf s) sigmaZero n z m)
      = fun m : ℤ => if m = n then 1 else prodFactor (sigmaOf s) z m := by
    funext m
    unfold ratioFam
    by_cases h : m = n
    · simp [h]
    · simp only [h, ite_false]
      have h1 : sigmaZero m - z ≠ 0 := sub_ne_zero.mpr (hz m h)
      have h2 : (piN m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (piN_ne_zero m)
      simp only [prodFactor, sigmaOf_zero_eq]
      field_simp
  rw [hfun] at hGR
  unfold omitProd ratioProd
  rw [hGR.tprod_eq]
  ring

/-! ### Cauchy–Schwarz for `ℓ²` sequences -/

theorem cs_tsum {f g : ℤ → ℝ} (hf0 : ∀ m, 0 ≤ f m) (hg0 : ∀ m, 0 ≤ g m)
    (hf : Summable fun m => f m ^ 2) (hg : Summable fun m => g m ^ 2) :
    Summable (fun m => f m * g m) ∧
      ∑' m, f m * g m ≤ Real.sqrt (∑' m, f m ^ 2) * Real.sqrt (∑' m, g m ^ 2) := by
  have hfin : ∀ s : Finset ℤ, ∑ m ∈ s, f m * g m
      ≤ Real.sqrt (∑' m, f m ^ 2) * Real.sqrt (∑' m, g m ^ 2) := by
    intro s
    refine (Real.sum_mul_le_sqrt_mul_sqrt s f g).trans ?_
    refine mul_le_mul (Real.sqrt_le_sqrt ?_) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    · exact hf.sum_le_tsum s fun _ _ => sq_nonneg _
    · exact hg.sum_le_tsum s fun _ _ => sq_nonneg _
  have h0 : ∀ m, 0 ≤ f m * g m := fun m => mul_nonneg (hf0 m) (hg0 m)
  exact ⟨summable_of_sum_le h0 hfin, Real.tsum_le_of_sum_le h0 hfin⟩

/-- `∑' ‖s m‖² = ‖s‖²` for `s ∈ ℓ²`. -/
theorem tsum_sq_l2 (s : L2Seq) : ∑' m : ℤ, ‖s m‖ ^ 2 = ‖s‖ ^ 2 := (hasSum_sq_l2 s).tsum_eq

/-! ### The circle bound -/

theorem ratioU_norm_le_circle {s : L2Seq} {n : ℤ} {N : ℕ} {z : ℂ}
    (hz : ‖z‖ = N * Real.pi + Real.pi / 2) (m : ℤ) :
    ‖ratioU (sigmaOf s) sigmaZero n z m‖ ≤ (1 / Real.pi) * (‖s m‖ * (1 / circDist N m)) := by
  unfold ratioU
  have hpi := Real.pi_pos
  by_cases h : m = n
  · simp only [h, ite_true, norm_zero]
    have := circDist_pos N n
    positivity
  · simp only [h, ite_false]
    have e : sigmaOf s m - sigmaZero m = s m := by simp [sigmaOf, sigmaZero]
    rw [e, norm_div]
    have hd := pi_mul_dd_le hz m
    have hdd := circDist_pos N m
    have hnn : ‖sigmaZero m - z‖ = ‖(m : ℂ) * (Real.pi : ℂ) - z‖ := rfl
    rw [hnn]
    calc ‖s m‖ / ‖(m : ℂ) * (Real.pi : ℂ) - z‖ ≤ ‖s m‖ / (Real.pi * circDist N m) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hpi hdd) hd
      _ = (1 / Real.pi) * (‖s m‖ * (1 / circDist N m)) := by field_simp

/-- The constant `S₀(K) = K √(2 K₀)/π` bounding `Σ_m ‖ratioU‖` on the circles. -/
def circS (K : ℝ) : ℝ := K * Real.sqrt (2 * halfInvSqSum) / Real.pi

theorem circS_nonneg {K : ℝ} (hK : 0 ≤ K) : 0 ≤ circS K := by
  unfold circS; have := Real.pi_pos; positivity

theorem summable_ratioU_circle {s : L2Seq} {n : ℤ} {N : ℕ} {z : ℂ}
    (hz : ‖z‖ = N * Real.pi + Real.pi / 2) :
    Summable (fun m => ‖ratioU (sigmaOf s) sigmaZero n z m‖) ∧
      ∑' m, ‖ratioU (sigmaOf s) sigmaZero n z m‖ ≤ circS ‖s‖ := by
  have hpi := Real.pi_pos
  have hsq : Summable fun m : ℤ => ‖s m‖ ^ 2 := (hasSum_sq_l2 s).summable
  have hgs : Summable fun m : ℤ => (1 / circDist N m) ^ 2 := by
    refine (summable_inv_circDist_sq N).congr fun m => ?_
    rw [div_pow, one_pow]
  obtain ⟨hs1, hs2⟩ := cs_tsum (f := fun m => ‖s m‖) (g := fun m => 1 / circDist N m)
    (fun _ => norm_nonneg _) (fun m => by have := circDist_pos N m; positivity) hsq hgs
  have hb : Summable fun m : ℤ => (1 / Real.pi) * (‖s m‖ * (1 / circDist N m)) := hs1.mul_left _
  have hsm := hb.of_nonneg_of_le (fun _ => norm_nonneg _) (ratioU_norm_le_circle (s := s) (n := n) hz)
  refine ⟨hsm, ?_⟩
  calc ∑' m, ‖ratioU (sigmaOf s) sigmaZero n z m‖
      ≤ ∑' m : ℤ, (1 / Real.pi) * (‖s m‖ * (1 / circDist N m)) :=
        hsm.tsum_le_tsum (ratioU_norm_le_circle hz) hb
    _ = (1 / Real.pi) * ∑' m : ℤ, ‖s m‖ * (1 / circDist N m) := tsum_mul_left
    _ ≤ (1 / Real.pi) * (Real.sqrt (∑' m, ‖s m‖ ^ 2) * Real.sqrt (∑' m : ℤ, (1 / circDist N m) ^ 2)) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
    _ ≤ circS ‖s‖ := by
        rw [tsum_sq_l2, Real.sqrt_sq (norm_nonneg _)]
        have h3 : Real.sqrt (∑' m : ℤ, (1 / circDist N m) ^ 2) ≤ Real.sqrt (2 * halfInvSqSum) := by
          refine Real.sqrt_le_sqrt ?_
          refine le_trans (le_of_eq ?_) (tsum_inv_circDist_sq_le N)
          exact tsum_congr fun m => by rw [div_pow, one_pow]
        unfold circS
        calc (1 / Real.pi) * (‖s‖ * Real.sqrt (∑' m : ℤ, (1 / circDist N m) ^ 2))
            ≤ (1 / Real.pi) * (‖s‖ * Real.sqrt (2 * halfInvSqSum)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)) (by positivity)
          _ = ‖s‖ * Real.sqrt (2 * halfInvSqSum) / Real.pi := by ring

theorem circle_no_lattice {N : ℕ} {z : ℂ} (hz : ‖z‖ = N * Real.pi + Real.pi / 2) (m : ℤ) :
    (m : ℂ) * (Real.pi : ℂ) ≠ z := by
  intro h
  have h1 := pi_mul_dd_le hz m
  rw [h, sub_self, norm_zero] at h1
  have := mul_pos Real.pi_pos (circDist_pos N m)
  linarith

theorem multipliable_ratioFam_circle {s : L2Seq} {n : ℤ} {N : ℕ} {z : ℂ}
    (hz : ‖z‖ = N * Real.pi + Real.pi / 2) :
    Multipliable (ratioFam (sigmaOf s) sigmaZero n z) (symmetricIcc ℤ) := by
  have hne : ∀ m, m ≠ n → sigmaZero m ≠ z := fun m _ => circle_no_lattice hz m
  have e : ratioFam (sigmaOf s) sigmaZero n z = fun m => 1 + ratioU (sigmaOf s) sigmaZero n z m :=
    funext (ratioFam_eq_one_add hne)
  rw [e]
  exact HasProd.multipliable ((multipliable_one_add_of_summable (summable_ratioU_circle hz).1).hasProd.mono_left
    (symmetricIcc ℤ).le_atTop)

theorem norm_ratioProd_circle_le {s : L2Seq} {n : ℤ} {N : ℕ} {z : ℂ}
    (hz : ‖z‖ = N * Real.pi + Real.pi / 2) :
    ‖ratioProd (sigmaOf s) sigmaZero n z‖ ≤ Real.exp (circS ‖s‖) := by
  have hne : ∀ m, m ≠ n → sigmaZero m ≠ z := fun m _ => circle_no_lattice hz m
  have e : ratioFam (sigmaOf s) sigmaZero n z = fun m => 1 + ratioU (sigmaOf s) sigmaZero n z m :=
    funext (ratioFam_eq_one_add hne)
  obtain ⟨h1, h2⟩ := summable_ratioU_circle (s := s) (n := n) hz
  unfold ratioProd
  rw [e, tprod_symm_eq_tprod_of_summable h1]
  exact (norm_tprod_one_add_le h1).trans (Real.exp_le_exp.mpr h2)

/-- **Growth of the omitted product on the circles `‖z‖ = Nπ + π/2`** (uniform in `n`, `N`, `σ̃`):
`‖f_n(z, σ̃)‖ · ‖z - nπ‖ ≤ exp(K √(2K₀)/π) ‖sin z‖` for `‖σ̃‖ ≤ K`. -/
theorem omitProd_circle_bound_dist (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : L2Seq, ‖s‖ ≤ K → ∀ (n : ℤ) (N : ℕ) (z : ℂ),
      ‖z‖ = N * Real.pi + Real.pi / 2 →
        ‖omitProd n s z‖ * ‖z - (n : ℂ) * (Real.pi : ℂ)‖ ≤ C * ‖Complex.sin z‖ := by
  refine ⟨Real.exp (circS (max K 0)), Real.exp_pos _, fun s hs n N z hz => ?_⟩
  have hne : ∀ m, m ≠ n → (m : ℂ) * (Real.pi : ℂ) ≠ z := fun m _ => circle_no_lattice hz m
  rw [omitProd_eq_ratio n s hne (multipliable_ratioFam_circle hz),
    omitProd_zero_of_ne n (circle_no_lattice hz n), norm_mul, norm_div, norm_neg]
  have hn : ‖(n : ℂ) * (Real.pi : ℂ) - z‖ = ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := norm_sub_rev _ _
  have hpos : 0 < ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr (circle_no_lattice hz n).symm
  rw [hn]
  have hR := norm_ratioProd_circle_le (s := s) (n := n) hz
  have hmono : circS ‖s‖ ≤ circS (max K 0) := by
    unfold circS
    have := Real.pi_pos
    have hk : ‖s‖ ≤ max K 0 := hs.trans (le_max_left _ _)
    gcongr
  have hR' := hR.trans (Real.exp_le_exp.mpr hmono)
  calc ‖Complex.sin z‖ / ‖z - (n : ℂ) * (Real.pi : ℂ)‖ * ‖ratioProd (sigmaOf s) sigmaZero n z‖
        * ‖z - (n : ℂ) * (Real.pi : ℂ)‖
      = ‖Complex.sin z‖ * ‖ratioProd (sigmaOf s) sigmaZero n z‖ := by field_simp
    _ ≤ ‖Complex.sin z‖ * Real.exp (circS (max K 0)) :=
        mul_le_mul_of_nonneg_left hR' (norm_nonneg _)
    _ = Real.exp (circS (max K 0)) * ‖Complex.sin z‖ := by ring

end

end NlsGge.GK38.Lib
