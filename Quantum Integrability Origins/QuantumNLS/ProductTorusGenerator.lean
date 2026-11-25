import QuantumNLS.HilbertL1Compact
import QuantumNLS.Ext025AFoundations

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T1: bounded angle generators and their product-topology continuity

Source: `chapters/global/product_torus.tex`, the setup (lines 9–20) and the proof sections "Bounded angle generators and
complete flows" (first two paragraphs) and "The product topology and full initial-point regularity" (first paragraph).

Setup (source): `H` a complex Hilbert space regarded as a real Hilbert space, `ω(h,k) = 2 Im⟪h,k⟫`,
`W v = ω(v,·)`, `X_F = W⁻¹ dF`, `{F,G} = dF[X_G]`. The inverse is the accepted GP-06 normalization
(`Ext025A.gp06_hamiltonian_normalization`): `W⁻¹ ℓ = −(i/2)·(Riesz vector of ℓ)`.

For a bounded real sequence `θ ∈ ℓ^∞(ℤ)` and a family of derivatives `DI : H → L(H, ℓ¹)` (later `DI = D𝓘`):
* `pair θ : ℓ¹ →L ℝ`, `x ↦ Σ θ_n x_n` (`‖pair θ‖ ≤ ‖θ‖_∞`), the source's "pairing with a bounded sequence";
* `X DI θ u = W⁻¹(θ ∘ D𝓘(u))` (the source's `X_θ`) and `Xn DI n u = W⁻¹(dI_n(u))` (`X_{I_n}`).

Proved here:
* `omega_Winv`, `norm_Winv`, `omega_antisymm`, `apply_Winv_antisymm` (`ℓ(W⁻¹m) = −m(W⁻¹ℓ)`);
* under the involution hypothesis `{I_n, I_j} = 0` (`Involutive`):
  `DI_Xn_zero` ("`D𝓘(u)X_{I_j}(u) = 0` as an element of `ℓ¹`"), `dH_Xn_zero` (`dH_θ[X_{I_j}] = 0`),
  `dIj_X_zero` (`dI_j[X_θ] = 0`, by antisymmetry), `DI_X_zero`, `dH_X_zero` (`dH_θ[X_η] = 0`);
* `X_add`, `X_smul`, `norm_X_le` (`‖X_θ(u)‖ ≤ ‖θ‖_∞‖D𝓘(u)‖/2`, the source's `‖X_θ(u)‖ ≤ (π/2)A₁` for `‖θ‖_∞ ≤ π`);
* **`pair_tendsto_uniform`** and **`X_tendsto_uniform`**: if `θ^j → θ` coordinatewise with `sup_j ‖θ^j‖_∞ ≤ R`, then
  `sup_{u ∈ 𝒞} ‖X_{θ^j}(u) − X_θ(u)‖ → 0` for every compact `𝒞` on which `D𝓘` is continuous (source: "truncate `D𝓘`
  uniformly in operator norm on `𝒞`, use coordinate convergence on that finite set, and then let the tail norm tend
  to zero"; R-1D98F7EC `tail_family_uniform`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Filter Topology InnerProductSpace
open scoped InnerProductSpace

noncomputable section

namespace QuantumNLS.ProductTorusGenerator

open _root_.HilbertL1Compact (L1 L1_summable L1_norm restrictFS restrictFS_apply tailCLM tailCLM_apply_coe
  tail_family_uniform)

/-- Bounded real sequences `ℓ^∞(ℤ)`. -/
abbrev Linf := lp (fun _ : ℤ => ℝ) ⊤

/-! ## 1. The `ℓ¹`–`ℓ^∞` pairing and the coordinates -/

lemma abs_apply_le (θ : Linf) (n : ℤ) : |θ n| ≤ ‖θ‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) ENNReal.top_ne_zero θ n
  rwa [Real.norm_eq_abs] at this

lemma abs_L1_apply_le (x : L1 ℝ) (n : ℤ) : |x n| ≤ ‖x‖ := by
  have := lp.norm_apply_le_norm (p := 1) one_ne_zero x n
  rwa [Real.norm_eq_abs] at this

lemma summable_pair (θ : Linf) (x : L1 ℝ) : Summable (fun n => θ n * x n) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((L1_summable x).mul_left ‖θ‖)
  rw [norm_mul, Real.norm_eq_abs (θ n)]
  exact mul_le_mul_of_nonneg_right (abs_apply_le θ n) (norm_nonneg _)

lemma pair_bound (θ : Linf) (x : L1 ℝ) : ‖∑' n, θ n * x n‖ ≤ ‖θ‖ * ‖x‖ := by
  have hs : Summable (fun n => ‖θ n * x n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((L1_summable x).mul_left ‖θ‖)
    rw [norm_mul, Real.norm_eq_abs (θ n)]
    exact mul_le_mul_of_nonneg_right (abs_apply_le θ n) (norm_nonneg _)
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  rw [L1_norm x, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) hs ((L1_summable x).mul_left ‖θ‖)
  rw [norm_mul, Real.norm_eq_abs (θ n)]
  exact mul_le_mul_of_nonneg_right (abs_apply_le θ n) (norm_nonneg _)

/-- The pairing `x ↦ Σ_n θ_n x_n` as a linear map. -/
def pairLin (θ : Linf) : L1 ℝ →ₗ[ℝ] ℝ where
  toFun x := ∑' n, θ n * x n
  map_add' x y := by
    simp only [lp.coeFn_add, Pi.add_apply, mul_add]
    exact (summable_pair θ x).tsum_add (summable_pair θ y)
  map_smul' c x := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring

/-- **Pairing with a bounded sequence**, a bounded linear functional on `ℓ¹` with `‖pair θ‖ ≤ ‖θ‖_∞`. -/
def pair (θ : Linf) : L1 ℝ →L[ℝ] ℝ := (pairLin θ).mkContinuous ‖θ‖ (pair_bound θ)

lemma pair_apply (θ : Linf) (x : L1 ℝ) : pair θ x = ∑' n, θ n * x n := rfl

lemma norm_pair_le (θ : Linf) : ‖pair θ‖ ≤ ‖θ‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _

lemma pair_add (θ η : Linf) : pair (θ + η) = pair θ + pair η := by
  ext x
  show ∑' n, (θ + η) n * x n = ∑' n, θ n * x n + ∑' n, η n * x n
  simp only [lp.coeFn_add, Pi.add_apply, add_mul]
  exact (summable_pair θ x).tsum_add (summable_pair η x)

lemma pair_smul (c : ℝ) (θ : Linf) : pair (c • θ) = c • pair θ := by
  ext x
  show ∑' n, (c • θ) n * x n = c * ∑' n, θ n * x n
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun n => by ring

lemma pair_sub (θ η : Linf) : pair (θ - η) = pair θ - pair η := by
  ext x
  show ∑' n, (θ - η) n * x n = ∑' n, θ n * x n - ∑' n, η n * x n
  simp only [lp.coeFn_sub, Pi.sub_apply, sub_mul]
  exact (summable_pair θ x).tsum_sub (summable_pair η x)

/-- The coordinate `x ↦ x_n` of `ℓ¹`. -/
def coordLin (n : ℤ) : L1 ℝ →ₗ[ℝ] ℝ where
  toFun x := x n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coord (n : ℤ) : L1 ℝ →L[ℝ] ℝ :=
  (coordLin n).mkContinuous 1 (fun x => by
    rw [one_mul, Real.norm_eq_abs]; exact abs_L1_apply_le x n)

lemma coord_apply (n : ℤ) (x : L1 ℝ) : coord n x = x n := rfl

lemma L1_ext {x y : L1 ℝ} (h : ∀ n, coord n x = coord n y) : x = y := by
  apply Subtype.ext
  funext n
  exact h n

/-- `pair δ y = Σ_{n ∈ S} δ_n y_n + pair δ ((1 − P_S) y)`. -/
lemma pair_split (δ : Linf) (S : Finset ℤ) (y : L1 ℝ) :
    pair δ y = ∑ n ∈ S, δ n * y n + pair δ (tailCLM S y) := by
  have h1 : pair δ y - pair δ (tailCLM S y) = pair δ (y - tailCLM S y) := (map_sub _ _ _).symm
  have h2 : pair δ (y - tailCLM S y) = ∑ n ∈ S, δ n * y n := by
    rw [pair_apply]
    have hc : ∀ n, (y - tailCLM S y : L1 ℝ) n = if n ∈ S then y n else 0 := by
      intro n
      rw [lp.coeFn_sub, Pi.sub_apply, tailCLM_apply_coe, restrictFS_apply]
      split_ifs <;> ring
    simp_rw [hc]
    rw [tsum_eq_sum (s := S) (fun n hn => by simp [hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [hn]
  linarith

/-! ## 2. The symplectic duality (GP-06 normalization) -/

section Symplectic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- `ω(h,k) = 2 Im⟪h,k⟫`. -/
def omega (h k : E) : ℝ := 2 * (inner ℂ h k).im

/-- `W⁻¹ℓ = −(i/2)·(Riesz vector of ℓ)`, the inverse of `W v = ω(v,·)` (GP-06). -/
def Winv (ℓ : E →L[ℝ] ℝ) : E := ((-Complex.I) / 2) • (toDual ℝ E).symm ℓ

theorem omega_Winv (ℓ : E →L[ℝ] ℝ) (w : E) : omega (Winv ℓ) w = ℓ w :=
  QuantumNLS.Ext025A.gp06_hamiltonian_normalization ℓ w

omit [CompleteSpace E] in
theorem omega_antisymm (h k : E) : omega h k = -omega k h := by
  unfold omega
  rw [← inner_conj_symm, Complex.conj_im]
  ring

/-- `ℓ(W⁻¹m) = −m(W⁻¹ℓ)`. -/
theorem apply_Winv_antisymm (ℓ m : E →L[ℝ] ℝ) : ℓ (Winv m) = -m (Winv ℓ) := by
  rw [← omega_Winv ℓ (Winv m), omega_antisymm, omega_Winv]

theorem norm_Winv (ℓ : E →L[ℝ] ℝ) : ‖Winv ℓ‖ = ‖ℓ‖ / 2 := by
  unfold Winv
  rw [norm_smul, LinearIsometryEquiv.norm_map]
  have : ‖(-Complex.I) / 2‖ = 1 / 2 := by simp
  rw [this]; ring

theorem Winv_add (ℓ m : E →L[ℝ] ℝ) : Winv (ℓ + m) = Winv ℓ + Winv m := by
  unfold Winv; rw [map_add, smul_add]

theorem Winv_sub (ℓ m : E →L[ℝ] ℝ) : Winv (ℓ - m) = Winv ℓ - Winv m := by
  unfold Winv; rw [map_sub, smul_sub]

theorem Winv_smul (c : ℝ) (ℓ : E →L[ℝ] ℝ) : Winv (c • ℓ) = c • Winv ℓ := by
  unfold Winv; rw [map_smul, smul_comm]

/-! ## 3. Bounded angle generators -/

/-- The source's `X_θ(u) = W⁻¹(θ ∘ D𝓘(u))`. -/
def X (DI : E → (E →L[ℝ] L1 ℝ)) (θ : Linf) (u : E) : E := Winv ((pair θ).comp (DI u))

/-- The source's `X_{I_n}(u) = W⁻¹ dI_n(u)`. -/
def Xn (DI : E → (E →L[ℝ] L1 ℝ)) (n : ℤ) (u : E) : E := Winv ((coord n).comp (DI u))

/-- The involution hypothesis `{I_n, I_j} = dI_n[X_{I_j}] = 0` for every `n, j` (source hypothesis 2). -/
def Involutive (DI : E → (E →L[ℝ] L1 ℝ)) : Prop := ∀ u n j, coord n (DI u (Xn DI j u)) = 0

variable {DI : E → (E →L[ℝ] L1 ℝ)}

/-- "Involution gives `D𝓘(u)X_{I_j}(u) = 0` as an element of `ℓ¹`." -/
theorem DI_Xn_zero (hinv : Involutive DI) (u : E) (j : ℤ) : DI u (Xn DI j u) = 0 :=
  L1_ext fun n => by rw [hinv u n j, map_zero]

/-- `dH_θ[X_{I_j}] = 0`. -/
theorem dH_Xn_zero (hinv : Involutive DI) (θ : Linf) (u : E) (j : ℤ) : pair θ (DI u (Xn DI j u)) = 0 := by
  rw [DI_Xn_zero hinv u j, map_zero]

/-- `dI_j[X_θ] = 0` (antisymmetry). -/
theorem dIj_X_zero (hinv : Involutive DI) (θ : Linf) (u : E) (j : ℤ) : coord j (DI u (X DI θ u)) = 0 := by
  have h := apply_Winv_antisymm ((coord j).comp (DI u)) ((pair θ).comp (DI u))
  rw [ContinuousLinearMap.comp_apply] at h
  unfold X
  rw [h, ContinuousLinearMap.comp_apply]
  change -(pair θ (DI u (Xn DI j u))) = 0
  rw [dH_Xn_zero hinv θ u j, neg_zero]

theorem DI_X_zero (hinv : Involutive DI) (θ : Linf) (u : E) : DI u (X DI θ u) = 0 :=
  L1_ext fun n => by rw [dIj_X_zero hinv θ u n, map_zero]

/-- `dH_η[X_θ] = 0` for any two bounded sequences. -/
theorem dH_X_zero (hinv : Involutive DI) (θ η : Linf) (u : E) : pair η (DI u (X DI θ u)) = 0 := by
  rw [DI_X_zero hinv θ u, map_zero]

theorem X_add (θ η : Linf) (u : E) : X DI (θ + η) u = X DI θ u + X DI η u := by
  unfold X; rw [pair_add, ContinuousLinearMap.add_comp, Winv_add]

theorem X_sub (θ η : Linf) (u : E) : X DI (θ - η) u = X DI θ u - X DI η u := by
  unfold X; rw [pair_sub, ContinuousLinearMap.sub_comp, Winv_sub]

theorem X_smul (c : ℝ) (θ : Linf) (u : E) : X DI (c • θ) u = c • X DI θ u := by
  unfold X; rw [pair_smul, ContinuousLinearMap.smul_comp, Winv_smul]

/-- `‖X_θ(u)‖ ≤ ‖θ‖_∞‖D𝓘(u)‖/2`. -/
theorem norm_X_le (θ : Linf) (u : E) : ‖X DI θ u‖ ≤ ‖θ‖ * ‖DI u‖ / 2 := by
  unfold X
  rw [norm_Winv]
  have := (ContinuousLinearMap.opNorm_comp_le (pair θ) (DI u)).trans
    (mul_le_mul_of_nonneg_right (norm_pair_le θ) (norm_nonneg _))
  linarith

end Symplectic

/-! ## 4. Coordinatewise convergence of bounded angles: uniform convergence on compact operator families -/

section Uniform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- **Uniform convergence of the pairings on a compact family of `H → ℓ¹` operators**: if `θ^j → θ` coordinatewise
and `‖θ^j‖_∞, ‖θ‖_∞ ≤ R`, then `sup_{A ∈ 𝒜} ‖pair(θ^j − θ) ∘ A‖ → 0` for a norm-compact family `𝒜`. -/
theorem pair_tendsto_uniform (𝒜 : Set (E →L[ℝ] L1 ℝ)) (hcomp : IsCompact 𝒜) (θs : ℕ → Linf) (θ : Linf) {R : ℝ}
    (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R) (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n))) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ A ∈ 𝒜, ‖(pair (θs j - θ)).comp A‖ ≤ ε := by
  intro ε hε
  have hR0 : 0 ≤ R := (norm_nonneg _).trans hθR
  obtain ⟨M, hM⟩ := hcomp.isBounded.exists_norm_le
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hAM : ∀ A ∈ 𝒜, ‖A‖ ≤ M' := fun A hA => (hM A hA).trans (le_max_left _ _)
  -- the exhausting finite sets
  set S : ℕ → Finset ℤ := fun N => Finset.Icc (-(N : ℤ)) N with hS
  have hSm : Monotone S := fun a b hab => Finset.Icc_subset_Icc (by omega) (by omega)
  have hexh : ∀ m : ℤ, ∃ N, m ∈ S N := fun m => ⟨m.natAbs, by
    simp only [hS, Finset.mem_Icc]; omega⟩
  obtain ⟨N₀, hN₀⟩ := tail_family_uniform (𝕜 := ℝ) 𝒜 hcomp S hSm hexh (ε / (2 * (2 * R + 1)))
    (by positivity)
  have htail : ∀ A ∈ 𝒜, ‖(tailCLM (S N₀)).comp A‖ ≤ ε / (2 * (2 * R + 1)) := fun A hA => hN₀ N₀ le_rfl A hA
  -- coordinate convergence on the finite set `S N₀`
  set η : ℝ := ε / (2 * ((S N₀).card + 1) * (M' + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hfin : ∀ᶠ j in atTop, ∀ n ∈ S N₀, |θs j n - θ n| ≤ η := by
    rw [Filter.eventually_all_finset]
    intro n _
    have := (hcoord n).sub_const (θ n)
    rw [sub_self] at this
    filter_upwards [this.eventually (Metric.closedBall_mem_nhds 0 hη0)] with j hj
    rw [Real.dist_eq, sub_zero] at hj
    exact hj
  filter_upwards [hfin] with j hj
  intro A hA
  refine ContinuousLinearMap.opNorm_le_bound _ hε.le fun x => ?_
  rw [ContinuousLinearMap.comp_apply, pair_split (θs j - θ) (S N₀) (A x)]
  have hδ : ‖θs j - θ‖ ≤ 2 * R := by
    have := norm_sub_le (θs j) θ; linarith [hR j]
  have hAx : ‖A x‖ ≤ M' * ‖x‖ := (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right (hAM A hA) (norm_nonneg _))
  have h1 : ‖∑ n ∈ S N₀, (θs j - θ) n * (A x) n‖ ≤ ε / 2 * ‖x‖ := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ n ∈ S N₀, ‖(θs j - θ) n * (A x) n‖ ≤ ∑ _n ∈ S N₀, η * (M' * ‖x‖) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, lp.coeFn_sub, Pi.sub_apply]
          exact mul_le_mul (hj n hn) ((abs_L1_apply_le (A x) n).trans hAx) (abs_nonneg _) hη0.le
      _ = (S N₀).card * η * M' * ‖x‖ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ε / 2 * ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hη]
          have hc : (0 : ℝ) ≤ (S N₀).card := Nat.cast_nonneg _
          rw [show ((S N₀).card : ℝ) * (ε / (2 * ((S N₀).card + 1) * (M' + 1))) * M' =
            ε / 2 * (((S N₀).card / ((S N₀).card + 1)) * (M' / (M' + 1))) by field_simp]
          have ha : ((S N₀).card : ℝ) / ((S N₀).card + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith
          have hb : M' / (M' + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          have hab : ((S N₀).card : ℝ) / ((S N₀).card + 1) * (M' / (M' + 1)) ≤ 1 :=
            (mul_le_mul ha hb (by positivity) zero_le_one).trans (le_of_eq (one_mul 1))
          nlinarith
  have h2 : ‖pair (θs j - θ) (tailCLM (S N₀) (A x))‖ ≤ ε / 2 * ‖x‖ := by
    have hp := (pair (θs j - θ)).le_opNorm (tailCLM (S N₀) (A x))
    have ht : ‖tailCLM (S N₀) (A x)‖ ≤ ε / (2 * (2 * R + 1)) * ‖x‖ := by
      have := ((tailCLM (S N₀)).comp A).le_opNorm x
      rw [ContinuousLinearMap.comp_apply] at this
      exact this.trans (mul_le_mul_of_nonneg_right (htail A hA) (norm_nonneg _))
    calc ‖pair (θs j - θ) (tailCLM (S N₀) (A x))‖ ≤ ‖pair (θs j - θ)‖ * ‖tailCLM (S N₀) (A x)‖ := hp
      _ ≤ (2 * R) * (ε / (2 * (2 * R + 1)) * ‖x‖) :=
          mul_le_mul ((norm_pair_le _).trans hδ) ht (norm_nonneg _) (by positivity)
      _ = ε / 2 * ‖x‖ * (2 * R / (2 * R + 1)) := by field_simp
      _ ≤ ε / 2 * ‖x‖ := by
          have : 2 * R / (2 * R + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          have h0 : 0 ≤ ε / 2 * ‖x‖ := by positivity
          nlinarith
  calc ‖∑ n ∈ S N₀, (θs j - θ) n * (A x) n + pair (θs j - θ) (tailCLM (S N₀) (A x))‖ ≤
        ‖∑ n ∈ S N₀, (θs j - θ) n * (A x) n‖ + ‖pair (θs j - θ) (tailCLM (S N₀) (A x))‖ := norm_add_le _ _
    _ ≤ ε / 2 * ‖x‖ + ε / 2 * ‖x‖ := add_le_add h1 h2
    _ = ε * ‖x‖ := by ring

/-- **The generators converge uniformly on compact sets** (source: "Suppose `θ^j → θ` coordinatewise, with
`sup_j ‖θ^j‖_∞ ≤ R < ∞`. For a compact `𝒞` ..., `sup_{u∈𝒞} ‖X_{θ^j}(u) − X_θ(u)‖ → 0`"). -/
theorem X_tendsto_uniform (DI : E → (E →L[ℝ] L1 ℝ)) (C : Set E) (hC : IsCompact C) (hDI : ContinuousOn DI C)
    (θs : ℕ → Linf) (θ : Linf) {R : ℝ} (hR : ∀ j, ‖θs j‖ ≤ R) (hθR : ‖θ‖ ≤ R)
    (hcoord : ∀ n, Tendsto (fun j => θs j n) atTop (𝓝 (θ n))) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ u ∈ C, ‖X DI (θs j) u - X DI θ u‖ ≤ ε := by
  intro ε hε
  filter_upwards [pair_tendsto_uniform (DI '' C) (hC.image_of_continuousOn hDI) θs θ hR hθR hcoord (2 * ε)
    (by positivity)] with j hj
  intro u hu
  rw [← X_sub]
  unfold X
  rw [norm_Winv]
  have := hj (DI u) ⟨u, hu, rfl⟩
  linarith

end Uniform

end QuantumNLS.ProductTorusGenerator

#print axioms QuantumNLS.ProductTorusGenerator.pair_split
#print axioms QuantumNLS.ProductTorusGenerator.apply_Winv_antisymm
#print axioms QuantumNLS.ProductTorusGenerator.dIj_X_zero
#print axioms QuantumNLS.ProductTorusGenerator.dH_X_zero
#print axioms QuantumNLS.ProductTorusGenerator.norm_X_le
#print axioms QuantumNLS.ProductTorusGenerator.pair_tendsto_uniform
#print axioms QuantumNLS.ProductTorusGenerator.X_tendsto_uniform
