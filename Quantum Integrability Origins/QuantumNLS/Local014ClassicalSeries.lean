import QuantumNLS.Local014IteratedSymbol
import QuantumNLS.IntrinsicContact

/-!
# LOCAL-014 stage E5: the classical series `b(phi^t v) = Σ_k (t^k/k!) ad_h^k b(v)`

Source: `source-text/chapters/local/quantum_periods.tex:248-256` (proof of LOCAL-014): "The resulting
classical series equals `b(phi^t v)` ... For clarity, `h` is analytic with bounded derivatives on a
larger norm ball. The Banach-space Picard construction, complexified in `v, v̄`, gives an analytic
solution for sufficiently small complex time. Differentiating `b(phi^t v)` at zero successively gives
these same iterated brackets. Both convergent series therefore agree on a sufficiently small real
interval. Shrink the previously chosen short time if needed; its size is uniform for unit vectors."
and line 260 ("norm conservation").

Realization. The flow is a hypothesis (any solution curve `phi` of `phi' = X_h(phi)`, DEF-015
`hamField`). The identification of the two series is proved along the real solution curve:
* `hasFDerivAt_symbol`: symbols of radius-`R` kernel families are real-Fréchet differentiable on
  `‖u‖² < R` (termwise, `hasFDerivAt_tsum_of_isPreconnected`, frozen derivative bounds);
* `pbC_ofReal`, `hasDerivAt_comp_flow`: along the flow of a real `h`, `d/ds g(phi s) = {g, h}(phi s)`
  ("differentiating `b(phi^t v)` successively gives these same iterated brackets");
* `kps_phase`, `symbol_phase`, `re_inner_hamField`, `norm_flow_const`: gauge invariance of symbols
  and norm conservation along the flow ("norm conservation");
* `taylor_bound`: Taylor remainder `‖G_0(t) − Σ_{k<n} (t^k/k!) G_k(0)‖ ≤ M_n |t|^n/n!` for a chain
  `G_k' = G_{k+1}` with `|G_n| ≤ M_n` between `0` and `t` (both time directions);
* `classical_hasSum`: if `|ad_h^k b| ≤ (Kk)^k C` on the unit sphere (E2 `norm_symbol_iterLim_le`)
  and `eK|t| < 1`, then `Σ_k (t^k/k!) ad_h^k b(v) = b(phi^t v)`, uniformly for unit `v`.

Argument-correspondence note for review: the printed justification of the agreement of the two
series is analyticity of `t ↦ b(phi^t v)` (complexified Picard, GP-04); here the agreement is
obtained from the same successive differentiation plus the Taylor remainder bounded by the same
Dyson majorant `(Kk)^k 4^q‖B‖` carried by the iterated symbols (E2), which gives convergence on the
same short interval `|t| < (eK)^{-1}` without a separate analytic-radius argument. GP-04 is not used.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open scoped InnerProductSpace BigOperators Nat
open Filter Topology Finset
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.KernelConvergence
  QuantumNLS.SymplecticBracket QuantumNLS.Local013CommutatorSeries

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.Local014ClassicalSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## 1. Differentiability of symbols -/

theorem hasFDerivAt_symbol {L : ∀ p : ℕ, BoundedSymmetricKernel H p} {R : ℝ}
    (hL : Summable fun p => R ^ p * ‖L p‖) {u : H} (hu : ‖u‖ ^ 2 < R) :
    HasFDerivAt (symbol L) (∑' n, fderiv ℝ (kernelProductSymbol (L n)) u) u := by
  have hR : 0 < R := lt_of_le_of_lt (by positivity) hu
  set s0 := Real.sqrt R with hs0
  have hus : ‖u‖ < s0 := (Real.lt_sqrt (norm_nonneg u)).2 hu
  have hs00 : 0 ≤ s0 := Real.sqrt_nonneg R
  set σ := (‖u‖ + s0) / 2 with hσdef
  have huσ : ‖u‖ < σ := by rw [hσdef]; linarith
  have hσs : σ < s0 := by rw [hσdef]; linarith
  have hσ0 : 0 ≤ σ := (norm_nonneg u).trans huσ.le
  have hσR : σ ^ 2 < R := by
    have h1 : σ ^ 2 < s0 ^ 2 := by nlinarith
    rwa [hs0, Real.sq_sqrt hR.le] at h1
  have hsum := summable_deriv_bound hσ0 hσR L hL
  have hf0 : Summable fun n => kernelProductSymbol (L n) (0 : H) := by
    refine Summable.of_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hL)
    exact norm_kps_le_radius (L n) (by simpa using hR.le)
  show HasFDerivAt (fun y => ∑' n, kernelProductSymbol (L n) y) _ u
  exact hasFDerivAt_tsum_of_isPreconnected hsum Metric.isOpen_ball
    (convex_ball (0 : H) σ).isPreconnected (fun n x _ => hasFDerivAt_kps (L n) x)
    (fun n x hx => norm_fderiv_kps_le (L n) x (mem_ball_zero_iff.1 hx).le)
    (Metric.mem_ball_self ((norm_nonneg u).trans_lt huσ)) hf0 (mem_ball_zero_iff.2 huσ)

theorem differentiableAt_symbol {L : ∀ p : ℕ, BoundedSymmetricKernel H p} {R : ℝ}
    (hL : Summable fun p => R ^ p * ‖L p‖) {u : H} (hu : ‖u‖ ^ 2 < R) :
    DifferentiableAt ℝ (symbol L) u :=
  (hasFDerivAt_symbol hL hu).differentiableAt

/-! ## 2. Derivative along the flow of a real Hamiltonian -/

theorem hamField_zero (u : H) : hamField (fun _ : H => (0 : ℝ)) u = 0 := by
  simp [hamField, SymplecticBracket.gradient]

/-- For real `h`, the complex bracket is the derivative along `X_h`: `{g, h}(u) = dg(u)[X_h(u)]`. -/
theorem pbC_ofReal (g : H → ℂ) (hr : H → ℝ) {u : H} (hg : DifferentiableAt ℝ g u) :
    pbC g (fun v => (hr v : ℂ)) u = fderiv ℝ g u (hamField hr u) := by
  have hre : HasFDerivAt (fun v => (g v).re) (Complex.reCLM.comp (fderiv ℝ g u)) u :=
    Complex.reCLM.hasFDerivAt.comp u hg.hasFDerivAt
  have him : HasFDerivAt (fun v => (g v).im) (Complex.imCLM.comp (fderiv ℝ g u)) u :=
    Complex.imCLM.hasFDerivAt.comp u hg.hasFDerivAt
  unfold pbC pbR
  simp only [Complex.ofReal_re, Complex.ofReal_im, hamField_zero, map_zero, sub_zero, add_zero]
  rw [hre.fderiv, him.fderiv]
  apply Complex.ext <;> simp

/-- Chain rule along a solution curve of `phi' = X_h(phi)`. -/
theorem hasDerivAt_comp_flow (g : H → ℂ) (hr : H → ℝ) {phi : ℝ → H} {s : ℝ}
    (hphi : HasDerivAt phi (hamField hr (phi s)) s) (hg : DifferentiableAt ℝ g (phi s)) :
    HasDerivAt (fun τ => g (phi τ)) (pbC g (fun v => (hr v : ℂ)) (phi s)) s := by
  rw [pbC_ofReal g hr hg]
  exact hg.hasFDerivAt.comp_hasDerivAt s hphi

/-! ## 3. Gauge invariance and norm conservation -/

theorem kps_phase {n : ℕ} (K : BoundedSymmetricKernel H n) {c : ℂ} (hc : ‖c‖ = 1) (u : H) :
    kernelProductSymbol K (c • u) = kernelProductSymbol K u := by
  have hx : (⟨htpow n (c • u), htpow_mem_symSector n (c • u)⟩ : SymSector ℂ H n) =
      c ^ n • (⟨htpow n u, htpow_mem_symSector n u⟩ : SymSector ℂ H n) := by
    apply Subtype.ext
    simp [QuantumNLS.IntrinsicContact.htpow_smul]
  unfold kernelProductSymbol
  rw [hx, map_smul, QuantumNLS.IntrinsicContact.htpow_smul, Submodule.coe_smul, inner_smul_left,
    inner_smul_right, ← mul_assoc]
  have h1 : (starRingEnd ℂ) (c ^ n) * c ^ n = 1 := by
    rw [Complex.conj_mul', norm_pow, hc]; simp
  rw [h1, one_mul]

theorem symbol_phase (L : ∀ p : ℕ, BoundedSymmetricKernel H p) {c : ℂ} (hc : ‖c‖ = 1) (u : H) :
    symbol L (c • u) = symbol L u := by
  unfold symbol
  exact tsum_congr fun p => kps_phase (L p) hc u

/-- For a gauge-invariant real `F`, `Re⟨u, X_F(u)⟩ = 0`. -/
theorem re_inner_hamField (F : H → ℝ)
    (hF : ∀ (θ : ℝ) (u : H), F (Complex.exp (θ * Complex.I) • u) = F u) (u : H) :
    (⟪u, hamField F u⟫_ℂ).re = 0 := by
  by_cases hd : DifferentiableAt ℝ F u
  · have hγ : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I) • u) (Complex.I • u) 0 := by
      have he : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I))
          (Complex.exp ((0 : ℝ) * Complex.I) * Complex.I) 0 :=
        ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const Complex.I).cexp.congr_deriv (by simp)
      have := he.smul_const u
      simpa using this
    have hcomp : HasDerivAt (fun θ : ℝ => F (Complex.exp (θ * Complex.I) • u))
        (fderiv ℝ F u (Complex.I • u)) 0 := by
      have h : HasFDerivAt F (fderiv ℝ F u) (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • u) := by
        simpa using hd.hasFDerivAt
      exact h.comp_hasDerivAt (0 : ℝ) hγ
    have hconst : HasDerivAt (fun θ : ℝ => F (Complex.exp (θ * Complex.I) • u)) 0 0 := by
      have : (fun θ : ℝ => F (Complex.exp (θ * Complex.I) • u)) = fun _ => F u :=
        funext fun θ => hF θ u
      rw [this]; exact hasDerivAt_const _ _
    have h0 : fderiv ℝ F u (Complex.I • u) = 0 := hcomp.unique hconst
    rw [fderiv_eq_two_inner_gradient, real_inner_eq_re_inner] at h0
    set g := SymplecticBracket.gradient F u with hg
    set a := ⟪u, g⟫_ℂ with ha
    have h0' : (⟪g, Complex.I • u⟫_ℂ).re = 0 := by
      have h1 := h0
      simp only [RCLike.re_to_complex] at h1
      linarith
    rw [inner_smul_right, ← inner_conj_symm g u] at h0'
    have h2 : (Complex.I * (starRingEnd ℂ) a).re = a.im := by simp [Complex.mul_re]
    rw [hamField, ← hg, inner_smul_right, re_neg_I_mul]
    rw [← ha] at h0'
    linarith
  · have hg : SymplecticBracket.gradient F u = 0 := by
      simp [SymplecticBracket.gradient, fderiv_zero_of_not_differentiableAt hd]
    simp [hamField, hg]

/-- **Norm conservation** along any solution curve of a gauge-invariant real Hamiltonian. -/
theorem norm_flow_const (F : H → ℝ)
    (hF : ∀ (θ : ℝ) (u : H), F (Complex.exp (θ * Complex.I) • u) = F u) {phi : ℝ → H}
    (hphi : ∀ s, HasDerivAt phi (hamField F (phi s)) s) (s : ℝ) : ‖phi s‖ = ‖phi 0‖ := by
  have hd : ∀ x, HasDerivAt (fun τ => ‖phi τ‖ ^ 2) 0 x := by
    intro x
    have h := (hphi x).norm_sq
    have h0 : ⟪phi x, hamField F (phi x)⟫_ℝ = 0 := re_inner_hamField F hF (phi x)
    rw [h0, mul_zero] at h
    exact h
  have hc := is_const_of_deriv_eq_zero (f := fun τ => ‖phi τ‖ ^ 2)
    (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) s 0
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hc

/-! ## 4. Taylor remainder for a chain `G_k' = G_{k+1}` -/

/-- The degree-`n` Taylor polynomial with real coefficients `s^k/k!`. -/
def taylorPoly (c : ℕ → ℂ) (n : ℕ) (s : ℝ) : ℂ :=
  ∑ k ∈ range n, (((s ^ k / (k ! : ℝ)) : ℝ) : ℂ) * c k

theorem hasDerivAt_monomial (m : ℕ) (c : ℂ) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (((x ^ (m + 1) / ((m + 1) ! : ℝ)) : ℝ) : ℂ) * c)
      ((((s ^ m / (m ! : ℝ)) : ℝ) : ℂ) * c) s := by
  have h := (((hasDerivAt_pow (m + 1) s).div_const ((m + 1) ! : ℝ)).ofReal_comp).mul_const c
  refine h.congr_deriv ?_
  congr 2
  rw [Nat.factorial_succ]
  have hm : (m ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  push_cast
  field_simp
  try ring

theorem hasDerivAt_taylorPoly (c : ℕ → ℂ) (n : ℕ) (s : ℝ) :
    HasDerivAt (taylorPoly c (n + 1)) (taylorPoly (fun k => c (k + 1)) n s) s := by
  induction n with
  | zero =>
    have : taylorPoly c 1 = fun _ => c 0 := by funext x; simp [taylorPoly]
    rw [this]
    simpa [taylorPoly] using hasDerivAt_const s (c 0)
  | succ n ih =>
    have hfun : taylorPoly c (n + 1 + 1) = fun x => taylorPoly c (n + 1) x +
        (((x ^ (n + 1) / ((n + 1) ! : ℝ)) : ℝ) : ℂ) * c (n + 1) := by
      funext x; simp [taylorPoly, Finset.sum_range_succ]
    have hval : taylorPoly (fun k => c (k + 1)) (n + 1) s = taylorPoly (fun k => c (k + 1)) n s +
        (((s ^ n / (n ! : ℝ)) : ℝ) : ℂ) * c (n + 1) := by
      simp [taylorPoly, Finset.sum_range_succ]
    rw [hfun, hval]
    exact ih.add (hasDerivAt_monomial n (c (n + 1)) s)

theorem taylorPoly_zero_point (c : ℕ → ℂ) (n : ℕ) : taylorPoly c (n + 1) 0 = c 0 := by
  unfold taylorPoly
  rw [Finset.sum_range_succ']
  simp

theorem taylor_bound_nonneg (n : ℕ) :
    ∀ (G : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (t : ℝ), 0 ≤ t →
      (∀ k s, HasDerivAt (G k) (G (k + 1) s) s) →
      (∀ k s, 0 ≤ s → s ≤ t → ‖G k s‖ ≤ M k) →
      ‖G 0 t - taylorPoly (fun k => G k 0) n t‖ ≤ M n * t ^ n / (n ! : ℝ) := by
  induction n with
  | zero =>
    intro G M t ht _ hb
    simpa [taylorPoly] using hb 0 t ht le_rfl
  | succ n ih =>
    intro G M t ht hd hb
    set f : ℝ → ℂ := fun s => G 0 s - taylorPoly (fun k => G k 0) (n + 1) s with hf
    set f' : ℝ → ℂ := fun s => G 1 s - taylorPoly (fun k => G (k + 1) 0) n s with hf'
    have hfd : ∀ s, HasDerivAt f (f' s) s := fun s =>
      (hd 0 s).sub (hasDerivAt_taylorPoly (fun k => G k 0) n s)
    have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hfac1 : (0 : ℝ) < ((n + 1) ! : ℝ) := by exact_mod_cast Nat.factorial_pos (n + 1)
    set B : ℝ → ℝ := fun s => M (n + 1) * s ^ (n + 1) / ((n + 1) ! : ℝ) with hB
    set B' : ℝ → ℝ := fun s => M (n + 1) * s ^ n / (n ! : ℝ) with hB'
    have hBd : ∀ s, HasDerivAt B (B' s) s := by
      intro s
      have h := ((hasDerivAt_pow (n + 1) s).const_mul (M (n + 1))).div_const ((n + 1) ! : ℝ)
      refine h.congr_deriv ?_
      simp only [hB', Nat.factorial_succ]
      push_cast
      field_simp
      try ring
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := t)
      (f := f) (f' := f') (B := B) (B' := B')
      (fun s _ => (hfd s).continuousAt.continuousWithinAt)
      (fun s _ => (hfd s).hasDerivWithinAt)
      (by simp [hf, hB, taylorPoly_zero_point])
      hBd
      (fun s hs => by
        have h := ih (fun k => G (k + 1)) (fun k => M (k + 1)) s hs.1
          (fun k x => hd (k + 1) x) (fun k x hx0 hxs => hb (k + 1) x hx0 (hxs.trans hs.2.le))
        simpa [hf'] using h)
    have := key ⟨ht, le_rfl⟩
    simpa [hf, hB] using this

/-- **Taylor remainder** in both time directions. -/
theorem taylor_bound (n : ℕ) (G : ℕ → ℝ → ℂ) (M : ℕ → ℝ) (t : ℝ)
    (hd : ∀ k s, HasDerivAt (G k) (G (k + 1) s) s) (hb : ∀ k s, ‖G k s‖ ≤ M k) :
    ‖G 0 t - taylorPoly (fun k => G k 0) n t‖ ≤ M n * |t| ^ n / (n ! : ℝ) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact taylor_bound_nonneg n G M t ht hd (fun k s _ _ => hb k s)
  · set G' : ℕ → ℝ → ℂ := fun k s => ((-1 : ℂ) ^ k) * G k (-s) with hG'
    have hd' : ∀ k s, HasDerivAt (G' k) (G' (k + 1) s) s := by
      intro k s
      have h1 := ((hd k (-s)).scomp s (hasDerivAt_neg s)).const_mul ((-1 : ℂ) ^ k)
      refine h1.congr_deriv ?_
      simp only [hG', pow_succ]
      simp [Function.comp_def]
    have hb' : ∀ k s, 0 ≤ s → s ≤ -t → ‖G' k s‖ ≤ M k := by
      intro k s _ _
      simp only [hG', norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      exact hb k (-s)
    have h := taylor_bound_nonneg n G' M (-t) (by linarith) hd' hb'
    rw [abs_of_neg ht]
    have hpoly : taylorPoly (fun k => G' k 0) n (-t) = taylorPoly (fun k => G k 0) n t := by
      unfold taylorPoly
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hG', neg_zero]
      rw [neg_pow t k]
      push_cast
      rw [← mul_assoc]
      congr 1
      rw [mul_div_assoc, mul_comm ((-1 : ℂ) ^ k), mul_assoc, ← mul_pow]
      norm_num
    rw [hpoly] at h
    simpa [hG'] using h

/-! ## 5. The classical series along the flow -/

/-- **Classical series.** Let `hr` be a real Hamiltonian, `phi` a solution curve of `phi' = X_{hr}(phi)`
on the unit sphere, and `g_k` a chain of functions, differentiable on the unit sphere, with
`g_{k+1} = {g_k, hr}` there and `|g_k| ≤ (Kk)^k C` there. If `eK|t| < 1`, then
`Σ_k (t^k/k!) g_k(phi 0) = g_0(phi t)`. -/
theorem classical_hasSum (hr : H → ℝ) (g : ℕ → H → ℂ) {K C : ℝ} (hK : 0 ≤ K) (hC : 0 ≤ C)
    {phi : ℝ → H} (hphi : ∀ s, HasDerivAt phi (hamField hr (phi s)) s) (hn : ∀ s, ‖phi s‖ = 1)
    (hdiff : ∀ k (u : H), ‖u‖ = 1 → DifferentiableAt ℝ (g k) u)
    (hsucc : ∀ k (u : H), ‖u‖ = 1 → g (k + 1) u = pbC (g k) (fun v => (hr v : ℂ)) u)
    (hbd : ∀ k (u : H), ‖u‖ = 1 → ‖g k u‖ ≤ (K * k) ^ k * C) {t : ℝ}
    (ht : Real.exp 1 * K * |t| < 1) :
    HasSum (fun k : ℕ => (((t ^ k / (k ! : ℝ)) : ℝ) : ℂ) * g k (phi 0)) (g 0 (phi t)) := by
  set G : ℕ → ℝ → ℂ := fun k s => g k (phi s) with hG
  have hd : ∀ k s, HasDerivAt (G k) (G (k + 1) s) s := by
    intro k s
    have h := hasDerivAt_comp_flow (g k) hr (hphi s) (hdiff k (phi s) (hn s))
    rw [← hsucc k (phi s) (hn s)] at h
    exact h
  set r : ℝ := Real.exp 1 * K * |t| with hr_def
  have hr0 : 0 ≤ r := by positivity
  -- the remainder bound
  have hrem : ∀ n : ℕ, ‖G 0 t - taylorPoly (fun k => G k 0) n t‖ ≤ r ^ n * C := by
    intro n
    refine (taylor_bound n G (fun k => (K * k) ^ k * C) t hd
      (fun k s => hbd k (phi s) (hn s))).trans ?_
    have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have hkey : (n : ℝ) ^ n / (n ! : ℝ) ≤ Real.exp 1 ^ n :=
      QuantumNLS.Local014Heisenberg.pow_div_factorial_le n
    calc (K * n) ^ n * C * |t| ^ n / (n ! : ℝ)
        = (K * |t|) ^ n * ((n : ℝ) ^ n / (n ! : ℝ)) * C := by
          rw [mul_pow, mul_pow]; field_simp
      _ ≤ (K * |t|) ^ n * Real.exp 1 ^ n * C := by gcongr
      _ = r ^ n * C := by rw [hr_def, mul_assoc (Real.exp 1), mul_pow (Real.exp 1)]; ring
  have htend : Tendsto (fun n : ℕ => taylorPoly (fun k => G k 0) n t) atTop (𝓝 (G 0 t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => r ^ n * C) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 ht).mul_const C
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    rw [norm_sub_rev]
    exact hrem n
  -- absolute summability of the series
  have hterm : ∀ k : ℕ, ‖(((t ^ k / (k ! : ℝ)) : ℝ) : ℂ) * g k (phi 0)‖ ≤ r ^ k * C := by
    intro k
    have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
    have hkey : (k : ℝ) ^ k / (k ! : ℝ) ≤ Real.exp 1 ^ k :=
      QuantumNLS.Local014Heisenberg.pow_div_factorial_le k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos hfac]
    calc |t| ^ k / (k ! : ℝ) * ‖g k (phi 0)‖ ≤ |t| ^ k / (k ! : ℝ) * ((K * k) ^ k * C) :=
          mul_le_mul_of_nonneg_left (hbd k (phi 0) (hn 0)) (by positivity)
      _ = (K * |t|) ^ k * ((k : ℝ) ^ k / (k ! : ℝ)) * C := by
          rw [mul_pow, mul_pow]; field_simp
      _ ≤ (K * |t|) ^ k * Real.exp 1 ^ k * C := by gcongr
      _ = r ^ k * C := by rw [hr_def, mul_assoc (Real.exp 1), mul_pow (Real.exp 1)]; ring
  have hsum : Summable fun k : ℕ => ‖(((t ^ k / (k ! : ℝ)) : ℝ) : ℂ) * g k (phi 0)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
      ((summable_geometric_of_lt_one hr0 ht).mul_right C)
  rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
  exact htend

end QuantumNLS.Local014ClassicalSeries

/-! Axiom audit. -/
#print axioms QuantumNLS.Local014ClassicalSeries.hasFDerivAt_symbol
#print axioms QuantumNLS.Local014ClassicalSeries.pbC_ofReal
#print axioms QuantumNLS.Local014ClassicalSeries.hasDerivAt_comp_flow
#print axioms QuantumNLS.Local014ClassicalSeries.kps_phase
#print axioms QuantumNLS.Local014ClassicalSeries.symbol_phase
#print axioms QuantumNLS.Local014ClassicalSeries.re_inner_hamField
#print axioms QuantumNLS.Local014ClassicalSeries.norm_flow_const
#print axioms QuantumNLS.Local014ClassicalSeries.taylor_bound
#print axioms QuantumNLS.Local014ClassicalSeries.classical_hasSum
