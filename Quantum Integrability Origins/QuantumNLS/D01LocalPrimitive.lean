import QuantumNLS.StrongSymplectic
import QuantumNLS.RealAnalyticDef

/-!
# `lem:global-D01-local-primitive` (R-81E9AAB6)

Source: `source/chapters/global/liouville_reconstruction.tex`: conventions (lines 19-55), the
hypotheses of `thm:global-D01-reconstruction` (lines 59-95), the analytic-form paragraph (lines
128-143), and the lemma with its proof (lines 145-210).

Realized objects used read-only:
* DEF-015 (`SymplecticBracket`, `056a23e2…`): `Ω(h,k) = 2 Im⟨h,k⟩` (`omega`), the gradient and the
  Hamiltonian vector field `X_F = −i∇F` (`hamField`), which is exactly the convention
  `ι_{X_F} Ω = dF` of the source (`omega_hamField` below);
* DEF-016 (`StrongSymplectic`, `6302051b…`): `IsStronglySymplectic`, for the individual torus maps;
* DEF-017 (`RealAnalyticDef`, `c13c7dd2…`): real analyticity as a norm-convergent series of continuous
  real homogeneous polynomials near each input (`IsRealAnalyticPoly`, `IsRealAnalyticMap`);
* the sequence space `K = ℓ²(ℤ;ℂ)` (`lp (fun _ : ℤ => ℂ) 2`, DEF-002 at `s = 0`) and
  `ℓ¹(ℤ;ℝ)` (`lp (fun _ : ℤ => ℝ) 1`); the torus `𝕋^ℤ` is `ℤ → Real.Angle` (`Real.Angle = ℝ/2πℤ`)
  with the product topology.

The hypotheses of `thm:global-D01-reconstruction` are bundled literally in `Hyp`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ENNReal
open Filter Set

-- the realification of a complex Hilbert space (as in DEF-015 / DEF-016)
attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.D01LocalPrimitive

open QuantumNLS.SymplecticBracket QuantumNLS.StrongSymplectic QuantumNLS.RealAnalyticDef

/-! ## 1. The forms `ω`, `α` and the map `W` on a complex Hilbert space -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `α_u(h) = Im⟨u,h⟩`. -/
def alphaF (u h : E) : ℝ := (inner ℂ u h).im

/-- `α_u` as a bounded real-linear functional. -/
def alphaL (u : E) : E →L[ℝ] ℝ := Complex.imCLM.comp ((innerSL ℂ u).restrictScalars ℝ)

@[simp] lemma alphaL_apply (u h : E) : alphaL u h = alphaF u h := rfl

lemma omega_sub_left (a b k : E) : omega (a - b) k = omega a k - omega b k := by
  unfold omega; rw [inner_sub_left, Complex.sub_im]; ring

/-- Strong nondegeneracy of `ω`. -/
lemma omega_eq_of_forall {a b : E} (h : ∀ k, omega a k = omega b k) : a = b := by
  have h1 := h (Complex.I • (a - b))
  rw [← sub_eq_zero, ← omega_sub_left, omega_mul_I] at h1
  have : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **The sign convention `ι_{X_F} ω = dF`** for DEF-015's `X_F = −i∇F`. -/
lemma omega_hamField (F : E → ℝ) (u h : E) : omega (hamField F u) h = fderiv ℝ F u h := by
  rw [fderiv_eq_two_inner_gradient, omega, hamField, inner_smul_left, real_inner_eq_re_inner ℂ]
  simp [Complex.mul_im]

/-- `ι_{z/2} ω = α_z` (`eq:global-D01-standard-signs`, third identity). -/
lemma omega_half (z k : E) : omega ((2⁻¹ : ℂ) • z) k = alphaF z k := by
  rw [omega, alphaF, inner_smul_left, show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
    Complex.conj_ofReal, Complex.im_ofReal_mul]
  ring

/-- `W⁻¹ f`: the vector `v` with `ω(v,·) = f` (`W v = ω(v,·)` is an isomorphism `E → E*`). -/
def Winv (f : E →L[ℝ] ℝ) : E := hamField (⇑f) 0

lemma omega_Winv (f : E →L[ℝ] ℝ) (h : E) : omega (Winv f) h = f h := by
  rw [Winv, omega_hamField, ContinuousLinearMap.fderiv]

lemma Winv_unique (f : E →L[ℝ] ℝ) (v : E) (hv : ∀ h, omega v h = f h) : v = Winv f :=
  omega_eq_of_forall fun h => by rw [hv, omega_Winv]

end General

/-! ## 2. The sequence space `K = ℓ²(ℤ;ℂ)`: actions, rotations, conjugation -/

/-- `K = ℓ²(ℤ;ℂ)`. -/
abbrev K := lp (fun _ : ℤ => ℂ) 2

/-- `ℓ¹(ℤ;ℝ)`. -/
abbrev L1 := lp (fun _ : ℤ => ℝ) 1

/-- The torus `𝕋^ℤ`, `𝕋 = ℝ/2πℤ`, with the product topology. -/
abbrev Tor := ℤ → Real.Angle

lemma norm_sq_K (z : K) : ‖z‖ ^ 2 = ∑' n, ‖z n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < (2 : ℝ≥0∞).toReal) z
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

lemma summable_sq_K (z : K) : Summable fun n => ‖z n‖ ^ 2 := by
  have h := (lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  rw [ENNReal.toReal_ofNat] at h
  simpa only [Real.rpow_two] using h

/-- The coordinate `z ↦ z_n`, real-linear. -/
def evalR (n : ℤ) : K →L[ℝ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).restrictScalars ℝ

@[simp] lemma evalR_apply (n : ℤ) (z : K) : evalR n z = z n := rfl

/-- `q_n(z) = |z_n|²`. -/
def q (n : ℤ) (z : K) : ℝ := ‖z n‖ ^ 2

/-- `X_{q_n}(z) = −i z_n e_n`. -/
def Xq (n : ℤ) (z : K) : K := lp.single 2 n (-Complex.I * z n)

lemma hasFDerivAt_q (n : ℤ) (z : K) :
    HasFDerivAt (q n) ((2 : ℝ) • (Complex.reCLM.comp ((conj (z n)) • evalR n))) z := by
  have he : HasFDerivAt (fun w : K => w n) (evalR n) z := (evalR n).hasFDerivAt
  have hc : HasFDerivAt (fun w : K => conj (w n))
      (Complex.conjCLE.toContinuousLinearMap.comp (evalR n)) z :=
    Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z he
  have hm := hc.mul he
  have hr := Complex.reCLM.hasFDerivAt.comp z hm
  have hq : q n = fun w : K => Complex.reCLM (conj (w n) * w n) := by
    funext w
    rw [q, Complex.conj_mul', ← Complex.ofReal_pow, Complex.reCLM_apply, Complex.ofReal_re]
  rw [hq]
  refine hr.congr_fderiv ?_
  ext h
  simp [Complex.mul_re]
  ring

lemma fderiv_q_apply (n : ℤ) (z h : K) :
    fderiv ℝ (q n) z h = 2 * (conj (z n) * h n).re := by
  rw [(hasFDerivAt_q n z).fderiv]
  simp

lemma omega_Xq (n : ℤ) (z h : K) : omega (Xq n z) h = 2 * (conj (z n) * h n).re := by
  rw [omega, Xq, lp.inner_single_left, RCLike.inner_apply]
  simp [Complex.mul_im, Complex.mul_re]
  ring

/-- `ω(X_{q_n}(z), h) = dq_n(z)[h]`. -/
lemma omega_Xq_eq_fderiv (n : ℤ) (z h : K) : omega (Xq n z) h = fderiv ℝ (q n) z h := by
  rw [omega_Xq, fderiv_q_apply]

/-- DEF-015's Hamiltonian field of `q_n` is `X_{q_n}(z) = −i z_n e_n`
(`eq:global-D01-standard-signs`, first identity). -/
lemma hamField_q (n : ℤ) (z : K) : hamField (q n) z = Xq n z :=
  omega_eq_of_forall fun h => (omega_hamField (q n) z h).trans (omega_Xq_eq_fderiv n z h).symm

/-- `α_z(X_{q_n}(z)) = −q_n(z)` (`eq:global-D01-standard-signs`, second identity). -/
lemma alpha_Xq (n : ℤ) (z : K) : alphaF z (Xq n z) = -q n z := by
  rw [alphaF, Xq, lp.inner_single_right, RCLike.inner_apply, q]
  have h : ∀ w : ℂ, ((-Complex.I * w) * conj w).im = -‖w‖ ^ 2 := fun w => by
    rw [mul_assoc, mul_comm w, Complex.conj_mul', ← Complex.ofReal_pow]
    simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  exact h (z n)

lemma Xq_sub (n : ℤ) (z w : K) : Xq n z - Xq n w = lp.single 2 n (-Complex.I * (z - w) n) := by
  rw [Xq, Xq, ← lp.single_sub, lp.coeFn_sub, Pi.sub_apply, mul_sub]

lemma lipschitz_Xq (n : ℤ) : LipschitzWith 1 (Xq n) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [dist_eq_norm, dist_eq_norm, Xq_sub, lp.norm_single (by norm_num), norm_mul, norm_neg,
    Complex.norm_I, one_mul, NNReal.coe_one, one_mul]
  exact lp.norm_apply_le_norm (by norm_num) (z - w) n

/-- The phase `e^{−iθ}` of `θ ∈ 𝕋`. -/
def ph (x : Real.Angle) : ℂ := (((-x).toCircle : Circle) : ℂ)

lemma norm_ph (x : Real.Angle) : ‖ph x‖ = 1 := Circle.norm_coe _

lemma ph_add (x y : Real.Angle) : ph (x + y) = ph x * ph y := by
  simp only [ph, neg_add, Real.Angle.toCircle_add, Circle.coe_mul]

lemma ph_zero : ph 0 = 1 := by simp [ph]

lemma ph_coe (t : ℝ) : ph (t : Real.Angle) = Complex.exp (-(t : ℂ) * Complex.I) := by
  rw [ph, ← Real.Angle.coe_neg, Real.Angle.toCircle_coe, Circle.coe_exp]
  push_cast; ring_nf

lemma conj_ph_mul (x : Real.Angle) : conj (ph x) * ph x = 1 := by
  rw [Complex.conj_mul', norm_ph]; simp

/-- The rotation `R_θ z = (e^{−iθ_n} z_n)_n`, complex-linear. -/
def rotL (θ : Tor) : K →ₗ[ℂ] K where
  toFun z := ⟨fun n => ph (θ n) * z n, by
    refine memℓp_gen ?_
    refine ((lp.memℓp z).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).congr fun n => ?_
    rw [norm_mul, norm_ph, one_mul]⟩
  map_add' z w := lp.ext (funext fun n => by
    show ph (θ n) * (z n + w n) = ph (θ n) * z n + ph (θ n) * w n
    ring)
  map_smul' c z := lp.ext (funext fun n => by
    show ph (θ n) * (c * z n) = c * (ph (θ n) * z n)
    ring)

lemma rotL_apply (θ : Tor) (z : K) (n : ℤ) : rotL θ z n = ph (θ n) * z n := rfl

lemma inner_rotL (θ : Tor) (z w : K) : inner ℂ (rotL θ z) (rotL θ w) = inner ℂ z w := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [rotL_apply, rotL_apply, RCLike.inner_apply, RCLike.inner_apply, map_mul]
  linear_combination (conj (z n) * w n) * conj_ph_mul (θ n)

lemma norm_rotL (θ : Tor) (z : K) : ‖rotL θ z‖ = ‖z‖ := by
  have h := inner_rotL θ z z
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖rotL θ z‖ ^ 2 = ‖z‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- `R_θ` as a bounded complex-linear map (an isometry). -/
def Rot (θ : Tor) : K →L[ℂ] K :=
  (rotL θ).mkContinuous 1 fun z => by rw [one_mul, norm_rotL]

@[simp] lemma Rot_apply (θ : Tor) (z : K) (n : ℤ) : Rot θ z n = ph (θ n) * z n := rfl

lemma norm_Rot (θ : Tor) (z : K) : ‖Rot θ z‖ = ‖z‖ := norm_rotL θ z

lemma inner_Rot (θ : Tor) (z w : K) : inner ℂ (Rot θ z) (Rot θ w) = inner ℂ z w := inner_rotL θ z w

lemma alpha_Rot (θ : Tor) (z k : K) : alphaF (Rot θ z) (Rot θ k) = alphaF z k := by
  rw [alphaF, alphaF, inner_Rot]

lemma Rot_zero (z : K) : Rot 0 z = z := lp.ext (funext fun n => by simp [ph_zero])

lemma Rot_add (θ θ' : Tor) (z : K) : Rot (θ + θ') z = Rot θ (Rot θ' z) :=
  lp.ext (funext fun n => by simp only [Rot_apply, Pi.add_apply, ph_add]; ring)

lemma Rot_single (n : ℤ) (x : Real.Angle) (z : K) :
    Rot (Pi.single n x) z = z + (ph x - 1) • lp.single 2 n (z n) := by
  refine lp.ext (funext fun m => ?_)
  rw [Rot_apply, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hm : m = n
  · subst hm; rw [Pi.single_eq_same, lp.single_apply_self]; ring
  · rw [Pi.single_eq_of_ne hm, ph_zero, lp.single_apply_ne _ _ _ hm]; ring

/-- `t ↦ R_{t e_n} z` solves `ż = X_{q_n}(z)`. -/
lemma hasDerivAt_Rot_single (n : ℤ) (z : K) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Rot (Pi.single n (s : Real.Angle)) z)
      (Xq n (Rot (Pi.single n (t : Real.Angle)) z)) t := by
  have he : HasDerivAt (fun s : ℝ => Complex.exp (-(s : ℂ) * Complex.I))
      (Complex.exp (-(t : ℂ) * Complex.I) * (-Complex.I)) t := by
    have h1 : HasDerivAt (fun s : ℝ => -(s : ℂ) * Complex.I) (-Complex.I) t := by
      have := ((hasDerivAt_id t).ofReal_comp.neg).mul_const Complex.I
      simpa using this
    exact h1.cexp
  have h2 := ((he.sub_const 1).smul_const (lp.single 2 n (z n))).const_add z
  have e : (fun s : ℝ => Rot (Pi.single n (s : Real.Angle)) z) =
      fun s : ℝ => z + (Complex.exp (-(s : ℂ) * Complex.I) - 1) • lp.single 2 n (z n) := by
    funext s; rw [Rot_single, ph_coe]
  rw [e]
  convert h2 using 1
  rw [Xq, Rot_apply, Pi.single_eq_same, ph_coe, ← lp.single_smul, smul_eq_mul]
  congr 1; ring

/-- Conjugation `C_K z = z̄`, real-linear and isometric. -/
def conjK : K →L[ℝ] K :=
  LinearMap.mkContinuous
    { toFun := star
      map_add' := star_add
      map_smul' := fun r z => lp.ext (funext fun n => by
        simp only [lp.star_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply,
          Complex.real_smul, star_mul', Complex.star_def, Complex.conj_ofReal]) }
    1 (fun z => by simp)

@[simp] lemma conjK_apply (z : K) : conjK z = star z := rfl

lemma inner_star (z k : K) : inner ℂ (star z) (star k) = conj (inner ℂ z k) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum, Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  simp only [lp.star_apply, RCLike.inner_apply, map_mul, Complex.star_def]

lemma alpha_star (z k : K) : alphaF (star z) (star k) = -alphaF z k := by
  rw [alphaF, alphaF, inner_star, Complex.conj_im]

#print axioms hamField_q
#print axioms alpha_Xq
#print axioms hasDerivAt_Rot_single
#print axioms alpha_star

/-- `α_z` on `K` as a bounded real-linear functional (elaborated on `K` itself). -/
def alphaK (z : K) : K →L[ℝ] ℝ := Complex.imCLM.comp ((innerSL ℂ z).restrictScalars ℝ)

@[simp] lemma alphaK_apply (z k : K) : alphaK z k = alphaF z k := rfl

lemma ph_arg_mul (w : ℂ) : ph (Complex.arg w : Real.Angle) * w = (‖w‖ : ℂ) := by
  rw [ph_coe]
  have e := Complex.norm_mul_exp_arg_mul_I w
  calc Complex.exp (-(Complex.arg w : ℂ) * Complex.I) * w
      = Complex.exp (-(Complex.arg w : ℂ) * Complex.I) *
          (‖w‖ * Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by rw [e]
    _ = ‖w‖ * Complex.exp (-(Complex.arg w : ℂ) * Complex.I + (Complex.arg w : ℂ) * Complex.I) := by
        rw [Complex.exp_add]; ring
    _ = ‖w‖ := by
        rw [show -(Complex.arg w : ℂ) * Complex.I + (Complex.arg w : ℂ) * Complex.I = 0 by ring,
          Complex.exp_zero, mul_one]

lemma ph_pi : ph (Real.pi : Real.Angle) = -1 := by
  rw [ph_coe, neg_mul, Complex.exp_neg_pi_mul_I]

lemma angle_surj (x : Real.Angle) : ∃ t : ℝ, (t : Real.Angle) = x := by
  induction x using Real.Angle.induction_on with
  | h t => exact ⟨t, rfl⟩

/-- Finite truncation of an angle sequence to `|n| ≤ N`. -/
def trunc (θ : Tor) (N : ℕ) : Tor := ∑ n ∈ Finset.Icc (-(N : ℤ)) N, Pi.single n (θ n)

lemma trunc_apply (θ : Tor) (N : ℕ) (n : ℤ) :
    trunc θ N n = if n ∈ Finset.Icc (-(N : ℤ)) N then θ n else 0 := by
  rw [trunc, Finset.sum_apply]
  simp [Pi.single_apply]

lemma eventually_trunc (θ : Tor) (n : ℤ) : ∀ᶠ N in atTop, trunc θ N n = θ n := by
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  have hmem : n ∈ Finset.Icc (-(N : ℤ)) N := by
    rw [Finset.mem_Icc]; omega
  simp [trunc_apply, hmem]

/-- Finitely supported angle sequences approximate every angle sequence (product topology). -/
lemma tendsto_trunc (θ : Tor) : Tendsto (trunc θ) atTop (𝓝 θ) :=
  tendsto_pi_nhds.mpr fun n =>
    tendsto_const_nhds.congr' ((eventually_trunc θ n).mono fun _ h => h.symm)

lemma tendsto_Rot_trunc (θ : Tor) (z : K) :
    Tendsto (fun N => Rot (trunc θ N) z) atTop (𝓝 (Rot θ z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (G := ℝ)
    (f := fun (N : ℕ) n => ‖(Rot (trunc θ N) z - Rot θ z) n‖ ^ 2) (g := fun _ => 0)
    (bound := fun n => 4 * ‖z n‖ ^ 2) ((summable_sq_K z).mul_left 4) ?_ ?_
  · rw [tsum_zero] at h
    have hsq : Tendsto (fun N => ‖Rot (trunc θ N) z - Rot θ z‖ ^ 2) atTop (𝓝 0) :=
      h.congr fun N => (norm_sq_K _).symm
    have h2 := hsq.sqrt
    rw [Real.sqrt_zero] at h2
    exact h2.congr fun N => Real.sqrt_sq (norm_nonneg _)
  · intro n
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_trunc θ n] with N hN
    rw [lp.coeFn_sub, Pi.sub_apply, Rot_apply, Rot_apply, hN, sub_self, norm_zero]
    norm_num
  · refine Eventually.of_forall fun N n => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _), lp.coeFn_sub, Pi.sub_apply, Rot_apply, Rot_apply,
      ← sub_mul, norm_mul, mul_pow]
    have h1 : ‖ph (trunc θ N n) - ph (θ n)‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by rw [norm_ph, norm_ph]; norm_num)
    have h2 : ‖ph (trunc θ N n) - ph (θ n)‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg (ph (trunc θ N n) - ph (θ n))]
    nlinarith [sq_nonneg ‖z n‖]

#print axioms tendsto_Rot_trunc

/-! ## 3. The hypotheses of `thm:global-D01-reconstruction` (items 1-4), literally -/

/-- The hypotheses of `thm:global-D01-reconstruction`. Real analyticity is DEF-017
(`IsRealAnalyticMap` / `IsRealAnalyticPoly`); strong symplecticity is DEF-016; `X_F` is DEF-015's
`hamField`; `ω = 2 Im⟨·,·⟩` is DEF-015's `omega` on `H` and on `K`. -/
structure Hyp (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- item 1: `I : H → ℓ¹(ℤ;ℝ)` real analytic, `I_n ≥ 0`, `Σ I_n(u) = ‖u‖²`, compact preimages of
  compact subsets of `ℓ¹_+`. -/
  act : H → L1
  act_analytic : IsRealAnalyticMap act
  act_nonneg : ∀ u n, 0 ≤ act u n
  act_mass : ∀ u, ∑' n, act u n = ‖u‖ ^ 2
  act_proper : ∀ A : Set L1, IsCompact A → (∀ a ∈ A, ∀ n, 0 ≤ a n) → IsCompact (act ⁻¹' A)
  /-- item 2: a jointly continuous action `ρ` of `𝕋^ℤ` preserving `I`, by real-analytic strong
  symplectic diffeomorphisms; its `n`th circle is the complete (`2π`-periodic) Hamiltonian flow of
  `I_n`. -/
  rho : Tor → H → H
  rho_cont : Continuous fun p : Tor × H => rho p.1 p.2
  rho_zero : rho 0 = id
  rho_add : ∀ θ θ', rho (θ + θ') = rho θ ∘ rho θ'
  rho_act : ∀ θ u, act (rho θ u) = act u
  rho_analytic : ∀ θ, IsRealAnalyticMap (rho θ)
  rho_symp : ∀ θ, IsStronglySymplectic (rho θ)
  rho_flow : ∀ (n : ℤ) (u : H) (t : ℝ),
    HasDerivAt (fun s : ℝ => rho (Pi.single n (s : Real.Angle)) u)
      (hamField (fun v => act v n) (rho (Pi.single n (t : Real.Angle)) u)) t
  /-- item 3: `ᾱ : H → H*` real analytic in the dual norm, `dᾱ = ω_H`, `ρ_θ^*ᾱ = ᾱ`,
  `ᾱ(X_{I_n}) = −I_n`; a real-linear isometric antisymplectic involution `C_H` preserving `I`,
  with `C_H^*ᾱ = −ᾱ`. -/
  abar : H → (H →L[ℝ] ℝ)
  abar_analytic : IsRealAnalyticMap abar
  abar_d : ∀ u h k, fderiv ℝ abar u h k - fderiv ℝ abar u k h = omega h k
  abar_inv : ∀ θ u h, abar (rho θ u) (fderiv ℝ (rho θ) u h) = abar u h
  abar_X : ∀ (n : ℤ) u, abar u (hamField (fun v => act v n) u) = -act u n
  CH : H →ₗᵢ[ℝ] H
  CH_invol : ∀ u, CH (CH u) = u
  CH_anti : ∀ h k, omega (CH h) (CH k) = -omega h k
  CH_act : ∀ u, act (CH u) = act u
  abar_CH : ∀ u h, abar (CH u) (CH h) = -abar u h
  /-- item 4: a real-analytic diffeomorphism `φ : B_ε(H) → B_ε(K)` of the entire open balls with
  real-analytic inverse `ψ`, `φ^*ω_K = ω_H`, `q_n ∘ φ = I_n`, `φ ∘ C_H = conj ∘ φ`. -/
  ε : ℝ
  ε_pos : 0 < ε
  phi : H → K
  psi : K → H
  phi_maps : MapsTo phi (Metric.ball 0 ε) (Metric.ball 0 ε)
  psi_maps : MapsTo psi (Metric.ball 0 ε) (Metric.ball 0 ε)
  psi_phi : ∀ u ∈ Metric.ball (0 : H) ε, psi (phi u) = u
  phi_psi : ∀ z ∈ Metric.ball (0 : K) ε, phi (psi z) = z
  phi_analytic : ∀ u ∈ Metric.ball (0 : H) ε, IsRealAnalyticPoly phi u
  psi_analytic : ∀ z ∈ Metric.ball (0 : K) ε, IsRealAnalyticPoly psi z
  phi_symp : ∀ u ∈ Metric.ball (0 : H) ε, ∀ h k,
    omega (fderiv ℝ phi u h) (fderiv ℝ phi u k) = omega h k
  phi_q : ∀ u ∈ Metric.ball (0 : H) ε, ∀ n, q n (phi u) = act u n
  phi_CH : ∀ u ∈ Metric.ball (0 : H) ε, phi (CH u) = star (phi u)

/-! ## 4. Proof of `lem:global-D01-local-primitive` -/

namespace Hyp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Hyp H)

/-- `Y = W⁻¹ ᾱ`. -/
def Y (u : H) : H := Winv (S.abar u)

/-- `B_ε(H)`. -/
abbrev B : Set H := Metric.ball 0 S.ε
/-- `B_ε(K)`. -/
abbrev BK : Set K := Metric.ball 0 S.ε

lemma diff_phi {u : H} (hu : u ∈ S.B) : DifferentiableAt ℝ S.phi u :=
  (analyticAt_of_isRealAnalyticPoly (S.phi_analytic u hu)).differentiableAt

lemma diff_psi {z : K} (hz : z ∈ S.BK) : DifferentiableAt ℝ S.psi z :=
  (analyticAt_of_isRealAnalyticPoly (S.psi_analytic z hz)).differentiableAt

lemma Dpsi_Dphi {u : H} (hu : u ∈ S.B) (h : H) :
    fderiv ℝ S.psi (S.phi u) (fderiv ℝ S.phi u h) = h := by
  have hev : S.psi ∘ S.phi =ᶠ[𝓝 u] id :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hu) fun v hv => S.psi_phi v hv
  have h1 := fderiv_comp u (S.diff_psi (S.phi_maps hu)) (S.diff_phi hu)
  rw [hev.fderiv_eq, fderiv_id] at h1
  have h2 := DFunLike.congr_fun h1 h
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at h2
  exact h2.symm

lemma Dphi_Dpsi {z : K} (hz : z ∈ S.BK) (k : K) :
    fderiv ℝ S.phi (S.psi z) (fderiv ℝ S.psi z k) = k := by
  have hev : S.phi ∘ S.psi =ᶠ[𝓝 z] id :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => S.phi_psi w hw
  have h1 := fderiv_comp z (S.diff_phi (S.psi_maps hz)) (S.diff_psi hz)
  rw [hev.fderiv_eq, fderiv_id] at h1
  have h2 := DFunLike.congr_fun h1 k
  simp only [ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply] at h2
  exact h2.symm

/-- `Dφ(u)` is onto: `Dφ(u) Dψ(φ u) = id`. -/
lemma Dphi_Dpsi' {u : H} (hu : u ∈ S.B) (k : K) :
    fderiv ℝ S.phi u (fderiv ℝ S.psi (S.phi u) k) = k := by
  have h := S.Dphi_Dpsi (S.phi_maps hu) k
  rwa [S.psi_phi u hu] at h

/-- **First step**: summing the action identities, `‖φ(u)‖_K = ‖u‖_H`. -/
lemma norm_phi {u : H} (hu : u ∈ S.B) : ‖S.phi u‖ = ‖u‖ := by
  have h1 : ‖S.phi u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_K, ← S.act_mass u]
    exact tsum_congr fun n => S.phi_q u hu n
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

lemma norm_rho (θ : Tor) (u : H) : ‖S.rho θ u‖ = ‖u‖ := by
  have h1 : ‖S.rho θ u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [← S.act_mass, ← S.act_mass, S.rho_act]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1

lemma rho_mem (θ : Tor) {u : H} (hu : u ∈ S.B) : S.rho θ u ∈ S.B := by
  rw [mem_ball_zero_iff] at hu ⊢; rwa [S.norm_rho]

lemma CH_mem {u : H} (hu : u ∈ S.B) : S.CH u ∈ S.B := by
  rw [mem_ball_zero_iff] at hu ⊢; rwa [LinearIsometry.norm_map]

lemma Rot_mem (θ : Tor) {z : K} (hz : z ∈ S.BK) : Rot θ z ∈ S.BK := by
  rw [mem_ball_zero_iff] at hz ⊢; rwa [norm_Rot]

lemma star_mem {z : K} (hz : z ∈ S.BK) : star z ∈ S.BK := by
  rw [mem_ball_zero_iff] at hz ⊢; rwa [norm_star]

/-- **Second step**: `Dφ(u) X_{I_n}(u) = X_{q_n}(φ(u))` on `B_ε(H)`. -/
lemma Dphi_X {u : H} (hu : u ∈ S.B) (n : ℤ) :
    fderiv ℝ S.phi u (hamField (fun v => S.act v n) u) = Xq n (S.phi u) := by
  have hev : (fun v => S.act v n) =ᶠ[𝓝 u] (q n ∘ S.phi) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hu) fun v hv => (S.phi_q v hv n).symm
  have hd : fderiv ℝ (fun v => S.act v n) u =
      (fderiv ℝ (q n) (S.phi u)).comp (fderiv ℝ S.phi u) := by
    rw [hev.fderiv_eq, fderiv_comp u (hasFDerivAt_q n _).differentiableAt (S.diff_phi hu)]
  refine omega_eq_of_forall fun k => ?_
  rw [← S.Dphi_Dpsi' hu k, S.phi_symp u hu, omega_hamField, hd, ContinuousLinearMap.comp_apply,
    omega_Xq_eq_fderiv]

/-- Single-coordinate conjugacy `φ ρ_{t e_n} = R_{t e_n} φ`, by uniqueness for `ż = X_{q_n}(z)`. -/
lemma single_conj {u : H} (hu : u ∈ S.B) (n : ℤ) (t : ℝ) :
    S.phi (S.rho (Pi.single n (t : Real.Angle)) u) = Rot (Pi.single n (t : Real.Angle)) (S.phi u) := by
  have huniq := ODE_solution_unique_univ (v := fun _ : ℝ => Xq n) (s := fun _ => Set.univ)
    (K := 1) (f := fun s : ℝ => S.phi (S.rho (Pi.single n (s : Real.Angle)) u))
    (g := fun s : ℝ => Rot (Pi.single n (s : Real.Angle)) (S.phi u)) (t₀ := 0)
    (fun _ => (lipschitz_Xq n).lipschitzOnWith) (fun s => ⟨?_, trivial⟩)
    (fun s => ⟨hasDerivAt_Rot_single n (S.phi u) s, trivial⟩) ?_
  · exact congrFun huniq t
  · have hmem := S.rho_mem (Pi.single n (s : Real.Angle)) hu
    have h1 := (S.diff_phi hmem).hasFDerivAt.comp_hasDerivAt s (S.rho_flow n u s)
    rw [S.Dphi_X hmem n] at h1
    exact h1
  · simp only [Real.Angle.coe_zero, Pi.single_zero, S.rho_zero, id, Rot_zero]

lemma finite_conj (F : Finset ℤ) (θ : Tor) : ∀ u ∈ S.B,
    S.phi (S.rho (∑ n ∈ F, Pi.single n (θ n)) u) = Rot (∑ n ∈ F, Pi.single n (θ n)) (S.phi u) := by
  classical
  induction F using Finset.induction_on with
  | empty => intro u hu; simp only [Finset.sum_empty, S.rho_zero, id, Rot_zero]
  | insert a F ha ih =>
    intro u hu
    rw [Finset.sum_insert ha, S.rho_add, Function.comp_apply, Rot_add]
    obtain ⟨t, ht⟩ := angle_surj (θ a)
    have hmem := S.rho_mem (∑ n ∈ F, Pi.single n (θ n)) hu
    rw [← ht, S.single_conj hmem, ih u hu]

/-- **Torus conjugacy** `φ ρ_θ = R_θ φ` on `B_ε(H)` for every `θ`: finitely supported angles, then
density and joint continuity. -/
lemma full_conj {u : H} (hu : u ∈ S.B) (θ : Tor) : S.phi (S.rho θ u) = Rot θ (S.phi u) := by
  have hc : Tendsto (fun N => S.rho (trunc θ N) u) atTop (𝓝 (S.rho θ u)) :=
    (S.rho_cont.tendsto (θ, u)).comp ((tendsto_trunc θ).prodMk_nhds tendsto_const_nhds)
  have h1 : Tendsto (fun N => S.phi (S.rho (trunc θ N) u)) atTop (𝓝 (S.phi (S.rho θ u))) :=
    ((S.diff_phi (S.rho_mem θ hu)).continuousAt.tendsto).comp hc
  have h2 : (fun N => S.phi (S.rho (trunc θ N) u)) = fun N => Rot (trunc θ N) (S.phi u) :=
    funext fun N => S.finite_conj (Finset.Icc (-(N : ℤ)) N) θ u hu
  rw [h2] at h1
  exact tendsto_nhds_unique h1 (tendsto_Rot_trunc θ (S.phi u))

lemma psi_rot {z : K} (hz : z ∈ S.BK) (θ : Tor) : S.psi (Rot θ z) = S.rho θ (S.psi z) := by
  have hu := S.psi_maps hz
  have h := S.full_conj hu θ
  rw [S.phi_psi z hz] at h
  rw [← h, S.psi_phi _ (S.rho_mem θ hu)]

lemma psi_conj {z : K} (hz : z ∈ S.BK) : S.psi (star z) = S.CH (S.psi z) := by
  have hu := S.psi_maps hz
  have h := S.phi_CH _ hu
  rw [S.phi_psi z hz] at h
  rw [← h, S.psi_phi _ (S.CH_mem hu)]

lemma Dpsi_X {z : K} (hz : z ∈ S.BK) (n : ℤ) :
    fderiv ℝ S.psi z (Xq n z) = hamField (fun v => S.act v n) (S.psi z) := by
  have hu := S.psi_maps hz
  have h := S.Dphi_X hu n
  rw [S.phi_psi z hz] at h
  rw [← h]
  have h2 := S.Dpsi_Dphi hu (hamField (fun v => S.act v n) (S.psi z))
  rwa [S.phi_psi z hz] at h2

/-- `β = (φ⁻¹)^*ᾱ − α_K` on `B_ε(K)`. -/
def beta (z : K) : K →L[ℝ] ℝ := (S.abar (S.psi z)).comp (fderiv ℝ S.psi z) - alphaK z

lemma beta_apply (z k : K) :
    S.beta z k = S.abar (S.psi z) (fderiv ℝ S.psi z k) - alphaF z k := rfl

/-- `β` is invariant under every `R_θ`. -/
lemma beta_rot {z : K} (hz : z ∈ S.BK) (θ : Tor) (k : K) :
    S.beta (Rot θ z) (Rot θ k) = S.beta z k := by
  have hRz := S.Rot_mem θ hz
  have hev : S.psi ∘ (Rot θ) =ᶠ[𝓝 z] S.rho θ ∘ S.psi :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => S.psi_rot hw θ
  have hA : HasFDerivAt (S.psi ∘ (Rot θ))
      ((fderiv ℝ S.psi (Rot θ z)).comp ((Rot θ).restrictScalars ℝ)) z :=
    (S.diff_psi hRz).hasFDerivAt.comp z ((Rot θ).hasFDerivAt.restrictScalars ℝ)
  have hB : HasFDerivAt (S.rho θ ∘ S.psi)
      ((fderiv ℝ (S.rho θ) (S.psi z)).comp (fderiv ℝ S.psi z)) z :=
    ((S.rho_symp θ).differentiable _).hasFDerivAt.comp z (S.diff_psi hz).hasFDerivAt
  have hk := DFunLike.congr_fun ((hA.congr_of_eventuallyEq hev.symm).unique hB) k
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] at hk
  rw [beta_apply, beta_apply, hk, S.psi_rot hz θ, S.abar_inv, alpha_Rot]

/-- `β(X_{q_n}) = 0`. -/
lemma beta_X {z : K} (hz : z ∈ S.BK) (n : ℤ) : S.beta z (Xq n z) = 0 := by
  rw [beta_apply, S.Dpsi_X hz n, S.abar_X, alpha_Xq]
  have h := S.phi_q _ (S.psi_maps hz) n
  rw [S.phi_psi z hz] at h
  rw [h]; ring

/-- `C_K^*β = −β`. -/
lemma beta_conj {z : K} (hz : z ∈ S.BK) (k : K) : S.beta (star z) (star k) = -S.beta z k := by
  have hsz := S.star_mem hz
  have hev : S.psi ∘ conjK =ᶠ[𝓝 z] S.CH ∘ S.psi :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds hz) fun w hw => S.psi_conj hw
  have hA : HasFDerivAt (S.psi ∘ conjK) ((fderiv ℝ S.psi (conjK z)).comp conjK) z :=
    (S.diff_psi hsz).hasFDerivAt.comp z conjK.hasFDerivAt
  have hB : HasFDerivAt (S.CH ∘ S.psi)
      (S.CH.toContinuousLinearMap.comp (fderiv ℝ S.psi z)) z :=
    S.CH.toContinuousLinearMap.hasFDerivAt.comp z (S.diff_psi hz).hasFDerivAt
  have hk := DFunLike.congr_fun ((hA.congr_of_eventuallyEq hev.symm).unique hB) k
  simp only [ContinuousLinearMap.comp_apply, conjK_apply,
    LinearIsometry.coe_toContinuousLinearMap] at hk
  rw [beta_apply, beta_apply, hk, S.psi_conj hz, S.abar_CH, alpha_star]
  ring

/-- `β_r(i e_n) = 0` at a point with real coordinates (both the positive and the collapsed case). -/
lemma beta_ie {r : K} (hr : r ∈ S.BK) (hre : ∀ n, (r n).im = 0) (n : ℤ) :
    S.beta r (lp.single 2 n Complex.I) = 0 := by
  by_cases h0 : r n = 0
  · -- collapsed coordinate: rotate the `n`th coordinate by `π`
    set θ : Tor := Pi.single n (Real.pi : Real.Angle)
    have hRr : Rot θ r = r := lp.ext (funext fun m => by
      rw [Rot_apply]
      by_cases hm : m = n
      · subst hm; rw [h0, mul_zero]
      · simp only [θ, Pi.single_eq_of_ne hm, ph_zero, one_mul])
    have hRs : Rot θ (lp.single 2 n Complex.I) = -lp.single 2 n Complex.I :=
      lp.ext (funext fun m => by
        rw [Rot_apply, lp.coeFn_neg, Pi.neg_apply]
        by_cases hm : m = n
        · subst hm; simp only [θ, Pi.single_eq_same, lp.single_apply_self, ph_pi]; ring
        · simp only [θ, Pi.single_eq_of_ne hm, lp.single_apply_ne _ _ _ hm, ph_zero]; ring)
    have h := S.beta_rot hr θ (lp.single 2 n Complex.I)
    rw [hRr, hRs, map_neg] at h
    linarith
  · -- positive coordinate: `X_{q_n}(r) = −r_n · i e_n`
    have hX : Xq n r = (-(r n).re) • lp.single 2 n Complex.I := by
      rw [Xq, ← lp.single_smul]
      congr 1
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hre n]
    have h := S.beta_X hr n
    rw [hX, map_smul, smul_eq_mul] at h
    have hne : (r n).re ≠ 0 := fun h' => h0 (Complex.ext (by simpa using h') (by simpa using hre n))
    exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hne)

/-- `β_r = 0` at a point with real coordinates. -/
lemma beta_real {r : K} (hr : r ∈ S.BK) (hre : ∀ n, (r n).im = 0) (k : K) : S.beta r k = 0 := by
  have hstar : star r = r := lp.ext (funext fun n => by
    rw [lp.star_apply, Complex.star_def, Complex.conj_eq_iff_im.mpr (hre n)])
  -- real sequences
  have hreal : ∀ a : K, star a = a → S.beta r a = 0 := fun a ha => by
    have h := S.beta_conj hr a
    rw [hstar, ha] at h
    linarith
  set a : K := (2⁻¹ : ℂ) • (k + star k)
  set b : K := (2⁻¹ : ℂ) • (k - star k)
  have hab : k = a + b := lp.ext (funext fun n => by
    simp only [a, b, lp.coeFn_add, lp.coeFn_smul, lp.coeFn_sub, Pi.add_apply, Pi.smul_apply,
      Pi.sub_apply, smul_eq_mul]
    ring)
  have ha : star a = a := lp.ext (funext fun n => by
    simp only [a, lp.star_apply, lp.coeFn_smul, lp.coeFn_add, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, star_mul', star_add, Complex.star_def, Complex.conj_conj, map_inv₀, map_ofNat]
    ring)
  -- purely imaginary part: a limit of real combinations of the `i e_n`
  have hb : S.beta r b = 0 := by
    have hs := (S.beta r).hasSum (lp.hasSum_single (p := 2) (by norm_num) b)
    have hterm : ∀ n, (lp.single 2 n (b n) : K) = ((k n).im : ℝ) • (lp.single 2 n Complex.I : K) := by
      intro n
      rw [← lp.single_smul]
      congr 1
      simp only [b, lp.coeFn_smul, lp.coeFn_sub, lp.star_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Complex.star_def, Complex.sub_conj, Complex.real_smul]
      push_cast; ring
    have hz : (fun n => S.beta r (lp.single 2 n (b n))) = fun _ => 0 := funext fun n => by
      rw [hterm, map_smul, S.beta_ie hr hre n, smul_zero]
    rw [hz] at hs
    exact hs.unique hasSum_zero
  rw [hab, map_add, hreal a ha, hb, add_zero]

/-- `β = 0` on `B_ε(K)`: rotate `z` to `(|z_n|)_n`. -/
lemma beta_zero {z : K} (hz : z ∈ S.BK) (k : K) : S.beta z k = 0 := by
  set θ : Tor := fun n => (Complex.arg (z n) : Real.Angle)
  have hre : ∀ n, (Rot θ z n).im = 0 := fun n => by
    rw [Rot_apply, ph_arg_mul, Complex.ofReal_im]
  rw [← S.beta_rot hz θ k]
  exact S.beta_real (S.Rot_mem θ hz) hre _

/-- **`eq:global-D01-local-primitive`**: `φ^*α_K = ᾱ` on `B_ε(H)`. -/
theorem local_primitive {u : H} (hu : u ∈ S.B) (h : H) :
    alphaF (S.phi u) (fderiv ℝ S.phi u h) = S.abar u h := by
  have := S.beta_zero (S.phi_maps hu) (fderiv ℝ S.phi u h)
  rw [beta_apply, S.Dpsi_Dphi hu h, S.psi_phi u hu] at this
  linarith

/-- **Consequence**: `Dφ(u) Y(u) = φ(u)/2` on `B_ε(H)`. -/
theorem Dphi_Y {u : H} (hu : u ∈ S.B) : fderiv ℝ S.phi u (S.Y u) = (2⁻¹ : ℂ) • S.phi u := by
  refine omega_eq_of_forall fun k => ?_
  rw [← S.Dphi_Dpsi' hu k, S.phi_symp u hu, Y, omega_Winv, omega_half, S.local_primitive hu]

end Hyp

/-- **`lem:global-D01-local-primitive` (R-81E9AAB6).** Under the hypotheses of
`thm:global-D01-reconstruction` (`Hyp`), on `B_ε(H)`: `‖φ(u)‖ = ‖u‖`;
`Dφ(u) X_{I_n}(u) = X_{q_n}(φ(u))` (with `X_{q_n}(z) = −i z_n e_n` DEF-015's field of `q_n`);
`φ ρ_θ = R_θ φ` for every `θ ∈ 𝕋^ℤ`; `φ^*α_K = ᾱ`; and `Dφ(u) Y(u) = φ(u)/2`, `Y = W⁻¹ᾱ`. -/
theorem local_primitive_lemma {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Hyp H) :
    (∀ u ∈ S.B, ‖S.phi u‖ = ‖u‖) ∧
    (∀ (n : ℤ) (z : K), hamField (q n) z = Xq n z) ∧
    (∀ u ∈ S.B, ∀ n : ℤ, fderiv ℝ S.phi u (hamField (fun v => S.act v n) u) = Xq n (S.phi u)) ∧
    (∀ u ∈ S.B, ∀ θ : Tor, S.phi (S.rho θ u) = Rot θ (S.phi u)) ∧
    (∀ u ∈ S.B, ∀ h : H, alphaF (S.phi u) (fderiv ℝ S.phi u h) = S.abar u h) ∧
    (∀ u ∈ S.B, ∀ h : H, omega (S.Y u) h = S.abar u h) ∧
    (∀ u ∈ S.B, fderiv ℝ S.phi u (S.Y u) = (2⁻¹ : ℂ) • S.phi u) :=
  ⟨fun _ hu => S.norm_phi hu, hamField_q, fun _ hu n => S.Dphi_X hu n,
    fun _ hu θ => S.full_conj hu θ, fun _ hu h => S.local_primitive hu h,
    fun u _ h => omega_Winv (S.abar u) h, fun _ hu => S.Dphi_Y hu⟩

#print axioms Hyp.Dphi_X
#print axioms Hyp.full_conj
#print axioms Hyp.beta_real
#print axioms Hyp.local_primitive
#print axioms Hyp.Dphi_Y
#print axioms local_primitive_lemma

end QuantumNLS.D01LocalPrimitive
