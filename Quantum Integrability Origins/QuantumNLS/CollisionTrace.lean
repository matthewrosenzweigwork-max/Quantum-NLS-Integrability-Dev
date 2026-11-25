import QuantumNLS.PhysicalEnergy

/-!
# R-C21B75F5 `contact:lem:trace`: the collision trace `T_ij : H¹(T_L^N) → L²(T_L^{N-1})`

Source (pinned PR11 `3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f`, `chapters/foundations/A01.tex:13`):
"The map `T_ij` extends continuously from smooth functions to `H¹(T_L^N)` with values in
`L²(T_L^{N-1})`. For every `ε > 0`,  `‖T_ijψ‖₂² ≤ ε‖∂_iψ‖₂² + (L^{-1} + ε^{-1})‖ψ‖₂²`."
`T_ij ψ` is the restriction of `ψ` to `Σ_ij = {x_i = x_j}`, parametrized by the common coordinate
`t = x_i = x_j` and the other `N-2` coordinates.

Proof route followed here (source: "FTC along the circle in `x_i`, average, `2ab ≤ εa² + ε⁻¹b²`"):
* §1 the one-variable inequality at a point for exponential polynomials, by the source's real-space
  fundamental-theorem-of-calculus argument: `|v(0)|² ≤ ε‖v'‖² + (L⁻¹+ε⁻¹)‖v‖²`; read on Fourier
  coefficients it says `|Σ_a c_a|² ≤ L Σ_a ω_a |c_a|²`, `ω_a = ε(2πa/L)² + L⁻¹ + ε⁻¹`.
* later sections: the trace on the Fourier side (sums over the antidiagonal `w_i + w_j = s`),
  the `k`-dimensional bound by Cauchy–Schwarz on each fiber (no real-space Fubini), agreement
  with the genuine restriction on trigonometric polynomials, and the continuous extension.

No `sorry`, no custom axioms.
-/

set_option autoImplicit false

noncomputable section

open scoped ComplexConjugate Real InnerProductSpace
open MeasureTheory

namespace QuantumNLS.CollisionTrace

/-! ## §1 The one-variable inequality for exponential polynomials -/

section OneD

variable (L : ℝ)

/-- `v(x) = Σ_{a∈S} c_a e^{i p_a x}`, `p_a = 2πa/L`: a trigonometric polynomial (unnormalized modes). -/
def expPoly (S : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ a ∈ S, c a * Complex.exp (Complex.I * ((2 * Real.pi * a / L : ℝ) : ℂ) * (x : ℂ))

/-- `v'` is again an exponential polynomial, with coefficients `i p_a c_a`. -/
def expPolyDeriv (_S : Finset ℤ) (c : ℤ → ℂ) : ℤ → ℂ :=
  fun a => c a * (Complex.I * ((2 * Real.pi * a / L : ℝ) : ℂ))

theorem hasDerivAt_expPoly (S : Finset ℤ) (c : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (expPoly L S c) (expPoly L S (expPolyDeriv L S c) x) x := by
  unfold expPoly expPolyDeriv
  refine HasDerivAt.fun_sum fun a _ => ?_
  have h := ((hasDerivAt_id' x).ofReal_comp.const_mul
    (Complex.I * ((2 * Real.pi * a / L : ℝ) : ℂ))).cexp.const_mul (c a)
  convert h using 1
  simp only [Complex.ofReal_one, mul_one]
  ring

theorem continuous_expPoly (S : Finset ℤ) (c : ℤ → ℂ) : Continuous (expPoly L S c) := by
  unfold expPoly
  fun_prop

/-- Periodicity: `v(L) = v(0)` when `L ≠ 0` (all frequencies are multiples of `2π/L`). -/
theorem expPoly_period (hL : L ≠ 0) (S : Finset ℤ) (c : ℤ → ℂ) :
    expPoly L S c L = expPoly L S c 0 := by
  unfold expPoly
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : Complex.I * ((2 * Real.pi * a / L : ℝ) : ℂ) * (L : ℂ) = (a : ℂ) * (2 * Real.pi * Complex.I) := by
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    push_cast
    field_simp
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
  simp

/-- `∫₀^L e^{i(2πm/L)x} dx = L·[m = 0]`. -/
theorem integral_exp_int (hL : 0 < L) (m : ℤ) :
    ∫ x in (0 : ℝ)..L, Complex.exp (Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ) * (x : ℂ)) =
      if m = 0 then (L : ℂ) else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hc : Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ) ≠ 0 := by
      push_cast
      simp [Complex.I_ne_zero, hmc, hpi, hLc]
    have h1 : ∀ x : ℝ, Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ) * (x : ℂ) =
        (Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ)) * (x : ℂ) := fun x => rfl
    rw [show (if m = 0 then (L : ℂ) else 0) = 0 from by simp [hm]]
    have := integral_exp_mul_complex (a := (0 : ℝ)) (b := L) hc
    rw [this]
    have h2 : Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ) * (L : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
    simp

theorem conj_exp_mul_exp (a b : ℤ) (x : ℝ) :
    conj (Complex.exp (Complex.I * ((2 * Real.pi * a / L : ℝ) : ℂ) * (x : ℂ))) *
        Complex.exp (Complex.I * ((2 * Real.pi * b / L : ℝ) : ℂ) * (x : ℂ)) =
      Complex.exp (Complex.I * ((2 * Real.pi * ((b - a : ℤ) : ℝ) / L : ℝ) : ℂ) * (x : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- **Plancherel for exponential polynomials**: `∫₀^L |v|² = L Σ |c_a|²`. -/
theorem integral_normSq_expPoly (hL : 0 < L) (S : Finset ℤ) (c : ℤ → ℂ) :
    ∫ x in (0 : ℝ)..L, ‖expPoly L S c x‖ ^ 2 = L * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h1 : ∀ x : ℝ, ((‖expPoly L S c x‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ S, ∑ b ∈ S, conj (c a) * c b *
        Complex.exp (Complex.I * ((2 * Real.pi * ((b - a : ℤ) : ℝ) / L : ℝ) : ℂ) * (x : ℂ)) := by
    intro x
    rw [Complex.ofReal_pow, ← Complex.conj_mul' (expPoly L S c x)]
    unfold expPoly
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul, ← conj_exp_mul_exp L a b x]
    ring
  simp_rw [h1]
  have hint : ∀ a ∈ S, ∀ b ∈ S, IntervalIntegrable (fun x : ℝ => conj (c a) * c b *
      Complex.exp (Complex.I * ((2 * Real.pi * ((b - a : ℤ) : ℝ) / L : ℝ) : ℂ) * (x : ℂ)))
      MeasureTheory.volume 0 L := fun a _ b _ => by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun a ha => ?_)]
  · have h2 : ∀ a ∈ S, ∫ x in (0 : ℝ)..L, ∑ b ∈ S, conj (c a) * c b *
        Complex.exp (Complex.I * ((2 * Real.pi * ((b - a : ℤ) : ℝ) / L : ℝ) : ℂ) * (x : ℂ)) =
        (L : ℂ) * (‖c a‖ ^ 2 : ℝ) := by
      intro a ha
      rw [intervalIntegral.integral_finsetSum (fun b hb => hint a ha b hb)]
      simp_rw [intervalIntegral.integral_const_mul, integral_exp_int L hL]
      rw [Finset.sum_eq_single a]
      · simp [Complex.conj_mul']
        ring
      · intro b _ hba
        have : (b - a : ℤ) ≠ 0 := sub_ne_zero.2 hba
        simp [this]
      · intro h; exact absurd ha h
    rw [Finset.sum_congr rfl h2]
    push_cast
    rw [Finset.mul_sum]
  · apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ (fun b _ => by fun_prop)

theorem two_mul_le_aux {ε a b : ℝ} (hε : 0 < ε) : 2 * (a * b) ≤ ε * b ^ 2 + ε⁻¹ * a ^ 2 := by
  have h := mul_nonneg (inv_nonneg.2 hε.le) (sq_nonneg (ε * b - a))
  have e : ε⁻¹ * (ε * b - a) ^ 2 = ε * b ^ 2 - 2 * (a * b) + ε⁻¹ * a ^ 2 := by
    field_simp
    ring
  linarith

/-- **The source's one-variable estimate** `|v(0)|² ≤ ε‖v'‖² + (L⁻¹+ε⁻¹)‖v‖²` (FTC along the circle,
average in the base point, `2ab ≤ εb² + ε⁻¹a²`) read on coefficients:
`|Σ_a c_a|² ≤ L Σ_a (ε p_a² + L⁻¹ + ε⁻¹)|c_a|²` with `p_a = 2πa/L`. -/
theorem sum_sq_le (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) (S : Finset ℤ) (c : ℤ → ℂ) :
    ‖∑ a ∈ S, c a‖ ^ 2 ≤
      L * ∑ a ∈ S, (ε * (2 * Real.pi * a / L) ^ 2 + L⁻¹ + ε⁻¹) * ‖c a‖ ^ 2 := by
  set v := expPoly L S c with hv
  set v' := expPoly L S (expPolyDeriv L S c) with hv'
  have hv0 : v 0 = ∑ a ∈ S, c a := by
    simp [hv, expPoly]
  have hcont : Continuous v := continuous_expPoly L S c
  have hcont' : Continuous v' := continuous_expPoly L S _
  set I0 : ℝ := ∫ x in (0 : ℝ)..L, ‖v x‖ ^ 2 with hI0
  set I1 : ℝ := ∫ x in (0 : ℝ)..L, ‖v' x‖ ^ 2 with hI1
  have hI0e : I0 = L * ∑ a ∈ S, ‖c a‖ ^ 2 := integral_normSq_expPoly L hL S c
  have hI1e : I1 = L * ∑ a ∈ S, (2 * Real.pi * a / L) ^ 2 * ‖c a‖ ^ 2 := by
    rw [hI1, hv', integral_normSq_expPoly L hL S (expPolyDeriv L S c)]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    unfold expPolyDeriv
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  -- the integrand bounding the derivative of `‖v‖²`
  set g : ℝ → ℝ := fun x => ε * ‖v' x‖ ^ 2 + ε⁻¹ * ‖v x‖ ^ 2 with hg
  have hgc : Continuous g := by
    have := hcont.norm; have := hcont'.norm
    fun_prop
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    have := hε.le
    positivity
  have hgint : ∫ x in (0 : ℝ)..L, g x = ε * I1 + ε⁻¹ * I0 := by
    simp only [hg]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · exact (Continuous.intervalIntegrable (by have := hcont'.norm; fun_prop) _ _)
    · exact (Continuous.intervalIntegrable (by have := hcont.norm; fun_prop) _ _)
  -- FTC from `s` to `L`
  have hftc : ∀ s ∈ Set.Icc (0 : ℝ) L, ‖v L‖ ^ 2 ≤ ‖v s‖ ^ 2 + (ε * I1 + ε⁻¹ * I0) := by
    intro s hs
    have hderiv : ∀ x ∈ Set.uIcc s L, HasDerivAt (fun x => ‖v x‖ ^ 2)
        (2 * inner ℝ (v x) (v' x)) x := fun x _ => (hasDerivAt_expPoly L S c x).norm_sq
    have hcf' : Continuous fun x => 2 * inner ℝ (v x) (v' x) := by
      fun_prop
    have h1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcf'.intervalIntegrable s L)
    have h2 : ∫ x in s..L, 2 * inner ℝ (v x) (v' x) ≤ ∫ x in s..L, g x := by
      refine intervalIntegral.integral_mono_on hs.2 (hcf'.intervalIntegrable s L)
        (hgc.intervalIntegrable s L) fun x _ => ?_
      have hi : inner ℝ (v x) (v' x) ≤ ‖v x‖ * ‖v' x‖ := real_inner_le_norm _ _
      have := two_mul_le_aux (ε := ε) (a := ‖v x‖) (b := ‖v' x‖) hε
      simp only [hg]
      linarith
    have h3 : ∫ x in s..L, g x ≤ ∫ x in (0 : ℝ)..L, g x :=
      intervalIntegral.integral_mono_interval hs.1 hs.2 le_rfl
        (Filter.Eventually.of_forall hg0) (hgc.intervalIntegrable 0 L)
    linarith
  -- average in `s`
  have hvc : Continuous fun s => ‖v s‖ ^ 2 := by
    have := hcont.norm
    fun_prop
  have hmain : L * ‖v L‖ ^ 2 ≤ I0 + L * (ε * I1 + ε⁻¹ * I0) := by
    have hle : ∫ s in (0 : ℝ)..L, ‖v L‖ ^ 2 ≤
        ∫ s in (0 : ℝ)..L, (‖v s‖ ^ 2 + (ε * I1 + ε⁻¹ * I0)) :=
      intervalIntegral.integral_mono_on hL.le intervalIntegrable_const
        ((hvc.intervalIntegrable 0 L).add intervalIntegrable_const)
        fun s hs => hftc s hs
    rw [intervalIntegral.integral_const, intervalIntegral.integral_add
      (hvc.intervalIntegrable 0 L) intervalIntegrable_const,
      intervalIntegral.integral_const] at hle
    simp only [sub_zero, smul_eq_mul] at hle
    linarith
  have hvL : v L = v 0 := expPoly_period L hL.ne' S c
  rw [hvL, hv0] at hmain
  set A : ℝ := ∑ a ∈ S, ‖c a‖ ^ 2 with hA
  set B : ℝ := ∑ a ∈ S, (2 * Real.pi * a / L) ^ 2 * ‖c a‖ ^ 2 with hB
  have hsum : ∑ a ∈ S, (ε * (2 * Real.pi * a / L) ^ 2 + L⁻¹ + ε⁻¹) * ‖c a‖ ^ 2 =
      ε * B + L⁻¹ * A + ε⁻¹ * A := by
    have : ∀ a : ℤ, (ε * (2 * Real.pi * a / L) ^ 2 + L⁻¹ + ε⁻¹) * ‖c a‖ ^ 2 =
        ε * ((2 * Real.pi * a / L) ^ 2 * ‖c a‖ ^ 2) + L⁻¹ * ‖c a‖ ^ 2 + ε⁻¹ * ‖c a‖ ^ 2 :=
      fun a => by ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
    rfl
  rw [hsum]
  rw [hI0e, hI1e] at hmain
  have hLne : L ≠ 0 := hL.ne'
  have key : L * ‖∑ a ∈ S, c a‖ ^ 2 ≤ L * (L * (ε * B + L⁻¹ * A + ε⁻¹ * A)) := by
    have e : L * (L * (ε * B + L⁻¹ * A + ε⁻¹ * A)) =
        L * A + L * (ε * (L * B) + ε⁻¹ * (L * A)) := by
      field_simp
      ring
    rw [e]
    exact hmain
  exact le_of_mul_le_mul_left key hL

end OneD

/-! ## §2 The one-variable bound for square-summable coefficient sequences -/

section Series

variable (L : ℝ)

/-- The weight `ω_a = ε (2πa/L)² + L⁻¹ + ε⁻¹`. -/
def omega (ε : ℝ) (a : ℤ) : ℝ := ε * (2 * Real.pi * a / L) ^ 2 + L⁻¹ + ε⁻¹

theorem omega_pos (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) (a : ℤ) : 0 < omega L ε a := by
  unfold omega
  positivity

/-- **§1 for infinite sequences** (by partial sums): if `Σ ω_a |c_a|² < ∞` then `Σ |c_a| < ∞` and
`|Σ c_a|² ≤ L Σ ω_a |c_a|²`. -/
theorem tsum_sq_le (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) (c : ℤ → ℂ)
    (hc : Summable fun a => omega L ε a * ‖c a‖ ^ 2) :
    Summable (fun a => ‖c a‖) ∧
      ‖∑' a, c a‖ ^ 2 ≤ L * ∑' a, omega L ε a * ‖c a‖ ^ 2 := by
  set T := ∑' a, omega L ε a * ‖c a‖ ^ 2 with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun a => mul_nonneg (omega_pos L hL hε a).le (sq_nonneg _)
  have hfin : ∀ S : Finset ℤ, (∑ a ∈ S, ‖c a‖) ^ 2 ≤ L * T := fun S => by
    have h1 := sum_sq_le L hL hε S (fun a => ((‖c a‖ : ℝ) : ℂ))
    have e : ‖∑ a ∈ S, ((‖c a‖ : ℝ) : ℂ)‖ = ∑ a ∈ S, ‖c a‖ := by
      rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_of_nonneg
        (Finset.sum_nonneg fun a _ => norm_nonneg _)]
    rw [e] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hL.le)
    calc ∑ a ∈ S, (ε * (2 * Real.pi * a / L) ^ 2 + L⁻¹ + ε⁻¹) * ‖((‖c a‖ : ℝ) : ℂ)‖ ^ 2
        = ∑ a ∈ S, omega L ε a * ‖c a‖ ^ 2 := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
          rfl
      _ ≤ T := hc.sum_le_tsum S fun a _ =>
          mul_nonneg (omega_pos L hL hε a).le (sq_nonneg _)
  have hbound : ∀ S : Finset ℤ, ∑ a ∈ S, ‖c a‖ ≤ Real.sqrt (L * T) := fun S =>
    Real.le_sqrt_of_sq_le (hfin S)
  have hsum : Summable fun a => ‖c a‖ := summable_of_sum_le (fun a => norm_nonneg _) hbound
  refine ⟨hsum, ?_⟩
  have h1 : ∑' a, ‖c a‖ ≤ Real.sqrt (L * T) := hsum.tsum_le_of_sum_le hbound
  have h2 : ‖∑' a, c a‖ ≤ ∑' a, ‖c a‖ := norm_tsum_le_tsum_norm hsum
  have h3 : ‖∑' a, c a‖ ≤ Real.sqrt (L * T) := h2.trans h1
  calc ‖∑' a, c a‖ ^ 2 ≤ Real.sqrt (L * T) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h3 2
    _ = L * T := Real.sq_sqrt (mul_nonneg hL.le hT0)

end Series

/-! ## §3 The antidiagonal reindexing `ℤ^N ≃ ℤ × (ℤ × ℤ^{N-2})` -/

section Index

variable {N : ℕ} (i j : Fin N)

/-- The coordinates other than `i` and `j`. -/
abbrev Rest (N : ℕ) (i j : Fin N) : Type := {l : Fin N // l ≠ i ∧ l ≠ j}

/-- The Fourier index set of `L²(T_L^{N-1})` seen from `Σ_ij`: the common-coordinate momentum
`s = w_i + w_j` and the momenta of the remaining `N-2` coordinates. -/
abbrev TIdx (N : ℕ) (i j : Fin N) : Type := ℤ × (Rest N i j → ℤ)

/-- `w ↦ (w_i, (w_i + w_j, (w_l)_{l ≠ i,j}))`: splits a momentum vector into the position along the
antidiagonal fibre and the fibre label. -/
def splitEquiv (hij : i ≠ j) : (Fin N → ℤ) ≃ ℤ × TIdx N i j where
  toFun w := (w i, (w i + w j, fun l => w l.1))
  invFun p := fun l => if h : l = i then p.1 else if h' : l = j then p.2.1 - p.1 else
    p.2.2 ⟨l, h, h'⟩
  left_inv w := by
    funext l
    by_cases h : l = i
    · subst h; simp
    · by_cases h' : l = j
      · subst h'; simp [h]
      · simp [h, h']
  right_inv p := by
    obtain ⟨a, s, m⟩ := p
    have hji : j ≠ i := hij.symm
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp [hji]
    · funext l
      obtain ⟨l, h1, h2⟩ := l
      simp [h1, h2]

/-- The antidiagonal fibre over `t = (s, m)`: `a ↦ (w_i = a, w_j = s - a, rest = m)`. -/
def fib (hij : i ≠ j) (t : TIdx N i j) (a : ℤ) : Fin N → ℤ := (splitEquiv i j hij).symm (a, t)

theorem fib_i (hij : i ≠ j) (t : TIdx N i j) (a : ℤ) : fib i j hij t a i = a := by
  simp [fib, splitEquiv]

theorem fib_j (hij : i ≠ j) (t : TIdx N i j) (a : ℤ) : fib i j hij t a j = t.1 - a := by
  simp [fib, splitEquiv, hij.symm]

theorem fib_injective (hij : i ≠ j) (t : TIdx N i j) : Function.Injective (fib i j hij t) := by
  intro a b h
  have := (splitEquiv i j hij).symm.injective h
  exact (Prod.mk.inj this).1

end Index

/-! ## §4 The trace on Fourier coefficients and the `N`-dimensional bound -/

section Trace

variable (L : ℝ) {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- Fibre reindexing `ℤ^N ≃ TIdx × ℤ`, `w ↦ ((w_i+w_j, rest), w_i)`. -/
def fibEquiv : (Fin N → ℤ) ≃ TIdx N i j × ℤ := (splitEquiv i j hij).trans (Equiv.prodComm _ _)

theorem fibEquiv_symm_apply (t : TIdx N i j) (a : ℤ) : (fibEquiv i j hij).symm (t, a) = fib i j hij t a :=
  rfl

/-- **The trace on Fourier coefficients.**  If `ψ = Σ_w c_w E_w`, `E_w = ∏_l e_{w_l}(x_l)`, then on
`Σ_ij = {x_i = x_j}`, with common coordinate `t`, `e_a(t)e_b(t) = L^{-1/2} e_{a+b}(t)`, so
`ψ|_{Σ_ij} = Σ_{(s,m)} (T c)(s,m) E'_{(s,m)}` with
`(T c)(s,m) = L^{-1/2} Σ_{a} c(w_i = a, w_j = s - a, rest = m)`  (sum over the antidiagonal). -/
def traceCoeff (c : (Fin N → ℤ) → ℂ) (t : TIdx N i j) : ℂ :=
  ((Real.sqrt L)⁻¹ : ℝ) * ∑' a, c (fib i j hij t a)

/-- **R-C21B75F5 on Fourier coefficients** (`‖∂_iψ‖² := Σ_w (2πw_i/L)²|ψ̂(w)|²`):
for every `ε > 0`, the fibre sums converge absolutely, the trace coefficients are square summable and
`‖Tψ‖² ≤ ε‖∂_iψ‖² + (L⁻¹+ε⁻¹)‖ψ‖²`. -/
theorem trace_bound (hL : 0 < L) {ε : ℝ} (hε : 0 < ε) (c : (Fin N → ℤ) → ℂ)
    (hc2 : Summable fun w => ‖c w‖ ^ 2)
    (hc1 : Summable fun w => (2 * Real.pi * (w i) / L) ^ 2 * ‖c w‖ ^ 2) :
    (∀ t, Summable fun a => ‖c (fib i j hij t a)‖) ∧
      Summable (fun t => ‖traceCoeff L i j hij c t‖ ^ 2) ∧
      ∑' t, ‖traceCoeff L i j hij c t‖ ^ 2 ≤
        ε * ∑' w, (2 * Real.pi * (w i) / L) ^ 2 * ‖c w‖ ^ 2 +
          (L⁻¹ + ε⁻¹) * ∑' w, ‖c w‖ ^ 2 := by
  set F : (Fin N → ℤ) → ℝ := fun w => omega L ε (w i) * ‖c w‖ ^ 2 with hFdef
  have hFe : ∀ w, F w = ε * ((2 * Real.pi * (w i) / L) ^ 2 * ‖c w‖ ^ 2) +
      (L⁻¹ + ε⁻¹) * ‖c w‖ ^ 2 := fun w => by simp only [hFdef, omega]; ring
  have hF : Summable F := by
    have := (hc1.mul_left ε).add (hc2.mul_left (L⁻¹ + ε⁻¹))
    exact this.congr fun w => (hFe w).symm
  have hF0 : ∀ w, 0 ≤ F w := fun w => mul_nonneg (omega_pos L hL hε _).le (sq_nonneg _)
  -- fibrewise inequality
  have hfib : ∀ t : TIdx N i j, Summable (fun a => ‖c (fib i j hij t a)‖) ∧
      ‖traceCoeff L i j hij c t‖ ^ 2 ≤ ∑' a, F (fib i j hij t a) := by
    intro t
    have hsum : Summable fun a => omega L ε a * ‖c (fib i j hij t a)‖ ^ 2 := by
      have := hF.comp_injective (fib_injective i j hij t)
      refine this.congr fun a => ?_
      simp only [Function.comp, hFdef, fib_i]
    obtain ⟨hs1, hs2⟩ := tsum_sq_le L hL hε (fun a => c (fib i j hij t a)) hsum
    refine ⟨hs1, ?_⟩
    have hLs : (Real.sqrt L)⁻¹ ^ 2 = L⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hL.le]
    have e : ‖traceCoeff L i j hij c t‖ ^ 2 =
        L⁻¹ * ‖∑' a, c (fib i j hij t a)‖ ^ 2 := by
      unfold traceCoeff
      rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hLs]
    rw [e]
    have e2 : ∑' a, omega L ε a * ‖c (fib i j hij t a)‖ ^ 2 = ∑' a, F (fib i j hij t a) := by
      refine tsum_congr fun a => ?_
      simp only [hFdef, fib_i]
    calc L⁻¹ * ‖∑' a, c (fib i j hij t a)‖ ^ 2
        ≤ L⁻¹ * (L * ∑' a, omega L ε a * ‖c (fib i j hij t a)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hs2 (inv_nonneg.2 hL.le)
      _ = ∑' a, F (fib i j hij t a) := by
          rw [e2, ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  -- sum over fibres
  have hF2 : Summable (F ∘ (fibEquiv i j hij).symm) :=
    ((fibEquiv i j hij).symm.summable_iff).2 hF
  have hG : Summable fun t : TIdx N i j => ∑' a, F (fib i j hij t a) := by
    have := hF2.prod
    exact this
  have hGsum : ∑' t : TIdx N i j, ∑' a, F (fib i j hij t a) = ∑' w, F w := by
    have h1 := hF2.tsum_prod
    have h0 : ∑' p, (F ∘ (fibEquiv i j hij).symm) p = ∑' w, F w :=
      (fibEquiv i j hij).symm.tsum_eq F
    rw [h0] at h1
    exact h1.symm
  have hnn : ∀ t : TIdx N i j, 0 ≤ ‖traceCoeff L i j hij c t‖ ^ 2 := fun t => sq_nonneg _
  have hsumT : Summable (fun t => ‖traceCoeff L i j hij c t‖ ^ 2) :=
    Summable.of_nonneg_of_le hnn (fun t => (hfib t).2) hG
  refine ⟨fun t => (hfib t).1, hsumT, ?_⟩
  calc ∑' t, ‖traceCoeff L i j hij c t‖ ^ 2 ≤ ∑' t : TIdx N i j, ∑' a, F (fib i j hij t a) :=
        hsumT.tsum_le_tsum (fun t => (hfib t).2) hG
    _ = ∑' w, F w := hGsum
    _ = ε * ∑' w, (2 * Real.pi * (w i) / L) ^ 2 * ‖c w‖ ^ 2 +
          (L⁻¹ + ε⁻¹) * ∑' w, ‖c w‖ ^ 2 := by
        simp_rw [hFe]
        rw [(hc1.mul_left ε).tsum_add (hc2.mul_left (L⁻¹ + ε⁻¹)), tsum_mul_left, tsum_mul_left]

end Trace

/-! ## §5 The collision trace `T_ij : H¹(T_L^N) → L²` on the physical `H¹` -/

section PhysTrace

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor

variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

/-- The Fourier coefficients `(x̂(w))_w` of an element of the physical `H¹`. -/
def coeffFun (x : PhysH1 L N) : (Fin N → ℤ) → ℂ := (momUnitary L N x.val : Mom N → ℂ)

theorem summable_coeffFun_sq (x : PhysH1 L N) : Summable fun w => ‖coeffFun x w‖ ^ 2 :=
  summable_sq (momUnitary L N x.val)

theorem summable_coeffFun_deriv (x : PhysH1 L N) :
    Summable fun w => (2 * Real.pi * (w i) / L) ^ 2 * ‖coeffFun x w‖ ^ 2 := by
  have h := summable_kin_term (show H1Dom L N from x) i
  have e : coeffFun x = ((show H1Dom L N from x).val : Mom N → ℂ) := by
    funext w
    unfold coeffFun
    rw [PhysH1.momUnitary_val]
  rw [e]
  exact h

omit [Fact (0 < L)] in
theorem traceCoeff_add (c d : (Fin N → ℤ) → ℂ)
    (hc : ∀ t, Summable fun a => ‖c (fib i j hij t a)‖)
    (hd : ∀ t, Summable fun a => ‖d (fib i j hij t a)‖) (t : TIdx N i j) :
    traceCoeff L i j hij (fun w => c w + d w) t =
      traceCoeff L i j hij c t + traceCoeff L i j hij d t := by
  unfold traceCoeff
  rw [← mul_add, ← (Summable.of_norm (hc t)).tsum_add (Summable.of_norm (hd t))]

omit [Fact (0 < L)] in
theorem traceCoeff_smul (r : ℂ) (c : (Fin N → ℤ) → ℂ) (t : TIdx N i j) :
    traceCoeff L i j hij (fun w => r * c w) t = r * traceCoeff L i j hij c t := by
  unfold traceCoeff
  rw [tsum_mul_left]
  ring

theorem memℓ_trace (x : PhysH1 L N) :
    Memℓp (traceCoeff L i j hij (coeffFun x)) 2 := by
  rw [memL2_iff]
  exact (trace_bound L i j hij (Fact.out : 0 < L) one_pos (coeffFun x)
    (summable_coeffFun_sq x) (summable_coeffFun_deriv i x)).2.1

theorem coeffFun_add (x y : PhysH1 L N) : coeffFun (x + y) = fun w => coeffFun x w + coeffFun y w := by
  funext w
  unfold coeffFun
  have : (x + y).val = x.val + y.val := (PhysH1.valₗ (L := L) (k := N)).map_add x y
  rw [this, map_add]
  rfl

theorem coeffFun_smul (r : ℂ) (x : PhysH1 L N) : coeffFun (r • x) = fun w => r * coeffFun x w := by
  funext w
  unfold coeffFun
  have : (r • x).val = r • x.val := (PhysH1.valₗ (L := L) (k := N)).map_smul r x
  rw [this, map_smul]
  rfl

/-- **The collision trace `T_ij` on `H¹(T_L^N)`**, constructed on Fourier coefficients (sums over the
antidiagonal `w_i + w_j = s`), valued in `ℓ²` of the Fourier index set `TIdx` of `L²(T_L^{N-1})`. -/
def traceMap : PhysH1 L N →ₗ[ℂ] L2 (TIdx N i j) where
  toFun x := ⟨traceCoeff L i j hij (coeffFun x), memℓ_trace i j hij x⟩
  map_add' x y := by
    apply Subtype.ext; funext t
    have hx := (trace_bound L i j hij (Fact.out : 0 < L) one_pos (coeffFun x)
      (summable_coeffFun_sq x) (summable_coeffFun_deriv i x)).1
    have hy := (trace_bound L i j hij (Fact.out : 0 < L) one_pos (coeffFun y)
      (summable_coeffFun_sq y) (summable_coeffFun_deriv i y)).1
    show traceCoeff L i j hij (coeffFun (x + y)) t = _ + _
    rw [coeffFun_add, traceCoeff_add i j hij _ _ hx hy]
  map_smul' r x := by
    apply Subtype.ext; funext t
    show traceCoeff L i j hij (coeffFun (r • x)) t = r * _
    rw [coeffFun_smul, traceCoeff_smul]

theorem traceMap_apply (x : PhysH1 L N) (t : TIdx N i j) :
    ((traceMap i j hij x : L2 (TIdx N i j)) : TIdx N i j → ℂ) t =
      traceCoeff L i j hij (coeffFun x) t := rfl

/-- **R-C21B75F5, trace estimate on the physical `H¹(T_L^N)`**: for every `ε > 0`,
`‖T_ij ψ‖² ≤ ε ‖∂_iψ‖² + (L⁻¹ + ε⁻¹) ‖ψ‖²`, where `‖∂_iψ‖² = Σ_w (2πw_i/L)²|ψ̂(w)|²` and
`‖ψ‖` is the `L²(T_L^N)` norm. -/
theorem trace_estimate {ε : ℝ} (hε : 0 < ε) (x : PhysH1 L N) :
    ‖traceMap i j hij x‖ ^ 2 ≤
      ε * ∑' w, (2 * Real.pi * (w i) / L) ^ 2 * ‖coeffFun x w‖ ^ 2 +
        (L⁻¹ + ε⁻¹) * ‖x.val‖ ^ 2 := by
  have h := (trace_bound L i j hij (Fact.out : 0 < L) hε (coeffFun x)
    (summable_coeffFun_sq x) (summable_coeffFun_deriv i x)).2.2
  have hn : ‖traceMap i j hij x‖ ^ 2 = ∑' t, ‖traceCoeff L i j hij (coeffFun x) t‖ ^ 2 :=
    norm_sq_eq_tsum _
  have hv : ‖x.val‖ ^ 2 = ∑' w, ‖coeffFun x w‖ ^ 2 := by
    rw [← (momUnitary L N).norm_map x.val]
    exact norm_sq_eq_tsum _
  rw [hn, hv]
  exact h

/-- `‖ψ‖²_{L²} + ‖∂_iψ‖² ≤ ‖ψ‖²_{H¹}` (one coordinate's kinetic term is part of the `H¹` norm). -/
theorem norm_sq_add_deriv_le (x : PhysH1 L N) :
    ‖x.val‖ ^ 2 + ∑' w, (2 * Real.pi * (w i) / L) ^ 2 * ‖coeffFun x w‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [PhysH1.kinetic_split x]
  have h : ∑' w, (2 * Real.pi * (w i) / L) ^ 2 * ‖coeffFun x w‖ ^ 2 ≤
      ∑ j, ∑' w, QuantumNLS.Fourier.freq L (w j) ^ 2 *
        ‖(momUnitary L N x.val : Mom N → ℂ) w‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑' w, QuantumNLS.Fourier.freq L (w j) ^ 2 *
        ‖(momUnitary L N x.val : Mom N → ℂ) w‖ ^ 2)
      (fun j _ => tsum_nonneg fun w => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Finset.mem_univ i)
  linarith

/-- **`T_ij` is bounded `H¹(T_L^N) → L²`**, `‖T_ij ψ‖² ≤ (1 + L⁻¹)‖ψ‖²_{H¹}`. -/
theorem norm_sq_traceMap_le (x : PhysH1 L N) :
    ‖traceMap i j hij x‖ ^ 2 ≤ (1 + L⁻¹) * ‖x‖ ^ 2 := by
  have h1 := trace_estimate i j hij one_pos x
  have h2 := norm_sq_add_deriv_le i x
  have hL : 0 < L := Fact.out
  have hD : 0 ≤ ∑' w, (2 * Real.pi * (w i) / L) ^ 2 * ‖coeffFun x w‖ ^ 2 :=
    tsum_nonneg fun w => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hv : 0 ≤ ‖x.val‖ ^ 2 := sq_nonneg _
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.2 hL.le
  simp only [one_mul, inv_one] at h1
  nlinarith [mul_nonneg hLi hD, mul_nonneg hLi hv]

/-- **The continuous linear collision trace** `T_ij : H¹(T_L^N) →L ℓ²(TIdx)`, norm `≤ √(1+L⁻¹)`. -/
def traceCLM : PhysH1 L N →L[ℂ] L2 (TIdx N i j) :=
  (traceMap i j hij).mkContinuous (Real.sqrt (1 + L⁻¹)) (fun x => by
    have hL : 0 < L := Fact.out
    have h := norm_sq_traceMap_le i j hij x
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact h)

@[simp] theorem traceCLM_apply (x : PhysH1 L N) : traceCLM i j hij x = traceMap i j hij x := rfl

end PhysTrace

/-! ## §6 Faithfulness: `T_ij` is the genuine restriction to `Σ_ij` on trigonometric polynomials -/

section Restriction

open QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)] {N : ℕ} (i j : Fin N) (hij : i ≠ j)

omit [Fact (0 < L)] in
theorem mode_mul_mode (a b : ℤ) (x : AddCircle L) :
    mode L a x * mode L b x = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * mode L (a + b) x := by
  unfold mode
  rw [fourier_add]
  ring

/-- The point of `T_L^N` with `x_i = x_j = t` and the other coordinates `y`. -/
def diagPoint (t : AddCircle L) (y : Rest N i j → AddCircle L) : Fin N → AddCircle L :=
  fun l => if h : l = i then t else if h' : l = j then t else y ⟨l, h, h'⟩

omit [Fact (0 < L)] in
theorem prod_diag (hij : i ≠ j) (f : Fin N → AddCircle L → ℂ) (t : AddCircle L) (y : Rest N i j → AddCircle L) :
    ∏ l, f l (diagPoint i j t y l) = f i t * f j t * ∏ l : Rest N i j, f l.1 (y l) := by
  classical
  have hji : j ≠ i := hij.symm
  have h1 : ∏ l : Fin N, f l (diagPoint i j t y l) =
      f i (diagPoint i j t y i) * ∏ l ∈ Finset.univ.erase i, f l (diagPoint i j t y l) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have h2 : ∏ l ∈ Finset.univ.erase i, f l (diagPoint i j t y l) =
      f j (diagPoint i j t y j) *
        ∏ l ∈ (Finset.univ.erase i).erase j, f l (diagPoint i j t y l) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩)).symm
  have h3 : ∏ l ∈ (Finset.univ.erase i).erase j, f l (diagPoint i j t y l) =
      ∏ l : Rest N i j, f l.1 (y l) := by
    rw [Finset.prod_subtype ((Finset.univ.erase i).erase j)
      (p := fun l => l ≠ i ∧ l ≠ j) (fun l => by simp [and_comm])]
    refine Finset.prod_congr rfl fun l _ => ?_
    obtain ⟨l, h1, h2⟩ := l
    simp [diagPoint, h1, h2]
  rw [h1, h2, h3]
  simp [diagPoint, hji]
  ring

/-- The product modes of the target `T_L^{N-1} = T_L × T_L^{N-2}` on `Σ_ij`:
`E'_{(s,m)}(t, y) = e_s(t) ∏_{l ≠ i,j} e_{m_l}(y_l)`. -/
def Ediag (τ : TIdx N i j) (t : AddCircle L) (y : Rest N i j → AddCircle L) : ℂ :=
  mode L τ.1 t * ∏ l : Rest N i j, mode L (τ.2 l) (y l)

omit [Fact (0 < L)] in
/-- On the diagonal the product mode `E_w` depends only on the antidiagonal sum:
`E_w(t,t,y) = L^{-1/2} E'_{(w_i+w_j, w|rest)}(t,y)`. -/
theorem prodMode_diag (hij : i ≠ j) (w : Fin N → ℤ) (t : AddCircle L) (y : Rest N i j → AddCircle L) :
    ∏ l, mode L (w l) (diagPoint i j t y l) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Ediag i j (w i + w j, fun l => w l.1) t y := by
  rw [prod_diag i j hij (fun l x => mode L (w l) x), mode_mul_mode]
  unfold Ediag
  ring

omit [Fact (0 < L)] in
/-- **`T_ij` is the restriction** (trigonometric polynomials): for a finitely supported coefficient
vector `c`, the restriction of `ψ = Σ_w c_w E_w` to `{x_i = x_j}` — as a function of the common
coordinate `t` and the other coordinates `y` — has Fourier expansion `Σ_τ (T c)(τ) E'_τ`, i.e. the
trace coefficients `traceCoeff` are exactly its Fourier coefficients in the product modes of
`T_L^{N-1}`. -/
theorem restriction_trig (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ)
    (hS : ∀ w, w ∉ S → c w = 0) (t : AddCircle L) (y : Rest N i j → AddCircle L) :
    ∑' w, c w * ∏ l, mode L (w l) (diagPoint i j t y l) =
      ∑' τ : TIdx N i j, traceCoeff L i j hij c τ * Ediag i j τ t y := by
  set g : (Fin N → ℤ) → ℂ := fun w => c w * ∏ l, mode L (w l) (diagPoint i j t y l) with hg
  have hgs : Summable g := summable_of_ne_finset_zero (s := S) fun w hw => by
    simp [hg, hS w hw]
  have hg2 : Summable (g ∘ (fibEquiv i j hij).symm) := ((fibEquiv i j hij).symm.summable_iff).2 hgs
  have h1 : ∑' w, g w = ∑' p, (g ∘ (fibEquiv i j hij).symm) p :=
    ((fibEquiv i j hij).symm.tsum_eq g).symm
  rw [h1, hg2.tsum_prod]
  refine tsum_congr fun τ => ?_
  -- fibre sum
  have hfib : ∀ a : ℤ, (g ∘ (fibEquiv i j hij).symm) (τ, a) =
      (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * c (fib i j hij τ a) * Ediag i j τ t y := by
    intro a
    show c (fib i j hij τ a) * ∏ l, mode L (fib i j hij τ a l) (diagPoint i j t y l) = _
    rw [prodMode_diag i j hij]
    have hs : fib i j hij τ a i + fib i j hij τ a j = τ.1 := by
      rw [fib_i, fib_j]; ring
    have hm : (fun l : Rest N i j => fib i j hij τ a l.1) = τ.2 := by
      funext l
      obtain ⟨l, h1, h2⟩ := l
      simp [fib, splitEquiv, h1, h2]
    rw [hs, hm]
    ring
  simp_rw [hfib]
  rw [tsum_mul_right]
  unfold traceCoeff
  rw [← tsum_mul_left]

end Restriction

/-! ## §7 Trigonometric-polynomial elements of the physical `H¹` and agreement with the restriction -/

section TrigElement

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.PhysicalTensor QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `momUnitary (E_w) = δ_w`: the product modes are the Fourier basis vectors. -/
theorem momUnitary_prodMode (w : Fin N → ℤ) :
    momUnitary L N (prodMode L N w) = lp.single 2 w (1 : ℂ) := by
  apply Subtype.ext; funext w'
  rw [show ((momUnitary L N (prodMode L N w) : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w' =
    ⟪prodMode L N w', prodMode L N w⟫_ℂ from momUnitary_apply_eq_inner _ _]
  unfold prodMode
  rw [inner_prodLp]
  have hmode : ∀ n m : ℤ, ⟪modeLp L n, modeLp L m⟫_ℂ = if n = m then 1 else 0 := fun n m => by
    rw [inner_modeLp, fourierL2_modeLp, lp.single_apply, Pi.single_apply]
  simp_rw [hmode]
  rw [lp.single_apply, Pi.single_apply, Finset.prod_ite_zero]
  simp only [Finset.prod_const_one]
  by_cases h : w' = w
  · subst h; simp
  · have : ∃ x, ¬ w' x = w x := not_forall.1 (fun hh => h (funext hh))
    simp [h, this]

/-- The `L²` class `E_w` has the pointwise representative `x ↦ ∏_l e_{w_l}(x_l)` (a.e.). -/
theorem prodMode_ae (w : Fin N → ℤ) :
    (prodMode L N w : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      fun x => ∏ l, mode L (w l) (x l) := by
  unfold prodMode prodLp
  have h1 := (memLp_prodFun (fun l => modeLp L (w l))).coeFn_toLp
  have h2 : ∀ l : Fin N, ∀ᵐ x ∂(torusPiMeasure L N), modeLp L (w l) (x l) = mode L (w l) (x l) :=
    fun l => (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => (volume : Measure (AddCircle L))) l).ae_eq_comp
      (coeFn_modeLp L (w l))
  have h3 := ae_all_iff.2 h2
  filter_upwards [h1, h3] with x hx hx3
  rw [hx]
  exact Finset.prod_congr rfl fun l _ => hx3 l

/-- The finitely supported `ℓ²` vector `w ↦ c_w·[w ∈ S]`. -/
def finVec (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) : L2 (Fin N → ℤ) :=
  ⟨fun w => if w ∈ S then c w else 0,
    memL2_iff.2 (summable_of_ne_finset_zero (s := S) fun w hw => by simp [hw])⟩

theorem finVec_apply (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) (w : Fin N → ℤ) :
    ((finVec S c : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w = if w ∈ S then c w else 0 := rfl

omit [Fact (0 < L)] in
theorem finVec_mem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    finVec S c ∈ mulDomain (kinSqrtMult L N).m := by
  rw [mem_mulDomain_iff]
  exact summable_of_ne_finset_zero (s := S) fun w hw => by simp [finVec_apply, hw]

/-- The element of `H¹(T_L^N)` with the finitely supported Fourier coefficients `c|_S`
(a trigonometric polynomial). -/
def trigElem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) : PhysH1 L N :=
  PhysH1.mk (Mult.DomSpace.mk (M := kinSqrtMult L N) (finVec S c) (finVec_mem S c))

theorem momUnitary_trigElem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    momUnitary L N (trigElem (L := L) S c).val = finVec S c := by
  rw [PhysH1.momUnitary_val]
  rfl

theorem coeffFun_trigElem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) (w : Fin N → ℤ) :
    coeffFun (trigElem (L := L) S c) w = if w ∈ S then c w else 0 := by
  unfold coeffFun
  rw [momUnitary_trigElem]
  rfl

/-- The `L²` class of the trigonometric polynomial is `Σ_{w∈S} c_w E_w`. -/
theorem val_trigElem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    (trigElem (L := L) S c).val = ∑ w ∈ S, c w • prodMode L N w := by
  apply (momUnitary L N).injective
  rw [momUnitary_trigElem, map_sum]
  simp_rw [map_smul, momUnitary_prodMode]
  apply Subtype.ext; funext w'
  rw [finVec_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply, Pi.single_apply]

/-- ... whose pointwise representative is the trigonometric polynomial `Σ_{w∈S} c_w ∏_l e_{w_l}(x_l)`. -/
theorem trigElem_ae (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ) :
    ((trigElem (L := L) S c).val : (Fin N → AddCircle L) → ℂ) =ᵐ[torusPiMeasure L N]
      fun x => ∑ w ∈ S, c w * ∏ l, mode L (w l) (x l) := by
  rw [val_trigElem]
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℂ 2 (torusPiMeasure L N)
  | insert a T ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • prodMode L N a) (∑ w ∈ T, c w • prodMode L N w),
      Lp.coeFn_smul (c a) (prodMode L N a), prodMode_ae (L := L) (N := N) a, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Finset.sum_insert ha]
    rfl

variable (i j : Fin N) (hij : i ≠ j)

/-- **Agreement with the genuine restriction, on actual elements of `H¹(T_L^N)`**: for the
trigonometric polynomial `ψ = Σ_{w∈S} c_w E_w` (an element of the physical `H¹`, with pointwise
representative `trigElem_ae`), the restriction of `ψ` to `{x_i = x_j}`, as a function of
`(t, y)`, is the function whose Fourier coefficients in the product modes of `T_L^{N-1}` are exactly
the values of the constructed trace `traceMap`. -/
theorem trace_trigElem (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ)
    (t : AddCircle L) (y : Rest N i j → AddCircle L) :
    ∑ w ∈ S, c w * ∏ l, mode L (w l) (diagPoint i j t y l) =
      ∑' τ : TIdx N i j,
        ((traceMap i j hij (trigElem (L := L) S c) : L2 (TIdx N i j)) : TIdx N i j → ℂ) τ *
          Ediag i j τ t y := by
  set c' : (Fin N → ℤ) → ℂ := fun w => if w ∈ S then c w else 0 with hc'
  have h := restriction_trig i j hij S c' (fun w hw => by simp [hc', hw]) t y
  have hL : ∑' w, c' w * ∏ l, mode L (w l) (diagPoint i j t y l) =
      ∑ w ∈ S, c w * ∏ l, mode L (w l) (diagPoint i j t y l) := by
    rw [tsum_eq_sum (s := S) (fun w hw => by simp [hc', hw])]
    exact Finset.sum_congr rfl fun w hw => by simp [hc', hw]
  have hco : coeffFun (trigElem (L := L) S c) = c' := funext fun w => coeffFun_trigElem S c w
  rw [← hL, h]
  refine tsum_congr fun τ => ?_
  rw [traceMap_apply, hco]

end TrigElement

/-! ## §8 Density of trigonometric polynomials in `H¹` and uniqueness of the extension -/

section Density

open QuantumNLS.PhysicalEnergy QuantumNLS.Energy QuantumNLS.Fourier

variable {L : ℝ} [Fact (0 < L)] {N : ℕ}

/-- `x ↦ (√a_k(w) x̂(w))_w`: `H¹(T_L^N) ≃ₗᵢ ℓ²(ℤ^N)`. -/
def Psi : PhysH1 L N ≃ₗᵢ[ℂ] L2 (Fin N → ℤ) := PhysH1.unitary.trans (momUnitary L N)

theorem Psi_apply (x : PhysH1 L N) (w : Fin N → ℤ) :
    ((Psi x : L2 (Fin N → ℤ)) : (Fin N → ℤ) → ℂ) w = (kinSqrt L N w : ℂ) * coeffFun x w :=
  PhysH1.unitary_coeff x w

theorem Psi_trigElem (S : Finset (Fin N → ℤ)) (x : PhysH1 L N) :
    Psi (trigElem (L := L) S (coeffFun x)) = ∑ w ∈ S, lp.single 2 w ((Psi x : L2 (Fin N → ℤ)) w) := by
  apply Subtype.ext; funext w'
  rw [Psi_apply, coeffFun_trigElem, lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply, Pi.single_apply, Psi_apply]

/-- **Density**: the finite Fourier truncations `ψ_S` of any `ψ ∈ H¹(T_L^N)` (trigonometric
polynomials) converge to `ψ` in the `H¹` energy norm. -/
theorem trigElem_tendsto (x : PhysH1 L N) :
    Filter.Tendsto (fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) Filter.atTop
      (nhds x) := by
  have hs := lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) (Psi x)
  have ht : Filter.Tendsto (fun S : Finset (Fin N → ℤ) =>
      ∑ w ∈ S, lp.single 2 w ((Psi x : L2 (Fin N → ℤ)) w)) Filter.atTop (nhds (Psi x)) := hs
  have h2 := ((Psi (L := L) (N := N)).symm.continuous.tendsto _).comp ht
  rw [LinearIsometryEquiv.symm_apply_apply] at h2
  refine h2.congr fun S => ?_
  show (Psi (L := L) (N := N)).symm (∑ w ∈ S, lp.single 2 w ((Psi x : L2 (Fin N → ℤ)) w)) = _
  rw [← Psi_trigElem, LinearIsometryEquiv.symm_apply_apply]

/-- **The continuous extension is unique**: any continuous linear map `H¹(T_L^N) → ℓ²` agreeing with
the collision trace on trigonometric polynomials equals it.  Together with `trace_trigElem`
(on trigonometric polynomials the trace *is* the restriction) this identifies `T_ij` as
the continuous extension of the restriction map. -/
theorem traceCLM_unique (i j : Fin N) (hij : i ≠ j) (T' : PhysH1 L N →L[ℂ] L2 (TIdx N i j))
    (h : ∀ (S : Finset (Fin N → ℤ)) (c : (Fin N → ℤ) → ℂ),
      T' (trigElem (L := L) S c) = traceCLM i j hij (trigElem (L := L) S c)) :
    T' = traceCLM i j hij := by
  refine ContinuousLinearMap.ext fun x => ?_
  have h1 := (T'.continuous.tendsto x).comp (trigElem_tendsto x)
  have h2 := ((traceCLM i j hij).continuous.tendsto x).comp (trigElem_tendsto x)
  have h3 : (T' ∘ fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) =
      (traceCLM i j hij ∘ fun S : Finset (Fin N → ℤ) => trigElem (L := L) S (coeffFun x)) :=
    funext fun S => h S _
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

end Density

end QuantumNLS.CollisionTrace
