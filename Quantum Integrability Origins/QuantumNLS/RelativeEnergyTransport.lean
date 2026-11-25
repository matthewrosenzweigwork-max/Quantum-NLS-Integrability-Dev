import QuantumNLS.RelativeEnergy

/-!
# ENERGY-006 `lem:A1-relative`: the transport clause `eq:A1-transport` and the assembled lemma

Source: `source/chapters/energy_prepared/cubic_charge.tex`, subsection "A relative energy on the
space of rays" (`lem:A1-relative`, `eq:A1-coercive` ... `eq:A1-transport` and the printed proof
`eq:A1-R` ... `eq:A1-relative-identity`, final `H¹` approximation).  This module imports the frozen
`RelativeEnergy` (sha256 `8fb33e5c...`, coercive and structural clauses) read-only.

## Objects (literal)
* Flow `X(v) = v''' − 6κ|v|²v'` (`eq:A1-flow`, Hamiltonian vector field of `I_4`, convention
  `X_F = −i∇F`): `Xf κ v`; `𝒩(v) = −6κ|v|²v'`: `Nf`; `∇E(q) = (1−∂²)q + 2κ|q|²q`: `gE`.
* `v(t)`: a smooth unit solution, i.e. `V : ℝ → ℝ → ℂ` jointly `C^∞`, `L`-periodic in `x`,
  `∂_t V = X(V)` (`hsol`), `‖V(t)‖₂ = 1`; time sets are compact `K ⊂ ℝ`.
* Weak derivative `u_x` of `u ∈ H¹`: `IsWD u u_x` (circle form of `HasWeakDeriv`, equivalent
  `isWD_iff_hasWeakDeriv`); every `H¹` function has one (`exists_IsWD`).
* The printed polynomial `S_v` of `eq:A1-S` as a function of the data `(α, ⟨ℓ,u⟩, ⟨r_v,u⟩,
  E₂(v), V₄(v))`: `Sigma`; `Sv_eq_Sigma` identifies it with the frozen `Sv = E − F_v`.
  `dSigma` is its directional derivative (`dSigma_eq_deriv`: the genuine `ε`-derivative along the
  line of data).
* `d_u[X(u)] S_v(u)`: `Tu κ v u u_x := dSigma` along the data `(⟨g, X(u)⟩)_{g ∈ {v, ℓ, r_v}}`,
  with `⟨g, X(u)⟩ := Xpair κ g u u_x = −⟨g''',u⟩ − 6κ ∫ ḡ|u|²u_x` (the third derivative moved
  onto the smooth contraction; `u_x` the weak derivative), exactly the printed meaning
  ("the third derivative is moved onto the smooth finite-rank contractions").  Consistency:
  `deriv_Sv_line` (for every `H¹` direction `h` it is the genuine derivative
  `d/dε S_v(u + εh)`), `Xpair_smooth` and `Tu_smooth` (for smooth `u` it is
  `d/dε|₀ S_v(u + εX(u))`).
* `∂_t S_{V(t)}(u)`: the genuine time derivative `deriv (fun s => Sv κ (lift (V s)) u) t`.
  `hasDerivAt_Sv_time` proves (differentiation under the integral, mixed partials, `∂_t V = X(V)`)
  that it equals `Tt κ (V t) u`, the derivative of `eq:A1-S` along `v_t = X(v)` (the printed
  assignment "`u_t = X(u)` and `v_t = X(v)`").  `Ttot = Tt + Tu`.

## The printed route (all proved, no assumption)
`eq:A1-conservation-derivative`: `kerK_eq_zero` (the Euler–Lagrange kernel of the conservation
law vanishes identically, by explicit jet calculus), `cons_E` (`dE(q)[X(q)] = 0`, total
derivative), `mass_v3`, `mass_N` (mass conservation), `C1_identity`
(`d²E(q)[X(q),w] + dE(q)[DX(q)w] = 0` tested against `w ∈ H¹`, the `w'` entering through the
weak derivative, `LamId`, `Ia_eq`); `Ttot_formula` (`S = E(q) + dE(q)[w]` differentiated:
`Ttot = 2Re⟨∇E(q), u_t⟩ + d²E(q)[q_t, w]`); `Ttot_identity` (`eq:A1-relative-identity`:
`Ttot = 2Re⟨∇E(q), R⟩ + d²E(q)[q_t − X(q), w]` with the nonlinear remainder `R` of `eq:A1-R`
(`RemC`)); `alpha_dot_eq`, `alpha_dot_bound` (`eq:A1-alpha`, `eq:A1-alpha-bound`);
`norm_RemC_le` (`eq:A1-R-bound`, with `κ > 0` through the arithmetic-geometric mean inequality
`pt_Rem_amgm`); `Ttot_bound` (`eq:A1-transport` at fixed time: `|Ttot| ≤ Cbound κ L M · F_v(u)`,
the constant depending only on `κ`, `L` and a common supremum bound `M` of `v, v', v'', v'''`);
`exists_JB_uniform`, `energy006_transport_uniform`, `energy006_transport_solution` (one constant
on a compact time set, for a classical solution, with the genuine `∂_t`).  No smooth approximation
of `u` is needed: the identity and the bound are proved directly for `u ∈ H¹` with weak derivative
(the approximation step of the printed proof is replaced by working with `H¹` pairings
throughout, which are exactly the printed "third derivative moved onto the contractions").

## Assembly
`energy006_A1_relative_complete`: coercive, prefatory, structural and phase clauses (frozen
`energy006_A1_relative`, `Fv_phase_u/v`), weak derivative existence, the fixed-time transport
bound, and the transport bound for a classical solution on every compact time set.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ComplexConjugate ContDiff
open MeasureTheory QuantumNLS.Fourier QuantumNLS.WeakDerivatives QuantumNLS.ClassicalCharges
  QuantumNLS.ChargeEnergy

noncomputable section

namespace QuantumNLS.RelativeEnergy

variable {L : ℝ}

section Calculus

theorem integral_eq_zero_of_hasDerivAt {G G' : ℝ → ℂ} (hG : ∀ x, HasDerivAt G (G' x) x)
    (hc : Continuous G') (hp : Function.Periodic G L) :
    ∫ x in (0 : ℝ)..L, G' x = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hG x) (hc.intervalIntegrable _ _)]
  have := hp 0
  simp only [zero_add] at this
  rw [this]; ring

theorem ibp_smooth {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g) :
    ∫ x in (0 : ℝ)..L, f x * deriv g x = -∫ x in (0 : ℝ)..L, deriv f x * g x := by
  have h : ∫ x in (0 : ℝ)..L, (deriv f x * g x + f x * deriv g x) = 0 := by
    refine integral_eq_zero_of_hasDerivAt (G := fun x => f x * g x) (fun x => ?_) ?_ ?_
    · exact (hasDerivAt_of_smooth hf x).mul (hasDerivAt_of_smooth hg x)
    · exact ((deriv_continuous hf).mul hg.smooth.continuous).add
        (hf.smooth.continuous.mul (deriv_continuous hg))
    · intro x
      simp only
      rw [hf.periodic x, hg.periodic x]
  rw [intervalIntegral.integral_add (f := fun x => deriv f x * g x) (g := fun x => f x * deriv g x)
    (((deriv_continuous hf).mul hg.smooth.continuous).intervalIntegrable _ _)
    ((hf.smooth.continuous.mul (deriv_continuous hg)).intervalIntegrable _ _)] at h
  linear_combination h

theorem exists_bound_periodic [Fact (0 < L)] {f : ℝ → ℂ} (hc : Continuous f)
    (hp : Function.Periodic f L) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  have hcomp := hp.compact_of_continuous (Fact.out : 0 < L).ne' hc
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hcomp.isBounded
  exact ⟨max M 0, le_max_right _ _, fun x => (hM _ ⟨x, rfl⟩).trans (le_max_left _ _)⟩

end Calculus

section WeakD

variable [Fact (0 < L)]

theorem circ_eq_interval (F : AddCircle L → ℂ) :
    ∫ y, F y ∂(volume : Measure (AddCircle L)) = ∫ x in (0 : ℝ)..L, F (x : AddCircle L) := by
  have := AddCircle.intervalIntegral_preimage L 0 F
  rw [zero_add] at this
  exact this.symm

/-- Weak derivative of a torus field, circle-integral form: `∫ u (φ') = −∫ u' φ` for every
smooth periodic `φ` (the lift to the circle is `lift`). -/
def IsWD (u u' : AddCircle L → ℂ) : Prop :=
  MemLp u 2 (volume : Measure (AddCircle L)) ∧ MemLp u' 2 (volume : Measure (AddCircle L)) ∧
    ∀ (φ : ℝ → ℂ) (hφ : SmoothPeriodic L φ),
      ∫ y, u y * lift (sp_deriv hφ) y ∂(volume : Measure (AddCircle L)) =
        -∫ y, u' y * lift hφ y ∂(volume : Measure (AddCircle L))

theorem interval_coe_eq {F G : AddCircle L → ℂ}
    (hFG : F =ᵐ[(volume : Measure (AddCircle L))] G) {ψ : ℝ → ℂ} (hψ : SmoothPeriodic L ψ) :
    ∫ x in (0 : ℝ)..L, F (x : AddCircle L) * ψ x = ∫ y, G y * lift hψ y ∂(volume : Measure (AddCircle L)) := by
  have h1 : ∫ x in (0 : ℝ)..L, F (x : AddCircle L) * ψ x =
      ∫ y, F y * lift hψ y ∂(volume : Measure (AddCircle L)) := by
    rw [circ_eq_interval]
    exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])
  rw [h1]
  exact integral_congr_ae (hFG.mono fun x hx => by simp only [hx])

theorem isWD_iff_hasWeakDeriv {u u' : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) (hu' : MemLp u' 2 (volume : Measure (AddCircle L))) :
    IsWD u u' ↔ HasWeakDeriv (hu.toLp u) (hu'.toLp u') := by
  constructor
  · intro h φ hφ
    have hφ' : SmoothPeriodic L φ := ⟨hφ.smooth, hφ.periodic⟩
    rw [interval_coe_eq hu.coeFn_toLp (sp_deriv hφ'), interval_coe_eq hu'.coeFn_toLp hφ']
    exact h.2.2 φ hφ'
  · intro h
    refine ⟨hu, hu', fun φ hφ => ?_⟩
    have := h φ ⟨hφ.smooth, hφ.periodic⟩
    rw [interval_coe_eq hu.coeFn_toLp (sp_deriv hφ), interval_coe_eq hu'.coeFn_toLp hφ] at this
    exact this

theorem integrable_mul_lift {u : AddCircle L → ℂ} (hu : MemLp u 2 (volume : Measure (AddCircle L)))
    {ψ : ℝ → ℂ} (hψ : SmoothPeriodic L ψ) :
    Integrable (fun y => u y * lift hψ y) (volume : Measure (AddCircle L)) :=
  hu.integrable_mul (memLp_of_continuous (continuous_lift hψ))

theorem IsWD.sub {u u' z z' : AddCircle L → ℂ} (h : IsWD u u') (k : IsWD z z') :
    IsWD (fun y => u y - z y) (fun y => u' y - z' y) := by
  refine ⟨h.1.sub k.1, h.2.1.sub k.2.1, fun φ hφ => ?_⟩
  have e1 := h.2.2 φ hφ
  have e2 := k.2.2 φ hφ
  simp only [sub_mul]
  rw [integral_sub (integrable_mul_lift h.1 _) (integrable_mul_lift k.1 _),
    integral_sub (integrable_mul_lift h.2.1 _) (integrable_mul_lift k.2.1 _), e1, e2]
  ring

theorem IsWD.const_mul {u u' : AddCircle L → ℂ} (h : IsWD u u') (c : ℂ) :
    IsWD (fun y => c * u y) (fun y => c * u' y) := by
  refine ⟨h.1.const_mul c, h.2.1.const_mul c, fun φ hφ => ?_⟩
  have e1 := h.2.2 φ hφ
  simp only [mul_assoc]
  rw [integral_const_mul, integral_const_mul, e1]
  ring

theorem IsWD.smooth {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    IsWD (lift hv) (lift (sp_deriv hv)) := by
  refine ⟨memLp_of_continuous (continuous_lift hv), memLp_of_continuous (continuous_lift _),
    fun φ hφ => ?_⟩
  rw [circ_eq_interval, circ_eq_interval]
  have e : ∀ (a b : ℝ → ℂ) (ha : SmoothPeriodic L a) (hb : SmoothPeriodic L b),
      ∫ x in (0 : ℝ)..L, lift ha (x : AddCircle L) * lift hb (x : AddCircle L) =
        ∫ x in (0 : ℝ)..L, a x * b x := by
    intro a b ha hb
    exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])
  show ∫ x in (0 : ℝ)..L, lift hv (x : AddCircle L) * lift (sp_deriv hφ) (x : AddCircle L) =
    -∫ x in (0 : ℝ)..L, lift (sp_deriv hv) (x : AddCircle L) * lift hφ (x : AddCircle L)
  rw [e, e]
  exact ibp_smooth hv hφ

theorem IsWD.ibp {w w' : AddCircle L → ℂ} (h : IsWD w w') {c : ℝ → ℂ} (hc : SmoothPeriodic L c) :
    ∫ y, lift hc y * w' y ∂(volume : Measure (AddCircle L)) =
      -∫ y, lift (sp_deriv hc) y * w y ∂(volume : Measure (AddCircle L)) := by
  have := h.2.2 c hc
  have e1 : ∫ y, lift hc y * w' y ∂(volume : Measure (AddCircle L)) =
      ∫ y, w' y * lift hc y ∂(volume : Measure (AddCircle L)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  have e2 : ∫ y, lift (sp_deriv hc) y * w y ∂(volume : Measure (AddCircle L)) =
      ∫ y, w y * lift (sp_deriv hc) y ∂(volume : Measure (AddCircle L)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)
  rw [e1, e2, this]; ring

theorem kinetic_eq_of_IsWD {w w' : AddCircle L → ℂ} (h : IsWD w w') :
    kinetic w = ∫ y, ‖w' y‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
  have hW := (isWD_iff_hasWeakDeriv h.1 h.2.1).1 h
  have hc : ∀ n, coeff L w' n = ikn L n * coeff L w n := by
    intro n
    have := coeff_of_hasWeakDeriv hW n
    rwa [coeff_congr_ae L h.2.1.coeFn_toLp n, coeff_congr_ae L h.1.coeFn_toLp n] at this
  rw [← tsum_sq_coeff L h.2.1]
  unfold kinetic
  refine tsum_congr fun n => ?_
  rw [hc n, norm_ikn_mul_sq]

theorem exists_IsWD {u : AddCircle L → ℂ} (hu : H04 L 1 u) : ∃ u', IsWD u u' := by
  have hs : Summable fun n : ℤ => freq L n ^ 2 *
      ‖coeff L ((hu.1.toLp u : Lp ℂ 2 (volume : Measure (AddCircle L))) : AddCircle L → ℂ) n‖ ^ 2 := by
    have h1 := kin_summable hu.2
    have h2 : (fun n : ℤ => (|freq L n| * ‖coeff L u n‖) ^ 2) =
        fun n : ℤ => freq L n ^ 2 * ‖coeff L u n‖ ^ 2 := kin_eq _
    rw [h2] at h1
    refine h1.congr fun n => ?_
    rw [coeff_congr_ae L hu.1.coeFn_toLp n]
  obtain ⟨g, hg⟩ := (exists_hasWeakDeriv_iff _).2 hs
  refine ⟨(g : AddCircle L → ℂ), ?_⟩
  rw [isWD_iff_hasWeakDeriv hu.1 (Lp.memLp g)]
  have : (Lp.memLp g).toLp (g : AddCircle L → ℂ) = g := Lp.toLp_coeFn g (Lp.memLp g)
  rw [this]
  exact hg

end WeakD

/-! ## The vector field, the energy gradient and the Hessian kernel -/

/-- `X(v) = v''' − 6κ|v|² v'` (`eq:A1-flow`). -/
def Xf (κ : ℝ) (v : ℝ → ℂ) : ℝ → ℂ := fun x =>
  deriv (deriv (deriv v)) x - 6 * (κ : ℂ) * ((‖v x‖ ^ 2 : ℝ) : ℂ) * deriv v x

/-- `𝒩(v) = −6κ|v|² v'`. -/
def Nf (κ : ℝ) (v : ℝ → ℂ) : ℝ → ℂ := fun x =>
  -6 * (κ : ℂ) * ((‖v x‖ ^ 2 : ℝ) : ℂ) * deriv v x

/-- `∇E(q) = (1−∂²)q + 2κ|q|²q`. -/
def gE (κ : ℝ) (q : ℝ → ℂ) : ℝ → ℂ := fun x => lvec q x + 2 * (κ : ℂ) * rvec q x

/-- The Hessian kernel: `d²E(q)[h, ·] = 2 Re ⟨k1 q h, ·⟩`. -/
def k1 (κ : ℝ) (q h : ℝ → ℂ) : ℝ → ℂ := fun x =>
  lvec h x + 2 * (κ : ℂ) * ((‖q x‖ ^ 2 : ℝ) : ℂ) * h x +
    4 * (κ : ℂ) * (((conj (q x) * h x).re : ℝ) : ℂ) * q x

/-- The Euler–Lagrange kernel of the conservation law (printed `eq:A1-conservation-derivative`
in kernel form): it vanishes identically. -/
def kerK (κ : ℝ) (q : ℝ → ℂ) : ℝ → ℂ := fun x =>
  k1 κ q (Xf κ q) x - deriv (deriv (deriv (gE κ q))) x
    + 6 * (κ : ℂ) * deriv (fun y => gE κ q y * ((‖q y‖ ^ 2 : ℝ) : ℂ)) x
    - 12 * (κ : ℂ) * (((conj (gE κ q x) * deriv q x).re : ℝ) : ℂ) * q x

theorem hn (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [mul_comm]; have := (Complex.conj_mul' z).symm; push_cast; exact this

/-- Jets `q^{(k)}`. -/
def jet (q : ℝ → ℂ) (k : ℕ) : ℝ → ℂ := deriv^[k] q

section JetCalc

variable [Fact (0 < L)]

theorem sp_jet {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (k : ℕ) : SmoothPeriodic L (jet q k) := by
  induction k with
  | zero => exact hq
  | succ k ih =>
    unfold jet at *
    rw [Function.iterate_succ_apply']
    exact sp_deriv ih

theorem hasDerivAt_jet {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (k : ℕ) (x : ℝ) :
    HasDerivAt (jet q k) (jet q (k + 1) x) x := by
  have : jet q (k + 1) = deriv (jet q k) := by
    unfold jet; rw [Function.iterate_succ_apply']
  rw [this]
  exact hasDerivAt_of_smooth (sp_jet hq k) x

theorem hasDerivAt_jet_conj {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => conj (jet q k y)) (conj (jet q (k + 1) x)) x :=
  (hasDerivAt_jet hq k x).star

end JetCalc

theorem jet_zero (q : ℝ → ℂ) : jet q 0 = q := rfl
theorem jet_one (q : ℝ → ℂ) : jet q 1 = deriv q := rfl
theorem jet_two (q : ℝ → ℂ) : jet q 2 = deriv (deriv q) := rfl
theorem jet_three (q : ℝ → ℂ) : jet q 3 = deriv (deriv (deriv q)) := rfl

theorem Xf_eq (κ : ℝ) (q : ℝ → ℂ) : Xf κ q = fun x =>
    jet q 3 x - 6 * (κ : ℂ) * (jet q 0 x * conj (jet q 0 x)) * jet q 1 x := by
  funext x; simp only [Xf, jet_zero, jet_one, jet_three, hn]

theorem Nf_eq (κ : ℝ) (q : ℝ → ℂ) : Nf κ q = fun x =>
    -6 * (κ : ℂ) * (jet q 0 x * conj (jet q 0 x)) * jet q 1 x := by
  funext x; simp only [Nf, jet_zero, jet_one, hn]

theorem gE_eq (κ : ℝ) (q : ℝ → ℂ) : gE κ q = fun x =>
    jet q 0 x - jet q 2 x + 2 * (κ : ℂ) * ((jet q 0 x * conj (jet q 0 x)) * jet q 0 x) := by
  funext x; simp only [gE, lvec, rvec, jet_zero, jet_two, hn]

theorem jet_four (q : ℝ → ℂ) : jet q 4 = deriv (deriv (deriv (deriv q))) := rfl
theorem jet_five (q : ℝ → ℂ) : jet q 5 = deriv (deriv (deriv (deriv (deriv q)))) := rfl

section Chain

variable [Fact (0 < L)]

def M0f (q : ℝ → ℂ) (y : ℝ) : ℂ := ((‖q y‖ ^ 2 : ℝ) : ℂ)
def M1f (q : ℝ → ℂ) (y : ℝ) : ℂ := jet q 1 y * conj (jet q 0 y) + jet q 0 y * conj (jet q 1 y)
def M2f (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 2 y * conj (jet q 0 y) + 2 * (jet q 1 y * conj (jet q 1 y)) + jet q 0 y * conj (jet q 2 y)
def M3f (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 3 y * conj (jet q 0 y) + 3 * (jet q 2 y * conj (jet q 1 y)) +
    3 * (jet q 1 y * conj (jet q 2 y)) + jet q 0 y * conj (jet q 3 y)

def X1f (κ : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 4 y - 6 * (κ : ℂ) * (M1f q y * jet q 1 y + M0f q y * jet q 2 y)
def X2f (κ : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 5 y - 6 * (κ : ℂ) * (M2f q y * jet q 1 y + 2 * (M1f q y * jet q 2 y) + M0f q y * jet q 3 y)

def g0f (κ : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 0 y - jet q 2 y + 2 * (κ : ℂ) * (M0f q y * jet q 0 y)
def g1f (κ : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 1 y - jet q 3 y + 2 * (κ : ℂ) * (M1f q y * jet q 0 y + M0f q y * jet q 1 y)
def g2f (κ : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 2 y - jet q 4 y + 2 * (κ : ℂ) *
    (M2f q y * jet q 0 y + 2 * (M1f q y * jet q 1 y) + M0f q y * jet q 2 y)
def g3f (κ : ℝ) (q : ℝ → ℂ) (y : ℝ) : ℂ :=
  jet q 3 y - jet q 5 y + 2 * (κ : ℂ) *
    (M3f q y * jet q 0 y + 3 * (M2f q y * jet q 1 y) + 3 * (M1f q y * jet q 2 y) +
      M0f q y * jet q 3 y)

variable {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (κ : ℝ)
include hq

theorem hasDerivAt_M0 (x : ℝ) : HasDerivAt (M0f q) (M1f q x) x := by
  have h := (hasDerivAt_jet hq 0 x).mul (hasDerivAt_jet_conj hq 0 x)
  have e : M0f q = fun y => jet q 0 y * conj (jet q 0 y) := by
    funext y; simp only [M0f, jet_zero, hn]
  rw [e]
  exact h.congr_deriv (by simp only [M1f])

theorem hasDerivAt_M1 (x : ℝ) : HasDerivAt (M1f q) (M2f q x) x := by
  have h := ((hasDerivAt_jet hq 1 x).mul (hasDerivAt_jet_conj hq 0 x)).add
    ((hasDerivAt_jet hq 0 x).mul (hasDerivAt_jet_conj hq 1 x))
  have e : M1f q = fun y => jet q 1 y * conj (jet q 0 y) + jet q 0 y * conj (jet q 1 y) := rfl
  rw [e]
  exact h.congr_deriv (by simp only [M2f]; ring)

theorem hasDerivAt_M2 (x : ℝ) : HasDerivAt (M2f q) (M3f q x) x := by
  have h := (((hasDerivAt_jet hq 2 x).mul (hasDerivAt_jet_conj hq 0 x)).add
    (((hasDerivAt_jet hq 1 x).mul (hasDerivAt_jet_conj hq 1 x)).const_mul 2)).add
    ((hasDerivAt_jet hq 0 x).mul (hasDerivAt_jet_conj hq 2 x))
  have e : M2f q = fun y => jet q 2 y * conj (jet q 0 y) + 2 * (jet q 1 y * conj (jet q 1 y)) +
      jet q 0 y * conj (jet q 2 y) := rfl
  rw [e]
  exact h.congr_deriv (by simp only [M3f]; ring)

theorem hasDerivAt_X0 (x : ℝ) : HasDerivAt (Xf κ q) (X1f κ q x) x := by
  have h := (hasDerivAt_jet hq 3 x).sub
    (((hasDerivAt_M0 hq x).mul (hasDerivAt_jet hq 1 x)).const_mul (6 * (κ : ℂ)))
  have e : Xf κ q = fun y => jet q 3 y - 6 * (κ : ℂ) * (M0f q y * jet q 1 y) := by
    funext y; simp only [Xf, M0f, jet_three, jet_one]; ring
  rw [e]
  exact h.congr_deriv (by simp only [X1f])

theorem hasDerivAt_X1 (x : ℝ) : HasDerivAt (X1f κ q) (X2f κ q x) x := by
  have h := (hasDerivAt_jet hq 4 x).sub
    ((((hasDerivAt_M1 hq x).mul (hasDerivAt_jet hq 1 x)).add
      ((hasDerivAt_M0 hq x).mul (hasDerivAt_jet hq 2 x))).const_mul (6 * (κ : ℂ)))
  have e : X1f κ q = fun y => jet q 4 y - 6 * (κ : ℂ) * (M1f q y * jet q 1 y + M0f q y * jet q 2 y) := rfl
  rw [e]
  exact h.congr_deriv (by simp only [X2f, M2f]; ring)

theorem hasDerivAt_g0 (x : ℝ) : HasDerivAt (gE κ q) (g1f κ q x) x := by
  have h := ((hasDerivAt_jet hq 0 x).sub (hasDerivAt_jet hq 2 x)).add
    (((hasDerivAt_M0 hq x).mul (hasDerivAt_jet hq 0 x)).const_mul (2 * (κ : ℂ)))
  have e : gE κ q = fun y => jet q 0 y - jet q 2 y + 2 * (κ : ℂ) * (M0f q y * jet q 0 y) := by
    funext y; simp only [gE, lvec, rvec, M0f, jet_zero, jet_two]
  rw [e]
  exact h.congr_deriv (by simp only [g1f])

theorem hasDerivAt_g1 (x : ℝ) : HasDerivAt (g1f κ q) (g2f κ q x) x := by
  have h := ((hasDerivAt_jet hq 1 x).sub (hasDerivAt_jet hq 3 x)).add
    ((((hasDerivAt_M1 hq x).mul (hasDerivAt_jet hq 0 x)).add
      ((hasDerivAt_M0 hq x).mul (hasDerivAt_jet hq 1 x))).const_mul (2 * (κ : ℂ)))
  have e : g1f κ q = fun y => jet q 1 y - jet q 3 y + 2 * (κ : ℂ) * (M1f q y * jet q 0 y + M0f q y * jet q 1 y) := rfl
  rw [e]
  exact h.congr_deriv (by simp only [g2f, M2f]; ring)

theorem hasDerivAt_g2 (x : ℝ) : HasDerivAt (g2f κ q) (g3f κ q x) x := by
  have h := ((hasDerivAt_jet hq 2 x).sub (hasDerivAt_jet hq 4 x)).add
    (((((hasDerivAt_M2 hq x).mul (hasDerivAt_jet hq 0 x)).add
      (((hasDerivAt_M1 hq x).mul (hasDerivAt_jet hq 1 x)).const_mul 2)).add
      ((hasDerivAt_M0 hq x).mul (hasDerivAt_jet hq 2 x))).const_mul (2 * (κ : ℂ)))
  have e : g2f κ q = fun y => jet q 2 y - jet q 4 y + 2 * (κ : ℂ) *
    (M2f q y * jet q 0 y + 2 * (M1f q y * jet q 1 y) + M0f q y * jet q 2 y) := rfl
  rw [e]
  exact h.congr_deriv (by simp only [g3f, M3f]; ring)

end Chain

section Cons

variable [Fact (0 < L)] {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (κ : ℝ)
include hq

theorem deriv_Xf : deriv (Xf κ q) = X1f κ q := funext fun x => (hasDerivAt_X0 hq κ x).deriv

theorem kerK_eq_zero (x : ℝ) : kerK κ q x = 0 := by
  have dX : deriv (deriv (Xf κ q)) = X2f κ q := by
    rw [deriv_Xf hq κ]; exact funext fun y => (hasDerivAt_X1 hq κ y).deriv
  have dg : deriv (deriv (deriv (gE κ q))) = g3f κ q := by
    have h1 : deriv (gE κ q) = g1f κ q := funext fun y => (hasDerivAt_g0 hq κ y).deriv
    have h2 : deriv (g1f κ q) = g2f κ q := funext fun y => (hasDerivAt_g1 hq κ y).deriv
    rw [h1, h2]; exact funext fun y => (hasDerivAt_g2 hq κ y).deriv
  have dgM : deriv (fun y => gE κ q y * ((‖q y‖ ^ 2 : ℝ) : ℂ)) x =
      g1f κ q x * M0f q x + gE κ q x * M1f q x :=
    ((hasDerivAt_g0 hq κ x).mul (hasDerivAt_M0 hq x)).deriv
  have re1 : (((conj (q x) * Xf κ q x).re : ℝ) : ℂ) =
      (conj (q x) * Xf κ q x + q x * conj (Xf κ q x)) / 2 := by
    rw [Complex.re_eq_add_conj]; simp only [map_mul, Complex.conj_conj]
  have re2 : (((conj (gE κ q x) * deriv q x).re : ℝ) : ℂ) =
      (conj (gE κ q x) * deriv q x + gE κ q x * conj (deriv q x)) / 2 := by
    rw [Complex.re_eq_add_conj]; simp only [map_mul, Complex.conj_conj]
  unfold kerK k1 lvec
  rw [dX, dg, dgM, re1, re2]
  simp only [Xf_eq, gE_eq, X2f, g3f, g1f, M0f, M1f, M2f, M3f, jet_zero, jet_one, jet_two, jet_three,
    jet_four, jet_five, hn, map_add, map_sub, map_mul, Complex.conj_ofReal, map_ofNat, Complex.conj_conj,
    map_neg, map_one, map_ofNat]
  ring

end Cons

section Conservation

variable [Fact (0 < L)]

theorem re_integral_eq_zero {f G G' : ℝ → ℂ} (hf : Continuous f)
    (hG : ∀ x, HasDerivAt G (G' x) x) (hc : Continuous G') (hp : Function.Periodic G L)
    (hfG : ∀ x, f x + conj (f x) = G' x) : (∫ x in (0 : ℝ)..L, f x).re = 0 := by
  have h0 := integral_eq_zero_of_hasDerivAt hG hc hp
  have hi : IntervalIntegrable f MeasureTheory.volume 0 L := hf.intervalIntegrable _ _
  have hci : IntervalIntegrable (fun x => conj (f x)) MeasureTheory.volume 0 L :=
    (Complex.continuous_conj.comp hf).intervalIntegrable _ _
  have hconj : ∫ x in (0 : ℝ)..L, conj (f x) = conj (∫ x in (0 : ℝ)..L, f x) :=
    intervalIntegral_conj hi
  have h1 : ∫ x in (0 : ℝ)..L, (f x + conj (f x)) = 0 := by
    simp only [hfG]; exact h0
  rw [intervalIntegral.integral_add hi hci, hconj] at h1
  have h3 : ((2 * (∫ x in (0 : ℝ)..L, f x).re : ℝ) : ℂ) = 0 := by
    rw [← Complex.add_conj]; exact h1
  have := Complex.ofReal_eq_zero.mp h3
  linarith

variable {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (κ : ℝ)
include hq

theorem hasDerivAt_aa (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y => jet q k y * conj (jet q k y))
      (jet q (k + 1) x * conj (jet q k x) + jet q k x * conj (jet q (k + 1) x)) x :=
  (hasDerivAt_jet hq k x).mul (hasDerivAt_jet_conj hq k x)

theorem cont_jet (k : ℕ) : Continuous (jet q k) := (sp_jet hq k).smooth.continuous

theorem cont_jet_conj (k : ℕ) : Continuous (fun y => conj (jet q k y)) :=
  Complex.continuous_conj.comp (cont_jet hq k)

theorem per_jet (k : ℕ) (x : ℝ) : jet q k (x + L) = jet q k x := (sp_jet hq k).periodic x

theorem cont_M0 : Continuous (M0f q) := by
  have e : M0f q = fun y => jet q 0 y * conj (jet q 0 y) := by
    funext y; simp only [M0f, jet_zero, hn]
  rw [e]; exact (cont_jet hq 0).mul (cont_jet_conj hq 0)

theorem per_M0 (x : ℝ) : M0f q (x + L) = M0f q x := by
  have e : M0f q = fun y => jet q 0 y * conj (jet q 0 y) := by
    funext y; simp only [M0f, jet_zero, hn]
  rw [e]; simp only [per_jet hq]

theorem cont_M1 : Continuous (M1f q) := by
  unfold M1f
  exact ((cont_jet hq 1).mul (cont_jet_conj hq 0)).add ((cont_jet hq 0).mul (cont_jet_conj hq 1))

theorem cont_M2 : Continuous (M2f q) := by
  unfold M2f
  exact (((cont_jet hq 2).mul (cont_jet_conj hq 0)).add
    (continuous_const.mul ((cont_jet hq 1).mul (cont_jet_conj hq 1)))).add
    ((cont_jet hq 0).mul (cont_jet_conj hq 2))

theorem cont_M3 : Continuous (M3f q) := by
  unfold M3f
  exact ((((cont_jet hq 3).mul (cont_jet_conj hq 0)).add
    (continuous_const.mul ((cont_jet hq 2).mul (cont_jet_conj hq 1)))).add
    (continuous_const.mul ((cont_jet hq 1).mul (cont_jet_conj hq 2)))).add
    ((cont_jet hq 0).mul (cont_jet_conj hq 3))

theorem per_M1 (x : ℝ) : M1f q (x + L) = M1f q x := by
  simp only [M1f, per_jet hq]

theorem per_M2 (x : ℝ) : M2f q (x + L) = M2f q x := by
  simp only [M2f, per_jet hq]

/-- Total derivative for the mass density. -/
theorem mass_v3 : (∫ x in (0 : ℝ)..L, conj (q x) * deriv (deriv (deriv q)) x).re = 0 := by
  have hf : Continuous fun x => conj (q x) * deriv (deriv (deriv q)) x := by
    have := (cont_jet_conj hq 0).mul (cont_jet hq 3)
    exact this
  refine re_integral_eq_zero (G := fun x => M2f q x - 3 * (jet q 1 x * conj (jet q 1 x)))
    (G' := fun x => M3f q x - 3 * (jet q 2 x * conj (jet q 1 x) + jet q 1 x * conj (jet q 2 x)))
    hf (fun x => ?_) ?_ ?_ ?_
  · exact (hasDerivAt_M2 hq x).sub ((hasDerivAt_aa hq 1 x).const_mul 3)
  · exact (cont_M3 hq).sub (continuous_const.mul (((cont_jet hq 2).mul (cont_jet_conj hq 1)).add
      ((cont_jet hq 1).mul (cont_jet_conj hq 2))))
  · intro x; simp only [per_M2 hq, per_jet hq]
  · intro x
    simp only [M3f, map_mul, Complex.conj_conj, jet_zero, jet_three]
    ring

end Conservation

section Conservation2

variable [Fact (0 < L)] {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (κ : ℝ)
include hq

theorem cont_Xf : Continuous (Xf κ q) := by
  rw [Xf_eq]
  have c0 := cont_jet hq 0
  have c1 := cont_jet hq 1
  have c3 := cont_jet hq 3
  have d0 := cont_jet_conj hq 0
  fun_prop

theorem cont_gE : Continuous (gE κ q) := by
  rw [gE_eq]
  have c0 := cont_jet hq 0
  have c2 := cont_jet hq 2
  have d0 := cont_jet_conj hq 0
  fun_prop

theorem cont_Nf : Continuous (Nf κ q) := by
  rw [Nf_eq]
  have c0 := cont_jet hq 0
  have c1 := cont_jet hq 1
  have d0 := cont_jet_conj hq 0
  fun_prop

theorem mass_N : (∫ x in (0 : ℝ)..L, conj (q x) * Nf κ q x).re = 0 := by
  have hf : Continuous fun x => conj (q x) * Nf κ q x :=
    (cont_jet_conj hq 0).mul (cont_Nf hq κ)
  have m0 := cont_M0 hq
  have m1 := cont_M1 hq
  refine re_integral_eq_zero (G := fun x => -3 * (κ : ℂ) * (M0f q x * M0f q x))
    (G' := fun x => -3 * (κ : ℂ) * (M1f q x * M0f q x + M0f q x * M1f q x)) hf
    (fun x => ?_) ?_ ?_ ?_
  · exact (((hasDerivAt_M0 hq x).mul (hasDerivAt_M0 hq x)).const_mul (-3 * (κ : ℂ)))
  · fun_prop
  · intro x; simp only [per_M0 hq]
  · intro x
    simp only [Nf_eq, M1f, map_mul, Complex.conj_conj, jet_zero, jet_one, M0f, hn, map_add,
      map_neg, Complex.conj_ofReal, map_ofNat]
    ring

theorem cons_E : (∫ x in (0 : ℝ)..L, conj (gE κ q x) * Xf κ q x).re = 0 := by
  have hf : Continuous fun x => conj (gE κ q x) * Xf κ q x :=
    (Complex.continuous_conj.comp (cont_gE hq κ)).mul (cont_Xf hq κ)
  have m0 := cont_M0 hq
  have m1 := cont_M1 hq
  have m2 := cont_M2 hq
  have m3 := cont_M3 hq
  have j1 := cont_jet hq 1
  have j2 := cont_jet hq 2
  have j3 := cont_jet hq 3
  have k1 := cont_jet_conj hq 1
  have k2 := cont_jet_conj hq 2
  have k3 := cont_jet_conj hq 3
  refine re_integral_eq_zero
    (G := fun x => M2f q x - 3 * (jet q 1 x * conj (jet q 1 x)) - jet q 2 x * conj (jet q 2 x)
      + 2 * (κ : ℂ) * (-(3 / 2 : ℂ) * (M0f q x * M0f q x) + M0f q x * M2f q x
        - (1 / 2 : ℂ) * (M1f q x * M1f q x))
      - 4 * (κ : ℂ) ^ 2 * (M0f q x * M0f q x * M0f q x))
    (G' := fun x => M3f q x - 3 * (jet q 2 x * conj (jet q 1 x) + jet q 1 x * conj (jet q 2 x))
      - (jet q 3 x * conj (jet q 2 x) + jet q 2 x * conj (jet q 3 x))
      + 2 * (κ : ℂ) * (-(3 / 2 : ℂ) * (M1f q x * M0f q x + M0f q x * M1f q x)
        + (M1f q x * M2f q x + M0f q x * M3f q x)
        - (1 / 2 : ℂ) * (M2f q x * M1f q x + M1f q x * M2f q x))
      - 4 * (κ : ℂ) ^ 2 * ((M1f q x * M0f q x + M0f q x * M1f q x) * M0f q x
        + M0f q x * M0f q x * M1f q x)) hf (fun x => ?_) ?_ ?_ ?_
  · have h := (((((hasDerivAt_M2 hq x).sub ((hasDerivAt_aa hq 1 x).const_mul 3)).sub
      (hasDerivAt_aa hq 2 x)).add
      ((((((hasDerivAt_M0 hq x).mul (hasDerivAt_M0 hq x)).const_mul (-(3 / 2 : ℂ))).add
        ((hasDerivAt_M0 hq x).mul (hasDerivAt_M2 hq x))).sub
        (((hasDerivAt_M1 hq x).mul (hasDerivAt_M1 hq x)).const_mul (1 / 2 : ℂ))).const_mul
        (2 * (κ : ℂ))))).sub
      ((((hasDerivAt_M0 hq x).mul (hasDerivAt_M0 hq x)).mul (hasDerivAt_M0 hq x)).const_mul
        (4 * (κ : ℂ) ^ 2))
    exact h
  · fun_prop
  · intro x
    simp only [per_M0 hq, per_M1 hq, per_M2 hq, per_jet hq]
  · intro x
    simp only [gE_eq, Xf_eq, M0f, M1f, M2f, M3f, hn, map_add, map_sub, map_mul, map_neg,
      Complex.conj_conj, Complex.conj_ofReal, map_ofNat, map_div₀, map_pow, map_one, jet_zero,
      jet_one, jet_two, jet_three]
    ring

end Conservation2

section Pair

variable [Fact (0 < L)]

/-- `⟨g, |u|² u'⟩ = ∫₀^L ḡ |u|² u'`. -/
def pairC (g : ℝ → ℂ) (u u' : AddCircle L → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..L, conj (g x) * (((‖u (x : AddCircle L)‖ ^ 2 : ℝ) : ℂ) * u' (x : AddCircle L))

/-- The pairing `⟨g, X(u)⟩ = ⟨g, u'''⟩ − 6κ⟨g, |u|²u'⟩` of a smooth `g` with `X(u)`, the third
derivative moved onto `g` (`⟨g,u'''⟩ := −⟨g''',u⟩`) and `u'` the weak derivative. -/
def Xpair (κ : ℝ) (g : ℝ → ℂ) (u u' : AddCircle L → ℂ) : ℂ :=
  - pair1 (deriv (deriv (deriv g))) u - 6 * (κ : ℂ) * pairC g u u'

theorem pair1_circ {g : ℝ → ℂ} (hg : SmoothPeriodic L g) (u : AddCircle L → ℂ) :
    pair1 g u = ∫ y, conj (lift hg y) * u y ∂(volume : Measure (AddCircle L)) :=
  pair1_eq_ip hg u

theorem pairC_circ {g : ℝ → ℂ} (hg : SmoothPeriodic L g) (u u' : AddCircle L → ℂ) :
    pairC g u u' = ∫ y, conj (lift hg y) * (((‖u y‖ ^ 2 : ℝ) : ℂ) * u' y)
      ∂(volume : Measure (AddCircle L)) := by
  unfold pairC
  rw [circ_eq_interval]
  exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])

theorem pair1_cmul (g : ℝ → ℂ) (c : ℂ) (u : AddCircle L → ℂ) :
    pair1 g (fun y => c * u y) = c * pair1 g u := by
  unfold pair1
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun x _ => by simp only; ring)

theorem pair1_add {g : ℝ → ℂ} (hg : Continuous g) {u z : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) (hz : MemLp z 2 (volume : Measure (AddCircle L))) :
    pair1 g (fun y => u y + z y) = pair1 g u + pair1 g z := by
  unfold pair1
  simp_rw [mul_add]
  exact intervalIntegral.integral_add (intervalIntegrable_pair hg hu) (intervalIntegrable_pair hg hz)

theorem pair1_sub {g : ℝ → ℂ} (hg : Continuous g) {u z : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) (hz : MemLp z 2 (volume : Measure (AddCircle L))) :
    pair1 g (fun y => u y - z y) = pair1 g u - pair1 g z := by
  unfold pair1
  simp_rw [mul_sub]
  exact intervalIntegral.integral_sub (intervalIntegrable_pair hg hu) (intervalIntegrable_pair hg hz)

theorem pair1_comb {g₁ g₂ : ℝ → ℂ} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    {u : AddCircle L → ℂ} (hu : MemLp u 2 (volume : Measure (AddCircle L))) (c₁ c₂ : ℂ) :
    pair1 (fun x => c₁ * g₁ x + c₂ * g₂ x) u = conj c₁ * pair1 g₁ u + conj c₂ * pair1 g₂ u := by
  unfold pair1
  have e : ∀ x : ℝ, conj (c₁ * g₁ x + c₂ * g₂ x) * u (x : AddCircle L) =
      conj c₁ * (conj (g₁ x) * u (x : AddCircle L)) + conj c₂ * (conj (g₂ x) * u (x : AddCircle L)) := by
    intro x; simp only [map_add, map_mul]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_add ((intervalIntegrable_pair h₁ hu).const_mul _)
    ((intervalIntegrable_pair h₂ hu).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

theorem norm_lift_le {g : ℝ → ℂ} (hg : SmoothPeriodic L g) {B : ℝ} (h : ∀ x, ‖g x‖ ≤ B)
    (y : AddCircle L) : ‖lift hg y‖ ≤ B := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [lift_coe]; exact h x

end Pair

section IntW

variable [Fact (0 < L)]

theorem memLp_normsq_real {w : AddCircle L → ℂ} (hw : H04 L 1 w) :
    MemLp (fun y => ‖w y‖ ^ 2) 2 (volume : Measure (AddCircle L)) := by
  have hm : AEStronglyMeasurable (fun y => ‖w y‖ ^ 2) (volume : Measure (AddCircle L)) :=
    (hw.1.aestronglyMeasurable.norm).pow 2
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine (quartic_integrable hw).congr (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [Real.norm_of_nonneg (by positivity)]
  ring

theorem int_norm {w : AddCircle L → ℂ} (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => ‖w y‖) (volume : Measure (AddCircle L)) :=
  hw.norm.integrable (by norm_num)

theorem int_norm_sq {w : AddCircle L → ℂ} (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => ‖w y‖ ^ 2) (volume : Measure (AddCircle L)) :=
  hw.norm.integrable_sq

theorem int_norm_mul {w w' : AddCircle L → ℂ} (hw : MemLp w 2 (volume : Measure (AddCircle L)))
    (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => ‖w y‖ * ‖w' y‖) (volume : Measure (AddCircle L)) :=
  hw.norm.integrable_mul hw'.norm

theorem int_sq_mul {w w' : AddCircle L → ℂ} (hw : H04 L 1 w)
    (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => ‖w y‖ ^ 2 * ‖w' y‖) (volume : Measure (AddCircle L)) :=
  (memLp_normsq_real hw).integrable_mul hw'.norm

/-- Linear part integrand `ḡ(|q|² w' + 2Re(q̄ w) q')`. -/
def fLin (G Q Q' w w' : AddCircle L → ℂ) (y : AddCircle L) : ℂ :=
  conj (G y) * (((‖Q y‖ ^ 2 : ℝ) : ℂ) * w' y + ((2 * (conj (Q y) * w y).re : ℝ) : ℂ) * Q' y)

/-- Remainder integrand `ḡ(2Re(q̄ w) w' + |w|² q' + |w|² w')`. -/
def fRem (G Q Q' w w' : AddCircle L → ℂ) (y : AddCircle L) : ℂ :=
  conj (G y) * (((2 * (conj (Q y) * w y).re : ℝ) : ℂ) * w' y + ((‖w y‖ ^ 2 : ℝ) : ℂ) * Q' y +
    ((‖w y‖ ^ 2 : ℝ) : ℂ) * w' y)

theorem pt_fLin {G Q Q1 w w1 : ℂ} {B M M1 : ℝ} (hG : ‖G‖ ≤ B) (hQ : ‖Q‖ ≤ M) (hQ1 : ‖Q1‖ ≤ M1) :
    ‖conj G * (((‖Q‖ ^ 2 : ℝ) : ℂ) * w1 + ((2 * (conj Q * w).re : ℝ) : ℂ) * Q1)‖ ≤
      B * (M ^ 2 * ‖w1‖ + 2 * M * M1 * ‖w‖) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hG
  have hM : 0 ≤ M := (norm_nonneg _).trans hQ
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans hQ1
  have hre : |(conj Q * w).re| ≤ M * ‖w‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
  have h1 : ‖(((‖Q‖ ^ 2 : ℝ) : ℂ)) * w1‖ ≤ M ^ 2 * ‖w1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hQ 2) (norm_nonneg _)
  have h2 : ‖((2 * (conj Q * w).re : ℝ) : ℂ) * Q1‖ ≤ 2 * M * M1 * ‖w‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have : 2 * |(conj Q * w).re| * ‖Q1‖ ≤ 2 * (M * ‖w‖) * M1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hre (by norm_num)) hQ1 (norm_nonneg _) (by positivity)
    nlinarith
  rw [norm_mul, RCLike.norm_conj]
  refine mul_le_mul hG ?_ (norm_nonneg _) hB
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem pt_fRem {G Q Q1 w w1 : ℂ} {B M M1 : ℝ} (hG : ‖G‖ ≤ B) (hQ : ‖Q‖ ≤ M) (hQ1 : ‖Q1‖ ≤ M1) :
    ‖conj G * (((2 * (conj Q * w).re : ℝ) : ℂ) * w1 + ((‖w‖ ^ 2 : ℝ) : ℂ) * Q1 +
      ((‖w‖ ^ 2 : ℝ) : ℂ) * w1)‖ ≤
      B * (2 * M * ‖w‖ * ‖w1‖ + M1 * ‖w‖ ^ 2 + ‖w‖ ^ 2 * ‖w1‖) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hG
  have hM : 0 ≤ M := (norm_nonneg _).trans hQ
  have hM1 : 0 ≤ M1 := (norm_nonneg _).trans hQ1
  have hre : |(conj Q * w).re| ≤ M * ‖w‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right hQ (norm_nonneg _)
  have h1 : ‖((2 * (conj Q * w).re : ℝ) : ℂ) * w1‖ ≤ 2 * M * ‖w‖ * ‖w1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have : 2 * |(conj Q * w).re| ≤ 2 * (M * ‖w‖) := mul_le_mul_of_nonneg_left hre (by norm_num)
    nlinarith [norm_nonneg w1]
  have h2 : ‖((‖w‖ ^ 2 : ℝ) : ℂ) * Q1‖ ≤ M1 * ‖w‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    nlinarith [sq_nonneg ‖w‖]
  have h3 : ‖((‖w‖ ^ 2 : ℝ) : ℂ) * w1‖ ≤ ‖w‖ ^ 2 * ‖w1‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [norm_mul, RCLike.norm_conj]
  refine mul_le_mul hG ?_ (norm_nonneg _) hB
  exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add h1 h2) h3)

theorem exists_bound_circ {f : AddCircle L → ℂ} (hf : Continuous f) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖f y‖ ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (f := f) hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun y => (hC y (Set.mem_univ y)).trans (le_max_left _ _)⟩

theorem integrable_fLin {G Q Q' w w' : AddCircle L → ℂ} (hG : Continuous G) (hQ : Continuous Q)
    (hQ' : Continuous Q') (hw : MemLp w 2 (volume : Measure (AddCircle L)))
    (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    Integrable (fLin G Q Q' w w') (volume : Measure (AddCircle L)) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_circ hG
  obtain ⟨M, hM0, hM⟩ := exists_bound_circ hQ
  obtain ⟨M1, hM10, hM1⟩ := exists_bound_circ hQ'
  have hm : AEStronglyMeasurable (fLin G Q Q' w w') (volume : Measure (AddCircle L)) := by
    have h1 := hw.aestronglyMeasurable
    have h2 := hw'.aestronglyMeasurable
    unfold fLin
    fun_prop
  refine Integrable.mono' (g := fun y => B * (M ^ 2 * ‖w' y‖ + 2 * M * M1 * ‖w y‖)) ?_ hm
    (Filter.Eventually.of_forall fun y => pt_fLin (hB y) (hM y) (hM1 y))
  exact ((int_norm hw').const_mul (M ^ 2)).add ((int_norm hw).const_mul (2 * M * M1)) |>.const_mul B

theorem integrable_fRem {G Q Q' w w' : AddCircle L → ℂ} (hG : Continuous G) (hQ : Continuous Q)
    (hQ' : Continuous Q') (hw : H04 L 1 w)
    (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    Integrable (fRem G Q Q' w w') (volume : Measure (AddCircle L)) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_circ hG
  obtain ⟨M, hM0, hM⟩ := exists_bound_circ hQ
  obtain ⟨M1, hM10, hM1⟩ := exists_bound_circ hQ'
  have hm : AEStronglyMeasurable (fRem G Q Q' w w') (volume : Measure (AddCircle L)) := by
    have h1 := hw.1.aestronglyMeasurable
    have h2 := hw'.aestronglyMeasurable
    unfold fRem
    fun_prop
  refine Integrable.mono' (g := fun y => B * (2 * M * ‖w y‖ * ‖w' y‖ + M1 * ‖w y‖ ^ 2 +
    ‖w y‖ ^ 2 * ‖w' y‖)) ?_ hm
    (Filter.Eventually.of_forall fun y => pt_fRem (hB y) (hM y) (hM1 y))
  have i1 : Integrable (fun y => 2 * M * ‖w y‖ * ‖w' y‖) (volume : Measure (AddCircle L)) := by
    have := (int_norm_mul hw.1 hw').const_mul (2 * M)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only; ring
  exact ((i1.add ((int_norm_sq hw.1).const_mul M1)).add (int_sq_mul hw hw')).const_mul B

end IntW

section Decomp

variable [Fact (0 < L)]

def LinC (G Q Q' w w' : AddCircle L → ℂ) : ℂ := ∫ y, fLin G Q Q' w w' y ∂(volume : Measure (AddCircle L))

def RemC (G Q Q' w w' : AddCircle L → ℂ) : ℂ := ∫ y, fRem G Q Q' w w' y ∂(volume : Measure (AddCircle L))

theorem normsq_add (Q w : ℂ) :
    ((‖Q + w‖ ^ 2 : ℝ) : ℂ) = ((‖Q‖ ^ 2 : ℝ) : ℂ) + ((2 * (conj Q * w).re : ℝ) : ℂ) +
      ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  have : ‖Q + w‖ ^ 2 = ‖Q‖ ^ 2 + 2 * (conj Q * w).re + ‖w‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  rw [this]; push_cast; ring

/-- The zeroth-order integrand `ḡ|q|²q'`. -/
def fZero (G Q Q' : AddCircle L → ℂ) (y : AddCircle L) : ℂ :=
  conj (G y) * (((‖Q y‖ ^ 2 : ℝ) : ℂ) * Q' y)

theorem pairC_decomp {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q)
    {w w' : AddCircle L → ℂ} (hw : H04 L 1 w) (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    pairC g (fun y => lift hq y + w y) (fun y => lift (sp_deriv hq) y + w' y) =
      pairC g (lift hq) (lift (sp_deriv hq)) +
        LinC (lift hg) (lift hq) (lift (sp_deriv hq)) w w' +
        RemC (lift hg) (lift hq) (lift (sp_deriv hq)) w w' := by
  have cG := continuous_lift hg
  have cQ := continuous_lift hq
  have cQ' := continuous_lift (sp_deriv hq)
  have hL := integrable_fLin cG cQ cQ' hw.1 hw'
  have hR := integrable_fRem cG cQ cQ' hw hw'
  have h0 : Integrable (fZero (lift hg) (lift hq) (lift (sp_deriv hq)))
      (volume : Measure (AddCircle L)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    unfold fZero
    fun_prop
  have h1 : pairC g (lift hq) (lift (sp_deriv hq)) =
      ∫ y, fZero (lift hg) (lift hq) (lift (sp_deriv hq)) y ∂(volume : Measure (AddCircle L)) :=
    pairC_circ hg _ _
  rw [pairC_circ hg, h1]
  unfold LinC RemC
  have hsum : ∫ y, conj (lift hg y) * (((‖lift hq y + w y‖ ^ 2 : ℝ) : ℂ) *
      (lift (sp_deriv hq) y + w' y)) ∂(volume : Measure (AddCircle L)) =
      ∫ y, ((fZero (lift hg) (lift hq) (lift (sp_deriv hq)) y +
        fLin (lift hg) (lift hq) (lift (sp_deriv hq)) w w' y) +
        fRem (lift hg) (lift hq) (lift (sp_deriv hq)) w w' y) ∂(volume : Measure (AddCircle L)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [fZero, fLin, fRem]
    rw [normsq_add]
    ring
  have hZL : Integrable (fun y => fZero (lift hg) (lift hq) (lift (sp_deriv hq)) y +
      fLin (lift hg) (lift hq) (lift (sp_deriv hq)) w w' y) (volume : Measure (AddCircle L)) :=
    h0.add hL
  rw [hsum, integral_add hZL hR, integral_add h0 hL]

theorem sp_conj {f : ℝ → ℂ} (hf : SmoothPeriodic L f) : SmoothPeriodic L (fun x => conj (f x)) :=
  ⟨(Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp hf.smooth, fun x => by simp only [hf.periodic x]⟩

theorem deriv_conj_fun {f : ℝ → ℂ} (hf : SmoothPeriodic L f) :
    deriv (fun x => conj (f x)) = fun x => conj (deriv f x) :=
  funext fun x => ((hasDerivAt_of_smooth hf x).star).deriv

theorem ibp_conj {f g : ℝ → ℂ} (hf : SmoothPeriodic L f) (hg : SmoothPeriodic L g) :
    ∫ x in (0 : ℝ)..L, conj (f x) * deriv g x = -∫ x in (0 : ℝ)..L, conj (deriv f x) * g x := by
  have := ibp_smooth (sp_conj hf) hg
  rw [deriv_conj_fun hf] at this
  exact this

theorem pair1_lift_eq {g : ℝ → ℂ} {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    pair1 g (lift hv) = ∫ x in (0 : ℝ)..L, conj (g x) * v x := by
  unfold pair1
  exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])

theorem pairC_lift_eq {g : ℝ → ℂ} {q : ℝ → ℂ} (hq : SmoothPeriodic L q) :
    pairC g (lift hq) (lift (sp_deriv hq)) =
      ∫ x in (0 : ℝ)..L, conj (g x) * (((‖q x‖ ^ 2 : ℝ) : ℂ) * deriv q x) := by
  unfold pairC
  exact intervalIntegral.integral_congr (fun x _ => by simp only [lift_coe])

/-- For smooth `u = q`, `⟨g, X(q)⟩` is the classical pairing `∫ ḡ X(q)`: the third derivative
moved onto `g` agrees with the classical third derivative of `q`. -/
theorem Xpair_smooth (κ : ℝ) {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q) :
    Xpair κ g (lift hq) (lift (sp_deriv hq)) = ∫ x in (0 : ℝ)..L, conj (g x) * Xf κ q x := by
  have h1 := sp_deriv hg
  have h2 := sp_deriv h1
  have hq1 := sp_deriv hq
  have hq2 := sp_deriv hq1
  have iB := ibp_conj h2 hq
  have iC := ibp_conj h1 hq1
  have iD := ibp_conj hg hq2
  have eA : pair1 (deriv (deriv (deriv g))) (lift hq) =
      -∫ x in (0 : ℝ)..L, conj (g x) * deriv (deriv (deriv q)) x := by
    rw [pair1_lift_eq hq]
    linear_combination iB - iC + iD
  have c1 : Continuous fun x => conj (g x) * deriv (deriv (deriv q)) x :=
    (Complex.continuous_conj.comp hg.smooth.continuous).mul (deriv_continuous hq2)
  have c2 : Continuous fun x => conj (g x) * (((‖q x‖ ^ 2 : ℝ) : ℂ) * deriv q x) :=
    (Complex.continuous_conj.comp hg.smooth.continuous).mul
      ((Complex.continuous_ofReal.comp ((continuous_norm.comp hq.smooth.continuous).pow 2)).mul
        (deriv_continuous hq))
  unfold Xpair
  rw [eA, pairC_lift_eq hq]
  have : ∀ x : ℝ, conj (g x) * Xf κ q x =
      conj (g x) * deriv (deriv (deriv q)) x -
        6 * (κ : ℂ) * (conj (g x) * (((‖q x‖ ^ 2 : ℝ) : ℂ) * deriv q x)) := by
    intro x; simp only [Xf]; ring
  simp_rw [this]
  rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _)
    ((c2.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul]
  ring

end Decomp

section Lam

variable [Fact (0 < L)]

theorem sp_normsq {q : ℝ → ℂ} (hq : SmoothPeriodic L q) :
    SmoothPeriodic L (fun x => ((‖q x‖ ^ 2 : ℝ) : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp ((contDiff_norm_sq ℝ).comp hq.smooth),
    fun x => by simp only [hq.periodic x]⟩

theorem sp_mul {a b : ℝ → ℂ} (ha : SmoothPeriodic L a) (hb : SmoothPeriodic L b) :
    SmoothPeriodic L (fun x => a x * b x) :=
  ⟨ha.smooth.mul hb.smooth, fun x => by simp only [ha.periodic x, hb.periodic x]⟩

theorem sp_re_conj_mul {a b : ℝ → ℂ} (ha : SmoothPeriodic L a) (hb : SmoothPeriodic L b) :
    SmoothPeriodic L (fun x => ((2 * (conj (a x) * b x).re : ℝ) : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (Complex.reCLM.contDiff.comp
    (((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp ha.smooth).mul hb.smooth))),
    fun x => by simp only [ha.periodic x, hb.periodic x]⟩

theorem sp_Xf (κ : ℝ) {q : ℝ → ℂ} (hq : SmoothPeriodic L q) : SmoothPeriodic L (Xf κ q) := by
  have e : Xf κ q = fun x => jet q 3 x - 6 * (κ : ℂ) * (((‖q x‖ ^ 2 : ℝ) : ℂ) * jet q 1 x) := by
    funext x; simp only [Xf, jet_three, jet_one]; ring
  rw [e]
  have h1 := sp_jet hq 3
  have h2 := sp_mul (sp_normsq hq) (sp_jet hq 1)
  exact ⟨h1.smooth.sub (contDiff_const.mul h2.smooth), fun x => by
    simp only [h1.periodic x, h2.periodic x]⟩

theorem sp_gE (κ : ℝ) {q : ℝ → ℂ} (hq : SmoothPeriodic L q) : SmoothPeriodic L (gE κ q) :=
  ⟨(sp_lvec hq).smooth.add (contDiff_const.mul (sp_rvec hq).smooth), fun x => by
    simp only [gE, (sp_lvec hq).periodic x, (sp_rvec hq).periodic x]⟩

theorem lift_eq_fun {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (G : AddCircle L → ℂ)
    (h : ∀ x : ℝ, G (x : AddCircle L) = f x) : lift hf = G := by
  funext y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [lift_coe, h]

theorem lift_conj_eq {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (y : AddCircle L) :
    lift (sp_conj hf) y = conj (lift hf y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  simp only [lift_coe]

theorem lift_deriv_conj {f : ℝ → ℂ} (hf : SmoothPeriodic L f) (y : AddCircle L) :
    lift (sp_deriv (sp_conj hf)) y = conj (lift (sp_deriv hf) y) := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  simp only [lift_coe]
  rw [deriv_conj_fun hf]

theorem pair1_cfun (c : ℂ) (g : ℝ → ℂ) (u : AddCircle L → ℂ) :
    pair1 (fun x => c * g x) u = conj c * pair1 g u := by
  unfold pair1
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr (fun x _ => by simp only [map_mul]; ring)

theorem pair1_add_fun {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B) {u : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) :
    pair1 (fun x => A x + B x) u = pair1 A u + pair1 B u := by
  unfold pair1
  simp_rw [map_add, add_mul]
  exact intervalIntegral.integral_add (intervalIntegrable_pair hA hu) (intervalIntegrable_pair hB hu)

theorem Ia_eq {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q)
    {w w' : AddCircle L → ℂ} (hd : IsWD w w') :
    ∫ y, conj (lift hg y) * (((‖lift hq y‖ ^ 2 : ℝ) : ℂ) * w' y) ∂(volume : Measure (AddCircle L)) =
      - pair1 (deriv (fun x => g x * ((‖q x‖ ^ 2 : ℝ) : ℂ))) w := by
  have he : SmoothPeriodic L (fun x => g x * ((‖q x‖ ^ 2 : ℝ) : ℂ)) := sp_mul hg (sp_normsq hq)
  have h := hd.ibp (sp_conj he)
  have e1 : ∀ y, lift (sp_conj he) y * w' y =
      conj (lift hg y) * (((‖lift hq y‖ ^ 2 : ℝ) : ℂ) * w' y) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    simp only [lift_coe, map_mul, Complex.conj_ofReal]; ring
  have e2 : ∀ y, lift (sp_deriv (sp_conj he)) y * w y = conj (lift (sp_deriv he) y) * w y := by
    intro y; rw [lift_deriv_conj he]
  simp_rw [e1, e2] at h
  rw [h, pair1_circ (sp_deriv he)]

end Lam

section Lam2

variable [Fact (0 < L)]

theorem integrable_Ia {G Q w' : AddCircle L → ℂ} (hG : Continuous G) (hQ : Continuous Q)
    (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => conj (G y) * (((‖Q y‖ ^ 2 : ℝ) : ℂ) * w' y))
      (volume : Measure (AddCircle L)) := by
  have hc : Continuous fun y => conj (G y) * ((‖Q y‖ ^ 2 : ℝ) : ℂ) := by fun_prop
  obtain ⟨B, -, hB⟩ := exists_bound_circ hc
  have := (hw'.integrable (by norm_num)).bdd_mul (f := fun y => conj (G y) * ((‖Q y‖ ^ 2 : ℝ) : ℂ))
    hc.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only; ring

theorem integrable_Ib {G Q Q' w : AddCircle L → ℂ} (hG : Continuous G) (hQ : Continuous Q)
    (hQ' : Continuous Q') (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => conj (G y) * (((2 * (conj (Q y) * w y).re : ℝ) : ℂ) * Q' y))
      (volume : Measure (AddCircle L)) := by
  have hint : Integrable (fun y => conj (Q y) * w y) (volume : Measure (AddCircle L)) :=
    integrable_conj_mul (memLp_of_continuous hQ) hw
  have hre : Integrable (fun y => ((2 * (conj (Q y) * w y).re : ℝ) : ℂ))
      (volume : Measure (AddCircle L)) := by
    have := (hint.re.const_mul 2).ofReal (𝕜 := ℂ)
    simpa using this
  have hc : Continuous fun y => conj (G y) * Q' y := by fun_prop
  obtain ⟨B, -, hB⟩ := exists_bound_circ hc
  have := hre.bdd_mul (f := fun y => conj (G y) * Q' y) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hB)
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only; ring

theorem Ib_re {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q)
    {w : AddCircle L → ℂ} (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    (∫ y, conj (lift hg y) * (((2 * (conj (lift hq y) * w y).re : ℝ) : ℂ) * lift (sp_deriv hq) y)
        ∂(volume : Measure (AddCircle L))).re =
      (pair1 (fun x => ((2 * (conj (g x) * deriv q x).re : ℝ) : ℂ) * q x) w).re := by
  have hsm : SmoothPeriodic L (fun x => ((2 * (conj (g x) * deriv q x).re : ℝ) : ℂ) * q x) :=
    sp_mul (sp_re_conj_mul hg (sp_deriv hq)) hq
  have iL := integrable_Ib (continuous_lift hg) (continuous_lift hq) (continuous_lift (sp_deriv hq)) hw
  have iR : Integrable (fun y => conj (lift hsm y) * w y) (volume : Measure (AddCircle L)) :=
    integrable_conj_mul (memLp_of_continuous (continuous_lift hsm)) hw
  rw [pair1_circ hsm]
  have e1 := integral_re iL
  have e2 := integral_re iR
  simp only [RCLike.re_to_complex] at e1 e2
  rw [← e1, ← e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
  simp only [lift_coe, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im]
  ring

/-- The kernel of the linear part after moving every derivative off `w`. -/
def k2 (κ : ℝ) (g q : ℝ → ℂ) : ℝ → ℂ := fun x =>
  (-1 : ℂ) * deriv (deriv (deriv g)) x +
    6 * (κ : ℂ) * deriv (fun y => g y * ((‖q y‖ ^ 2 : ℝ) : ℂ)) x +
    (-(6 * (κ : ℂ))) * (((2 * (conj (g x) * deriv q x).re : ℝ) : ℂ) * q x)

theorem cont_k2 (κ : ℝ) {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q) :
    Continuous (k2 κ g q) := by
  have h3 := sp_deriv (sp_deriv (sp_deriv hg))
  have he := sp_deriv (sp_mul hg (sp_normsq hq))
  have hr := sp_mul (sp_re_conj_mul hg (sp_deriv hq)) hq
  unfold k2
  exact ((continuous_const.mul h3.smooth.continuous).add
    (continuous_const.mul he.smooth.continuous)).add (continuous_const.mul hr.smooth.continuous)

theorem cont_k1 (κ : ℝ) {q h : ℝ → ℂ} (hq : SmoothPeriodic L q) (hh : SmoothPeriodic L h) :
    Continuous (k1 κ q h) := by
  have h2 := sp_deriv (sp_deriv hh)
  have hn := sp_normsq hq
  unfold k1 lvec
  have c1 := hq.smooth.continuous
  have c2 := hh.smooth.continuous
  have c3 := h2.smooth.continuous
  have c4 := hn.smooth.continuous
  fun_prop

theorem LamId (κ : ℝ) {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q)
    {w w' : AddCircle L → ℂ} (hw : H04 L 1 w) (hd : IsWD w w') :
    (-pair1 (deriv (deriv (deriv g))) w - 6 * (κ : ℂ) *
        LinC (lift hg) (lift hq) (lift (sp_deriv hq)) w w').re =
      (pair1 (k2 κ g q) w).re := by
  have cG := continuous_lift hg
  have cQ := continuous_lift hq
  have cQ' := continuous_lift (sp_deriv hq)
  have iA := integrable_Ia cG cQ hd.2.1
  have iB := integrable_Ib cG cQ cQ' hw.1
  have hLin : LinC (lift hg) (lift hq) (lift (sp_deriv hq)) w w' =
      (∫ y, conj (lift hg y) * (((‖lift hq y‖ ^ 2 : ℝ) : ℂ) * w' y) ∂(volume : Measure (AddCircle L))) +
      ∫ y, conj (lift hg y) * (((2 * (conj (lift hq y) * w y).re : ℝ) : ℂ) * lift (sp_deriv hq) y)
        ∂(volume : Measure (AddCircle L)) := by
    unfold LinC
    rw [← integral_add iA iB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [fLin]; ring
  rw [hLin, Ia_eq hg hq hd]
  have hIb := Ib_re hg hq hw.1
  set Ib := ∫ y, conj (lift hg y) * (((2 * (conj (lift hq y) * w y).re : ℝ) : ℂ) *
    lift (sp_deriv hq) y) ∂(volume : Measure (AddCircle L)) with hIbdef
  have h3 := sp_deriv (sp_deriv (sp_deriv hg))
  have he := sp_deriv (sp_mul hg (sp_normsq hq))
  have hr := sp_mul (sp_re_conj_mul hg (sp_deriv hq)) hq
  have hk : pair1 (k2 κ g q) w = conj (-1 : ℂ) * pair1 (deriv (deriv (deriv g))) w +
      conj (6 * (κ : ℂ)) * pair1 (deriv (fun y => g y * ((‖q y‖ ^ 2 : ℝ) : ℂ))) w +
      conj (-(6 * (κ : ℂ))) * pair1 (fun x => ((2 * (conj (g x) * deriv q x).re : ℝ) : ℂ) * q x) w := by
    unfold k2
    rw [pair1_add_fun (A := fun x => (-1 : ℂ) * deriv (deriv (deriv g)) x +
          6 * (κ : ℂ) * deriv (fun y => g y * ((‖q y‖ ^ 2 : ℝ) : ℂ)) x)
        (B := fun x => (-(6 * (κ : ℂ))) * (((2 * (conj (g x) * deriv q x).re : ℝ) : ℂ) * q x))
        ((continuous_const.mul h3.smooth.continuous).add
        (continuous_const.mul he.smooth.continuous)) (continuous_const.mul hr.smooth.continuous) hw.1,
      pair1_add_fun (A := fun x => (-1 : ℂ) * deriv (deriv (deriv g)) x)
        (B := fun x => 6 * (κ : ℂ) * deriv (fun y => g y * ((‖q y‖ ^ 2 : ℝ) : ℂ)) x)
        (continuous_const.mul h3.smooth.continuous)
        (continuous_const.mul he.smooth.continuous) hw.1,
      pair1_cfun, pair1_cfun, pair1_cfun]
  rw [hk]
  generalize pair1 (fun x => ((2 * (conj (g x) * deriv q x).re : ℝ) : ℂ) * q x) w = R at hIb ⊢
  generalize pair1 (deriv (deriv (deriv g))) w = P
  generalize pair1 (deriv (fun y => g y * ((‖q y‖ ^ 2 : ℝ) : ℂ))) w = Q1
  have h6 : (6 * (κ : ℂ)) = ((6 * κ : ℝ) : ℂ) := by push_cast; ring
  simp only [map_neg, map_one, h6, Complex.conj_ofReal, Complex.add_re, Complex.sub_re,
    Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
    Complex.one_im, neg_mul, mul_neg, zero_mul, sub_zero, one_mul, neg_neg, neg_zero, mul_zero,
    Complex.neg_im, add_zero, zero_sub, Complex.add_im, Complex.neg_re]
  rw [← hIb]
  ring

end Lam2

section C1sec

variable [Fact (0 < L)]

theorem k1_k2_ker (κ : ℝ) (q : ℝ → ℂ) (x : ℝ) :
    k1 κ q (Xf κ q) x + k2 κ (gE κ q) q x = kerK κ q x := by
  simp only [kerK, k2]
  push_cast
  ring

/-- **The derivative of the conservation law, tested against `w`** (`eq:A1-conservation-derivative`):
`d²E(q)[X(q), w] + dE(q)[DX(q) w] = 0`, with `d²E(q)[h,w] = 2Re⟨k1 q h, w⟩` and
`dE(q)[DX(q)w] = 2Re (linear part)`. -/
theorem C1_identity (κ : ℝ) {q : ℝ → ℂ} (hq : SmoothPeriodic L q) {w : AddCircle L → ℂ}
    (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    (pair1 (k1 κ q (Xf κ q)) w).re + (pair1 (k2 κ (gE κ q) q) w).re = 0 := by
  have hX := sp_Xf κ hq
  have hg := sp_gE κ hq
  have h := pair1_add_fun (cont_k1 κ hq hX) (cont_k2 κ hg hq) hw
  have hz : (fun x => k1 κ q (Xf κ q) x + k2 κ (gE κ q) q x) = fun _ => (0 : ℂ) :=
    funext fun x => by rw [k1_k2_ker, kerK_eq_zero hq]
  rw [hz] at h
  have h0 : pair1 (fun _ => (0 : ℂ)) w = 0 := by simp [pair1]
  rw [h0] at h
  have := congrArg Complex.re h
  simpa using this.symm

end C1sec

section Sigma

/-- The printed polynomial `S_v` of `eq:A1-S` as a function of the data
`α = ⟨v,u⟩`, `a = ⟨ℓ,u⟩`, `b = ⟨r_v,u⟩`, `E₂(v)`, `V₄(v)`. -/
def Sigma (κ E₂ V₄ : ℝ) (α a b : ℂ) : ℝ :=
  2 * (conj α * a).re - ‖α‖ ^ 2 * E₂ + 4 * κ * ‖α‖ ^ 2 * (conj α * b).re - 3 * κ * ‖α‖ ^ 4 * V₄

/-- Its directional derivative along data `(α', a', b', E₂', V₄')`. -/
def dSigma (κ E₂ V₄ : ℝ) (α a b α' a' b' : ℂ) (E₂' V₄' : ℝ) : ℝ :=
  2 * (conj α' * a + conj α * a').re - 2 * (conj α * α').re * E₂ - ‖α‖ ^ 2 * E₂'
    + 4 * κ * (2 * (conj α * α').re * (conj α * b).re + ‖α‖ ^ 2 * (conj α' * b + conj α * b').re)
    - 12 * κ * ‖α‖ ^ 2 * (conj α * α').re * V₄ - 3 * κ * ‖α‖ ^ 4 * V₄'

theorem dSigma_add (κ E₂ V₄ : ℝ) (α a b α₁ a₁ b₁ α₂ a₂ b₂ : ℂ) (E₁ V₁ E₂' V₂ : ℝ) :
    dSigma κ E₂ V₄ α a b α₁ a₁ b₁ E₁ V₁ + dSigma κ E₂ V₄ α a b α₂ a₂ b₂ E₂' V₂ =
    dSigma κ E₂ V₄ α a b (α₁ + α₂) (a₁ + a₂) (b₁ + b₂) (E₁ + E₂') (V₁ + V₂) := by
  unfold dSigma
  simp only [map_add, mul_add, add_mul, Complex.add_re]
  ring

/-- The algebraic core of the relative-energy computation: with `a = αE₂ + λ`, `b = αV₄ + θ`
(`λ = ⟨ℓ,w⟩`, `θ = ⟨r_v,w⟩`), the directional derivative of `S_v` is
`2Re(ᾱ̇ λ) + 8κ Re(ᾱα̇)Re(ᾱθ) + 4κ|α|²Re(ᾱ̇ θ) + 2Re(ᾱ(ȧ + 2κ|α|²ḃ)) − |α|²Ed₂ − 3κ|α|⁴Vd₄`. -/
theorem dSigma_star (κ p V Ed Vd : ℝ) (α lam th α' a' b' : ℂ) :
    dSigma κ p V α (α * (p : ℂ) + lam) (α * (V : ℂ) + th) α' a' b' Ed Vd =
      2 * (conj α' * lam).re + 8 * κ * (conj α * α').re * (conj α * th).re
        + 4 * κ * ‖α‖ ^ 2 * (conj α' * th).re
        + 2 * (conj α * (a' + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * b')).re
        - ‖α‖ ^ 2 * Ed - 3 * κ * ‖α‖ ^ 4 * Vd := by
  have h2 : ‖α‖ ^ 2 = α.re * α.re + α.im * α.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h4 : ‖α‖ ^ 4 = (α.re * α.re + α.im * α.im) ^ 2 := by rw [← h2]; ring
  unfold dSigma
  rw [h4, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end Sigma

section TData

variable [Fact (0 < L)]

/-- `D r_v[ξ] = 2Re(v̄ξ) v + |v|² ξ`: the directional derivative of `r_v = |v|²v` at `v` along `ξ`. -/
def Drv (v ξ : ℝ → ℂ) : ℝ → ℂ := fun x =>
  ((2 * (conj (v x) * ξ x).re : ℝ) : ℂ) * v x + ((‖v x‖ ^ 2 : ℝ) : ℂ) * ξ x

/-- `dE₂(v)[ξ] = ∫₀^L (2Re(v̄'ξ') + 2Re(v̄ξ))`: the directional derivative of `E₂(v)`. -/
def E2dot (L : ℝ) (v ξ : ℝ → ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..L, (2 * (conj (deriv v x) * deriv ξ x).re + 2 * (conj (v x) * ξ x).re)

/-- `dV₄(v)[ξ] = ∫₀^L 4|v|² Re(v̄ξ)`: the directional derivative of `V₄(v)`. -/
def V4dot (L : ℝ) (v ξ : ℝ → ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..L, 4 * ‖v x‖ ^ 2 * (conj (v x) * ξ x).re

theorem re_intervalIntegral {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 L) :
    (∫ x in (0 : ℝ)..L, f x).re = ∫ x in (0 : ℝ)..L, (f x).re := by
  have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hf
  simpa using this.symm

theorem pair1_lvec_self {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    pair1 (lvec v) (lift hv) = ((E2 L v : ℝ) : ℂ) := by
  rw [pair1_eq_ip (sp_lvec hv), ← ip1_eq_ip_lvec hv (h04_lift hv), ip1_self,
    ← h04Norm_sq, E2_eq hv]

theorem pair1_rvec_self {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    pair1 (rvec v) (lift hv) = ((V4 L v : ℝ) : ℂ) := by
  rw [pair1_lift_eq hv]
  unfold V4
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [rvec, map_mul, Complex.conj_ofReal]
  have : ((‖v x‖ ^ 4 : ℝ) : ℂ) = ((‖v x‖ ^ 2 : ℝ) : ℂ) * (conj (v x) * v x) := by
    rw [Complex.conj_mul']; push_cast; ring
  rw [this]; ring

theorem E2dot_rel {v ξ : ℝ → ℂ} (hv : SmoothPeriodic L v) (hξ : SmoothPeriodic L ξ) :
    2 * (pair1 (lvec ξ) (lift hv)).re = E2dot L v ξ := by
  have h1 := sp_deriv hξ
  have h2 := sp_deriv h1
  have iB := ibp_conj h1 hv
  have c1 : Continuous fun x => conj (ξ x) * v x :=
    (Complex.continuous_conj.comp hξ.smooth.continuous).mul hv.smooth.continuous
  have c2 : Continuous fun x => conj (deriv (deriv ξ) x) * v x :=
    (Complex.continuous_conj.comp (deriv_continuous h1)).mul hv.smooth.continuous
  have c3 : Continuous fun x => conj (deriv ξ x) * deriv v x :=
    (Complex.continuous_conj.comp (deriv_continuous hξ)).mul (deriv_continuous hv)
  have e : pair1 (lvec ξ) (lift hv) =
      ∫ x in (0 : ℝ)..L, (conj (ξ x) * v x + conj (deriv ξ x) * deriv v x) := by
    rw [pair1_lift_eq hv]
    have : ∀ x, conj (lvec ξ x) * v x =
        conj (ξ x) * v x - conj (deriv (deriv ξ) x) * v x := by
      intro x; simp only [lvec, map_sub]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_sub (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c3.intervalIntegrable _ _), iB]
    ring
  have cs : Continuous fun x => conj (ξ x) * v x + conj (deriv ξ x) * deriv v x := c1.add c3
  rw [e, re_intervalIntegral (cs.intervalIntegrable _ _)]
  unfold E2dot
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Complex.add_re]
  have : (conj (deriv v x) * deriv ξ x).re = (conj (deriv ξ x) * deriv v x).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  have h' : (conj (v x) * ξ x).re = (conj (ξ x) * v x).re := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring
  rw [this, h']; ring

theorem V4dot_rel {v ξ : ℝ → ℂ} (hv : SmoothPeriodic L v) (hξ : SmoothPeriodic L ξ) :
    4 * (pair1 (Drv v ξ) (lift hv)).re = 3 * V4dot L v ξ := by
  have cD : Continuous fun x => conj (Drv v ξ x) * v x := by
    unfold Drv
    have c1 := hv.smooth.continuous
    have c2 := hξ.smooth.continuous
    fun_prop
  rw [pair1_lift_eq hv, re_intervalIntegral (cD.intervalIntegrable _ _)]
  unfold V4dot
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Drv, map_add, map_mul, Complex.conj_ofReal, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.add_im,
    Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

end TData

section Struct

variable [Fact (0 < L)]

theorem deriv_cmul_fun {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (c : ℂ) :
    deriv (fun x => c * v x) = fun x => c * deriv v x :=
  funext fun x => ((hasDerivAt_of_smooth hv x).const_mul c).deriv

theorem deriv_comb_fun {g₁ g₂ : ℝ → ℂ} (h₁ : SmoothPeriodic L g₁) (h₂ : SmoothPeriodic L g₂)
    (c₁ c₂ : ℂ) :
    deriv (fun x => c₁ * g₁ x + c₂ * g₂ x) = fun x => c₁ * deriv g₁ x + c₂ * deriv g₂ x :=
  funext fun x =>
    (((hasDerivAt_of_smooth h₁ x).const_mul c₁).add ((hasDerivAt_of_smooth h₂ x).const_mul c₂)).deriv

theorem lvec_cmul {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (c : ℂ) :
    lvec (fun x => c * v x) = fun x => c * lvec v x := by
  funext x
  simp only [lvec]
  rw [deriv_cmul_fun hv c, deriv_cmul_fun (sp_deriv hv) c]
  ring

theorem re_conj_mul_mul (α c v : ℂ) :
    (conj (α * v) * (c * v)).re = (conj α * c).re * ‖v‖ ^ 2 := by
  have : conj (α * v) * (c * v) = (conj α * c) * ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    have h := Complex.conj_mul' v
    rw [map_mul]
    calc conj α * conj v * (c * v) = conj α * c * (conj v * v) := by ring
      _ = _ := by rw [h]; push_cast; ring
  rw [this, Complex.re_mul_ofReal]

theorem k1_cmul (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (α c : ℂ) :
    k1 κ (fun x => α * v x) (fun x => c * v x) = fun x =>
      c * lvec v x + (((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * c +
        ((4 * κ * (conj α * c).re : ℝ) : ℂ) * α) * rvec v x := by
  funext x
  simp only [k1, lvec_cmul hv, re_conj_mul_mul, rvec, norm_mul, mul_pow]
  push_cast
  ring

theorem k1_cmul_xi (κ : ℝ) {v ξ : ℝ → ℂ} (hv : SmoothPeriodic L v) (hξ : SmoothPeriodic L ξ)
    (α : ℂ) :
    k1 κ (fun x => α * v x) (fun x => α * ξ x) = fun x =>
      α * (lvec ξ x + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * Drv v ξ x) := by
  funext x
  have hre : (conj (α * v x) * (α * ξ x)).re = ‖α‖ ^ 2 * (conj (v x) * ξ x).re := by
    have : conj (α * v x) * (α * ξ x) = ((‖α‖ ^ 2 : ℝ) : ℂ) * (conj (v x) * ξ x) := by
      have h := Complex.conj_mul' α
      rw [map_mul]
      calc conj α * conj (v x) * (α * ξ x) = (conj α * α) * (conj (v x) * ξ x) := by ring
        _ = _ := by rw [h]; push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  simp only [k1, lvec_cmul hξ, hre, Drv, norm_mul, mul_pow]
  push_cast
  ring

theorem integrable_cub {u u' : AddCircle L → ℂ} (hu : H04 L 1 u)
    (hu' : MemLp u' 2 (volume : Measure (AddCircle L))) :
    Integrable (fun y => ((‖u y‖ ^ 2 : ℝ) : ℂ) * u' y) (volume : Measure (AddCircle L)) :=
  have h : MemLp (fun y => ((‖u y‖ ^ 2 : ℝ) : ℂ)) 2 (volume : Measure (AddCircle L)) :=
    (memLp_normsq_real hu).ofReal
  h.integrable_mul hu'

theorem intervalIntegrable_pairC {g : ℝ → ℂ} (hg : Continuous g) {u u' : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hu' : MemLp u' 2 (volume : Measure (AddCircle L))) :
    IntervalIntegrable (fun x : ℝ => conj (g x) *
      (((‖u (x : AddCircle L)‖ ^ 2 : ℝ) : ℂ) * u' (x : AddCircle L))) volume 0 L :=
  (intervalIntegrable_coe (integrable_cub hu hu')).continuousOn_mul
    (Complex.continuous_conj.comp hg).continuousOn

theorem Xpair_comb (κ : ℝ) {g₁ g₂ : ℝ → ℂ} (h₁ : SmoothPeriodic L g₁) (h₂ : SmoothPeriodic L g₂)
    {u u' : AddCircle L → ℂ} (hu : H04 L 1 u) (hu' : MemLp u' 2 (volume : Measure (AddCircle L)))
    (c₁ c₂ : ℂ) :
    Xpair κ (fun x => c₁ * g₁ x + c₂ * g₂ x) u u' =
      conj c₁ * Xpair κ g₁ u u' + conj c₂ * Xpair κ g₂ u u' := by
  have d1 := deriv_comb_fun h₁ h₂ c₁ c₂
  have d2 := deriv_comb_fun (sp_deriv h₁) (sp_deriv h₂) c₁ c₂
  have d3 := deriv_comb_fun (sp_deriv (sp_deriv h₁)) (sp_deriv (sp_deriv h₂)) c₁ c₂
  have hp : pairC (fun x => c₁ * g₁ x + c₂ * g₂ x) u u' =
      conj c₁ * pairC g₁ u u' + conj c₂ * pairC g₂ u u' := by
    unfold pairC
    have e : ∀ x : ℝ, conj (c₁ * g₁ x + c₂ * g₂ x) *
        (((‖u (x : AddCircle L)‖ ^ 2 : ℝ) : ℂ) * u' (x : AddCircle L)) =
        conj c₁ * (conj (g₁ x) * (((‖u (x : AddCircle L)‖ ^ 2 : ℝ) : ℂ) * u' (x : AddCircle L))) +
        conj c₂ * (conj (g₂ x) * (((‖u (x : AddCircle L)‖ ^ 2 : ℝ) : ℂ) * u' (x : AddCircle L))) := by
      intro x; simp only [map_add, map_mul]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add
      ((intervalIntegrable_pairC h₁.smooth.continuous hu hu').const_mul _)
      ((intervalIntegrable_pairC h₂.smooth.continuous hu hu').const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  unfold Xpair
  rw [d1, d2, d3, hp,
    pair1_comb (sp_deriv (sp_deriv (sp_deriv h₁))).smooth.continuous
      (sp_deriv (sp_deriv (sp_deriv h₂))).smooth.continuous hu.1 c₁ c₂]
  ring

theorem gE_cmul (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (α : ℂ) :
    gE κ (fun x => α * v x) = fun x =>
      α * lvec v x + (α * ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ)) * rvec v x := by
  funext x
  simp only [gE, lvec_cmul hv, rvec, norm_mul, mul_pow]
  push_cast
  ring

theorem Xpair_gE (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (α : ℂ) {u u' : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hu' : MemLp u' 2 (volume : Measure (AddCircle L))) :
    Xpair κ (gE κ (fun x => α * v x)) u u' =
      conj α * (Xpair κ (lvec v) u u' + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * Xpair κ (rvec v) u u') := by
  rw [gE_cmul κ hv α, Xpair_comb κ (sp_lvec hv) (sp_rvec hv) hu hu']
  simp only [map_mul, Complex.conj_ofReal]
  ring

end Struct

section MasterAlg

theorem master_alg (κ Ed Vd : ℝ) (α α' lam th lamx thx Pl PD aX bX : ℂ)
    (hE : 2 * Pl.re = Ed) (hV : 4 * PD.re = 3 * Vd) :
    2 * (conj α' * lam).re + 8 * κ * (conj α * α').re * (conj α * th).re
        + 4 * κ * ‖α‖ ^ 2 * (conj α' * th).re
        + 2 * (conj α * ((lamx + α * Pl + aX) + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) *
            (thx + α * PD + bX))).re
        - ‖α‖ ^ 2 * Ed - 3 * κ * ‖α‖ ^ 4 * Vd =
      2 * (conj α * (aX + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * bX)).re
        + 2 * (conj α' * lam + (((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * conj α' +
            ((4 * κ * (conj α * α').re : ℝ) : ℂ) * conj α) * th).re
        + 2 * (conj α * (lamx + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * thx)).re := by
  have h2 : ‖α‖ ^ 2 = α.re * α.re + α.im * α.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have h4 : ‖α‖ ^ 4 = (α.re * α.re + α.im * α.im) ^ 2 := by rw [← h2]; ring
  rw [h4, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (α.re * α.re + α.im * α.im) * hE + (κ * (α.re * α.re + α.im * α.im) ^ 2) * hV

end MasterAlg

section Master

variable [Fact (0 < L)]

/-- The time part of the transport derivative `(∂_t + d_u[X(u)]) S_{v(t)}(u)`: the derivative of
`S_v(u)` (in the polynomial form `eq:A1-S`) with respect to the target `v` along `v_t = X(v)`
(the printed assignment "`v_t = X(v)`"). -/
def Tt (κ : ℝ) (v : ℝ → ℂ) (u : AddCircle L → ℂ) : ℝ :=
  dSigma κ (E2 L v) (V4 L v) (pair1 v u) (pair1 (lvec v) u) (pair1 (rvec v) u)
    (pair1 (Xf κ v) u) (pair1 (lvec (Xf κ v)) u) (pair1 (Drv v (Xf κ v)) u)
    (E2dot L v (Xf κ v)) (V4dot L v (Xf κ v))

/-- The `u`-part: the directional derivative of the polynomial `S_v` along `X(u)`, the third
derivative moved onto the smooth contractions of `J` (`Xpair`), `u'` the weak derivative. -/
def Tu (κ : ℝ) (v : ℝ → ℂ) (u u' : AddCircle L → ℂ) : ℝ :=
  dSigma κ (E2 L v) (V4 L v) (pair1 v u) (pair1 (lvec v) u) (pair1 (rvec v) u)
    (Xpair κ v u u') (Xpair κ (lvec v) u u') (Xpair κ (rvec v) u u') 0 0

/-- `(∂_t + d_u[X(u)]) S_{v}(u)`. -/
def Ttot (κ : ℝ) (v : ℝ → ℂ) (u u' : AddCircle L → ℂ) : ℝ := Tt κ v u + Tu κ v u u'

theorem cont_Drv {v ξ : ℝ → ℂ} (hv : Continuous v) (hξ : Continuous ξ) : Continuous (Drv v ξ) := by
  unfold Drv
  fun_prop

theorem Ttot_formula (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u u' : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hu' : MemLp u' 2 (volume : Measure (AddCircle L))) {α : ℂ}
    (hα : pair1 v u = α) :
    Ttot κ v u u' =
      2 * (Xpair κ (gE κ (fun x => α * v x)) u u').re
      + 2 * (pair1 (k1 κ (fun x => α * v x)
          (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x))
          (fun y => u y - α * lift hv y)).re
      + 2 * (pair1 (k1 κ (fun x => α * v x) (fun x => α * Xf κ v x))
          (fun y => u y - α * lift hv y)).re := by
  have hξ := sp_Xf κ hv
  have hvL : MemLp (lift hv) 2 (volume : Measure (AddCircle L)) :=
    memLp_of_continuous (continuous_lift hv)
  have hwL : MemLp (fun y => u y - α * lift hv y) 2 (volume : Measure (AddCircle L)) :=
    hu.1.sub (hvL.const_mul α)
  have hdec : ∀ g : ℝ → ℂ, Continuous g →
      pair1 g u = pair1 g (fun y => u y - α * lift hv y) + α * pair1 g (lift hv) := by
    intro g hg
    have e : u = fun y => (u y - α * lift hv y) + α * lift hv y := by funext y; ring
    conv_lhs => rw [e]
    rw [pair1_add hg hwL (hvL.const_mul α), pair1_smul]
  have ha : pair1 (lvec v) u = α * ((E2 L v : ℝ) : ℂ) +
      pair1 (lvec v) (fun y => u y - α * lift hv y) := by
    rw [hdec _ (sp_lvec hv).smooth.continuous, pair1_lvec_self hv]; ring
  have hb : pair1 (rvec v) u = α * ((V4 L v : ℝ) : ℂ) +
      pair1 (rvec v) (fun y => u y - α * lift hv y) := by
    rw [hdec _ (sp_rvec hv).smooth.continuous, pair1_rvec_self hv]; ring
  have hat := hdec (lvec (Xf κ v)) (sp_lvec hξ).smooth.continuous
  have hbt := hdec (Drv v (Xf κ v)) (cont_Drv hv.smooth.continuous hξ.smooth.continuous)
  unfold Ttot Tt Tu
  rw [dSigma_add, hα, ha, hb, dSigma_star, hat, hbt, Xpair_gE κ hv α hu hu']
  have hA : pair1 (k1 κ (fun x => α * v x)
      (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x)) (fun y => u y - α * lift hv y) =
      conj (pair1 (Xf κ v) u + Xpair κ v u u') * pair1 (lvec v) (fun y => u y - α * lift hv y) +
        (((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * conj (pair1 (Xf κ v) u + Xpair κ v u u') +
          ((4 * κ * (conj α * (pair1 (Xf κ v) u + Xpair κ v u u')).re : ℝ) : ℂ) * conj α) *
        pair1 (rvec v) (fun y => u y - α * lift hv y) := by
    rw [k1_cmul κ hv α, pair1_comb (sp_lvec hv).smooth.continuous (sp_rvec hv).smooth.continuous hwL]
    simp only [map_add, map_mul, Complex.conj_ofReal]
  have hB : pair1 (k1 κ (fun x => α * v x) (fun x => α * Xf κ v x))
      (fun y => u y - α * lift hv y) =
      conj α * (pair1 (lvec (Xf κ v)) (fun y => u y - α * lift hv y) +
        ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * pair1 (Drv v (Xf κ v)) (fun y => u y - α * lift hv y)) := by
    rw [k1_cmul_xi κ hv hξ α]
    have e : (fun x => α * (lvec (Xf κ v) x + ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ) * Drv v (Xf κ v) x)) =
        fun x => α * lvec (Xf κ v) x + (α * ((2 * κ * ‖α‖ ^ 2 : ℝ) : ℂ)) * Drv v (Xf κ v) x := by
      funext x; ring
    rw [e, pair1_comb (sp_lvec hξ).smooth.continuous
      (cont_Drv hv.smooth.continuous hξ.smooth.continuous) hwL]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [hA, hB]
  have hE := E2dot_rel hv hξ
  have hV := V4dot_rel hv hξ
  have := master_alg κ (E2dot L v (Xf κ v)) (V4dot L v (Xf κ v)) α
    (pair1 (Xf κ v) u + Xpair κ v u u')
    (pair1 (lvec v) (fun y => u y - α * lift hv y)) (pair1 (rvec v) (fun y => u y - α * lift hv y))
    (pair1 (lvec (Xf κ v)) (fun y => u y - α * lift hv y))
    (pair1 (Drv v (Xf κ v)) (fun y => u y - α * lift hv y))
    (pair1 (lvec (Xf κ v)) (lift hv)) (pair1 (Drv v (Xf κ v)) (lift hv))
    (Xpair κ (lvec v) u u') (Xpair κ (rvec v) u u') hE hV
  simp only [add_zero]
  exact this

end Master

section Ident

variable [Fact (0 < L)]

theorem sp_cmul {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (c : ℂ) :
    SmoothPeriodic L (fun x => c * v x) :=
  ⟨contDiff_const.mul hv.smooth, fun x => by simp only [hv.periodic x]⟩

theorem Xpair_decomp (κ : ℝ) {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q)
    {w w' : AddCircle L → ℂ} (hw : H04 L 1 w) (hw' : MemLp w' 2 (volume : Measure (AddCircle L))) :
    Xpair κ g (fun y => lift hq y + w y) (fun y => lift (sp_deriv hq) y + w' y) =
      (∫ x in (0 : ℝ)..L, conj (g x) * Xf κ q x) +
        (-pair1 (deriv (deriv (deriv g))) w -
          6 * (κ : ℂ) * LinC (lift hg) (lift hq) (lift (sp_deriv hq)) w w') +
        (-(6 * (κ : ℂ)) * RemC (lift hg) (lift hq) (lift (sp_deriv hq)) w w') := by
  have hqL : MemLp (lift hq) 2 (volume : Measure (AddCircle L)) :=
    memLp_of_continuous (continuous_lift hq)
  have e1 := Xpair_smooth κ hg hq
  have e2 := pairC_decomp hg hq hw hw'
  unfold Xpair at e1 ⊢
  rw [pair1_add (sp_deriv (sp_deriv (sp_deriv hg))).smooth.continuous hqL hw.1, e2, ← e1]
  ring

end Ident

section Ident2

variable [Fact (0 < L)]

theorem pair1_sub_fun {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B) {u : AddCircle L → ℂ}
    (hu : MemLp u 2 (volume : Measure (AddCircle L))) :
    pair1 (fun x => A x - B x) u = pair1 A u - pair1 B u := by
  unfold pair1
  simp_rw [map_sub, sub_mul]
  exact intervalIntegral.integral_sub (intervalIntegrable_pair hA hu) (intervalIntegrable_pair hB hu)

/-- **The relative-energy identity** (`eq:A1-relative-identity`, in explicit form): with
`q = αv`, `w = u − q`, the transport derivative equals `2Re⟨∇E(q), R⟩ + d²E(q)[q_t − X(q), w]`
(`R` the nonlinear remainder, `q_t = α̇ v + α v_t`). -/
theorem Ttot_identity (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u u' : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hd : IsWD u u') {α : ℂ} (hα : pair1 v u = α) {q : ℝ → ℂ}
    (hq : SmoothPeriodic L q) (hqe : q = fun x => α * v x) :
    Ttot κ v u u' =
      2 * (-(6 * (κ : ℂ)) * RemC (lift (sp_gE κ hq)) (lift hq) (lift (sp_deriv hq))
          (fun y => u y - α * lift hv y) (fun y => u' y - α * lift (sp_deriv hv) y)).re
      + 2 * (pair1 (k1 κ q (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x))
          (fun y => u y - α * lift hv y)).re
      + 2 * (pair1 (fun x => k1 κ q (fun x => α * Xf κ v x) x - k1 κ q (Xf κ q) x)
          (fun y => u y - α * lift hv y)).re := by
  subst hqe
  have hvH := h04_lift hv
  have hwH : H04 L 1 (fun y => u y - α * lift hv y) := (h04_sub hu (h04_cmul hvH α).1).1
  have hw'L : MemLp (fun y => u' y - α * lift (sp_deriv hv) y) 2 (volume : Measure (AddCircle L)) :=
    hd.2.1.sub ((memLp_of_continuous (continuous_lift (sp_deriv hv))).const_mul α)
  have hdw : IsWD (fun y => u y - α * lift hv y) (fun y => u' y - α * lift (sp_deriv hv) y) :=
    hd.sub (IsWD.const_mul (IsWD.smooth hv) α)
  have hlq : lift hq = fun y => α * lift hv y :=
    lift_eq_fun hq _ (fun x => by simp only [lift_coe])
  have hlq' : lift (sp_deriv hq) = fun y => α * lift (sp_deriv hv) y :=
    lift_eq_fun (sp_deriv hq) _ (fun x => by
      simp only [lift_coe]; rw [deriv_cmul_fun hv α])
  have eu : u = fun y => lift hq y + (u y - α * lift hv y) := by
    funext y; rw [hlq]; ring
  have eu' : u' = fun y => lift (sp_deriv hq) y + (u' y - α * lift (sp_deriv hv) y) := by
    funext y; rw [hlq']; ring
  have hT := Ttot_formula κ hv hu hd.2.1 hα
  have hX := Xpair_decomp κ (sp_gE κ hq) hq hwH hw'L
  rw [← eu, ← eu'] at hX
  have c0 := cons_E hq κ
  have hLam := LamId κ (sp_gE κ hq) hq hwH hdw
  have hC1 := C1_identity κ hq hwH.1
  have hkA := cont_k1 κ hq (sp_cmul (sp_Xf κ hv) α)
  have hkB := cont_k1 κ hq (sp_Xf κ hq)
  rw [pair1_sub_fun hkA hkB hwH.1, Complex.sub_re]
  rw [hT, hX, Complex.add_re, Complex.add_re, c0, hLam]
  linarith

end Ident2

section Bounds

variable [Fact (0 < L)]

theorem Aw_sq_le {w : AddCircle L → ℂ} (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    (∫ y, ‖w y‖ ∂(volume : Measure (AddCircle L))) ^ 2 ≤
      L * ∫ y, ‖w y‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
  have hL : 0 < L := Fact.out
  have i1 := int_norm hw
  have i2 := int_norm_sq hw
  set A := ∫ y, ‖w y‖ ∂(volume : Measure (AddCircle L)) with hA
  set I := ∫ y, ‖w y‖ ^ 2 ∂(volume : Measure (AddCircle L)) with hI
  set c := A / L with hc
  have h0 : 0 ≤ ∫ y, (‖w y‖ - c) ^ 2 ∂(volume : Measure (AddCircle L)) :=
    integral_nonneg (fun y => sq_nonneg _)
  have hvol : (volume : Measure (AddCircle L)).real Set.univ = L := by
    simp [Measure.real, AddCircle.measure_univ, hL.le]
  have h1 : ∫ y, (‖w y‖ - c) ^ 2 ∂(volume : Measure (AddCircle L)) = I - 2 * c * A + c ^ 2 * L := by
    have e : ∀ y, (‖w y‖ - c) ^ 2 = (‖w y‖ ^ 2 - 2 * c * ‖w y‖) + c ^ 2 := fun y => by ring
    simp_rw [e]
    have i3 : Integrable (fun y => ‖w y‖ ^ 2 - 2 * c * ‖w y‖) (volume : Measure (AddCircle L)) :=
      i2.sub (i1.const_mul _)
    rw [integral_add i3 (integrable_const _), integral_sub i2 (i1.const_mul _),
      integral_const_mul, integral_const, hvol]
    simp
    ring
  rw [h1] at h0
  have : c ^ 2 * L = A ^ 2 / L := by rw [hc]; field_simp
  have h2 : 2 * c * A = 2 * (A ^ 2 / L) := by rw [hc]; field_simp
  rw [this, h2] at h0
  have h3 : A ^ 2 / L ≤ I := by linarith
  rw [div_le_iff₀ hL] at h3
  linarith

theorem norm_pair1_le {g : ℝ → ℂ} (hg : SmoothPeriodic L g) {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B)
    {w : AddCircle L → ℂ} (hw : MemLp w 2 (volume : Measure (AddCircle L))) :
    ‖pair1 g w‖ ≤ B * ∫ y, ‖w y‖ ∂(volume : Measure (AddCircle L)) := by
  rw [pair1_circ hg]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    ((int_norm hw).const_mul B) (Filter.Eventually.of_forall fun y => ?_)
  simp only [norm_mul, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_lift_le hg hB y) (norm_nonneg _)

theorem amgm_cubic {a b κ : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * (a ^ 2 * b) ≤ κ / 3 * a ^ 4 + 3 / κ * b ^ 2 := by
  have h : 0 ≤ (κ / 3 * a ^ 2 - b) ^ 2 * (3 / κ) := by positivity
  have e : (κ / 3 * a ^ 2 - b) ^ 2 * (3 / κ) = κ / 3 * a ^ 4 + 3 / κ * b ^ 2 - 2 * (a ^ 2 * b) := by
    field_simp
    ring
  linarith

theorem pt_Rem_amgm {a b B M M1 κ : ℝ} (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hM1 : 0 ≤ M1) :
    B * (2 * M * a * b + M1 * a ^ 2 + a ^ 2 * b) ≤
      B * (M + M1 + 3 / (2 * κ) + 1 / 2) * (b ^ 2 + a ^ 2 + κ / 3 * a ^ 4) := by
  have h1 := amgm_cubic hκ ha hb
  have h2 : 0 ≤ 3 / (2 * κ) := by positivity
  have h3 : 3 / κ = 2 * (3 / (2 * κ)) := by field_simp
  have e : 2 * M * a * b ≤ M * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  have hK : B * (2 * M * a * b + M1 * a ^ 2 + a ^ 2 * b) ≤
      B * (M * (a ^ 2 + b ^ 2) + M1 * a ^ 2 + (κ / 3 * a ^ 4 / 2 + 3 / (2 * κ) * b ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hB
    rw [h3] at h1
    nlinarith
  refine hK.trans ?_
  have h4 : 0 ≤ κ / 3 * a ^ 4 := by positivity
  have h5 : M * (a ^ 2 + b ^ 2) + M1 * a ^ 2 + (κ / 3 * a ^ 4 / 2 + 3 / (2 * κ) * b ^ 2) ≤
      (M + M1 + 3 / (2 * κ) + 1 / 2) * (b ^ 2 + a ^ 2 + κ / 3 * a ^ 4) := by
    have : 0 ≤ M * b ^ 2 := by positivity
    nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hM (sq_nonneg a), mul_nonneg hM (sq_nonneg b),
      mul_nonneg hM1 (sq_nonneg a), mul_nonneg h2 (sq_nonneg b), mul_nonneg h2 (sq_nonneg a),
      mul_nonneg h2 h4, mul_nonneg hM h4, mul_nonneg hM1 h4]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h5 hB

end Bounds

section Bounds2

variable [Fact (0 < L)]

theorem norm_RemC_le {G Q Q' w w' : AddCircle L → ℂ} (hG : Continuous G) (hQ : Continuous Q)
    (hQ' : Continuous Q') (hw : H04 L 1 w) (hw' : MemLp w' 2 (volume : Measure (AddCircle L)))
    {κ B M M1 : ℝ} (hκ : 0 < κ) (hB : ∀ y, ‖G y‖ ≤ B) (hM : ∀ y, ‖Q y‖ ≤ M)
    (hM1 : ∀ y, ‖Q' y‖ ≤ M1) :
    ‖RemC G Q Q' w w'‖ ≤ B * (M + M1 + 3 / (2 * κ) + 1 / 2) *
      ((∫ y, ‖w' y‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
        (∫ y, ‖w y‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
        κ / 3 * ∫ y, ‖w y‖ ^ 4 ∂(volume : Measure (AddCircle L))) := by
  have iw2 := int_norm_sq hw.1
  have iw2' := int_norm_sq hw'
  have iw4 := quartic_integrable hw
  have iS : Integrable (fun y => B * (M + M1 + 3 / (2 * κ) + 1 / 2) *
      (‖w' y‖ ^ 2 + ‖w y‖ ^ 2 + κ / 3 * ‖w y‖ ^ 4)) (volume : Measure (AddCircle L)) :=
    ((iw2'.add iw2).add (iw4.const_mul _)).const_mul _
  unfold RemC
  refine (norm_integral_le_integral_norm _).trans ?_
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) iS
    (Filter.Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · have h1 := pt_fRem (w := w y) (w1 := w' y) (hB y) (hM y) (hM1 y)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y)
    have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 y)
    refine h1.trans ?_
    exact pt_Rem_amgm hκ (norm_nonneg _) (norm_nonneg _) hB0 hM0 hM10
  · have iA : Integrable (fun y => ‖w' y‖ ^ 2 + ‖w y‖ ^ 2) (volume : Measure (AddCircle L)) :=
      iw2'.add iw2
    rw [integral_const_mul, integral_add iA (iw4.const_mul _), integral_add iw2' iw2,
      integral_const_mul]

theorem norm_k1_le (κ : ℝ) (hκ : 0 ≤ κ) (q h : ℝ → ℂ) (x : ℝ) :
    ‖k1 κ q h x‖ ≤ ‖h x‖ + ‖deriv (deriv h) x‖ + 6 * κ * ‖q x‖ ^ 2 * ‖h x‖ := by
  have hre : |(conj (q x) * h x).re| ≤ ‖q x‖ * ‖h x‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
  have h1 : ‖lvec h x‖ ≤ ‖h x‖ + ‖deriv (deriv h) x‖ := by
    simp only [lvec]; exact norm_sub_le _ _
  have h2 : ‖2 * (κ : ℂ) * ((‖q x‖ ^ 2 : ℝ) : ℂ) * h x‖ ≤ 2 * κ * ‖q x‖ ^ 2 * ‖h x‖ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hκ, Real.norm_of_nonneg (by positivity)]
    simp
  have h3 : ‖4 * (κ : ℂ) * (((conj (q x) * h x).re : ℝ) : ℂ) * q x‖ ≤
      4 * κ * (‖q x‖ * ‖h x‖) * ‖q x‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ, Complex.norm_ofNat]
    have := mul_le_mul_of_nonneg_left hre (by positivity : 0 ≤ 4 * κ)
    exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  unfold k1
  calc _ ≤ ‖lvec h x + 2 * (κ : ℂ) * ((‖q x‖ ^ 2 : ℝ) : ℂ) * h x‖ +
        ‖4 * (κ : ℂ) * (((conj (q x) * h x).re : ℝ) : ℂ) * q x‖ := norm_add_le _ _
    _ ≤ (‖lvec h x‖ + ‖2 * (κ : ℂ) * ((‖q x‖ ^ 2 : ℝ) : ℂ) * h x‖) +
        ‖4 * (κ : ℂ) * (((conj (q x) * h x).re : ℝ) : ℂ) * q x‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ _ := by nlinarith [norm_nonneg (h x), norm_nonneg (q x), norm_nonneg (deriv (deriv h) x)]

end Bounds2

section Bounds3

variable [Fact (0 < L)]

/-- Uniform bounds for the jets `v, v', v'', v'''`. -/
def JB (v : ℝ → ℂ) (M : ℝ) : Prop :=
  ∀ x, ‖v x‖ ≤ M ∧ ‖deriv v x‖ ≤ M ∧ ‖deriv (deriv v) x‖ ≤ M ∧ ‖deriv (deriv (deriv v)) x‖ ≤ M

theorem JB.nonneg {v : ℝ → ℂ} {M : ℝ} (h : JB v M) : 0 ≤ M := (norm_nonneg _).trans (h 0).1

theorem norm_M0f_le {v : ℝ → ℂ} {M : ℝ} (hJ : JB v M) (x : ℝ) : ‖M0f v x‖ ≤ M ^ 2 := by
  unfold M0f
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hJ x).1 2

theorem norm_M1f_le {v : ℝ → ℂ} {M : ℝ} (hJ : JB v M) (x : ℝ) : ‖M1f v x‖ ≤ 2 * M ^ 2 := by
  have h0 := (hJ x).1
  have h1 := (hJ x).2.1
  unfold M1f
  simp only [jet_zero, jet_one]
  calc _ ≤ ‖deriv v x * conj (v x)‖ + ‖v x * conj (deriv v x)‖ := norm_add_le _ _
    _ ≤ M * M + M * M := by
      simp only [norm_mul, RCLike.norm_conj]
      exact add_le_add (mul_le_mul h1 h0 (norm_nonneg _) (hJ.nonneg)) (mul_le_mul h0 h1 (norm_nonneg _) (hJ.nonneg))
    _ = 2 * M ^ 2 := by ring

theorem norm_M2f_le {v : ℝ → ℂ} {M : ℝ} (hJ : JB v M) (x : ℝ) : ‖M2f v x‖ ≤ 4 * M ^ 2 := by
  have h0 := (hJ x).1
  have h1 := (hJ x).2.1
  have h2 := (hJ x).2.2.1
  have hM := hJ.nonneg
  unfold M2f
  simp only [jet_zero, jet_one, jet_two]
  calc _ ≤ ‖deriv (deriv v) x * conj (v x)‖ + ‖2 * (deriv v x * conj (deriv v x))‖ +
        ‖v x * conj (deriv (deriv v) x)‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ M * M + 2 * (M * M) + M * M := by
      simp only [norm_mul, RCLike.norm_conj]
      have : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [this]
      exact add_le_add (add_le_add (mul_le_mul h2 h0 (norm_nonneg _) hM)
        (mul_le_mul_of_nonneg_left (mul_le_mul h1 h1 (norm_nonneg _) hM) (by norm_num)))
        (mul_le_mul h0 h2 (norm_nonneg _) hM)
    _ = 4 * M ^ 2 := by ring

theorem norm_Nf_le {v : ℝ → ℂ} {M κ : ℝ} (hJ : JB v M) (hκ : 0 ≤ κ) (x : ℝ) :
    ‖Nf κ v x‖ ≤ 6 * κ * M ^ 3 := by
  have h0 := norm_M0f_le hJ x
  have h1 := (hJ x).2.1
  have hM := hJ.nonneg
  unfold Nf
  have e : ‖(-6 : ℂ) * (κ : ℂ) * ((‖v x‖ ^ 2 : ℝ) : ℂ) * deriv v x‖ =
      6 * κ * ‖M0f v x‖ * ‖deriv v x‖ := by
    simp only [norm_mul, M0f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ, norm_neg,
      Complex.norm_ofNat]
  rw [e]
  have : 0 ≤ 6 * κ := by positivity
  calc 6 * κ * ‖M0f v x‖ * ‖deriv v x‖ ≤ 6 * κ * M ^ 2 * M := by
        gcongr
    _ = 6 * κ * M ^ 3 := by ring

theorem norm_Xf_le {v : ℝ → ℂ} {M κ : ℝ} (hJ : JB v M) (hκ : 0 ≤ κ) (x : ℝ) :
    ‖Xf κ v x‖ ≤ M + 6 * κ * M ^ 3 := by
  have hN := norm_Nf_le hJ hκ x
  have h3 := (hJ x).2.2.2
  have e : Xf κ v x = deriv (deriv (deriv v)) x + Nf κ v x := by
    simp only [Xf, Nf]; ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add h3 hN)

theorem sp_Nf (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) : SmoothPeriodic L (Nf κ v) := by
  have e : Nf κ v = fun x => (-6 * (κ : ℂ)) * (((‖v x‖ ^ 2 : ℝ) : ℂ) * deriv v x) := by
    funext x; simp only [Nf]; ring
  rw [e]
  exact sp_cmul (sp_mul (sp_normsq hv) (sp_deriv hv)) _

def N1f (κ : ℝ) (v : ℝ → ℂ) (y : ℝ) : ℂ :=
  (-6 * (κ : ℂ)) * (M1f v y * jet v 1 y + M0f v y * jet v 2 y)
def N2f (κ : ℝ) (v : ℝ → ℂ) (y : ℝ) : ℂ :=
  (-6 * (κ : ℂ)) * (M2f v y * jet v 1 y + 2 * (M1f v y * jet v 2 y) + M0f v y * jet v 3 y)

theorem hasDerivAt_N0 (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (x : ℝ) :
    HasDerivAt (Nf κ v) (N1f κ v x) x := by
  have h := (((hasDerivAt_M0 hv x).mul (hasDerivAt_jet hv 1 x)).const_mul (-6 * (κ : ℂ)))
  have e : Nf κ v = fun y => (-6 * (κ : ℂ)) * (M0f v y * jet v 1 y) := by
    funext y; simp only [Nf, M0f, jet_one]; ring
  rw [e]
  exact h.congr_deriv (by simp only [N1f])

theorem hasDerivAt_N1 (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (x : ℝ) :
    HasDerivAt (N1f κ v) (N2f κ v x) x := by
  have h := ((((hasDerivAt_M1 hv x).mul (hasDerivAt_jet hv 1 x)).add
    ((hasDerivAt_M0 hv x).mul (hasDerivAt_jet hv 2 x))).const_mul (-6 * (κ : ℂ)))
  exact h.congr_deriv (by simp only [N2f, M2f]; ring)

theorem deriv2_Nf (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) :
    deriv (deriv (Nf κ v)) = N2f κ v := by
  have h1 : deriv (Nf κ v) = N1f κ v := funext fun x => (hasDerivAt_N0 κ hv x).deriv
  rw [h1]
  exact funext fun x => (hasDerivAt_N1 κ hv x).deriv

theorem norm_N2_le {v : ℝ → ℂ} {M κ : ℝ} (hv : SmoothPeriodic L v) (hJ : JB v M) (hκ : 0 ≤ κ)
    (x : ℝ) : ‖deriv (deriv (Nf κ v)) x‖ ≤ 54 * κ * M ^ 3 := by
  rw [deriv2_Nf κ hv]
  have h0 := norm_M0f_le hJ x
  have h1 := norm_M1f_le hJ x
  have h2 := norm_M2f_le hJ x
  have j1 := (hJ x).2.1
  have j2 := (hJ x).2.2.1
  have j3 := (hJ x).2.2.2
  have hM := hJ.nonneg
  unfold N2f
  simp only [jet_one, jet_two, jet_three]
  have e : ‖(-6 * (κ : ℂ))‖ = 6 * κ := by
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hκ]
  rw [norm_mul, e]
  have hb : ‖M2f v x * deriv v x + 2 * (M1f v x * deriv (deriv v) x) +
      M0f v x * deriv (deriv (deriv v)) x‖ ≤ 9 * M ^ 3 := by
    calc _ ≤ ‖M2f v x * deriv v x‖ + ‖2 * (M1f v x * deriv (deriv v) x)‖ +
          ‖M0f v x * deriv (deriv (deriv v)) x‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 4 * M ^ 2 * M + 2 * (2 * M ^ 2 * M) + M ^ 2 * M := by
        simp only [norm_mul]
        have : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [this]
        exact add_le_add (add_le_add (mul_le_mul h2 j1 (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left (mul_le_mul h1 j2 (norm_nonneg _) (by positivity)) (by norm_num)))
          (mul_le_mul h0 j3 (norm_nonneg _) (by positivity))
      _ = 9 * M ^ 3 := by ring
  calc 6 * κ * _ ≤ 6 * κ * (9 * M ^ 3) := by gcongr
    _ = 54 * κ * M ^ 3 := by ring

end Bounds3

section Bounds4

variable [Fact (0 < L)]

theorem JB_cmul {v : ℝ → ℂ} {M : ℝ} (hv : SmoothPeriodic L v) (hJ : JB v M) {α : ℂ}
    (hα : ‖α‖ ≤ 1) : JB (fun x => α * v x) M := by
  intro x
  rw [deriv_cmul_fun hv α, deriv_cmul_fun (sp_deriv hv) α, deriv_cmul_fun (sp_deriv (sp_deriv hv)) α]
  obtain ⟨h0, h1, h2, h3⟩ := hJ x
  have hM := hJ.nonneg
  have key : ∀ z : ℂ, ‖z‖ ≤ M → ‖α * z‖ ≤ M := fun z hz => by
    rw [norm_mul]
    calc ‖α‖ * ‖z‖ ≤ 1 * M := mul_le_mul hα hz (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  exact ⟨key _ h0, key _ h1, key _ h2, key _ h3⟩

theorem norm_gE_le {q : ℝ → ℂ} {M κ : ℝ} (hJ : JB q M) (hκ : 0 ≤ κ) (x : ℝ) :
    ‖gE κ q x‖ ≤ 2 * M + 2 * κ * M ^ 3 := by
  obtain ⟨h0, -, h2, -⟩ := hJ x
  have hM := hJ.nonneg
  unfold gE lvec rvec
  have e1 : ‖q x - deriv (deriv q) x‖ ≤ 2 * M := by
    calc _ ≤ ‖q x‖ + ‖deriv (deriv q) x‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add h0 h2
      _ = 2 * M := by ring
  have e2 : ‖2 * (κ : ℂ) * (((‖q x‖ ^ 2 : ℝ) : ℂ) * q x)‖ ≤ 2 * κ * M ^ 3 := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ, Complex.norm_ofNat,
      abs_of_nonneg (sq_nonneg ‖q x‖)]
    have : ‖q x‖ ^ 2 * ‖q x‖ ≤ M ^ 3 := by
      calc ‖q x‖ ^ 2 * ‖q x‖ ≤ M ^ 2 * M := by
            gcongr
        _ = M ^ 3 := by ring
    nlinarith
  calc _ ≤ ‖q x - deriv (deriv q) x‖ + ‖2 * (κ : ℂ) * (((‖q x‖ ^ 2 : ℝ) : ℂ) * q x)‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add e1 e2

theorem k1_sub (κ : ℝ) (q : ℝ → ℂ) {h₁ h₂ : ℝ → ℂ} (hh₁ : SmoothPeriodic L h₁)
    (hh₂ : SmoothPeriodic L h₂) :
    k1 κ q (fun x => h₁ x - h₂ x) = fun x => k1 κ q h₁ x - k1 κ q h₂ x := by
  have d1 : deriv (fun x => h₁ x - h₂ x) = fun x => deriv h₁ x - deriv h₂ x :=
    funext fun x => ((hasDerivAt_of_smooth hh₁ x).sub (hasDerivAt_of_smooth hh₂ x)).deriv
  have d2 : deriv (fun x => deriv h₁ x - deriv h₂ x) = fun x => deriv (deriv h₁) x - deriv (deriv h₂) x :=
    funext fun x => ((hasDerivAt_of_smooth (sp_deriv hh₁) x).sub
      (hasDerivAt_of_smooth (sp_deriv hh₂) x)).deriv
  funext x
  simp only [k1, lvec, d1, d2, mul_sub, Complex.sub_re]
  push_cast
  ring

theorem Xf_cmul (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (α : ℂ) :
    Xf κ (fun x => α * v x) = fun x =>
      α * deriv (deriv (deriv v)) x + ((‖α‖ ^ 2 : ℝ) : ℂ) * α * Nf κ v x := by
  funext x
  simp only [Xf, Nf]
  rw [deriv_cmul_fun hv α, deriv_cmul_fun (sp_deriv hv) α, deriv_cmul_fun (sp_deriv (sp_deriv hv)) α]
  simp only [norm_mul, mul_pow]
  push_cast
  ring

theorem xi_sub (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (α : ℂ) :
    (fun x => α * Xf κ v x - Xf κ (fun x => α * v x) x) =
      fun x => (α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ))) * Nf κ v x := by
  funext x
  rw [Xf_cmul κ hv α]
  simp only [Xf, Nf]
  ring

theorem sp_Xf_cmul (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (α : ℂ) :
    SmoothPeriodic L (fun x => α * Xf κ v x) := sp_cmul (sp_Xf κ hv) α

theorem norm_k1_cN_le {v : ℝ → ℂ} {M κ : ℝ} {q : ℝ → ℂ} (hv : SmoothPeriodic L v) (hJ : JB v M)
    (hJq : JB q M) (hκ : 0 ≤ κ) (c : ℂ) (x : ℝ) :
    ‖k1 κ q (fun x => c * Nf κ v x) x‖ ≤ ‖c‖ * (60 * κ * M ^ 3 + 36 * κ ^ 2 * M ^ 5) := by
  have h := norm_k1_le κ hκ q (fun x => c * Nf κ v x) x
  rw [deriv_cmul_fun (sp_Nf κ hv) c, deriv_cmul_fun (sp_deriv (sp_Nf κ hv)) c] at h
  have hN := norm_Nf_le hJ hκ x
  have hN2 := norm_N2_le hv hJ hκ x
  have hq := (hJq x).1
  have hM := hJ.nonneg
  have hc := norm_nonneg c
  refine h.trans ?_
  simp only [norm_mul]
  have hq2 : ‖q x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
  have a1 : ‖c‖ * ‖Nf κ v x‖ ≤ ‖c‖ * (6 * κ * M ^ 3) := mul_le_mul_of_nonneg_left hN hc
  have a2 : ‖c‖ * ‖deriv (deriv (Nf κ v)) x‖ ≤ ‖c‖ * (54 * κ * M ^ 3) := mul_le_mul_of_nonneg_left hN2 hc
  have a3 : 6 * κ * ‖q x‖ ^ 2 * (‖c‖ * ‖Nf κ v x‖) ≤ 6 * κ * M ^ 2 * (‖c‖ * (6 * κ * M ^ 3)) := by
    have : 0 ≤ 6 * κ := by positivity
    gcongr
  nlinarith

theorem norm_k1_cv_le {v : ℝ → ℂ} {M κ : ℝ} {q : ℝ → ℂ} (hv : SmoothPeriodic L v) (hJ : JB v M)
    (hJq : JB q M) (hκ : 0 ≤ κ) (c : ℂ) (x : ℝ) :
    ‖k1 κ q (fun x => c * v x) x‖ ≤ ‖c‖ * (2 * M + 6 * κ * M ^ 3) := by
  have h := norm_k1_le κ hκ q (fun x => c * v x) x
  rw [deriv_cmul_fun hv c, deriv_cmul_fun (sp_deriv hv) c] at h
  obtain ⟨h0, -, h2, -⟩ := hJ x
  have hq := (hJq x).1
  have hM := hJ.nonneg
  have hc := norm_nonneg c
  refine h.trans ?_
  simp only [norm_mul]
  have hq2 : ‖q x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hq 2
  have a1 : ‖c‖ * ‖v x‖ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left h0 hc
  have a2 : ‖c‖ * ‖deriv (deriv v) x‖ ≤ ‖c‖ * M := mul_le_mul_of_nonneg_left h2 hc
  have a3 : 6 * κ * ‖q x‖ ^ 2 * (‖c‖ * ‖v x‖) ≤ 6 * κ * M ^ 2 * (‖c‖ * M) := by
    have : 0 ≤ 6 * κ := by positivity
    gcongr
  nlinarith

end Bounds4

section AlphaDot

variable [Fact (0 < L)]

theorem conj_of_re_zero {z : ℂ} (h : z.re = 0) : conj z = -z :=
  Complex.ext (by simp [h]) (by simp)

theorem alpha_dot_eq (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u u' : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hd : IsWD u u') {α : ℂ} (hα : pair1 v u = α) {q : ℝ → ℂ}
    (hq : SmoothPeriodic L q) (hqe : q = fun x => α * v x) :
    pair1 (Xf κ v) u + Xpair κ v u u' =
      pair1 (Xf κ v) (fun y => u y - α * lift hv y)
        - α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * (∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x)
        + (-pair1 (deriv (deriv (deriv v))) (fun y => u y - α * lift hv y) -
            6 * (κ : ℂ) * LinC (lift hv) (lift hq) (lift (sp_deriv hq))
              (fun y => u y - α * lift hv y) (fun y => u' y - α * lift (sp_deriv hv) y))
        + (-(6 * (κ : ℂ)) * RemC (lift hv) (lift hq) (lift (sp_deriv hq))
            (fun y => u y - α * lift hv y) (fun y => u' y - α * lift (sp_deriv hv) y)) := by
  subst hqe
  have hvH := h04_lift hv
  have hvL : MemLp (lift hv) 2 (volume : Measure (AddCircle L)) :=
    memLp_of_continuous (continuous_lift hv)
  have hwH : H04 L 1 (fun y => u y - α * lift hv y) := (h04_sub hu (h04_cmul hvH α).1).1
  have hwL : MemLp (fun y => u y - α * lift hv y) 2 (volume : Measure (AddCircle L)) := hwH.1
  have hw'L : MemLp (fun y => u' y - α * lift (sp_deriv hv) y) 2 (volume : Measure (AddCircle L)) :=
    hd.2.1.sub ((memLp_of_continuous (continuous_lift (sp_deriv hv))).const_mul α)
  have hlq : lift hq = fun y => α * lift hv y :=
    lift_eq_fun hq _ (fun x => by simp only [lift_coe])
  have hlq' : lift (sp_deriv hq) = fun y => α * lift (sp_deriv hv) y :=
    lift_eq_fun (sp_deriv hq) _ (fun x => by
      simp only [lift_coe]; rw [deriv_cmul_fun hv α])
  have eu : u = fun y => lift hq y + (u y - α * lift hv y) := by
    funext y; rw [hlq]; ring
  have eu' : u' = fun y => lift (sp_deriv hq) y + (u' y - α * lift (sp_deriv hv) y) := by
    funext y; rw [hlq']; ring
  have hX := Xpair_decomp κ hv hq hwH hw'L
  rw [← eu, ← eu'] at hX
  have hξ := sp_Xf κ hv
  -- decomposition of the pairing with ξ
  have hdec : pair1 (Xf κ v) u = pair1 (Xf κ v) (fun y => u y - α * lift hv y) +
      α * pair1 (Xf κ v) (lift hv) := by
    have e : u = fun y => (u y - α * lift hv y) + α * lift hv y := by funext y; ring
    conv_lhs => rw [e]
    rw [pair1_add hξ.smooth.continuous hwL (hvL.const_mul α), pair1_smul]
  -- the scalars `a3`, `aN`
  set a3 := ∫ x in (0 : ℝ)..L, conj (v x) * deriv (deriv (deriv v)) x with ha3
  set aN := ∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x with haN
  have c3 : Continuous fun x => conj (v x) * deriv (deriv (deriv v)) x :=
    (Complex.continuous_conj.comp hv.smooth.continuous).mul
      (deriv_continuous (sp_deriv (sp_deriv hv)))
  have cN : Continuous fun x => conj (v x) * Nf κ v x :=
    (Complex.continuous_conj.comp hv.smooth.continuous).mul (sp_Nf κ hv).smooth.continuous
  have hxi : ∫ x in (0 : ℝ)..L, conj (v x) * Xf κ v x = a3 + aN := by
    have : ∀ x, conj (v x) * Xf κ v x = conj (v x) * deriv (deriv (deriv v)) x +
        conj (v x) * Nf κ v x := by
      intro x; simp only [Xf, Nf]; ring
    simp_rw [this]
    exact intervalIntegral.integral_add (c3.intervalIntegrable _ _) (cN.intervalIntegrable _ _)
  have hI0 : ∫ x in (0 : ℝ)..L, conj (v x) * Xf κ (fun x => α * v x) x =
      α * a3 + ((‖α‖ ^ 2 : ℝ) : ℂ) * α * aN := by
    rw [Xf_cmul κ hv α]
    have : ∀ x, conj (v x) * (α * deriv (deriv (deriv v)) x +
        ((‖α‖ ^ 2 : ℝ) : ℂ) * α * Nf κ v x) =
        α * (conj (v x) * deriv (deriv (deriv v)) x) +
          (((‖α‖ ^ 2 : ℝ) : ℂ) * α) * (conj (v x) * Nf κ v x) := by
      intro x; ring
    simp_rw [this]
    rw [intervalIntegral.integral_add ((c3.intervalIntegrable _ _).const_mul _)
      ((cN.intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  have hpv : pair1 (Xf κ v) (lift hv) = conj (a3 + aN) := by
    rw [pair1_lift_eq hv, ← hxi]
    have cx : Continuous fun x => conj (v x) * Xf κ v x :=
      (Complex.continuous_conj.comp hv.smooth.continuous).mul hξ.smooth.continuous
    rw [← intervalIntegral_conj (cx.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [map_mul, Complex.conj_conj]; ring
  have r3 : (a3 + aN).re = 0 := by
    rw [Complex.add_re, ha3, haN, mass_v3 hv, mass_N hv κ]; norm_num
  rw [hdec, hpv, conj_of_re_zero r3, hX, hI0]
  ring

end AlphaDot

section LinSplit

variable [Fact (0 < L)]

/-- The non-integrated part `∫ ḡ · 2Re(q̄ w) q'` of the linear remainder. -/
def IbC (G Q Q' w : AddCircle L → ℂ) : ℂ :=
  ∫ y, conj (G y) * (((2 * (conj (Q y) * w y).re : ℝ) : ℂ) * Q' y) ∂(volume : Measure (AddCircle L))

theorem LinC_eq {g q : ℝ → ℂ} (hg : SmoothPeriodic L g) (hq : SmoothPeriodic L q)
    {w w' : AddCircle L → ℂ} (hw : H04 L 1 w) (hd : IsWD w w') :
    LinC (lift hg) (lift hq) (lift (sp_deriv hq)) w w' =
      - pair1 (deriv (fun x => g x * ((‖q x‖ ^ 2 : ℝ) : ℂ))) w +
        IbC (lift hg) (lift hq) (lift (sp_deriv hq)) w := by
  have cG := continuous_lift hg
  have cQ := continuous_lift hq
  have cQ' := continuous_lift (sp_deriv hq)
  have iA := integrable_Ia cG cQ hd.2.1
  have iB := integrable_Ib cG cQ cQ' hw.1
  unfold LinC IbC
  rw [← Ia_eq hg hq hd, ← integral_add iA iB]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [fLin]; ring

theorem norm_IbC_le {G Q Q' w : AddCircle L → ℂ} (hG : Continuous G) (hQ : Continuous Q)
    (hQ' : Continuous Q') (hw : MemLp w 2 (volume : Measure (AddCircle L)))
    {B M M1 : ℝ} (hB : ∀ y, ‖G y‖ ≤ B) (hM : ∀ y, ‖Q y‖ ≤ M) (hM1 : ∀ y, ‖Q' y‖ ≤ M1) :
    ‖IbC G Q Q' w‖ ≤ B * (2 * M * M1) * ∫ y, ‖w y‖ ∂(volume : Measure (AddCircle L)) := by
  have iB := integrable_Ib hG hQ hQ' hw
  unfold IbC
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    ((int_norm hw).const_mul _) (Filter.Eventually.of_forall fun y => ?_)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB y)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM y)
  have hM10 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 y)
  have hre : |(conj (Q y) * w y).re| ≤ M * ‖w y‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hM y) (norm_nonneg _)
  simp only [norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
  have h1 : 2 * |(conj (Q y) * w y).re| ≤ 2 * (M * ‖w y‖) :=
    mul_le_mul_of_nonneg_left hre (by norm_num)
  calc ‖G y‖ * (2 * |(conj (Q y) * w y).re| * ‖Q' y‖) ≤ B * (2 * (M * ‖w y‖) * M1) := by
        refine mul_le_mul (hB y) (mul_le_mul h1 (hM1 y) (norm_nonneg _) (by positivity))
          (by positivity) hB0
    _ = B * (2 * M * M1) * ‖w y‖ := by ring

theorem sp_add {a b : ℝ → ℂ} (ha : SmoothPeriodic L a) (hb : SmoothPeriodic L b) :
    SmoothPeriodic L (fun x => a x + b x) :=
  ⟨ha.smooth.add hb.smooth, fun x => by simp only [ha.periodic x, hb.periodic x]⟩

theorem sp_k1 (κ : ℝ) {q h : ℝ → ℂ} (hq : SmoothPeriodic L q) (hh : SmoothPeriodic L h) :
    SmoothPeriodic L (k1 κ q h) := by
  have h1 := sp_lvec hh
  have h2 := sp_mul (sp_cmul (sp_normsq hq) (2 * (κ : ℂ))) hh
  have h3 := sp_mul (sp_cmul (sp_re_conj_mul hq hh) (2 * (κ : ℂ))) hq
  have e : k1 κ q h = fun x => (lvec h x + (2 * (κ : ℂ) * ((‖q x‖ ^ 2 : ℝ) : ℂ)) * h x) +
      (2 * (κ : ℂ) * ((2 * (conj (q x) * h x).re : ℝ) : ℂ)) * q x := by
    funext x; simp only [k1]; push_cast; ring
  rw [e]
  exact sp_add (sp_add h1 h2) h3

end LinSplit

section Combine

theorem combine_bound {L κ F' Aw W2 a T R PA PB S Bg KR kA ca cb cc CN : ℝ}
    (hL : 0 < L) (hκ : 0 ≤ κ) (hAw0 : 0 ≤ Aw) (hAw2 : Aw ^ 2 ≤ L * W2) (hAwS : Aw ≤ S)
    (hW20 : 0 ≤ W2) (hW2F : W2 ≤ F') (ha0 : 0 ≤ a) (hF0 : 0 ≤ F')
    (hBg : 0 ≤ Bg) (hKR : 0 ≤ KR) (hkA : 0 ≤ kA) (hca : 0 ≤ ca) (hcb : 0 ≤ cb) (hcc : 0 ≤ cc)
    (hCN : 0 ≤ CN) (hS : 0 ≤ S)
    (hα' : a ≤ ca * Aw + cb * W2 + cc * F')
    (hR : R ≤ 6 * κ * Bg * KR * F') (hPA : PA ≤ a * kA * Aw) (hPB : PB ≤ W2 * CN * Aw)
    (hT : |T| ≤ 2 * R + 2 * PA + 2 * PB) :
    |T| ≤ (12 * κ * Bg * KR + 2 * kA * (ca * L + cb * S + cc * S) + 2 * CN * S) * F' := by
  have e2 : Aw ^ 2 ≤ L * F' := hAw2.trans (mul_le_mul_of_nonneg_left hW2F hL.le)
  have e3 : W2 * Aw ≤ S * F' := by
    calc W2 * Aw ≤ W2 * S := mul_le_mul_of_nonneg_left hAwS hW20
      _ ≤ F' * S := mul_le_mul_of_nonneg_right hW2F hS
      _ = S * F' := by ring
  have e4 : F' * Aw ≤ S * F' := by
    calc F' * Aw ≤ F' * S := mul_le_mul_of_nonneg_left hAwS hF0
      _ = S * F' := by ring
  have e1 : a * Aw ≤ ca * (L * F') + cb * (S * F') + cc * (S * F') := by
    have h1 := mul_le_mul_of_nonneg_right hα' hAw0
    have : (ca * Aw + cb * W2 + cc * F') * Aw = ca * Aw ^ 2 + cb * (W2 * Aw) + cc * (F' * Aw) := by ring
    rw [this] at h1
    have h2 := mul_le_mul_of_nonneg_left e2 hca
    have h3 := mul_le_mul_of_nonneg_left e3 hcb
    have h4 := mul_le_mul_of_nonneg_left e4 hcc
    linarith
  have hPA' : PA ≤ kA * (ca * (L * F') + cb * (S * F') + cc * (S * F')) := by
    calc PA ≤ a * kA * Aw := hPA
      _ = kA * (a * Aw) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e1 hkA
  have hPB' : PB ≤ CN * (S * F') := by
    calc PB ≤ W2 * CN * Aw := hPB
      _ = CN * (W2 * Aw) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left e3 hCN
  refine hT.trans ?_
  nlinarith [hR, hPA', hPB']

end Combine

section Final

variable [Fact (0 < L)]

/-- `w = u − αv` as a torus field. -/
def wfn {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (u : AddCircle L → ℂ) (α : ℂ) : AddCircle L → ℂ :=
  fun y => u y - α * lift hv y

/-- `w' = u' − αv'`. -/
def wpfn {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (u' : AddCircle L → ℂ) (α : ℂ) : AddCircle L → ℂ :=
  fun y => u' y - α * lift (sp_deriv hv) y

/-- `‖w'‖₂² + ‖w‖₂² + (κ/3)‖w‖₄⁴`. -/
def Fp (κ : ℝ) (w w' : AddCircle L → ℂ) : ℝ :=
  (∫ y, ‖w' y‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
    (∫ y, ‖w y‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
    κ / 3 * ∫ y, ‖w y‖ ^ 4 ∂(volume : Measure (AddCircle L))

def KR (κ M : ℝ) : ℝ := M + M + 3 / (2 * κ) + 1 / 2

theorem wfn_H04 {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ} (hu : H04 L 1 u)
    (α : ℂ) : H04 L 1 (wfn hv u α) := (h04_sub hu (h04_cmul (h04_lift hv) α).1).1

theorem wpfn_memLp {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u' : AddCircle L → ℂ}
    (hu' : MemLp u' 2 (volume : Measure (AddCircle L))) (α : ℂ) :
    MemLp (wpfn hv u' α) 2 (volume : Measure (AddCircle L)) :=
  hu'.sub ((memLp_of_continuous (continuous_lift (sp_deriv hv))).const_mul α)

theorem wfn_IsWD {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u u' : AddCircle L → ℂ} (hd : IsWD u u')
    (α : ℂ) : IsWD (wfn hv u α) (wpfn hv u' α) :=
  hd.sub (IsWD.const_mul (IsWD.smooth hv) α)

theorem Fp_le_Fv {κ : ℝ} (hκ : 0 ≤ κ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v)
    {u u' : AddCircle L → ℂ} (hu : H04 L 1 u) (hd : IsWD u u') {α : ℂ} (hα : pair1 v u = α) :
    Fp κ (wfn hv u α) (wpfn hv u' α) ≤ Fv κ (lift hv) u := by
  have hvH := h04_lift hv
  have hwH := wfn_H04 hv hu α
  have hdw := wfn_IsWD hv hd α
  have hc := Fv_coercive_general hκ hvH hu
  have hal : alpha (lift hv) u = α := by rw [alpha_eq_pair1 hv, hα]
  have hwF : wF (lift hv) u = wfn hv u α := by
    funext y; simp only [wF, wfn, hal]
  rw [hwF, h04Norm_sq, f04NormSq_eq hwH, kinetic_eq_of_IsWD hdw] at hc
  unfold Fp
  have e1 : I1 (wfn hv u α) = ∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L)) := rfl
  have e2 : quartic (wfn hv u α) = ∫ y, ‖wfn hv u α y‖ ^ 4 ∂(volume : Measure (AddCircle L)) := rfl
  rw [e1, e2] at hc
  exact hc

theorem norm_alpha_le {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (hv1 : I1 (lift hv) = 1)
    {u : AddCircle L → ℂ} (hu : H04 L 1 u) (hu1 : I1 u = 1) {α : ℂ} (hα : pair1 v u = α) :
    (∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L))) = 1 - ‖α‖ ^ 2 ∧ ‖α‖ ≤ 1 := by
  have hvH := h04_lift hv
  have hal : alpha (lift hv) u = α := by rw [alpha_eq_pair1 hv, hα]
  have hwF : wF (lift hv) u = wfn hv u α := by
    funext y; simp only [wF, wfn, hal]
  have h := I1_wF hvH hu hv1 hu1
  rw [hwF, hal] at h
  have e1 : I1 (wfn hv u α) = ∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L)) := rfl
  rw [e1] at h
  refine ⟨h, ?_⟩
  have h0 : 0 ≤ ∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L)) :=
    integral_nonneg (fun y => sq_nonneg _)
  rw [h] at h0
  nlinarith [norm_nonneg α]

end Final

section AlphaBound

variable [Fact (0 < L)]

theorem norm_aN_le {v : ℝ → ℂ} {M κ : ℝ} (hv : SmoothPeriodic L v) (hJ : JB v M) (hκ : 0 ≤ κ) :
    ‖∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x‖ ≤ (M * (6 * κ * M ^ 3)) * L := by
  have hL : 0 < L := Fact.out
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := L)
    (f := fun x => conj (v x) * Nf κ v x) (C := M * (6 * κ * M ^ 3)) (fun x _ => by
      simp only [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (hJ x).1 (norm_Nf_le hJ hκ x) (norm_nonneg _) hJ.nonneg)
  simpa [abs_of_pos hL] using this

theorem norm_deriv_e_le {v q : ℝ → ℂ} {M : ℝ} (hv : SmoothPeriodic L v) (hJ : JB v M)
    (hq : SmoothPeriodic L q) (hJq : JB q M) (x : ℝ) :
    ‖deriv (fun x => v x * ((‖q x‖ ^ 2 : ℝ) : ℂ)) x‖ ≤ 3 * M ^ 3 := by
  have h := ((hasDerivAt_of_smooth hv x).mul (hasDerivAt_M0 hq x)).deriv
  have hh : deriv (fun x => v x * ((‖q x‖ ^ 2 : ℝ) : ℂ)) x =
      deriv v x * M0f q x + v x * M1f q x := h
  rw [hh]
  have a0 := norm_M0f_le hJq x
  have a1 := norm_M1f_le hJq x
  have hM := hJ.nonneg
  obtain ⟨h0, h1, -, -⟩ := hJ x
  calc _ ≤ ‖deriv v x * M0f q x‖ + ‖v x * M1f q x‖ := norm_add_le _ _
    _ ≤ M * M ^ 2 + M * (2 * M ^ 2) := by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul h1 a0 (norm_nonneg _) hM) (mul_le_mul h0 a1 (norm_nonneg _) hM)
    _ = 3 * M ^ 3 := by ring

theorem alpha_dot_bound {κ M : ℝ} (hκ : 0 < κ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v)
    (hJ : JB v M) {u u' : AddCircle L → ℂ} (hu : H04 L 1 u) (hd : IsWD u u') {α : ℂ}
    (hα : pair1 v u = α) (hα1 : ‖α‖ ≤ 1)
    (hW2 : (∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L))) = 1 - ‖α‖ ^ 2)
    {q : ℝ → ℂ} (hq : SmoothPeriodic L q) (hqe : q = fun x => α * v x) :
    ‖pair1 (Xf κ v) u + Xpair κ v u u'‖ ≤
      (2 * M + 36 * κ * M ^ 3) * (∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L))) +
        6 * κ * L * M ^ 4 * (∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L))) +
        6 * κ * M * KR κ M * Fp κ (wfn hv u α) (wpfn hv u' α) := by
  have hL : 0 < L := Fact.out
  have hM := hJ.nonneg
  have hJq : JB q M := by rw [hqe]; exact JB_cmul hv hJ hα1
  have hwH := wfn_H04 hv hu α
  have hwL := hwH.1
  have hw'L := wpfn_memLp hv hd.2.1 α
  have hdw := wfn_IsWD hv hd α
  have hid : pair1 (Xf κ v) u + Xpair κ v u u' =
      pair1 (Xf κ v) (wfn hv u α)
        - α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * (∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x)
        + (-pair1 (deriv (deriv (deriv v))) (wfn hv u α) -
            6 * (κ : ℂ) * LinC (lift hv) (lift hq) (lift (sp_deriv hq))
              (wfn hv u α) (wpfn hv u' α))
        + (-(6 * (κ : ℂ)) * RemC (lift hv) (lift hq) (lift (sp_deriv hq))
            (wfn hv u α) (wpfn hv u' α)) := alpha_dot_eq κ hv hu hd hα hq hqe
  rw [hid, LinC_eq hv hq hwH hdw]
  -- individual bounds
  have b1 : ‖pair1 (Xf κ v) (wfn hv u α)‖ ≤
      (M + 6 * κ * M ^ 3) * ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) :=
    norm_pair1_le (sp_Xf κ hv) (norm_Xf_le hJ hκ.le) hwL
  have b2 : ‖pair1 (deriv (deriv (deriv v))) (wfn hv u α)‖ ≤
      M * ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) :=
    norm_pair1_le (sp_deriv (sp_deriv (sp_deriv hv))) (fun x => (hJ x).2.2.2) hwL
  have he := sp_mul hv (sp_normsq hq)
  have b3 : ‖pair1 (deriv (fun x => v x * ((‖q x‖ ^ 2 : ℝ) : ℂ))) (wfn hv u α)‖ ≤
      (3 * M ^ 3) * ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) :=
    norm_pair1_le (sp_deriv he) (norm_deriv_e_le hv hJ hq hJq) hwL
  have b4 : ‖IbC (lift hv) (lift hq) (lift (sp_deriv hq)) (wfn hv u α)‖ ≤
      M * (2 * M * M) * ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) :=
    norm_IbC_le (continuous_lift hv) (continuous_lift hq) (continuous_lift (sp_deriv hq)) hwL
      (norm_lift_le hv (fun x => (hJ x).1)) (norm_lift_le hq (fun x => (hJq x).1))
      (norm_lift_le (sp_deriv hq) (fun x => (hJq x).2.1))
  have b5 : ‖RemC (lift hv) (lift hq) (lift (sp_deriv hq)) (wfn hv u α) (wpfn hv u' α)‖ ≤
      M * KR κ M * Fp κ (wfn hv u α) (wpfn hv u' α) := by
    have := norm_RemC_le (continuous_lift hv) (continuous_lift hq) (continuous_lift (sp_deriv hq))
      hwH hw'L hκ (norm_lift_le hv (fun x => (hJ x).1)) (norm_lift_le hq (fun x => (hJq x).1))
      (norm_lift_le (sp_deriv hq) (fun x => (hJq x).2.1))
    unfold KR Fp
    exact this
  have b6 := norm_aN_le hv hJ hκ.le
  have hW2' : ‖(1 : ℂ) - ((‖α‖ ^ 2 : ℝ) : ℂ)‖ = 1 - ‖α‖ ^ 2 := by
    have : (1 : ℂ) - ((‖α‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg]
    nlinarith [norm_nonneg α]
  have b7 : ‖α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * ∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x‖ ≤
      6 * κ * L * M ^ 4 * ∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L)) := by
    rw [norm_mul, norm_mul, hW2', hW2]
    have h1 : 0 ≤ 1 - ‖α‖ ^ 2 := by nlinarith [norm_nonneg α]
    calc ‖α‖ * (1 - ‖α‖ ^ 2) * ‖∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x‖ ≤
          1 * (1 - ‖α‖ ^ 2) * ((M * (6 * κ * M ^ 3)) * L) := by
          refine mul_le_mul (mul_le_mul hα1 le_rfl h1 zero_le_one) b6 (norm_nonneg _) (by positivity)
      _ = 6 * κ * L * M ^ 4 * (1 - ‖α‖ ^ 2) := by ring
  have hAw0 : 0 ≤ ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) :=
    integral_nonneg (fun y => norm_nonneg _)
  set Aw := ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) with hAw
  set Rm := RemC (lift hv) (lift hq) (lift (sp_deriv hq)) (wfn hv u α) (wpfn hv u' α)
  set Ib := IbC (lift hv) (lift hq) (lift (sp_deriv hq)) (wfn hv u α)
  set E := pair1 (deriv (fun x => v x * ((‖q x‖ ^ 2 : ℝ) : ℂ))) (wfn hv u α)
  set P := pair1 (deriv (deriv (deriv v))) (wfn hv u α)
  set Ξ := pair1 (Xf κ v) (wfn hv u α)
  set aN := ∫ x in (0 : ℝ)..L, conj (v x) * Nf κ v x
  have h6κ : ‖(6 * (κ : ℂ))‖ = 6 * κ := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  calc _ ≤ ‖Ξ - α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * aN + (-P - 6 * (κ : ℂ) * (-E + Ib))‖ +
        ‖-(6 * (κ : ℂ)) * Rm‖ := norm_add_le _ _
    _ ≤ (‖Ξ - α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * aN‖ + ‖-P - 6 * (κ : ℂ) * (-E + Ib)‖) +
        ‖-(6 * (κ : ℂ)) * Rm‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖Ξ‖ + ‖α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * aN‖) +
        (‖P‖ + 6 * κ * (‖E‖ + ‖Ib‖))) + 6 * κ * ‖Rm‖ := by
        have t1 : ‖Ξ - α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * aN‖ ≤
            ‖Ξ‖ + ‖α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ)) * aN‖ := norm_sub_le _ _
        have t2 : ‖-P - 6 * (κ : ℂ) * (-E + Ib)‖ ≤ ‖P‖ + 6 * κ * (‖E‖ + ‖Ib‖) := by
          calc _ ≤ ‖-P‖ + ‖6 * (κ : ℂ) * (-E + Ib)‖ := norm_sub_le _ _
            _ = ‖P‖ + 6 * κ * ‖-E + Ib‖ := by rw [norm_neg, norm_mul, h6κ]
            _ ≤ ‖P‖ + 6 * κ * (‖E‖ + ‖Ib‖) := by
              gcongr
              exact (norm_add_le _ _).trans (by rw [norm_neg])
        have t3 : ‖-(6 * (κ : ℂ)) * Rm‖ = 6 * κ * ‖Rm‖ := by rw [norm_mul, norm_neg, h6κ]
        rw [t3]
        linarith
    _ ≤ _ := by
      have : 0 ≤ 6 * κ := by positivity
      have c1 := mul_le_mul_of_nonneg_left b3 this
      have c2 := mul_le_mul_of_nonneg_left b4 this
      have c3 := mul_le_mul_of_nonneg_left b5 this
      nlinarith [b1, b2, b7, c1, c2, c3]

end AlphaBound

section MainBound

variable [Fact (0 < L)]

def Cbound (κ L M : ℝ) : ℝ :=
  12 * κ * (2 * M + 2 * κ * M ^ 3) * KR κ M +
    2 * (2 * M + 6 * κ * M ^ 3) * ((2 * M + 36 * κ * M ^ 3) * L +
      6 * κ * L * M ^ 4 * ((1 + L) / 2) + 6 * κ * M * KR κ M * ((1 + L) / 2)) +
    2 * (60 * κ * M ^ 3 + 36 * κ ^ 2 * M ^ 5) * ((1 + L) / 2)

theorem Ttot_bound {κ M : ℝ} (hκ : 0 < κ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) (hJ : JB v M)
    (hv1 : I1 (lift hv) = 1) {u u' : AddCircle L → ℂ} (hu : H04 L 1 u) (hu1 : I1 u = 1)
    (hd : IsWD u u') : |Ttot κ v u u'| ≤ Cbound κ L M * Fv κ (lift hv) u := by
  have hL : 0 < L := Fact.out
  have hM := hJ.nonneg
  obtain ⟨α, hα⟩ : ∃ α, pair1 v u = α := ⟨_, rfl⟩
  obtain ⟨hW2, hα1⟩ := norm_alpha_le hv hv1 hu hu1 hα
  have hq : SmoothPeriodic L (fun x => α * v x) := sp_cmul hv α
  have hJq : JB (fun x => α * v x) M := JB_cmul hv hJ hα1
  have hwH := wfn_H04 hv hu α
  have hwL := hwH.1
  have hw'L := wpfn_memLp hv hd.2.1 α
  have hdw := wfn_IsWD hv hd α
  have hid : Ttot κ v u u' =
      2 * (-(6 * (κ : ℂ)) * RemC (lift (sp_gE κ hq)) (lift hq) (lift (sp_deriv hq))
          (wfn hv u α) (wpfn hv u' α)).re
      + 2 * (pair1 (k1 κ (fun x => α * v x)
          (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x)) (wfn hv u α)).re
      + 2 * (pair1 (fun x => k1 κ (fun x => α * v x) (fun x => α * Xf κ v x) x -
          k1 κ (fun x => α * v x) (Xf κ (fun x => α * v x)) x) (wfn hv u α)).re :=
    Ttot_identity κ hv hu hd hα hq rfl
  have hF := Fp_le_Fv hκ.le hv hu hd hα
  set Aw := ∫ y, ‖wfn hv u α y‖ ∂(volume : Measure (AddCircle L)) with hAw
  set W2 := ∫ y, ‖wfn hv u α y‖ ^ 2 ∂(volume : Measure (AddCircle L)) with hW2d
  set F' := Fp κ (wfn hv u α) (wpfn hv u' α) with hF'
  have hAw0 : 0 ≤ Aw := integral_nonneg (fun y => norm_nonneg _)
  have hAw2 : Aw ^ 2 ≤ L * W2 := Aw_sq_le hwL
  have hW20 : 0 ≤ W2 := integral_nonneg (fun y => sq_nonneg _)
  have hW2le : W2 ≤ 1 := by rw [hW2]; nlinarith [norm_nonneg α]
  have hAwS : Aw ≤ (1 + L) / 2 := by
    have : Aw ^ 2 ≤ L := by nlinarith
    nlinarith [sq_nonneg (Aw - 1)]
  have hW2F : W2 ≤ F' := by
    have h1 : 0 ≤ ∫ y, ‖wpfn hv u' α y‖ ^ 2 ∂(volume : Measure (AddCircle L)) :=
      integral_nonneg (fun y => sq_nonneg _)
    have h2 : 0 ≤ ∫ y, ‖wfn hv u α y‖ ^ 4 ∂(volume : Measure (AddCircle L)) :=
      integral_nonneg (fun y => by positivity)
    unfold Fp at hF'
    rw [hF']
    nlinarith
  have hF0 : 0 ≤ F' := hW20.trans hW2F
  -- the three bounds
  have hα' := alpha_dot_bound hκ hv hJ hu hd hα hα1 hW2 hq rfl
  set a := ‖pair1 (Xf κ v) u + Xpair κ v u u'‖ with ha
  have hRem := norm_RemC_le (continuous_lift (sp_gE κ hq)) (continuous_lift hq)
    (continuous_lift (sp_deriv hq)) hwH hw'L hκ
    (norm_lift_le (sp_gE κ hq) (norm_gE_le hJq hκ.le))
    (norm_lift_le hq (fun x => (hJq x).1)) (norm_lift_le (sp_deriv hq) (fun x => (hJq x).2.1))
  have h6κ : ‖(6 * (κ : ℂ))‖ = 6 * κ := by
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  have hR : ‖-(6 * (κ : ℂ)) * RemC (lift (sp_gE κ hq)) (lift hq) (lift (sp_deriv hq))
      (wfn hv u α) (wpfn hv u' α)‖ ≤ 6 * κ * (2 * M + 2 * κ * M ^ 3) * KR κ M * F' := by
    rw [norm_mul, norm_neg, h6κ]
    have h1 : 0 ≤ 6 * κ := by positivity
    calc 6 * κ * ‖RemC (lift (sp_gE κ hq)) (lift hq) (lift (sp_deriv hq))
          (wfn hv u α) (wpfn hv u' α)‖ ≤ 6 * κ * ((2 * M + 2 * κ * M ^ 3) * KR κ M * F') := by
          refine mul_le_mul_of_nonneg_left ?_ h1
          unfold KR Fp at *
          exact hRem
      _ = _ := by ring
  have hPA : ‖pair1 (k1 κ (fun x => α * v x)
      (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x)) (wfn hv u α)‖ ≤
      a * (2 * M + 6 * κ * M ^ 3) * Aw :=
    norm_pair1_le (sp_k1 κ hq (sp_cmul hv _))
      (fun x => norm_k1_cv_le hv hJ hJq hκ.le _ x) hwL
  have hfun : (fun x => k1 κ (fun x => α * v x) (fun x => α * Xf κ v x) x -
      k1 κ (fun x => α * v x) (Xf κ (fun x => α * v x)) x) =
      k1 κ (fun x => α * v x) (fun x => (α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ))) * Nf κ v x) := by
    rw [← xi_sub κ hv α]
    exact (k1_sub κ (fun x => α * v x) (sp_Xf_cmul κ hv α) (sp_Xf κ hq)).symm
  have hcn : ‖α * (1 - ((‖α‖ ^ 2 : ℝ) : ℂ))‖ ≤ W2 := by
    have : (1 : ℂ) - ((‖α‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖α‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, this, Complex.norm_real, Real.norm_of_nonneg (by nlinarith [norm_nonneg α]), hW2]
    nlinarith [norm_nonneg α, sq_nonneg ‖α‖]
  have hPB : ‖pair1 (fun x => k1 κ (fun x => α * v x) (fun x => α * Xf κ v x) x -
      k1 κ (fun x => α * v x) (Xf κ (fun x => α * v x)) x) (wfn hv u α)‖ ≤
      W2 * (60 * κ * M ^ 3 + 36 * κ ^ 2 * M ^ 5) * Aw := by
    rw [hfun]
    refine (norm_pair1_le (sp_k1 κ hq (sp_cmul (sp_Nf κ hv) _))
      (fun x => norm_k1_cN_le hv hJ hJq hκ.le _ x) hwL).trans ?_
    have h0 : 0 ≤ 60 * κ * M ^ 3 + 36 * κ ^ 2 * M ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_right hcn h0
    exact mul_le_mul_of_nonneg_right this hAw0
  -- assemble
  have hre : ∀ z : ℂ, |z.re| ≤ ‖z‖ := fun z => Complex.abs_re_le_norm z
  have hT : |Ttot κ v u u'| ≤ 2 * ‖-(6 * (κ : ℂ)) * RemC (lift (sp_gE κ hq)) (lift hq)
        (lift (sp_deriv hq)) (wfn hv u α) (wpfn hv u' α)‖ +
      2 * ‖pair1 (k1 κ (fun x => α * v x)
        (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x)) (wfn hv u α)‖ +
      2 * ‖pair1 (fun x => k1 κ (fun x => α * v x) (fun x => α * Xf κ v x) x -
          k1 κ (fun x => α * v x) (Xf κ (fun x => α * v x)) x) (wfn hv u α)‖ := by
    rw [hid]
    refine (abs_add_three _ _ _).trans ?_
    have := hre (-(6 * (κ : ℂ)) * RemC (lift (sp_gE κ hq)) (lift hq) (lift (sp_deriv hq))
          (wfn hv u α) (wpfn hv u' α))
    have h2 := hre (pair1 (k1 κ (fun x => α * v x)
        (fun x => (pair1 (Xf κ v) u + Xpair κ v u u') * v x)) (wfn hv u α))
    have h3 := hre (pair1 (fun x => k1 κ (fun x => α * v x) (fun x => α * Xf κ v x) x -
          k1 κ (fun x => α * v x) (Xf κ (fun x => α * v x)) x) (wfn hv u α))
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    linarith
  have hpos : 0 ≤ KR κ M := by unfold KR; positivity
  have hfin := combine_bound (L := L) (κ := κ) (F' := F') (Aw := Aw) (W2 := W2) (a := a)
    (T := Ttot κ v u u') (S := (1 + L) / 2) (Bg := 2 * M + 2 * κ * M ^ 3) (KR := KR κ M)
    (kA := 2 * M + 6 * κ * M ^ 3) (ca := 2 * M + 36 * κ * M ^ 3) (cb := 6 * κ * L * M ^ 4)
    (cc := 6 * κ * M * KR κ M) (CN := 60 * κ * M ^ 3 + 36 * κ ^ 2 * M ^ 5)
    hL hκ.le hAw0 hAw2 hAwS hW20 hW2F (norm_nonneg _) hF0 (by positivity) hpos (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by simpa [ha] using hα')
    hR hPA hPB hT
  have hC : Cbound κ L M * F' ≤ Cbound κ L M * Fv κ (lift hv) u := by
    refine mul_le_mul_of_nonneg_left hF ?_
    unfold Cbound; positivity
  refine hfin.trans ?_
  unfold Cbound
  unfold Cbound at hC
  exact hC

end MainBound

section Uniform

/-- The partial derivative in the space variable of a function of `(t, x)`. -/
def Dx (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => fderiv ℝ g p (0, 1)

theorem contDiff_Dx {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (Dx g) :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

theorem contDiff_Dx_iter {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    ContDiff ℝ ∞ (Dx^[k] g) := by
  induction k with
  | zero => exact hg
  | succ k ih => rw [Function.iterate_succ_apply']; exact contDiff_Dx ih

theorem hasDerivAt_Dx {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (t x : ℝ) :
    HasDerivAt (fun y => g (t, y)) (Dx g (t, x)) x := by
  have h1 : HasFDerivAt g (fderiv ℝ g (t, x)) (t, x) :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun y : ℝ => ((t, y) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  exact h1.comp_hasDerivAt x h2

theorem jet_slice {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (k : ℕ) :
    jet (fun x => f (t, x)) k = fun x => (Dx^[k] f) (t, x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : jet (fun x => f (t, x)) (k + 1) = deriv (jet (fun x => f (t, x)) k) := by
      unfold jet; rw [Function.iterate_succ_apply']
    rw [this, ih, Function.iterate_succ_apply']
    exact funext fun x => (hasDerivAt_Dx (contDiff_Dx_iter hf k) t x).deriv

theorem sp_slice [Fact (0 < L)] {V : ℝ → ℝ → ℂ} (hV : ContDiff ℝ ∞ (Function.uncurry V))
    (hper : ∀ t, Function.Periodic (V t) L) (t : ℝ) : SmoothPeriodic L (V t) :=
  ⟨hV.comp (contDiff_const.prodMk contDiff_id), hper t⟩

theorem exists_JB_uniform [Fact (0 < L)] {V : ℝ → ℝ → ℂ}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hper : ∀ t, Function.Periodic (V t) L)
    {K : Set ℝ} (hK : IsCompact K) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ K, JB (V t) M := by
  have hL : 0 < L := Fact.out
  have hKc : IsCompact (K ×ˢ Set.Icc (0 : ℝ) L) := hK.prod isCompact_Icc
  have hb : ∀ k : ℕ, ∃ C : ℝ, ∀ p ∈ K ×ˢ Set.Icc (0 : ℝ) L, ‖(Dx^[k] (Function.uncurry V)) p‖ ≤ C :=
    fun k => hKc.exists_bound_of_continuousOn (contDiff_Dx_iter hV k).continuous.continuousOn
  obtain ⟨C0, h0⟩ := hb 0
  obtain ⟨C1, h1⟩ := hb 1
  obtain ⟨C2, h2⟩ := hb 2
  obtain ⟨C3, h3⟩ := hb 3
  refine ⟨max (max C0 C1) (max (max C2 C3) 0), le_max_of_le_right (le_max_right _ _), fun t ht x => ?_⟩
  have key : ∀ (k : ℕ) (C : ℝ), (∀ p ∈ K ×ˢ Set.Icc (0 : ℝ) L, ‖(Dx^[k] (Function.uncurry V)) p‖ ≤ C) →
      ‖jet (V t) k x‖ ≤ C := by
    intro k C hC
    have hp := (sp_jet (sp_slice hV hper t) k).periodic
    obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico₀ hL x
    rw [hxy]
    have := hC (t, y) ⟨ht, ⟨hy.1, hy.2.le⟩⟩
    have e : jet (V t) k y = (Dx^[k] (Function.uncurry V)) (t, y) := by
      have := jet_slice hV t k
      exact congrFun this y
    rw [e]; exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (key 0 C0 h0).trans (le_max_of_le_left (le_max_left _ _))
  · exact (key 1 C1 h1).trans (le_max_of_le_left (le_max_right _ _))
  · exact (key 2 C2 h2).trans (le_max_of_le_right (le_max_of_le_left (le_max_left _ _)))
  · exact (key 3 C3 h3).trans (le_max_of_le_right (le_max_of_le_left (le_max_right _ _)))

end Uniform

section FinalThm

variable [Fact (0 < L)]

/-- **Uniform transport bound on a compact time set, formal `v_t = X(v)` form.** -/
theorem energy006_transport_uniform {κ : ℝ} (hκ : 0 < κ) {V : ℝ → ℝ → ℂ}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hper : ∀ t, Function.Periodic (V t) L)
    (hunit : ∀ t, I1 (lift (sp_slice hV hper t)) = 1) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ (u u' : AddCircle L → ℂ) (hu : H04 L 1 u), I1 u = 1 →
      IsWD u u' → |Ttot κ (V t) u u'| ≤ C * Fv κ (lift (sp_slice hV hper t)) u := by
  have hL : 0 < L := Fact.out
  obtain ⟨M, hM0, hM⟩ := exists_JB_uniform hV hper hK
  refine ⟨Cbound κ L M, ?_, fun t ht u u' hu hu1 hd => ?_⟩
  · unfold Cbound KR; positivity
  · exact Ttot_bound hκ (sp_slice hV hper t) (hM t ht) (hunit t) hu hu1 hd

end FinalThm

section Faithful

variable [Fact (0 < L)]

theorem hasDerivAt_quad (c0 c1 c2 : ℝ) :
    HasDerivAt (fun ε : ℝ => c0 + ε * c1 + ε ^ 2 * c2) c1 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => ε * c1) c1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c1
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * c2) 0 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const c2
  exact ((h1.const_add c0).add h2).congr_deriv (by simp)

/-- `dSigma` is the directional derivative of the printed polynomial `Σ` (`eq:A1-S`) along the
line of data `(α + εα', a + εa', b + εb', E₂ + εE₂', V₄ + εV₄')`. -/
theorem dSigma_eq_deriv (κ E₂ V₄ : ℝ) (α a b α' a' b' : ℂ) (E₂' V₄' : ℝ) :
    deriv (fun ε : ℝ => Sigma κ (E₂ + ε * E₂') (V₄ + ε * V₄') (α + (ε : ℂ) * α')
        (a + (ε : ℂ) * a') (b + (ε : ℂ) * b')) 0 = dSigma κ E₂ V₄ α a b α' a' b' E₂' V₄' := by
  have nrm : ∀ ε : ℝ, ‖α + (ε : ℂ) * α'‖ ^ 2 =
      ‖α‖ ^ 2 + ε * (2 * (conj α * α').re) + ε ^ 2 * ‖α'‖ ^ 2 := by
    intro ε
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im]
    ring
  have rea : ∀ (x x' : ℂ) (ε : ℝ), (conj (α + (ε : ℂ) * α') * (x + (ε : ℂ) * x')).re =
      (conj α * x).re + ε * (conj α' * x + conj α * x').re + ε ^ 2 * (conj α' * x').re := by
    intro x x' ε
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have h1 : HasDerivAt (fun ε : ℝ => ‖α + (ε : ℂ) * α'‖ ^ 2) (2 * (conj α * α').re) 0 := by
    have := hasDerivAt_quad (‖α‖ ^ 2) (2 * (conj α * α').re) (‖α'‖ ^ 2)
    simpa only [nrm] using this
  have h2 : ∀ x x' : ℂ, HasDerivAt (fun ε : ℝ => (conj (α + (ε : ℂ) * α') * (x + (ε : ℂ) * x')).re)
      (conj α' * x + conj α * x').re 0 := by
    intro x x'
    have := hasDerivAt_quad (conj α * x).re (conj α' * x + conj α * x').re (conj α' * x').re
    simpa only [rea] using this
  have hE : HasDerivAt (fun ε : ℝ => E₂ + ε * E₂') E₂' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const E₂').const_add E₂
  have hV : HasDerivAt (fun ε : ℝ => V₄ + ε * V₄') V₄' 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const V₄').const_add V₄
  have hS : HasDerivAt (fun ε : ℝ => 2 * (conj (α + (ε : ℂ) * α') * (a + (ε : ℂ) * a')).re -
      ‖α + (ε : ℂ) * α'‖ ^ 2 * (E₂ + ε * E₂') +
      4 * κ * (‖α + (ε : ℂ) * α'‖ ^ 2 * (conj (α + (ε : ℂ) * α') * (b + (ε : ℂ) * b')).re) -
      3 * κ * ((‖α + (ε : ℂ) * α'‖ ^ 2) ^ 2 * (V₄ + ε * V₄')))
      (2 * (conj α' * a + conj α * a').re -
        (2 * (conj α * α').re * (E₂ + 0 * E₂') + ‖α + ((0 : ℝ) : ℂ) * α'‖ ^ 2 * E₂') +
        4 * κ * (2 * (conj α * α').re * (conj (α + ((0 : ℝ) : ℂ) * α') * (b + ((0 : ℝ) : ℂ) * b')).re +
          ‖α + ((0 : ℝ) : ℂ) * α'‖ ^ 2 * (conj α' * b + conj α * b').re) -
        3 * κ * ((↑(2 : ℕ) * (‖α + ((0 : ℝ) : ℂ) * α'‖ ^ 2) ^ (2 - 1) * (2 * (conj α * α').re)) *
          (V₄ + 0 * V₄') + (‖α + ((0 : ℝ) : ℂ) * α'‖ ^ 2) ^ 2 * V₄')) 0 :=
    ((((h2 a a').const_mul 2).sub (h1.mul hE)).add ((h1.mul (h2 b b')).const_mul (4 * κ))).sub
      (((h1.pow 2).mul hV).const_mul (3 * κ))
  have hfun : (fun ε : ℝ => Sigma κ (E₂ + ε * E₂') (V₄ + ε * V₄') (α + (ε : ℂ) * α')
        (a + (ε : ℂ) * a') (b + (ε : ℂ) * b')) = fun ε : ℝ =>
      2 * (conj (α + (ε : ℂ) * α') * (a + (ε : ℂ) * a')).re -
      ‖α + (ε : ℂ) * α'‖ ^ 2 * (E₂ + ε * E₂') +
      4 * κ * (‖α + (ε : ℂ) * α'‖ ^ 2 * (conj (α + (ε : ℂ) * α') * (b + (ε : ℂ) * b')).re) -
      3 * κ * ((‖α + (ε : ℂ) * α'‖ ^ 2) ^ 2 * (V₄ + ε * V₄')) := by
    funext ε
    simp only [Sigma]
    ring
  rw [hfun, hS.deriv]
  simp only [dSigma, Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_ofNat]
  ring

end Faithful

section Faithful2

variable [Fact (0 < L)]

theorem Sv_eq_Sigma (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u : AddCircle L → ℂ}
    (hu : H04 L 1 u) :
    Sv κ (lift hv) u = Sigma κ (E2 L v) (V4 L v) (pair1 v u) (pair1 (lvec v) u) (pair1 (rvec v) u) := by
  have h := Sv_explicit κ hv hu
  rw [E2_eq hv, V4_eq hv, alpha_eq_pair1 hv] at h
  exact h

theorem Sv_line (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u h : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hh : H04 L 1 h) (ε : ℝ) :
    Sv κ (lift hv) (lineF u h ε) =
      Sigma κ (E2 L v) (V4 L v) (pair1 v u + (ε : ℂ) * pair1 v h)
        (pair1 (lvec v) u + (ε : ℂ) * pair1 (lvec v) h)
        (pair1 (rvec v) u + (ε : ℂ) * pair1 (rvec v) h) := by
  have hl : ∀ g : ℝ → ℂ, Continuous g →
      pair1 g (lineF u h ε) = pair1 g u + (ε : ℂ) * pair1 g h := by
    intro g hg
    unfold lineF
    rw [pair1_add hg hu.1 (hh.1.const_mul (ε : ℂ)), pair1_smul]
  rw [Sv_eq_Sigma κ hv (h04_line hu hh ε).1, hl _ hv.smooth.continuous,
    hl _ (sp_lvec hv).smooth.continuous, hl _ (sp_rvec hv).smooth.continuous]

/-- `d_u S_v(u)[h]` along an `H¹` direction `h` is the genuine directional derivative, equal to
`dSigma` of the printed polynomial with data `(⟨v,h⟩, ⟨ℓ,h⟩, ⟨r_v,h⟩)`. -/
theorem deriv_Sv_line (κ : ℝ) {v : ℝ → ℂ} (hv : SmoothPeriodic L v) {u h : AddCircle L → ℂ}
    (hu : H04 L 1 u) (hh : H04 L 1 h) :
    deriv (fun ε : ℝ => Sv κ (lift hv) (lineF u h ε)) 0 =
      dSigma κ (E2 L v) (V4 L v) (pair1 v u) (pair1 (lvec v) u) (pair1 (rvec v) u)
        (pair1 v h) (pair1 (lvec v) h) (pair1 (rvec v) h) 0 0 := by
  have h1 := dSigma_eq_deriv κ (E2 L v) (V4 L v) (pair1 v u) (pair1 (lvec v) u)
    (pair1 (rvec v) u) (pair1 v h) (pair1 (lvec v) h) (pair1 (rvec v) h) 0 0
  simp only [mul_zero, add_zero] at h1
  rw [← h1]
  congr 1
  funext ε
  exact Sv_line κ hv hu hh ε

/-- For smooth `u`, the `u`-part `Tu` of the transport derivative is the genuine directional
derivative of `S_v` along the smooth vector `X(u)`: `d/dε|₀ S_v(u + εX(u))`. -/
theorem Tu_smooth (κ : ℝ) {v u : ℝ → ℂ} (hv : SmoothPeriodic L v) (hu : SmoothPeriodic L u) :
    Tu κ v (lift hu) (lift (sp_deriv hu)) =
      deriv (fun ε : ℝ => Sv κ (lift hv) (lineF (lift hu) (lift (sp_Xf κ hu)) ε)) 0 := by
  rw [deriv_Sv_line κ hv (h04_lift hu) (h04_lift (sp_Xf κ hu))]
  unfold Tu
  rw [Xpair_smooth κ hv hu, Xpair_smooth κ (sp_lvec hv) hu, Xpair_smooth κ (sp_rvec hv) hu,
    pair1_lift_eq (sp_Xf κ hu), pair1_lift_eq (sp_Xf κ hu), pair1_lift_eq (sp_Xf κ hu)]

end Faithful2

section Assembly

variable [Fact (0 < L)]

/-- **ENERGY-006 `lem:A1-relative`: every printed clause.**  For `L, κ > 0`:
1. (coercive, prefatory and structural clauses) for every smooth unit `v` and unit `u ∈ H¹`:
   `⟨v,w⟩ = 0`, `1 − |α|² = ‖w‖₂²`, `F_v(u) ≥ ‖w‖²_{H¹} + (κ/3)‖w‖₄⁴` (`eq:A1-coercive`),
   `S_v = E − F_v = a_{J₂} + a_{J₄}` with smooth selfadjoint rank-`≤3` data and gauge invariant
   homogeneous polynomials of degrees `2` and `4`, and `F_v(u)` unchanged by a constant phase of
   `u` or of `v`;
2. every `H¹` function has a weak derivative `u_x` (so clause 3 is not vacuous);
3. (`eq:A1-transport`, fixed time) `|(∂_t + d_u[X(u)]) S_v(u)| ≤ C F_v(u)` for every unit `u ∈ H¹`
   with weak derivative `u_x`, where `C = Cbound κ L M` depends only on `κ, L` and a common
   supremum bound `M` of `v, v', v'', v'''` ("finitely many supremum norms");
4. (`eq:A1-transport`, compact time set) for a smooth time-dependent family `v(t)` and a compact
   time set `K`, one constant `C` works for all `t ∈ K` and all unit `u ∈ H¹`. -/
theorem energy006_A1_relative_full {κ : ℝ} (hκ : 0 < κ) :
    (∀ {v : ℝ → ℂ} (hv : SmoothPeriodic L v), I1 (lift hv) = 1 →
      ∀ {u : AddCircle L → ℂ} (hu : H04 L 1 u), I1 u = 1 →
        (ip (lift hv) (wF (lift hv) u) = 0 ∧
          I1 (wF (lift hv) u) = 1 - ‖alpha (lift hv) u‖ ^ 2) ∧
        (h04Norm L 1 (wF (lift hv) u) ^ 2 + κ / 3 * quartic (wF (lift hv) u) ≤
          Fv κ (lift hv) u) ∧
        (((Sv κ (lift hv) u : ℝ) : ℂ) = (J2 L v).poly u + (J4 κ L v).poly u) ∧
        ((J2 L v).IsSmooth L ∧ (J4 κ L v).IsSmooth L) ∧
        ((J2 L v).Herm ∧ (J4 κ L v).Herm) ∧
        ((J2 L v).n = 3 ∧ (J4 κ L v).n = 3) ∧
        ((∀ (z : ℂ), ‖z‖ = 1 →
            (J2 L v).poly (fun x => z * u x) = (J2 L v).poly u ∧
            (J4 κ L v).poly (fun x => z * u x) = (J4 κ L v).poly u) ∧
          (∀ (z : ℂ),
            (J2 L v).poly (fun x => z * u x) = ((‖z‖ ^ 2 : ℝ) : ℂ) * (J2 L v).poly u ∧
            (J4 κ L v).poly (fun x => z * u x) = ((‖z‖ ^ 4 : ℝ) : ℂ) * (J4 κ L v).poly u)) ∧
        (∀ z : ℂ, ‖z‖ = 1 → Fv κ (lift hv) (fun x => z * u x) = Fv κ (lift hv) u) ∧
        (∀ z : ℂ, ‖z‖ = 1 → Fv κ (fun x => z * lift hv x) u = Fv κ (lift hv) u)) ∧
    (∀ {u : AddCircle L → ℂ}, H04 L 1 u → ∃ u', IsWD u u') ∧
    (∀ {M : ℝ} {v : ℝ → ℂ} (hv : SmoothPeriodic L v), JB v M → I1 (lift hv) = 1 →
      ∀ {u u' : AddCircle L → ℂ} (hu : H04 L 1 u), I1 u = 1 → IsWD u u' →
        |Ttot κ v u u'| ≤ Cbound κ L M * Fv κ (lift hv) u) ∧
    (∀ {V : ℝ → ℝ → ℂ} (hV : ContDiff ℝ ∞ (Function.uncurry V))
      (hper : ∀ t, Function.Periodic (V t) L)
      (hunit : ∀ t, I1 (lift (sp_slice hV hper t)) = 1) {K : Set ℝ}, IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ (u u' : AddCircle L → ℂ) (hu : H04 L 1 u), I1 u = 1 →
        IsWD u u' → |Ttot κ (V t) u u'| ≤ C * Fv κ (lift (sp_slice hV hper t)) u) := by
  refine ⟨fun {v} hv hvu {u} hu huu => ?_, fun {u} hu => exists_IsWD hu,
    fun {M v} hv hJ hvu {u u'} hu huu hd => Ttot_bound hκ hv hJ hvu hu huu hd,
    fun {V} hV hper hunit {K} hK => energy006_transport_uniform hκ hV hper hunit hK⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := energy006_A1_relative hκ hv hvu hu huu
  exact ⟨h1, h2, h3, h4, h5, h6, h7,
    fun z hz => Fv_phase_u κ (h04_lift hv) hu hz,
    fun z hz => Fv_phase_v κ (lift hv) u hz⟩

end Assembly

section TimeCalc

/-- The partial derivative in the time variable of a function of `(t, x)`. -/
def Dt (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun p => fderiv ℝ g p (1, 0)

theorem contDiff_Dt {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (Dt g) :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

theorem hasDerivAt_Dt {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (s x : ℝ) :
    HasDerivAt (fun r => g (r, x)) (Dt g (s, x)) s := by
  have h1 : HasFDerivAt g (fderiv ℝ g (s, x)) (s, x) :=
    (hg.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h2 : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact h1.comp_hasDerivAt s h2

theorem Dt_Dx_comm {g : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    Dt (Dx g) p = Dx (Dt g) p := by
  have hs := (hg.contDiffAt (x := p)).isSymmSndFDerivAt (n := ∞) (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ g) p :=
    ((hg.fderiv_right (m := ∞) le_rfl).differentiable (by simp)).differentiableAt
  unfold Dt Dx
  rw [fderiv_clm_apply h2 (differentiableAt_const _)]
  rw [fderiv_clm_apply h2 (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, map_zero]
  exact hs _ _

end TimeCalc

section DUI

variable [Fact (0 < L)]

/-- Differentiation under the integral sign in the time variable. -/
theorem hasDerivAt_integral_time {G G' : ℝ → ℝ → ℂ} (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2)
    (hG' : Continuous fun p : ℝ × ℝ => G' p.1 p.2)
    (hd : ∀ s x, HasDerivAt (fun r => G r x) (G' s x) s) {f : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 L) (t : ℝ) :
    HasDerivAt (fun s => ∫ x in (0 : ℝ)..L, G s x * f x) (∫ x in (0 : ℝ)..L, G' t x * f x) t := by
  have hL : 0 < L := Fact.out
  have hcmp : IsCompact (Metric.closedBall t 1 ×ˢ Set.Icc (0 : ℝ) L) :=
    (isCompact_closedBall t 1).prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcmp.exists_bound_of_continuousOn
    (f := fun p : ℝ × ℝ => G' p.1 p.2) hG'.continuousOn
  have hfm : AEStronglyMeasurable f (volume.restrict (Set.uIoc (0 : ℝ) L)) :=
    (intervalIntegrable_iff.mp hf).aestronglyMeasurable
  have hGc : ∀ s, Continuous (G s) := fun s => hG.comp (continuous_const.prodMk continuous_id)
  have hG'c : ∀ s, Continuous (G' s) := fun s => hG'.comp (continuous_const.prodMk continuous_id)
  have := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := L) (F := fun s x => G s x * f x) (F' := fun s x => G' s x * f x)
    (x₀ := t) (s := Metric.ball t 1) (bound := fun x => C * ‖f x‖) (Metric.ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall fun s => ((hGc s).aestronglyMeasurable).mul hfm)
    (hf.continuousOn_mul (hGc t).continuousOn)
    (((hG'c t).aestronglyMeasurable).mul hfm)
    (Filter.Eventually.of_forall fun x hx s hs => by
      have hx' : x ∈ Set.Icc (0 : ℝ) L := by
        rw [Set.uIoc_of_le hL.le] at hx; exact ⟨hx.1.le, hx.2⟩
      have h1 := hC (s, x) ⟨Metric.ball_subset_closedBall hs, hx'⟩
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    (hf.norm.const_mul C)
    (Filter.Eventually.of_forall fun x hx s hs => (hd s x).mul_const (f x))
  exact this.2

end DUI

section SigmaChain

theorem hasDerivAt_Sigma {κ : ℝ} {E Vv : ℝ → ℝ} {α a b : ℝ → ℂ} {E' V' : ℝ} {α' a' b' : ℂ} {t : ℝ}
    (hE : HasDerivAt E E' t) (hV : HasDerivAt Vv V' t) (hα : HasDerivAt α α' t)
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => Sigma κ (E s) (Vv s) (α s) (a s) (b s))
      (dSigma κ (E t) (Vv t) (α t) (a t) (b t) α' a' b' E' V') t := by
  have hn : HasDerivAt (fun s => ‖α s‖ ^ 2) (2 * (conj (α t) * α').re) t := by
    refine hα.norm_sq.congr_deriv ?_
    rw [Complex.inner, mul_comm α' (conj (α t))]
  have hre : ∀ {x x' : ℝ → ℂ} {y y' : ℂ}, HasDerivAt x y t → HasDerivAt x' y' t →
      HasDerivAt (fun s => (conj (x s) * x' s).re) (conj y * x' t + conj (x t) * y').re t := by
    intro x x' y y' hx hx'
    have h := (hx.star.mul hx')
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have h1 := hre hα ha
  have h2 := hre hα hb
  have hS := ((((h1.const_mul 2).sub (hn.mul hE)).add ((hn.mul h2).const_mul (4 * κ)))).sub
    (((hn.pow 2).mul hV).const_mul (3 * κ))
  unfold Sigma dSigma
  have e : (fun s => 2 * (conj (α s) * a s).re - ‖α s‖ ^ 2 * E s +
      4 * κ * ‖α s‖ ^ 2 * (conj (α s) * b s).re - 3 * κ * ‖α s‖ ^ 4 * Vv s) =
      fun s => 2 * (conj (α s) * a s).re - ‖α s‖ ^ 2 * E s +
      4 * κ * (‖α s‖ ^ 2 * (conj (α s) * b s).re) - 3 * κ * ((‖α s‖ ^ 2) ^ 2 * Vv s) := by
    funext s; ring
  rw [e]
  refine hS.congr_deriv ?_
  simp only [Nat.cast_ofNat, Pi.pow_apply]
  ring

end SigmaChain

section Bridge

variable [Fact (0 < L)] {κ : ℝ} {V : ℝ → ℝ → ℂ}

section Facts

variable (hV : ContDiff ℝ ∞ (Function.uncurry V))
  (hsol : ∀ t x, deriv (fun s => V s x) t = Xf κ (V t) x)
include hV hsol

theorem Dt_eq (t x : ℝ) : Dt (Function.uncurry V) (t, x) = Xf κ (V t) x := by
  rw [← hsol t x]
  exact ((hasDerivAt_Dt hV t x).deriv).symm

theorem deriv1_slice (t y : ℝ) : deriv (V t) y = Dx (Function.uncurry V) (t, y) :=
  (hasDerivAt_Dx hV t y).deriv

theorem deriv2_slice (t y : ℝ) :
    deriv (deriv (V t)) y = Dx (Dx (Function.uncurry V)) (t, y) := by
  have : deriv (V t) = fun y => Dx (Function.uncurry V) (t, y) := funext fun y => deriv1_slice hV hsol t y
  rw [this]
  exact (hasDerivAt_Dx (contDiff_Dx hV) t y).deriv

theorem Dx_Dt_val (t y : ℝ) :
    Dx (Dt (Function.uncurry V)) (t, y) = deriv (Xf κ (V t)) y := by
  have : (fun y => Dt (Function.uncurry V) (t, y)) = Xf κ (V t) :=
    funext fun y => Dt_eq hV hsol t y
  rw [← this]
  exact ((hasDerivAt_Dx (contDiff_Dt hV) t y).deriv).symm

theorem Dx_Dx_Dt_val (t y : ℝ) :
    Dx (Dx (Dt (Function.uncurry V))) (t, y) = deriv (deriv (Xf κ (V t))) y := by
  have : (fun y => Dx (Dt (Function.uncurry V)) (t, y)) = deriv (Xf κ (V t)) :=
    funext fun y => Dx_Dt_val hV hsol t y
  rw [← this]
  exact ((hasDerivAt_Dx (contDiff_Dx (contDiff_Dt hV)) t y).deriv).symm

theorem Dt_Dx_val (t y : ℝ) :
    Dt (Dx (Function.uncurry V)) (t, y) = deriv (Xf κ (V t)) y := by
  rw [Dt_Dx_comm hV, Dx_Dt_val hV hsol]

theorem Dt_Dx_Dx_val (t y : ℝ) :
    Dt (Dx (Dx (Function.uncurry V))) (t, y) = deriv (deriv (Xf κ (V t))) y := by
  rw [Dt_Dx_comm (contDiff_Dx hV)]
  have : Dt (Dx (Function.uncurry V)) = Dx (Dt (Function.uncurry V)) :=
    funext fun p => Dt_Dx_comm hV p
  rw [this, Dx_Dx_Dt_val hV hsol]

end Facts

section Pieces

variable [Fact (0 < L)] {κ : ℝ} {V : ℝ → ℝ → ℂ}
variable (hV : ContDiff ℝ ∞ (Function.uncurry V))
  (hsol : ∀ t x, deriv (fun s => V s x) t = Xf κ (V t) x)
include hV hsol

theorem hasDerivAt_alpha {u : AddCircle L → ℂ} (hu : MemLp u 2 (volume : Measure (AddCircle L)))
    (t : ℝ) : HasDerivAt (fun s => pair1 (V s) u) (pair1 (Xf κ (V t)) u) t := by
  have hf : IntervalIntegrable (fun x : ℝ => u (x : AddCircle L)) volume 0 L :=
    intervalIntegrable_coe (integrable_of_h04 hu)
  have cV : Continuous (Function.uncurry V) := hV.continuous
  have cDt : Continuous (Dt (Function.uncurry V)) := (contDiff_Dt hV).continuous
  have h := hasDerivAt_integral_time (G := fun s x => conj (V s x))
    (G' := fun s x => conj (Dt (Function.uncurry V) (s, x)))
    (Complex.continuous_conj.comp cV)
    (Complex.continuous_conj.comp (cDt.comp (continuous_fst.prodMk continuous_snd)))
    (fun s x => (hasDerivAt_Dt hV s x).star) hf t
  refine h.congr_deriv ?_
  unfold pair1
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Dt_eq hV hsol]

theorem hasDerivAt_lvec {u : AddCircle L → ℂ} (hu : MemLp u 2 (volume : Measure (AddCircle L)))
    (t : ℝ) :
    HasDerivAt (fun s => pair1 (lvec (V s)) u) (pair1 (lvec (Xf κ (V t))) u) t := by
  have hf : IntervalIntegrable (fun x : ℝ => u (x : AddCircle L)) volume 0 L :=
    intervalIntegrable_coe (integrable_of_h04 hu)
  have cV : Continuous (Function.uncurry V) := hV.continuous
  have c2 : Continuous (Dx (Dx (Function.uncurry V))) := (contDiff_Dx (contDiff_Dx hV)).continuous
  have cDt : Continuous (Dt (Function.uncurry V)) := (contDiff_Dt hV).continuous
  have cDt2 : Continuous (Dt (Dx (Dx (Function.uncurry V)))) :=
    (contDiff_Dt (contDiff_Dx (contDiff_Dx hV))).continuous
  have h := hasDerivAt_integral_time
    (G := fun s x => conj (Function.uncurry V (s, x) - Dx (Dx (Function.uncurry V)) (s, x)))
    (G' := fun s x => conj (Dt (Function.uncurry V) (s, x) -
      Dt (Dx (Dx (Function.uncurry V))) (s, x)))
    (Complex.continuous_conj.comp (cV.sub (c2.comp (continuous_fst.prodMk continuous_snd))))
    (Complex.continuous_conj.comp ((cDt.comp (continuous_fst.prodMk continuous_snd)).sub
      (cDt2.comp (continuous_fst.prodMk continuous_snd))))
    (fun s x => ((hasDerivAt_Dt hV s x).sub (hasDerivAt_Dt (contDiff_Dx (contDiff_Dx hV)) s x)).star)
    hf t
  have el : ∀ s, pair1 (lvec (V s)) u = ∫ x in (0 : ℝ)..L,
      conj (Function.uncurry V (s, x) - Dx (Dx (Function.uncurry V)) (s, x)) * u (x : AddCircle L) := by
    intro s
    unfold pair1
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [lvec, deriv2_slice hV hsol s x, Function.uncurry_apply_pair]
  have e : (fun s => pair1 (lvec (V s)) u) = fun s => ∫ x in (0 : ℝ)..L,
      conj (Function.uncurry V (s, x) - Dx (Dx (Function.uncurry V)) (s, x)) * u (x : AddCircle L) :=
    funext el
  rw [e]
  refine h.congr_deriv ?_
  unfold pair1
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Dt_eq hV hsol, Dt_Dx_Dx_val hV hsol, lvec]

end Pieces

end Bridge

section Pieces2

variable [Fact (0 < L)] {κ : ℝ} {V : ℝ → ℝ → ℂ}
variable (hV : ContDiff ℝ ∞ (Function.uncurry V))
  (hsol : ∀ t x, deriv (fun s => V s x) t = Xf κ (V t) x)
include hV hsol

theorem hasDerivAt_rvec {u : AddCircle L → ℂ} (hu : MemLp u 2 (volume : Measure (AddCircle L)))
    (t : ℝ) :
    HasDerivAt (fun s => pair1 (rvec (V s)) u)
      (pair1 (Drv (V t) (Xf κ (V t))) u) t := by
  have hf : IntervalIntegrable (fun x : ℝ => u (x : AddCircle L)) volume 0 L :=
    intervalIntegrable_coe (integrable_of_h04 hu)
  have cV : Continuous (Function.uncurry V) := hV.continuous
  have cDt : Continuous (Dt (Function.uncurry V)) := (contDiff_Dt hV).continuous
  have hd : ∀ s x, HasDerivAt (fun r => conj (((‖V r x‖ ^ 2 : ℝ) : ℂ) * V r x))
      (conj (((2 * (conj (V s x) * Dt (Function.uncurry V) (s, x)).re : ℝ) : ℂ) * V s x +
        ((‖V s x‖ ^ 2 : ℝ) : ℂ) * Dt (Function.uncurry V) (s, x))) s := by
    intro s x
    have h0 := hasDerivAt_Dt hV s x
    have h1 : HasDerivAt (fun r => ((‖V r x‖ ^ 2 : ℝ) : ℂ))
        (((2 * (conj (V s x) * Dt (Function.uncurry V) (s, x)).re : ℝ) : ℂ)) s := by
      have := (h0.norm_sq).ofReal_comp
      refine this.congr_deriv ?_
      have m : Dt (Function.uncurry V) (s, x) * conj (V s x) =
          conj (V s x) * Dt (Function.uncurry V) (s, x) := mul_comm _ _
      simp only [Complex.inner, Function.uncurry_apply_pair, m]
    exact (h1.mul h0).star
  have h := hasDerivAt_integral_time
    (G := fun s x => conj (((‖V s x‖ ^ 2 : ℝ) : ℂ) * V s x))
    (G' := fun s x => conj (((2 * (conj (V s x) * Dt (Function.uncurry V) (s, x)).re : ℝ) : ℂ) *
      V s x + ((‖V s x‖ ^ 2 : ℝ) : ℂ) * Dt (Function.uncurry V) (s, x)))
    (by
      have : Continuous fun p : ℝ × ℝ => conj (((‖V p.1 p.2‖ ^ 2 : ℝ) : ℂ) * V p.1 p.2) := by
        have c : Continuous fun p : ℝ × ℝ => V p.1 p.2 := cV
        fun_prop
      exact this)
    (by
      have c : Continuous fun p : ℝ × ℝ => V p.1 p.2 := cV
      have c' : Continuous fun p : ℝ × ℝ => Dt (Function.uncurry V) (p.1, p.2) :=
        cDt.comp (continuous_fst.prodMk continuous_snd)
      fun_prop)
    hd hf t
  have e : (fun s => pair1 (rvec (V s)) u) = fun s => ∫ x in (0 : ℝ)..L,
      conj (((‖V s x‖ ^ 2 : ℝ) : ℂ) * V s x) * u (x : AddCircle L) := by
    funext s; unfold pair1 rvec; rfl
  rw [e]
  refine h.congr_deriv ?_
  unfold pair1
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [Dt_eq hV hsol, Drv]

theorem hasDerivAt_E2 (t : ℝ) :
    HasDerivAt (fun s => E2 L (V s)) (E2dot L (V t) (Xf κ (V t))) t := by
  have hf : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume 0 L := intervalIntegrable_const
  have cV : Continuous (Function.uncurry V) := hV.continuous
  have cDx : Continuous (Dx (Function.uncurry V)) := (contDiff_Dx hV).continuous
  have cDt : Continuous (Dt (Function.uncurry V)) := (contDiff_Dt hV).continuous
  have cDtx : Continuous (Dt (Dx (Function.uncurry V))) :=
    (contDiff_Dt (contDiff_Dx hV)).continuous
  have hd : ∀ s x, HasDerivAt (fun r => ((‖Dx (Function.uncurry V) (r, x)‖ ^ 2 + ‖V r x‖ ^ 2 : ℝ) : ℂ))
      (((2 * (conj (Dx (Function.uncurry V) (s, x)) * Dt (Dx (Function.uncurry V)) (s, x)).re +
        2 * (conj (V s x) * Dt (Function.uncurry V) (s, x)).re : ℝ) : ℂ)) s := by
    intro s x
    have h1 := (hasDerivAt_Dt (contDiff_Dx hV) s x).norm_sq
    have h2 := (hasDerivAt_Dt hV s x).norm_sq
    have := (h1.add h2).ofReal_comp
    refine this.congr_deriv ?_
    have m1 : Dt (Dx (Function.uncurry V)) (s, x) * conj (Dx (Function.uncurry V) (s, x)) =
        conj (Dx (Function.uncurry V) (s, x)) * Dt (Dx (Function.uncurry V)) (s, x) := mul_comm _ _
    have m2 : Dt (Function.uncurry V) (s, x) * conj (V s x) =
        conj (V s x) * Dt (Function.uncurry V) (s, x) := mul_comm _ _
    simp only [Complex.inner, Function.uncurry_apply_pair, m1, m2]
  have h := hasDerivAt_integral_time
    (G := fun s x => ((‖Dx (Function.uncurry V) (s, x)‖ ^ 2 + ‖V s x‖ ^ 2 : ℝ) : ℂ))
    (G' := fun s x => ((2 * (conj (Dx (Function.uncurry V) (s, x)) *
        Dt (Dx (Function.uncurry V)) (s, x)).re +
        2 * (conj (V s x) * Dt (Function.uncurry V) (s, x)).re : ℝ) : ℂ))
    (by
      have c : Continuous fun p : ℝ × ℝ => V p.1 p.2 := cV
      have c' : Continuous fun p : ℝ × ℝ => Dx (Function.uncurry V) (p.1, p.2) :=
        cDx.comp (continuous_fst.prodMk continuous_snd)
      fun_prop)
    (by
      have c : Continuous fun p : ℝ × ℝ => V p.1 p.2 := cV
      have c' : Continuous fun p : ℝ × ℝ => Dx (Function.uncurry V) (p.1, p.2) :=
        cDx.comp (continuous_fst.prodMk continuous_snd)
      have c'' : Continuous fun p : ℝ × ℝ => Dt (Function.uncurry V) (p.1, p.2) :=
        cDt.comp (continuous_fst.prodMk continuous_snd)
      have c''' : Continuous fun p : ℝ × ℝ => Dt (Dx (Function.uncurry V)) (p.1, p.2) :=
        cDtx.comp (continuous_fst.prodMk continuous_snd)
      fun_prop)
    hd hf t
  have e : ∀ s, ((E2 L (V s) : ℝ) : ℂ) = ∫ x in (0 : ℝ)..L,
      ((‖Dx (Function.uncurry V) (s, x)‖ ^ 2 + ‖V s x‖ ^ 2 : ℝ) : ℂ) * (fun _ : ℝ => (1 : ℂ)) x := by
    intro s
    unfold E2
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [mul_one, deriv1_slice hV hsol]
  have hc := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hfun : (fun s => E2 L (V s)) = ⇑Complex.reCLM ∘ fun s => ∫ x in (0 : ℝ)..L,
      ((‖Dx (Function.uncurry V) (s, x)‖ ^ 2 + ‖V s x‖ ^ 2 : ℝ) : ℂ) * (fun _ : ℝ => (1 : ℂ)) x := by
    funext s
    simp only [Function.comp, ← e s, Complex.reCLM_apply, Complex.ofReal_re]
  rw [hfun]
  refine hc.congr_deriv ?_
  have hval : (∫ x in (0 : ℝ)..L, ((2 * (conj (Dx (Function.uncurry V) (t, x)) *
        Dt (Dx (Function.uncurry V)) (t, x)).re +
        2 * (conj (V t x) * Dt (Function.uncurry V) (t, x)).re : ℝ) : ℂ) *
        (fun _ : ℝ => (1 : ℂ)) x) = ((E2dot L (V t) (Xf κ (V t)) : ℝ) : ℂ) := by
    unfold E2dot
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [mul_one, Dt_Dx_val hV hsol t x, Dt_eq hV hsol t x, ← deriv1_slice hV hsol t x]
  simp only [Complex.reCLM_apply]
  rw [hval]
  simp

end Pieces2

section Pieces3

variable [Fact (0 < L)] {κ : ℝ} {V : ℝ → ℝ → ℂ}
variable (hV : ContDiff ℝ ∞ (Function.uncurry V))
  (hsol : ∀ t x, deriv (fun s => V s x) t = Xf κ (V t) x)
include hV hsol

theorem hasDerivAt_V4 (t : ℝ) :
    HasDerivAt (fun s => V4 L (V s)) (V4dot L (V t) (Xf κ (V t))) t := by
  have hf : IntervalIntegrable (fun _ : ℝ => (1 : ℂ)) volume 0 L := intervalIntegrable_const
  have cV : Continuous (Function.uncurry V) := hV.continuous
  have cDt : Continuous (Dt (Function.uncurry V)) := (contDiff_Dt hV).continuous
  have hd : ∀ s x, HasDerivAt (fun r => (((‖V r x‖ ^ 2) ^ 2 : ℝ) : ℂ))
      (((2 * ‖V s x‖ ^ 2 * (2 * (conj (V s x) * Dt (Function.uncurry V) (s, x)).re) : ℝ) : ℂ)) s := by
    intro s x
    have h1 := ((hasDerivAt_Dt hV s x).norm_sq).pow 2
    have := h1.ofReal_comp
    refine this.congr_deriv ?_
    have m : Dt (Function.uncurry V) (s, x) * conj (V s x) =
        conj (V s x) * Dt (Function.uncurry V) (s, x) := mul_comm _ _
    simp only [Complex.inner, Function.uncurry_apply_pair, m]
    push_cast
    ring_nf
  have h := hasDerivAt_integral_time
    (G := fun s x => (((‖V s x‖ ^ 2) ^ 2 : ℝ) : ℂ))
    (G' := fun s x => ((2 * ‖V s x‖ ^ 2 * (2 * (conj (V s x) *
      Dt (Function.uncurry V) (s, x)).re) : ℝ) : ℂ))
    (by
      have c : Continuous fun p : ℝ × ℝ => V p.1 p.2 := cV
      fun_prop)
    (by
      have c : Continuous fun p : ℝ × ℝ => V p.1 p.2 := cV
      have c'' : Continuous fun p : ℝ × ℝ => Dt (Function.uncurry V) (p.1, p.2) :=
        cDt.comp (continuous_fst.prodMk continuous_snd)
      fun_prop)
    hd hf t
  have e : ∀ s, ((V4 L (V s) : ℝ) : ℂ) = ∫ x in (0 : ℝ)..L,
      (((‖V s x‖ ^ 2) ^ 2 : ℝ) : ℂ) * (fun _ : ℝ => (1 : ℂ)) x := by
    intro s
    unfold V4
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [mul_one]
    push_cast
    ring
  have hc := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h
  have hfun : (fun s => V4 L (V s)) = ⇑Complex.reCLM ∘ fun s => ∫ x in (0 : ℝ)..L,
      (((‖V s x‖ ^ 2) ^ 2 : ℝ) : ℂ) * (fun _ : ℝ => (1 : ℂ)) x := by
    funext s
    simp only [Function.comp, ← e s, Complex.reCLM_apply, Complex.ofReal_re]
  rw [hfun]
  refine hc.congr_deriv ?_
  have hval : (∫ x in (0 : ℝ)..L, ((2 * ‖V t x‖ ^ 2 * (2 * (conj (V t x) *
        Dt (Function.uncurry V) (t, x)).re) : ℝ) : ℂ) * (fun _ : ℝ => (1 : ℂ)) x) =
        ((V4dot L (V t) (Xf κ (V t)) : ℝ) : ℂ) := by
    unfold V4dot
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [mul_one, Dt_eq hV hsol t x]
    push_cast
    ring
  simp only [Complex.reCLM_apply]
  rw [hval]
  simp

/-- **Bridge to the genuine time derivative.**  For a smooth periodic classical solution `V` of
`∂_t V = X(V)` and `u ∈ H¹`, the genuine time derivative of `S_{V(t)}(u)` is the formal
`Tt` (the printed assignment `v_t = X(v)` in `eq:A1-S`). -/
theorem hasDerivAt_Sv_time (hper : ∀ t, Function.Periodic (V t) L) {u : AddCircle L → ℂ}
    (hu : H04 L 1 u) (t : ℝ) :
    HasDerivAt (fun s => Sv κ (lift (sp_slice hV hper s)) u) (Tt κ (V t) u) t := by
  have e : (fun s => Sv κ (lift (sp_slice hV hper s)) u) = fun s =>
      Sigma κ (E2 L (V s)) (V4 L (V s)) (pair1 (V s) u) (pair1 (lvec (V s)) u)
        (pair1 (rvec (V s)) u) :=
    funext fun s => Sv_eq_Sigma κ (sp_slice hV hper s) hu
  rw [e]
  exact hasDerivAt_Sigma (hasDerivAt_E2 hV hsol t) (hasDerivAt_V4 hV hsol t)
    (hasDerivAt_alpha hV hsol hu.1 t) (hasDerivAt_lvec hV hsol hu.1 t)
    (hasDerivAt_rvec hV hsol hu.1 t)

end Pieces3

section Complete

variable [Fact (0 < L)]

/-- **`eq:A1-transport` for a classical smooth solution, with the genuine time derivative.**
`V` is smooth, `L`-periodic in `x`, solves `∂_t V = X(V)` and has unit mass; `K` is a compact time
set.  There is one constant `C` (depending on `V, L, κ, K` only through finitely many supremum
norms of `V` and its first three `x`-derivatives on `K`) such that for every unit `u ∈ H¹` with
weak derivative `u_x` and every `t ∈ K`,
`|∂_t S_{V(t)}(u) + d_u[X(u)] S_{V(t)}(u)| ≤ C F_{V(t)}(u)`. -/
theorem energy006_transport_solution {κ : ℝ} (hκ : 0 < κ) {V : ℝ → ℝ → ℂ}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hper : ∀ t, Function.Periodic (V t) L)
    (hsol : ∀ t x, deriv (fun s => V s x) t = Xf κ (V t) x)
    (hunit : ∀ t, I1 (lift (sp_slice hV hper t)) = 1) {K : Set ℝ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ (u u' : AddCircle L → ℂ) (hu : H04 L 1 u), I1 u = 1 →
      IsWD u u' →
      |deriv (fun s => Sv κ (lift (sp_slice hV hper s)) u) t + Tu κ (V t) u u'| ≤
        C * Fv κ (lift (sp_slice hV hper t)) u := by
  obtain ⟨C, hC0, hC⟩ := energy006_transport_uniform hκ hV hper hunit hK
  refine ⟨C, hC0, fun t ht u u' hu hu1 hd => ?_⟩
  have h := (hasDerivAt_Sv_time hV hsol hper hu t).deriv
  rw [h]
  exact hC t ht u u' hu hu1 hd

/-- **ENERGY-006 `lem:A1-relative`: every printed clause, with a classical solution `v(t)`.** -/
theorem energy006_A1_relative_complete {κ : ℝ} (hκ : 0 < κ) :
    (∀ {v : ℝ → ℂ} (hv : SmoothPeriodic L v), I1 (lift hv) = 1 →
      ∀ {u : AddCircle L → ℂ} (hu : H04 L 1 u), I1 u = 1 →
        (ip (lift hv) (wF (lift hv) u) = 0 ∧
          I1 (wF (lift hv) u) = 1 - ‖alpha (lift hv) u‖ ^ 2) ∧
        (h04Norm L 1 (wF (lift hv) u) ^ 2 + κ / 3 * quartic (wF (lift hv) u) ≤
          Fv κ (lift hv) u) ∧
        (((Sv κ (lift hv) u : ℝ) : ℂ) = (J2 L v).poly u + (J4 κ L v).poly u) ∧
        ((J2 L v).IsSmooth L ∧ (J4 κ L v).IsSmooth L) ∧
        ((J2 L v).Herm ∧ (J4 κ L v).Herm) ∧
        ((J2 L v).n = 3 ∧ (J4 κ L v).n = 3) ∧
        ((∀ (z : ℂ), ‖z‖ = 1 →
            (J2 L v).poly (fun x => z * u x) = (J2 L v).poly u ∧
            (J4 κ L v).poly (fun x => z * u x) = (J4 κ L v).poly u) ∧
          (∀ (z : ℂ),
            (J2 L v).poly (fun x => z * u x) = ((‖z‖ ^ 2 : ℝ) : ℂ) * (J2 L v).poly u ∧
            (J4 κ L v).poly (fun x => z * u x) = ((‖z‖ ^ 4 : ℝ) : ℂ) * (J4 κ L v).poly u)) ∧
        (∀ z : ℂ, ‖z‖ = 1 → Fv κ (lift hv) (fun x => z * u x) = Fv κ (lift hv) u) ∧
        (∀ z : ℂ, ‖z‖ = 1 → Fv κ (fun x => z * lift hv x) u = Fv κ (lift hv) u)) ∧
    (∀ {u : AddCircle L → ℂ}, H04 L 1 u → ∃ u', IsWD u u') ∧
    (∀ {M : ℝ} {v : ℝ → ℂ} (hv : SmoothPeriodic L v), JB v M → I1 (lift hv) = 1 →
      ∀ {u u' : AddCircle L → ℂ} (hu : H04 L 1 u), I1 u = 1 → IsWD u u' →
        |Ttot κ v u u'| ≤ Cbound κ L M * Fv κ (lift hv) u) ∧
    (∀ {V : ℝ → ℝ → ℂ} (hV : ContDiff ℝ ∞ (Function.uncurry V))
      (hper : ∀ t, Function.Periodic (V t) L)
      (hsol : ∀ t x, deriv (fun s => V s x) t = Xf κ (V t) x)
      (hunit : ∀ t, I1 (lift (sp_slice hV hper t)) = 1) {K : Set ℝ}, IsCompact K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ K, ∀ (u u' : AddCircle L → ℂ) (hu : H04 L 1 u), I1 u = 1 →
        IsWD u u' →
        |deriv (fun s => Sv κ (lift (sp_slice hV hper s)) u) t + Tu κ (V t) u u'| ≤
          C * Fv κ (lift (sp_slice hV hper t)) u) := by
  obtain ⟨h1, h2, h3, -⟩ := energy006_A1_relative_full (L := L) hκ
  exact ⟨h1, h2, h3, fun {V} hV hper hsol hunit {K} hK =>
    energy006_transport_solution hκ hV hper hsol hunit hK⟩

end Complete

end QuantumNLS.RelativeEnergy

#print axioms QuantumNLS.RelativeEnergy.energy006_A1_relative_complete
#print axioms QuantumNLS.RelativeEnergy.energy006_A1_relative_full
#print axioms QuantumNLS.RelativeEnergy.energy006_transport_solution
#print axioms QuantumNLS.RelativeEnergy.energy006_transport_uniform
#print axioms QuantumNLS.RelativeEnergy.Ttot_bound
#print axioms QuantumNLS.RelativeEnergy.Ttot_identity
#print axioms QuantumNLS.RelativeEnergy.Ttot_formula
#print axioms QuantumNLS.RelativeEnergy.alpha_dot_eq
#print axioms QuantumNLS.RelativeEnergy.alpha_dot_bound
#print axioms QuantumNLS.RelativeEnergy.norm_RemC_le
#print axioms QuantumNLS.RelativeEnergy.kerK_eq_zero
#print axioms QuantumNLS.RelativeEnergy.cons_E
#print axioms QuantumNLS.RelativeEnergy.mass_v3
#print axioms QuantumNLS.RelativeEnergy.mass_N
#print axioms QuantumNLS.RelativeEnergy.C1_identity
#print axioms QuantumNLS.RelativeEnergy.LamId
#print axioms QuantumNLS.RelativeEnergy.Ia_eq
#print axioms QuantumNLS.RelativeEnergy.LinC_eq
#print axioms QuantumNLS.RelativeEnergy.Xpair_decomp
#print axioms QuantumNLS.RelativeEnergy.Xpair_smooth
#print axioms QuantumNLS.RelativeEnergy.Xpair_comb
#print axioms QuantumNLS.RelativeEnergy.Xpair_gE
#print axioms QuantumNLS.RelativeEnergy.pairC_decomp
#print axioms QuantumNLS.RelativeEnergy.exists_IsWD
#print axioms QuantumNLS.RelativeEnergy.kinetic_eq_of_IsWD
#print axioms QuantumNLS.RelativeEnergy.isWD_iff_hasWeakDeriv
#print axioms QuantumNLS.RelativeEnergy.IsWD.ibp
#print axioms QuantumNLS.RelativeEnergy.exists_JB_uniform
#print axioms QuantumNLS.RelativeEnergy.dSigma_eq_deriv
#print axioms QuantumNLS.RelativeEnergy.deriv_Sv_line
#print axioms QuantumNLS.RelativeEnergy.Tu_smooth
#print axioms QuantumNLS.RelativeEnergy.Sv_eq_Sigma
#print axioms QuantumNLS.RelativeEnergy.Sv_line
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_Sv_time
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_integral_time
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_Sigma
#print axioms QuantumNLS.RelativeEnergy.dSigma_star
#print axioms QuantumNLS.RelativeEnergy.master_alg
#print axioms QuantumNLS.RelativeEnergy.Aw_sq_le
#print axioms QuantumNLS.RelativeEnergy.norm_pair1_le
#print axioms QuantumNLS.RelativeEnergy.Fp_le_Fv
#print axioms QuantumNLS.RelativeEnergy.norm_alpha_le
#print axioms QuantumNLS.RelativeEnergy.Dt_Dx_comm
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_alpha
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_lvec
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_rvec
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_E2
#print axioms QuantumNLS.RelativeEnergy.hasDerivAt_V4
#print axioms QuantumNLS.RelativeEnergy.E2dot_rel
#print axioms QuantumNLS.RelativeEnergy.V4dot_rel
#print axioms QuantumNLS.RelativeEnergy.combine_bound
#print axioms QuantumNLS.RelativeEnergy.norm_k1_cN_le
#print axioms QuantumNLS.RelativeEnergy.norm_k1_cv_le
#print axioms QuantumNLS.RelativeEnergy.k1_sub
#print axioms QuantumNLS.RelativeEnergy.Xf_cmul
#print axioms QuantumNLS.RelativeEnergy.xi_sub
