import QuantumNLS.WeakDerivatives

/-!
# DEF-022: the classical charges `I_j^{(κ)}(u)` of a smooth profile

Source (report pin 3b1f701a43a387dd5a779bad3ceb2c56c3c2a53f, `chapters/definitions.tex:135`,
prerequisite DEF-015): "For smooth `u`, set `v_1 = u` and
`v_{j+1} = −i ∂_x v_j + κ ū ∑_{a=1}^{j−1} v_a v_{j−a}`.  The charge of order `j` is
`I_j^{(κ)}(u) = ∫ ū v_j`.  In particular `I_1 = ‖u‖₂²`, `I_2 = ∫ ū (−i ∂_x u)` and
`I_3 = ∫ (|∂_x u|² + κ |u|⁴)`."

A smooth profile on `𝕋_L = ℝ/Lℤ` is an `L`-periodic `C^∞` function `ℝ → ℂ` (the lift to `ℝ`, as in
`WeakDerivatives`), integrals are over one period `[0, L]` (Lebesgue measure of mass `L`, DEF-001).

What is proved: the recursion unfolds as printed; every `v_j` is `C^∞` and `L`-periodic (the
regularity needed for `∂_x v_j` and the integrals); the three displayed particular cases `I_1`
(mass), `I_2` (momentum), `I_3` (energy, with the integration by parts on the circle proved, not
assumed).  No dynamics, no conservation law, no Poisson-bracket statement is assumed or proved.
-/

open scoped ComplexConjugate ContDiff
open MeasureTheory

noncomputable section

namespace QuantumNLS.ClassicalCharges

/-- A smooth profile on the torus `𝕋_L`, lifted to `ℝ`: `C^∞` and `L`-periodic. -/
structure SmoothPeriodic (L : ℝ) (u : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ u
  periodic : Function.Periodic u L

/-- The recursion of DEF-022: `v 1 = u`, `v (j+1) = −i ∂ v_j + κ ū ∑_{a=1}^{j−1} v_a v_{j−a}`
(`v 0` is an unused placeholder). -/
def vseq (κ : ℝ) (u : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 0
  | 1 => u
  | (j + 2) => fun x =>
      -Complex.I * deriv (vseq κ u (j + 1)) x + (κ : ℂ) * conj (u x) *
        ∑ a ∈ (Finset.Icc 1 j).attach, vseq κ u a.1 x * vseq κ u (j + 1 - a.1) x
  decreasing_by
    all_goals
      first
        | omega
        | (have h := Finset.mem_Icc.mp a.2
           simp only [Nat.succ_eq_add_one]
           omega)

/-- The charge of order `j`: `I_j^{(κ)}(u) = ∫_0^L ū v_j`. -/
def charge (L κ : ℝ) (u : ℝ → ℂ) (j : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..L, conj (u x) * vseq κ u j x

lemma vseq_one (κ : ℝ) (u : ℝ → ℂ) : vseq κ u 1 = u := by rw [vseq]

lemma vseq_succ (κ : ℝ) (u : ℝ → ℂ) (j : ℕ) :
    vseq κ u (j + 2) = fun x =>
      -Complex.I * deriv (vseq κ u (j + 1)) x + (κ : ℂ) * conj (u x) *
        ∑ a ∈ Finset.Icc 1 j, vseq κ u a x * vseq κ u (j + 1 - a) x := by
  rw [vseq]
  funext x
  simp only [Finset.sum_attach (Finset.Icc 1 j) (fun a => vseq κ u a x * vseq κ u (j + 1 - a) x)]

open QuantumNLS.WeakDerivatives

variable {L : ℝ}

/-- **Required regularity**: for a smooth periodic profile every `v_j` is again smooth and
`L`-periodic (so each `∂_x v_j` exists, is smooth and periodic, and every integrand is continuous). -/
theorem vseq_regular (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (j : ℕ) :
    ContDiff ℝ ∞ (vseq κ u j) ∧ Function.Periodic (vseq κ u j) L := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ =>
      simp only [vseq]
      exact ⟨contDiff_const, fun _ => rfl⟩
    | 1, _ =>
      rw [vseq_one]; exact ⟨hu.smooth, hu.periodic⟩
    | k + 2, ih =>
      rw [vseq_succ]
      obtain ⟨hs1, hp1⟩ := ih (k + 1) (by omega)
      have hsum_s : ContDiff ℝ ∞ (fun x => ∑ a ∈ Finset.Icc 1 k,
          vseq κ u a x * vseq κ u (k + 1 - a) x) := by
        refine ContDiff.sum (fun a ha => ?_)
        have ha' := Finset.mem_Icc.mp ha
        exact (ih a (by omega)).1.mul (ih (k + 1 - a) (by omega)).1
      refine ⟨?_, ?_⟩
      · exact (contDiff_const.mul (contDiff_infty_iff_deriv.mp hs1).2).add
          ((contDiff_const.mul (Complex.conjCLE.contDiff.comp hu.smooth)).mul hsum_s)
      · intro x
        have hd := periodic_deriv hp1 x
        have hs : ∑ a ∈ Finset.Icc 1 k, vseq κ u a (x + L) * vseq κ u (k + 1 - a) (x + L)
            = ∑ a ∈ Finset.Icc 1 k, vseq κ u a x * vseq κ u (k + 1 - a) x := by
          refine Finset.sum_congr rfl (fun a ha => ?_)
          have ha' := Finset.mem_Icc.mp ha
          rw [(ih a (by omega)).2 x, (ih (k + 1 - a) (by omega)).2 x]
        simp only [hd, hu.periodic x, hs]

/-- Each charge integrand is continuous, hence the charge is a well-defined interval integral. -/
theorem charge_integrand_continuous (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) (j : ℕ) :
    Continuous (fun x => conj (u x) * vseq κ u j x) :=
  (Complex.continuous_conj.comp hu.smooth.continuous).mul (vseq_regular κ hu j).1.continuous

/-! ### The displayed particular cases -/

lemma vseq_two (κ : ℝ) (u : ℝ → ℂ) : vseq κ u 2 = fun x => -Complex.I * deriv u x := by
  have := vseq_succ κ u 0
  rw [vseq_one] at this
  simpa using this

lemma vseq_three (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    vseq κ u 3 = fun x => -(deriv (deriv u) x) + (κ : ℂ) * conj (u x) * (u x * u x) := by
  have h := vseq_succ κ u 1
  rw [vseq_two] at h
  have hd : ∀ x, deriv (fun y => -Complex.I * deriv u y) x = -Complex.I * deriv (deriv u) x := by
    intro x
    exact deriv_const_mul _ ((contDiff_infty_iff_deriv.mp
      (contDiff_infty_iff_deriv.mp hu.smooth).2).1 x)
  funext x
  have := congrFun h x
  simp only [hd, Finset.Icc_self, Finset.sum_singleton, vseq_one, Nat.reduceAdd] at this
  rw [show (2 - 1 : ℕ) = 1 from rfl, vseq_one] at this
  rw [this]
  have hI : -Complex.I * (-Complex.I * deriv (deriv u) x) = -(deriv (deriv u) x) := by
    rw [← mul_assoc, show -Complex.I * -Complex.I = (Complex.I * Complex.I) by ring, Complex.I_mul_I]
    ring
  rw [hI]

/-- **I₁ = ‖u‖₂²** (mass): `I_1 = ∫₀^L |u|²`, a real number. -/
theorem charge_one (L κ : ℝ) (u : ℝ → ℂ) :
    charge L κ u 1 = ((∫ x in (0 : ℝ)..L, ‖u x‖ ^ 2 : ℝ) : ℂ) := by
  unfold charge
  rw [vseq_one, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  rw [Complex.conj_mul']
  push_cast; rfl

/-- **I₂ = ∫ ū (−i ∂ₓu)** (momentum). -/
theorem charge_two (L κ : ℝ) (u : ℝ → ℂ) :
    charge L κ u 2 = ∫ x in (0 : ℝ)..L, conj (u x) * (-Complex.I * deriv u x) := by
  unfold charge
  rw [vseq_two]

/-- Integration by parts on the circle: `∫₀^L ū ∂ₓ²u = −∫₀^L conj(∂ₓu) ∂ₓu`. -/
theorem integral_conj_mul_deriv_deriv {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    ∫ x in (0 : ℝ)..L, conj (u x) * deriv (deriv u) x
      = -∫ x in (0 : ℝ)..L, conj (deriv u x) * deriv u x := by
  have h1 : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    ((contDiff_infty_iff_deriv.mp hu.smooth).1 x).hasDerivAt
  have h2 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x =>
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu.smooth).2).1 x).hasDerivAt
  have hc1 : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu.smooth).2.continuous
  have hc2 : Continuous (deriv (deriv u)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu.smooth).2).2.continuous
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := L)
    (u := fun x => conj (u x)) (u' := fun x => conj (deriv u x)) (v := deriv u)
    (v' := deriv (deriv u))
    (fun x _ => (h1 x).star) (fun x _ => h2 x)
    ((Complex.continuous_conj.comp hc1).intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
  have hb : conj (u L) * deriv u L - conj (u 0) * deriv u 0 = 0 := by
    have e1 : u L = u 0 := by simpa using hu.periodic 0
    have e2 : deriv u L = deriv u 0 := by simpa using periodic_deriv hu.periodic 0
    rw [e1, e2]; ring
  rw [key, hb]
  ring

/-- **I₃ = ∫ (|∂ₓu|² + κ|u|⁴)** (energy), with the integration by parts proved above. -/
theorem charge_three (L κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    charge L κ u 3 = ((∫ x in (0 : ℝ)..L, (‖deriv u x‖ ^ 2 + κ * ‖u x‖ ^ 4) : ℝ) : ℂ) := by
  have hc1 : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp hu.smooth).2.continuous
  have hc2 : Continuous (deriv (deriv u)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu.smooth).2).2.continuous
  have hcu : Continuous u := hu.smooth.continuous
  have hpt : ∀ x, conj (u x) * vseq κ u 3 x
      = -(conj (u x) * deriv (deriv u) x) + (((κ * ‖u x‖ ^ 4 : ℝ)) : ℂ) := by
    intro x
    rw [vseq_three κ hu]
    simp only
    have h4 : conj (u x) * conj (u x) * (u x * u x) = ((‖u x‖ ^ 4 : ℝ) : ℂ) := by
      have : conj (u x) * u x = ((‖u x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']; push_cast; rfl
      calc conj (u x) * conj (u x) * (u x * u x) = (conj (u x) * u x) * (conj (u x) * u x) := by ring
        _ = _ := by rw [this]; push_cast; ring
    push_cast at h4 ⊢
    linear_combination (κ : ℂ) * h4
  unfold charge
  rw [intervalIntegral.integral_congr (fun x _ => hpt x)]
  have hi1 : IntervalIntegrable (fun x => -(conj (u x) * deriv (deriv u) x)) MeasureTheory.volume 0 L :=
    (((Complex.continuous_conj.comp hcu).mul hc2).neg).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => (((κ * ‖u x‖ ^ 4 : ℝ)) : ℂ)) MeasureTheory.volume 0 L :=
    (Complex.continuous_ofReal.comp
      (continuous_const.mul ((continuous_norm.comp hcu).pow 4))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_neg,
    integral_conj_mul_deriv_deriv hu, neg_neg, intervalIntegral.integral_ofReal]
  have hn : ∀ x, conj (deriv u x) * deriv u x = ((‖deriv u x‖ ^ 2 : ℝ) : ℂ) := by
    intro x; rw [Complex.conj_mul']; push_cast; rfl
  simp only [hn]
  rw [intervalIntegral.integral_ofReal]
  rw [← Complex.ofReal_add, ← intervalIntegral.integral_add]
  · exact (continuous_norm.comp hc1 |>.pow 2).intervalIntegrable _ _
  · exact (continuous_const.mul ((continuous_norm.comp hcu).pow 4)).intervalIntegrable _ _

/-- **I₁ = ‖u‖₂² on the actual Hilbert space** `L²(𝕋_L)` (DEF-001 normalisation, measure of mass
`L`): `I_1(u) = ‖u‖²` for the `L²` element carried by the smooth periodic profile. -/
theorem charge_one_L2 [Fact (0 < L)] (κ : ℝ) {u : ℝ → ℂ} (hu : SmoothPeriodic L u) :
    charge L κ u 1 = ((‖(ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ
        (liftC hu.smooth.continuous hu.periodic) : Lp ℂ 2 (volume : Measure (AddCircle L)))‖ ^ 2 : ℝ) : ℂ) := by
  set F := liftC hu.smooth.continuous hu.periodic with hF
  set f : Lp ℂ 2 (volume : Measure (AddCircle L)) :=
    ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ F with hf
  have hae : (f : AddCircle L → ℂ) =ᵐ[(volume : Measure (AddCircle L))] F :=
    ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) (volume : Measure (AddCircle L)) F
  have h1 : ((‖f‖ ^ 2 : ℝ) : ℂ) = inner ℂ f f := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have h2 : inner ℂ f f = ∫ a, conj (F a) * F a ∂(volume : Measure (AddCircle L)) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [RCLike.inner_apply', hy]
  have h3 : charge L κ u 1 = ∫ a, conj (F a) * F a ∂(volume : Measure (AddCircle L)) := by
    unfold charge
    rw [vseq_one]
    have e : ∫ x in (0 : ℝ)..L, conj (u x) * u x
        = ∫ x in (0 : ℝ)..L, conj (F (x : AddCircle L)) * F (x : AddCircle L) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      simp only [hF, liftC_coe]
    rw [e]
    have h := AddCircle.intervalIntegral_preimage L 0 (fun a : AddCircle L => conj (F a) * F a)
    rw [zero_add] at h
    exact h
  rw [h3, h1, h2]

/-! Kernel axiom audit. -/
#print axioms vseq_succ
#print axioms vseq_regular
#print axioms charge_integrand_continuous
#print axioms vseq_two
#print axioms vseq_three
#print axioms charge_one
#print axioms charge_two
#print axioms integral_conj_mul_deriv_deriv
#print axioms charge_three
#print axioms charge_one_L2

end QuantumNLS.ClassicalCharges
