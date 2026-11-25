import NlsGge.GK38.Lib.EntireProductsParamb

/-!
# L4c, part 2a (core): generic parametric symmetric products

Plan section 6.1, piece L4c, part 2a (rev. 4.3); generalises the method of L4c part 1
(`EntireProductsParam{b,c}`), i.e. Grébert–Kappeler book Lemma C.1 and Thm A.3/A.4.

For a family `F : ℤ → E → ℂ` of analytic factors on an open subset `U` of a complex normed space `E`
the *paired deviation* is `pairDev (fun n => F n x) m = F (m+1) x * F (-(m+1)) x - 1`
(for `F m = 1 + a_m` it is `a_{m+1} + a_{-(m+1)} + a_{m+1} a_{-(m+1)}`, the book's pairing).

**Main theorem `analyticOnNhd_symm_tprod`.**  Hypotheses:
* each `F m` is analytic on `U`;
* `hline` (linewise majorant): along every complex line through a point of `U`, near the base
  point, `‖pairDev‖ ≤ u m` with a summable `u` (depending on the line);
* `hmass` (local uniform total mass): near every point of `U`, `Σ_m ‖pairDev‖ ≤ B`.

Conclusion: `x ↦ ∏'[symmetricIcc ℤ] m, F m x` is analytic on `U`.  Proof: along lines the product
is a locally uniform limit of analytic functions (Weierstrass), so it is weakly analytic; the total
mass gives local boundedness `‖∏‖ ≤ ‖F 0‖ e^B`; L3a closes.  The convergence of the product itself
is not a hypothesis (it follows from `hline` with `h = 0`).  The tail `∏_{m ≥ M}` of the pairs is the
analytic function used for the zero/order statements (`ParamProductsZeros`).
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-- Paired deviation from `1`: `f (m+1) f (-(m+1)) - 1`. -/
def pairDev (f : ℤ → ℂ) (m : ℕ) : ℂ := f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) - 1

theorem pairTerm_eq_pairDev (σ : ℤ → ℂ) (z : ℂ) (m : ℕ) :
    pairTerm σ z m = pairDev (prodFactor σ z) m := rfl

theorem one_add_pairDev (f : ℤ → ℂ) (m : ℕ) :
    1 + pairDev f m = f ((m : ℤ) + 1) * f (-((m : ℤ) + 1)) := by
  simp [pairDev]

/-! ### One sequence -/

theorem multipliable_symm_of_summable_pairDev {f : ℤ → ℂ}
    (h : Summable fun m : ℕ => ‖pairDev f m‖) : Multipliable f (symmetricIcc ℤ) :=
  multipliable_symm_pair h

theorem tprod_symm_eq_mul_tprod_pairDev {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) :
    ∏'[symmetricIcc ℤ] m, f m = f 0 * ∏' m : ℕ, (1 + pairDev f m) := by
  rw [tprod_symm_pair h]
  congr 2
  funext m
  rw [one_add_pairDev]

/-- Splitting off the finitely many factors `|n| ≤ M`. -/
theorem tprod_symm_eq_prod_mul_tail {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) (M : ℕ) :
    ∏'[symmetricIcc ℤ] m, f m
      = (∏ n ∈ Finset.Icc (-(M : ℤ)) M, f n) * ∏' m : ℕ, (1 + pairDev f (m + M)) := by
  have hshift : Multipliable fun n : ℕ => 1 + pairDev f (n + M) :=
    multipliable_one_add_of_summable ((summable_nat_add_iff M).mpr h)
  have hsplit := Multipliable.prod_mul_tprod_nat_mul' (f := fun k : ℕ => 1 + pairDev f k)
    (k := M) hshift
  have hprod : ∏ k ∈ Finset.range M, (1 + pairDev f k)
      = ∏ k ∈ Finset.range M, (f ((k : ℤ) + 1) * f (-((k : ℤ) + 1))) :=
    Finset.prod_congr rfl fun k _ => by rw [one_add_pairDev]
  rw [tprod_symm_eq_mul_tprod_pairDev h, prod_Icc_symm_eq, ← hsplit, hprod, mul_assoc]

/-- A weak bound: `‖∏'[sym] f‖ ≤ ‖f 0‖ exp (Σ ‖pairDev f‖)`. -/
theorem norm_tprod_symm_le {f : ℤ → ℂ} (h : Summable fun m : ℕ => ‖pairDev f m‖) :
    ‖∏'[symmetricIcc ℤ] m, f m‖ ≤ ‖f 0‖ * Real.exp (∑' m : ℕ, ‖pairDev f m‖) := by
  rw [tprod_symm_eq_mul_tprod_pairDev h, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_tprod_one_add_le h) (norm_nonneg _)

/-! ### One complex variable: Weierstrass on a ball -/

theorem differentiableOn_pairDev {G : ℤ → ℂ → ℂ} {K : Set ℂ} (hG : ∀ m, DifferentiableOn ℂ (G m) K)
    (m : ℕ) : DifferentiableOn ℂ (fun z => pairDev (fun n => G n z) m) K := by
  unfold pairDev
  exact ((hG _).mul (hG _)).sub_const 1

/-- The tails of the paired product are differentiable on a ball with a summable majorant. -/
theorem differentiableOn_pairTail {G : ℤ → ℂ → ℂ} {w : ℂ} {ρ : ℝ}
    (hG : ∀ m, DifferentiableOn ℂ (G m) (ball w ρ)) {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ z ∈ ball w ρ, ∀ m, ‖pairDev (fun n => G n z) m‖ ≤ u m) (M : ℕ) :
    DifferentiableOn ℂ (fun z => ∏' m : ℕ, (1 + pairDev (fun n => G n z) (m + M))) (ball w ρ) := by
  have h := Summable.hasProdLocallyUniformlyOn_nat_one_add
    (f := fun m z => pairDev (fun n => G n z) (m + M)) (K := ball w ρ) isOpen_ball
    ((summable_nat_add_iff M).mpr hu)
    (Filter.Eventually.of_forall fun m z hz => hb z hz (m + M))
    (fun m => (differentiableOn_pairDev hG (m + M)).continuousOn)
  refine TendstoLocallyUniformlyOn.differentiableOn h (Filter.Eventually.of_forall fun s => ?_)
    isOpen_ball
  exact DifferentiableOn.fun_finsetProd fun i _ =>
    (differentiableOn_pairDev hG (i + M)).const_add 1

/-- **One variable.**  A symmetric product of analytic factors with a summable majorant of the
paired deviations is differentiable on the ball. -/
theorem differentiableOn_symm_tprod {G : ℤ → ℂ → ℂ} {w : ℂ} {ρ : ℝ}
    (hG : ∀ m, DifferentiableOn ℂ (G m) (ball w ρ)) {u : ℕ → ℝ} (hu : Summable u)
    (hb : ∀ z ∈ ball w ρ, ∀ m, ‖pairDev (fun n => G n z) m‖ ≤ u m) :
    DifferentiableOn ℂ (fun z => ∏'[symmetricIcc ℤ] m : ℤ, G m z) (ball w ρ) := by
  have hT := differentiableOn_pairTail hG hu hb 0
  have e : ∀ z ∈ ball w ρ, ∏'[symmetricIcc ℤ] m : ℤ, G m z
      = G 0 z * ∏' m : ℕ, (1 + pairDev (fun n => G n z) (m + 0)) := fun z hz => by
    rw [tprod_symm_eq_mul_tprod_pairDev (hu.of_nonneg_of_le (fun _ => norm_nonneg _) (hb z hz))]
    simp
  exact ((hG 0).mul hT).congr e

/-! ### Several variables: the generic parametric product -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **L4c part 2a, main theorem.**  See the module docstring. -/
theorem analyticOnNhd_symm_tprod {U : Set E} (hU : IsOpen U) {F : ℤ → E → ℂ}
    (hF : ∀ m, AnalyticOnNhd ℂ (F m) U)
    (hline : ∀ x ∈ U, ∀ h : E, ∃ ρ > 0, ∃ u : ℕ → ℝ, Summable u ∧ ∀ ζ : ℂ, ‖ζ‖ < ρ →
      x + ζ • h ∈ U → ∀ m, ‖pairDev (fun n => F n (x + ζ • h)) m‖ ≤ u m)
    (hmass : ∀ x ∈ U, ∃ r > 0, ∃ B : ℝ, ∀ y ∈ ball x r, y ∈ U →
      ∑' m : ℕ, ‖pairDev (fun n => F n y) m‖ ≤ B) :
    AnalyticOnNhd ℂ (fun x => ∏'[symmetricIcc ℤ] m : ℤ, F m x) U := by
  have hsum : ∀ y ∈ U, Summable fun m : ℕ => ‖pairDev (fun n => F n y) m‖ := by
    intro y hy
    obtain ⟨ρ, hρ, u, hu, hb⟩ := hline y hy 0
    refine hu.of_nonneg_of_le (fun _ => norm_nonneg _) fun m => ?_
    simpa using hb 0 (by simpa using hρ) (by simpa using hy) m
  have hweak : WeaklyAnalyticOn (fun x => ∏'[symmetricIcc ℤ] m : ℤ, F m x) U := by
    intro x hx h ℓ
    obtain ⟨ρ, hρ, u, hu, hb⟩ := hline x hx h
    have hV : IsOpen {ζ : ℂ | x + ζ • h ∈ U} :=
      hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
    obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hV 0 (by simpa using hx)
    set r : ℝ := min ρ ρ' with hr
    have hrpos : 0 < r := lt_min hρ hρ'
    have hlineA : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => x + ζ • h) ζ := fun ζ =>
      analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    have hGd : ∀ m, DifferentiableOn ℂ (fun ζ : ℂ => F m (x + ζ • h)) (ball 0 r) := by
      intro m ζ hζ
      have hζV : ζ ∈ {ζ : ℂ | x + ζ • h ∈ U} :=
        hball (Metric.ball_subset_ball (min_le_right _ _) hζ)
      exact (((hF m) _ hζV).comp_of_eq (hlineA ζ) rfl).differentiableAt.differentiableWithinAt
    have hD := differentiableOn_symm_tprod (G := fun m ζ => F m (x + ζ • h)) (w := 0) (ρ := r)
      hGd hu (fun ζ hζ m => hb ζ (by
        have := (mem_ball_zero_iff.mp hζ)
        exact lt_of_lt_of_le this (min_le_left _ _))
        (hball (Metric.ball_subset_ball (min_le_right _ _) hζ)) m)
    have hA : AnalyticAt ℂ (fun ζ : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, F m (x + ζ • h)) 0 :=
      hD.analyticAt (ball_mem_nhds 0 hrpos)
    exact (ℓ.analyticAt _).comp hA
  refine analyticOnNhd_of_weak_of_locBdd hU hweak ?_
  intro x hx
  obtain ⟨r₁, hr₁, B, hB⟩ := hmass x hx
  obtain ⟨r₂, hr₂, C, hC⟩ := locBdd_of_analyticOnNhd (hF 0) x hx
  obtain ⟨r₃, hr₃, hU3⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨min r₁ (min r₂ r₃), lt_min hr₁ (lt_min hr₂ hr₃), C * Real.exp B, fun y hy => ?_⟩
  have hy1 : y ∈ ball x r₁ := ball_subset_ball (min_le_left _ _) hy
  have hy2 : y ∈ ball x r₂ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hy
  have hy3 : y ∈ ball x r₃ := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hy
  have hyU : y ∈ U := hU3 hy3
  refine (norm_tprod_symm_le (hsum y hyU)).trans ?_
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x (mem_ball_self hr₂))
  exact mul_le_mul (hC y hy2) (Real.exp_le_exp.mpr (hB y hy1 hyU)) (Real.exp_nonneg _) hC0

/-! ### The total-mass form (the interface for `entProd` and for P1's canonical root) -/

theorem pairMaj_mono {d d' : ℤ → ℝ} (h : ∀ n, d n ≤ d' n) (R : ℝ) (m : ℕ) :
    pairMaj d R m ≤ pairMaj d' R m := by
  unfold pairMaj
  have := majC1_nonneg
  gcongr
  · exact h _
  · exact h _

/-- **L4c part 2a, total-mass form.**  Let `Q y n ≥ 0` be an `ℓ¹`-type "density" of the deviations
(for `entProd`: `Q (z, s) n = ‖s n‖²`; for P1's canonical root: the sum of the squared deviations
`γ_n²`, `τ_n - nπ`).  Suppose

* `hpt`: near each `x ∈ U`, the paired deviation is bounded by `pairMaj (c Q y) R` with constants
  `c ≥ 0`, `R` (this is the book's pointwise estimate of the paired terms);
* `hQline`: `Q` has a summable majorant along every complex line;
* `hQmass`: `∑ Q y` is locally uniformly bounded.

Then the symmetric product of the analytic factors is analytic on `U`. -/
theorem analyticOnNhd_symm_tprod_of_mass {U : Set E} (hU : IsOpen U) {F : ℤ → E → ℂ}
    (hF : ∀ m, AnalyticOnNhd ℂ (F m) U) {Q : E → ℤ → ℝ} (hQ0 : ∀ y n, 0 ≤ Q y n)
    (hpt : ∀ x ∈ U, ∃ r > 0, ∃ c R : ℝ, 0 ≤ c ∧ ∀ y ∈ ball x r, y ∈ U → ∀ m : ℕ,
      ‖pairDev (fun n => F n y) m‖ ≤ pairMaj (fun n => c * Q y n) R m)
    (hQline : ∀ x ∈ U, ∀ h : E, ∃ ρ > 0, ∃ q : ℤ → ℝ, Summable q ∧ ∀ ζ : ℂ, ‖ζ‖ < ρ →
      x + ζ • h ∈ U → ∀ n, Q (x + ζ • h) n ≤ q n)
    (hQmass : ∀ x ∈ U, ∃ r > 0, ∃ B : ℝ, ∀ y ∈ ball x r, y ∈ U →
      Summable (Q y) ∧ ∑' n, Q y n ≤ B) :
    AnalyticOnNhd ℂ (fun x => ∏'[symmetricIcc ℤ] m : ℤ, F m x) U := by
  refine analyticOnNhd_symm_tprod hU hF ?_ ?_
  · intro x hx h
    obtain ⟨r, hr, c, R, hc, hb⟩ := hpt x hx
    obtain ⟨ρ, hρ, q, hq, hQ⟩ := hQline x hx h
    refine ⟨min ρ (r / (‖h‖ + 1)), lt_min hρ (by positivity), pairMaj (fun n => c * q n) R,
      summable_pairMaj (hq.mul_left c) R, fun ζ hζ hζU m => ?_⟩
    have hζρ : ‖ζ‖ < ρ := hζ.trans_le (min_le_left _ _)
    have hζr : ‖ζ‖ < r / (‖h‖ + 1) := hζ.trans_le (min_le_right _ _)
    have hball : x + ζ • h ∈ ball x r := by
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
      have h1 : ‖ζ‖ * (‖h‖ + 1) < r := (lt_div_iff₀ (by positivity)).mp hζr
      nlinarith [norm_nonneg ζ, norm_nonneg h]
    refine (hb _ hball hζU m).trans (pairMaj_mono (fun n => ?_) R m)
    exact mul_le_mul_of_nonneg_left (hQ ζ hζρ hζU n) hc
  · intro x hx
    obtain ⟨r, hr, c, R, hc, hb⟩ := hpt x hx
    obtain ⟨r', hr', B, hB⟩ := hQmass x hx
    refine ⟨min r r', lt_min hr hr', 2 * majC1 * (c * B) + majC2 R * sumInvSq,
      fun y hy hyU => ?_⟩
    have hy1 : y ∈ ball x r := ball_subset_ball (min_le_left _ _) hy
    have hy2 : y ∈ ball x r' := ball_subset_ball (min_le_right _ _) hy
    obtain ⟨hQs, hQB⟩ := hB y hy2 hyU
    have hdS : Summable fun n : ℤ => c * Q y n := hQs.mul_left c
    have hb' := hb y hy1 hyU
    have hsm : Summable fun m : ℕ => ‖pairDev (fun n => F n y) m‖ :=
      (summable_pairMaj hdS R).of_nonneg_of_le (fun _ => norm_nonneg _) hb'
    refine (Summable.tsum_le_tsum hb' hsm (summable_pairMaj hdS R)).trans ?_
    refine (tsum_pairMaj_le hdS (fun n => mul_nonneg hc (hQ0 y n)) R).trans ?_
    rw [tsum_mul_left]
    have h1 := majC1_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hQB hc]

end

end NlsGge.GK38.Lib
