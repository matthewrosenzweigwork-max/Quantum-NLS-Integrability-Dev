import NlsGge.Hierarchy.GaussianTailCovarianceBernstein38
import NlsGge.Hierarchy.ComplexGaussianWick38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Hierarchy.RiccatiFormalChargeRemainderUniformNormalizationRecovery29Fourth
import NlsGge.Hierarchy.RiccatiNormalizedRemainderDerivativeCountAndTopSlotsRecovery33Second

/-! F06-B1: one gauge-balanced monomial of the normalized remainder after the Gaussian tail
substitution `u = v + Y` (paper/v2.tex `C:lem:contractions`, lines 743-781). -/

set_option autoImplicit false
noncomputable section
namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory NlsGge.Pilot NlsGge.Measure

section Gauss

variable {K : ℕ} {O : Type*} [DecidableEq O]

theorem prod_finset_eq_fin38 {M : Type*} [CommMonoid M] (A : Finset O) {n : ℕ} (e : A ≃ Fin n)
    (f : O → M) :
    ∏ i ∈ A, f i = ∏ t : Fin n, f (e.symm t : O) := by
  rw [← Finset.prod_coe_sort A f]
  exact (Equiv.prod_comp e.symm (fun i : A => f (i : O))).symm

/-- Wick bound for a Finset-indexed product, with separable covariance bounds. -/
theorem wick_norm_le38 (a : Fin K → ℝ) (ha : ∀ n, 0 < a n) (A B : Finset O)
    (c e : O → Fin K → ℂ) (κ : ℝ) (u w : O → ℝ) (hκ : 0 ≤ κ) (hu : ∀ i, 0 ≤ u i)
    (hw : ∀ j, 0 ≤ w j)
    (hcov : ∀ i ∈ A, ∀ j ∈ B, ‖∑ n, c i n * star (e j n) / (a n : ℂ)‖ ≤ κ * u i * w j) :
    ‖∫ g : Fin K → ℂ, (∏ i ∈ A, ∑ n, c i n * g n) * ∏ j ∈ B, star (∑ n, e j n * g n) ∂cgPi a‖ ≤
      if A.card = B.card then
        ((A.card).factorial : ℝ) * κ ^ A.card * ((∏ i ∈ A, u i) * ∏ j ∈ B, w j) else 0 := by
  classical
  by_cases h : A.card = B.card
  · rw [if_pos h]
    let eA : A ≃ Fin A.card := A.equivFin
    let eB : B ≃ Fin A.card := Finset.equivFinOfCardEq h.symm
    have hint : (fun g : Fin K → ℂ => (∏ i ∈ A, ∑ n, c i n * g n) * ∏ j ∈ B, star (∑ n, e j n * g n))
        = fun g => (∏ t : Fin A.card, ∑ n, c (eA.symm t : O) n * g n) *
            ∏ t : Fin A.card, star (∑ n, e (eB.symm t : O) n * g n) := by
      funext g
      rw [prod_finset_eq_fin38 A eA (fun i => ∑ n, c i n * g n),
        prod_finset_eq_fin38 B eB (fun j => star (∑ n, e j n * g n))]
    rw [hint, integral_cgPi_wick_eq a ha (fun t => c (eA.symm t : O)) (fun t => e (eB.symm t : O))]
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ σ : Equiv.Perm (Fin A.card),
        ‖∏ i, ∑ n, c (eA.symm i : O) n * star (e (eB.symm (σ i) : O) n) / (a n : ℂ)‖ ≤
        κ ^ A.card * ((∏ i ∈ A, u i) * ∏ j ∈ B, w j) := by
      intro σ
      rw [norm_prod]
      calc ∏ i, ‖∑ n, c (eA.symm i : O) n * star (e (eB.symm (σ i) : O) n) / (a n : ℂ)‖
          ≤ ∏ i : Fin A.card, (κ * u (eA.symm i : O) * w (eB.symm (σ i) : O)) :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ =>
              hcov _ (eA.symm i).2 _ (eB.symm (σ i)).2)
        _ = κ ^ A.card * ((∏ i ∈ A, u i) * ∏ j ∈ B, w j) := by
            rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
              prod_finset_eq_fin38 A eA u, prod_finset_eq_fin38 B eB w,
              Equiv.prod_comp σ (fun t : Fin A.card => w (eB.symm t : O))]
            ring
    calc ∑ σ : Equiv.Perm (Fin A.card), _ ≤ ∑ σ : Equiv.Perm (Fin A.card),
          κ ^ A.card * ((∏ i ∈ A, u i) * ∏ j ∈ B, w j) :=
          Finset.sum_le_sum fun σ _ => hterm σ
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
          ring
  · rw [if_neg h]
    have hint : (fun g : Fin K → ℂ => (∏ i ∈ A, ∑ n, c i n * g n) * ∏ j ∈ B, star (∑ n, e j n * g n))
        = fun g => (∏ t : Fin A.card, ∑ n, c (A.equivFin.symm t : O) n * g n) *
            ∏ t : Fin B.card, star (∑ n, e (B.equivFin.symm t : O) n * g n) := by
      funext g
      rw [prod_finset_eq_fin38 A A.equivFin (fun i => ∑ n, c i n * g n),
        prod_finset_eq_fin38 B B.equivFin (fun j => star (∑ n, e j n * g n))]
    rw [hint, integral_cgPi_wick_ne h a ha]
    simp


/-- Joint integrability of a polynomial-in-`g` term with continuous `x`-dependent coefficients. -/
theorem integrable_term38 (a : Fin K → ℝ) (A B : Finset O) (W : ℝ → ℂ) (hW : Continuous W)
    (c e : O → Fin K → ℝ → ℂ) (hc : ∀ i n, Continuous (c i n)) (he : ∀ j n, Continuous (e j n)) :
    Integrable (fun pr : ℝ × (Fin K → ℂ) => W pr.1 *
        ((∏ i ∈ A, ∑ n, c i n pr.1 * pr.2 n) * ∏ j ∈ B, star (∑ n, e j n pr.1 * pr.2 n)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (cgPi a)) := by
  classical
  let eA : A ≃ Fin A.card := A.equivFin
  let eB : B ≃ Fin B.card := B.equivFin
  have hfun : (fun pr : ℝ × (Fin K → ℂ) => W pr.1 *
        ((∏ i ∈ A, ∑ n, c i n pr.1 * pr.2 n) * ∏ j ∈ B, star (∑ n, e j n pr.1 * pr.2 n))) =
      fun pr => ∑ f : Fin A.card → Fin K, ∑ h : Fin B.card → Fin K,
        (W pr.1 * ((∏ i, c (eA.symm i : O) (f i) pr.1) *
            ∏ j, star (e (eB.symm j : O) (h j) pr.1))) *
          ∏ n, (pr.2 n ^ cnt f n * star (pr.2 n) ^ cnt h n) := by
    funext pr
    rw [prod_finset_eq_fin38 A eA (fun i => ∑ n, c i n pr.1 * pr.2 n),
      prod_finset_eq_fin38 B eB (fun j => star (∑ n, e j n pr.1 * pr.2 n)),
      integrand_expand (fun i n => c (eA.symm i : O) n pr.1) (fun j n => e (eB.symm j : O) n pr.1)
        pr.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hfun]
  refine integrable_finset_sum _ fun f _ => integrable_finset_sum _ fun h _ => ?_
  refine Integrable.mul_prod (f := fun x => W x * ((∏ i, c (eA.symm i : O) (f i) x) *
            ∏ j, star (e (eB.symm j : O) (h j) x))) ?_ (integrable_cgPi_monomial a (cnt f) (cnt h))
  refine Continuous.integrableOn_Ioc ?_
  refine hW.mul ((continuous_finset_prod _ fun i _ => hc _ _).mul
    (continuous_finset_prod _ fun j _ => (he _ _).star))

/-- Fubini and the Wick bound for one term. -/
theorem fubini_wick_term38 (a : Fin K → ℝ) (ha : ∀ n, 0 < a n) (A B : Finset O) (W : ℝ → ℂ)
    (hW : Continuous W)
    (c e : O → Fin K → ℝ → ℂ) (hc : ∀ i n, Continuous (c i n)) (he : ∀ j n, Continuous (e j n))
    (κ : ℝ) (u w : O → ℝ) (hκ : 0 ≤ κ) (hu : ∀ i, 0 ≤ u i) (hw0 : ∀ j, 0 ≤ w j)
    (hcov : ∀ x, ∀ i ∈ A, ∀ j ∈ B, ‖∑ n, c i n x * star (e j n x) / (a n : ℂ)‖ ≤ κ * u i * w j) :
    Integrable (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1, W x *
        ((∏ i ∈ A, ∑ n, c i n x * g n) * ∏ j ∈ B, star (∑ n, e j n x * g n))) (cgPi a) ∧
    ‖∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1, W x *
        ((∏ i ∈ A, ∑ n, c i n x * g n) * ∏ j ∈ B, star (∑ n, e j n x * g n))) ∂cgPi a‖ ≤
      (if A.card = B.card then
        ((A.card).factorial : ℝ) * κ ^ A.card * ((∏ i ∈ A, u i) * ∏ j ∈ B, w j) else 0) *
        ∫ x in (0 : ℝ)..1, ‖W x‖ := by
  classical
  have hint := integrable_term38 a A B W hW c e hc he
  set F : ℝ → (Fin K → ℂ) → ℂ := fun x g => W x *
        ((∏ i ∈ A, ∑ n, c i n x * g n) * ∏ j ∈ B, star (∑ n, e j n x * g n)) with hF
  have hint' : Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (cgPi a)) := hint
  have h1 : Integrable (fun g : Fin K → ℂ => ∫ x, F x g ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)))
      (cgPi a) := hint'.integral_prod_right
  have h2 : Integrable (fun x : ℝ => ∫ g, F x g ∂cgPi a) (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    hint'.integral_prod_left
  simp only [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine ⟨h1, ?_⟩
  rw [← integral_integral_swap hint']
  refine (norm_integral_le_integral_norm _).trans ?_
  have hW1 : IntegrableOn (fun x => ‖W x‖) (Set.Ioc (0 : ℝ) 1) :=
    (hW.norm).integrableOn_Ioc
  rw [← integral_const_mul]
  refine integral_mono h2.norm (hW1.const_mul _) fun x => ?_
  have hx : ∫ g, F x g ∂cgPi a = W x * ∫ g, ((∏ i ∈ A, ∑ n, c i n x * g n) *
      ∏ j ∈ B, star (∑ n, e j n x * g n)) ∂cgPi a := by
    simp only [hF]
    rw [integral_const_mul]
  rw [hx, norm_mul]
  have hw := wick_norm_le38 a ha A B (fun i n => c i n x) (fun j n => e j n x) κ u w hκ hu hw0
    (hcov x)
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)

end Gauss

section XSide

/-- Two factors in `L²`, the rest in `L∞`. -/
theorem integral_prod_le38 {T : Type*} [DecidableEq T] (R : Finset T) (hR : 2 ≤ R.card)
    (f : T → ℝ → ℝ) (hcont : ∀ t, Continuous (f t)) (hnn : ∀ t x, 0 ≤ f t x)
    (S0 L0 : ℝ) (hS0 : 0 ≤ S0) (hsup : ∀ t x, f t x ≤ S0)
    (hL2 : ∀ t, ∫ x in (0 : ℝ)..1, (f t x) ^ 2 ≤ L0) :
    ∫ x in (0 : ℝ)..1, ∏ t ∈ R, f t x ≤ S0 ^ (R.card - 2) * L0 := by
  obtain ⟨t1, h1, t2, h2, h12⟩ := Finset.one_lt_card.1 (by omega : 1 < R.card)
  have h2' : t2 ∈ R.erase t1 := Finset.mem_erase.2 ⟨h12.symm, h2⟩
  set R' := (R.erase t1).erase t2 with hR'
  have hcard : R'.card = R.card - 2 := by
    rw [hR', Finset.card_erase_of_mem h2', Finset.card_erase_of_mem h1]; omega
  have hprod : ∀ x, ∏ t ∈ R, f t x = f t1 x * (f t2 x * ∏ t ∈ R', f t x) := by
    intro x
    have e1 := Finset.mul_prod_erase R (fun t => f t x) h1
    have e2 := Finset.mul_prod_erase (R.erase t1) (fun t => f t x) h2'
    rw [hR', e2, e1]
  have hrest : ∀ x, ∏ t ∈ R', f t x ≤ S0 ^ (R.card - 2) := by
    intro x
    rw [← hcard]
    calc ∏ t ∈ R', f t x ≤ ∏ t ∈ R', S0 :=
          Finset.prod_le_prod₀ (fun t _ => hnn t x) fun t _ => hsup t x
      _ = S0 ^ R'.card := Finset.prod_const _
  have hrest0 : ∀ x, 0 ≤ ∏ t ∈ R', f t x := fun x => Finset.prod_nonneg fun t _ => hnn t x
  have hpt : ∀ x, ∏ t ∈ R, f t x ≤ S0 ^ (R.card - 2) * (((f t1 x) ^ 2 + (f t2 x) ^ 2) / 2) := by
    intro x
    rw [hprod x]
    have hab : f t1 x * f t2 x ≤ ((f t1 x) ^ 2 + (f t2 x) ^ 2) / 2 := by
      nlinarith [sq_nonneg (f t1 x - f t2 x)]
    calc f t1 x * (f t2 x * ∏ t ∈ R', f t x) = (f t1 x * f t2 x) * ∏ t ∈ R', f t x := by ring
      _ ≤ (((f t1 x) ^ 2 + (f t2 x) ^ 2) / 2) * S0 ^ (R.card - 2) :=
          mul_le_mul hab (hrest x) (hrest0 x) (by positivity)
      _ = _ := by ring
  have hi : ∀ t, IntervalIntegrable (fun x => (f t x) ^ 2) MeasureTheory.volume 0 1 :=
    fun t => ((hcont t).pow 2).intervalIntegrable _ _
  calc ∫ x in (0 : ℝ)..1, ∏ t ∈ R, f t x
      ≤ ∫ x in (0 : ℝ)..1, S0 ^ (R.card - 2) * (((f t1 x) ^ 2 + (f t2 x) ^ 2) / 2) :=
        intervalIntegral.integral_mono_on zero_le_one
          ((continuous_finset_prod _ fun t _ => hcont t).intervalIntegrable _ _)
          (((((hcont t1).pow 2).add ((hcont t2).pow 2)).div_const 2).const_mul _ |>.intervalIntegrable _ _)
          fun x _ => hpt x
    _ = S0 ^ (R.card - 2) * ((∫ x in (0 : ℝ)..1, (f t1 x) ^ 2) / 2 +
          (∫ x in (0 : ℝ)..1, (f t2 x) ^ 2) / 2) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi t1) (hi t2)]
        ring
    _ ≤ S0 ^ (R.card - 2) * (L0 / 2 + L0 / 2) := by
        gcongr
        · exact hL2 t1
        · exact hL2 t2
    _ = _ := by ring


theorem continuous_iteratedDeriv_planeReal38 (N : ℕ) (z : FourierPlane N) (a : ℕ) :
    Continuous (iteratedDeriv a (planeReal N z)) := by
  rw [iteratedDeriv_planeReal]
  exact (contDiff_planeReal N _).continuous

/-- Bernstein bound for a product of derivatives of `v = planeReal N z` over `R`, `|R| ≥ 2`. -/
theorem integral_prod_bernstein38 {T : Type*} [DecidableEq T] (R : Finset T) (hR : 2 ≤ R.card)
    (ord : T → ℕ) (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) :
    ∫ x in (0 : ℝ)..1, ∏ t ∈ R, ‖iteratedDeriv (ord t) (planeReal N z) x‖ ≤
      (2 * Real.pi * N) ^ (∑ t ∈ R, ord t) *
        ((Real.sqrt (2 * N + 1) * Real.sqrt (∑ i, ‖z i‖ ^ 2)) ^ (R.card - 2) * ∑ i, ‖z i‖ ^ 2) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlam : ∀ t, 0 < (2 * Real.pi * N) ^ ord t := fun t => by positivity
  set M : ℝ := ∑ i, ‖z i‖ ^ 2 with hM
  set f : T → ℝ → ℝ := fun t x => ‖iteratedDeriv (ord t) (planeReal N z) x‖ /
    (2 * Real.pi * N) ^ ord t with hf
  have hI : ∫ y in (0 : ℝ)..1, ‖planeReal N z y‖ ^ 2 = M := planeReal_integral_norm_sq38 N z
  have key := integral_prod_le38 R hR f
    (fun t => (continuous_iteratedDeriv_planeReal38 N z _).norm.div_const _)
    (fun t x => by positivity)
    (Real.sqrt (2 * N + 1) * Real.sqrt M) M (by positivity)
    (fun t x => by
      have h := bernstein_sup_38 N z (ord t) x
      rw [hI] at h
      simp only [hf]
      rw [div_le_iff₀ (hlam t)]
      calc _ ≤ _ := h
        _ = _ := by ring)
    (fun t => by
      have h := bernstein_L2_sq38 N z (ord t)
      rw [planeReal_integral_norm_sq38] at h
      simp only [hf, div_pow]
      rw [intervalIntegral.integral_div, div_le_iff₀ (by have := hlam t; positivity)]
      calc _ ≤ _ := h
        _ = _ := by ring)
  have hprod : ∀ x, ∏ t ∈ R, ‖iteratedDeriv (ord t) (planeReal N z) x‖ =
      (2 * Real.pi * N) ^ (∑ t ∈ R, ord t) * ∏ t ∈ R, f t x := by
    intro x
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    simp only [hf]
    rw [mul_div_cancel₀ _ (hlam t).ne']
  simp_rw [hprod]
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left key (by positivity)

end XSide

section Tail

variable {K : ℕ}

theorem hasDerivAt_cexp_mul38 (c : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (c * (y : ℂ))) (c * Complex.exp (c * (x : ℂ))) x := by
  have h : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * (x : ℂ)) * c) (x : ℂ) :=
    ((hasDerivAt_id (x : ℂ)).const_mul c).cexp |>.congr_deriv (by simp)
  have := h.comp_ofReal
  convert this using 1
  ring

theorem iteratedDeriv_sum_cexp38 (g c : Fin K → ℂ) (a : ℕ) :
    iteratedDeriv a (fun x : ℝ => ∑ k, g k * Complex.exp (c k * (x : ℂ))) =
      fun x : ℝ => ∑ k, g k * c k ^ a * Complex.exp (c k * (x : ℂ)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : HasDerivAt (fun y : ℝ => ∑ k, g k * c k ^ a * Complex.exp (c k * (y : ℂ)))
        (∑ k, g k * c k ^ a * (c k * Complex.exp (c k * (x : ℂ)))) x :=
      HasDerivAt.fun_sum fun k _ => (hasDerivAt_cexp_mul38 (c k) x).const_mul _
    rw [h.deriv]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- the Gaussian tail field `Y = Σ_k g_k e_{ι k}`. -/
def tailField38 (ι : Fin K → ℤ) (g : Fin K → ℂ) (x : ℝ) : ℂ :=
  ∑ k, g k * Complex.exp (2 * Real.pi * Complex.I * (ι k : ℂ) * (x : ℂ))

/-- Coefficient of `g k` in `Y^{(a)}(x)`. -/
def tailCoef38 (ι : Fin K → ℤ) (a : ℕ) (k : Fin K) (x : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I * (ι k : ℂ)) ^ a *
    Complex.exp (2 * Real.pi * Complex.I * (ι k : ℂ) * (x : ℂ))

theorem iteratedDeriv_tailField38 (ι : Fin K → ℤ) (g : Fin K → ℂ) (a : ℕ) (x : ℝ) :
    iteratedDeriv a (tailField38 ι g) x = ∑ k, tailCoef38 ι a k x * g k := by
  have := congrFun (iteratedDeriv_sum_cexp38 g (fun k => 2 * Real.pi * Complex.I * (ι k : ℂ)) a) x
  unfold tailField38 tailCoef38
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem contDiff_tailField38 (ι : Fin K → ℤ) (g : Fin K → ℂ) :
    ContDiff ℝ (⊤ : WithTop ℕ∞) (tailField38 ι g) := by
  unfold tailField38
  apply ContDiff.sum
  intro k _
  apply contDiff_const.mul
  apply ContDiff.cexp
  exact contDiff_const.mul Complex.ofRealCLM.contDiff

theorem continuous_tailCoef38 (ι : Fin K → ℤ) (a : ℕ) (k : Fin K) :
    Continuous (tailCoef38 ι a k) := by
  unfold tailCoef38
  exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

theorem norm_tailCoef38 (ι : Fin K → ℤ) (a : ℕ) (k : Fin K) (x : ℝ) :
    ‖tailCoef38 ι a k x‖ = (2 * Real.pi * |((ι k : ℤ) : ℝ)|) ^ a := by
  unfold tailCoef38
  rw [norm_mul, norm_pow]
  have : 2 * Real.pi * Complex.I * (ι k : ℂ) * (x : ℂ) =
      ((2 * Real.pi * (ι k : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, mul_one]
  congr 1
  simp [Complex.norm_mul, abs_of_pos Real.pi_pos]

/-- Jets of `v + Y`. -/
theorem iteratedDeriv_add_tail38 (N : ℕ) (z : FourierPlane N) (ι : Fin K → ℤ) (g : Fin K → ℂ)
    (a : ℕ) (x : ℝ) :
    iteratedDeriv a (fun y => planeReal N z y + tailField38 ι g y) x =
      iteratedDeriv a (planeReal N z) x + ∑ k, tailCoef38 ι a k x * g k := by
  have h := iteratedDeriv_add (n := a) (x := x) (f := planeReal N z) (g := tailField38 ι g)
    ((contDiff_planeReal N z).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiff_tailField38 ι g).contDiffAt.of_le (by exact_mod_cast le_top))
  rw [← iteratedDeriv_tailField38]
  exact h


theorem finiteHierarchyRate38_pos (m : ℕ) (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (hm : 1 ≤ m)
    (h0 : 0 < β 0) (hM : 0 < β m) (n : ℤ) : 0 < finiteHierarchyRate38 m β n := by
  have := finiteHierarchyRate38_lower m β hβ hm n
  have h : 0 < min (β 0) (β m) * (1 + (2 * Real.pi * |(n : ℝ)|) ^ (2 * m)) := by
    have := lt_min h0 hM
    positivity
  linarith

/-- The covariance of the tail jets (source `C:eq:covariance`), uniformly in `x`. -/
theorem cov_bound38 (m a b N : ℕ) (hm : 1 ≤ m) (ha : a ≤ m - 1) (hb : b ≤ m - 1)
    (β : ℕ → ℝ) (hβ : ∀ j ≤ m, 0 ≤ β j) (h0 : 0 < β 0) (hM : 0 < β m) (hN : 1 ≤ N)
    (ι : Fin K → ℤ) (hinj : Function.Injective ι) (hι : ∀ k, (N : ℤ) < |ι k|) (x : ℝ) :
    ‖∑ k, tailCoef38 ι a k x * star (tailCoef38 ι b k x) /
        ((finiteHierarchyRate38 m β (ι k) : ℝ) : ℂ)‖ ≤
      (2 / min (β 0) (β m)) / (N : ℝ) ^ (2 * m - 1) * (N : ℝ) ^ a * (N : ℝ) ^ b := by
  classical
  obtain ⟨hs, ht⟩ := covariance_tail_finiteHierarchy38 m a b N hm ha hb β hβ h0 hM hN
  set F : ℤ → ℝ := fun n => if (N : ℤ) < |n| then
    (2 * Real.pi * |(n : ℝ)|) ^ (a + b) / finiteHierarchyRate38 m β n else 0 with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => by
    simp only [hF]
    split_ifs
    · have := finiteHierarchyRate38_pos m β hβ hm h0 hM n
      positivity
    · exact le_refl _
  have h1 : ‖∑ k, tailCoef38 ι a k x * star (tailCoef38 ι b k x) /
        ((finiteHierarchyRate38 m β (ι k) : ℝ) : ℂ)‖ ≤ ∑ k, F (ι k) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    have hr := finiteHierarchyRate38_pos m β hβ hm h0 hM (ι k)
    rw [norm_div, norm_mul, norm_star, norm_tailCoef38, norm_tailCoef38, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    simp only [hF, hι k, if_true]
    rw [pow_add]
  have h2 : ∑ k, F (ι k) ≤ ∑' n, F n := by
    rw [← Finset.sum_image (f := F) (fun i _ j _ h => hinj h)]
    exact hs.sum_le_tsum _ (fun n _ => hF0 n)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : (2 / min (β 0) (β m)) * (N : ℝ) ^ ((a : ℤ) + b - 2 * m + 1) =
      (2 / min (β 0) (β m)) / (N : ℝ) ^ (2 * m - 1) * (N : ℝ) ^ a * (N : ℝ) ^ b := by
    have : ((a : ℤ) + b - 2 * m + 1) = ((a + b : ℕ) : ℤ) - ((2 * m - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)]; ring
    rw [this, zpow_sub₀ hN0.ne', zpow_natCast, zpow_natCast, pow_add]
    ring
  rw [← h3]
  exact h1.trans (h2.trans ht)

end Tail

section Arith

theorem pow_div_le38 (N : ℝ) (hN : 1 ≤ N) (a b c : ℕ) (h : a + c ≤ b) :
    N ^ a / N ^ b ≤ 1 / N ^ c := by
  have hN0 : 0 < N := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
  exact pow_le_pow_right₀ hN h

theorem sqrt_prod_pow38 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (l : ℕ) :
    (Real.sqrt x * Real.sqrt y) ^ (2 * l) = (x * y) ^ l := by
  rw [pow_mul, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- term with `l = l' + 1` remaining pairs. -/
theorem arith_pos38 (N M K0 : ℝ) (hN : 1 ≤ N) (hM : 0 ≤ M) (hK0 : 0 ≤ K0)
    (k l' dS dR m j : ℕ) (hk : 1 ≤ k) (hdeg : dS + dR + 2 * k + 2 * (l' + 1) = 2 * j + 2)
    (hj : j ≤ m) :
    ((k.factorial : ℝ) * (K0 / N ^ (2 * m - 1)) ^ k * N ^ dS) *
        ((2 * Real.pi * N) ^ dR *
          ((Real.sqrt (2 * N + 1) * Real.sqrt M) ^ (2 * (l' + 1) - 2) * M)) ≤
      (k.factorial : ℝ) * K0 ^ k * (2 * Real.pi) ^ dR * 3 ^ (l' + 1) * (M / N) ^ (l' + 1) := by
  have hN0 : 0 < N := by linarith
  have e2 : 2 * (l' + 1) - 2 = 2 * l' := by omega
  rw [e2, sqrt_prod_pow38 _ _ (by linarith) hM]
  have h3 : (2 * N + 1) ^ l' ≤ (3 * N) ^ l' := pow_le_pow_left₀ (by linarith) (by linarith) l'
  have hMl : (2 * N + 1) * M ≤ 3 * N * M := by nlinarith
  have h4 : ((2 * N + 1) * M) ^ l' ≤ (3 * N * M) ^ l' :=
    pow_le_pow_left₀ (by positivity) hMl l'
  have hexp : dS + dR + l' + (l' + 1) ≤ (2 * m - 1) * k := by
    have : 2 * j + 1 ≤ (2 * m + 1) * k := by nlinarith
    zify [(by omega : 1 ≤ 2 * m)] at this ⊢
    nlinarith
  have hpd := pow_div_le38 N hN (dS + dR + l') ((2 * m - 1) * k) (l' + 1) hexp
  have hfac : (0 : ℝ) ≤ (k.factorial : ℝ) * K0 ^ k * (2 * Real.pi) ^ dR * M ^ (l' + 1) := by
    positivity
  have hL : ((k.factorial : ℝ) * (K0 / N ^ (2 * m - 1)) ^ k * N ^ dS) *
        ((2 * Real.pi * N) ^ dR * (((2 * N + 1) * M) ^ l' * M)) ≤
      ((k.factorial : ℝ) * K0 ^ k * (2 * Real.pi) ^ dR * M ^ (l' + 1)) *
        (3 ^ l' * (N ^ (dS + dR + l') / N ^ ((2 * m - 1) * k))) := by
    have e : ((k.factorial : ℝ) * (K0 / N ^ (2 * m - 1)) ^ k * N ^ dS) *
        ((2 * Real.pi * N) ^ dR * (((3 * N * M)) ^ l' * M)) =
      ((k.factorial : ℝ) * K0 ^ k * (2 * Real.pi) ^ dR * M ^ (l' + 1)) *
        (3 ^ l' * (N ^ (dS + dR + l') / N ^ ((2 * m - 1) * k))) := by
      rw [div_pow, ← pow_mul, mul_pow, mul_pow, mul_pow, pow_add, pow_add, pow_one]
      field_simp
      rw [mul_pow, pow_add]
      ring
    rw [← e]
    gcongr
  refine hL.trans ?_
  have e5 : (M / N) ^ (l' + 1) = M ^ (l' + 1) * (1 / N ^ (l' + 1)) := by
    rw [div_pow]; ring
  rw [e5]
  have : 3 ^ l' * (N ^ (dS + dR + l') / N ^ ((2 * m - 1) * k)) ≤ 3 ^ (l' + 1) * (1 / N ^ (l' + 1)) := by
    rw [pow_succ]
    have h3p : (0 : ℝ) ≤ 3 ^ l' := by positivity
    calc 3 ^ l' * (N ^ (dS + dR + l') / N ^ ((2 * m - 1) * k)) ≤ 3 ^ l' * (1 / N ^ (l' + 1)) :=
          mul_le_mul_of_nonneg_left hpd h3p
      _ ≤ 3 ^ l' * 3 * (1 / N ^ (l' + 1)) := by
          have : (0 : ℝ) ≤ 3 ^ l' * (1 / N ^ (l' + 1)) := by positivity
          nlinarith
  calc _ ≤ ((k.factorial : ℝ) * K0 ^ k * (2 * Real.pi) ^ dR * M ^ (l' + 1)) *
        (3 ^ (l' + 1) * (1 / N ^ (l' + 1))) := mul_le_mul_of_nonneg_left this hfac
    _ = _ := by ring


theorem arith_zero38 (N K0 : ℝ) (hN : 1 ≤ N) (hK0 : 0 ≤ K0) (k dS m j : ℕ) (hk : 2 ≤ k)
    (hdeg : dS + 2 * k = 2 * j + 2) (hj : j ≤ m) :
    ((k.factorial : ℝ) * (K0 / N ^ (2 * m - 1)) ^ k * N ^ dS) ≤
      (k.factorial : ℝ) * K0 ^ k * (N ^ (2 * m))⁻¹ := by
  have hN0 : 0 < N := by linarith
  have hexp : dS + 2 * m ≤ (2 * m - 1) * k := by
    have : 2 * j + 2 + 2 * m ≤ (2 * m + 1) * k := by nlinarith
    zify [(by omega : 1 ≤ 2 * m)] at this ⊢
    nlinarith
  have hpd := pow_div_le38 N hN dS ((2 * m - 1) * k) (2 * m) hexp
  have e : ((k.factorial : ℝ) * (K0 / N ^ (2 * m - 1)) ^ k * N ^ dS) =
      ((k.factorial : ℝ) * K0 ^ k) * (N ^ dS / N ^ ((2 * m - 1) * k)) := by
    rw [div_pow, ← pow_mul]; ring
  rw [e]
  have : (N ^ (2 * m))⁻¹ = 1 / N ^ (2 * m) := by rw [one_div]
  rw [this]
  exact mul_le_mul_of_nonneg_left hpd (by positivity : (0:ℝ) ≤ (k.factorial : ℝ) * K0 ^ k)

end Arith

section Main

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- value of the jet at an occurrence `t` (barred: complex conjugate). -/
def jet38 (bar : O → Bool) (ord : O → ℕ) (u : ℝ → ℂ) (t : O) (x : ℝ) : ℂ :=
  if bar t = true then star (iteratedDeriv (ord t) u x) else iteratedDeriv (ord t) u x

/-- the term of the expansion in which the occurrences in `R` keep their `v`-value. -/
def termR38 {K : ℕ} (bar : O → Bool) (ord : O → ℕ) (N : ℕ) (z : FourierPlane N)
    (ι : Fin K → ℤ) (R : Finset O) (x : ℝ) (g : Fin K → ℂ) : ℂ :=
  (∏ t ∈ R, jet38 bar ord (planeReal N z) t x) *
    ((∏ i ∈ (Finset.univ \ R).filter (fun t => ¬ bar t = true),
        ∑ k, tailCoef38 ι (ord i) k x * g k) *
      ∏ j ∈ (Finset.univ \ R).filter (fun t => bar t = true),
        star (∑ k, tailCoef38 ι (ord j) k x * g k))

def Phi38 (m N : ℕ) (M : ℝ) : ℝ :=
  ((N : ℝ) ^ (2 * m))⁻¹ + ∑ l ∈ Finset.Icc 1 m, (M / N) ^ l

theorem Phi38_nonneg (m N : ℕ) (M : ℝ) (hM : 0 ≤ M) : 0 ≤ Phi38 m N M := by
  unfold Phi38
  positivity

def CC38 (m : ℕ) (β : ℕ → ℝ) (ord : O → ℕ) : ℝ :=
  ((Fintype.card O).factorial : ℝ) * (1 + 2 / min (β 0) (β m)) ^ Fintype.card O *
    (1 + 2 * Real.pi) ^ (∑ t, ord t) * 3 ^ Fintype.card O

theorem continuous_jet38 (bar : O → Bool) (ord : O → ℕ) (N : ℕ) (z : FourierPlane N) (t : O) :
    Continuous (jet38 bar ord (planeReal N z) t) := by
  unfold jet38
  split_ifs
  · exact (continuous_iteratedDeriv_planeReal38 N z _).star
  · exact continuous_iteratedDeriv_planeReal38 N z _

theorem norm_jet38 (bar : O → Bool) (ord : O → ℕ) (u : ℝ → ℂ) (t : O) (x : ℝ) :
    ‖jet38 bar ord u t x‖ = ‖iteratedDeriv (ord t) u x‖ := by
  unfold jet38
  split_ifs
  · exact norm_star _
  · rfl


theorem CC_bound38 (m : ℕ) (β : ℕ → ℝ) (h0 : 0 < β 0) (hM : 0 < β m) (ord : O → ℕ)
    (k l dR : ℕ) (hk : k ≤ Fintype.card O) (hl : l ≤ Fintype.card O)
    (hdR : dR ≤ ∑ t, ord t) :
    (k.factorial : ℝ) * (2 / min (β 0) (β m)) ^ k * (2 * Real.pi) ^ dR * 3 ^ l ≤
      CC38 m β ord := by
  unfold CC38
  have hK0 : 0 ≤ 2 / min (β 0) (β m) := by have := lt_min h0 hM; positivity
  have h1 : (k.factorial : ℝ) ≤ ((Fintype.card O).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hk
  have h2 : (2 / min (β 0) (β m)) ^ k ≤ (1 + 2 / min (β 0) (β m)) ^ Fintype.card O :=
    (pow_le_pow_left₀ hK0 (by linarith) k).trans
      (pow_le_pow_right₀ (by linarith) hk)
  have h3 : (2 * Real.pi) ^ dR ≤ (1 + 2 * Real.pi) ^ (∑ t, ord t) :=
    (pow_le_pow_left₀ (by positivity) (by linarith) dR).trans
      (pow_le_pow_right₀ (by nlinarith [Real.pi_pos]) hdR)
  have h4 : (3 : ℝ) ^ l ≤ 3 ^ Fintype.card O := pow_le_pow_right₀ (by norm_num) hl
  gcongr

theorem R_term_bound38 (m j : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m) (bar : O → Bool) (ord : O → ℕ) (hord : ∀ t, ord t ≤ m - 1)
    (hbal : (Finset.univ.filter fun t => bar t = true).card =
      (Finset.univ.filter fun t => ¬ bar t = true).card)
    (h4 : 4 ≤ Fintype.card O) (hdeg : ∑ t, ord t + Fintype.card O = 2 * j + 2) (hj : j ≤ m)
    (N : ℕ) (hN : 1 ≤ N) (z : FourierPlane N) {K : ℕ} (ι : Fin K → ℤ)
    (hinj : Function.Injective ι) (hι : ∀ k, (N : ℤ) < |ι k|)
    (R : Finset O) (hR : R ≠ Finset.univ) :
    Integrable (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g)
        (cgPi (fun k => finiteHierarchyRate38 m β (ι k))) ∧
      ‖∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g)
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))‖ ≤
        CC38 m β ord * Phi38 m N (∑ i, ‖z i‖ ^ 2) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set M : ℝ := ∑ i, ‖z i‖ ^ 2 with hMdef
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => by positivity
  set K0 : ℝ := 2 / min (β 0) (β m) with hK0def
  have hK0 : 0 ≤ K0 := by
    have := lt_min h0 hM
    positivity
  set S := Finset.univ \ R with hS
  set A := S.filter (fun t => ¬ bar t = true) with hA
  set B := S.filter (fun t => bar t = true) with hB
  have hrate : ∀ k, 0 < finiteHierarchyRate38 m β (ι k) := fun k =>
    finiteHierarchyRate38_pos m β hβ hm h0 hM (ι k)
  have hcov : ∀ x, ∀ i ∈ A, ∀ j ∈ B,
      ‖∑ n, tailCoef38 ι (ord i) n x * star (tailCoef38 ι (ord j) n x) /
        ((finiteHierarchyRate38 m β (ι n) : ℝ) : ℂ)‖ ≤
      K0 / (N : ℝ) ^ (2 * m - 1) * (N : ℝ) ^ (ord i) * (N : ℝ) ^ (ord j) := fun x i _ j _ =>
    cov_bound38 m (ord i) (ord j) N hm (hord i) (hord j) β hβ h0 hM hN ι hinj hι x
  have hfw := fubini_wick_term38 (fun k => finiteHierarchyRate38 m β (ι k)) hrate A B
    (fun x => ∏ t ∈ R, jet38 bar ord (planeReal N z) t x)
    (continuous_finset_prod _ fun t _ => continuous_jet38 bar ord N z t)
    (fun t n x => tailCoef38 ι (ord t) n x) (fun t n x => tailCoef38 ι (ord t) n x)
    (fun t n => continuous_tailCoef38 ι _ n) (fun t n => continuous_tailCoef38 ι _ n)
    (K0 / (N : ℝ) ^ (2 * m - 1)) (fun t => (N : ℝ) ^ (ord t)) (fun t => (N : ℝ) ^ (ord t))
    (by positivity) (fun t => by positivity) (fun t => by positivity) hcov
  refine ⟨hfw.1, hfw.2.trans ?_⟩
  -- combinatorics
  set p := (Finset.univ.filter fun t => bar t = true).card with hp
  have hcardO : Fintype.card O = 2 * p := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset O))
      (fun t => bar t = true)
    rw [Finset.card_univ] at this
    omega
  have hAB : A.card + B.card = S.card := by
    have := Finset.card_filter_add_card_filter_not (s := S) (fun t => bar t = true)
    rw [hA, hB]; omega
  have hSR : S.card + R.card = Fintype.card O := by
    rw [hS, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ R), Finset.card_univ]
  have hdSR : ∑ t ∈ S, ord t + ∑ t ∈ R, ord t = ∑ t, ord t := by
    rw [hS]; exact Finset.sum_sdiff (Finset.subset_univ R)
  have hdAB : ∑ t ∈ B, ord t + ∑ t ∈ A, ord t = ∑ t ∈ S, ord t :=
    Finset.sum_filter_add_sum_filter_not S (fun t => bar t = true) ord
  have hAle : A.card ≤ p := by
    have : A ⊆ Finset.univ.filter fun t => ¬ bar t = true := by
      intro t ht
      simp only [hA, Finset.mem_filter] at ht ⊢
      exact ⟨Finset.mem_univ _, ht.2⟩
    have := Finset.card_le_card this
    omega
  have hSne : S.Nonempty := by
    rw [hS]
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exact hR (Finset.eq_univ_of_forall fun t => hne (Finset.mem_univ t))
  have hSpos : 0 < S.card := Finset.card_pos.2 hSne
  have hCCnn : 0 ≤ CC38 m β ord := by
    unfold CC38
    have : 0 ≤ 2 / min (β 0) (β m) := by have := lt_min h0 hM; positivity
    positivity
  have hPhi := Phi38_nonneg m N M hM0
  by_cases hcard : A.card = B.card
  · rw [if_pos hcard]
    set k := A.card with hk
    have hk1 : 1 ≤ k := by omega
    have hRc : R.card = 2 * (p - k) := by omega
    have hprodU : (∏ i ∈ A, (N : ℝ) ^ (ord i)) * ∏ j ∈ B, (N : ℝ) ^ (ord j) =
        (N : ℝ) ^ (∑ t ∈ S, ord t) := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add, ← hdAB, add_comm]
    rw [hprodU]
    have hkO : k ≤ Fintype.card O := by omega
    have hdtot : ∑ t, ord t ≤ ∑ t, ord t := le_refl _
    obtain hl0 | hl1 : p - k = 0 ∨ 1 ≤ p - k := by omega
    · -- all occurrences contracted
      have hRe : R = ∅ := Finset.card_eq_zero.1 (by omega)
      have hk2 : 2 ≤ k := by omega
      have hdS : ∑ t ∈ S, ord t = ∑ t, ord t := by
        have := hdSR; rw [hRe] at this; simpa using this
      have hint : ∫ x in (0 : ℝ)..1, ‖∏ t ∈ R, jet38 bar ord (planeReal N z) t x‖ = 1 := by
        simp [hRe]
      rw [hint, mul_one]
      have := arith_zero38 N K0 hN1 hK0 k (∑ t ∈ S, ord t) m j hk2 (by omega) hj
      refine this.trans ?_
      have hb := CC_bound38 m β h0 hM ord k 0 0 hkO (Nat.zero_le _) (Nat.zero_le _)
      simp only [pow_zero, mul_one] at hb
      have hI : ((N : ℝ) ^ (2 * m))⁻¹ ≤ Phi38 m N M := by
        unfold Phi38
        have : 0 ≤ ∑ l ∈ Finset.Icc 1 m, (M / (N : ℝ)) ^ l := by positivity
        linarith
      calc _ ≤ CC38 m β ord * ((N : ℝ) ^ (2 * m))⁻¹ :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hI hCCnn
    · obtain ⟨l', hl'⟩ : ∃ l', p - k = l' + 1 := ⟨p - k - 1, by omega⟩
      have hR2 : 2 ≤ R.card := by omega
      have hint : ∫ x in (0 : ℝ)..1, ‖∏ t ∈ R, jet38 bar ord (planeReal N z) t x‖ ≤
          (2 * Real.pi * N) ^ (∑ t ∈ R, ord t) *
            ((Real.sqrt (2 * N + 1) * Real.sqrt M) ^ (R.card - 2) * M) := by
        have := integral_prod_bernstein38 R hR2 ord N hN z
        simpa [norm_prod, norm_jet38] using this
      have hdeg' : ∑ t ∈ S, ord t + ∑ t ∈ R, ord t + 2 * k + 2 * (l' + 1) = 2 * j + 2 := by
        omega
      have hw := arith_pos38 N M K0 hN1 hM0 hK0 k l' (∑ t ∈ S, ord t) (∑ t ∈ R, ord t) m j hk1
        hdeg' hj
      rw [show R.card - 2 = 2 * (l' + 1) - 2 by omega] at hint
      have hnn : 0 ≤ (k.factorial : ℝ) * (K0 / (N : ℝ) ^ (2 * m - 1)) ^ k * (N : ℝ) ^ (∑ t ∈ S, ord t) := by
        positivity
      have hstep := (mul_le_mul_of_nonneg_left hint hnn).trans hw
      refine hstep.trans ?_
      have hlm : l' + 1 ≤ m := by
        have : p ≤ j + 1 := by omega
        omega
      have hb := CC_bound38 m β h0 hM ord k (l' + 1) (∑ t ∈ R, ord t) hkO (by omega)
        (by omega)
      have hPl : (M / (N : ℝ)) ^ (l' + 1) ≤ Phi38 m N M := by
        unfold Phi38
        have h1 : (M / (N : ℝ)) ^ (l' + 1) ≤ ∑ l ∈ Finset.Icc 1 m, (M / (N : ℝ)) ^ l :=
          Finset.single_le_sum (f := fun l => (M / (N : ℝ)) ^ l) (fun l _ => by positivity)
            (Finset.mem_Icc.2 ⟨by omega, hlm⟩)
        have : 0 ≤ ((N : ℝ) ^ (2 * m))⁻¹ := by positivity
        linarith
      calc _ ≤ CC38 m β ord * (M / (N : ℝ)) ^ (l' + 1) :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left hPl hCCnn
  · rw [if_neg hcard]
    simp only [zero_mul]
    exact mul_nonneg hCCnn hPhi


theorem continuous_termR38 {K : ℕ} (bar : O → Bool) (ord : O → ℕ) (N : ℕ) (z : FourierPlane N)
    (ι : Fin K → ℤ) (R : Finset O) (g : Fin K → ℂ) :
    Continuous (fun x => termR38 bar ord N z ι R x g) := by
  unfold termR38
  refine (continuous_finset_prod _ fun t _ => continuous_jet38 bar ord N z t).mul
    ((continuous_finset_prod _ fun i _ => ?_).mul (continuous_finset_prod _ fun j _ => ?_))
  · exact continuous_finset_sum _ fun k _ => (continuous_tailCoef38 ι _ k).mul continuous_const
  · exact (continuous_finset_sum _ fun k _ => (continuous_tailCoef38 ι _ k).mul continuous_const).star

theorem prod_jet_expand38 {K : ℕ} (bar : O → Bool) (ord : O → ℕ) (N : ℕ) (z : FourierPlane N)
    (ι : Fin K → ℤ) (g : Fin K → ℂ) (x : ℝ) :
    ∏ t, jet38 bar ord (fun y => planeReal N z y + tailField38 ι g y) t x =
      ∑ R ∈ (Finset.univ : Finset O).powerset, termR38 bar ord N z ι R x g := by
  classical
  set H : O → ℂ := fun t => if bar t = true then star (∑ k, tailCoef38 ι (ord t) k x * g k)
    else ∑ k, tailCoef38 ι (ord t) k x * g k with hH
  have h1 : ∀ t, jet38 bar ord (fun y => planeReal N z y + tailField38 ι g y) t x =
      jet38 bar ord (planeReal N z) t x + H t := by
    intro t
    unfold jet38
    rw [iteratedDeriv_add_tail38]
    simp only [hH]
    split_ifs
    · rw [star_add]
    · rfl
  simp_rw [h1]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun R _ => ?_
  unfold termR38
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ \ R) (fun t => bar t = true) H, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl fun t ht => ?_
    simp only [Finset.mem_filter] at ht
    simp [hH, ht.2]
  · refine Finset.prod_congr rfl fun t ht => ?_
    simp only [Finset.mem_filter] at ht
    simp [hH, ht.2]

theorem monomial_tail_bound38 (m j : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m) (bar : O → Bool) (ord : O → ℕ) (hord : ∀ t, ord t ≤ m - 1)
    (hbal : (Finset.univ.filter fun t => bar t = true).card =
      (Finset.univ.filter fun t => ¬ bar t = true).card)
    (h4 : 4 ≤ Fintype.card O) (hdeg : ∑ t, ord t + Fintype.card O = 2 * j + 2) (hj : j ≤ m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (z : FourierPlane N) (K : ℕ) (ι : Fin K → ℤ),
      Function.Injective ι → (∀ k, (N : ℤ) < |ι k|) →
      ‖(∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1,
            ∏ t, jet38 bar ord (fun y => planeReal N z y + tailField38 ι g y) t x)
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))) -
        ∫ x in (0 : ℝ)..1, ∏ t, jet38 bar ord (planeReal N z) t x‖ ≤
      A * Phi38 m N (∑ i, ‖z i‖ ^ 2) := by
  classical
  have hCC : 0 ≤ CC38 m β ord := by
    unfold CC38
    have : 0 ≤ 2 / min (β 0) (β m) := by have := lt_min h0 hM; positivity
    positivity
  refine ⟨2 ^ Fintype.card O * CC38 m β ord, by positivity, ?_⟩
  intro N hN z K ι hinj hι
  set μ := cgPi (fun k => finiteHierarchyRate38 m β (ι k)) with hμ
  set P := (Finset.univ : Finset O).powerset with hP
  have huniv : Finset.univ ∈ P := by simp [hP]
  have hbd := fun R (hR : R ≠ Finset.univ) =>
    R_term_bound38 m j β hm hβ h0 hM bar ord hord hbal h4 hdeg hj N hN z ι hinj hι R hR
  -- integrability in g of each R-term
  have hint : ∀ R ∈ P, Integrable (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g) μ := by
    intro R _
    by_cases hR : R = Finset.univ
    · subst hR
      have : (fun g : Fin K → ℂ => ∫ x in (0 : ℝ)..1, termR38 bar ord N z ι Finset.univ x g) =
          fun _ => ∫ x in (0 : ℝ)..1, ∏ t, jet38 bar ord (planeReal N z) t x := by
        funext g; simp [termR38]
      rw [this]
      exact integrable_const _
    · exact (hbd R hR).1
  have hxint : ∀ R ∈ P, ∀ g : Fin K → ℂ, IntervalIntegrable (fun x => termR38 bar ord N z ι R x g)
      MeasureTheory.volume 0 1 := fun R _ g => (continuous_termR38 bar ord N z ι R g).intervalIntegrable _ _
  have hlhs : (∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1,
            ∏ t, jet38 bar ord (fun y => planeReal N z y + tailField38 ι g y) t x) ∂μ) =
      ∑ R ∈ P, ∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g) ∂μ := by
    simp_rw [prod_jet_expand38, ← hP]
    have : ∀ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1,
        ∑ R ∈ P, termR38 bar ord N z ι R x g) =
        ∑ R ∈ P, ∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g := fun g =>
      intervalIntegral.integral_finset_sum (fun R hR => hxint R hR g)
    simp_rw [this]
    exact integral_finset_sum _ hint
  have hconst : (∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1, termR38 bar ord N z ι Finset.univ x g) ∂μ) =
      ∫ x in (0 : ℝ)..1, ∏ t, jet38 bar ord (planeReal N z) t x := by
    simp [termR38]
  rw [hlhs, ← Finset.add_sum_erase P _ huniv, hconst, add_sub_cancel_left]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ R ∈ P.erase Finset.univ, ‖∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1, termR38 bar ord N z ι R x g) ∂μ‖
      ≤ ∑ R ∈ P.erase Finset.univ, CC38 m β ord * Phi38 m N (∑ i, ‖z i‖ ^ 2) :=
        Finset.sum_le_sum fun R hR => (hbd R (Finset.ne_of_mem_erase hR)).2
    _ ≤ ∑ R ∈ P, CC38 m β ord * Phi38 m N (∑ i, ‖z i‖ ^ 2) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ =>
          mul_nonneg hCC (Phi38_nonneg m N _ (Finset.sum_nonneg fun i _ => by positivity))
    _ = _ := by
        rw [Finset.sum_const, hP, Finset.card_powerset, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

end Main

/-! ### B2: occurrence model of a monomial -/
section Occ

/-- the occurrences of the jets of a monomial `q` (each jet `v` occurs `q v` times). -/
abbrev OccType38 (q : Jet →₀ ℕ) := Σ v : ↥q.support, Fin (q v)

def occBar38 (q : Jet →₀ ℕ) : OccType38 q → Bool := fun t => t.1.1.1
def occOrd38 (q : Jet →₀ ℕ) : OccType38 q → ℕ := fun t => t.1.1.2

theorem riccatiJetFunction_eq_jet38 (u : ℝ → ℂ) (v : Jet) (x : ℝ) :
    riccatiJetFunction u v x = (if v.1 = true then star (iteratedDeriv v.2 u x)
      else iteratedDeriv v.2 u x) := by
  obtain ⟨b, n⟩ := v
  cases b
  · simp [riccatiJetFunction]
  · simp only [riccatiJetFunction, if_true]
    rw [iteratedDeriv_star_prerequisite]

theorem eval_monomial38 (u : ℝ → ℂ) (x : ℝ) (q : Jet →₀ ℕ) (c : ℤ) :
    riccatiJetEvaluation u x (MvPolynomial.monomial q c) =
      (c : ℂ) * ∏ t : OccType38 q, jet38 (occBar38 q) (occOrd38 q) u t x := by
  classical
  unfold riccatiJetEvaluation polynomialEvaluation
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  congr 1
  rw [Fintype.prod_sigma]
  simp only [Finsupp.prod]
  rw [← Finset.prod_coe_sort q.support]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [riccatiJetFunction_eq_jet38]
  have e : ∏ y : Fin (q v), jet38 (occBar38 q) (occOrd38 q) u ⟨v, y⟩ x =
      ∏ _y : Fin (q v), (if (v.1).1 = true then star (iteratedDeriv (v.1).2 u x)
        else iteratedDeriv (v.1).2 u x) := rfl
  rw [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_occ38 (q : Jet →₀ ℕ) : Fintype.card (OccType38 q) = q.degree := by
  classical
  rw [Fintype.card_sigma, Finsupp.degree_apply]
  simp only [Fintype.card_fin]
  exact Finset.sum_coe_sort q.support (fun v => q v)

theorem sum_ord_occ38 (q : Jet →₀ ℕ) :
    ∑ t : OccType38 q, occOrd38 q t = riccatiJetDerivativeOrderSumNativeRecovery q := by
  classical
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, occOrd38, smul_eq_mul]
  unfold riccatiJetDerivativeOrderSumNativeRecovery Finsupp.sum
  rw [← Finset.sum_coe_sort q.support]

theorem card_bar_occ38 (q : Jet →₀ ℕ) (hg : riccatiJetGaugeHomAfterComponents q = 0) :
    (Finset.univ.filter fun t : OccType38 q => occBar38 q t = true).card =
      (Finset.univ.filter fun t : OccType38 q => ¬ occBar38 q t = true).card := by
  classical
  have h1 : ∀ b : Bool, (Finset.univ.filter fun t : OccType38 q => (occBar38 q t = true) = (b = true)).card
      = ∑ v : ↥q.support, if (v.1.1 = true) = (b = true) then q v else 0 := by
    intro b
    rw [Finset.card_filter, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [occBar38]
  have hT := h1 true
  have hF := h1 false
  simp only [eq_iff_iff, iff_true, Bool.false_eq_true, iff_false] at hT hF
  rw [hT, hF]
  unfold riccatiJetGaugeHomAfterComponents at hg
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finsupp.sum] at hg
  rw [← Finset.sum_coe_sort q.support] at hg
  have : ((∑ v : ↥q.support, if v.1.1 = true then q v else 0 : ℕ) : ℤ) -
      ((∑ v : ↥q.support, if v.1.1 = true then 0 else q v : ℕ) : ℤ) = 0 := by
    rw [← hg]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v.1.1 = true <;> simp [hv]
  have := sub_eq_zero.1 this
  simp only [ite_not]
  exact_mod_cast this


/-- F06-B (generic monomial): for a monomial `q` with all jet orders `≤ m-1`, at least four
factors, weight `2j+2` and gauge `0`, `j ≤ m`, the Gaussian-tail correction is bounded by
`A (N^{-2m} + Σ_{l=1}^m (M/N)^l)` with `A` independent of `N`, `z`, the tail modes. -/
theorem monomial_tail_bound_q38 (m j : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i)
    (h0 : 0 < β 0) (hM : 0 < β m) (q : Jet →₀ ℕ) (c : ℤ)
    (hq_ord : ∀ v ∈ q.support, v.2 ≤ m - 1) (hq_deg : 4 ≤ q.degree)
    (hq_wt : riccatiJetWeightHomAfterComponents q = 2 * j + 2)
    (hq_g : riccatiJetGaugeHomAfterComponents q = 0) (hj : j ≤ m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (z : FourierPlane N) (K : ℕ) (ι : Fin K → ℤ),
      Function.Injective ι → (∀ k, (N : ℤ) < |ι k|) →
      ‖(∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation (fun y => planeReal N z y + tailField38 ι g y) x
              (MvPolynomial.monomial q c))
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))) -
        ∫ x in (0 : ℝ)..1, riccatiJetEvaluation (planeReal N z) x (MvPolynomial.monomial q c)‖ ≤
      A * (((N : ℝ) ^ (2 * m))⁻¹ + ∑ l ∈ Finset.Icc 1 m, ((∑ i, ‖z i‖ ^ 2) / N) ^ l) := by
  classical
  have hdeg : ∑ t : OccType38 q, occOrd38 q t + Fintype.card (OccType38 q) = 2 * j + 2 := by
    rw [sum_ord_occ38, card_occ38, add_comm, ← riccatiJetWeight_eq_degree_add_derivativeOrderSumNativeRecovery]
    exact hq_wt
  obtain ⟨A0, hA0, h⟩ := monomial_tail_bound38 m j β hm hβ h0 hM (occBar38 q) (occOrd38 q)
    (fun t => hq_ord t.1.1 t.1.2) (card_bar_occ38 q hq_g) (by rw [card_occ38]; exact hq_deg) hdeg hj
  refine ⟨|(c : ℝ)| * A0, by positivity, ?_⟩
  intro N hN z K ι hinj hι
  have h1 := h N hN z K ι hinj hι
  simp_rw [eval_monomial38]
  rw [intervalIntegral.integral_const_mul]
  simp_rw [intervalIntegral.integral_const_mul]
  rw [integral_const_mul, ← mul_sub, norm_mul, Complex.norm_intCast, mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _) |>.trans_eq (by unfold Phi38; ring)

/-- F06-B2: every supported monomial of the normalized remainder `R_j`, `1 ≤ j ≤ m`. -/
theorem normalizedRemainder_monomial_tail_bound38 (m j : ℕ) (β : ℕ → ℝ) (hm : 1 ≤ m)
    (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m) (hj : j ≤ m)
    (q : Jet →₀ ℕ)
    (hq : q ∈ (formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).support) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (z : FourierPlane N) (K : ℕ) (ι : Fin K → ℤ),
      Function.Injective ι → (∀ k, (N : ℤ) < |ι k|) →
      ‖(∫ g : Fin K → ℂ, (∫ x in (0 : ℝ)..1,
            riccatiJetEvaluation (fun y => planeReal N z y + tailField38 ι g y) x
              (MvPolynomial.monomial q
                ((formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).coeff q)))
          ∂cgPi (fun k => finiteHierarchyRate38 m β (ι k))) -
        ∫ x in (0 : ℝ)..1, riccatiJetEvaluation (planeReal N z) x
          (MvPolynomial.monomial q
            ((formalChargeRemainderNormalizedUniformNativeRecovery29Fourth j).coeff q))‖ ≤
      A * (((N : ℝ) ^ (2 * m))⁻¹ + ∑ l ∈ Finset.Icc 1 m, ((∑ i, ‖z i‖ ^ 2) / N) ^ l) := by
  have hprop := formalChargeRemainderNormalizedUniform_propertiesNativeRecovery29Fourth j
  have hbi := hprop.2.2.1 q hq
  have hwt : riccatiJetWeightHomAfterComponents q = 2 * j + 2 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.fst hbi
  have hg : riccatiJetGaugeHomAfterComponents q = 0 := by
    simpa [riccatiJetBidegreeAfterComponents] using congrArg Prod.snd hbi
  exact monomial_tail_bound_q38 m j β hm hβ h0 hM q _
    (fun v hv => (hprop.1 q hq v hv).trans (by omega)) (hprop.2.1 q hq) hwt hg hj

end Occ
end NlsGge.HierarchyRiccati.Core
