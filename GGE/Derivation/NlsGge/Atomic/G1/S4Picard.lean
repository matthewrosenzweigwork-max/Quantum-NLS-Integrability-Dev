import Mathlib

/- G1-081 S4 / L1 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/G1/S4Picard.lean.
   CONDITIONAL support: Pro round 14 `exists_local_complex_analytic_flow` proved by complex Picard iteration
   (Riemann-sum differentiability of iterates, uniform geometric convergence, integral equation, ray argument for the
   t-derivative) from exactly two general analyticity theorems taken as hypotheses
   (HolAnalyticProp: differentiable => analytic on open subsets of C x E;
    UniformLimitAnalyticProp: uniform limits of analytic maps on open subsets of C x E are analytic).
   Both are true general theorems (proof development leaves (a),(b)). -/

set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
namespace NlsGge.Atomic.G1081S4Picard
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- One Picard step: `Φ ↦ (t,z) ↦ z + ∫_{[0,t]} F(Φ(s,z)) ds`, written along the ray `s = θ t`. -/
def picardStep (F : E → E) (Φ : ℂ × E → E) (p : ℂ × E) : E :=
  p.2 + p.1 • ∫ θ in (0:ℝ)..1, F (Φ (θ • p.1, p.2))

/-- Picard iterates started at the projection `(t,z) ↦ z`. -/
def picardIter (F : E → E) : ℕ → ℂ × E → E
  | 0 => fun p => p.2
  | k+1 => picardStep F (picardIter F k)

/-- Numerical and analytic data of the local problem. -/
structure PData (F : E → E) (a : E) (ρ M τ r : ℝ) (K : NNReal) : Prop where
  hρ : 0 < ρ
  hFd : DifferentiableOn ℂ F (ball a ρ)
  hFL : LipschitzOnWith K F (ball a ρ)
  hFM : ∀ x ∈ ball a ρ, ‖F x‖ ≤ M
  hM : 0 ≤ M
  hτ : 0 < τ
  hr : 0 < r
  hrρ : r ≤ ρ / 2
  hτM : τ * M ≤ ρ / 4
  hτK : τ * K ≤ 1 / 2

variable {F : E → E} {a : E} {ρ M τ r : ℝ} {K : NNReal}

lemma mem_ball_of_close (h : PData F a ρ M τ r K) {t : ℂ} {z w : E} (ht : t ∈ ball (0:ℂ) τ)
    (hz : z ∈ ball a r) (hw : ‖w - z‖ ≤ M * ‖t‖) : w ∈ ball a ρ := by
  have h1 : ‖t‖ < τ := by simpa using ht
  have h2 : dist z a < r := hz
  have h3 : M * ‖t‖ ≤ M * τ := mul_le_mul_of_nonneg_left h1.le h.hM
  rw [mem_ball, dist_eq_norm]
  have : ‖w - a‖ ≤ ‖w - z‖ + ‖z - a‖ := by
    simpa using norm_add_le (w - z) (z - a)
  have h4 := h.hτM; have h5 := h.hrρ; have h6 := h.hρ
  rw [dist_eq_norm] at h2
  nlinarith

/-- Invariant of the iterates on `ball 0 τ × ball a r`. -/
def Inv (F : E → E) (a : E) (M τ r : ℝ) (k : ℕ) : Prop :=
  ∀ t ∈ ball (0:ℂ) τ, ∀ z ∈ ball a r,
    ‖picardIter F k (t, z) - z‖ ≤ M * ‖t‖ ∧
    ∀ t' ∈ ball (0:ℂ) τ, ‖picardIter F k (t, z) - picardIter F k (t', z)‖ ≤ 2 * M * ‖t - t'‖

lemma smul_mem_ball (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {θ : ℝ}
    (hθ : θ ∈ Icc (0:ℝ) 1) : θ • t ∈ ball (0:ℂ) τ := by
  have h1 : ‖t‖ < τ := by simpa using ht
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
  have := h.hτ
  nlinarith [hθ.2, norm_nonneg t]

lemma cont_g (h : PData F a ρ M τ r K) {k : ℕ} (hk : Inv F a M τ r k) {t : ℂ}
    (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    ContinuousOn (fun θ : ℝ => F (picardIter F k (θ • t, z))) (Icc (0:ℝ) 1) := by
  have hLip : LipschitzOnWith (Real.toNNReal (2 * M * ‖t‖)) (fun θ : ℝ => picardIter F k (θ • t, z)) (Icc (0:ℝ) 1) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have := (hk _ (smul_mem_ball h ht hx) z hz).2 _ (smul_mem_ball h ht hy)
    rw [dist_eq_norm, dist_eq_norm]
    refine this.trans ?_
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, Real.coe_toNNReal _ (by have := h.hM; positivity)]
    nlinarith [norm_nonneg t, abs_nonneg (x - y), h.hM]
  have hc : ContinuousOn (fun θ : ℝ => picardIter F k (θ • t, z)) (Icc (0:ℝ) 1) := hLip.continuousOn
  refine h.hFL.continuousOn.comp hc ?_
  intro θ hθ
  exact mem_ball_of_close h (smul_mem_ball h ht hθ) hz ((hk _ (smul_mem_ball h ht hθ) z hz).1)

lemma inv_zero (h : PData F a ρ M τ r K) : Inv F a M τ r 0 := by
  intro t ht z hz
  refine ⟨by simpa [picardIter] using mul_nonneg h.hM (norm_nonneg t), ?_⟩
  intro t' ht'
  simpa [picardIter] using mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h.hM) (norm_nonneg (t - t'))

lemma g_bound (h : PData F a ρ M τ r K) {k : ℕ} (hk : Inv F a M τ r k) {t : ℂ}
    (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    IntervalIntegrable (fun θ : ℝ => F (picardIter F k (θ • t, z))) volume 0 1 ∧
    (∀ θ ∈ Icc (0:ℝ) 1, ‖F (picardIter F k (θ • t, z))‖ ≤ M) ∧
    ‖∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))‖ ≤ M := by
  have hb : ∀ θ ∈ Icc (0:ℝ) 1, ‖F (picardIter F k (θ • t, z))‖ ≤ M := fun θ hθ =>
    h.hFM _ (mem_ball_of_close h (smul_mem_ball h ht hθ) hz ((hk _ (smul_mem_ball h ht hθ) z hz).1))
  refine ⟨(cont_g h hk ht hz).intervalIntegrable_of_Icc zero_le_one, hb, ?_⟩
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (f := fun θ : ℝ => F (picardIter F k (θ • t, z))) (C := M)
    (fun θ hθ => hb θ (by rw [uIoc_of_le zero_le_one] at hθ; exact ⟨hθ.1.le, hθ.2⟩))
  simpa using this

lemma inv_succ (h : PData F a ρ M τ r K) {k : ℕ} (hk : Inv F a M τ r k) : Inv F a M τ r (k+1) := by
  intro t ht z hz
  obtain ⟨hi, hb, hI⟩ := g_bound h hk ht hz
  have ht1 : ‖t‖ < τ := by simpa using ht
  have hstep : picardIter F (k+1) (t, z) = z + t • ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z)) := rfl
  refine ⟨?_, ?_⟩
  · rw [hstep, add_sub_cancel_left, norm_smul]
    nlinarith [norm_nonneg t, norm_nonneg (∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z)))]
  · intro t' ht'
    obtain ⟨hi', hb', hI'⟩ := g_bound h hk ht' hz
    have ht1' : ‖t'‖ < τ := by simpa using ht'
    have hstep' : picardIter F (k+1) (t', z) = z + t' • ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t', z)) := rfl
    have hdiff : ‖(∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) -
        ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t', z))‖ ≤ (K * (2 * M * ‖t - t'‖)) := by
      rw [← intervalIntegral.integral_sub hi hi']
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
        (f := fun θ : ℝ => F (picardIter F k (θ • t, z)) - F (picardIter F k (θ • t', z)))
        (C := K * (2 * M * ‖t - t'‖)) (by
          intro θ hθ
          rw [uIoc_of_le zero_le_one] at hθ
          have hθ' : θ ∈ Icc (0:ℝ) 1 := ⟨hθ.1.le, hθ.2⟩
          have h1 := smul_mem_ball h ht hθ'
          have h2 := smul_mem_ball h ht' hθ'
          have m1 := mem_ball_of_close h h1 hz ((hk _ h1 z hz).1)
          have m2 := mem_ball_of_close h h2 hz ((hk _ h2 z hz).1)
          have := h.hFL.norm_sub_le m1 m2
          refine this.trans ?_
          have h3 := (hk _ h1 z hz).2 _ h2
          have h4 : ‖θ • t - θ • t'‖ ≤ ‖t - t'‖ := by
            rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ'.1]
            nlinarith [norm_nonneg (t - t'), hθ'.2]
          have h5 : (0:ℝ) ≤ K := K.coe_nonneg
          have : ‖picardIter F k (θ • t, z) - picardIter F k (θ • t', z)‖ ≤ 2 * M * ‖t - t'‖ :=
            h3.trans (mul_le_mul_of_nonneg_left h4 (by have := h.hM; positivity))
          exact mul_le_mul_of_nonneg_left this h5)
      simpa using this
    rw [hstep, hstep']
    have e : z + t • (∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) -
        (z + t' • ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t', z))) =
        (t - t') • (∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) +
        t' • ((∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) -
          ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t', z))) := by
      simp only [sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have hK : (0:ℝ) ≤ K := K.coe_nonneg
    have a1 : ‖t - t'‖ * ‖∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))‖ ≤ ‖t - t'‖ * M :=
      mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    have a2 : ‖t'‖ * ‖(∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) -
        ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t', z))‖ ≤ τ * (K * (2 * M * ‖t - t'‖)) :=
      mul_le_mul ht1'.le hdiff (norm_nonneg _) h.hτ.le
    have a3 : τ * (K * (2 * M * ‖t - t'‖)) = (τ * K) * (2 * M * ‖t - t'‖) := by ring
    have a4 : (τ * K) * (2 * M * ‖t - t'‖) ≤ (1/2) * (2 * M * ‖t - t'‖) :=
      mul_le_mul_of_nonneg_right h.hτK (by have := h.hM; positivity)
    nlinarith

lemma inv_all (h : PData F a ρ M τ r K) (k : ℕ) : Inv F a M τ r k := by
  induction k with
  | zero => exact inv_zero h
  | succ k ih => exact inv_succ h ih

lemma contr (h : PData F a ρ M τ r K) (k : ℕ) :
    ∀ t ∈ ball (0:ℂ) τ, ∀ z ∈ ball a r,
      ‖picardIter F (k+1) (t, z) - picardIter F k (t, z)‖ ≤ τ * M / 2 ^ k := by
  induction k with
  | zero =>
    intro t ht z hz
    have h1 := (inv_all h 1 t ht z hz).1
    have ht1 : ‖t‖ < τ := by simpa using ht
    have : M * ‖t‖ ≤ τ * M := by nlinarith [h.hM]
    simpa [picardIter] using h1.trans this
  | succ k ih =>
    intro t ht z hz
    obtain ⟨hi, hb, hI⟩ := g_bound h (inv_all h (k+1)) ht hz
    obtain ⟨hi', hb', hI'⟩ := g_bound h (inv_all h k) ht hz
    have ht1 : ‖t‖ < τ := by simpa using ht
    have e : picardIter F (k+1+1) (t, z) - picardIter F (k+1) (t, z) =
        t • ((∫ θ in (0:ℝ)..1, F (picardIter F (k+1) (θ • t, z))) -
          ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) := by
      show z + t • (∫ θ in (0:ℝ)..1, F (picardIter F (k+1) (θ • t, z))) -
        (z + t • ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) = _
      rw [smul_sub]; abel
    have hdiff : ‖(∫ θ in (0:ℝ)..1, F (picardIter F (k+1) (θ • t, z))) -
        ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))‖ ≤ K * (τ * M / 2 ^ k) := by
      rw [← intervalIntegral.integral_sub hi hi']
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
        (f := fun θ : ℝ => F (picardIter F (k+1) (θ • t, z)) - F (picardIter F k (θ • t, z)))
        (C := K * (τ * M / 2 ^ k)) (by
          intro θ hθ
          rw [uIoc_of_le zero_le_one] at hθ
          have hθ' : θ ∈ Icc (0:ℝ) 1 := ⟨hθ.1.le, hθ.2⟩
          have h1 := smul_mem_ball h ht hθ'
          have m1 := mem_ball_of_close h h1 hz ((inv_all h (k+1) _ h1 z hz).1)
          have m2 := mem_ball_of_close h h1 hz ((inv_all h k _ h1 z hz).1)
          have := h.hFL.norm_sub_le m1 m2
          refine this.trans ?_
          exact mul_le_mul_of_nonneg_left (ih _ h1 z hz) K.coe_nonneg)
      simpa using this
    rw [e, norm_smul]
    have hK : (0:ℝ) ≤ K := K.coe_nonneg
    have hp : (0:ℝ) < 2 ^ k := by positivity
    have a1 : ‖t‖ * ‖(∫ θ in (0:ℝ)..1, F (picardIter F (k+1) (θ • t, z))) -
        ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))‖ ≤ τ * (K * (τ * M / 2 ^ k)) :=
      mul_le_mul ht1.le hdiff (norm_nonneg _) h.hτ.le
    have a2 : τ * (K * (τ * M / 2 ^ k)) = (τ * K) * (τ * M / 2 ^ k) := by ring
    have a3 : (τ * K) * (τ * M / 2 ^ k) ≤ (1/2) * (τ * M / 2 ^ k) :=
      mul_le_mul_of_nonneg_right h.hτK (by have := h.hM; have := h.hτ; positivity)
    have a4 : τ * M / 2 ^ (k+1) = (1/2) * (τ * M / 2 ^ k) := by rw [pow_succ]; field_simp
    rw [a4]; linarith

/-- Riemann sums of a Lipschitz function. -/
lemma riemann (g : ℝ → E) (Λ : ℝ) (hc : ContinuousOn g (Icc (0:ℝ) 1))
    (hg : ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, ‖g x - g y‖ ≤ Λ * |x - y|)
    (N : ℕ) (hN : 0 < N) :
    ‖(∫ θ in (0:ℝ)..1, g θ) - (1 / (N:ℝ)) • ∑ j ∈ Finset.range N, g ((j:ℝ) / N)‖ ≤ Λ / N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hΛ : 0 ≤ Λ := by
    have := hg 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    simp at this
    exact (norm_nonneg _).trans this
  have hpt : ∀ j : ℕ, j ≤ N → (j:ℝ) / N ∈ Icc (0:ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNpos]; exact_mod_cast hj
  have hII : ∀ j ∈ Finset.range N, IntervalIntegrable g volume ((j:ℝ) / N) (((j+1 : ℕ):ℝ) / N) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 := hpt j hj'.le
    have h2 := hpt (j+1) hj'
    refine (hc.intervalIntegrable_of_Icc zero_le_one).mono_set ?_
    rw [uIcc_of_le zero_le_one]
    intro x hx
    rw [uIcc_of_le (by have : (j:ℝ) ≤ ((j+1:ℕ):ℝ) := by exact_mod_cast Nat.le_succ j
                       exact div_le_div_of_nonneg_right this hNpos.le)] at hx
    exact ⟨h1.1.trans hx.1, hx.2.trans h2.2⟩
  have hsplit : (∫ θ in (0:ℝ)..1, g θ) = ∑ j ∈ Finset.range N,
      ∫ θ in ((j:ℝ) / N)..(((j+1 : ℕ):ℝ) / N), g θ := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun j : ℕ => (j:ℝ) / N) (n := N) (fun k hk => hII k (Finset.mem_range.2 hk))
    have e0 : ((0:ℕ):ℝ) / N = 0 := by simp
    have e1 : ((N:ℕ):ℝ) / N = 1 := div_self hNpos.ne'
    simp only [e0, e1] at this
    exact this.symm
  have hsm : (1 / (N:ℝ)) • ∑ j ∈ Finset.range N, g ((j:ℝ) / N) =
      ∑ j ∈ Finset.range N, ((((j+1 : ℕ):ℝ) / N - (j:ℝ) / N) • g ((j:ℝ) / N)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast; field_simp; ring
  rw [hsplit, hsm, ← Finset.sum_sub_distrib]
  have hterm : ∀ j ∈ Finset.range N, ‖(∫ θ in ((j:ℝ) / N)..(((j+1 : ℕ):ℝ) / N), g θ) -
      ((((j+1 : ℕ):ℝ) / N - (j:ℝ) / N) • g ((j:ℝ) / N))‖ ≤ Λ / (N:ℝ)^2 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 := hpt j hj'.le
    have h2 := hpt (j+1) hj'
    have hjl : (j:ℝ) / N ≤ ((j+1:ℕ):ℝ) / N :=
      div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hNpos.le
    have hw : ((j+1 : ℕ):ℝ) / N - (j:ℝ) / N = 1 / N := by push_cast; field_simp; ring
    have e : (∫ θ in ((j:ℝ) / N)..(((j+1 : ℕ):ℝ) / N), g θ) -
        ((((j+1 : ℕ):ℝ) / N - (j:ℝ) / N) • g ((j:ℝ) / N)) =
        ∫ θ in ((j:ℝ) / N)..(((j+1 : ℕ):ℝ) / N), (g θ - g ((j:ℝ) / N)) := by
      rw [intervalIntegral.integral_sub (hII j hj) intervalIntegrable_const,
        intervalIntegral.integral_const]
    rw [e]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (j:ℝ) / N)
      (b := ((j+1 : ℕ):ℝ) / N) (f := fun θ => g θ - g ((j:ℝ) / N)) (C := Λ / N) (by
        intro x hx
        rw [uIoc_of_le hjl] at hx
        have hx' : x ∈ Icc (0:ℝ) 1 := ⟨h1.1.trans hx.1.le, hx.2.trans h2.2⟩
        refine (hg x hx' _ h1).trans ?_
        have : |x - (j:ℝ) / N| ≤ 1 / N := by
          rw [abs_of_nonneg (by linarith [hx.1])]
          linarith [hx.2]
        calc Λ * |x - (j:ℝ) / N| ≤ Λ * (1 / N) := mul_le_mul_of_nonneg_left this hΛ
          _ = Λ / N := by ring)
    refine this.trans ?_
    rw [abs_of_nonneg (by linarith), hw]
    apply le_of_eq; field_simp
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  apply le_of_eq; field_simp

/-- General theorem shape (b1): a `ℂ`-differentiable map on an open subset of `ℂ × E` is analytic. -/
def HolAnalyticProp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ {U : Set (ℂ × E)} {f : ℂ × E → E}, IsOpen U → DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U

/-- General theorem shape (b2): a uniform limit of analytic maps on an open subset of `ℂ × E`
is analytic. -/
def UniformLimitAnalyticProp (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ {U : Set (ℂ × E)} {f : ℕ → ℂ × E → E} {g : ℂ × E → E}, IsOpen U →
    (∀ n, AnalyticOnNhd ℂ (f n) U) → TendstoUniformlyOn f g atTop U → AnalyticOnNhd ℂ g U

/-- the Riemann sum approximants of the next Picard iterate -/
def riemannApprox (F : E → E) (k n : ℕ) (p : ℂ × E) : E :=
  p.2 + p.1 • ((1 / ((n + 1 : ℕ) : ℝ)) • ∑ j ∈ Finset.range (n + 1),
    F (picardIter F k ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2)))

lemma riemannApprox_diff (h : PData F a ρ M τ r K) {k : ℕ}
    (hk : DifferentiableOn ℂ (picardIter F k) (ball (0:ℂ) τ ×ˢ ball a r)) (n : ℕ) :
    DifferentiableOn ℂ (riemannApprox F k n) (ball (0:ℂ) τ ×ˢ ball a r) := by
  have hinner : ∀ j ∈ Finset.range (n+1), DifferentiableOn ℂ (fun p : ℂ × E =>
      F (picardIter F k ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2)))
      (ball (0:ℂ) τ ×ˢ ball a r) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hc : ((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) ∈ Icc (0:ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]; exact_mod_cast hj'.le
    have hφ : DifferentiableOn ℂ (fun p : ℂ × E => ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2))
        (ball (0:ℂ) τ ×ˢ ball a r) := by
      simp only [Complex.real_smul]
      fun_prop
    have hmaps : MapsTo (fun p : ℂ × E => ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2))
        (ball (0:ℂ) τ ×ˢ ball a r) (ball (0:ℂ) τ ×ˢ ball a r) := fun p hp =>
      ⟨smul_mem_ball h hp.1 hc, hp.2⟩
    refine h.hFd.comp (hk.comp hφ hmaps) ?_
    intro p hp
    have hp' := hmaps hp
    exact mem_ball_of_close h hp'.1 hp'.2 ((inv_all h k _ hp'.1 _ hp'.2).1)
  unfold riemannApprox
  refine differentiableOn_snd.add (differentiableOn_fst.smul ?_)
  have hs : DifferentiableOn ℂ (fun p : ℂ × E => ∑ j ∈ Finset.range (n + 1),
      F (picardIter F k ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • p.1, p.2))) (ball (0:ℂ) τ ×ˢ ball a r) :=
    DifferentiableOn.fun_sum hinner
  exact hs.const_smul (1 / ((n + 1 : ℕ) : ℝ))

lemma riemannApprox_tendsto (h : PData F a ρ M τ r K) (k : ℕ) :
    TendstoUniformlyOn (fun n => riemannApprox F k n) (picardIter F (k+1)) atTop
      (ball (0:ℂ) τ ×ˢ ball a r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set Λ : ℝ := K * (2 * M * τ) with hΛ
  have hΛ0 : 0 ≤ Λ := by have := h.hM; have := h.hτ; positivity
  obtain ⟨m, hm⟩ := exists_nat_gt (τ * Λ / ε)
  filter_upwards [eventually_ge_atTop m] with n hn
  rintro ⟨t, z⟩ hp
  obtain ⟨ht, hz⟩ := hp
  have ht1 : ‖t‖ < τ := by simpa using ht
  have hN : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hcont := cont_g h (inv_all h k) ht hz
  have hriem := riemann (fun θ : ℝ => F (picardIter F k (θ • t, z))) Λ hcont (by
    intro x hx y hy
    have m1 := mem_ball_of_close h (smul_mem_ball h ht hx) hz ((inv_all h k _ (smul_mem_ball h ht hx) z hz).1)
    have m2 := mem_ball_of_close h (smul_mem_ball h ht hy) hz ((inv_all h k _ (smul_mem_ball h ht hy) z hz).1)
    refine (h.hFL.norm_sub_le m1 m2).trans ?_
    have h3 := (inv_all h k _ (smul_mem_ball h ht hx) z hz).2 _ (smul_mem_ball h ht hy)
    have h4 : ‖x • t - y • t‖ = |x - y| * ‖t‖ := by
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    rw [h4] at h3
    have : ‖picardIter F k (x • t, z) - picardIter F k (y • t, z)‖ ≤ 2 * M * τ * |x - y| := by
      refine h3.trans ?_
      have := h.hM
      nlinarith [abs_nonneg (x - y), mul_nonneg this (abs_nonneg (x - y))]
    calc (K:ℝ) * ‖picardIter F k (x • t, z) - picardIter F k (y • t, z)‖
        ≤ K * (2 * M * τ * |x - y|) := mul_le_mul_of_nonneg_left this K.coe_nonneg
      _ = Λ * |x - y| := by rw [hΛ]; ring) (n+1) (Nat.succ_pos n)
  have hdist : ‖picardIter F (k+1) (t, z) - riemannApprox F k n (t, z)‖ ≤ τ * (Λ / ((n + 1 : ℕ) : ℝ)) := by
    have e : picardIter F (k+1) (t, z) - riemannApprox F k n (t, z) =
        t • ((∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) -
          (1 / ((n + 1 : ℕ) : ℝ)) • ∑ j ∈ Finset.range (n + 1),
            F (picardIter F k ((((j : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) • t, z))) := by
      show z + t • (∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) - (z + t • _) = _
      rw [smul_sub]; abel
    rw [e, norm_smul]
    exact mul_le_mul ht1.le hriem (norm_nonneg _) h.hτ.le
  rw [dist_eq_norm]
  refine hdist.trans_lt ?_
  have hnm : (m:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    have : m ≤ n + 1 := by omega
    exact_mod_cast this
  have h1 : τ * Λ / ε < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hm hnm
  rw [div_lt_iff₀ hε] at h1
  rw [← mul_div_assoc, div_lt_iff₀ hN]
  linarith

lemma diff_iter (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) (k : ℕ) :
    DifferentiableOn ℂ (picardIter F k) (ball (0:ℂ) τ ×ˢ ball a r) := by
  induction k with
  | zero => exact differentiableOn_snd
  | succ k ih =>
    have hU : IsOpen (ball (0:ℂ) τ ×ˢ ball a r) := isOpen_ball.prod isOpen_ball
    exact (hLim hU (fun n => hHol hU (riemannApprox_diff h ih n)) (riemannApprox_tendsto h k)).differentiableOn

/-- The limit of the Picard iterates. -/
def picardLim (F : E → E) (p : ℂ × E) : E := limUnder atTop (fun k => picardIter F k p)

lemma tendsto_iter (h : PData F a ρ M τ r K) {p : ℂ × E}
    (hp : p ∈ ball (0:ℂ) τ ×ˢ ball a r) :
    Tendsto (fun k => picardIter F k p) atTop (𝓝 (picardLim F p)) := by
  obtain ⟨t, z⟩ := p
  have hc : CauchySeq (fun k => picardIter F k (t, z)) := by
    refine cauchySeq_of_le_geometric_two (C := 2 * (τ * M)) (fun n => ?_)
    rw [dist_comm, dist_eq_norm]
    have := contr h n t hp.1 z hp.2
    refine this.trans (le_of_eq ?_)
    ring
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete hc)

lemma dist_iter_lim (h : PData F a ρ M τ r K) {p : ℂ × E}
    (hp : p ∈ ball (0:ℂ) τ ×ˢ ball a r) (n : ℕ) :
    dist (picardIter F n p) (picardLim F p) ≤ 2 * (τ * M) / 2 ^ n := by
  obtain ⟨t, z⟩ := p
  refine dist_le_of_le_geometric_two_of_tendsto (C := 2 * (τ * M)) (f := fun k => picardIter F k (t, z))
    (fun n => ?_) (tendsto_iter h hp) n
  rw [dist_comm, dist_eq_norm]
  have := contr h n t hp.1 z hp.2
  refine this.trans (le_of_eq ?_)
  ring

lemma tendstoU_iter (h : PData F a ρ M τ r K) :
    TendstoUniformlyOn (fun k => picardIter F k) (picardLim F) atTop
      (ball (0:ℂ) τ ×ˢ ball a r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 2 * (τ * M) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul (2 * (τ * M))
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn p hp
  rw [dist_comm]
  refine lt_of_le_of_lt (dist_iter_lim h hp n) ?_
  simpa [div_eq_mul_inv, one_div, inv_pow] using hn

lemma lim_close (h : PData F a ρ M τ r K) {t : ℂ} {z : E} (ht : t ∈ ball (0:ℂ) τ)
    (hz : z ∈ ball a r) : ‖picardLim F (t, z) - z‖ ≤ M * ‖t‖ := by
  have hT := (tendsto_iter h (p := (t, z)) ⟨ht, hz⟩).sub_const z
  exact le_of_tendsto' hT.norm (fun k => (inv_all h k t ht z hz).1)

lemma lim_zero (h : PData F a ρ M τ r K) {z : E} (hz : z ∈ ball a r) :
    picardLim F (0, z) = z := by
  have h0 : ∀ k, picardIter F k (0, z) = z := by
    intro k
    have := (inv_all h k 0 (mem_ball_self h.hτ) z hz).1
    simp at this
    exact sub_eq_zero.mp this
  have := tendsto_iter h (p := (0, z)) ⟨mem_ball_self h.hτ, hz⟩
  simp only [h0] at this
  exact tendsto_nhds_unique this tendsto_const_nhds

lemma lim_analytic (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) :
    AnalyticOnNhd ℂ (picardLim F) (ball (0:ℂ) τ ×ˢ ball a r) := by
  have hU : IsOpen (ball (0:ℂ) τ ×ˢ ball a r) := isOpen_ball.prod isOpen_ball
  exact hLim hU (fun k => hHol hU (diff_iter hHol hLim h k)) (tendstoU_iter h)

lemma lim_mem (h : PData F a ρ M τ r K) {t : ℂ} {z : E} (ht : t ∈ ball (0:ℂ) τ)
    (hz : z ∈ ball a r) : picardLim F (t, z) ∈ ball a ρ :=
  mem_ball_of_close h ht hz (lim_close h ht hz)

lemma cont_lim_ray (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    ContinuousOn (fun θ : ℝ => F (picardLim F (θ • t, z))) {θ : ℝ | θ • t ∈ ball (0:ℂ) τ} := by
  have h1 : ContinuousOn (fun θ : ℝ => picardLim F (θ • t, z)) {θ : ℝ | θ • t ∈ ball (0:ℂ) τ} := by
    refine (lim_analytic hHol hLim h).continuousOn.comp ?_ (fun θ hθ => ⟨hθ, hz⟩)
    fun_prop
  exact h.hFL.continuousOn.comp h1 (fun θ hθ => lim_mem h hθ hz)

/-- The integral equation for the limit. -/
lemma lim_integral_eq (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) {t : ℂ} {z : E} (ht : t ∈ ball (0:ℂ) τ) (hz : z ∈ ball a r) :
    picardLim F (t, z) = z + t • ∫ θ in (0:ℝ)..1, F (picardLim F (θ • t, z)) := by
  have hI : ∀ θ ∈ Icc (0:ℝ) 1, θ • t ∈ ball (0:ℂ) τ := fun θ hθ => smul_mem_ball h ht hθ
  have hcL := (cont_lim_ray hHol hLim h ht hz).mono (fun θ hθ => hI θ hθ)
  have hiL : IntervalIntegrable (fun θ : ℝ => F (picardLim F (θ • t, z))) volume 0 1 :=
    hcL.intervalIntegrable_of_Icc zero_le_one
  set I : E := ∫ θ in (0:ℝ)..1, F (picardLim F (θ • t, z)) with hIdef
  have hIk : Tendsto (fun k => ∫ θ in (0:ℝ)..1, F (picardIter F k (θ • t, z))) atTop (𝓝 I) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => K * (2 * (τ * M) / 2 ^ n)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1/2:ℝ) < 1)).const_mul (K * (2 * (τ * M)))
      simpa [div_eq_mul_inv, one_div, inv_pow, mul_assoc] using this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
    obtain ⟨hik, hbk, _⟩ := g_bound h (inv_all h k) ht hz
    rw [← intervalIntegral.integral_sub hik hiL]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (f := fun θ : ℝ => F (picardIter F k (θ • t, z)) - F (picardLim F (θ • t, z)))
      (C := K * (2 * (τ * M) / 2 ^ k)) (by
        intro θ hθ
        rw [uIoc_of_le zero_le_one] at hθ
        have hθ' : θ ∈ Icc (0:ℝ) 1 := ⟨hθ.1.le, hθ.2⟩
        have h1 := hI θ hθ'
        have m1 := mem_ball_of_close h h1 hz ((inv_all h k _ h1 z hz).1)
        have m2 := lim_mem h h1 hz
        refine (h.hFL.norm_sub_le m1 m2).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ K.coe_nonneg
        have := dist_iter_lim h (p := (θ • t, z)) ⟨h1, hz⟩ k
        rwa [dist_eq_norm] at this)
    simpa using this
  have hA : Tendsto (fun k => picardIter F (k+1) (t, z)) atTop (𝓝 (picardLim F (t, z))) :=
    (tendsto_add_atTop_iff_nat (f := fun k => picardIter F k (t, z)) 1).2 (tendsto_iter h ⟨ht, hz⟩)
  have hB : Tendsto (fun k => picardIter F (k+1) (t, z)) atTop (𝓝 (z + t • I)) :=
    (tendsto_const_nhds.add (hIk.const_smul t))
  exact tendsto_nhds_unique hA hB

lemma lim_analyticAt_slice (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) {s : ℂ} (hs : s ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    AnalyticAt ℂ (fun s : ℂ => picardLim F (s, z)) s := by
  have h1 := lim_analytic hHol hLim h (s, z) ⟨hs, hz⟩
  have h2 : AnalyticAt ℂ (fun s : ℂ => (s, z)) s := by fun_prop
  exact h1.comp_of_eq h2 rfl

lemma deriv_eq_of_ne (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) (ht0 : t ≠ 0) {z : E}
    (hz : z ∈ ball a r) :
    deriv (fun s : ℂ => picardLim F (s, z)) t = F (picardLim F (t, z)) := by
  set φ : ℂ → E := fun s => picardLim F (s, z) with hφ
  have hd : HasDerivAt φ (deriv φ t) t := (lim_analyticAt_slice hHol hLim h ht hz).differentiableAt.hasDerivAt
  set W : Set ℝ := {σ : ℝ | σ • t ∈ ball (0:ℂ) τ} with hW
  have hWo : IsOpen W := isOpen_ball.preimage (by fun_prop)
  have h1W : (1:ℝ) ∈ W := by simpa [hW] using ht
  set G : ℝ → E := fun σ => F (picardLim F (σ • t, z)) with hG
  have hGc : ContinuousOn G W := cont_lim_ray hHol hLim h ht hz
  have hGi : IntervalIntegrable G volume 0 1 := by
    refine (hGc.mono ?_).intervalIntegrable_of_Icc zero_le_one
    intro θ hθ; exact smul_mem_ball h ht hθ
  have hint : HasDerivAt (fun ρ : ℝ => ∫ σ in (0:ℝ)..ρ, G σ) (G 1) 1 :=
    intervalIntegral.integral_hasDerivAt_right hGi
      (hGc.stronglyMeasurableAtFilter hWo 1 h1W) (hGc.continuousAt (hWo.mem_nhds h1W))
  have hR : HasDerivAt (fun ρ : ℝ => z + t • ∫ σ in (0:ℝ)..ρ, G σ) (t • G 1) 1 :=
    (hint.const_smul t).const_add z
  have hh : HasDerivAt (fun ρ : ℝ => ρ • t) t 1 := by
    simpa using (hasDerivAt_id (1:ℝ)).smul_const t
  have hd' : HasDerivAt φ (deriv φ t) ((fun ρ : ℝ => ρ • t) 1) := by simpa using hd
  have hψ : HasDerivAt (φ ∘ fun ρ : ℝ => ρ • t) (t • deriv φ t) 1 := hd'.scomp (1:ℝ) hh
  have hev : (φ ∘ fun ρ : ℝ => ρ • t) =ᶠ[𝓝 (1:ℝ)] fun ρ : ℝ => z + t • ∫ σ in (0:ℝ)..ρ, G σ := by
    filter_upwards [hWo.mem_nhds h1W, Ioi_mem_nhds (zero_lt_one : (0:ℝ) < 1)] with ρ hρW hρ0
    have hρ0' : (0:ℝ) < ρ := hρ0
    have heq := lim_integral_eq hHol hLim h hρW hz
    simp only [Function.comp, hφ]
    rw [heq]
    have hcomp : (∫ θ in (0:ℝ)..1, F (picardLim F (θ • ρ • t, z))) =
        ρ⁻¹ • ∫ σ in (0:ℝ)..ρ, G σ := by
      have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1) G (c := ρ) hρ0'.ne'
      simp only [mul_zero, mul_one] at this
      rw [← this]
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [hG]
      rw [smul_smul, mul_comm]
    rw [hcomp]
    congr 1
    rw [smul_assoc, smul_comm t ρ⁻¹, smul_smul, mul_inv_cancel₀ hρ0'.ne', one_smul]
  have hψ2 : HasDerivAt (φ ∘ fun ρ : ℝ => ρ • t) (t • G 1) 1 := hR.congr_of_eventuallyEq hev
  have := hψ.unique hψ2
  have hG1 : G 1 = F (picardLim F (t, z)) := by simp [hG]
  rw [hG1] at this
  exact smul_right_injective E ht0 this

lemma deriv_eq (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    deriv (fun s : ℂ => picardLim F (s, z)) t = F (picardLim F (t, z)) := by
  by_cases ht0 : t = 0
  · subst ht0
    set φ : ℂ → E := fun s => picardLim F (s, z) with hφ
    have hA : AnalyticAt ℂ φ 0 := lim_analyticAt_slice hHol hLim h ht hz
    have h1 : Tendsto (deriv φ) (𝓝[≠] (0:ℂ)) (𝓝 (deriv φ 0)) :=
      (hA.deriv.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun s => F (φ s)) (𝓝[≠] (0:ℂ)) (𝓝 (F (φ 0))) := by
      have hFc : ContinuousAt F (φ 0) :=
        h.hFL.continuousOn.continuousAt (isOpen_ball.mem_nhds (lim_mem h ht hz))
      exact (hFc.comp hA.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
    have h3 : deriv φ =ᶠ[𝓝[≠] (0:ℂ)] fun s => F (φ s) := by
      have : ∀ᶠ s in 𝓝 (0:ℂ), s ∈ ball (0:ℂ) τ := isOpen_ball.mem_nhds ht
      filter_upwards [nhdsWithin_le_nhds this, self_mem_nhdsWithin] with s hs hs0
      exact deriv_eq_of_ne hHol hLim h hs hs0 hz
    exact tendsto_nhds_unique_of_eventuallyEq h1 h2 h3
  · exact deriv_eq_of_ne hHol hLim h ht ht0 hz

lemma lim_hasDerivAt (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (h : PData F a ρ M τ r K) {t : ℂ} (ht : t ∈ ball (0:ℂ) τ) {z : E} (hz : z ∈ ball a r) :
    HasDerivAt (fun s : ℂ => picardLim F (s, z)) (F (picardLim F (t, z))) t := by
  have := (lim_analyticAt_slice hHol hLim h ht hz).differentiableAt.hasDerivAt
  rwa [deriv_eq hHol hLim h ht hz] at this

lemma exists_pdata (hF : AnalyticAt ℂ F a) :
    ∃ (ρ M τ r : ℝ) (K : NNReal), PData F a ρ M τ r K := by
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 hF.eventually_analyticAt
  obtain ⟨K, s, hs, hL⟩ := hF.contDiffAt.exists_lipschitzOnWith
  obtain ⟨ε', hε', hε's⟩ := Metric.mem_nhds_iff.1 hs
  set ρ : ℝ := min ε ε' with hρ
  have hρ0 : 0 < ρ := lt_min hε hε'
  have hb1 : ball a ρ ⊆ ball a ε := ball_subset_ball (min_le_left _ _)
  have hb2 : ball a ρ ⊆ ball a ε' := ball_subset_ball (min_le_right _ _)
  have hKnn : (0:ℝ) ≤ K := K.coe_nonneg
  set M : ℝ := ‖F a‖ + K * ρ with hM
  have hM0 : 0 ≤ M := by positivity
  set τ : ℝ := min (ρ / (4 * (M + 1))) (1 / (2 * ((K:ℝ) + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by positivity) (by positivity)
  refine ⟨ρ, M, τ, ρ / 2, K, ?_⟩
  have hLip : LipschitzOnWith K F (ball a ρ) := hL.mono (hb2.trans hε's)
  refine ⟨hρ0, fun x hx => (hεs x (hb1 hx)).differentiableAt.differentiableWithinAt, hLip, ?_, hM0, hτ0,
    by positivity, le_rfl, ?_, ?_⟩
  · intro x hx
    have h1 := hLip.dist_le_mul x hx a (mem_ball_self hρ0)
    rw [dist_eq_norm] at h1
    have h2 : dist x a < ρ := hx
    have h3 : ‖F x‖ ≤ ‖F a‖ + ‖F x - F a‖ := by simpa using norm_add_le (F a) (F x - F a)
    nlinarith
  · have h1 : τ ≤ ρ / (4 * (M + 1)) := min_le_left _ _
    have h2 : τ * (M + 1) ≤ ρ / 4 := by
      calc τ * (M + 1) ≤ ρ / (4 * (M + 1)) * (M + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ρ / 4 := by field_simp
    nlinarith
  · have h1 : τ ≤ 1 / (2 * ((K:ℝ) + 1)) := min_le_right _ _
    have h2 : τ * ((K:ℝ) + 1) ≤ 1 / 2 := by
      calc τ * ((K:ℝ) + 1) ≤ 1 / (2 * ((K:ℝ) + 1)) * ((K:ℝ) + 1) := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 1 / 2 := by field_simp
    nlinarith

/-- **L1** (conditional on the two general analyticity theorems `hHol`, `hLim`): local complex
analytic flow of an analytic vector field on a complex Banach space; head text of Pro round 14 S4
with the two extra hypotheses. -/
theorem exists_local_complex_analytic_flow_of_hyp
    (hHol : HolAnalyticProp E) (hLim : UniformLimitAnalyticProp E)
    (F : E → E) (a : E) (hF : AnalyticAt ℂ F a) :
  ∃ (tau r : ℝ) (Phi : ℂ × E → E),
    0 < tau ∧ 0 < r ∧
    AnalyticOnNhd ℂ Phi
      (Metric.ball (0 : ℂ) tau ×ˢ Metric.ball a r) ∧
    (∀ z : E, z ∈ Metric.ball a r → Phi (0, z) = z) ∧
    ∀ (t : ℂ) (z : E), t ∈ Metric.ball (0 : ℂ) tau →
      z ∈ Metric.ball a r →
      HasDerivAt (fun s : ℂ => Phi (s, z)) (F (Phi (t, z))) t := by
  obtain ⟨ρ, M, τ, r, K, h⟩ := exists_pdata hF
  exact ⟨τ, r, picardLim F, h.hτ, h.hr, lim_analytic hHol hLim h, fun z hz => lim_zero h hz,
    fun t z ht hz => lim_hasDerivAt hHol hLim h ht hz⟩

end
end NlsGge.Atomic.G1081S4Picard
