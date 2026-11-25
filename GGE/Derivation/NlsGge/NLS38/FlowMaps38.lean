import NlsGge.NLS38.StabilityHm38
import NlsGge.NLS38.GlobalH1_38

/-! # GWP piece A9: the solution map `nlsFlowSeq` on sequences, group law, continuity, Lipschitz bounds

Plan: `campaign/GWP_PLAN.md` §6.1 and §7, piece A9.

* `nlsFlowSeq t x` is the value at time `t` of the unique `IsNLSSol` through `x` (A8), and `x`
  itself if `x ∉ h¹` (junk branch).
* `nlsFlowSeq_spec` (an `h¹` datum gives an `IsNLSSol` curve), `nlsFlowSeq_eq_of_sol` (every
  `IsNLSSol` is the flow of its datum, by `nls_unique`), `nlsFlowSeq_zero`, `nlsFlowSeq_add`
  (time shift `isNLSSol_shift` plus uniqueness), `nlsFlowSeq_mem` (persistence of `h^m`).
* `nlsFlowC`, `nlsFlowC_lipschitzOn` (a ball of `h^m` has a fixed `Bx` bound, so the flow on it is
  the cutoff flow with fixed `R`; A6b), `continuous_nlsFlowC_uncurry`, `nlsFlowSeq_refl`,
  `nlsFlowSeq_planeWave`.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Set Filter Topology
open scoped ComplexConjugate NNReal

open scoped Classical in
/-- The solution map: the value at time `t` of the (unique, A8) `IsNLSSol` through `x`;
`x` itself if there is none (`x ∉ h¹`). -/
def nlsFlowSeq (t : ℝ) (x : ℤ → ℂ) : ℤ → ℂ :=
  if h : ∃ u, IsNLSSol u ∧ u 0 = x then (Classical.choose h) t else x

/-! ## Spec, group law -/

theorem nlsFlowSeq_spec (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    IsNLSSol (fun t => nlsFlowSeq t x) ∧ nlsFlowSeq 0 x = x := by
  have h : ∃ u, IsNLSSol u ∧ u 0 = x := nls_exists x hx
  have hc := Classical.choose_spec h
  have e : (fun t => nlsFlowSeq t x) = Classical.choose h := by
    funext t; simp [nlsFlowSeq, h]
  rw [e]
  refine ⟨hc.1, ?_⟩
  simp only [nlsFlowSeq, h, dite_true]
  exact hc.2

theorem exists_sol_iff38 (x : ℤ → ℂ) :
    (∃ u, IsNLSSol u ∧ u 0 = x) ↔ x ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
  ⟨fun ⟨_, hu, h0⟩ => h0 ▸ hu.mem 0, nls_exists x⟩

theorem nlsFlowSeq_of_not_h1 (t : ℝ) {x : ℤ → ℂ} (hx : x ∉ seqSobolev38 ((1 : ℕ) : ℝ)) :
    nlsFlowSeq t x = x := by
  have h : ¬ ∃ u, IsNLSSol u ∧ u 0 = x := fun h => hx ((exists_sol_iff38 x).1 h)
  simp [nlsFlowSeq, h]

theorem nlsFlowSeq_zero (x : ℤ → ℂ) : nlsFlowSeq 0 x = x := by
  by_cases hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)
  · exact (nlsFlowSeq_spec x hx).2
  · exact nlsFlowSeq_of_not_h1 0 hx

/-- Every `IsNLSSol` is the flow of its datum (uniqueness, A8). -/
theorem nlsFlowSeq_eq_of_sol {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u) (t : ℝ) :
    nlsFlowSeq t (u 0) = u t := by
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec (u 0) (hu.mem 0)
  have := nls_unique hs hu (by simpa using h0)
  exact congrFun this t

theorem nlsFlowSeq_add (s t : ℝ) (x : ℤ → ℂ) :
    nlsFlowSeq (s + t) x = nlsFlowSeq s (nlsFlowSeq t x) := by
  by_cases hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)
  · obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx
    have hw := isNLSSol_shift hs t
    have h := nlsFlowSeq_eq_of_sol hw s
    simp only [zero_add] at h
    rw [h, add_comm]
  · rw [nlsFlowSeq_of_not_h1 _ hx, nlsFlowSeq_of_not_h1 _ hx, nlsFlowSeq_of_not_h1 _ hx]

/-! ## Persistence -/

theorem Bx_le_of_hn_le38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) {ρ : ℝ}
    (hρ : hn 1 x ≤ ρ) :
    Bx x ≤ Real.sqrt (ρ ^ 2 + C1 ^ 2 * ρ ^ 4 / (4 * Real.pi ^ 2)) := by
  unfold Bx
  apply Real.sqrt_le_sqrt
  have h0 := hn_nonneg38 1 x
  have h1 : hn 1 x ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ h0 hρ 2
  have h2 : hn 1 x ^ 4 ≤ ρ ^ 4 := pow_le_pow_left₀ h0 hρ 4
  have hq := quart_le hx
  have hpi : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have hs := hn_one_sq hx
  rw [ham_def]
  have e : mass x + (kin x + quart x) / (4 * Real.pi ^ 2) =
      hn 1 x ^ 2 + quart x / (4 * Real.pi ^ 2) := by rw [hs]; ring
  rw [e]
  have hC : 0 ≤ C1 ^ 2 := sq_nonneg _
  have : quart x / (4 * Real.pi ^ 2) ≤ C1 ^ 2 * ρ ^ 4 / (4 * Real.pi ^ 2) :=
    div_le_div_of_nonneg_right (hq.trans (mul_le_mul_of_nonneg_left h2 hC)) hpi.le
  linarith

theorem nlsSol_isCutSol38 {u : ℝ → ℤ → ℂ} (hu : IsNLSSol u) {R : ℝ} (hR : Bx (u 0) ≤ R) :
    IsCutSol R u :=
  isCutSol_of_nlsSol hu fun s => by
    have h := hn_le_Bx38 (hu.mem s)
    have : Bx (u s) = Bx (u 0) := by
      unfold Bx; rw [(nls_conserved hu s).1, (nls_conserved hu s).2]
    linarith

theorem flow_isCutSolM38 (m : ℕ) (hm : 1 ≤ m) {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 (m : ℝ))
    {R : ℝ} (hR : Bx x + 2 ≤ R) :
    IsCutSolM m R (fun t => nlsFlowSeq t x) := by
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) :=
    seqSobolev38_mono (by exact_mod_cast hm) hx
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx1
  have hR0 : 0 < R := by linarith [Bx_nonneg38 x]
  have hcut : IsCutSol R (fun t => nlsFlowSeq t x) :=
    nlsSol_isCutSol38 hs (by simp only [h0]; linarith)
  obtain ⟨C, _, hC⟩ := cutSol_persistence m hm
  exact (hC R hR0 _ hcut (by simp only [h0]; exact hx)).1

theorem nlsFlowSeq_mem (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    ∀ x ∈ seqSobolev38 (m : ℝ), nlsFlowSeq t x ∈ seqSobolev38 (m : ℝ) := fun _ hx =>
  (flow_isCutSolM38 m hm hx (le_refl _)).mem t

/-! ## The flow on the carrier -/

def nlsFlowC (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  carrierMap38 _ _ (nlsFlowSeq t) (nlsFlowSeq_mem m hm t)

theorem norm_sub_eq_hn38 (m : ℕ) (x y : SobolevCarrier38 (m : ℝ)) :
    ‖x - y‖ = hn m (fun n => carrierCoe38 (m : ℝ) x n - carrierCoe38 (m : ℝ) y n) := by
  have h := norm_carrierMk38_eq_hn m _ (sub_mem_nat38 m (carrierCoe38_mem _ x) (carrierCoe38_mem _ y))
  rw [← h]
  rfl

theorem nlsFlow_lipschitz_hn38 (m : ℕ) (hm : 1 ≤ m) (ρ T : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℤ → ℂ, x ∈ seqSobolev38 (m : ℝ) → y ∈ seqSobolev38 (m : ℝ) →
      hn m x ≤ ρ → hn m y ≤ ρ → ∀ t : ℝ, |t| ≤ T →
      hn m (fun n => nlsFlowSeq t x n - nlsFlowSeq t y n) ≤
        Real.exp (L * T) * hn m (fun n => x n - y n) := by
  set R : ℝ := Real.sqrt (ρ ^ 2 + C1 ^ 2 * ρ ^ 4 / (4 * Real.pi ^ 2)) + 2 with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨L, hL0, hL⟩ := cutSol_stability_hm m hm R ρ hR
  refine ⟨L, hL0, fun x y hx hy hxρ hyρ t ht => ?_⟩
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) := seqSobolev38_mono (by exact_mod_cast hm) hx
  have hy1 : y ∈ seqSobolev38 ((1 : ℕ) : ℝ) := seqSobolev38_mono (by exact_mod_cast hm) hy
  have hxB : Bx x + 2 ≤ R := by
    have := Bx_le_of_hn_le38 hx1 ((hn_one_le_hn38 m hm x hx).trans hxρ)
    rw [hRdef]; linarith
  have hyB : Bx y + 2 ≤ R := by
    have := Bx_le_of_hn_le38 hy1 ((hn_one_le_hn38 m hm y hy).trans hyρ)
    rw [hRdef]; linarith
  have hu := flow_isCutSolM38 m hm hx hxB
  have hw := flow_isCutSolM38 m hm hy hyB
  have hu1 : IsCutSol R (fun t => nlsFlowSeq t x) := by
    obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx1
    exact nlsSol_isCutSol38 hs (by simp only [h0]; linarith)
  have hw1 : IsCutSol R (fun t => nlsFlowSeq t y) := by
    obtain ⟨hs, h0⟩ := nlsFlowSeq_spec y hy1
    exact nlsSol_isCutSol38 hs (by simp only [h0]; linarith)
  have h := hL _ _ hu1 hw1 (by simp only [nlsFlowSeq_zero]; exact hx)
    (by simp only [nlsFlowSeq_zero]; exact hy) (by simp only [nlsFlowSeq_zero]; exact hxρ)
    (by simp only [nlsFlowSeq_zero]; exact hyρ) t
  simp only [nlsFlowSeq_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (hn_nonneg38 _ _))
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht hL0)

theorem nlsFlowC_lipschitzOn (m : ℕ) (hm : 1 ≤ m) (ρ T : ℝ) :
    ∃ L : ℝ≥0, ∀ t : ℝ, |t| ≤ T →
      LipschitzOnWith L (nlsFlowC m hm t) (Metric.closedBall 0 ρ) := by
  obtain ⟨L, hL0, hL⟩ := nlsFlow_lipschitz_hn38 m hm ρ T
  refine ⟨⟨Real.exp (L * T), (Real.exp_pos _).le⟩, fun t ht => ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [mem_closedBall_zero_iff] at hx hy
  rw [dist_eq_norm, dist_eq_norm, norm_sub_eq_hn38, norm_sub_eq_hn38]
  exact hL _ _ (carrierCoe38_mem _ x) (carrierCoe38_mem _ y) (by rwa [hn_coe38])
    (by rwa [hn_coe38]) t ht

theorem continuous_nlsFlowC_time (m : ℕ) (hm : 1 ≤ m) (x : SobolevCarrier38 (m : ℝ)) :
    Continuous fun t : ℝ => nlsFlowC m hm t x :=
  (flow_isCutSolM38 m hm (carrierCoe38_mem _ x) (le_refl _)).cont

theorem continuous_nlsFlowC_uncurry (m : ℕ) (hm : 1 ≤ m) :
    Continuous fun p : ℝ × SobolevCarrier38 (m : ℝ) => nlsFlowC m hm p.1 p.2 := by
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨t0, x0⟩ := p0
  obtain ⟨L, hL⟩ := nlsFlowC_lipschitzOn m hm (‖x0‖ + 1) (|t0| + 1)
  have hsplit : (fun p : ℝ × SobolevCarrier38 (m : ℝ) => nlsFlowC m hm p.1 p.2) =
      fun p => (nlsFlowC m hm p.1 p.2 - nlsFlowC m hm p.1 x0) + nlsFlowC m hm p.1 x0 := by
    funext p; abel
  show ContinuousAt _ (t0, x0)
  rw [hsplit]
  have h2 : ContinuousAt (fun p : ℝ × SobolevCarrier38 (m : ℝ) => nlsFlowC m hm p.1 x0) (t0, x0) :=
    ((continuous_nlsFlowC_time m hm x0).comp continuous_fst).continuousAt
  have h1 : Tendsto (fun p : ℝ × SobolevCarrier38 (m : ℝ) =>
      nlsFlowC m hm p.1 p.2 - nlsFlowC m hm p.1 x0) (𝓝 (t0, x0)) (𝓝 0) := by
    have hbd : ∀ᶠ p : ℝ × SobolevCarrier38 (m : ℝ) in 𝓝 (t0, x0),
        ‖nlsFlowC m hm p.1 p.2 - nlsFlowC m hm p.1 x0‖ ≤ (L : ℝ) * ‖p.2 - x0‖ := by
      have ht : ∀ᶠ p : ℝ × SobolevCarrier38 (m : ℝ) in 𝓝 (t0, x0), |p.1| ≤ |t0| + 1 := by
        have hc : ContinuousAt (fun p : ℝ × SobolevCarrier38 (m : ℝ) => |p.1|) (t0, x0) :=
          (continuous_abs.comp continuous_fst).continuousAt
        exact hc.eventually (eventually_le_nhds (by linarith))
      have hx : ∀ᶠ p : ℝ × SobolevCarrier38 (m : ℝ) in 𝓝 (t0, x0), ‖p.2 - x0‖ < 1 := by
        have hc : ContinuousAt (fun p : ℝ × SobolevCarrier38 (m : ℝ) => ‖p.2 - x0‖) (t0, x0) :=
          (continuous_norm.comp (continuous_snd.sub continuous_const)).continuousAt
        exact hc.eventually (eventually_lt_nhds (by simp))
      filter_upwards [ht, hx] with p hp1 hp2
      have hmem : p.2 ∈ Metric.closedBall (0 : SobolevCarrier38 (m : ℝ)) (‖x0‖ + 1) := by
        rw [mem_closedBall_zero_iff]
        have := norm_le_insert' p.2 x0
        have h3 := norm_sub_rev p.2 x0
        have := norm_sub_norm_le p.2 x0
        linarith
      have hmem0 : x0 ∈ Metric.closedBall (0 : SobolevCarrier38 (m : ℝ)) (‖x0‖ + 1) := by
        rw [mem_closedBall_zero_iff]; linarith
      have := (hL p.1 hp1).dist_le_mul p.2 hmem x0 hmem0
      rwa [dist_eq_norm, dist_eq_norm] at this
    have hz : Tendsto (fun p : ℝ × SobolevCarrier38 (m : ℝ) => (L : ℝ) * ‖p.2 - x0‖)
        (𝓝 (t0, x0)) (𝓝 0) := by
      have hc : ContinuousAt (fun p : ℝ × SobolevCarrier38 (m : ℝ) => (L : ℝ) * ‖p.2 - x0‖)
          (t0, x0) :=
        (continuous_const.mul (continuous_norm.comp (continuous_snd.sub continuous_const))).continuousAt
      simpa using hc.tendsto
    exact squeeze_zero_norm' hbd hz
  have h3 := h1.add h2.tendsto
  rw [zero_add] at h3
  show Tendsto _ _ (𝓝 (nlsFlowC m hm t0 x0 - nlsFlowC m hm t0 x0 + nlsFlowC m hm t0 x0))
  rwa [sub_self, zero_add]

/-! ## Reflection -/

theorem refl_refl38 (x : ℤ → ℂ) : refl (refl x) = x := by
  funext n; simp [refl]

theorem nlsFlowSeq_refl (t : ℝ) (x : ℤ → ℂ) :
    nlsFlowSeq t (refl x) = refl (nlsFlowSeq t x) := by
  by_cases hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)
  · obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx
    have hr := isNLSSol_refl hs
    have h := nlsFlowSeq_eq_of_sol hr t
    simp only [h0] at h
    exact h
  · have hrx : refl x ∉ seqSobolev38 ((1 : ℕ) : ℝ) := fun h => hx (by
      have := refl_mem_seqSobolev38 h
      rwa [refl_refl38] at this)
    rw [nlsFlowSeq_of_not_h1 _ hx, nlsFlowSeq_of_not_h1 _ hrx]

/-! ## Plane-wave regression -/

theorem nlsFlowSeq_planeWave (t : ℝ) (k : ℤ) (a : ℂ) :
    nlsFlowSeq t (Pi.single k a) =
      Pi.single k (Complex.exp (-(Complex.I * t *
        ((2 * Real.pi * k) ^ 2 + 2 * (‖a‖ : ℂ) ^ 2))) * a) := by
  have h := nlsFlowSeq_eq_of_sol (isNLSSol_planeWave k a) t
  simp only [planeWaveAmp38_zero] at h
  rw [h]
  unfold planeWaveAmp38
  congr 2
  rw [disp_eq]
  push_cast
  ring_nf

end NlsGge.NLS38
