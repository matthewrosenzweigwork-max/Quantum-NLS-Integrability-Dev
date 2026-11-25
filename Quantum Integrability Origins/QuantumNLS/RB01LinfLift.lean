import Mathlib
import QuantumNLS.ComplexifiedSeriesLift

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-18: the `ℓ∞`-analytic lifting principle (source
`collective_actions.tex:405-411`: "All assertions here are uniform bounded holomorphic-family assertions, with
values in `ℓ∞` ... They follow directly from the uniform contour bounds and the Banach-valued Cauchy formula, rather
than from coordinatewise analyticity").  Generic, unconditional.

Direct Bochner integration into `ℓ∞` is not available for the RB01 families (`x ↦ (e^{−2ip_n x})_n` is not strongly
measurable), so the `ℓ∞` power series is built from uniform Cauchy estimates instead:
* `taylor_bound` (Cauchy estimate, infinite-dimensional domain): if `Φ : E → ℂ` is complex analytic on `B(x₀, R)`
  and bounded by `M` there, and `p` is any power series of `Φ` at `x₀`, then `‖p_k(h, …, h)‖ ≤ M (‖h‖/R)^k` for
  every `h` and `Σ_k p_k(h, …, h) = Φ(x₀ + h)` for `‖h‖ < R` (one-variable restriction `t ↦ Φ(x₀ + t h)`,
  uniqueness of one-variable power series, `norm_cauchyPowerSeries_le`, Cauchy–Taylor on the disk);
* `liftCoef`: a uniformly bounded family of real continuous multilinear maps into `ℂ` as one continuous
  multilinear map into `ℓ∞(I)`;
* **`linf_lift`**: a family `(Φ_i)_{i ∈ I}` of maps `E → ℂ`, each complex analytic on the common ball `B(x₀, R)`
  and bounded there by the common constant `M`, defines `G : E → ℓ∞(I)`, `G(x)_i = Φ_i(x)` on `B(x₀, R)`,
  `‖G x‖ ≤ M`, with a complex power series at `x₀` on `B(x₀, R/e)` (symmetrized coordinate series, polarization
  bound `RealAnalyticDef.norm_symC_le`, complex lift `ComplexifiedSeriesLift`); hence `G` is complex analytic on
  `B(x₀, R/e)`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumNLS.RB01LinfLift

open QuantumNLS.ComplexifiedSeriesLift (IsCHom liftC symC_isCHom hasFPowerSeriesOnBall_of_coe_eq)
open QuantumNLS.RealAnalyticDef (symC symC_diag norm_symC_le symSeries hasFPowerSeriesOnBall_symSeries)

/-! ## The Cauchy estimate for a bounded analytic function on a ball -/

section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem taylor_bound {Φ : E → ℂ} {p : FormalMultilinearSeries ℂ E ℂ} {x₀ : E} {R M : ℝ} (hR : 0 < R)
    (han : AnalyticOnNhd ℂ Φ (ball x₀ R)) (hb : ∀ x ∈ ball x₀ R, ‖Φ x‖ ≤ M) (hp : HasFPowerSeriesAt Φ p x₀)
    (h : E) :
    (∀ k : ℕ, ‖p k (fun _ => h)‖ ≤ M * (‖h‖ / R) ^ k) ∧
      (‖h‖ < R → HasSum (fun k : ℕ => p k (fun _ => h)) (Φ (x₀ + h))) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb x₀ (mem_ball_self hR))
  rcases eq_or_ne h 0 with rfl | hh
  · have hz : ∀ k, p k (fun _ => (0 : E)) = if k = 0 then Φ x₀ else 0 := by
      intro k
      rcases k with _ | k
      · simpa using hp.coeff_zero (fun _ => (0 : E))
      · simp only [Nat.succ_ne_zero, if_false]
        exact (p (k + 1)).map_coord_zero 0 rfl
    refine ⟨fun k => ?_, fun _ => ?_⟩
    · rw [hz k]
      split_ifs with hk
      · subst hk; simpa using hb x₀ (mem_ball_self hR)
      · rw [norm_zero, norm_zero, zero_div, zero_pow hk, mul_zero]
    · rw [add_zero]
      convert hasSum_ite_eq 0 (Φ x₀) using 1
      funext k
      rw [hz k]
  -- the one-variable restriction
  have hhn : 0 < ‖h‖ := norm_pos_iff.2 hh
  set ρ := R / ‖h‖ with hρ
  have hρpos : 0 < ρ := div_pos hR hhn
  set φ : ℂ → ℂ := fun t => Φ (x₀ + t • h) with hφ
  have hφd : DifferentiableOn ℂ φ (ball 0 ρ) := by
    intro t ht
    rw [mem_ball_zero_iff] at ht
    have hx : x₀ + t • h ∈ ball x₀ R := by
      rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
      rw [hρ, lt_div_iff₀ hhn] at ht
      exact ht
    have hd : DifferentiableAt ℂ Φ (x₀ + t • h) := (han _ hx).differentiableAt
    exact (hd.comp t ((differentiableAt_const x₀).add (differentiableAt_id.smul_const h))).differentiableWithinAt
  have hφb : ∀ t : ℂ, ‖t‖ < ρ → ‖φ t‖ ≤ M := by
    intro t ht
    apply hb
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
    rw [hρ, lt_div_iff₀ hhn] at ht
    exact ht
  -- the power series of `φ` coming from `p`
  set u : ℂ →L[ℂ] E := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ) h with hu
  have hu0 : u 0 = x₀ + -x₀ := by rw [map_zero, add_neg_cancel]
  have hq : HasFPowerSeriesAt φ (p.compContinuousLinearMap u) 0 := by
    have h1 := hp.comp_sub (-x₀)
    rw [← hu0] at h1
    have h2 := h1.compContinuousLinearMap
    have e : ((fun z => Φ (z - -x₀)) ∘ u) = φ := by
      funext t
      simp only [Function.comp, hu, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, hφ,
        sub_neg_eq_add, add_comm]
    rwa [e] at h2
  have hcoef : ∀ k, (p.compContinuousLinearMap u) k (fun _ => (1 : ℂ)) = p k (fun _ => h) := by
    intro k
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply]
    congr 1
    funext _
    simp [hu]
  -- identification with the Cauchy coefficients on every circle `|t| = s < ρ`
  have hcauchy : ∀ s : ℝ, 0 < s → s < ρ → ∀ k,
      cauchyPowerSeries φ 0 s k (fun _ => 1) = p k (fun _ => h) := by
    intro s hs0 hs k
    set s' : ℝ≥0 := ⟨s, hs0.le⟩
    have hps : HasFPowerSeriesOnBall φ (cauchyPowerSeries φ 0 s') 0 s' :=
      (hφd.mono (closedBall_subset_ball hs)).hasFPowerSeriesOnBall (by rw [← NNReal.coe_pos]; exact hs0)
    have := hps.hasFPowerSeriesAt.eq_formalMultilinearSeries hq
    rw [← hcoef k, ← this]
    rfl
  refine ⟨fun k => ?_, fun hlt => ?_⟩
  · -- Cauchy estimate on circles `s ↑ ρ`
    have hle : ∀ s : ℝ, 0 < s → s < ρ → ‖p k (fun _ => h)‖ ≤ M * (s⁻¹) ^ k := by
      intro s hs0 hs
      rw [← hcauchy s hs0 hs k]
      have h1 : ‖cauchyPowerSeries φ 0 s k (fun _ => 1)‖ ≤ ‖cauchyPowerSeries φ 0 s k‖ := by
        have := (cauchyPowerSeries φ 0 s k).le_opNorm (fun _ => (1 : ℂ))
        simpa using this
      have h2 := norm_cauchyPowerSeries_le φ 0 s k
      have hcont : Continuous fun θ : ℝ => ‖φ (circleMap 0 s θ)‖ := by
        have hc : ContinuousOn φ (closedBall 0 s) := (hφd.mono (closedBall_subset_ball hs)).continuousOn
        refine continuous_norm.comp (hc.comp_continuous (continuous_circleMap 0 s) fun θ => ?_)
        rw [mem_closedBall_zero_iff, norm_circleMap_zero, abs_of_pos hs0]
      have h3 : ∫ θ : ℝ in (0)..2 * Real.pi, ‖φ (circleMap 0 s θ)‖ ≤ 2 * Real.pi * M := by
        have := intervalIntegral.integral_mono_on (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
          (hcont.intervalIntegrable _ _) (intervalIntegrable_const (μ := volume) (c := M)) (fun θ _ => by
            apply hφb
            rw [norm_circleMap_zero, abs_of_pos hs0]; exact hs)
        simpa using this
      have hπ := Real.pi_pos
      calc ‖cauchyPowerSeries φ 0 s k (fun _ => 1)‖ ≤ ‖cauchyPowerSeries φ 0 s k‖ := h1
        _ ≤ ((2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0)..2 * Real.pi, ‖φ (circleMap 0 s θ)‖) * |s|⁻¹ ^ k := h2
        _ ≤ ((2 * Real.pi)⁻¹ * (2 * Real.pi * M)) * |s|⁻¹ ^ k := by gcongr
        _ = M * (s⁻¹) ^ k := by rw [abs_of_pos hs0]; field_simp
    have ht : Tendsto (fun s : ℝ => M * (s⁻¹) ^ k) (𝓝[<] ρ) (𝓝 (M * (ρ⁻¹) ^ k)) := by
      have : ContinuousAt (fun s : ℝ => M * (s⁻¹) ^ k) ρ :=
        (continuousAt_const.mul ((continuousAt_inv₀ hρpos.ne').pow k))
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[<] ρ, ‖p k (fun _ => h)‖ ≤ M * (s⁻¹) ^ k := by
      have h1 : ∀ᶠ s in 𝓝[<] ρ, 0 < s := by
        have : Ioi (0 : ℝ) ∈ 𝓝 ρ := Ioi_mem_nhds hρpos
        exact nhdsWithin_le_nhds this
      filter_upwards [h1, self_mem_nhdsWithin] with s hs0 hs
      exact hle s hs0 hs
    have := ge_of_tendsto ht hev
    rwa [hρ, inv_div] at this
  · -- the diagonal series converges on the ball
    have h1ρ : 1 < ρ := by rw [hρ, lt_div_iff₀ hhn, one_mul]; exact hlt
    obtain ⟨s, hs1, hsρ⟩ := exists_between h1ρ
    have hs0 : 0 < s := zero_lt_one.trans hs1
    set s' : ℝ≥0 := ⟨s, hs0.le⟩
    have hps : HasFPowerSeriesOnBall φ (cauchyPowerSeries φ 0 s') 0 s' :=
      (hφd.mono (closedBall_subset_ball hsρ)).hasFPowerSeriesOnBall (by rw [← NNReal.coe_pos]; exact hs0)
    have hmem : (1 : ℂ) ∈ Metric.eball (0 : ℂ) s' := by
      rw [Metric.eball_coe, mem_ball_zero_iff, norm_one]; exact hs1
    have := hps.hasSum hmem
    simp only [zero_add, hφ, one_smul] at this
    convert this using 1
    funext k
    exact (hcauchy s hs0 hsρ k).symm

end Taylor

/-! ## Lifting uniformly bounded families into `ℓ∞` -/

section Lift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- `ℓ∞(I; ℂ)`. -/
abbrev Linf (I : Type*) := lp (fun _ : I => ℂ) ∞

/-- A uniformly bounded family of real continuous multilinear maps into `ℂ`, as one map into `ℓ∞(I)`. -/
def liftCoef {I : Type*} {k : ℕ} (A : I → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖A i‖ ≤ K) : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (Linf I) :=
  MultilinearMap.mkContinuous
    { toFun := fun m => ⟨fun i => A i m, memℓp_infty ⟨K * ∏ j, ‖m j‖, by
        rintro _ ⟨i, rfl⟩
        exact ((A i).le_opNorm m).trans (mul_le_mul_of_nonneg_right (hK i) (by positivity))⟩⟩
      map_update_add' := fun m j x y => by
        apply lp.ext
        funext i
        simp only [lp.coeFn_add, Pi.add_apply]
        exact (A i).map_update_add m j x y
      map_update_smul' := fun m j c x => by
        apply lp.ext
        funext i
        simp only [lp.coeFn_smul, Pi.smul_apply]
        exact (A i).map_update_smul m j c x }
    K (fun m => lp.norm_le_of_forall_le (by positivity) fun i =>
      ((A i).le_opNorm m).trans (mul_le_mul_of_nonneg_right (hK i) (by positivity)))

theorem liftCoef_apply {I : Type*} {k : ℕ} (A : I → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖A i‖ ≤ K) (m : Fin k → E) (i : I) : liftCoef A hK0 hK m i = A i m := rfl

theorem liftCoef_isCHom {I : Type*} {k : ℕ} (A : I → ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ) {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i, ‖A i‖ ≤ K) (hA : ∀ i, IsCHom (A i)) : IsCHom (liftCoef A hK0 hK) := by
  intro m j c x
  apply lp.ext
  funext i
  rw [lp.coeFn_smul, Pi.smul_apply, liftCoef_apply, liftCoef_apply]
  exact hA i m j c x

/-- **`ℓ∞` lifting**: a family of maps, complex analytic and bounded by `M` on a common ball `B(x₀, R)`, is one
complex analytic `ℓ∞(I)`-valued map on `B(x₀, R/e)`. -/
theorem linf_lift {I : Type*} {Φ : I → E → ℂ} {x₀ : E} {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (han : ∀ i, AnalyticOnNhd ℂ (Φ i) (ball x₀ R)) (hb : ∀ i, ∀ x ∈ ball x₀ R, ‖Φ i x‖ ≤ M) :
    ∃ G : E → Linf I, (∀ x ∈ ball x₀ R, ∀ i, G x i = Φ i x) ∧ (∀ x ∈ ball x₀ R, ‖G x‖ ≤ M) ∧
      (∃ q : FormalMultilinearSeries ℂ E (Linf I),
        HasFPowerSeriesOnBall G q x₀ (ENNReal.ofReal (R / Real.exp 1))) ∧
      AnalyticOnNhd ℂ G (ball x₀ (R / Real.exp 1)) := by
  classical
  -- coordinate power series
  have hex : ∀ i, ∃ p : FormalMultilinearSeries ℂ E ℂ, HasFPowerSeriesAt (Φ i) p x₀ :=
    fun i => han i x₀ (mem_ball_self hR)
  choose p hp using hex
  have htb := fun i h => taylor_bound hR (han i) (hb i) (hp i) h
  -- real symmetrized coefficients
  set P : I → ∀ k : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℂ :=
    fun i k => (p i k).restrictScalars ℝ with hP
  have hPdiag : ∀ i k (h : E), ‖P i k (fun _ => h)‖ ≤ (M / R ^ k) * ‖h‖ ^ k := by
    intro i k h
    have := (htb i h).1 k
    rw [div_pow] at this
    calc ‖P i k (fun _ => h)‖ = ‖p i k (fun _ => h)‖ := rfl
      _ ≤ M * (‖h‖ ^ k / R ^ k) := this
      _ = (M / R ^ k) * ‖h‖ ^ k := by ring
  set K : ℕ → ℝ := fun k => (k : ℝ) ^ k / k.factorial * (M / R ^ k) with hKdef
  have hK0 : ∀ k, 0 ≤ K k := fun k => by positivity
  have hSK : ∀ k i, ‖symC (P i k)‖ ≤ K k := fun k i =>
    norm_symC_le (P i k) (by positivity) (hPdiag i k)
  set A : ∀ k : ℕ, ContinuousMultilinearMap ℝ (fun _ : Fin k => E) (Linf I) :=
    fun k => liftCoef (fun i => symC (P i k)) (hK0 k) (hSK k) with hA
  -- the lifted map
  have hmem : ∀ x ∈ ball x₀ R, Memℓp (fun i => Φ i x) ∞ := fun x hx =>
    memℓp_infty ⟨M, by rintro _ ⟨i, rfl⟩; exact hb i x hx⟩
  set G : E → Linf I := fun x => if hx : x ∈ ball x₀ R then ⟨fun i => Φ i x, hmem x hx⟩ else 0 with hG
  have hGapp : ∀ x ∈ ball x₀ R, ∀ i, G x i = Φ i x := by
    intro x hx i
    simp only [hG, dif_pos hx]
  have hGnorm : ∀ x ∈ ball x₀ R, ‖G x‖ ≤ M := fun x hx =>
    lp.norm_le_of_forall_le hM fun i => by rw [hGapp x hx i]; exact hb i x hx
  have hAdiag : ∀ k (h : E) i, A k (fun _ => h) i = p i k (fun _ => h) := by
    intro k h i
    simp only [hA, liftCoef_apply]
    rw [symC_diag]
    rfl
  have hbound : ∀ k (h : E), ‖A k (fun _ => h)‖ ≤ M * (‖h‖ / R) ^ k := fun k h =>
    lp.norm_le_of_forall_le (by positivity) fun i => by rw [hAdiag]; exact (htb i h).1 k
  have hsum : ∀ h : E, ‖h‖ < R →
      Tendsto (fun N => ∑ k ∈ Finset.range N, A k (fun _ => h)) atTop (𝓝 (G (x₀ + h))) := by
    intro h hh
    have hxh : x₀ + h ∈ ball x₀ R := by rw [mem_ball_iff_norm, add_sub_cancel_left]; exact hh
    set q := ‖h‖ / R with hq
    have hq0 : 0 ≤ q := by positivity
    have hq1 : q < 1 := by rw [hq, div_lt_one hR]; exact hh
    have hq' : 0 < 1 - q := by linarith
    have htail : ∀ N, ‖∑ k ∈ Finset.range N, A k (fun _ => h) - G (x₀ + h)‖ ≤ M * q ^ N / (1 - q) := by
      intro N
      refine lp.norm_le_of_forall_le (by positivity) fun i => ?_
      rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_sum, Finset.sum_apply, hGapp _ hxh i]
      simp only [hAdiag]
      have hs := (htb i h).2 hh
      have e := hs.summable.sum_add_tsum_nat_add N
      rw [← hs.tsum_eq, ← e, sub_add_cancel_left, norm_neg]
      have hg : HasSum (fun k : ℕ => M * q ^ N * q ^ k) (M * q ^ N * (1 - q)⁻¹) :=
        (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q ^ N)
      calc ‖∑' k : ℕ, p i (k + N) (fun _ => h)‖ ≤ M * q ^ N * (1 - q)⁻¹ := by
            refine tsum_of_norm_bounded hg fun k => ?_
            have := (htb i h).1 (k + N)
            rw [pow_add] at this
            calc ‖p i (k + N) (fun _ => h)‖ ≤ M * (q ^ k * q ^ N) := this
              _ = M * q ^ N * q ^ k := by ring
        _ = M * q ^ N / (1 - q) := by rw [div_eq_mul_inv]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun N => norm_nonneg _) htail ?_
    have : Tendsto (fun N : ℕ => M * q ^ N / (1 - q)) atTop (𝓝 (M * 0 / (1 - q))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul M).div_const (1 - q)
    simpa using this
  have hreal := hasFPowerSeriesOnBall_symSeries (f := G) (x := x₀) A hM hR hbound hsum
  -- complex lift
  have hPc : ∀ i k, IsCHom (P i k) := by
    intro i k m j c x
    exact (p i k).map_update_smul m j c x
  have hAc : ∀ k, IsCHom (A k) := fun k =>
    liftCoef_isCHom _ (hK0 k) (hSK k) (fun i => symC_isCHom _ (hPc i k))
  set qc : FormalMultilinearSeries ℂ E (Linf I) := fun k => liftC (symC (A k)) (symC_isCHom _ (hAc k))
  have hc : HasFPowerSeriesOnBall G qc x₀ (ENNReal.ofReal (R / Real.exp 1)) :=
    hasFPowerSeriesOnBall_of_coe_eq qc (symSeries A) (fun _ _ => rfl) hreal
  refine ⟨G, hGapp, hGnorm, ⟨qc, hc⟩, fun x hx => hc.analyticAt_of_mem ?_⟩
  rw [Metric.mem_eball, edist_lt_ofReal]
  exact hx

end Lift

end QuantumNLS.RB01LinfLift

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01LinfLift.taylor_bound
#print axioms QuantumNLS.RB01LinfLift.liftCoef_isCHom
#print axioms QuantumNLS.RB01LinfLift.linf_lift
