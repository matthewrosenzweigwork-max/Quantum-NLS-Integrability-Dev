import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA5Mem

/-! # Track A, step A5 (generic, part 4): analyticity in the stronger space; the generic lemma A-GEN

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

* `liftCML`: a continuous multilinear map into `h^r` whose values lie in `h^{r+σ}` with a
  multilinear bound is lifted to a continuous multilinear map into `h^{r+σ}`;
* `hasFPowerSeriesOnBall_restriction`: if `ι ∘ F = g ∘ ι` with `g : h^r → h^r` real analytic and
  rotation equivariant, then `F : h^{r+σ} → h^{r+σ}` has, at every center, the power series
  `Σ_k (k!)⁻¹ D^k g(ι v0)` (lifted), with positive radius.  The sum is identified through the
  injective inclusion `ι` (Pro report: "Its image in `Y_0` is `F`; injectivity proves weighted
  holomorphy");
* `analytic_restriction_of_rot_equivariant` (**A-GEN**, statement as submitted in
  STATEMENTS_TRACK_A.md): any sequence map preserving `h^N`, real analytic there and commuting
  with every rotation `S_θ` on `h^N`, preserves `h^{N+σ}` (`0 < σ < 1`) and is real analytic on it.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ENNReal NNReal Nat

namespace NlsGge.ALLS.TransA

local instance carrierCompleteSpaceA5G (r : ℝ) : CompleteSpace (SobolevCarrier38 r) :=
  inferInstanceAs (CompleteSpace (SobolevHilbert r))

theorem incl_mk {r s : ℝ} (hrs : r ≤ s) (b : SobolevCarrier38 r) (hb : carrierCoe38 r b ∈ seqSobolev38 s) :
    carrierIncl38 hrs (carrierMk38 s (carrierCoe38 r b) hb) = b :=
  carrierExt38 (by rw [carrierCoe38_incl38, carrierCoe38_mk])

theorem incl_injective {r s : ℝ} (hrs : r ≤ s) : Function.Injective (carrierIncl38 hrs) := by
  intro a b h
  apply carrierExt38
  have := congrArg (carrierCoe38 r) h
  rwa [carrierCoe38_incl38, carrierCoe38_incl38] at this

/-- Lift of a multilinear map with values in the stronger space. -/
def liftCML {r s : ℝ} (hrs : r ≤ s) {k : ℕ}
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => SobolevCarrier38 s) (SobolevCarrier38 r))
    (hmem : ∀ h, carrierCoe38 r (B h) ∈ seqSobolev38 s) (M : ℝ)
    (hM : ∀ h, ‖carrierMk38 s (carrierCoe38 r (B h)) (hmem h)‖ ≤ M * ∏ i, ‖h i‖) :
    ContinuousMultilinearMap ℝ (fun _ : Fin k => SobolevCarrier38 s) (SobolevCarrier38 s) :=
  MultilinearMap.mkContinuous
    { toFun := fun h => carrierMk38 s (carrierCoe38 r (B h)) (hmem h)
      map_update_add' := fun m i x y => by
        apply incl_injective hrs
        rw [map_add, incl_mk, incl_mk, incl_mk, B.map_update_add]
      map_update_smul' := fun m i c x => by
        apply incl_injective hrs
        rw [map_smul, incl_mk, incl_mk, B.map_update_smul] }
    M hM

theorem incl_liftCML {r s : ℝ} (hrs : r ≤ s) {k : ℕ}
    (B : ContinuousMultilinearMap ℝ (fun _ : Fin k => SobolevCarrier38 s) (SobolevCarrier38 r))
    (hmem : ∀ h, carrierCoe38 r (B h) ∈ seqSobolev38 s) (M : ℝ)
    (hM : ∀ h, ‖carrierMk38 s (carrierCoe38 r (B h)) (hmem h)‖ ≤ M * ∏ i, ‖h i‖)
    (h : Fin k → SobolevCarrier38 s) :
    carrierIncl38 hrs (liftCML hrs B hmem M hM h) = B h :=
  incl_mk hrs _ _

/-- `(k+1)² ≤ 4^k`. -/
theorem sq_succ_le_four_pow (k : ℕ) : ((k : ℝ) + 1) ^ 2 ≤ 4 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih =>
    push_cast
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ((n : ℝ) + 1 + 1) ^ 2 ≤ 4 * ((n : ℝ) + 1) ^ 2 := by nlinarith
      _ ≤ 4 * 4 ^ n := by linarith
      _ = 4 ^ (n + 1) := by ring

/-- **Power series of the restriction at a stronger-space center.** -/
theorem analyticAt_restriction {r σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hrs : r ≤ r + σ)
    {g : SobolevCarrier38 r → SobolevCarrier38 r} (han : AnalyticOnNhd ℝ g Set.univ)
    (hcomm : ∀ (θ : ℝ) (x : SobolevCarrier38 r), g (rotC38 r θ x) = rotC38 r θ (g x))
    {F : SobolevCarrier38 (r + σ) → SobolevCarrier38 (r + σ)}
    (hF : ∀ v, carrierIncl38 hrs (F v) = g (carrierIncl38 hrs v)) (v0 : SobolevCarrier38 (r + σ)) :
    AnalyticAt ℝ F v0 := by
  obtain ⟨C, ρ, δ, hC, hρ, hδ0, hδπ, hb, hδ⟩ := exists_setup hrs han v0
  set x0 := carrierIncl38 hrs v0 with hx0
  -- the stronger-space coefficients
  let A : (k : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin k => SobolevCarrier38 (r + σ))
      (SobolevCarrier38 r) := fun k =>
    (iteratedFDeriv ℝ k g x0).compContinuousLinearMap (fun _ => carrierIncl38 hrs)
  have hAapp : ∀ k h, A k h = iteratedFDeriv ℝ k g x0 (fun i => carrierIncl38 hrs (h i)) :=
    fun k h => rfl
  have hmem : ∀ k h, carrierCoe38 r (A k h) ∈ seqSobolev38 (r + σ) := fun k h =>
    (coeff_mem_and_norm_le hσ0 hσ1 hrs han hcomm v0 hρ.le hδ0 hδπ hb hδ k h).1
  have hM : ∀ k h, ‖carrierMk38 (r + σ) (carrierCoe38 r (A k h)) (hmem k h)‖ ≤
      coeffBound σ C ρ δ ‖v0‖ ‖iteratedFDeriv ℝ k g x0‖ k * ∏ i, ‖h i‖ := fun k h =>
    (coeff_mem_and_norm_le hσ0 hσ1 hrs han hcomm v0 hρ.le hδ0 hδπ hb hδ k h).2
  let Q : (k : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin k => SobolevCarrier38 (r + σ))
      (SobolevCarrier38 (r + σ)) := fun k =>
    liftCML hrs (A k) (hmem k) (coeffBound σ C ρ δ ‖v0‖ ‖iteratedFDeriv ℝ k g x0‖ k) (hM k)
  let q : FormalMultilinearSeries ℝ (SobolevCarrier38 (r + σ)) (SobolevCarrier38 (r + σ)) :=
    fun k => ((k ! : ℝ)⁻¹) • Q k
  -- norm bounds and radius
  obtain ⟨K, hK0, hK⟩ := coeffBound_le hσ0 hσ1 hC.le hρ hδ0 ‖v0‖ (norm_nonneg _)
  have hAk : ∀ k : ℕ, ‖iteratedFDeriv ℝ k g x0‖ ≤ C * k ! * (ρ⁻¹) ^ k := fun k => by
    have := hb k 0 (by simpa using hρ.le); simpa using this
  have hqn : ∀ k : ℕ, ‖q k‖ ≤ K * ((k : ℝ) + 1) ^ 2 * (ρ⁻¹) ^ k := by
    intro k
    have hfac : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    have hQ : ‖Q k‖ ≤ coeffBound σ C ρ δ ‖v0‖ ‖iteratedFDeriv ℝ k g x0‖ k :=
      MultilinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _
    have hB := hK k _ (norm_nonneg _) (hAk k)
    calc ‖q k‖ ≤ ‖((k ! : ℝ)⁻¹)‖ * ‖Q k‖ := ContinuousMultilinearMap.opNorm_smul_le _ _
      _ ≤ (k ! : ℝ)⁻¹ * (K * k ! * ((k : ℝ) + 1) ^ 2 * (ρ⁻¹) ^ k) := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hfac)]
          gcongr
          exact hQ.trans hB
      _ = K * ((k : ℝ) + 1) ^ 2 * (ρ⁻¹) ^ k := by field_simp
  set t : ℝ≥0 := ⟨ρ / 4, (div_pos hρ (by norm_num)).le⟩ with ht
  have htρ : (t : ℝ) = ρ / 4 := rfl
  have hrad : (t : ℝ≥0∞) ≤ q.radius := by
    refine q.le_radius_of_bound K fun k => ?_
    rw [htρ]
    have h4 := sq_succ_le_four_pow k
    calc ‖q k‖ * (ρ / 4) ^ k ≤ K * ((k : ℝ) + 1) ^ 2 * (ρ⁻¹) ^ k * (ρ / 4) ^ k := by
          gcongr; exact hqn k
      _ = K * (((k : ℝ) + 1) ^ 2 / 4 ^ k) := by
          rw [div_pow, inv_pow]; field_simp
      _ ≤ K * 1 := by
          gcongr
          rw [div_le_one (by positivity)]; exact h4
      _ = K := mul_one K
  -- the base power series of `g` at `x0`
  obtain ⟨p, R, hp⟩ := han x0 trivial
  set ε : ℝ≥0∞ := min (t : ℝ≥0∞) R with hε
  have ht0 : (0 : ℝ≥0∞) < t := by
    rw [ENNReal.coe_pos, ← NNReal.coe_pos, htρ]; exact div_pos hρ (by norm_num)
  have hε0 : 0 < ε := lt_min ht0 hp.r_pos
  refine ⟨q, ε, ?_, hε0, fun {y} hy => ?_⟩
  · exact (min_le_left _ _).trans hrad
  · have hyq : y ∈ Metric.eball (0 : SobolevCarrier38 (r + σ)) q.radius :=
      Metric.eball_subset_eball ((min_le_left _ _).trans hrad) hy
    have hsum := (q.summable_norm_apply hyq).of_norm
    set S := ∑' n, q n (fun _ => y) with hS
    have hS' : HasSum (fun n => q n (fun _ => y)) S := hsum.hasSum
    -- image under the inclusion
    have hι := hS'.mapL (carrierIncl38 hrs)
    have hterm : ∀ n, carrierIncl38 hrs (q n (fun _ => y)) =
        ((n ! : ℝ)⁻¹) • iteratedFDeriv ℝ n g x0 (fun _ => carrierIncl38 hrs y) := by
      intro n
      show carrierIncl38 hrs (((n ! : ℝ)⁻¹ • Q n) (fun _ => y)) = _
      rw [ContinuousMultilinearMap.smul_apply, map_smul]
      all_goals exact congrArg _ (incl_liftCML hrs (A n) (hmem n) _ (hM n) _)
    have hyR : carrierIncl38 hrs y ∈ Metric.eball (0 : SobolevCarrier38 r) R := by
      rw [Metric.mem_eball, edist_zero_right] at hy ⊢
      refine lt_of_le_of_lt ?_ (lt_of_lt_of_le hy (min_le_right _ _))
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_carrierIncl38_le hrs y)
    have hg := hp.hasSum_iteratedFDeriv hyR
    have hιS : carrierIncl38 hrs S = g (x0 + carrierIncl38 hrs y) := by
      refine hι.unique ?_
      simp only [hterm]
      exact hg
    have hval : F (v0 + y) = S := by
      apply incl_injective hrs
      rw [hF, map_add, hιS]
    rw [hval]
    exact hS'

/-- **A-GEN**: rotation-equivariant analytic maps of `h^N` restrict analytically to `h^{N+σ}`. -/
theorem analytic_restriction_of_rot_equivariant (N : ℕ) (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hf : ∀ x ∈ seqSobolev38 (N : ℝ), f x ∈ seqSobolev38 (N : ℝ))
    (han : AnalyticOnNhd ℝ (carrierMap38 (N : ℝ) (N : ℝ) f hf) Set.univ)
    (heq : ∀ θ : ℝ, ∀ x ∈ seqSobolev38 (N : ℝ), f (rotSeq38 θ x) = rotSeq38 θ (f x)) :
    ∃ hfs : (∀ x ∈ seqSobolev38 ((N : ℝ) + σ), f x ∈ seqSobolev38 ((N : ℝ) + σ)),
      AnalyticOnNhd ℝ (carrierMap38 ((N : ℝ) + σ) ((N : ℝ) + σ) f hfs) Set.univ := by
  set g := carrierMap38 (N : ℝ) (N : ℝ) f hf with hg
  have hcomm : ∀ (θ : ℝ) (x : SobolevCarrier38 (N : ℝ)), g (rotC38 (N : ℝ) θ x) =
      rotC38 (N : ℝ) θ (g x) := carrierMap38_rot_comm (N : ℝ) f hf heq
  have hrs : (N : ℝ) ≤ (N : ℝ) + σ := by linarith
  have hgcoe : ∀ v : SobolevCarrier38 ((N : ℝ) + σ),
      carrierCoe38 (N : ℝ) (g (carrierIncl38 hrs v)) = f (carrierCoe38 ((N : ℝ) + σ) v) := by
    intro v; rw [hg, carrierMap38_coe, carrierCoe38_incl38]
  have hfs : ∀ x ∈ seqSobolev38 ((N : ℝ) + σ), f x ∈ seqSobolev38 ((N : ℝ) + σ) := by
    intro x hx
    set v0 := carrierMk38 ((N : ℝ) + σ) x hx
    obtain ⟨C, ρ, δ, _, hρ, hδ0, hδπ, hb, hδ⟩ := exists_setup hrs han v0
    obtain ⟨hmem, -⟩ := coeff_mem_and_norm_le hσ0 hσ1 hrs han hcomm v0 hρ.le hδ0 hδπ hb hδ 0
      Fin.elim0
    rw [iteratedFDeriv_zero_apply, hgcoe, carrierCoe38_mk] at hmem
    exact hmem
  refine ⟨hfs, fun v0 _ => ?_⟩
  refine analyticAt_restriction hσ0 hσ1 hrs han hcomm (fun v => ?_) v0
  apply carrierExt38
  rw [carrierCoe38_incl38, carrierMap38_coe, hgcoe]

end NlsGge.ALLS.TransA
