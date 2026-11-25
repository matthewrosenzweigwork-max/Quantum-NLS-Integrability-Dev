import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA3Diff

/-! # Track A, step A4 (generic): rotation equivariance of iterated derivatives; strong continuity

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

* `carrierMap38_rot_comm`: a sequence map that commutes with every diagonal rotation `rotSeq38 θ`
  on `h^r` induces a carrier map commuting with `rotC38 r θ`;
* `iteratedFDeriv_rot`: for such a carrier map `g` that is real analytic on `h^r`,
  `D^k g(S_θ x)[S_θ v_1, …, S_θ v_k] = S_θ (D^k g(x)[v_1, …, v_k])`
  (the real equivariance differentiated `k` times; no complexification);
* `continuous_rotC38_apply`: `θ ↦ S_θ u` is continuous into `h^r` (strong continuity of the
  rotation group, by dominated convergence on the Parseval sum). -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff

namespace NlsGge.ALLS.TransA

/-- A rotation-equivariant sequence map induces a rotation-equivariant carrier map. -/
theorem carrierMap38_rot_comm (r : ℝ) (f : (ℤ → ℂ) → (ℤ → ℂ))
    (hf : ∀ x ∈ seqSobolev38 r, f x ∈ seqSobolev38 r)
    (heq : ∀ θ : ℝ, ∀ x ∈ seqSobolev38 r, f (rotSeq38 θ x) = rotSeq38 θ (f x))
    (θ : ℝ) (x : SobolevCarrier38 r) :
    carrierMap38 r r f hf (rotC38 r θ x) = rotC38 r θ (carrierMap38 r r f hf x) := by
  apply carrierExt38
  rw [carrierMap38_coe, rotC38_coe, rotC38_coe, carrierMap38_coe]
  exact heq θ _ (carrierCoe38_mem r x)

/-- **Equivariance of iterated derivatives** under the rotation group. -/
theorem iteratedFDeriv_rot {r : ℝ} {g : SobolevCarrier38 r → SobolevCarrier38 r}
    (han : AnalyticOnNhd ℝ g Set.univ)
    (hcomm : ∀ (θ : ℝ) (x : SobolevCarrier38 r), g (rotC38 r θ x) = rotC38 r θ (g x))
    (θ : ℝ) (k : ℕ) (x : SobolevCarrier38 r) (v : Fin k → SobolevCarrier38 r) :
    iteratedFDeriv ℝ k g (rotC38 r θ x) (fun i => rotC38 r θ (v i)) =
      rotC38 r θ (iteratedFDeriv ℝ k g x v) := by
  have hcd : ContDiff ℝ k g := han.contDiff
  have hfun : g ∘ rotC38 r θ = rotC38 r θ ∘ g := funext fun x => hcomm θ x
  have h1 := (rotC38 r θ).iteratedFDeriv_comp_right hcd x (i := k) le_rfl
  have h2 := (rotC38 r θ).iteratedFDeriv_comp_left (f := g) (x := x) hcd.contDiffAt (i := k) le_rfl
  rw [hfun, h2] at h1
  have h3 := congrArg (fun A => A v) h1
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at h3
  exact h3.symm

/-- The rotation group law on the carrier. -/
theorem rotC38_add_apply (r θ φ : ℝ) (u : SobolevCarrier38 r) :
    rotC38 r (θ + φ) u = rotC38 r θ (rotC38 r φ u) := by
  apply carrierExt38
  rw [rotC38_coe, rotC38_coe, rotC38_coe, rotSeq38_add]

/-- `‖S_t u - u‖ → 0` as `t → 0`. -/
theorem tendsto_norm_rot_sub (r : ℝ) (u : SobolevCarrier38 r) :
    Tendsto (fun t : ℝ => ‖rotC38 r t u - u‖ ^ 2) (𝓝 0) (𝓝 0) := by
  have heq : (fun t : ℝ => ‖rotC38 r t u - u‖ ^ 2) = fun t => ∑' n : ℤ,
      sobolevModeWeight r n * ‖carrierCoe38 r u n‖ ^ 2 * ‖rotPhase38 t n - 1‖ ^ 2 := by
    funext t; exact (hasSum_norm_rot_sub_sq r t u).tsum_eq.symm
  rw [heq]
  have hz : (0 : ℝ) = ∑' n : ℤ, (0 : ℝ) := by simp
  rw [hz]
  have hs := (carrier_hasSum_norm_sq38 r u).summable.mul_left 4
  refine tendsto_tsum_of_dominated_convergence (bound := fun n =>
    4 * (sobolevModeWeight r n * ‖carrierCoe38 r u n‖ ^ 2)) hs (fun n => ?_) ?_
  · have hc : Continuous fun t : ℝ =>
        sobolevModeWeight r n * ‖carrierCoe38 r u n‖ ^ 2 * ‖rotPhase38 t n - 1‖ ^ 2 := by
      unfold rotPhase38; fun_prop
    have := hc.tendsto 0
    simpa [rotPhase38_zero] using this
  · refine Eventually.of_forall fun t n => ?_
    have hw := (sobolevModeWeight_pos r n).le
    have h2 := norm_rotPhase38_sub_one_le_two t n
    have hsq : ‖rotPhase38 t n - 1‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (rotPhase38 t n - 1)]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have := mul_nonneg hw (sq_nonneg ‖carrierCoe38 r u n‖)
    nlinarith

/-- **Strong continuity**: `θ ↦ S_θ u` is continuous into `h^r`. -/
theorem continuous_rotC38_apply (r : ℝ) (u : SobolevCarrier38 r) :
    Continuous fun θ : ℝ => rotC38 r θ u := by
  rw [continuous_iff_continuousAt]
  intro θ0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq := (tendsto_norm_rot_sub r u).comp
    ((continuous_sub_right θ0).tendsto' θ0 0 (sub_self θ0))
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun θ => ?_
  simp only [Function.comp_apply]
  rw [Real.sqrt_sq (norm_nonneg _)]
  have e : rotC38 r θ u = rotC38 r θ0 (rotC38 r (θ - θ0) u) := by
    rw [← rotC38_add_apply, add_sub_cancel]
  rw [e, ← map_sub, norm_rotC38]

end NlsGge.ALLS.TransA
