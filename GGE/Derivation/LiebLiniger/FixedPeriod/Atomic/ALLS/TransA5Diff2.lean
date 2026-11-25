import LiebLiniger.FixedPeriod.Atomic.ALLS.TransA4Equivariant

/-! # Track A, step A5 (generic, part 1): seminorm bound from small-angle domination

Author: Claude Opus 5.5 (track A).  Not self-reviewed, not accepted.

* `norm_carrierIncl38_le`: the inclusion `h^s → h^r` (`r ≤ s`) has norm at most one;
* `diffSemi_le_of_small`: if on `(0, δ]` the rotation difference of `y` is dominated by a finite
  nonnegative combination of rotation differences of `u_j`, then
  `diffSemi r σ y ≤ Σ_j c_j diffSemi r σ u_j + 4 ‖y‖² δ^{-2σ}/(2σ)`.
  For angles beyond `δ` only the isometry bound `‖S_θ y - y‖ ≤ 2‖y‖` is used (Pro report:
  "large translations use only the target isometry"; no invariant complex tube). -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ENNReal

namespace NlsGge.ALLS.TransA

/-- The inclusion `h^s → h^r` is a contraction. -/
theorem norm_carrierIncl38_le {r s : ℝ} (h : r ≤ s) (x : SobolevCarrier38 s) :
    ‖carrierIncl38 h x‖ ≤ ‖x‖ := by
  have h1 := carrier_hasSum_norm_sq38 r (carrierIncl38 h x)
  have h2 := carrier_hasSum_norm_sq38 s x
  have hle : ‖carrierIncl38 h x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    refine hasSum_le (fun n => ?_) h1 h2
    rw [carrierCoe38_incl38]
    exact mul_le_mul_of_nonneg_right (sobolevModeWeight_mono h n) (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hle

/-- Rotation differences are bounded by twice the norm. -/
theorem norm_rot_sub_le_two (r θ : ℝ) (y : SobolevCarrier38 r) :
    ‖rotC38 r θ y - y‖ ≤ 2 * ‖y‖ := by
  calc ‖rotC38 r θ y - y‖ ≤ ‖rotC38 r θ y‖ + ‖y‖ := norm_sub_le _ _
    _ = 2 * ‖y‖ := by rw [norm_rotC38]; ring

theorem measurable_diffSemi_integrand (r σ : ℝ) (u : SobolevCarrier38 r) :
    Measurable fun θ : ℝ => ENNReal.ofReal (‖rotC38 r θ u - u‖ ^ 2 * θ ^ (-1 - 2 * σ)) := by
  have hc : Continuous fun θ : ℝ => ‖rotC38 r θ u - u‖ ^ 2 :=
    (((continuous_rotC38_apply r u).sub continuous_const).norm).pow 2
  exact (hc.measurable.mul (measurable_id.pow_const _)).ennreal_ofReal

/-- **Seminorm bound from small-angle domination and the large-angle isometry bound.** -/
theorem diffSemi_le_of_small {r σ δ : ℝ} (hσ0 : 0 < σ) (hδ0 : 0 < δ) (hδπ : δ ≤ Real.pi)
    (y : SobolevCarrier38 r) {ι : Type*} (J : Finset ι) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (u : ι → SobolevCarrier38 r)
    (hsmall : ∀ θ ∈ Ioc 0 δ, ‖rotC38 r θ y - y‖ ^ 2 ≤ ∑ j ∈ J, c j * ‖rotC38 r θ (u j) - u j‖ ^ 2) :
    diffSemi r σ y ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * diffSemi r σ (u j) +
      ENNReal.ofReal (4 * ‖y‖ ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ))) := by
  set a : ℝ := -1 - 2 * σ with hadef
  have hsplit : Ioc 0 Real.pi ⊆ Ioc 0 δ ∪ Ioi δ := by
    intro θ hθ
    rcases le_or_gt θ δ with h | h
    · exact Or.inl ⟨hθ.1, h⟩
    · exact Or.inr h
  have hA : ∀ θ ∈ Ioc 0 δ, ENNReal.ofReal (‖rotC38 r θ y - y‖ ^ 2 * θ ^ a) ≤
      ∑ j ∈ J, ENNReal.ofReal (c j) * ENNReal.ofReal (‖rotC38 r θ (u j) - u j‖ ^ 2 * θ ^ a) := by
    intro θ hθ
    have hθa : 0 ≤ θ ^ a := Real.rpow_nonneg hθ.1.le _
    calc ENNReal.ofReal (‖rotC38 r θ y - y‖ ^ 2 * θ ^ a)
        ≤ ENNReal.ofReal ((∑ j ∈ J, c j * ‖rotC38 r θ (u j) - u j‖ ^ 2) * θ ^ a) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsmall θ hθ) hθa)
      _ = ∑ j ∈ J, ENNReal.ofReal (c j) * ENNReal.ofReal (‖rotC38 r θ (u j) - u j‖ ^ 2 * θ ^ a) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun j _ => by
            have := hc j; positivity)]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← ENNReal.ofReal_mul (hc j), mul_assoc]
  have hB : ∀ θ ∈ Ioi δ, ENNReal.ofReal (‖rotC38 r θ y - y‖ ^ 2 * θ ^ a) ≤
      ENNReal.ofReal (4 * ‖y‖ ^ 2 * θ ^ a) := by
    intro θ hθ
    apply ENNReal.ofReal_le_ofReal
    have hθa : 0 ≤ θ ^ a := Real.rpow_nonneg (hδ0.trans hθ).le _
    have h2 := norm_rot_sub_le_two r θ y
    have : ‖rotC38 r θ y - y‖ ^ 2 ≤ 4 * ‖y‖ ^ 2 := by
      nlinarith [norm_nonneg (rotC38 r θ y - y), norm_nonneg y]
    exact mul_le_mul_of_nonneg_right this hθa
  have ha : a < -1 := by rw [hadef]; linarith
  have hI : ∫⁻ θ in Ioi δ, ENNReal.ofReal (4 * ‖y‖ ^ 2 * θ ^ a) =
      ENNReal.ofReal (4 * ‖y‖ ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ))) := by
    rw [lintegral_Ioi_rpow ha hδ0 _ (by positivity)]
    congr 1
    have e : a + 1 = -(2 * σ) := by rw [hadef]; ring
    rw [e, neg_div_neg_eq]
  have hJ : ∫⁻ θ in Ioc 0 δ, ∑ j ∈ J, ENNReal.ofReal (c j) *
      ENNReal.ofReal (‖rotC38 r θ (u j) - u j‖ ^ 2 * θ ^ a) ≤
      ∑ j ∈ J, ENNReal.ofReal (c j) * diffSemi r σ (u j) := by
    rw [lintegral_finsetSum J (fun j _ => (measurable_diffSemi_integrand r σ (u j)).const_mul _)]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    exact lintegral_mono_set (fun θ hθ => ⟨hθ.1, hθ.2.trans hδπ⟩)
  calc diffSemi r σ y
      ≤ ∫⁻ θ in Ioc 0 δ ∪ Ioi δ, ENNReal.ofReal (‖rotC38 r θ y - y‖ ^ 2 * θ ^ a) :=
        lintegral_mono_set hsplit
    _ ≤ (∫⁻ θ in Ioc 0 δ, ENNReal.ofReal (‖rotC38 r θ y - y‖ ^ 2 * θ ^ a)) +
        (∫⁻ θ in Ioi δ, ENNReal.ofReal (‖rotC38 r θ y - y‖ ^ 2 * θ ^ a)) :=
        lintegral_union_le _ _ _
    _ ≤ (∫⁻ θ in Ioc 0 δ, ∑ j ∈ J, ENNReal.ofReal (c j) *
          ENNReal.ofReal (‖rotC38 r θ (u j) - u j‖ ^ 2 * θ ^ a)) +
        (∫⁻ θ in Ioi δ, ENNReal.ofReal (4 * ‖y‖ ^ 2 * θ ^ a)) :=
        add_le_add (setLIntegral_mono' measurableSet_Ioc hA) (setLIntegral_mono' measurableSet_Ioi hB)
    _ ≤ ∑ j ∈ J, ENNReal.ofReal (c j) * diffSemi r σ (u j) +
        ENNReal.ofReal (4 * ‖y‖ ^ 2 * (δ ^ (-(2 * σ)) / (2 * σ))) := by
        rw [hI]; exact add_le_add hJ le_rfl

end NlsGge.ALLS.TransA
