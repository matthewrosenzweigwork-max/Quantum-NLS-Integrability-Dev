import Mathlib
import QuantumNLS.RB01Det
import QuantumNLS.Local002Idem

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-23: `Q_n = P_n Q_n P_n` for the dressed contour integral
on arbitrary real fields at high labels (source `collective_actions.tex:272-307`, eq. `GB01-B`:
`K_n = E^*Q_nE` with `Q_n = (2πi)⁻¹∮(z − p_n)(z − 𝓛_u)⁻¹dz = P_nQ_nP_n`; needed to identify RB01Matrix's
`S^{-1/2}KS^{-1/2}` with the reduced matrix, as recorded at RB01-7).

* `algebra_weighted` (generic Banach algebra, after the frozen `Local002Idem.algebra_idem`): for a family satisfying
  the resolvent identity and continuous on a closed annulus, with `D_r = ∮_{|z−c|=r}(z − c)R(z)dz` and
  `P_r = ∮_{|z−c|=r}R(z)dz`: `D_{r₂} = D_{r₁}`, `D_{r₂}P_{r₁} = 2πi D_{r₂}`, `P_{r₂}D_{r₁} = 2πi D_{r₂}`
  (resolvent identity on `Γ_{r₂} × Γ_{r₁}`, Cauchy's formula for `z ↦ z − c`, Fubini `Local002Circle.circle_swap`);
* **`dressed_proj`**: under `RB01Resolvent.SqSmall` (resolvents on the annulus `r/2 ≤ |z − p_n| ≤ r`):
  `D P = D` and `P D = D` for `P = perturbedProj`, `D = dressedIntegral` (radius `r`). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal ComplexConjugate

namespace QuantumNLS.RB01SpecIdem

open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Circle QuantumNLS.Local002Idem

theorem const_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {c : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (a : E) : ∮ _z in C(c, r), a = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
    (f := fun _ => a) continuousOn_const (fun _ _ => differentiableAt_const _)

/-- `∮_{|z−c|=r}(z − c)(z − w)⁻¹dz = 2πi(w − c)` for `|w − c| < r`. -/
theorem weight_cauchy {c w : ℂ} {r : ℝ} (hw : w ∈ ball c r) :
    ∮ z in C(c, r), (z - c) * (z - w)⁻¹ = (2 * Real.pi * Complex.I) * (w - c) := by
  have hr : 0 < r := dist_nonneg.trans_lt hw
  have hne : ∀ z ∈ sphere c r, z - w ≠ 0 := fun z hz h => by
    have : z = w := sub_eq_zero.1 h
    subst this
    rw [mem_ball] at hw; rw [mem_sphere] at hz; linarith
  have he : ∀ z ∈ sphere c r, (z - c) * (z - w)⁻¹ = 1 + (w - c) * (z - w)⁻¹ := by
    intro z hz
    have := hne z hz
    field_simp
    ring
  have hinv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere c r) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  rw [circleIntegral.integral_congr hr.le he, circleIntegral.integral_add (f := fun _ => (1 : ℂ))
    (g := fun z => (w - c) * (z - w)⁻¹)
    (continuousOn_const.circleIntegrable hr.le) ((continuousOn_const.mul hinv).circleIntegrable hr.le),
    const_zero hr.le, zero_add, circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball hw]
  ring

/-- `∮_{|w−c|=r}(w − c)(z − w)⁻¹dw = 0` for `|z − c| > r`. -/
theorem weight_outer {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r < ‖z - c‖) :
    ∮ w in C(c, r), (w - c) * (z - w)⁻¹ = 0 := by
  have hne : ∀ w ∈ closedBall c r, z - w ≠ 0 := fun w hw h => by
    have : z = w := sub_eq_zero.1 h
    subst this
    have := mem_closedBall.1 hw
    rw [dist_eq_norm] at this
    linarith
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty ?_ ?_
  · intro w hw
    exact ((continuousAt_id.sub continuousAt_const).mul
      ((continuousAt_const.sub continuousAt_id).inv₀ (hne w hw))).continuousWithinAt
  · intro w hw
    exact (differentiableAt_id.sub (differentiableAt_const _)).mul
      ((differentiableAt_const _).sub differentiableAt_id |>.inv (hne w (ball_subset_closedBall hw.1)))

theorem algebra_weighted {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (Rf : ℂ → B) {c : ℂ} {r1 r2 : ℝ} (hr1 : 0 < r1) (hr12 : r1 < r2)
    (hid : ∀ z w : ℂ, r1 ≤ ‖z - c‖ → ‖z - c‖ ≤ r2 → r1 ≤ ‖w - c‖ → ‖w - c‖ ≤ r2 →
      Rf z - Rf w = (w - z) • (Rf z * Rf w))
    (hcont : ContinuousOn Rf {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2}) :
    (∮ z in C(c, r2), (z - c) • Rf z) = (∮ z in C(c, r1), (z - c) • Rf z) ∧
      (∮ z in C(c, r2), (z - c) • Rf z) * (∮ w in C(c, r1), Rf w) =
        (2 * Real.pi * Complex.I : ℂ) • ∮ z in C(c, r2), (z - c) • Rf z ∧
      (∮ z in C(c, r2), Rf z) * (∮ w in C(c, r1), (w - c) • Rf w) =
        (2 * Real.pi * Complex.I : ℂ) • ∮ z in C(c, r2), (z - c) • Rf z := by
  have hr2 : 0 < r2 := hr1.trans hr12
  have hsph1 : sphere c r1 ⊆ {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2} := fun z hz => by
    have : ‖z - c‖ = r1 := by simpa [mem_sphere_iff_norm] using hz
    exact ⟨this.ge, by rw [this]; exact hr12.le⟩
  have hsph2 : sphere c r2 ⊆ {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2} := fun z hz => by
    have : ‖z - c‖ = r2 := by simpa [mem_sphere_iff_norm] using hz
    exact ⟨by rw [this]; exact hr12.le, this.le⟩
  -- holomorphy on the open annulus
  have hderiv : ∀ z : ℂ, r1 < ‖z - c‖ → ‖z - c‖ < r2 → DifferentiableAt ℂ Rf z := by
    intro z hz1 hz2
    have hopen : {w : ℂ | r1 < ‖w - c‖ ∧ ‖w - c‖ < r2} ∈ 𝓝 z := by
      have o1 : IsOpen {w : ℂ | r1 < ‖w - c‖} := isOpen_lt continuous_const (by fun_prop)
      have o2 : IsOpen {w : ℂ | ‖w - c‖ < r2} := isOpen_lt (by fun_prop) continuous_const
      exact (o1.inter o2).mem_nhds ⟨hz1, hz2⟩
    have hcz : ContinuousAt Rf z :=
      hcont.continuousAt (Filter.mem_of_superset hopen fun w hw => ⟨hw.1.le, hw.2.le⟩)
    refine (hasDerivAt_iff_tendsto_slope.2 ?_).differentiableAt (f' := -(Rf z * Rf z))
    have hlim : Filter.Tendsto (fun w => -(Rf w * Rf z)) (𝓝[≠] z) (𝓝 (-(Rf z * Rf z))) :=
      ((hcz.tendsto.mul tendsto_const_nhds).neg).mono_left nhdsWithin_le_nhds
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hopen] with w hwz hw
    have hwz' : w ≠ z := hwz
    have hid' := hid w z hw.1.le hw.2.le hz1.le hz2.le
    have hne : (w - z) ≠ 0 := sub_ne_zero.2 hwz'
    show -(Rf w * Rf z) = slope Rf z w
    rw [slope_def_module, hid', smul_smul]
    have h1 : (w - z)⁻¹ * (z - w) = -1 := by field_simp; ring
    rw [h1]
    exact (neg_one_smul ℂ _).symm
  set Wf : ℂ → B := fun z => (z - c) • Rf z with hWf
  have hWcont : ContinuousOn Wf {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2} :=
    (continuousOn_id.sub continuousOn_const).smul hcont
  have hAnn : ∀ (F : ℂ → B), ContinuousOn F {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2} →
      (∀ z : ℂ, r1 < ‖z - c‖ → ‖z - c‖ < r2 → DifferentiableAt ℂ F z) →
      (∮ z in C(c, r2), F z) = ∮ z in C(c, r1), F z := by
    intro F hF hFd
    have hAnnCont : ContinuousOn F (closedBall c r2 \ ball c r1) := hF.mono (fun z hz => by
      have h1 : dist z c ≤ r2 := hz.1
      have h2 : ¬ dist z c < r1 := hz.2
      rw [dist_eq_norm] at h1 h2
      exact ⟨not_lt.1 h2, h1⟩)
    have hAnnDiff : ∀ z ∈ (ball c r2 \ closedBall c r1) \ (∅ : Set ℂ), DifferentiableAt ℂ F z :=
      fun z hz => by
        have h1 : dist z c < r2 := hz.1.1
        have h2 : ¬ dist z c ≤ r1 := hz.1.2
        rw [dist_eq_norm] at h1 h2
        exact hFd z (not_le.1 h2) h1
    exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr1 hr12.le
      Set.countable_empty hAnnCont hAnnDiff
  have hW : (∮ z in C(c, r2), Wf z) = ∮ z in C(c, r1), Wf z :=
    hAnn Wf hWcont fun z h1 h2 => (differentiableAt_id.sub (differentiableAt_const c)).smul (hderiv z h1 h2)
  have hQ : (∮ z in C(c, r2), Rf z) = ∮ z in C(c, r1), Rf z := hAnn Rf hcont hderiv
  have hn1 : ∀ w ∈ sphere c r1, ‖w - c‖ = r1 := fun w hw => by simpa [mem_sphere_iff_norm] using hw
  have hn2 : ∀ z ∈ sphere c r2, ‖z - c‖ = r2 := fun z hz => by simpa [mem_sphere_iff_norm] using hz
  have hzw : ∀ z ∈ sphere c r2, ∀ w ∈ sphere c r1, z - w ≠ 0 := fun z hz w hw h => by
    have : z = w := sub_eq_zero.1 h
    subst this
    have h1 := hn1 z hw
    have h2 := hn2 z hz
    linarith
  have hcont1 : ContinuousOn Rf (sphere c r1) := hcont.mono hsph1
  have hcont2 : ContinuousOn Rf (sphere c r2) := hcont.mono hsph2
  have hint1 : CircleIntegrable Rf c r1 := hcont1.circleIntegrable hr1.le
  have hint2 : CircleIntegrable Rf c r2 := hcont2.circleIntegrable hr2.le
  have hW1 : ContinuousOn Wf (sphere c r1) := hWcont.mono hsph1
  have hW2 : ContinuousOn Wf (sphere c r2) := hWcont.mono hsph2
  have hWint1 : CircleIntegrable Wf c r1 := hW1.circleIntegrable hr1.le
  have hWint2 : CircleIntegrable Wf c r2 := hW2.circleIntegrable hr2.le
  -- the product identity at points of the inner circle
  have hprod : ∀ z ∈ sphere c r2, ∀ w ∈ sphere c r1,
      Rf z * Rf w = (z - w)⁻¹ • Rf w - (z - w)⁻¹ • Rf z := by
    intro z hz w hw
    have hne := hzw z hz w hw
    have hid' := hid z w (by rw [hn2 z hz]; exact hr12.le) (hn2 z hz).le
      (hn1 w hw).ge (by rw [hn1 w hw]; exact hr12.le)
    have h1 : (z - w) • (Rf z * Rf w) = Rf w - Rf z := by
      have : (z - w) = -(w - z) := by ring
      rw [this, neg_smul, ← hid']; abel
    have h2 : Rf z * Rf w = (z - w)⁻¹ • ((z - w) • (Rf z * Rf w)) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [h2, h1, smul_sub]
  have hinvc : ∀ w ∈ sphere c r1, ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere c r2) := fun w hw =>
    (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hzw z hz w hw)
  have hG : ∀ (g : ℂ → ℂ → ℂ), ContinuousOn (fun p : ℂ × ℂ => g p.1 p.2) (sphere c r2 ×ˢ sphere c r1) →
      ContinuousOn (fun p : ℂ × ℂ => (fun z w : ℂ => (g z w * (z - w)⁻¹) • Rf z) p.1 p.2)
        (sphere c r2 ×ˢ sphere c r1) := by
    intro g hg
    have h1 : ContinuousOn (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹) (sphere c r2 ×ˢ sphere c r1) :=
      (continuousOn_fst.sub continuousOn_snd).inv₀ (fun p hp => hzw p.1 hp.1 p.2 hp.2)
    exact (hg.mul h1).smul (hcont2.comp continuousOn_fst (fun p hp => hp.1))
  -- (b): D_{r₂} P_{r₁}
  have KD : ∀ w ∈ sphere c r1, (∮ z in C(c, r2), Wf z) * Rf w =
      ((2 * Real.pi * Complex.I) * (w - c)) • Rf w - ∮ z in C(c, r2), ((z - c) * (z - w)⁻¹) • Rf z := by
    intro w hw
    have hwb : w ∈ ball c r2 := by rw [mem_ball_iff_norm, hn1 w hw]; exact hr12
    have hΛ := clm_circleIntegral ((ContinuousLinearMap.mul ℂ B).flip (Rf w)) hWint2
    have hpt : ∀ z ∈ sphere c r2, ((ContinuousLinearMap.mul ℂ B).flip (Rf w)) (Wf z) =
        ((z - c) * (z - w)⁻¹) • Rf w - ((z - c) * (z - w)⁻¹) • Rf z := by
      intro z hz
      show ((z - c) • Rf z) * Rf w = _
      rw [smul_mul_assoc, hprod z hz w hw, smul_sub, smul_smul, smul_smul]
    have hI1 : CircleIntegrable (fun z : ℂ => ((z - c) * (z - w)⁻¹) • Rf w) c r2 :=
      (((continuousOn_id.sub continuousOn_const).mul (hinvc w hw)).smul continuousOn_const).circleIntegrable
        hr2.le
    have hI2 : CircleIntegrable (fun z : ℂ => ((z - c) * (z - w)⁻¹) • Rf z) c r2 :=
      (((continuousOn_id.sub continuousOn_const).mul (hinvc w hw)).smul hcont2).circleIntegrable hr2.le
    have h1 : ((ContinuousLinearMap.mul ℂ B).flip (Rf w)) (∮ z in C(c, r2), Wf z) =
        (∮ z in C(c, r2), Wf z) * Rf w := rfl
    rw [← h1, hΛ, circleIntegral.integral_congr hr2.le hpt, circleIntegral.integral_sub hI1 hI2,
      circleIntegral.integral_smul_const, weight_cauchy hwb]
  -- (c): P_{r₂} D_{r₁}
  have KP : ∀ w ∈ sphere c r1, (∮ z in C(c, r2), Rf z) * Wf w =
      ((2 * Real.pi * Complex.I) * (w - c)) • Rf w - ∮ z in C(c, r2), ((w - c) * (z - w)⁻¹) • Rf z := by
    intro w hw
    have hwb : w ∈ ball c r2 := by rw [mem_ball_iff_norm, hn1 w hw]; exact hr12
    have hΛ := clm_circleIntegral ((ContinuousLinearMap.mul ℂ B).flip (Wf w)) hint2
    have hpt : ∀ z ∈ sphere c r2, ((ContinuousLinearMap.mul ℂ B).flip (Wf w)) (Rf z) =
        ((w - c) * (z - w)⁻¹) • Rf w - ((w - c) * (z - w)⁻¹) • Rf z := by
      intro z hz
      show Rf z * ((w - c) • Rf w) = _
      rw [mul_smul_comm, hprod z hz w hw, smul_sub, smul_smul, smul_smul]
    have hI1 : CircleIntegrable (fun z : ℂ => ((w - c) * (z - w)⁻¹) • Rf w) c r2 :=
      ((continuousOn_const.mul (hinvc w hw)).smul continuousOn_const).circleIntegrable hr2.le
    have hI2 : CircleIntegrable (fun z : ℂ => ((w - c) * (z - w)⁻¹) • Rf z) c r2 :=
      ((continuousOn_const.mul (hinvc w hw)).smul hcont2).circleIntegrable hr2.le
    have h1 : ((ContinuousLinearMap.mul ℂ B).flip (Wf w)) (∮ z in C(c, r2), Rf z) =
        (∮ z in C(c, r2), Rf z) * Wf w := rfl
    rw [← h1, hΛ, circleIntegral.integral_congr hr2.le hpt, circleIntegral.integral_sub hI1 hI2,
      circleIntegral.integral_smul_const, circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball hwb]
    congr 1
    rw [mul_comm]
  -- the double integrals vanish
  have KD3 : (∮ w in C(c, r1), ∮ z in C(c, r2), ((z - c) * (z - w)⁻¹) • Rf z) = 0 := by
    rw [circle_swap hr1.le hr2.le (fun z w : ℂ => ((z - c) * (z - w)⁻¹) • Rf z)
      (hG (fun z _ => z - c) (continuousOn_fst.sub continuousOn_const))]
    have : ∀ z ∈ sphere c r2, (∮ w in C(c, r1), ((z - c) * (z - w)⁻¹) • Rf z) = 0 := by
      intro z hz
      rw [circleIntegral.integral_smul_const, circleIntegral.integral_const_mul]
      have hz1 : r1 < ‖z - c‖ := by rw [hn2 z hz]; exact hr12
      have h0 := scalar_inv_zero hr1 hz1
      have : (∮ w in C(c, r1), (z - w)⁻¹) = 0 := by
        have e : (fun w : ℂ => (z - w)⁻¹) = fun w => (-1 : ℂ) * (w - z)⁻¹ := by
          funext w; rw [← neg_sub, inv_neg]; ring
        rw [e, circleIntegral.integral_const_mul, h0, mul_zero]
      rw [this, mul_zero, zero_smul]
    rw [circleIntegral.integral_congr hr2.le this]
    exact const_zero hr2.le 0
  have KP3 : (∮ w in C(c, r1), ∮ z in C(c, r2), ((w - c) * (z - w)⁻¹) • Rf z) = 0 := by
    rw [circle_swap hr1.le hr2.le (fun z w : ℂ => ((w - c) * (z - w)⁻¹) • Rf z)
      (hG (fun _ w => w - c) (continuousOn_snd.sub continuousOn_const))]
    have : ∀ z ∈ sphere c r2, (∮ w in C(c, r1), ((w - c) * (z - w)⁻¹) • Rf z) = 0 := by
      intro z hz
      rw [circleIntegral.integral_smul_const]
      have hz1 : r1 < ‖z - c‖ := by rw [hn2 z hz]; exact hr12
      rw [weight_outer hr1 hz1, zero_smul]
    rw [circleIntegral.integral_congr hr2.le this]
    exact const_zero hr2.le 0
  -- assemble
  have hJD : ContinuousOn (fun w : ℂ => ∮ z in C(c, r2), ((z - c) * (z - w)⁻¹) • Rf z) (sphere c r1) := by
    have : ContinuousOn (fun w : ℂ => ((2 * Real.pi * Complex.I) * (w - c)) • Rf w -
        (∮ z in C(c, r2), Wf z) * Rf w) (sphere c r1) :=
      ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).smul hcont1).sub
        (continuousOn_const.mul hcont1)
    refine this.congr (fun w hw => ?_)
    beta_reduce
    rw [KD w hw]; abel
  have hJP : ContinuousOn (fun w : ℂ => ∮ z in C(c, r2), ((w - c) * (z - w)⁻¹) • Rf z) (sphere c r1) := by
    have : ContinuousOn (fun w : ℂ => ((2 * Real.pi * Complex.I) * (w - c)) • Rf w -
        (∮ z in C(c, r2), Rf z) * Wf w) (sphere c r1) :=
      ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).smul hcont1).sub
        (continuousOn_const.mul hW1)
    refine this.congr (fun w hw => ?_)
    beta_reduce
    rw [KP w hw]; abel
  have hRi : CircleIntegrable (fun w : ℂ => ((2 * Real.pi * Complex.I) * (w - c)) • Rf w) c r1 :=
    ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const)).smul hcont1).circleIntegrable hr1.le
  have hfin : (∮ w in C(c, r1), ((2 * Real.pi * Complex.I) * (w - c)) • Rf w) =
      (2 * Real.pi * Complex.I : ℂ) • ∮ z in C(c, r2), Wf z := by
    rw [hW, ← circleIntegral.integral_smul]
    refine circleIntegral.integral_congr hr1.le fun w _ => ?_
    simp only [hWf, smul_smul]
  refine ⟨hW, ?_, ?_⟩
  · have hΛ := clm_circleIntegral (ContinuousLinearMap.mul ℂ B (∮ z in C(c, r2), Wf z)) hint1
    calc (∮ z in C(c, r2), Wf z) * (∮ w in C(c, r1), Rf w)
        = ∮ w in C(c, r1), (∮ z in C(c, r2), Wf z) * Rf w := hΛ
      _ = ∮ w in C(c, r1), (((2 * Real.pi * Complex.I) * (w - c)) • Rf w -
            ∮ z in C(c, r2), ((z - c) * (z - w)⁻¹) • Rf z) := circleIntegral.integral_congr hr1.le KD
      _ = _ := by
          rw [circleIntegral.integral_sub hRi (hJD.circleIntegrable hr1.le), KD3, sub_zero, hfin]
  · have hΛ := clm_circleIntegral (ContinuousLinearMap.mul ℂ B (∮ z in C(c, r2), Rf z)) hWint1
    calc (∮ z in C(c, r2), Rf z) * (∮ w in C(c, r1), Wf w)
        = ∮ w in C(c, r1), (∮ z in C(c, r2), Rf z) * Wf w := hΛ
      _ = ∮ w in C(c, r1), (((2 * Real.pi * Complex.I) * (w - c)) • Rf w -
            ∮ z in C(c, r2), ((w - c) * (z - w)⁻¹) • Rf z) := circleIntegral.integral_congr hr1.le KP
      _ = _ := by
          rw [circleIntegral.integral_sub hRi (hJP.circleIntegrable hr1.le), KP3, sub_zero, hfin]

variable {L κ : ℝ}

/-- **`D P = D` and `P D = D`** for the actual dressed integral and Riesz projection (radius `r`), whenever the
resolvents exist with one bound on the closed annulus `r/2 ≤ |z − p_n| ≤ r`. -/
theorem dressed_proj_of_annulus {u : ℝ → ℂ} {n : ℤ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ z : ℂ, r / 2 ≤ ‖z - center L n‖ → ‖z - center L n‖ ≤ r →
      ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ u (parity n) z R ∧ ‖R‖ ≤ M) :
    dressedIntegral L κ u n r * perturbedProj L κ u n r = dressedIntegral L κ u n r ∧
      perturbedProj L κ u n r * dressedIntegral L κ u n r = dressedIntegral L κ u n r := by
  set c : ℂ := center L n with hc
  have hr1 : 0 < r / 2 := by positivity
  have hr12 : r / 2 < r := by linarith
  let Rf : ℂ → H2 L →L[ℂ] H2 L := fun z => QuantumNLS.LocalSpectral.resolvent L κ u (parity n) z
  have hres : ∀ z : ℂ, r / 2 ≤ ‖z - c‖ → ‖z - c‖ ≤ r →
      IsResolvent L κ u (parity n) z (Rf z) ∧ ‖Rf z‖ ≤ M := fun z h1 h2 => by
    obtain ⟨R, hR, hn⟩ := hM z h1 h2
    have : Rf z = R := resolvent_eq hR
    rw [this]; exact ⟨hR, hn⟩
  have hM0 : 0 ≤ M := by
    have hn : ‖(c + (r : ℂ)) - c‖ = r := by simp [abs_of_pos hr]
    exact le_trans (norm_nonneg _) (hres (c + r) (by rw [hn]; linarith) hn.le).2
  have hcont : ContinuousOn Rf {z : ℂ | r / 2 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r} :=
    continuousOn_resolvent _ hM0 (fun z hz => ⟨Rf z, (hres z hz.1 hz.2).1, (hres z hz.1 hz.2).2⟩)
  obtain ⟨hA, hB, hC⟩ := algebra_weighted Rf (c := c) hr1 hr12
    (fun z w hz1 hz2 hw1 hw2 => resolvent_identity (hres z hz1 hz2).1 (hres w hw1 hw2).1) hcont
  have hPr := (annulus_idem (L := L) (κ := κ) (u := u) (σ := parity n) (n := n) hr1 hr12 hM).1
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hP1 : perturbedProj L κ u n r = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ w in C(c, r / 2), Rf w := by
    change rieszProj L κ u (parity n) n r = _
    rw [hPr]; rfl
  have hD1 : dressedIntegral L κ u n r = ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ w in C(c, r / 2), (w - c) • Rf w := by
    change ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r), (z - c) • Rf z) = _
    rw [hA]
  constructor
  · conv_lhs => rw [hP1]
    change ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r), (z - c) • Rf z) *
      (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ w in C(c, r / 2), Rf w) =
        ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r), (z - c) • Rf z)
    rw [smul_mul_smul_comm, hB, smul_smul]
    congr 1
    field_simp
  · conv_lhs => rw [hD1]
    change ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r), Rf z) *
      (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • ∮ w in C(c, r / 2), (w - c) • Rf w) =
        ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r), (z - c) • Rf z)
    rw [smul_mul_smul_comm, hC, smul_smul]
    congr 1
    field_simp

/-- Under square-smallness at a label: `D P = D = P D`. -/
theorem dressed_proj (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ}
    {u : Lp ℂ 2 (μI L)} (hu : QuantumNLS.RB01Resolvent.SqSmall L κ r n u) :
    dressedIntegral L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r =
        dressedIntegral L κ (u : ℝ → ℂ) n r ∧
      perturbedProj L κ (u : ℝ → ℂ) n r * dressedIntegral L κ (u : ℝ → ℂ) n r =
        dressedIntegral L κ (u : ℝ → ℂ) n r :=
  dressed_proj_of_annulus hr fun z h1 h2 => QuantumNLS.RB01Resolvent.resolvent_exists hL hr hr2 hu h1 h2

end QuantumNLS.RB01SpecIdem

#print axioms QuantumNLS.RB01SpecIdem.algebra_weighted
#print axioms QuantumNLS.RB01SpecIdem.dressed_proj_of_annulus
#print axioms QuantumNLS.RB01SpecIdem.dressed_proj
