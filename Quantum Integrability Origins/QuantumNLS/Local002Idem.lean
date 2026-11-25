import Mathlib
import QuantumNLS.Local002Hyp
import QuantumNLS.Local002Circle

/-! LOCAL-002 stage E: Riesz projections of `𝓛_u` are idempotent and independent of the radius.

`annulus_idem` is purely operator-theoretic in the frozen DEF-049 encoding: if resolvents (`IsResolvent`)
exist on the closed annulus `r1 ≤ |z - p_n| ≤ r2` with a uniform bound, then
`rieszProj ... r2 = rieszProj ... r1` (Cauchy on the annulus; the resolvent is holomorphic with derivative
`-R²` by the resolvent identity) and `P² = P` (resolvent identity on `Γ_{r2} × Γ_{r1}` plus Fubini). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal ComplexConjugate
namespace QuantumNLS.Local002Idem
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Circle

variable {L κ : ℝ}

lemma scalar_inv_zero {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r < ‖z - c‖) :
    ∮ w in C(c, r), (w - z)⁻¹ = 0 := by
  have hne : ∀ w ∈ closedBall c r, w - z ≠ 0 := fun w hw h => by
    have : w = z := sub_eq_zero.1 h
    subst this
    have := mem_closedBall.1 hw
    rw [dist_eq_norm] at this
    linarith
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le
    Set.countable_empty ?_ ?_
  · intro w hw
    exact ((continuousAt_id.sub continuousAt_const).inv₀ (hne w hw)).continuousWithinAt
  · intro w hw
    exact (differentiableAt_id.sub (differentiableAt_const _)).inv (hne w (ball_subset_closedBall hw.1))

/-- **Abstract annulus idempotence**: for a family `Rf : ℂ → B` in a Banach algebra satisfying the
resolvent identity `Rf z - Rf w = (w - z) Rf z Rf w` and continuous on the closed annulus
`r₁ ≤ |z - c| ≤ r₂`, the circle integrals over `|z-c| = r₂` and `|z-c| = r₁` agree and
`(∮ Rf)² = 2πi ∮ Rf`. -/
theorem algebra_idem {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]
    (Rf : ℂ → B) {c : ℂ} {r1 r2 : ℝ} (hr1 : 0 < r1) (hr12 : r1 < r2)
    (hid : ∀ z w : ℂ, r1 ≤ ‖z - c‖ → ‖z - c‖ ≤ r2 → r1 ≤ ‖w - c‖ → ‖w - c‖ ≤ r2 →
      Rf z - Rf w = (w - z) • (Rf z * Rf w))
    (hcont : ContinuousOn Rf {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2}) :
    (∮ z in C(c, r2), Rf z) = (∮ z in C(c, r1), Rf z) ∧
      (∮ z in C(c, r2), Rf z) * (∮ z in C(c, r2), Rf z) =
        (2 * Real.pi * Complex.I : ℂ) • ∮ z in C(c, r2), Rf z := by
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
  have hAnnCont : ContinuousOn Rf (closedBall c r2 \ ball c r1) := hcont.mono (fun z hz => by
    have h1 : dist z c ≤ r2 := hz.1
    have h2 : ¬ dist z c < r1 := hz.2
    rw [dist_eq_norm] at h1 h2
    exact ⟨not_lt.1 h2, h1⟩)
  have hAnnDiff : ∀ z ∈ (ball c r2 \ closedBall c r1) \ (∅ : Set ℂ), DifferentiableAt ℂ Rf z :=
    fun z hz => by
      have h1 : dist z c < r2 := hz.1.1
      have h2 : ¬ dist z c ≤ r1 := hz.1.2
      rw [dist_eq_norm] at h1 h2
      exact hderiv z (not_le.1 h2) h1
  have hQ : (∮ z in C(c, r2), Rf z) = ∮ z in C(c, r1), Rf z :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr1 hr12.le
      Set.countable_empty hAnnCont hAnnDiff
  refine ⟨hQ, ?_⟩
  have hint1 : CircleIntegrable Rf c r1 := (hcont.mono hsph1).circleIntegrable hr1.le
  have hint2 : CircleIntegrable Rf c r2 := (hcont.mono hsph2).circleIntegrable hr2.le
  have hn1 : ∀ w ∈ sphere c r1, ‖w - c‖ = r1 := fun w hw => by
    simpa [mem_sphere_iff_norm] using hw
  have hn2 : ∀ z ∈ sphere c r2, ‖z - c‖ = r2 := fun z hz => by
    simpa [mem_sphere_iff_norm] using hz
  have hzw : ∀ z ∈ sphere c r2, ∀ w ∈ sphere c r1, z - w ≠ 0 := fun z hz w hw h => by
    have : z = w := sub_eq_zero.1 h
    subst this
    have h1 := hn1 z hw
    have h2 := hn2 z hz
    linarith
  have hcont1 : ContinuousOn Rf (sphere c r1) := hcont.mono hsph1
  have hcont2 : ContinuousOn Rf (sphere c r2) := hcont.mono hsph2
  obtain ⟨Q2, hQ2⟩ : ∃ Q2 : B, Q2 = ∮ z in C(c, r2), Rf z := ⟨_, rfl⟩
  have K1 : ∀ w ∈ sphere c r1, Q2 * Rf w =
      (2 * Real.pi * Complex.I : ℂ) • Rf w - ∮ z in C(c, r2), (z - w)⁻¹ • Rf z := by
    intro w hw
    have hwb : w ∈ ball c r2 := by
      rw [mem_ball_iff_norm, hn1 w hw]; exact hr12
    have hΛ := clm_circleIntegral ((ContinuousLinearMap.mul ℂ B).flip (Rf w)) hint2
    have hpt : ∀ z ∈ sphere c r2, ((ContinuousLinearMap.mul ℂ B).flip (Rf w)) (Rf z) =
        (z - w)⁻¹ • Rf w - (z - w)⁻¹ • Rf z := by
      intro z hz
      have hne := hzw z hz w hw
      have hid' := hid z w (by rw [hn2 z hz]; exact hr12.le) (hn2 z hz).le
        (hn1 w hw).ge (by rw [hn1 w hw]; exact hr12.le)
      show Rf z * Rf w = _
      have h1 : (z - w) • (Rf z * Rf w) = Rf w - Rf z := by
        have : (z - w) = -(w - z) := by ring
        rw [this, neg_smul, ← hid']; abel
      have h2 : Rf z * Rf w = (z - w)⁻¹ • ((z - w) • (Rf z * Rf w)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [h2, h1, smul_sub]
    have hinv : ContinuousOn (fun z : ℂ => (z - w)⁻¹) (sphere c r2) :=
      (continuousOn_id.sub continuousOn_const).inv₀ (fun z hz => hzw z hz w hw)
    have hI1 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ • Rf w) c r2 :=
      (hinv.smul continuousOn_const).circleIntegrable hr2.le
    have hI2 : CircleIntegrable (fun z : ℂ => (z - w)⁻¹ • Rf z) c r2 :=
      (hinv.smul hcont2).circleIntegrable hr2.le
    have h1 : ((ContinuousLinearMap.mul ℂ B).flip (Rf w)) (∮ z in C(c, r2), Rf z) =
        Q2 * Rf w := by rw [hQ2]; rfl
    rw [← h1, hΛ, circleIntegral.integral_congr hr2.le hpt, circleIntegral.integral_sub hI1 hI2,
      circleIntegral.integral_smul_const, circleIntegral.integral_sub_inv_of_mem_ball hwb]
  have K3 : (∮ w in C(c, r1), ∮ z in C(c, r2), (z - w)⁻¹ • Rf z) = 0 := by
    have hG : ContinuousOn (fun p : ℂ × ℂ => (fun z w : ℂ => (z - w)⁻¹ • Rf z) p.1 p.2)
        (sphere c r2 ×ˢ sphere c r1) := by
      have h1 : ContinuousOn (fun p : ℂ × ℂ => (p.1 - p.2)⁻¹) (sphere c r2 ×ˢ sphere c r1) :=
        (continuousOn_fst.sub continuousOn_snd).inv₀ (fun p hp => hzw p.1 hp.1 p.2 hp.2)
      exact h1.smul (hcont2.comp continuousOn_fst (fun p hp => hp.1))
    rw [circle_swap hr1.le hr2.le (fun z w : ℂ => (z - w)⁻¹ • Rf z) hG]
    have : ∀ z ∈ sphere c r2, (∮ w in C(c, r1), (z - w)⁻¹ • Rf z) = 0 := by
      intro z hz
      rw [circleIntegral.integral_smul_const]
      have hz1 : r1 < ‖z - c‖ := by rw [hn2 z hz]; exact hr12
      have h0 := scalar_inv_zero hr1 hz1
      have : (∮ w in C(c, r1), (z - w)⁻¹) = 0 := by
        have e : (fun w : ℂ => (z - w)⁻¹) = fun w => (-1 : ℂ) * (w - z)⁻¹ := by
          funext w; rw [← neg_sub, inv_neg]; ring
        rw [e, circleIntegral.integral_const_mul, h0, mul_zero]
      rw [this]
      exact zero_smul ℂ _
    rw [circleIntegral.integral_congr hr2.le this]
    simp [circleIntegral]
  have hΛ := clm_circleIntegral (ContinuousLinearMap.mul ℂ B Q2) hint1
  have h1 : (ContinuousLinearMap.mul ℂ B Q2) (∮ w in C(c, r1), Rf w) =
      Q2 * (∮ w in C(c, r1), Rf w) := rfl
  have hJc : ContinuousOn (fun w : ℂ => ∮ z in C(c, r2), (z - w)⁻¹ • Rf z) (sphere c r1) := by
    have : ContinuousOn (fun w : ℂ => (2 * Real.pi * Complex.I : ℂ) • Rf w - Q2 * Rf w)
        (sphere c r1) :=
      (hcont1.const_smul _).sub (continuousOn_const.mul hcont1)
    refine this.congr (fun w hw => ?_)
    beta_reduce
    rw [K1 w hw]; abel
  have hJi : CircleIntegrable (fun w : ℂ => ∮ z in C(c, r2), (z - w)⁻¹ • Rf z) c r1 :=
    hJc.circleIntegrable hr1.le
  have hRi : CircleIntegrable (fun w : ℂ => (2 * Real.pi * Complex.I : ℂ) • Rf w) c r1 :=
    (hcont1.const_smul _).circleIntegrable hr1.le
  rw [← hQ2]
  calc Q2 * Q2 = Q2 * (∮ w in C(c, r1), Rf w) := by rw [← hQ, ← hQ2]
    _ = ∮ w in C(c, r1), Q2 * Rf w := by rw [← h1, hΛ]; rfl
    _ = ∮ w in C(c, r1), ((2 * Real.pi * Complex.I : ℂ) • Rf w -
          ∮ z in C(c, r2), (z - w)⁻¹ • Rf z) := circleIntegral.integral_congr hr1.le K1
    _ = (∮ w in C(c, r1), (2 * Real.pi * Complex.I : ℂ) • Rf w) -
          ∮ w in C(c, r1), ∮ z in C(c, r2), (z - w)⁻¹ • Rf z :=
        circleIntegral.integral_sub hRi hJi
    _ = (2 * Real.pi * Complex.I : ℂ) • Q2 := by
        rw [K3, sub_zero, hQ2, hQ]
        exact circleIntegral.integral_smul (2 * Real.pi * Complex.I : ℂ) Rf c r1

theorem annulus_idem {u : ℝ → ℂ} {σ : ℤˣ} {n : ℤ} {r1 r2 M : ℝ} (hr1 : 0 < r1) (hr12 : r1 < r2)
    (hM : ∀ z : ℂ, r1 ≤ ‖z - center L n‖ → ‖z - center L n‖ ≤ r2 →
      ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ u σ z R ∧ ‖R‖ ≤ M) :
    rieszProj L κ u σ n r2 = rieszProj L κ u σ n r1 ∧
      rieszProj L κ u σ n r2 * rieszProj L κ u σ n r2 = rieszProj L κ u σ n r2 := by
  set c : ℂ := center L n with hc
  let Rf : ℂ → H2 L →L[ℂ] H2 L := fun z => QuantumNLS.LocalSpectral.resolvent L κ u σ z
  have hres : ∀ z : ℂ, r1 ≤ ‖z - c‖ → ‖z - c‖ ≤ r2 → IsResolvent L κ u σ z (Rf z) ∧ ‖Rf z‖ ≤ M :=
    fun z h1 h2 => by
      obtain ⟨R, hR, hn⟩ := hM z h1 h2
      have : Rf z = R := resolvent_eq hR
      rw [this]; exact ⟨hR, hn⟩
  have hM0 : 0 ≤ M := by
    have hn : ‖(c + (r1 : ℂ)) - c‖ = r1 := by simp [abs_of_pos hr1]
    have := (hres (c + r1) hn.ge (by rw [hn]; exact hr12.le)).2
    exact le_trans (norm_nonneg _) this
  have hcont : ContinuousOn Rf {z : ℂ | r1 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ r2} :=
    continuousOn_resolvent _ hM0
      (fun z hz => ⟨Rf z, (hres z hz.1 hz.2).1, (hres z hz.1 hz.2).2⟩)
  obtain ⟨hA, hB⟩ := algebra_idem Rf (c := c) hr1 hr12
    (fun z w hz1 hz2 hw1 hw2 => resolvent_identity (hres z hz1 hz2).1 (hres w hw1 hw2).1) hcont
  refine ⟨?_, ?_⟩
  · show ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r2), Rf z) =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r1), Rf z)
    rw [hA]
  · show ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r2), Rf z) *
        (((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r2), Rf z)) =
      ((2 * Real.pi * Complex.I)⁻¹ : ℂ) • (∮ z in C(c, r2), Rf z)
    rw [smul_mul_smul_comm, hB, smul_smul]
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    congr 1
    field_simp

end QuantumNLS.Local002Idem
#print axioms QuantumNLS.Local002Idem.algebra_idem
#print axioms QuantumNLS.Local002Idem.annulus_idem
