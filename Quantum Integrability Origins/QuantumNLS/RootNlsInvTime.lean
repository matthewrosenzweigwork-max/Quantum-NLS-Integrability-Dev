import Mathlib
import QuantumNLS.L1Stability

/-!
# R-BFCC01E8, stage 1: time differentiability of the spatial transfer

Source: `ROOT_nls_invariance.tex`, proof of `thm:root-nls-invariance`, second paragraph:
"The integral equation for `M` and its differentiated integral equation give continuous time
differentiability ... The derivative satisfies `(M_t)_x = A_t M + A M_t` and `M_t(0) = 0`."

Generic statement (any complete normed `ℝ`-algebra `𝔸`). Let `A t` be a family of coefficients,
continuous on `[0,L]`, differentiable in `t` within a set `J` at `t₀` uniformly on `[0,L]` with
derivative `Ad`. If `W` is a continuous solution of the differentiated integral equation
`W(x) = ∫₀ˣ (A(t₀) W + Ad · M(t₀))`, `M(t) = transfer (A t)`, then `t ↦ M(t)(L)` has derivative
`W(L)` within `J` at `t₀`. The proof is the Volterra/Gronwall estimate of the remainder
`M(t) − M(t₀) − (t − t₀) W` (frozen `L1Stability.gronwall_integral`), which is the factorial-majorant
argument of the source.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Asymptotics
open scoped Interval

namespace QuantumNLS.RootNlsInvTime
open QuantumNLS.L1SpatialTransfer QuantumNLS.L1Stability

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

lemma uIcc_sub {L x : ℝ} (hx : x ∈ Icc 0 L) : uIcc (0 : ℝ) x ⊆ Icc 0 L := by
  rw [uIcc_of_le hx.1]; exact Icc_subset_Icc_right hx.2

/-- Gronwall for the inhomogeneous Volterra equation `D = g + ∫₀ˣ A D`. -/
theorem norm_le_of_inhom {A D g : ℝ → 𝔸} {L γ : ℝ} (hL : 0 ≤ L)
    (hA : ContinuousOn A (Icc 0 L)) (hD : ContinuousOn D (Icc 0 L))
    (hg : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ γ)
    (he : ∀ x ∈ Icc 0 L, D x = g x + ∫ s in (0 : ℝ)..x, A s * D s) :
    ∀ x ∈ Icc 0 L, ‖D x‖ ≤ γ * Real.exp (∫ s in (0 : ℝ)..x, ‖A s‖) := by
  have hAi : IntervalIntegrable (fun s => ‖A s‖) volume 0 L :=
    hA.norm.intervalIntegrable_of_Icc hL
  apply gronwall_integral hL hAi (fun s => norm_nonneg _) hD.norm
  intro x hx
  have hsub := uIcc_sub hx
  have hp : IntervalIntegrable (fun s => A s * D s) volume 0 x :=
    ((hA.mono hsub).mul (hD.mono hsub)).intervalIntegrable
  have hn : IntervalIntegrable (fun s => ‖A s‖ * ‖D s‖) volume 0 x :=
    ((hA.mono hsub).norm.mul (hD.mono hsub).norm).intervalIntegrable
  calc ‖D x‖ = ‖g x + ∫ s in (0 : ℝ)..x, A s * D s‖ := by rw [he x hx]
    _ ≤ ‖g x‖ + ‖∫ s in (0 : ℝ)..x, A s * D s‖ := norm_add_le _ _
    _ ≤ γ + ∫ s in (0 : ℝ)..x, ‖A s‖ * ‖D s‖ := by
      gcongr
      · exact hg x hx
      · calc _ ≤ ∫ s in (0 : ℝ)..x, ‖A s * D s‖ :=
              intervalIntegral.norm_integral_le_integral_norm hx.1
          _ ≤ _ := intervalIntegral.integral_mono_on hx.1 hp.norm hn (fun s _ => norm_mul_le _ _)

/-- Pointwise algebra of the remainder equation. -/
lemma remainder_algebra (At A0 Ad M0 Mt W : 𝔸) (h : ℝ) :
    ((At - A0 - h • Ad) * M0 + h • ((At - A0) * W)) + At * (Mt - M0 - h • W) =
      At * Mt - A0 * M0 - h • (A0 * W + Ad * M0) := by
  simp only [mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]
  abel

/-- **Time differentiability of the transfer at the period endpoint.** -/
theorem hasDerivWithinAt_transfer {A : ℝ → ℝ → 𝔸} {Ad W : ℝ → 𝔸} {J : Set ℝ} {t₀ L : ℝ}
    (hL : 0 ≤ L)
    (hA : ∀ t, ContinuousOn (A t) (Icc 0 L))
    (hAd : ContinuousOn Ad (Icc 0 L))
    (hW : ContinuousOn W (Icc 0 L))
    (hlin : ∀ ε > 0, ∀ᶠ t in 𝓝[J] t₀, ∀ x ∈ Icc 0 L,
        ‖A t x - A t₀ x - (t - t₀) • Ad x‖ ≤ ε * |t - t₀|)
    (hWe : ∀ x ∈ Icc 0 L,
        W x = ∫ s in (0 : ℝ)..x, (A t₀ s * W s + Ad s * transfer (A t₀) s)) :
    HasDerivWithinAt (fun t => transfer (A t) L) (W L) J t₀ := by
  have hAi : ∀ t, IntervalIntegrable (A t) volume 0 L := fun t => (hA t).intervalIntegrable_of_Icc hL
  have hMc : ∀ t, ContinuousOn (transfer (A t)) (Icc 0 L) := fun t => continuousOn_transfer hL (hAi t)
  have hMe : ∀ t, ∀ x ∈ Icc 0 L, transfer (A t) x = 1 + ∫ s in (0 : ℝ)..x, A t s * transfer (A t) s :=
    fun t x hx => transfer_integral_eq hL (hAi t) hx
  have hLm : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  -- uniform bounds at `t₀`
  obtain ⟨m, hm⟩ := isCompact_Icc.exists_bound_of_continuousOn (hMc t₀)
  obtain ⟨w, hw⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  obtain ⟨α, hα⟩ := isCompact_Icc.exists_bound_of_continuousOn hAd
  obtain ⟨a₀, ha₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA t₀)
  have hm0 : 0 ≤ m := (norm_nonneg _).trans (hm L hLm)
  have hw0 : 0 ≤ w := (norm_nonneg _).trans (hw L hLm)
  have hα0 : 0 ≤ α := (norm_nonneg _).trans (hα L hLm)
  have ha00 : 0 ≤ a₀ := (norm_nonneg _).trans (ha₀ L hLm)
  set a : ℝ := a₀ + α + 1 with ha
  set E : ℝ := Real.exp (a * L) with hE
  set K : ℝ := E * L * (m + (α + 1) * w) + 1 with hK
  have hE0 : 0 < E := Real.exp_pos _
  have hK0 : 0 < K := by positivity
  rw [hasDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  set ε : ℝ := min 1 (c / K) with hε
  have hε0 : 0 < ε := lt_min one_pos (div_pos hc hK0)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεK : ε * K ≤ c := by
    have := min_le_right 1 (c / K)
    rw [← hε] at this
    calc ε * K ≤ c / K * K := mul_le_mul_of_nonneg_right this hK0.le
      _ = c := div_mul_cancel₀ c hK0.ne'
  have hnear : ∀ᶠ t in 𝓝[J] t₀, |t - t₀| < ε := by
    apply nhdsWithin_le_nhds
    filter_upwards [Metric.ball_mem_nhds t₀ hε0] with t ht
    rwa [Metric.mem_ball, Real.dist_eq] at ht
  filter_upwards [hlin ε hε0, hnear] with t hlt hnt
  set h : ℝ := t - t₀ with hh
  have hh1 : |h| ≤ 1 := hnt.le.trans hε1
  -- coefficient bounds at time t
  have hdiff : ∀ x ∈ Icc 0 L, ‖A t x - A t₀ x‖ ≤ (α + 1) * |h| := by
    intro x hx
    have e1 : A t x - A t₀ x = (A t x - A t₀ x - h • Ad x) + h • Ad x := by abel
    rw [e1]
    calc _ ≤ ‖A t x - A t₀ x - h • Ad x‖ + ‖h • Ad x‖ := norm_add_le _ _
      _ ≤ ε * |h| + |h| * α := by
        gcongr
        · exact hlt x hx
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hα x hx) (abs_nonneg _)
      _ ≤ 1 * |h| + |h| * α := by gcongr
      _ = (α + 1) * |h| := by ring
  have hAt : ∀ x ∈ Icc 0 L, ‖A t x‖ ≤ a := by
    intro x hx
    have e1 : A t x = A t₀ x + (A t x - A t₀ x) := by abel
    rw [e1]
    calc _ ≤ ‖A t₀ x‖ + ‖A t x - A t₀ x‖ := norm_add_le _ _
      _ ≤ a₀ + (α + 1) * 1 := by
        gcongr
        · exact ha₀ x hx
        · exact (hdiff x hx).trans (mul_le_mul_of_nonneg_left hh1 (by linarith))
      _ = a := by rw [ha]; ring
  -- the remainder and its equation
  set D : ℝ → 𝔸 := fun x => transfer (A t) x - transfer (A t₀) x - h • W x with hD
  set G : ℝ → 𝔸 := fun s => (A t s - A t₀ s - h • Ad s) * transfer (A t₀) s +
    h • ((A t s - A t₀ s) * W s) with hG
  set g : ℝ → 𝔸 := fun x => ∫ s in (0 : ℝ)..x, G s with hg
  have hDc : ContinuousOn D (Icc 0 L) := ((hMc t).sub (hMc t₀)).sub (hW.const_smul h)
  have hGc : ContinuousOn G (Icc 0 L) :=
    ((((hA t).sub (hA t₀)).sub (hAd.const_smul h)).mul (hMc t₀)).add
      ((((hA t).sub (hA t₀)).mul hW).const_smul h)
  have heq : ∀ x ∈ Icc 0 L, D x = g x + ∫ s in (0 : ℝ)..x, A t s * D s := by
    intro x hx
    have hs := uIcc_sub hx
    have i1 : IntervalIntegrable (fun s => A t s * transfer (A t) s) volume 0 x :=
      (((hA t).mono hs).mul ((hMc t).mono hs)).intervalIntegrable
    have i2 : IntervalIntegrable (fun s => A t₀ s * transfer (A t₀) s) volume 0 x :=
      (((hA t₀).mono hs).mul ((hMc t₀).mono hs)).intervalIntegrable
    have i3 : IntervalIntegrable (fun s => A t₀ s * W s + Ad s * transfer (A t₀) s) volume 0 x :=
      ((((hA t₀).mono hs).mul (hW.mono hs)).add ((hAd.mono hs).mul ((hMc t₀).mono hs))).intervalIntegrable
    have iG : IntervalIntegrable G volume 0 x := (hGc.mono hs).intervalIntegrable
    have iD : IntervalIntegrable (fun s => A t s * D s) volume 0 x :=
      (((hA t).mono hs).mul (hDc.mono hs)).intervalIntegrable
    have hsum : g x + ∫ s in (0 : ℝ)..x, A t s * D s =
        ∫ s in (0 : ℝ)..x, (A t s * transfer (A t) s - A t₀ s * transfer (A t₀) s -
          h • (A t₀ s * W s + Ad s * transfer (A t₀) s)) := by
      rw [hg]
      simp only
      rw [← intervalIntegral.integral_add iG iD]
      apply intervalIntegral.integral_congr
      intro s _
      simp only [hG, hD]
      exact remainder_algebra _ _ _ _ _ _ _
    have i3' : IntervalIntegrable (fun s => h • (A t₀ s * W s + Ad s * transfer (A t₀) s))
        volume 0 x := i3.smul h
    rw [hsum, intervalIntegral.integral_sub (i1.sub i2) i3',
      intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_smul, ← hWe x hx]
    simp only [hD]
    rw [hMe t x hx, hMe t₀ x hx]
    abel
  -- bound on the inhomogeneity
  set γ : ℝ := L * (|h| * (ε * (m + (α + 1) * w))) with hγ
  have hgb : ∀ x ∈ Icc 0 L, ‖g x‖ ≤ γ := by
    intro x hx
    have hpt : ∀ s ∈ Ι (0 : ℝ) x, ‖G s‖ ≤ |h| * (ε * (m + (α + 1) * w)) := by
      intro s hs'
      have hs : s ∈ Icc 0 L := by
        rw [uIoc_of_le hx.1] at hs'
        exact ⟨hs'.1.le, hs'.2.trans hx.2⟩
      simp only [hG]
      calc _ ≤ ‖(A t s - A t₀ s - h • Ad s) * transfer (A t₀) s‖ +
            ‖h • ((A t s - A t₀ s) * W s)‖ := norm_add_le _ _
        _ ≤ (ε * |h|) * m + |h| * (((α + 1) * |h|) * w) := by
          gcongr
          · exact (norm_mul_le _ _).trans
              (mul_le_mul (hlt s hs) (hm s hs) (norm_nonneg _) (by positivity))
          · rw [norm_smul, Real.norm_eq_abs]
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            exact (norm_mul_le _ _).trans
              (mul_le_mul (hdiff s hs) (hw s hs) (norm_nonneg _) (by positivity))
        _ ≤ (ε * |h|) * m + |h| * (((α + 1) * ε) * w) := by
          gcongr
        _ = |h| * (ε * (m + (α + 1) * w)) := by ring
    have := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [sub_zero, abs_of_nonneg hx.1] at this
    calc ‖g x‖ ≤ |h| * (ε * (m + (α + 1) * w)) * x := this
      _ ≤ |h| * (ε * (m + (α + 1) * w)) * L := by
        apply mul_le_mul_of_nonneg_left hx.2; positivity
      _ = γ := by rw [hγ]; ring
  have hAtc : ContinuousOn (A t) (Icc 0 L) := hA t
  have hgr := norm_le_of_inhom hL hAtc hDc hgb heq L hLm
  have hint : (∫ s in (0 : ℝ)..L, ‖A t s‖) ≤ a * L := by
    have hb : ∀ s ∈ Ι (0 : ℝ) L, ‖‖A t s‖‖ ≤ a := by
      intro s hs'
      rw [uIoc_of_le hL] at hs'
      rw [norm_norm]
      exact hAt s ⟨hs'.1.le, hs'.2⟩
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [sub_zero, abs_of_nonneg hL] at this
    exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact this)
  have hexp : Real.exp (∫ s in (0 : ℝ)..L, ‖A t s‖) ≤ E := Real.exp_le_exp.mpr hint
  have hγ0 : 0 ≤ γ := by positivity
  change ‖transfer (A t) L - transfer (A t₀) L - (t - t₀) • W L‖ ≤ c * ‖t - t₀‖
  rw [Real.norm_eq_abs, ← hh]
  calc ‖D L‖ ≤ γ * Real.exp (∫ s in (0 : ℝ)..L, ‖A t s‖) := hgr
    _ ≤ γ * E := mul_le_mul_of_nonneg_left hexp hγ0
    _ = ε * (E * L * (m + (α + 1) * w)) * |h| := by rw [hγ]; ring
    _ ≤ ε * K * |h| := by
        gcongr
        rw [hK]; linarith
    _ ≤ c * |h| := mul_le_mul_of_nonneg_right hεK (abs_nonneg _)

end QuantumNLS.RootNlsInvTime

#print axioms QuantumNLS.RootNlsInvTime.norm_le_of_inhom
#print axioms QuantumNLS.RootNlsInvTime.hasDerivWithinAt_transfer
