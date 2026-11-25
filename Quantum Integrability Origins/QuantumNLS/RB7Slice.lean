import Mathlib
import QuantumNLS.RB7Smooth

/-!
# R-7B122087 `thm:hierarchy`: the `L²`-derivative of a jointly smooth periodic family (RB7Slice)

Printed use: "`u(t)` is smooth in space and time ... identifies its derivative with ...": a jointly `C^∞` function `G(τ,x)`, `L`-periodic in `x`, has the `L²(𝕋_L)`-valued
curve `τ ↦ [G(τ,·)]` differentiable (in the `L²` norm) with derivative the `L²` class of the pointwise `∂_τ G(τ,·)`.

`hasDerivAt_slice`: `HasDerivAt (τ ↦ smoothL2 (G(τ,·))) (smoothL2 (∂_τ G(s,·))) s`.  Proof: uniform (in `x ∈ [0,L]`, hence in `x ∈ ℝ` by periodicity) first-order Taylor estimate
(mean value inequality + uniform continuity of `∂_τ G` on a compact box), i.e. differentiability of `τ ↦ G(τ,·)` into `C(𝕋_L, ℂ)`, then the bounded linear map `C(𝕋_L,ℂ) → L²`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open scoped ComplexConjugate Topology ContDiff
open MeasureTheory Filter Set Metric

namespace QuantumNLS.RB7

open QuantumNLS.ClassicalCharges QuantumNLS.SmoothScalarMomentsPhysical QuantumNLS.WeakDerivatives

variable {L : ℝ} [Fact (0 < L)]

/-- The `x`-slice of `G` at `τ`. -/
def slice (G : ℝ × ℝ → ℂ) (τ : ℝ) : ℝ → ℂ := fun x => G (τ, x)

/-- The pointwise partial derivative `∂_τ G(τ, x)`. -/
def dslice (G : ℝ × ℝ → ℂ) (τ : ℝ) : ℝ → ℂ := fun x => fderiv ℝ G (τ, x) (1, 0)

theorem hasDerivAt_partial {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ 2 G) (τ x : ℝ) :
    HasDerivAt (fun t : ℝ => G (t, x)) (fderiv ℝ G (τ, x) (1, 0)) τ := by
  have h1 : HasFDerivAt G (fderiv ℝ G (τ, x)) (τ, x) :=
    ((hG.differentiable (by norm_num)) (τ, x)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × ℝ)) ((1, 0) : ℝ × ℝ) τ :=
    (hasDerivAt_id τ).prodMk (hasDerivAt_const τ x)
  exact h1.comp_hasDerivAt τ h2

theorem slice_smooth {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hper : ∀ τ x, G (τ, x + L) = G (τ, x)) (τ : ℝ) :
    SmoothPeriodic L (slice G τ) :=
  ⟨hG.comp (contDiff_const.prodMk contDiff_id), fun x => hper τ x⟩

theorem dslice_smooth {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hper : ∀ τ x, G (τ, x + L) = G (τ, x)) (τ : ℝ) :
    SmoothPeriodic L (dslice G τ) := by
  refine ⟨?_, fun x => ?_⟩
  · have hF : ContDiff ℝ ∞ (fderiv ℝ G) := hG.fderiv_right (by simp)
    exact (hF.clm_apply contDiff_const).comp (contDiff_const.prodMk contDiff_id)
  · have h1 := hasDerivAt_partial (hG.of_le (by simp)) τ (x + L)
    have h2 := hasDerivAt_partial (hG.of_le (by simp)) τ x
    have e : (fun t : ℝ => G (t, x + L)) = fun t : ℝ => G (t, x) := funext fun t => hper t x
    rw [e] at h1
    exact h1.unique h2

/-- Uniform first-order estimate on `x ∈ [0,L]`. -/
theorem taylor_est {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ 2 G) (s : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ τ : ℝ, |τ - s| < δ → ∀ x ∈ Icc (0 : ℝ) L,
      ‖G (τ, x) - G (s, x) - ((τ - s : ℝ) : ℂ) * fderiv ℝ G (s, x) (1, 0)‖ ≤ ε * |τ - s| := by
  have hL : 0 < L := Fact.out
  have hD : Continuous fun p : ℝ × ℝ => fderiv ℝ G p (1, 0) :=
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hK : IsCompact ((Icc (s - 1) (s + 1)) ×ˢ (Icc (0 : ℝ) L)) := isCompact_Icc.prod isCompact_Icc
  have hU := hK.uniformContinuousOn_of_continuous hD.continuousOn
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1 hU ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, fun τ hτ x hx => ?_⟩
  have hτδ : |τ - s| < δ := lt_of_lt_of_le hτ (min_le_left _ _)
  have hτ1 : |τ - s| < 1 := lt_of_lt_of_le hτ (min_le_right _ _)
  -- the auxiliary function
  set c : ℂ := fderiv ℝ G (s, x) (1, 0) with hc
  let φ : ℝ → ℂ := fun t => G (t, x) - (t : ℂ) * c
  have hφ : ∀ t ∈ uIcc s τ, HasDerivWithinAt φ (fderiv ℝ G (t, x) (1, 0) - c) (uIcc s τ) t := by
    intro t _
    have h1 := hasDerivAt_partial hG t x
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * c) c t := by
      have := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const c
      simpa using this
    exact (h1.sub h2).hasDerivWithinAt
  have hb : ∀ t ∈ uIcc s τ, ‖fderiv ℝ G (t, x) (1, 0) - c‖ ≤ ε := by
    intro t ht
    have hts : |t - s| ≤ |τ - s| := by
      rcases le_total s τ with h | h
      · rw [uIcc_of_le h] at ht
        rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]
        linarith [ht.2]
      · rw [uIcc_of_ge h] at ht
        rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]
        linarith [ht.1]
    have ht1 : |t - s| < 1 := lt_of_le_of_lt hts hτ1
    have hmem : (t, x) ∈ (Icc (s - 1) (s + 1)) ×ˢ (Icc (0 : ℝ) L) :=
      ⟨⟨by linarith [(abs_lt.1 ht1).1], by linarith [(abs_lt.1 ht1).2]⟩, hx⟩
    have hsmem : (s, x) ∈ (Icc (s - 1) (s + 1)) ×ˢ (Icc (0 : ℝ) L) :=
      ⟨⟨by linarith, by linarith⟩, hx⟩
    have hd : dist ((t, x) : ℝ × ℝ) (s, x) < δ := by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq, dist_self]
      exact max_lt (lt_of_le_of_lt hts hτδ) hδ
    have := hδε _ hmem _ hsmem hd
    rw [dist_eq_norm] at this
    exact this.le
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hb (convex_uIcc s τ)
    (left_mem_uIcc) (right_mem_uIcc)
  have e : φ τ - φ s = G (τ, x) - G (s, x) - ((τ - s : ℝ) : ℂ) * c := by
    simp only [φ]; push_cast; ring
  rw [e, Real.norm_eq_abs] at hmvt
  simpa [mul_comm] using hmvt

/-- `τ ↦ G(τ, ·)` is differentiable into `C(𝕋_L, ℂ)`. -/
theorem hasDerivAt_liftC {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hper : ∀ τ x, G (τ, x + L) = G (τ, x)) (s : ℝ) :
    HasDerivAt (fun τ : ℝ => (liftC (slice_smooth hG hper τ).smooth.continuous (slice_smooth hG hper τ).periodic :
        C(AddCircle L, ℂ)))
      (liftC (dslice_smooth hG hper s).smooth.continuous (dslice_smooth hG hper s).periodic) s := by
  have hL : 0 < L := Fact.out
  have hG2 : ContDiff ℝ 2 G := hG.of_le (by simp)
  rw [hasDerivAt_iff_isLittleO]
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hest⟩ := taylor_est (L := L) hG2 s hε
  filter_upwards [Metric.ball_mem_nhds s hδ] with τ hτ
  have hτ' : |τ - s| < δ := by simpa [Real.dist_eq] using hτ
  rw [Real.norm_eq_abs (τ - s)]
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun p => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective p
  -- the quantity is periodic in `y`
  let P : ℝ → ℝ := fun x => ‖G (τ, x) - G (s, x) - ((τ - s : ℝ) : ℂ) * fderiv ℝ G (s, x) (1, 0)‖
  have hP : Function.Periodic P L := by
    intro x
    simp only [P]
    rw [hper τ x, hper s x]
    have := (dslice_smooth hG hper s).periodic x
    simp only [dslice] at this
    rw [this]
  obtain ⟨x, hx, hxy⟩ := hP.exists_mem_Ico₀ hL y
  have h1 : ‖(((liftC (slice_smooth hG hper τ).smooth.continuous (slice_smooth hG hper τ).periodic :
        C(AddCircle L, ℂ)) - liftC (slice_smooth hG hper s).smooth.continuous (slice_smooth hG hper s).periodic -
        (τ - s) • liftC (dslice_smooth hG hper s).smooth.continuous
          (dslice_smooth hG hper s).periodic) : C(AddCircle L, ℂ)) (y : AddCircle L)‖ = P y := by
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, liftC_coe, slice, dslice, P, Complex.real_smul]
  rw [h1, hxy]
  exact hest τ hτ' x ⟨hx.1, hx.2.le⟩

/-- **The `L²`-derivative of a jointly smooth periodic family** (`smoothL2` of the slices). -/
theorem hasDerivAt_slice {G : ℝ × ℝ → ℂ} (hG : ContDiff ℝ ∞ G) (hper : ∀ τ x, G (τ, x + L) = G (τ, x)) (s : ℝ) :
    HasDerivAt (fun τ : ℝ => smoothL2 (slice_smooth hG hper τ)) (smoothL2 (dslice_smooth hG hper s)) s := by
  have h := hasDerivAt_liftC hG hper s
  let T : C(AddCircle L, ℂ) →L[ℝ] QuantumNLS.PhysicalTensor.L2T L :=
    ((ContinuousMap.toLp (E := ℂ) 2 (volume : Measure (AddCircle L)) ℂ :
      C(AddCircle L, ℂ) →L[ℂ] QuantumNLS.PhysicalTensor.L2T L)).restrictScalars ℝ
  exact T.hasFDerivAt.comp_hasDerivAt s h

end QuantumNLS.RB7

#print axioms QuantumNLS.RB7.taylor_est
#print axioms QuantumNLS.RB7.hasDerivAt_slice
