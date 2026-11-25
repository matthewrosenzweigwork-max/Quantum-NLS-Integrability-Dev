import QuantumNLS.Prop025OTraj
import QuantumNLS.ActualModelTargetR53a
import QuantumNLS.Def044ChartR28m
import QuantumNLS.RB7BindTopology

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O5b-4:
**the classical-target identification** (source lines 589-654, eq:MP-classical-window-error).

"The simultaneous finite-action phase is an isometry on every sequence Sobolev space and is identical in the two
expressions.  Thus the window-removal proof of Proposition prop:window applies with that common phase ...
`‖v_{a,t,θ} − Φ_t(Φ_I(θ)u)‖_{L²} ≤ C a^{−1/4}`."

* `window_fderiv_u`, `grad_at_u`: the frozen O5b-1 `window_fderiv` / `grad_at` with the cut threshold chosen
  BEFORE the joint times (the frozen proofs choose it independently of `t`; the bodies are copied verbatim, only the
  quantifier order is changed), so that the gradient agreement is uniform on the time box;
* `angleL`, `Tθ_angleL`: the finitely supported angle vector `θ_I` and `T_{θ_I} = Φ_I(θ)` (the R53a `rotate`,
  via the accepted `rotate_eq_action`);
* `physical_injective`, `rotateSmooth_congr`, `continuous_rotateSmooth`, `isCompact_rotClass`: the rotated smooth
  data `{Φ_I(θ)u : |θ_n| ≤ Θ_n}` form a compact class in `Smooth L` (the DEF-044 clause (2) Sobolev restrictions of
  the chart, finitely many rotated coordinates, `RB7BindTopology.continuous_toSmooth`);
* **`classical_target`**: for every solution `γ` of the frozen affine equation `γ' = X_F(γ)`, `γ(0) = u`
  (`F = coh(mixK)` at a large regular cut, torus invariant and differentiable), `‖γ(1) − Φ_t(Φ_I(θ)u)‖ ≤ C a^{−1/4}`,
  one `C` and one cut threshold for all times and angles in the boxes; `Φ_t(Φ_I(θ)u)` is literally the R53a
  `target`.  The named input is `Prop025OInputs.WindowInput` (R-E59628C9), applied through `window_spec` with the
  DEF-044 chart (`Def044ChartR28m.printed_chart`, `sobolev_iff`).
No hypothesis is added beyond the stated ones; all inherited modules are read-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open scoped Topology NNReal ENNReal
open MeasureTheory Filter Set Metric Complex

namespace QuantumNLS.Prop025OTarget
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Extrapolation (Gfull)
open QuantumNLS.PeriodReconstructionCore (Df Af ef)
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT continuous_zθ continuous_uθ)
open QuantumNLS.MPFixedContour (rectGen rectGen_mem_Gam)
open QuantumNLS.Prop026Uniform (rectFamily)
open QuantumNLS.Prop025OPhase (mixedPieces xmS xpS)
open QuantumNLS.Prop025OKer (mixK mixD)
open QuantumNLS.R52CFKernels (kerA physK)
open QuantumNLS.R52CFCoh (lam lam_hasFDerivAt)
open QuantumNLS.Prop010RectangleDifferentialR17 (Boundary boundaryIntegral boundaryIntegral_eq)
open QuantumNLS.RootCauchyFullBracketR8 (G)
open QuantumNLS.RootCauchyJointR9 (Regular)
open QuantumNLS.RootMassInvolutionR8 (mass)
open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.PROP017UniformN (cutSeq)
open QuantumNLS.Prop025OGrad

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. The gradient agreement with the cut threshold chosen before the joint times -/

/-- `Prop025OGrad.window_fderiv` with `∃ l0, ∀ l ≥ l0, ∀ t` (verbatim proof; the threshold never depended on `t`). -/
theorem window_fderiv_u (hκ : 0 < κ) {s B h : ℝ} (hs : 0 < s) (hh : 0 < h) (R : Finset ℕ) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ t : ℕ → ℝ, 1 ≤ cutSeq L l ∧ ∀ u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B,
      (∀ z ∈ Gam (-(cutSeq L l)) (cutSeq L l) h, Regular κ (u, z)) ∧
      DifferentiableAt ℝ (Prop025OInputs.windowFamily (L := L) κ R t (cutSeq L l)) u ∧
      ∀ k : L2T L, fderiv ℝ (Prop025OInputs.windowFamily (L := L) κ R t (cutSeq L l)) u k =
        -(2 * Real.pi * κ)⁻¹ * (rectIntegral (fun z => polyT R t z *
          (fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Df L κ (fun w => G hκ w u) z))
          (-(cutSeq L l)) (cutSeq L l) h).re := by
  obtain ⟨l1, hpath⟩ := window_path (L := L) hκ (B := B) hs hh
  have hq := fun r : ℕ => Q07BUniformCutsR16.q07Buniformcuts (L := L) hκ hs B hh r
  choose hstrip η hη lr C hC hd using hq
  refine ⟨max l1 (R.sup lr), fun l hl t => ?_⟩
  have hl1 := (le_max_left _ _).trans hl
  have hlr : ∀ r ∈ R, lr r ≤ l := fun r hr => (Finset.le_sup hr).trans ((le_max_right _ _).trans hl)
  set a := cutSeq L l with ha
  obtain ⟨ha1, hp⟩ := hpath l hl1
  refine ⟨ha1, fun u hu => ?_⟩
  obtain ⟨hregu, H, hH, hHe⟩ := hp u hu
  have hab : -a ≤ a := by linarith
  set T := boundaryIntegral hab hh.le with hT
  let cr : ℕ → C(Boundary (-a) a h, ℂ) := fun r =>
    ⟨fun z => z.1 ^ r * (I * (κ : ℂ)), (continuous_subtype_val.pow r).mul continuous_const⟩
  let c : C(Boundary (-a) a h, ℂ) := ∑ r ∈ R, t r • cr r
  have hc : ∀ z : Boundary (-a) a h, c z = polyT R t z.1 * (I * (κ : ℂ)) := by
    intro z
    simp only [c, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul, Pi.smul_apply, cr,
      ContinuousMap.coe_mk, polyT, Finset.sum_mul, Complex.real_smul]
    refine Finset.sum_congr rfl fun r _ => by ring
  let Λ : C(Boundary (-a) a h, ℂ) →L[ℝ] ℝ :=
    Complex.reCLM.comp (T.comp (ContinuousLinearMap.mul ℝ C(Boundary (-a) a h, ℂ) c))
  -- the window Hamiltonian is the contour functional near `u`
  have hnear : ∀ᶠ v : L2T L in 𝓝 u, ∀ r ∈ R, ‖v - u‖ < η r := by
    have hR : ∀ r ∈ R, ∀ᶠ v : L2T L in 𝓝 u, ‖v - u‖ < η r := fun r _ => by
      filter_upwards [ball_mem_nhds u (hη r)] with v hv
      rw [← dist_eq_norm]; exact hv
    exact (Finset.eventually_all R).mpr hR
  have heq : Prop025OInputs.windowFamily (L := L) κ R t a =ᶠ[𝓝 u]
      fun v => -(1 / (2 * Real.pi * κ)) * Λ (H v) := by
    filter_upwards [hnear, hHe] with v hv hHv
    have hr : ∀ r ∈ R, Prop025OInputs.windowHam (L := L) κ r a v =
        -(1 / (2 * Real.pi * κ)) * (T (cr r * H v)).re := by
      intro r hrR
      obtain ⟨-, hall⟩ := hd r l (hlr r hrR)
      have hw := ((hall u hu v (hv r hrR)).2.1).symm
      unfold Prop025OInputs.windowHam
      rw [hw]
      unfold Q07IntegratedHessiansR16.windowContour ContourPrefactor.contourFunctional
      rw [rectContour_eq, ← boundaryIntegral_eq hab hh.le (cr r * H v)]
      intro z
      simp only [ContinuousMap.mul_apply, cr, ContinuousMap.coe_mk, hHv z, Q07LogDifferentialsR16.logarithm]
      ring
    unfold Prop025OInputs.windowFamily
    rw [Finset.sum_congr rfl fun r hrR => by rw [hr r hrR]]
    simp only [Λ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', Complex.reCLM_apply]
    have hsum : c * H v = ∑ r ∈ R, t r • (cr r * H v) := by
      simp only [c, Finset.sum_mul, smul_mul_assoc]
    rw [hsum, map_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, Complex.smul_re, smul_eq_mul]
    ring
  have hF := (Λ.hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt).const_mul (-(1 / (2 * Real.pi * κ)))
  have hW := hF.congr_of_eventuallyEq heq
  refine ⟨hregu, hW.differentiableAt, fun k => ?_⟩
  rw [hW.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, Λ,
    Complex.reCLM_apply, ContinuousLinearMap.mul_apply']
  have hDH : ∀ z : Boundary (-a) a h, (fderiv ℝ H u k) z = fderiv ℝ (G hκ z.1) u k := by
    intro z
    have hd := (ContinuousMap.evalCLM ℝ z).hasFDerivAt.comp u hH.differentiableAt.hasFDerivAt
    have hev : (fun w => H w z) =ᶠ[𝓝 u] G hκ z.1 := hHe.mono fun w hw => hw z
    have hhd := (hd.congr_of_eventuallyEq hev.symm).fderiv
    simpa using (congrArg (fun A : L2T L →L[ℝ] ℂ => A k) hhd).symm
  rw [boundaryIntegral_eq hab hh.le (c * fderiv ℝ H u k)
    (fun z => polyT R t z * ((I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k)) (fun z => by
      rw [ContinuousMap.mul_apply, hc z, hDH z]; ring)]
  have hcongr : rectIntegral (fun z => polyT R t z * ((I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k)) (-a) a h =
      rectIntegral (fun z => polyT R t z *
        (fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k / Df L κ (fun w => G hκ w u) z))
        (-a) a h := by
    have hp : ∀ z ∈ Gam (-a) a h, polyT R t z * ((I * (κ : ℂ)) * fderiv ℝ (G hκ z) u k) =
        polyT R t z * (fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k /
          Df L κ (fun w => G hκ w u) z) := by
      intro z hz
      rw [dsD_eq hκ u k (hregu z hz)]
    apply LabelExactPeriod.rectIntegral_congr
    · exact fun x hx => hp _ (PeriodTwoTerm.bot_mem hab hx)
    · exact fun x hx => hp _ (PeriodTwoTerm.top_mem hab hx)
    · exact fun y hy => hp _ (PeriodTwoTerm.right_mem hh.le hy)
    · exact fun y hy => hp _ (PeriodTwoTerm.left_mem hh.le hy)
  rw [hcongr]
  have : (1 / (2 * Real.pi * κ)) = (2 * Real.pi * κ)⁻¹ := one_div _
  rw [this]

/-- `Prop025OGrad.grad_at` with `∃ l0, ∀ l ≥ l0, ∀ t` (verbatim proof). -/
theorem grad_at_u (hκ : 0 < κ) (u : L2T L) {s B h : ℝ} (hs : 0 < s) (hh : 0 < h)
    (hu : u ∈ Q07SobolevCutsR16.sobolevClass (L := L) s B) (μ : Measure ℝ)
    (hμ : PhysicalQuantumMeasure.measure hκ u = μ) (ords : Finset ℕ) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ t : ℕ → ℝ, 1 ≤ cutSeq L l ∧
      DifferentiableAt ℝ (Prop025OInputs.windowFamily (L := L) κ ords t (cutSeq L l)) u ∧
      ∀ {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ),
        fderiv ℝ (R52CFHartree.coh (mixK (L := L) hκ u μ h (cutSeq L l) ords t n θf)) u =
          fderiv ℝ (Prop025OInputs.windowFamily (L := L) κ ords t (cutSeq L l)) u +
            ∑ i, θf i • fderiv ℝ (mass hκ (n i)) u := by
  obtain ⟨l0, hw⟩ := window_fderiv_u (L := L) hκ (B := B) hs hh ords
  refine ⟨l0, fun l hl t => ?_⟩
  obtain ⟨ha1, hwu⟩ := hw l hl t
  obtain ⟨hregw, hWd, hWf⟩ := hwu u hu
  refine ⟨ha1, hWd, fun {nI} n θf => ?_⟩
  set a := cutSeq L l with ha
  have ha0 : 0 < a := by linarith
  have hGD : Df L κ (Gfull μ) = Df L κ (fun w => G hκ w u) := by
    funext z
    have : Gfull μ = fun w => G hκ w u := by
      funext w
      rw [RootSpectralInputsDischarge.Gfull_eq, ← hμ]
      rfl
    rw [this]
  -- regularity on the fixed rectangles (accepted R52CF stage 1)
  have hfix : ∀ i, (∀ z ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h, Regular κ (u, z)) ∧
      ∀ k : L2T L, fderiv ℝ (mass hκ (n i)) u k = -(2 * Real.pi * κ)⁻¹ *
        (rectIntegral (fun z => fderiv ℝ (fun w : L2T L => RootScalarPeriodR10.symbol κ w z) u k /
          Df L κ (fun w => G hκ w u) z) (xmS hκ u n i) (xpS hκ u n i) h).re := by
    intro i
    obtain ⟨W, -, huW, hW⟩ := R52CFDeriv.fixed_rectangle_neighborhood hκ u (n i) hh
    obtain ⟨hr, -, hd⟩ := hW u huW
    exact ⟨hr, hd⟩
  have hlt : ∀ i, xmS hκ u n i < xpS hκ u n i := fun i => R52CFDeriv.cut_lt hκ u (n i)
  have hDw : ∀ z ∈ Gam (-a) a h, ContinuousAt (fun z => (Df L κ (Gfull μ) z)⁻¹) z := by
    intro z hz; rw [hGD]; exact (D_regular hκ u (hregw z hz)).1
  have hDf : ∀ i, ∀ z ∈ Gam (xmS hκ u n i) (xpS hκ u n i) h,
      ContinuousAt (fun z => (Df L κ (Gfull μ) z)⁻¹) z := by
    intro i z hz; rw [hGD]; exact (D_regular hκ u ((hfix i).1 z hz)).1
  have hfun : R52CFHartree.coh (mixK (L := L) hκ u μ h a ords t n θf) = fun v =>
      lam (L := L) κ (fun z => Df L κ (Gfull μ) z / polyT ords t z) (-a) a h v +
        ∑ i, θf i * lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h v :=
    funext fun v => coh_mix_eq hκ u μ hh ha0 ords t n θf hlt hDw hDf v
  -- differentials of the two kinds of frozen functionals
  have hcw : ContinuousOn (fun z => (Df L κ (Gfull μ) z / polyT ords t z)⁻¹) (Gam (-a) a h) := by
    intro z hz
    have h1 : ContinuousWithinAt (fun z => polyT ords t z * (Df L κ (Gfull μ) z)⁻¹) (Gam (-a) a h) z :=
      ((continuous_polyT ords t).continuousAt.mul (hDw z hz)).continuousWithinAt
    exact h1.congr (fun y _ => by rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm])
      (by rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm])
  have hLw := lam_hasFDerivAt (L := L) κ hκ.le (fun z => Df L κ (Gfull μ) z / polyT ords t z)
    (by linarith : -a ≤ a) hh.le hcw u
  have hLf : ∀ i, HasFDerivAt (lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h)
      (fderiv ℝ (lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h) u) u ∧
      ∀ k : L2T L, fderiv ℝ (lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h) u k =
        -(2 * Real.pi * κ)⁻¹ * (rectIntegral (fun z => fderiv ℝ (fun w : L2T L =>
          RootScalarPeriodR10.symbol κ w z) u k / Df L κ (Gfull μ) z) (xmS hκ u n i) (xpS hκ u n i) h).re :=
    fun i => lam_hasFDerivAt (L := L) κ hκ.le (Df L κ (Gfull μ)) (hlt i).le hh.le
      (fun z hz => (hDf i z hz).continuousWithinAt) u
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hLf i).1.const_mul (θf i))
  have htot : HasFDerivAt (fun v =>
      lam (L := L) κ (fun z => Df L κ (Gfull μ) z / polyT ords t z) (-a) a h v +
        ∑ i, θf i * lam (L := L) κ (Df L κ (Gfull μ)) (xmS hκ u n i) (xpS hκ u n i) h v) _ u :=
    hLw.1.add hsum
  rw [hfun, htot.fderiv]
  ext k
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  rw [hLw.2 k, hWf k]
  congr 1
  · congr 2
    apply LabelExactPeriod.rectIntegral_congr <;> intros <;> rw [hGD, div_div_eq_mul_div] <;> ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [(hLf i).2 k, (hfix i).2 k, hGD]

/-! ### 2. The rotated smooth class -/

open QuantumNLS.Def033HierarchyR24m (Smooth physical jointSmooth)
open QuantumNLS.ActualModelTargetR53a (HigherFlows hamFlows flowMap flow_isHam angle rotate rotateSmooth
  rotateSmooth_physical target rotate_eq_action)
open QuantumNLS.RF535Final (Tact Tθ Hθ GlobalStatement)
open QuantumNLS.ProductTorusGenerator (Linf)
open QuantumNLS.SymplecticBracket (hamField)
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

/-- The finitely supported angle vector `θ_I` (zero off `I`). -/
def angleL (I : Finset ℤ) (θ : ℤ → ℝ) : Linf :=
  ⟨fun n => if n ∈ I then θ n else 0, memℓp_infty ⟨∑ m ∈ I, |θ m|, by
    rintro x ⟨n, rfl⟩
    show ‖(if n ∈ I then θ n else 0)‖ ≤ ∑ m ∈ I, |θ m|
    split_ifs with hn
    · rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun m => |θ m|) (fun _ _ => abs_nonneg _) hn
    · rw [norm_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _⟩⟩

theorem angleL_apply (I : Finset ℤ) (θ : ℤ → ℝ) (n : ℤ) : angleL I θ n = if n ∈ I then θ n else 0 := rfl

theorem angleL_supp (I : Finset ℤ) (θ : ℤ → ℝ) : ∀ m ∉ I, angleL I θ m = 0 := fun m hm => by
  rw [angleL_apply, if_neg hm]

/-- **`T_{θ_I} = Φ_I(θ)`**: the time-one action flow of `Σ_{n∈I} θ_n I_n` is the R53a angle rotation, for every
DEF-021 chart (the accepted `rotate_eq_action` and the action flows of the accepted global chart statement). -/
theorem Tθ_angleL (hκ : 0 < κ) {d : ℝ} {Φl : L2T L → QuantumNLS.D01LocalPrimitive.K}
    {Ψl : QuantumNLS.D01LocalPrimitive.K → L2T L} (hG : GlobalStatement L κ hκ d Φl Ψl)
    (C : Def021ChartR41b.Chart L κ hκ) (I : Finset ℤ) (θ : ℤ → ℝ) (v : L2T L) :
    Tθ (L := L) hκ (angleL I θ) v = rotate C I θ v := by
  rw [rotate_eq_action, ← hG.1.2.1]
  congr 1
  funext n
  rw [Pi.inv_apply, angleL_apply]
  unfold angle
  split_ifs with hn
  · rw [Circle.exp_neg, inv_inv]
  · rw [Circle.exp_zero, inv_one]

/-- A smooth profile is determined by its `L²` class. -/
theorem physical_injective : Function.Injective (physical (L := L)) := by
  intro u v h
  have hu := PhysicalProductPreparation.smoothClass_ae u.property
  have hv := PhysicalProductPreparation.smoothClass_ae v.property
  change PhysicalProductPreparation.smoothClass u.property =
    PhysicalProductPreparation.smoothClass v.property at h
  rw [h] at hu
  let F1 := WeakDerivatives.liftC u.property.smooth.continuous u.property.periodic
  let G1 := WeakDerivatives.liftC v.property.smooth.continuous v.property.periodic
  have he : (F1 : AddCircle L → ℂ) = (G1 : AddCircle L → ℂ) :=
    MeasureTheory.Measure.eq_of_ae_eq (hu.symm.trans hv) F1.continuous G1.continuous
  apply Subtype.ext
  funext x
  simpa only [F1, G1, WeakDerivatives.liftC_coe] using congrFun he (x : AddCircle L)

/-- `Φ_I(θ)u` depends only on the angles of the labels in `I`. -/
theorem rotateSmooth_congr {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (I : Finset ℤ)
    {θ θ' : ℤ → ℝ} (h : ∀ n ∈ I, θ n = θ' n) (u : Smooth L) :
    rotateSmooth C I θ u = rotateSmooth C I θ' u := by
  apply physical_injective
  rw [rotateSmooth_physical, rotateSmooth_physical]
  have ha : angle I θ = angle I θ' := by
    funext n
    unfold angle
    split_ifs with hn
    · rw [h n hn]
    · rfl
  unfold rotate
  rw [ha]

/-- The `h^s` vector supported at the single site `m`. -/
def site (s : ℝ) (m : ℤ) (c : ℂ) : Sobolev.h02 L s :=
  Sobolev.h02.ofMem (L := L) (x := Pi.single m c) (by
    unfold Fourier.MemHs
    apply summable_of_ne_finset_zero (s := {m})
    intro n hn
    rw [Finset.mem_singleton] at hn
    simp [Pi.single_apply, hn])

/-- `x ↦ x.val` is additive on `h^s`. -/
def valHom (s : ℝ) : Sobolev.h02 L s →+ (ℤ → ℂ) :=
  AddMonoidHom.mk' (fun x => x.val) (fun _ _ => rfl)

theorem val_sum (s : ℝ) (f : ℤ → Sobolev.h02 L s) (I : Finset ℤ) :
    (∑ m ∈ I, f m).val = ∑ m ∈ I, (f m).val :=
  map_sum (valHom (L := L) s) f I

/-- **Continuity of the angle rotation in the smooth topology** (DEF-044 clause (2): the chart and its inverse restrict
to homeomorphisms of every Sobolev scale; only the finitely many coordinates in `I` move). -/
theorem continuous_rotateSmooth (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (hsob : Def044ChartR51a.SobolevRestrictions hκ C) (I : Finset ℤ) (u : Smooth L) :
    Continuous fun θ : ℤ → ℝ => rotateSmooth C I θ u := by
  have hcomp : (fun θ : ℤ → ℝ => rotateSmooth C I θ u) = RB7BindTopology.toSmooth ∘
      fun θ => (⟨(rotateSmooth C I θ u).val, (rotateSmooth C I θ u).property⟩ : RB7.SmoothProf L) := rfl
  rw [hcomp]
  refine RB7BindTopology.continuous_toSmooth.comp (continuous_induced_rng.2 (continuous_pi fun k => ?_))
  show Continuous fun θ : ℤ → ℝ => RB7.jetOf (L := L) (rotateSmooth C I θ u).val k
  obtain ⟨E, hE, hEs⟩ := hsob (k : ℝ) (Nat.cast_nonneg k)
  set z0 := C.Φ (physical u) with hz0
  set uq : Sobolev.H02 L (k : ℝ) := Sobolev.WField.mk (physical u) (RB7.memHs_of_smooth u.property (k : ℝ))
    with huq
  have hEu : ∀ n, (E uq).val n = z0 n := fun n =>
    (Reg015Setting.toBase_apply (k : ℝ) (Nat.cast_nonneg k) (E uq) n).symm.trans
      (congrArg (fun a : REF88Chart.K => a n) (hE uq))
  set c : (ℤ → ℝ) → ℤ → ℂ := fun θ m => ((Circle.exp (-θ m) : Circle) : ℂ) - 1 with hc
  set zq : (ℤ → ℝ) → Sobolev.h02 L (k : ℝ) := fun θ =>
    E uq + ∑ m ∈ I, c θ m • site (L := L) (k : ℝ) m (z0 m) with hzq
  have hzq_val : ∀ θ n, (zq θ).val n = ActionTorus.rotate (angle I θ) z0 n := by
    intro θ n
    have h1 : (zq θ).val = (E uq).val + ∑ m ∈ I, c θ m • (site (L := L) (k : ℝ) m (z0 m)).val := by
      rw [hzq]
      dsimp only
      rw [Sobolev.PosWeight.WSeq.val_add, val_sum]
      rfl
    rw [h1, Pi.add_apply, Finset.sum_apply, hEu, ActionTorus.rotate_apply]
    have h2 : ∀ m, (c θ m • (site (L := L) (k : ℝ) m (z0 m)).val) n = if n = m then c θ m * z0 m else 0 := by
      intro m
      show c θ m * (Pi.single m (z0 m) : ℤ → ℂ) n = _
      rw [Pi.single_apply]
      split_ifs with h
      · subst h; rfl
      · ring
    rw [Finset.sum_congr rfl fun m _ => h2 m, Finset.sum_ite_eq]
    unfold angle
    by_cases hn : n ∈ I
    · rw [if_pos hn, if_pos hn, hc]; ring
    · rw [if_neg hn, if_neg hn]; simp
  have hjet : ∀ θ, RB7.jetOf (L := L) (rotateSmooth C I θ u).val k = E.symm (zq θ) := by
    intro θ
    rw [RB7BindTopology.jetOf_eq (rotateSmooth C I θ u).property k]
    apply Sobolev.WField.ext
    rw [hEs]
    have hb : Reg015Setting.toBase (k : ℝ) (Nat.cast_nonneg k) (zq θ) = ActionTorus.rotate (angle I θ) z0 := by
      apply lp.ext
      funext n
      rw [Reg015Setting.toBase_apply, hzq_val]
    rw [hb]
    show physical (rotateSmooth C I θ u) = _
    rw [rotateSmooth_physical]
    rfl
  have hcont : Continuous zq := by
    refine continuous_const.add (continuous_finset_sum I fun m _ => ?_)
    have h3 : Continuous fun θ : ℤ → ℝ => c θ m := by
      have e : (fun θ : ℤ → ℝ => c θ m) =
          fun θ => Complex.exp (((-θ m : ℝ) : ℂ) * Complex.I) - 1 :=
        funext fun θ => by rw [hc]; dsimp only; rw [Circle.coe_exp]
      rw [e]
      fun_prop
    exact h3.smul (continuous_const (y := site (L := L) (k : ℝ) m (z0 m)))
  exact (E.symm.continuous.comp hcont).congr fun θ => (hjet θ).symm

/-- The angle box, as a compact subset of `ℤ → ℝ` (coordinates off `I` pinned to `0`). -/
def angleBox (I : Finset ℤ) (Θ : ℤ → ℝ) : Set (ℤ → ℝ) :=
  Set.pi univ fun n => if n ∈ I then Icc (-Θ n) (Θ n) else ({0} : Set ℝ)

/-- **The rotated class `{Φ_I(θ)u : |θ_n| ≤ Θ_n}` is compact in the smooth topology.** -/
theorem isCompact_rotClass (hκ : 0 < κ) (C : Def021ChartR41b.Chart L κ hκ)
    (hsob : Def044ChartR51a.SobolevRestrictions hκ C) (I : Finset ℤ) (Θ : ℤ → ℝ) (u : Smooth L) :
    IsCompact ((fun θ : ℤ → ℝ => rotateSmooth C I θ u) '' angleBox I Θ) :=
  (isCompact_univ_pi fun n => by
    by_cases hn : n ∈ I
    · rw [if_pos hn]; exact isCompact_Icc
    · rw [if_neg hn]; exact isCompact_singleton).image (continuous_rotateSmooth hκ C hsob I u)

theorem mem_rotClass {hκ : 0 < κ} (C : Def021ChartR41b.Chart L κ hκ) (I : Finset ℤ) (Θ : ℤ → ℝ)
    (u : Smooth L) (θ : ℤ → ℝ) (hθ : ∀ n ∈ I, |θ n| ≤ Θ n) :
    rotateSmooth C I θ u ∈ (fun θ : ℤ → ℝ => rotateSmooth C I θ u) '' angleBox I Θ := by
  refine ⟨fun n => if n ∈ I then θ n else 0, fun n _ => ?_,
    rotateSmooth_congr C I (fun n hn => by simp only [if_pos hn]) u⟩
  by_cases hn : n ∈ I
  · show (if n ∈ I then θ n else 0) ∈ (if n ∈ I then Icc (-Θ n) (Θ n) else ({0} : Set ℝ))
    rw [if_pos hn, if_pos hn]
    exact abs_le.mp (hθ n hn)
  · show (if n ∈ I then θ n else 0) ∈ (if n ∈ I then Icc (-Θ n) (Θ n) else ({0} : Set ℝ))
    rw [if_neg hn, if_neg hn]
    rfl

/-! ### 3. The classical target -/

/-- The enumeration `n : Fin |I| → ℤ` of a finite label set. -/
def enum (I : Finset ℤ) : Fin I.card → ℤ := fun i => (I.equivFin.symm i : ℤ)

theorem sum_enum {M : Type*} [AddCommMonoid M] (I : Finset ℤ) (f : ℤ → M) :
    ∑ i, f (enum I i) = ∑ m ∈ I, f m := by
  rw [← Finset.sum_coe_sort I f]
  exact Equiv.sum_comp I.equivFin.symm (fun m : I => f m)

/-- **The classical-target identification (eq:MP-classical-window-error).**  For the named window input, a DEF-021
chart with its Sobolev restrictions (DEF-044 clause (2)), the higher-order hierarchy flows `F`, a smooth profile `u`
whose scalar measure is `μ`, charge orders `2 ≤ r ≤ d`, a time box and an angle box: there are `C_w` and a cut index
`ℓ₀` such that for every `ℓ ≥ ℓ₀`, all times and angles in the boxes, and every solution `γ` of the frozen affine
equation `γ' = X_F(γ)`, `γ(0) = u`, of the frozen coherent energy `F = coh(mixK)` at the cut `a = a_ℓ` (torus
invariant, differentiable): `‖γ(1) − Φ_t(Φ_I(θ)u)‖ ≤ C_w a^{−1/4}`. -/
theorem classical_target (hκ : 0 < κ) (HW : Prop025OInputs.WindowInput (L := L) hκ)
    (C : Def021ChartR41b.Chart L κ hκ) (hsob : Def044ChartR51a.SobolevRestrictions hκ C)
    (F : HigherFlows L κ) (u : Smooth L) (μ : Measure ℝ)
    (hμ : PhysicalQuantumMeasure.measure hκ (physical u) = μ) {h : ℝ} (hh : 0 < h)
    (d : ℕ) (hd : 2 ≤ d) (R : Finset ℕ) (hR : ∀ r ∈ R, 2 ≤ r ∧ r ≤ d) (T : ℕ → ℝ) (hT : ∀ r, 0 ≤ T r)
    (I : Finset ℤ) (Θ : ℤ → ℝ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ t : ℕ → ℝ, (∀ r ∈ R, |t r| ≤ T r) →
      ∀ θ : ℤ → ℝ, (∀ n ∈ I, |θ n| ≤ Θ n) →
      (∀ (ψ : Torus) (v : L2T L), R52CFHartree.coh (mixK (L := L) hκ (physical u) μ h (cutSeq L l) R t (enum I)
          (fun i => θ (enum I i))) (Tact (L := L) hκ ψ v) =
        R52CFHartree.coh (mixK (L := L) hκ (physical u) μ h (cutSeq L l) R t (enum I)
          (fun i => θ (enum I i))) v) →
      Differentiable ℝ (R52CFHartree.coh (mixK (L := L) hκ (physical u) μ h (cutSeq L l) R t (enum I)
          (fun i => θ (enum I i)))) →
      ∀ γ : ℝ → L2T L, γ 0 = physical u →
      (∀ τ, HasDerivAt γ (hamField (R52CFHartree.coh (mixK (L := L) hκ (physical u) μ h (cutSeq L l) R t
          (enum I) (fun i => θ (enum I i)))) (γ τ)) τ) →
      ‖γ 1 - target C F I R θ t u‖ ≤ Cw * (cutSeq L l) ^ (-(1/4 : ℝ)) := by
  obtain ⟨⟨dl, CL, hdl, hCL, Φloc, Ψloc, hloc⟩, hglob⟩ := RF535Final.global_actual_chart L
  have hG := hglob dl CL Φloc Ψloc hdl hCL hloc κ hκ
  -- the Sobolev class of the profile (smooth, so in `H¹`)
  set v1 : Sobolev.H02 L 1 := Sobolev.WField.mk (physical u) (RB7.memHs_of_smooth u.property 1) with hv1
  have hu1 : physical u ∈ Q07SobolevCutsR16.sobolevClass (L := L) 1 ‖v1‖ := ⟨v1, le_rfl, rfl⟩
  obtain ⟨l1, hgr⟩ := grad_at_u hκ (physical u) one_pos hh hu1 μ hμ R
  -- the compact rotated class and the named window input at the DEF-044 chart
  have hK := isCompact_rotClass hκ C hsob I Θ u
  obtain ⟨Cw, hCw, l2, hwin⟩ := Prop025OInputs.window_spec hκ HW C.Φ (Def044ChartR28m.printed_chart hκ C)
    ((Def044ChartR28m.sobolev_iff hκ C).mp hsob) (flowMap F) (fun r _ => flow_isHam F r) d hd R hR T hT _ hK
  refine ⟨Cw, hCw, max l1 l2, fun l hl t ht θ hθ hFinv hFd γ hγ0 hγ => ?_⟩
  have hl1 : l1 ≤ l := (le_max_left _ _).trans hl
  have hl2 : l2 ≤ l := (le_max_right _ _).trans hl
  obtain ⟨-, hWd, hgrad⟩ := hgr l hl1 t
  have hWinv : ∀ (ψ : Torus) (v : L2T L),
      Prop025OInputs.windowFamily (L := L) κ R t (cutSeq L l) (Tact (L := L) hκ ψ v) =
        Prop025OInputs.windowFamily (L := L) κ R t (cutSeq L l) v :=
    fun ψ v => Prop025OTorus.windowFamily_Tact hκ hG ψ R t (cutSeq L l) v
  have hgr' := fun ψ => Prop025OTorus.grad_transport hκ hG hFinv hWinv hFd (physical u) hWd (enum I)
    (fun i => θ (enum I i)) (hgrad (enum I) (fun i => θ (enum I i))) ψ
  have hA : ∀ v, ∑ i, θ (enum I i) * mass hκ (enum I i) v = Hθ (L := L) hκ (angleL I θ) v := by
    intro v
    have e := congrFun (R52CFOrbit.Hθ_eq_sum (L := L) hκ I (angleL I θ) (angleL_supp I θ)) v
    rw [e]
    exact (sum_enum I (fun m => θ m * mass hκ m v)).trans (Finset.sum_congr rfl fun m hm => by
      show θ m * mass hκ m v = angleL I θ m * mass hκ m v
      rw [angleL_apply, if_pos hm])
  obtain ⟨y, hy, hy1⟩ := Prop025OTraj.window_traj hκ hG (physical u) R t (cutSeq L l) hFinv hFd (enum I)
    (fun i => θ (enum I i)) I (angleL I θ) (angleL_supp I θ) hA hgr' γ hγ0 hγ
  rw [Tθ_angleL hκ hG C, ← rotateSmooth_physical] at hy
  have hres := hwin l hl2 _ (mem_rotClass C I Θ u θ hθ) t ht y hy
  rw [← hy1]
  exact hres

end QuantumNLS.Prop025OTarget

#print axioms QuantumNLS.Prop025OTarget.window_fderiv_u
#print axioms QuantumNLS.Prop025OTarget.grad_at_u
#print axioms QuantumNLS.Prop025OTarget.Tθ_angleL
#print axioms QuantumNLS.Prop025OTarget.continuous_rotateSmooth
#print axioms QuantumNLS.Prop025OTarget.isCompact_rotClass
#print axioms QuantumNLS.Prop025OTarget.classical_target

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OTarget." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OTarget aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
