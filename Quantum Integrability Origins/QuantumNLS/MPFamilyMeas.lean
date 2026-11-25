import Mathlib
import QuantumNLS.MPFamily

/-!
# PROP-026: joint continuity and measurability of the actual family (`hFm`, `hdF`)

New module (continuation of `MPFamily`).  For the actual contour parameter space and background family:

* `continuousAt_gθ`: `(θ, w) ↦ g_θ(w)` is continuous at every good `θ` and every `w` (open cover `‖w - s_θ‖ < ρ` / `> r`);
* `continuousAt_Fθ`: `(θ, x) ↦ F_θ(x)` is continuous at good `θ`;
* **`aesm_resKd`** (`hFm`): `θ ↦ F_θ|_{K} ∈ C(K,ℂ)` is a.e. strongly measurable (continuous on the open good set, constant elsewhere);
* `hasDerivAt_gθ`: `g_θ'(s_θ) = dθ θ` (`= D(z_θ)⁻¹` at good `θ`);
* **`aesm_fderiv`** (`hdF`): the directional derivatives `∂_jF_θ(b_θ)` are strongly measurable in `θ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ContDiff

namespace QuantumNLS.MPFamilyMeas

open QuantumNLS.MPContour QuantumNLS.MPChartBounds QuantumNLS.MPChartSmooth QuantumNLS.MPChartDeriv
  QuantumNLS.MPFamily
open QuantumNLS.MixedQuadratures (quadF isoR2 Kdisc fderiv_quadF continuous_quadF)
open QuantumNLS.FunctionalLinearization (resKd resKd_apply)
open QuantumNLS.MixedTraceNorm (chartLambda chartA chartD hasDerivAt_chartLambda)

variable {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (κ : ℝ) (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁)
  (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z)

include hZ in
theorem continuousAt_comp_good (f : ℂ → ℂ) (hf : ContinuousOn f (Z ∩ {z | z.im ≠ 0})) {θ₀ : ThetaSpace m}
    (h0 : good P θ₀) : ContinuousAt (fun θ => f (zθ P θ)) θ₀ := by
  have : ContinuousOn (fun θ => f (zθ P θ)) {θ | good P θ} :=
    hf.comp (continuous_zθ P).continuousOn (fun θ hθ => ⟨hZ θ.1 θ.2 θ.2.2, hθ⟩)
  exact this.continuousAt ((isOpen_good P).mem_nhds h0)

include hZ in
theorem continuousAt_gθ {θ₀ : ThetaSpace m} (h0 : good P θ₀) (w₀ : ℂ) :
    ContinuousAt (fun p : ThetaSpace m × ℂ => gθ P B p.1 p.2) (θ₀, w₀) := by
  have hbg := B.bg _ (hZ θ₀.1 θ₀.2 θ₀.2.2) h0
  have hr : 0 < rad d₀ s₁ a₀ := rad_pos hbg
  have hρ := rho_pos hbg.hd0 hbg.hs0 hbg.ha0
  have h3 : rad d₀ s₁ a₀ < rho d₀ s₁ a₀ := by unfold rad; linarith
  have cC : ContinuousAt (fun p : ThetaSpace m × ℂ => B.c0 (zθ P p.1)) (θ₀, w₀) :=
    ContinuousAt.comp (g := fun θ => B.c0 (zθ P θ)) (f := Prod.fst) (x := (θ₀, w₀))
      (continuousAt_comp_good P hZ B.c0 B.hc0 h0) continuousAt_fst
  have cD : ContinuousAt (fun p : ThetaSpace m × ℂ => B.D (zθ P p.1)) (θ₀, w₀) :=
    ContinuousAt.comp (g := fun θ => B.D (zθ P θ)) (f := Prod.fst) (x := (θ₀, w₀))
      (continuousAt_comp_good P hZ B.D B.hD h0) continuousAt_fst
  have cS : ContinuousAt (fun p : ThetaSpace m × ℂ => B.s (zθ P p.1)) (θ₀, w₀) :=
    ContinuousAt.comp (g := fun θ => B.s (zθ P θ)) (f := Prod.fst) (x := (θ₀, w₀))
      (continuousAt_comp_good P hZ B.s B.hs h0) continuousAt_fst
  have cA : ContinuousAt (fun p : ThetaSpace m × ℂ => B.A (zθ P p.1)) (θ₀, w₀) :=
    ContinuousAt.comp (g := fun θ => B.A (zθ P θ)) (f := Prod.fst) (x := (θ₀, w₀))
      (continuousAt_comp_good P hZ B.A B.hA h0) continuousAt_fst
  have hgood : ∀ᶠ p : ThetaSpace m × ℂ in 𝓝 (θ₀, w₀), good P p.1 := by
    have : (Prod.fst ⁻¹' {θ | good P θ} : Set (ThetaSpace m × ℂ)) ∈ 𝓝 (θ₀, w₀) :=
      continuousAt_fst.preimage_mem_nhds ((isOpen_good P).mem_nhds (show θ₀ ∈ {θ | good P θ} from h0))
    exact this
  by_cases hw : ‖w₀ - B.s (zθ P θ₀)‖ < rho d₀ s₁ a₀
  · have hDne : B.D (zθ P θ₀) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hbg.hd0 hbg.hD)
    have hAne : B.A (zθ P θ₀) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hbg.ha0 hbg.hA)
    have hq : ContinuousAt (fun p : ThetaSpace m × ℂ =>
        1 + (p.2 ^ 2 - (B.s (zθ P p.1)) ^ 2) / (B.D (zθ P p.1)) ^ 2) (θ₀, w₀) :=
      continuousAt_const.add (((continuousAt_snd.pow 2).sub (cS.pow 2)).div (cD.pow 2) (pow_ne_zero 2 hDne))
    have hslit : (1 + (w₀ ^ 2 - (B.s (zθ P θ₀)) ^ 2) / (B.D (zθ P θ₀)) ^ 2) ∈ Complex.slitPlane :=
      one_add_mem_slit (q_le hbg.hd0 hbg.hs0 hbg.hD hbg.hs hw)
    have hcp := hq.cpow (continuousAt_const (y := (1 / 2 : ℂ))) hslit
    have ha' := (continuousAt_snd.add (cD.mul hcp)).div_const 2
    have hslit2 : ((w₀ + B.D (zθ P θ₀) * (1 + (w₀ ^ 2 - (B.s (zθ P θ₀)) ^ 2) / (B.D (zθ P θ₀)) ^ 2) ^ (1 / 2 : ℂ)) / 2) /
        B.A (zθ P θ₀) ∈ Complex.slitPlane := by
      have := chartA_div_mem_slit hbg.hd0 hbg.hs0 hbg.ha0 hbg.hD hbg.hs hbg.hA hbg.hAd hw
      exact this
    have hl := (ha'.div cA hAne).clog hslit2
    have hcut : ContinuousAt (fun p : ThetaSpace m × ℂ =>
        ((cutoff (rad d₀ s₁ a₀) (p.2 - B.s (zθ P p.1)) : ℝ) : ℂ)) (θ₀, w₀) :=
      Complex.continuous_ofReal.continuousAt.comp
        ((contDiff_cutoff _).continuous.continuousAt.comp (continuousAt_snd.sub cS))
    have hF := hcut.mul (cC.add hl)
    refine hF.congr ?_
    filter_upwards [hgood] with p hp
    unfold gθ
    rw [if_pos hp]
    rfl
  · have hw' : rho d₀ s₁ a₀ ≤ ‖w₀ - B.s (zθ P θ₀)‖ := not_lt.1 hw
    have hev : ∀ᶠ p : ThetaSpace m × ℂ in 𝓝 (θ₀, w₀), rad d₀ s₁ a₀ < ‖p.2 - B.s (zθ P p.1)‖ :=
      (continuousAt_const.eventually_lt ((continuousAt_snd.sub cS).norm) (lt_of_lt_of_le h3 hw'))
    have : (fun p : ThetaSpace m × ℂ => gθ P B p.1 p.2) =ᶠ[𝓝 (θ₀, w₀)] fun _ => (0 : ℂ) := by
      filter_upwards [hgood, hev] with p hp hq
      unfold gθ
      rw [if_pos hp]
      unfold gfun
      rw [cutoff_eq_zero (rad_pos (B.bg _ (hZ p.1.1 p.1.2 p.1.2.2) hp)) hq.le]
      simp
    exact continuousAt_const.congr this.symm

include hZ in
theorem continuousAt_Fθ {θ₀ : ThetaSpace m} (h0 : good P θ₀) (x₀ : EuclideanSpace ℝ (Fin 2)) :
    ContinuousAt (fun p : ThetaSpace m × EuclideanSpace ℝ (Fin 2) => Fθ κ P B p.1 p.2) (θ₀, x₀) := by
  have hg : ContinuousAt (fun p : ThetaSpace m × EuclideanSpace ℝ (Fin 2) =>
      gθ P B p.1 (isoR2.symm p.2)) (θ₀, x₀) :=
    ContinuousAt.comp (g := fun p : ThetaSpace m × ℂ => gθ P B p.1 p.2)
      (f := fun p : ThetaSpace m × EuclideanSpace ℝ (Fin 2) => (p.1, isoR2.symm p.2)) (x := (θ₀, x₀))
      (continuousAt_gθ P B hZ h0 (isoR2.symm x₀))
      (continuousAt_fst.prodMk (isoR2.symm.continuous.continuousAt.comp continuousAt_snd))
  have hu : ContinuousAt (fun p : ThetaSpace m × EuclideanSpace ℝ (Fin 2) => uθ κ P p.1) (θ₀, x₀) :=
    (continuous_uθ κ P).continuousAt.comp (f := Prod.fst) continuousAt_fst
  exact Complex.continuous_re.continuousAt.comp (hu.mul hg)

include hZ in
theorem aesm_resKd (R : ℝ) :
    AEStronglyMeasurable (fun θ => resKd (Kdisc R) (Fθ κ P B θ)) (nu m) := by
  classical
  have hKc : CompactSpace (Kdisc R) := inferInstance
  set f0 : ThetaSpace m → C(Kdisc R, ℂ) := fun θ => resKd (Kdisc R) (Fθ κ P B θ) with hf0
  borelize C(Kdisc R, ℂ)
  have hFcont : ∀ θ, ContinuousOn (Fθ κ P B θ) (Kdisc R) :=
    fun θ => (contDiff_Fθ κ P B hZ θ).continuous.continuousOn
  -- continuity on the good set
  let Gd := {θ : ThetaSpace m // good P θ}
  let H : C(Gd × Kdisc R, ℂ) :=
    ⟨fun p => ((Fθ κ P B p.1.1 p.2.1 : ℝ) : ℂ), by
      refine continuous_iff_continuousAt.2 (fun p => ?_)
      have hat := continuousAt_Fθ κ P B hZ p.1.2 p.2.1
      have hmap : Continuous (fun q : Gd × Kdisc R => ((q.1.1, q.2.1) : ThetaSpace m × EuclideanSpace ℝ (Fin 2))) :=
        (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
      exact Complex.continuous_ofReal.continuousAt.comp (hat.comp (f := fun q : Gd × Kdisc R =>
        ((q.1.1, q.2.1) : ThetaSpace m × EuclideanSpace ℝ (Fin 2))) hmap.continuousAt)⟩
  have hcurry : ∀ θ : Gd, H.curry θ = f0 θ.1 := by
    intro θ
    ext x
    simp only [ContinuousMap.curry_apply, ContinuousMap.coe_mk, hf0]
    rw [resKd_apply (hFcont θ.1) x]
    rfl
  have hcon : ContinuousOn f0 {θ | good P θ} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have : ({θ | good P θ}.domRestrict f0) = fun θ : Gd => H.curry θ := by
      funext θ; exact (hcurry θ).symm
    rw [this]
    exact H.curry.continuous
  have hbad : ∀ θ, ¬ good P θ → f0 θ = resKd (Kdisc R) (fun _ => 0) := by
    intro θ h
    simp only [hf0]
    rw [Fθ_bad κ P B h]
  have hpw : f0 = {θ | good P θ}.piecewise f0 (fun _ => resKd (Kdisc R) (fun _ => 0)) := by
    classical
    funext θ
    by_cases h : good P θ
    · simp [Set.piecewise, h]
    · simp [Set.piecewise, h, hbad θ h]
  have hmeas : Measurable f0 := by
    classical
    rw [hpw]
    exact ContinuousOn.measurable_piecewise hcon continuousOn_const (isOpen_good P).measurableSet
  exact hmeas.aestronglyMeasurable

include hZ in
theorem hasDerivAt_gθ (θ : ThetaSpace m) :
    HasDerivAt (gθ P B θ) (dθ P B θ) (B.s (zθ P θ)) := by
  unfold gθ dθ
  by_cases h : good P θ
  · rw [if_pos h, if_pos h]
    have hbg := B.bg _ (hZ θ.1 θ.2 θ.2.2) h
    have hDne : B.D (zθ P θ) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hbg.hd0 hbg.hD)
    have hAne : B.A (zθ P θ) ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le hbg.ha0 hbg.hA)
    have hsD : B.s (zθ P θ) + B.D (zθ P θ) ≠ 0 := by
      intro h0
      apply hAne
      have hAd : B.A (zθ P θ) = (B.s (zθ P θ) + B.D (zθ P θ)) / 2 := hbg.hAd
      rw [hAd, h0]; simp
    exact (hasDerivAt_chartLambda (B.c0 (zθ P θ)) hDne hsD hbg.hAd).congr_of_eventuallyEq
      (gfun_eq_chart_near hbg (B.c0 (zθ P θ)))
  · rw [if_neg h, if_neg h]
    exact hasDerivAt_const _ _

include hZ in
theorem aesm_dθ : AEStronglyMeasurable (dθ P B) (nu m) := by
  classical
  borelize ℂ
  have hD0 : ∀ θ, good P θ → B.D (zθ P θ) ≠ 0 := fun θ h =>
    norm_pos_iff.1 (lt_of_lt_of_le (B.bg _ (hZ θ.1 θ.2 θ.2.2) h).hd0 (B.bg _ (hZ θ.1 θ.2 θ.2.2) h).hD)
  have hcon : ContinuousOn (fun θ => (B.D (zθ P θ))⁻¹) {θ | good P θ} := by
    have : ContinuousOn (fun θ => B.D (zθ P θ)) {θ | good P θ} :=
      B.hD.comp (continuous_zθ P).continuousOn (fun θ hθ => ⟨hZ θ.1 θ.2 θ.2.2, hθ⟩)
    exact this.inv₀ (fun θ hθ => hD0 θ hθ)
  have hpw : dθ P B = {θ | good P θ}.piecewise (fun θ => (B.D (zθ P θ))⁻¹) (fun _ => 0) := by
    funext θ
    by_cases h : good P θ
    · simp [dθ, Set.piecewise, h]
    · simp [dθ, Set.piecewise, h]
  have hmeas : Measurable (dθ P B) := by
    rw [hpw]
    exact ContinuousOn.measurable_piecewise hcon continuousOn_const (isOpen_good P).measurableSet
  exact hmeas.aestronglyMeasurable

include hZ in
theorem aesm_fderiv (j : Fin 2) :
    AEStronglyMeasurable (fun θ => fderiv ℝ (Fθ κ P B θ) (isoR2 (B.s (zθ P θ))) (EuclideanSpace.single j 1))
      (nu m) := by
  have heq : ∀ θ, fderiv ℝ (Fθ κ P B θ) (isoR2 (B.s (zθ P θ))) (EuclideanSpace.single j 1) =
      (uθ κ P θ * dθ P B θ * isoR2.symm (EuclideanSpace.single j 1)).re := fun θ => by
    unfold Fθ
    exact fderiv_quadF (uθ κ P θ) (hasDerivAt_gθ P B hZ θ) j
  simp_rw [heq]
  have hd := (aesm_dθ P B hZ)
  have hu : AEStronglyMeasurable (uθ κ P) (nu m) := (continuous_uθ κ P).aestronglyMeasurable
  exact Complex.continuous_re.comp_aestronglyMeasurable
    ((hu.mul hd).mul aestronglyMeasurable_const)

end QuantumNLS.MPFamilyMeas

#print axioms QuantumNLS.MPFamilyMeas.continuousAt_gθ
#print axioms QuantumNLS.MPFamilyMeas.aesm_resKd
#print axioms QuantumNLS.MPFamilyMeas.aesm_fderiv
