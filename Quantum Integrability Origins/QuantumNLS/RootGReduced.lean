import QuantumNLS.RootGBracket
import QuantumNLS.RootGNeighbourhood

/-!
# R-C4F43CA8 part (c): the reduced bracket on the unit sphere, and the zero brackets restated

**Source (ROOT_transfer_involution.tex:18-23).** For phase-invariant functions the Poisson bracket restricted to the unit
sphere is the bracket on the common-phase quotient; equivalently, radial additions to the gradients make no contribution,
since their pairing with a gradient is real by common-phase invariance.

**Formal reading (recorded for Terra).**
* `PhaseInv L F`: `F (c • v) = F v` for all complex `c` with `‖c‖ = 1` and all `v` (common-phase invariance).
* `tanGrad L G u := ∇G(u) − Re⟪u, ∇G(u)⟫ • u`: the gradient with its radial component at `u` removed. For unit `u`,
  `Re⟪u, tanGrad⟫ = 0` (`re_inner_tanGrad`), so `tanGrad` is the tangential gradient of the sphere.
* `reducedR L F G u := dF(u)[(−i) • tanGrad G u]`: the reduced bracket on the sphere. `reducedC` is its complex bilinear
  extension, with the same four-term combination as `SymplecticBracket.pbC`.
* Equivalence (`pbR_eq_reducedR`, `pbC_eq_reducedC`): for `F` phase-invariant and differentiable at `u`, the full bracket
  `pbR F G u` equals `reducedR F G u` for every `G`. The difference is `dF(u)[(−i)•(Re⟪u,∇G⟫•u)] = −Re⟪u,∇G⟫ dF(u)[i•u]`,
  and `dF(u)[i•u] = 0` by phase invariance (`fderiv_I_smul_eq_zero`).

Proved here (standard axioms only):
* `fderiv_I_smul_eq_zero`, `re_inner_tanGrad`, `pbR_eq_reducedR`, `pbC_eq_reducedC`, `G_phaseInv` (from
  `FullMass.Mmeas_phase`), `G_re_im_differentiable`;
* `reduced_bracket_zero`: the four real and two complex zero brackets of `RootGBracket.G_pbR_zero`/`G_pbC_zero`,
  restated for the reduced bracket on the unit sphere.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

namespace QuantumNLS.RootGReduced

open QuantumNLS.SymplecticBracket QuantumNLS.RootGBracket QuantumNLS.RootGNeighbourhood
  QuantumNLS.RootGLocal QuantumNLS.PhysicalTensor

/-- Common-phase invariance on the full space: `F (c • v) = F v` for unit complex `c`. -/
def PhaseInv {E : Type*} (L : ℝ) [Fact (0 < L)] (F : L2T L → E) : Prop :=
  ∀ c : ℂ, ‖c‖ = 1 → ∀ v : L2T L, F (c • v) = F v

/-- Tangential gradient: the gradient with its radial component at `u` removed. -/
def tanGrad (L : ℝ) [Fact (0 < L)] (G : L2T L → ℝ) (u : L2T L) : L2T L :=
  SymplecticBracket.gradient G u - (inner ℂ u (SymplecticBracket.gradient G u)).re • u

/-- Reduced bracket on the sphere: `dF(u)[(−i) • ∇^T G(u)]`. -/
def reducedR (L : ℝ) [Fact (0 < L)] (F G : L2T L → ℝ) (u : L2T L) : ℝ :=
  fderiv ℝ F u ((-Complex.I) • tanGrad L G u)

/-- Complex reduced bracket, the same four-term combination as `pbC`. -/
def reducedC (L : ℝ) [Fact (0 < L)] (F G : L2T L → ℂ) (u : L2T L) : ℂ :=
  ⟨reducedR L (fun v => (F v).re) (fun v => (G v).re) u - reducedR L (fun v => (F v).im) (fun v => (G v).im) u,
    reducedR L (fun v => (F v).im) (fun v => (G v).re) u + reducedR L (fun v => (F v).re) (fun v => (G v).im) u⟩

/-- A phase-invariant real function has zero derivative in the direction `i • u`. -/
theorem fderiv_I_smul_eq_zero (L : ℝ) [Fact (0 < L)] {F : L2T L → ℝ} {u : L2T L}
    (hF : DifferentiableAt ℝ F u) (hinv : PhaseInv L F) :
    fderiv ℝ F u (Complex.I • u) = 0 := by
  set γ : ℝ → L2T L := fun t => Complex.exp ((t : ℂ) * Complex.I) • u with hγ
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const Complex.I
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) Complex.I 0 := by
    simpa using h0.cexp
  have hγd : HasDerivAt γ (Complex.I • u) 0 := h1.smul_const u
  have hγ0 : γ 0 = u := by simp [hγ]
  have hF0 : HasFDerivAt F (fderiv ℝ F u) (γ 0) := by
    rw [hγ0]
    exact hF.hasFDerivAt
  have hcomp : HasDerivAt (F ∘ γ) (fderiv ℝ F u (Complex.I • u)) 0 := hF0.comp_hasDerivAt 0 hγd
  have hconst : F ∘ γ = fun _ => F u := by
    funext t
    exact hinv _ (Complex.norm_exp_ofReal_mul_I t) u
  have hzero : HasDerivAt (F ∘ γ) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const _ _
  exact hcomp.unique hzero

/-- For a unit vector, the tangential gradient is real-orthogonal to `u`. -/
theorem re_inner_tanGrad (L : ℝ) [Fact (0 < L)] (G : L2T L → ℝ) (u : L2T L) (hu : ‖u‖ = 1) :
    (inner ℂ u (tanGrad L G u)).re = 0 := by
  unfold tanGrad
  rw [inner_sub_right, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, inner_self_eq_norm_sq_to_K, hu]
  simp

/-- **Equivalence.** For a phase-invariant `F` differentiable at `u`, the full bracket equals the reduced bracket:
radial additions to `∇G` contribute nothing. -/
theorem pbR_eq_reducedR (L : ℝ) [Fact (0 < L)] {F G : L2T L → ℝ} {u : L2T L}
    (hF : DifferentiableAt ℝ F u) (hinv : PhaseInv L F) :
    pbR F G u = reducedR L F G u := by
  unfold pbR reducedR hamField
  have hdec : SymplecticBracket.gradient G u = tanGrad L G u + (inner ℂ u (SymplecticBracket.gradient G u)).re • u := by
    unfold tanGrad
    abel
  have hrad : fderiv ℝ F u ((-Complex.I) • (inner ℂ u (SymplecticBracket.gradient G u)).re • u) = 0 := by
    rw [smul_comm, map_smul, neg_smul, map_neg, fderiv_I_smul_eq_zero L hF hinv]
    simp
  rw [hdec, smul_add, map_add]
  exact add_eq_left.mpr hrad

/-- Real part of a phase-invariant complex function is phase-invariant. -/
theorem phaseInv_re {L : ℝ} [Fact (0 < L)] {F : L2T L → ℂ} (hF : PhaseInv L F) :
    PhaseInv L (fun v => (F v).re) :=
  fun c hc v => by simp only [hF c hc v]

/-- Imaginary part of a phase-invariant complex function is phase-invariant. -/
theorem phaseInv_im {L : ℝ} [Fact (0 < L)] {F : L2T L → ℂ} (hF : PhaseInv L F) :
    PhaseInv L (fun v => (F v).im) :=
  fun c hc v => by simp only [hF c hc v]

/-- **Equivalence, complex form.** -/
theorem pbC_eq_reducedC (L : ℝ) [Fact (0 < L)] {F G : L2T L → ℂ} {u : L2T L}
    (hre : DifferentiableAt ℝ (fun v => (F v).re) u) (him : DifferentiableAt ℝ (fun v => (F v).im) u)
    (hF : PhaseInv L F) :
    pbC F G u = reducedC L F G u := by
  unfold pbC reducedC
  simp only [pbR_eq_reducedR L hre (phaseInv_re hF), pbR_eq_reducedR L him (phaseInv_im hF)]

/-- `G_z` is common-phase invariant on the full space (`FullMass.Mmeas_phase`). -/
theorem G_phaseInv (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) :
    PhaseInv L (fun v : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z) := by
  intro c hc v
  show QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ (c • v)) z =
    QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z
  rw [FullMass.Mmeas_phase hκ v hc]

/-- Real and imaginary parts of `G_z` are differentiable at a unit vector (from `G_hasFDerivAt_region`). -/
theorem G_re_im_differentiable (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z : ℂ) (hz4 : 4 * κ < z.im)
    (hzL : Real.log 16 < L * z.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    DifferentiableAt ℝ (fun v : L2T L => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re) u0 ∧
    DifferentiableAt ℝ (fun v : L2T L => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im) u0 := by
  have hp : 0 < ‖u0‖ := by rw [hu0]; norm_num
  have hr : ‖u0‖ ^ 2 < 1 + gMargin κ z := by
    rw [hu0, one_pow]
    linarith [gMargin_pos hκ hz4]
  have hb : ‖u0‖ < 2 := by rw [hu0]; norm_num
  have hG : DifferentiableAt ℝ (fun v : L2T L => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z) u0 :=
    (G_hasFDerivAt_region L κ hκ z hz4 hzL u0 hp hr hb).2.differentiableAt
  exact ⟨Complex.reCLM.differentiableAt.comp u0 hG, Complex.imCLM.differentiableAt.comp u0 hG⟩

/-- **Part (c), assembled.** The four real and two complex zero brackets of `G_z`, `G_w` on the unit sphere, restated for
the reduced bracket (the same statements as `RootGBracket.G_pbR_zero` and `G_pbC_zero`). -/
theorem reduced_bracket_zero (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (z w : ℂ)
    (hz4 : 4 * κ < z.im) (hzL : Real.log 16 < L * z.im)
    (hw4 : 4 * κ < w.im) (hwL : Real.log 16 < L * w.im) (u0 : L2T L) (hu0 : ‖u0‖ = 1) :
    reducedC L (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z)
        (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w) u0 = 0 ∧
    reducedC L (fun v => QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z)
        (fun v => conj (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w)) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).im)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).re) u0 = 0 ∧
    reducedR L (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) z).re)
        (fun v => (QuantumNLS.CauchyUniqueness.cauchyTransform (FullMass.Mmeas κ v) w).im) u0 = 0 := by
  obtain ⟨h1, h2⟩ := G_pbC_zero L κ hκ z w hz4 hzL hw4 hwL u0 hu0
  obtain ⟨h3, h4, h5, h6⟩ := G_pbR_zero L κ hκ z w hz4 hzL hw4 hwL u0 hu0
  obtain ⟨hre, him⟩ := G_re_im_differentiable L κ hκ z hz4 hzL u0 hu0
  have hph := G_phaseInv L κ hκ z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pbC_eq_reducedC L hre him hph).symm.trans h1
  · exact (pbC_eq_reducedC L hre him hph).symm.trans h2
  · exact (pbR_eq_reducedR L hre (phaseInv_re hph)).symm.trans h3
  · exact (pbR_eq_reducedR L him (phaseInv_im hph)).symm.trans h4
  · exact (pbR_eq_reducedR L him (phaseInv_im hph)).symm.trans h5
  · exact (pbR_eq_reducedR L hre (phaseInv_re hph)).symm.trans h6

end QuantumNLS.RootGReduced

#print axioms QuantumNLS.RootGReduced.reduced_bracket_zero
#print axioms QuantumNLS.RootGReduced.pbR_eq_reducedR
