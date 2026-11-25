import QuantumNLS.RootOverlapLimit

/-!
# R-32EBD5C1 `lem:root-overlap`, remaining clause: the bracket on the common-phase quotient
(ROOT_transfer_involution.tex:18-23, the remark that `{·,·}` "can be computed either on the full Hilbert
space or on the phase quotient of the unit sphere")

`RootOverlapLimit.root_overlap_limit` proves `lim −iN⟨u^{⊗N},[Q_{N,p}(A),Q_{N,q}(B)]u^{⊗N}⟩ = {a,b}(u)` with the
full-space bracket of DEF-015 (`SymplecticBracket.pbC`).  This module realizes the second reading of the
remark and proves that it agrees with the first.

Realization (no assumed conclusion, nothing supplied):

* `Sph H = {u // ‖u‖ = 1}` with the action of the circle group `Circle` by `u ↦ c • u`; the phase quotient is
  `PhaseQuot H = MulAction.orbitRel.Quotient Circle (Sph H)` with projection `proj`.
* A phase-invariant function `F : H → β` (`PhaseInv F`: `F (c • v) = F v` for `c : Circle`) descends to
  `descend F hF : PhaseQuot H → β` with `descend F hF (proj u) = F u` (`descend_proj`); the product symbol
  `v ↦ ⟨v^{⊗p}, A v^{⊗p}⟩` of every bounded symmetric kernel is phase invariant (`kps_circle`).
* The quotient bracket `qbr a b : PhaseQuot H → ℝ` of two functions `a, b : PhaseQuot H → ℝ` on the quotient is
  the source recipe: extend `a` to a function `extR a` on `H ∖ {0}` that is constant along rays and along
  phases (`extR a v = a [v/‖v‖]`), form the horizontal gradients `hg F u = ∇F(u) − ⟨u,∇F(u)⟩u` (the gradient
  minus its component along the complex line `ℂu`) and insert them into `Ω`:
  `qbr a b [u] = Ω(hg (extR a) u, hg (extR b) u)`.  It is a `Quotient.lift`; the proof that it is independent of
  the representative uses the equivariance `∇F(c•v) = c•∇F(v)` of gradients of phase-invariant functions
  (`gradient_rot`, `hg_rot`, `qpre_rot`).  `qbrC` is the complex bilinear extension, exactly as `pbC`.
* Agreement (`qbr_eq_pbR`, `qbrC_eq_pbC`): for phase-invariant `F, G` differentiable at the unit vector `u` and
  any `a, b` on the quotient with `a ∘ proj = F|_S`, `b ∘ proj = G|_S`,
  `qbr a b [u] = {F,G}(u)` (full-space bracket).  Ingredients: the Fréchet derivative of the normalization
  `v ↦ v/‖v‖` at a unit vector (`hasFDerivAt_nu`), which gives `hg (extR a) u = hg F u` (`hg_ext`), and the fact
  that for phase-invariant `F` the inner product `⟨u,∇F(u)⟩` is real (`im_inner_gradient`, from the vanishing
  derivative along the phase curve `e^{iθ}u`), so that removing the complex-line components of the gradients
  does not change `Im⟨∇F,∇G⟩` (`RootOverlapLimit.im_inner_tangential`).  This holds for every phase-invariant
  pair, not only for symbols of self-adjoint kernels.
* `root_overlap_limit_quotient`: `root_overlap_limit` with the right-hand side the quotient bracket of the
  descended product symbols, `lim_{N→∞} −iN⟨u^{⊗N},[Q_{N,p}(A),Q_{N,q}(B)]u^{⊗N}⟩ =
  qbrC (ā) (b̄) [u]` for every point `[u]` of the quotient and every bounded kernels `A, B` (no self-adjointness).
  `qbr_symbolR_formula` records the printed value `2pq Im⟨α_⊥,β_⊥⟩` of the quotient bracket for self-adjoint
  kernels.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace TensorProduct ComplexConjugate
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements QuantumNLS.KernelDefinition
  QuantumNLS.PlacementFusion QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementCovariance QuantumNLS.PlacementGrouping QuantumNLS.PlacementUnionReindex
  QuantumNLS.PlacementFiberOperator QuantumNLS.RootOverlapCommutator QuantumNLS.RootOverlapLimit

namespace QuantumNLS.PhaseQuotientBracket

open QuantumNLS.SymplecticBracket (omega pbR pbC hamField fderiv_eq_two_inner_gradient pbR_eq_omega)
local notation "sgrad" => QuantumNLS.SymplecticBracket.gradient

/-! ### The phase quotient of the unit sphere -/

section Quot
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem circle_conj_mul (c : Circle) : (starRingEnd ℂ) (c : ℂ) * (c : ℂ) = 1 := by
  rw [Complex.conj_mul', Circle.norm_coe]; norm_num

theorem inner_smul_circle (c : Circle) (x y : H) : ⟪c • x, c • y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [Circle.smul_def, Circle.smul_def, inner_smul_left, inner_smul_right, ← mul_assoc,
    circle_conj_mul, one_mul]

/-- The unit sphere of `H`. -/
def Sph (H : Type*) [NormedAddCommGroup H] : Type _ := {u : H // ‖u‖ = 1}

instance : SMul Circle (Sph H) := ⟨fun c u => ⟨c • u.1, by rw [Circle.norm_smul]; exact u.2⟩⟩

theorem Sph.smul_val (c : Circle) (u : Sph H) : (c • u).1 = c • u.1 := rfl

instance : MulAction Circle (Sph H) where
  one_smul u := Subtype.ext (one_smul Circle u.1)
  mul_smul a b u := Subtype.ext (mul_smul a b u.1)

/-- The common-phase quotient of the unit sphere: orbits of the circle action `u ↦ e^{iθ}u`. -/
abbrev PhaseQuot (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Type _ :=
  MulAction.orbitRel.Quotient Circle (Sph H)

/-- The projection `π : S → S/U(1)`. -/
def proj (u : Sph H) : PhaseQuot H := Quotient.mk'' u

theorem proj_sound {u v : Sph H} (c : Circle) (h : c • v = u) : proj u = proj v :=
  Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨c, h⟩))

theorem proj_smul (c : Circle) (u : Sph H) : proj (c • u) = proj u := proj_sound c rfl

/-- Invariance under the common phase `v ↦ c • v`, `c : Circle`. -/
def PhaseInv {β : Type*} (F : H → β) : Prop := ∀ (c : Circle) (v : H), F (c • v) = F v

/-- A phase-invariant function on `H` descends to the phase quotient: `descend F hF ∘ proj = F|_S`. -/
def descend {β : Type*} (F : H → β) (hF : PhaseInv F) : PhaseQuot H → β :=
  Quotient.lift (fun u : Sph H => F u.1) (by
    intro a b hab
    obtain ⟨c, hc⟩ := hab
    show F a.1 = F b.1
    rw [← hc]
    exact hF c b.1)

theorem descend_proj {β : Type*} (F : H → β) (hF : PhaseInv F) (u : Sph H) :
    descend F hF (proj u) = F u.1 := rfl

/-- The point of the sphere `v/‖v‖`. -/
def nuS (v : H) (hv : v ≠ 0) : Sph H := ⟨(‖v‖⁻¹ : ℝ) • v, norm_smul_inv_norm hv⟩

open Classical in
/-- The extension `v ↦ a [v/‖v‖]` of a function on the quotient to `H` (constant along rays and phases;
`0` at the origin). -/
def extR (a : PhaseQuot H → ℝ) (v : H) : ℝ := if hv : v = 0 then 0 else a (proj (nuS v hv))

theorem ne_zero_smul (c : Circle) {v : H} (hv : v ≠ 0) : c • v ≠ 0 := by
  intro h
  apply hv
  have := Circle.norm_smul c v
  rw [h, norm_zero] at this
  exact norm_eq_zero.mp this.symm

theorem extR_phaseInv (a : PhaseQuot H → ℝ) : PhaseInv (extR a) := by
  intro c v
  unfold extR
  by_cases hv : v = 0
  · simp [hv]
  · have hcv := ne_zero_smul c hv
    rw [dif_neg hcv, dif_neg hv]
    congr 1
    apply proj_sound c
    apply Subtype.ext
    show c • ((‖v‖⁻¹ : ℝ) • v) = (‖c • v‖⁻¹ : ℝ) • (c • v)
    rw [Circle.norm_smul, smul_comm]

theorem extR_of_restrict {F : H → ℝ} {a : PhaseQuot H → ℝ} (ha : ∀ u : Sph H, a (proj u) = F u.1)
    {v : H} (hv : v ≠ 0) : extR a v = F ((‖v‖⁻¹ : ℝ) • v) := by
  unfold extR
  rw [dif_neg hv]
  exact ha (nuS v hv)

end Quot

/-! ### Horizontal gradients and the quotient bracket -/

section Calc
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
attribute [local instance] InnerProductSpace.complexToReal

theorem inner_rot_real (c : Circle) (x y : H) : inner ℝ (c • x) (c • y) = inner ℝ x y := by
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_smul_circle]

/-- Multiplication by `c : Circle` as a real continuous linear map. -/
def rotCLM (c : Circle) : H →L[ℝ] H := ((c : ℂ) • ContinuousLinearMap.id ℂ H).restrictScalars ℝ

theorem rotCLM_apply (c : Circle) (v : H) : rotCLM c v = c • v := rfl

theorem differentiableAt_rot {F : H → ℝ} (hF : PhaseInv F) (c : Circle) {v : H}
    (hd : DifferentiableAt ℝ F v) : DifferentiableAt ℝ F (c • v) := by
  have h1 : DifferentiableAt ℝ F (rotCLM c⁻¹ (c • v)) := by
    rw [rotCLM_apply, inv_smul_smul]; exact hd
  have h2 := h1.comp (c • v) (rotCLM c⁻¹).differentiableAt
  have e : (F ∘ rotCLM c⁻¹) = F := funext fun w => hF c⁻¹ w
  rw [e] at h2
  exact h2

/-- The Fréchet derivative of a phase-invariant function is equivariant (no regularity assumed). -/
theorem fderiv_rot {F : H → ℝ} (hF : PhaseInv F) (c : Circle) (v h : H) :
    fderiv ℝ F (c • v) (c • h) = fderiv ℝ F v h := by
  have hcomp : (F ∘ rotCLM c) = F := funext fun w => hF c w
  by_cases hd : DifferentiableAt ℝ F v
  · have hd' : DifferentiableAt ℝ F (rotCLM c v) := by
      rw [rotCLM_apply]; exact differentiableAt_rot hF c hd
    have := fderiv_comp v hd' (rotCLM c).differentiableAt
    rw [hcomp] at this
    rw [this, ContinuousLinearMap.fderiv]; rfl
  · have hnd : ¬ DifferentiableAt ℝ F (c • v) := by
      intro h'
      apply hd
      have h'' : DifferentiableAt ℝ F (rotCLM c v) := by rw [rotCLM_apply]; exact h'
      have := h''.comp v (rotCLM c).differentiableAt
      rwa [hcomp] at this
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hnd]; rfl

/-- `∇F(c•v) = c•∇F(v)` for phase-invariant `F`. -/
theorem gradient_rot {F : H → ℝ} (hF : PhaseInv F) (c : Circle) (v : H) :
    sgrad F (c • v) = c • sgrad F v := by
  apply ext_inner_right ℝ
  intro h
  have h1 := fderiv_eq_two_inner_gradient F (c • v) h
  have h2 := fderiv_eq_two_inner_gradient F v (c⁻¹ • h)
  have h3 := fderiv_rot hF c v (c⁻¹ • h)
  rw [smul_inv_smul] at h3
  have h4 : inner ℝ (c • sgrad F v) h = inner ℝ (sgrad F v) (c⁻¹ • h) := by
    have := inner_rot_real c (sgrad F v) (c⁻¹ • h)
    rw [smul_inv_smul] at this
    exact this
  rw [h4]
  linarith

/-- The horizontal gradient `∇F(u) − ⟨u,∇F(u)⟩u`: the gradient minus its component along the complex line
`ℂu` (for a unit vector `u`, the radial real component and the phase component). -/
def hg (F : H → ℝ) (u : H) : H := sgrad F u - ⟪u, sgrad F u⟫_ℂ • u

theorem hg_rot {F : H → ℝ} (hF : PhaseInv F) (c : Circle) (u : H) :
    hg F (c • u) = c • hg F u := by
  unfold hg
  rw [gradient_rot hF, inner_smul_circle, smul_sub, smul_comm c]

theorem omega_rot (c : Circle) (x y : H) : omega (c • x) (c • y) = omega x y := by
  unfold omega; rw [inner_smul_circle]

/-- The bracket of horizontal gradients at a representative. -/
def qpre (F G : H → ℝ) (u : H) : ℝ := omega (hg F u) (hg G u)

theorem qpre_rot {F G : H → ℝ} (hF : PhaseInv F) (hG : PhaseInv G) (c : Circle) (u : H) :
    qpre F G (c • u) = qpre F G u := by
  unfold qpre; rw [hg_rot hF, hg_rot hG, omega_rot]

/-- **The quotient bracket** `{a,b}_Q([u]) = Ω(hg (extR a) u, hg (extR b) u)` of two real functions on the
phase quotient (independent of the representative `u` of the class). -/
def qbr (a b : PhaseQuot H → ℝ) : PhaseQuot H → ℝ :=
  Quotient.lift (fun u : Sph H => qpre (extR a) (extR b) u.1) (by
    intro x y hxy
    obtain ⟨c, hc⟩ := hxy
    show qpre (extR a) (extR b) x.1 = qpre (extR a) (extR b) y.1
    rw [← hc]
    exact qpre_rot (extR_phaseInv a) (extR_phaseInv b) c y.1)

theorem qbr_proj (a b : PhaseQuot H → ℝ) (u : Sph H) :
    qbr a b (proj u) = qpre (extR a) (extR b) u.1 := rfl

/-- Independence of the representative, explicitly. -/
theorem qbr_proj_smul (a b : PhaseQuot H → ℝ) (c : Circle) (u : Sph H) :
    qbr a b (proj (c • u)) = qbr a b (proj u) := by
  rw [proj_smul]

/-- The complex bilinear extension of the quotient bracket (as `pbC` extends `pbR`). -/
def qbrC (a b : PhaseQuot H → ℂ) (x : PhaseQuot H) : ℂ :=
  ⟨qbr (fun y => (a y).re) (fun y => (b y).re) x - qbr (fun y => (a y).im) (fun y => (b y).im) x,
    qbr (fun y => (a y).im) (fun y => (b y).re) x + qbr (fun y => (a y).re) (fun y => (b y).im) x⟩

/-! ### Derivative of the normalization and identification with the full-space bracket -/

theorem hasFDerivAt_norm_unit (u : H) (hu : ‖u‖ = 1) :
    HasFDerivAt (fun v : H => ‖v‖) (innerSL ℝ u) u := by
  have h1 := (hasStrictFDerivAt_norm_sq u).hasFDerivAt
  have hne : ‖u‖ ^ 2 ≠ 0 := by rw [hu]; norm_num
  have h2 := h1.sqrt hne
  have e : (fun v : H => Real.sqrt (‖v‖ ^ 2)) = fun v => ‖v‖ := by
    funext v; exact Real.sqrt_sq (norm_nonneg v)
  rw [e] at h2
  convert h2 using 1
  ext h
  simp [hu, two_smul]
  ring

/-- The derivative of the normalization `v ↦ v/‖v‖` at a unit vector `u` is `h ↦ h − Re⟨u,h⟩ u`. -/
theorem hasFDerivAt_nu (u : H) (hu : ‖u‖ = 1) :
    HasFDerivAt (fun v : H => (‖v‖⁻¹ : ℝ) • v)
      (ContinuousLinearMap.id ℝ H - (innerSL ℝ u).smulRight u) u := by
  have hn := hasFDerivAt_norm_unit u hu
  have hinv := (hasDerivAt_inv (x := ‖u‖) (by rw [hu]; norm_num)).comp_hasFDerivAt u hn
  have h := hinv.smul (hasFDerivAt_id u)
  refine h.congr_fderiv ?_
  ext w
  simp [hu, sub_eq_add_neg]

theorem hasFDerivAt_ext {F : H → ℝ} {a : PhaseQuot H → ℝ} (ha : ∀ u : Sph H, a (proj u) = F u.1)
    {u : H} (hu : ‖u‖ = 1) (hd : DifferentiableAt ℝ F u) :
    HasFDerivAt (extR a)
      ((fderiv ℝ F u).comp (ContinuousLinearMap.id ℝ H - (innerSL ℝ u).smulRight u)) u := by
  have hν := hasFDerivAt_nu u hu
  have hνu : (‖u‖⁻¹ : ℝ) • u = u := by rw [hu]; simp
  have hd' : HasFDerivAt F (fderiv ℝ F u) ((‖u‖⁻¹ : ℝ) • u) := by
    rw [hνu]; exact hd.hasFDerivAt
  have hcomp := HasFDerivAt.comp (f := fun v : H => (‖v‖⁻¹ : ℝ) • v) u hd' hν
  refine hcomp.congr_of_eventuallyEq ?_
  have hne : ∀ᶠ v in nhds u, v ≠ 0 := isOpen_ne.mem_nhds (by rintro rfl; simp at hu)
  filter_upwards [hne] with v hv
  exact extR_of_restrict ha hv

/-- Gradient of the ray-and-phase-constant extension at a unit vector. -/
theorem gradient_ext {F : H → ℝ} {a : PhaseQuot H → ℝ} (ha : ∀ u : Sph H, a (proj u) = F u.1)
    {u : H} (hu : ‖u‖ = 1) (hd : DifferentiableAt ℝ F u) :
    sgrad (extR a) u = sgrad F u - (inner ℝ (sgrad F u) u) • u := by
  have hE := hasFDerivAt_ext ha hu hd
  apply ext_inner_right ℝ
  intro h
  have h1 := fderiv_eq_two_inner_gradient (extR a) u h
  rw [hE.fderiv] at h1
  have h2 := fderiv_eq_two_inner_gradient F u h
  have h3 := fderiv_eq_two_inner_gradient F u u
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_sub,
    map_smul, smul_eq_mul] at h1
  rw [inner_sub_left, real_inner_smul_left]
  rw [h2, h3] at h1
  linarith

theorem hasDerivAt_phase_curve (u : H) :
    HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I) • u) (Complex.I • u) 0 := by
  have h1 : HasDerivAt (fun w : ℂ => Complex.exp (w * Complex.I)) Complex.I ((0 : ℝ) : ℂ) := by
    have := ((hasDerivAt_id (((0 : ℝ) : ℂ))).mul_const Complex.I).cexp
    simpa using this
  have h2 := h1.comp_ofReal
  have h3 := h2.smul_const u
  simpa using h3

/-- For a phase-invariant `F`, `⟨u,∇F(u)⟩` is real: the derivative along the phase curve `e^{iθ}u`
vanishes. -/
theorem im_inner_gradient {F : H → ℝ} (hF : PhaseInv F) (u : H) (hd : DifferentiableAt ℝ F u) :
    (⟪u, sgrad F u⟫_ℂ).im = 0 := by
  have hcurve := hasDerivAt_phase_curve u
  have hF0 : ∀ t : ℝ, F (Complex.exp (t * Complex.I) • u) = F u := by
    intro t
    have := hF (Circle.exp t) u
    rwa [Circle.smul_def, Circle.coe_exp] at this
  have hl : HasFDerivAt F (fderiv ℝ F u) ((fun t : ℝ => Complex.exp (t * Complex.I) • u) 0) := by
    simpa using hd.hasFDerivAt
  have h1 := hl.comp_hasDerivAt (0 : ℝ) hcurve
  have h2 : HasDerivAt (fun t : ℝ => F (Complex.exp (t * Complex.I) • u)) 0 0 := by
    have : (fun t : ℝ => F (Complex.exp (t * Complex.I) • u)) = fun _ => F u := funext hF0
    rw [this]; exact hasDerivAt_const _ _
  have h3 : fderiv ℝ F u (Complex.I • u) = 0 := h1.unique h2
  have h4 := fderiv_eq_two_inner_gradient F u (Complex.I • u)
  rw [h3, real_inner_eq_re_inner ℂ, RCLike.re_to_complex, inner_smul_right] at h4
  have h5 := inner_conj_symm (𝕜 := ℂ) u (sgrad F u)
  rw [← h5, Complex.conj_im]
  simp [Complex.mul_re] at h4
  linarith

/-- The horizontal gradient of the extension of `a` equals the horizontal gradient of any phase-invariant
function `F` whose restriction to the sphere is `a ∘ proj`. -/
theorem hg_ext {F : H → ℝ} (hF : PhaseInv F) {a : PhaseQuot H → ℝ}
    (ha : ∀ u : Sph H, a (proj u) = F u.1) {u : H} (hu : ‖u‖ = 1) (hd : DifferentiableAt ℝ F u) :
    hg (extR a) u = hg F u := by
  have huu : ⟪u, u⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hu]; norm_num
  have hre : (⟪u, sgrad F u⟫_ℂ).re = inner ℝ (sgrad F u) u := by
    rw [real_inner_eq_re_inner ℂ, RCLike.re_to_complex, ← inner_conj_symm u (sgrad F u),
      Complex.conj_re]
  have hr : ⟪u, sgrad F u⟫_ℂ = ((inner ℝ (sgrad F u) u : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact hre
    · rw [Complex.ofReal_im]; exact im_inner_gradient hF u hd
  have h0 : ⟪u, sgrad F u - (inner ℝ (sgrad F u) u) • u⟫_ℂ = 0 := by
    rw [← Complex.coe_smul, inner_sub_right, inner_smul_right, huu, ← hr]
    ring
  unfold hg
  rw [gradient_ext ha hu hd, h0, zero_smul, sub_zero, hr, Complex.coe_smul]

/-- **Agreement of the two readings of the bracket.**  For phase-invariant `F, G` differentiable at the unit
vector `u` and any functions `a, b` on the quotient with `a ∘ proj = F|_S`, `b ∘ proj = G|_S`, the quotient
bracket at `[u]` is the full-space bracket `{F,G}(u)`. -/
theorem qbr_eq_pbR {F G : H → ℝ} (hF : PhaseInv F) (hG : PhaseInv G) {a b : PhaseQuot H → ℝ}
    (ha : ∀ u : Sph H, a (proj u) = F u.1) (hb : ∀ u : Sph H, b (proj u) = G u.1) (u : Sph H)
    (hFd : DifferentiableAt ℝ F u.1) (hGd : DifferentiableAt ℝ G u.1) :
    qbr a b (proj u) = pbR F G u.1 := by
  rw [qbr_proj, qpre, hg_ext hF ha u.2 hFd, hg_ext hG hb u.2 hGd, pbR_eq_omega]
  unfold hg omega
  rw [im_inner_tangential u.1 _ _ u.2 (im_inner_gradient hF u.1 hFd) (im_inner_gradient hG u.1 hGd)]

/-- Complex-valued version: `qbrC a b [u] = pbC F G u`. -/
theorem qbrC_eq_pbC {F G : H → ℂ} (hF : PhaseInv F) (hG : PhaseInv G) {a b : PhaseQuot H → ℂ}
    (ha : ∀ u : Sph H, a (proj u) = F u.1) (hb : ∀ u : Sph H, b (proj u) = G u.1) (u : Sph H)
    (hFre : DifferentiableAt ℝ (fun v => (F v).re) u.1)
    (hFim : DifferentiableAt ℝ (fun v => (F v).im) u.1)
    (hGre : DifferentiableAt ℝ (fun v => (G v).re) u.1)
    (hGim : DifferentiableAt ℝ (fun v => (G v).im) u.1) :
    qbrC a b (proj u) = pbC F G u.1 := by
  have iFre : PhaseInv (fun v => (F v).re) := fun c v => by simp only [hF c v]
  have iFim : PhaseInv (fun v => (F v).im) := fun c v => by simp only [hF c v]
  have iGre : PhaseInv (fun v => (G v).re) := fun c v => by simp only [hG c v]
  have iGim : PhaseInv (fun v => (G v).im) := fun c v => by simp only [hG c v]
  have e1 := qbr_eq_pbR iFre iGre (a := fun y => (a y).re) (b := fun y => (b y).re)
    (fun w => by simp only [ha w]) (fun w => by simp only [hb w]) u hFre hGre
  have e2 := qbr_eq_pbR iFim iGim (a := fun y => (a y).im) (b := fun y => (b y).im)
    (fun w => by simp only [ha w]) (fun w => by simp only [hb w]) u hFim hGim
  have e3 := qbr_eq_pbR iFim iGre (a := fun y => (a y).im) (b := fun y => (b y).re)
    (fun w => by simp only [ha w]) (fun w => by simp only [hb w]) u hFim hGre
  have e4 := qbr_eq_pbR iFre iGim (a := fun y => (a y).re) (b := fun y => (b y).im)
    (fun w => by simp only [ha w]) (fun w => by simp only [hb w]) u hFre hGim
  unfold qbrC pbC
  rw [e1, e2, e3, e4]

end Calc

/-! ### Product symbols of kernels -/

section Symbols
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem htpow_smul' (n : ℕ) (c : ℂ) (u : H) :
    (htpow n (c • u) : HilbertTensorPower ℂ H n) = c ^ n • htpow n u := by
  have h := (PiTensorProduct.tprod ℂ (s := fun _ : Fin n => H)).map_smul_univ
    (fun _ : Fin n => c) (fun _ : Fin n => u)
  have h' : (ptprod (fun _ : Fin n => c • u) : AlgTensorPower ℂ H n) =
      c ^ n • (ptprod (fun _ : Fin n => u) : AlgTensorPower ℂ H n) := by
    have := h
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  simp only [htpow]
  rw [h', UniformSpace.Completion.coe_smul]

/-- The product symbol of every bounded symmetric kernel is phase invariant. -/
theorem kps_circle {r : ℕ} (A : BoundedSymmetricKernel H r) (c : Circle) (v : H) :
    kernelProductSymbol A (c • v) = kernelProductSymbol A v := by
  have hv : (c • v : H) = (c : ℂ) • v := Circle.smul_def c v
  have hpow : (htpow r (c • v) : HilbertTensorPower ℂ H r) = (c : ℂ) ^ r • htpow r v := by
    rw [hv]; exact htpow_smul' r c v
  have hx : (⟨htpow r (c • v), htpow_mem_symSector r (c • v)⟩ : SymSector ℂ H r) =
      ((c : ℂ) ^ r) • (⟨htpow r v, htpow_mem_symSector r v⟩ : SymSector ℂ H r) := Subtype.ext hpow
  have hcc : (starRingEnd ℂ) ((c : ℂ) ^ r) * (c : ℂ) ^ r = 1 := by
    rw [map_pow, ← mul_pow, circle_conj_mul, one_pow]
  have key : ∀ x y : HilbertTensorPower ℂ H r,
      ⟪((c : ℂ) ^ r) • x, ((c : ℂ) ^ r) • y⟫_ℂ = ⟪x, y⟫_ℂ := by
    intro x y
    rw [inner_smul_left, inner_smul_right, ← mul_assoc, hcc, one_mul]
  unfold kernelProductSymbol
  rw [hx, map_smul, hpow]
  exact key (htpow r v) ((A ⟨htpow r v, htpow_mem_symSector r v⟩ : SymSector ℂ H r) :
    HilbertTensorPower ℂ H r)

theorem kps_phaseInv {r : ℕ} (A : BoundedSymmetricKernel H r) :
    PhaseInv (kernelProductSymbol A) := fun c v => kps_circle A c v

theorem kps_re_phaseInv {r : ℕ} (A : BoundedSymmetricKernel H r) :
    PhaseInv (fun v => (kernelProductSymbol A v).re) := fun c v => by simp only [kps_circle]

theorem kps_im_phaseInv {r : ℕ} (A : BoundedSymmetricKernel H r) :
    PhaseInv (fun v => (kernelProductSymbol A v).im) := fun c v => by simp only [kps_circle]

theorem symbolR_phaseInv {r : ℕ} (A : BoundedSymmetricKernel H r) : PhaseInv (symbolR A) :=
  fun c v => by unfold symbolR; rw [kps_circle]

/-- The real symbol of a kernel is Fréchet differentiable (no self-adjointness needed). -/
theorem differentiableAt_symbolR {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    DifferentiableAt ℝ (symbolR A) u := by
  set Ae := extendSymKernel A with hAe
  have hP := hasFDerivAt_htpow r u
  have hAeD : HasFDerivAt (fun v : H => Ae (htpow r v : HilbertTensorPower ℂ H r))
      ((Ae.restrictScalars ℝ).comp (dP r u)) u :=
    ((Ae.restrictScalars ℝ).hasFDerivAt).comp u hP
  have hI := hP.inner ℂ hAeD
  have hRe := Complex.reCLM.hasFDerivAt.comp u hI
  have hfun : symbolR A = ⇑Complex.reCLM ∘ fun t => ⟪(htpow r t :
      HilbertTensorPower ℂ H r), Ae (htpow r t)⟫_ℂ := by
    funext v
    simp only [symbolR, kernelProductSymbol, hAe, extend_htpow, Function.comp_apply,
      Complex.reCLM_apply]
  rw [hfun]
  exact hRe.differentiableAt

theorem differentiableAt_kps_re {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    DifferentiableAt ℝ (fun v => (kernelProductSymbol A v).re) u := by
  have : (fun v => (kernelProductSymbol A v).re) = symbolR (reK A) := funext (re_kps A)
  rw [this]; exact differentiableAt_symbolR (reK A) u

theorem differentiableAt_kps_im {r : ℕ} (A : BoundedSymmetricKernel H r) (u : H) :
    DifferentiableAt ℝ (fun v => (kernelProductSymbol A v).im) u := by
  have : (fun v => (kernelProductSymbol A v).im) = symbolR (imK A) := funext (im_kps A)
  rw [this]; exact differentiableAt_symbolR (imK A) u

/-- **The phase-quotient bracket of two product symbols is the full-space bracket.** -/
theorem qbrC_kps {p q : ℕ} (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q)
    (u : Sph H) :
    qbrC (descend (kernelProductSymbol A) (kps_phaseInv A))
        (descend (kernelProductSymbol B) (kps_phaseInv B)) (proj u) =
      pbC (kernelProductSymbol A) (kernelProductSymbol B) u.1 :=
  qbrC_eq_pbC (kps_phaseInv A) (kps_phaseInv B) (descend_proj _ _) (descend_proj _ _) u
    (differentiableAt_kps_re A u.1) (differentiableAt_kps_im A u.1)
    (differentiableAt_kps_re B u.1) (differentiableAt_kps_im B u.1)

open Filter Topology in
/-- **`lem:root-overlap`, with the right-hand side the bracket on the phase quotient.**  For all bounded
symmetric kernels `A, B` and every point `[u]` of the common-phase quotient of the unit sphere,
`lim_{N→∞} −iN⟨u^{⊗N},[Q_{N,p}(A),Q_{N,q}(B)]u^{⊗N}⟩ = {ā,b̄}_Q([u])`, where `ā, b̄` are the descended
product symbols and `{·,·}_Q` the quotient bracket `qbrC`. -/
theorem root_overlap_limit_quotient (p q : ℕ) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) (u : Sph H) :
    Tendsto (limSeq p q A B u.1) atTop
      (𝓝 (qbrC (descend (kernelProductSymbol A) (kps_phaseInv A))
        (descend (kernelProductSymbol B) (kps_phaseInv B)) (proj u))) := by
  rw [qbrC_kps A B u]
  exact root_overlap_limit p q A B u.1 u.2

section TangentialValue
attribute [local instance] InnerProductSpace.complexToReal

/-- The quotient bracket of the symbols of self-adjoint kernels has the printed value
`2pq Im⟨α_⊥,β_⊥⟩`, `α_⊥ = α − ⟨u,α⟩u`. -/
theorem qbr_symbolR_formula (p' q' : ℕ) {A : BoundedSymmetricKernel H (p' + 1)}
    {B : BoundedSymmetricKernel H (1 + q')} (hA : SelfAdj A) (hB : SelfAdj B) (u : Sph H) :
    qbr (descend (symbolR A) (symbolR_phaseInv A)) (descend (symbolR B) (symbolR_phaseInv B))
        (proj u) =
      2 * (((p' + 1 : ℕ) : ℝ) * ((1 + q' : ℕ) : ℝ)) *
        (⟪alphaIns (insA p' u.1) A u.1 - ⟪u.1, alphaIns (insA p' u.1) A u.1⟫_ℂ • u.1,
          alphaIns (insB q' u.1) B u.1 - ⟪u.1, alphaIns (insB q' u.1) B u.1⟫_ℂ • u.1⟫_ℂ).im := by
  rw [qbr_eq_pbR (symbolR_phaseInv A) (symbolR_phaseInv B) (descend_proj _ _) (descend_proj _ _) u
    (differentiableAt_symbolR A u.1) (differentiableAt_symbolR B u.1)]
  exact pbR_tangential p' q' hA hB u.1 u.2

end TangentialValue

end Symbols

#print axioms qbr_eq_pbR
#print axioms qbrC_eq_pbC
#print axioms root_overlap_limit_quotient
#print axioms qbr_symbolR_formula
#print axioms qbr_proj_smul
#print axioms kps_circle

end QuantumNLS.PhaseQuotientBracket
