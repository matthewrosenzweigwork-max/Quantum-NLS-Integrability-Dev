import NlsGge.Atomic.LIB.LIB080
import NlsGge.GK38.Lib.PoissonH0

/-!
# Jacobi identity for a constant skew Poisson tensor

The bracket is defined on the actual continuous dual by evaluation of `J (Dg)` against `Df`.
Its derivative is obtained from Mathlib's bounded bilinear product rule; the Jacobi identity then
cancels the six Hessian terms using skewness and symmetry of the second Fréchet derivative.
The final section identifies the real `h⁰` tensor with the existing NLS bracket, including its
minus sign in the Hamiltonian vector field.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.LIB

open scoped InnerProductSpace

/-- A continuous constant map from the continuous dual to the phase space. -/
def IsSkewDualMap {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) : Prop :=
  ∀ α β : E →L[𝕜] 𝕜, α (J β) = -β (J α)

/-- The bounded bilinear evaluation `B(α,β)=α(J β)` associated with `J`. -/
def constantPoissonBilinear {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) :
    (E →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜) →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.apply 𝕜 (Fₗ := 𝕜)).comp J |>.flip

/-- Constant Poisson bracket `{f,g}(x)=Df(x)(J(Dg(x)))`. -/
def constantPoisson {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) (f g : E → 𝕜) : E → 𝕜 :=
  fun x => (constantPoissonBilinear J) (fderiv 𝕜 f x) (fderiv 𝕜 g x)

@[simp] theorem constantPoisson_apply {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) (f g : E → 𝕜) (x : E) :
    constantPoisson J f g x = fderiv 𝕜 f x (J (fderiv 𝕜 g x)) := by
  simp [constantPoisson, constantPoissonBilinear, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-- Differentiating the bracket yields precisely its two product-rule Hessian terms. -/
theorem fderiv_constantPoisson {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) (f g : E → 𝕜)
    (hf : ContDiff 𝕜 2 f) (hg : ContDiff 𝕜 2 g) (x v : E) :
    fderiv 𝕜 (constantPoisson J f g) x v =
      fderiv 𝕜 (fderiv 𝕜 f) x v (J (fderiv 𝕜 g x)) +
      fderiv 𝕜 f x (J (fderiv 𝕜 (fderiv 𝕜 g) x v)) := by
  let B := constantPoissonBilinear J
  have hfc : ContDiff 𝕜 1 (fderiv 𝕜 f) := by
    have hf' : ContDiff 𝕜 (1 + 1) f := by convert hf using 1; norm_num
    exact (contDiff_succ_iff_fderiv.mp hf').2.2
  have hgc : ContDiff 𝕜 1 (fderiv 𝕜 g) := by
    have hg' : ContDiff 𝕜 (1 + 1) g := by convert hg using 1; norm_num
    exact (contDiff_succ_iff_fderiv.mp hg').2.2
  have hfd : DifferentiableAt 𝕜 (fderiv 𝕜 f) x := (hfc.differentiable (by norm_num)) x
  have hgd : DifferentiableAt 𝕜 (fderiv 𝕜 g) x := (hgc.differentiable (by norm_num)) x
  have hderiv := ContinuousLinearMap.fderiv_of_bilinear B hfd hgd
  have h := congrArg (fun L : E →L[𝕜] 𝕜 => L v) hderiv
  change fderiv 𝕜 (fun y => B (fderiv 𝕜 f y) (fderiv 𝕜 g y)) x v = _
  simpa [B, constantPoissonBilinear, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, add_comm] using h


/-- The constant skew Poisson bracket satisfies the cyclic Jacobi identity. -/
theorem constantPoisson_jacobi {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (J : (E →L[𝕜] 𝕜) →L[𝕜] E) (hJ : IsSkewDualMap J)
    (f g h : E → 𝕜) (hf : ContDiff 𝕜 2 f) (hg : ContDiff 𝕜 2 g)
    (hh : ContDiff 𝕜 2 h) (x : E) :
    constantPoisson J (constantPoisson J f g) h x +
      constantPoisson J (constantPoisson J g h) f x +
      constantPoisson J (constantPoisson J h f) g x = 0 := by
  have hexpand (p q r : E → 𝕜) (hp : ContDiff 𝕜 2 p) (hq : ContDiff 𝕜 2 q) :
      constantPoisson J (constantPoisson J p q) r x =
        fderiv 𝕜 (fderiv 𝕜 p) x (J (fderiv 𝕜 r x)) (J (fderiv 𝕜 q x)) -
          fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)) (J (fderiv 𝕜 p x)) := by
    change fderiv 𝕜 (constantPoisson J p q) x (J (fderiv 𝕜 r x)) = _
    rw [fderiv_constantPoisson J p q hp hq]
    have hskew := hJ (fderiv 𝕜 p x)
      (fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)))
    have hskew' : fderiv 𝕜 p x
        (J (fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)))) =
        -fderiv 𝕜 (fderiv 𝕜 q) x (J (fderiv 𝕜 r x)) (J (fderiv 𝕜 p x)) := by
      simpa only [ContinuousLinearMap.apply_apply] using hskew
    rw [hskew']
    ring
  rw [hexpand f g h hf hg, hexpand g h f hg hh, hexpand h f g hh hf]
  have hfs := NlsGge.Atomic.LIB.secondFrechetDeriv_swap f x
    (J (fderiv 𝕜 h x)) (J (fderiv 𝕜 g x)) (hf.contDiffAt)
  have hgs := NlsGge.Atomic.LIB.secondFrechetDeriv_swap g x
    (J (fderiv 𝕜 f x)) (J (fderiv 𝕜 h x)) (hg.contDiffAt)
  have hhs := NlsGge.Atomic.LIB.secondFrechetDeriv_swap h x
    (J (fderiv 𝕜 g x)) (J (fderiv 𝕜 f x)) (hh.contDiffAt)
  rw [hfs, hgs, hhs]
  ring

/-- The dual-to-phase-space tensor for the NLS real `h⁰` carrier. Its minus sign is the
Hamiltonian vector field convention `X_G=-J∇G` used by `poissonH0`. -/
def JdualH0 : (NlsGge.GK38.Lib.H0Space38 →L[ℝ] ℝ) →L[ℝ] NlsGge.GK38.Lib.H0Space38 :=
  -(NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ)).comp
    (InnerProductSpace.toDual ℝ NlsGge.GK38.Lib.H0Space38).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem riesz_symm_eq_gradH0 (F : NlsGge.GK38.Lib.H0Space38 → ℝ)
    (x : NlsGge.GK38.Lib.H0Space38) :
    (InnerProductSpace.toDual ℝ NlsGge.GK38.Lib.H0Space38).symm (fderiv ℝ F x) =
      NlsGge.GK38.Lib.gradH0 F x := by
  apply ext_inner_right ℝ
  intro v
  rw [InnerProductSpace.toDual_symm_apply, NlsGge.GK38.Lib.inner_gradH0]

theorem isSkewDualMap_JdualH0 : IsSkewDualMap JdualH0 := by
  intro α β
  let R : (NlsGge.GK38.Lib.H0Space38 →L[ℝ] ℝ) → NlsGge.GK38.Lib.H0Space38 :=
    (InnerProductSpace.toDual ℝ NlsGge.GK38.Lib.H0Space38).symm
  have hα : α (NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R β)) =
      ⟪R α, NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R β)⟫_ℝ :=
    (InnerProductSpace.toDual_symm_apply (x := NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R β))
      (y := α)).symm
  have hβ : β (NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α)) =
      ⟪R β, NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α)⟫_ℝ :=
    (InnerProductSpace.toDual_symm_apply (x := NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α))
      (y := β)).symm
  change α (-(NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R β))) =
    -β (-(NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α)))
  rw [map_neg, map_neg, hα, hβ]
  calc
    -⟪R α, NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R β)⟫_ℝ =
        ⟪NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α), R β⟫_ℝ := by
      rw [NlsGge.Birkhoff.inner_J38_left]
    _ = ⟪R β, NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α)⟫_ℝ := real_inner_comm _ _
    _ = -(-⟪R β, NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (R α)⟫_ℝ) := by ring

/-- The abstract bracket with `JdualH0` is exactly the existing, sign-fixed NLS `poissonH0`;
this uses the project Riesz-gradient identity for its actual Fréchet derivative. -/
theorem constantPoisson_JdualH0_eq_poissonH0
    (F G : NlsGge.GK38.Lib.H0Space38 → ℝ)
    (x : NlsGge.GK38.Lib.H0Space38) :
    constantPoisson JdualH0 F G x = NlsGge.GK38.Lib.poissonH0 F G x := by
  rw [constantPoisson_apply]
  change fderiv ℝ F x (-(NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ)
    ((InnerProductSpace.toDual ℝ NlsGge.GK38.Lib.H0Space38).symm (fderiv ℝ G x)))) = _
  rw [riesz_symm_eq_gradH0 G x, ← NlsGge.GK38.Lib.inner_gradH0 F x]
  calc
    ⟪NlsGge.GK38.Lib.gradH0 F x,
      -(NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (NlsGge.GK38.Lib.gradH0 G x))⟫_ℝ =
        ⟪NlsGge.Birkhoff.J38 ((0 : ℕ) : ℝ) (NlsGge.GK38.Lib.gradH0 F x),
          NlsGge.GK38.Lib.gradH0 G x⟫_ℝ := by
      rw [inner_neg_right, NlsGge.Birkhoff.inner_J38_left]
    _ = NlsGge.GK38.Lib.poissonH0 F G x :=
      (NlsGge.GK38.Lib.poissonH0_eq_inner F G x).symm

/-- The actual NLS `h⁰` Poisson bracket satisfies Jacobi with the same real C² hypotheses. -/
theorem poissonH0_jacobi (F G H : NlsGge.GK38.Lib.H0Space38 → ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 2 G) (hH : ContDiff ℝ 2 H)
    (x : NlsGge.GK38.Lib.H0Space38) :
    NlsGge.GK38.Lib.poissonH0 (NlsGge.GK38.Lib.poissonH0 F G) H x +
      NlsGge.GK38.Lib.poissonH0 (NlsGge.GK38.Lib.poissonH0 G H) F x +
      NlsGge.GK38.Lib.poissonH0 (NlsGge.GK38.Lib.poissonH0 H F) G x = 0 := by
  have hfg : constantPoisson JdualH0 F G = NlsGge.GK38.Lib.poissonH0 F G := by
    funext y
    exact constantPoisson_JdualH0_eq_poissonH0 F G y
  have hgh : constantPoisson JdualH0 G H = NlsGge.GK38.Lib.poissonH0 G H := by
    funext y
    exact constantPoisson_JdualH0_eq_poissonH0 G H y
  have hhf : constantPoisson JdualH0 H F = NlsGge.GK38.Lib.poissonH0 H F := by
    funext y
    exact constantPoisson_JdualH0_eq_poissonH0 H F y
  have hOuterFG : constantPoisson JdualH0 (NlsGge.GK38.Lib.poissonH0 F G) H =
      NlsGge.GK38.Lib.poissonH0 (NlsGge.GK38.Lib.poissonH0 F G) H := by
    funext y
    exact constantPoisson_JdualH0_eq_poissonH0 _ _ y
  have hOuterGH : constantPoisson JdualH0 (NlsGge.GK38.Lib.poissonH0 G H) F =
      NlsGge.GK38.Lib.poissonH0 (NlsGge.GK38.Lib.poissonH0 G H) F := by
    funext y
    exact constantPoisson_JdualH0_eq_poissonH0 _ _ y
  have hOuterHF : constantPoisson JdualH0 (NlsGge.GK38.Lib.poissonH0 H F) G =
      NlsGge.GK38.Lib.poissonH0 (NlsGge.GK38.Lib.poissonH0 H F) G := by
    funext y
    exact constantPoisson_JdualH0_eq_poissonH0 _ _ y
  simpa only [hfg, hgh, hhf, hOuterFG, hOuterGH, hOuterHF] using
    constantPoisson_jacobi JdualH0 isSkewDualMap_JdualH0 F G H hF hG hH x

end NlsGge.Atomic.LIB
