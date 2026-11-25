import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB7
import LiebLiniger.FixedPeriod.Atomic.EXT.FlowRotationB
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Radial equivariance of the actual finite-plane Hamiltonian vector field

Differentiate the already proved phase invariance of the literal Hamiltonian.
The real symplectic pairing identifies the transformed vector field. Polar
coordinates give phase transitivity without division; isotropy handles zeros.
-/

set_option autoImplicit false
noncomputable section
namespace LiebLiniger.FixedPeriod.EXT

/-- At every finite-plane point the differential of the literal Hamiltonian
is twice the real symplectic pairing with its actual Hamiltonian vector field. -/
theorem HLambda_fderiv_Y38 (Λ : Finset ℤ) (w η : Λ → ℂ) :
    fderiv ℝ (HΛ Λ) w η =
      2 * ∑ i : Λ, (starRingEnd ℂ (YΛ Λ w i) * η i).im := by
  have hd := (differentiable_ZΛ38 Λ w 0).hasDerivAt.unique
    (finiteGap_actualODE38 Λ w 0)
  rw [ZΛ_zero38] at hd
  have hh := HΛ_fderiv_actual38 Λ w 0 η
  rw [ZΛ_zero38, hd] at hh
  exact hh

/-- Coordinatewise multiplication by the prescribed complex unit phases,
viewed as a real continuous linear map on the finite complex plane. -/
def finitePlanePhase38 (Λ : Finset ℤ) (θ : Λ → ℝ) : (Λ → ℂ) →L[ℝ] (Λ → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w i => Complex.exp ((θ i : ℂ) * Complex.I) * w i
      map_add' := by intro w v; ext i; exact mul_add _ _ _
      map_smul' := by
        intro a w
        ext i
        simp only [Pi.smul_apply, RingHom.id_apply, Complex.real_smul]
        ring }

/-- Differentiating phase invariance gives the chain-rule identity for every
real tangent, including at points with collapsed coordinates. -/
theorem HLambda_phase_fderiv38 (Λ : Finset ℤ) (θ : Λ → ℝ) (w η : Λ → ℂ) :
    fderiv ℝ (HΛ Λ) (finitePlanePhase38 Λ θ w) (finitePlanePhase38 Λ θ η) =
      fderiv ℝ (HΛ Λ) w η := by
  have hf := (analytic_HLambda38 Λ (finitePlanePhase38 Λ θ w)
    (Set.mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hf.comp w (finitePlanePhase38 Λ θ).hasFDerivAt
  have he : HΛ Λ ∘ finitePlanePhase38 Λ θ = HΛ Λ :=
    funext (fun v => HLambda_phaseInvariant38 Λ v θ)
  rw [he] at hc
  exact congrArg (fun L => L η) (hc.unique
    (analytic_HLambda38 Λ w (Set.mem_univ _)).differentiableAt.hasFDerivAt)

set_option maxHeartbeats 400000 in
/-- The actual finite-plane Hamiltonian vector field intertwines every
coordinate phase rotation. -/
theorem YLambda_phase_equivariant38 (Λ : Finset ℤ) (w : Λ → ℂ) (θ : Λ → ℝ)
    (i : Λ) :
    YΛ Λ (finitePlanePhase38 Λ θ w) i =
      Complex.exp ((θ i : ℂ) * Complex.I) * YΛ Λ w i := by
  classical
  let p : ℂ := Complex.exp ((θ i : ℂ) * Complex.I)
  let a : ℂ := YΛ Λ (finitePlanePhase38 Λ θ w) i
  let b : ℂ := YΛ Λ w i
  have hp (c : ℂ) :
      finitePlanePhase38 Λ θ (Pi.single i c) = Pi.single i (p * c) := by
    ext j
    by_cases hj : j = i
    · subst j; simp [finitePlanePhase38, p]
    · simp [finitePlanePhase38, hj]
  have hs (c : ℂ) : (starRingEnd ℂ a * (p * c)).im =
      (starRingEnd ℂ b * c).im := by
    have hh := HLambda_phase_fderiv38 Λ θ w (Pi.single i c)
    rw [hp, HLambda_fderiv_Y38, HLambda_fderiv_Y38,
      finitePlane_symplectic_single38, finitePlane_symplectic_single38] at hh
    change 2 * (starRingEnd ℂ a * (p * c)).im =
      2 * (starRingEnd ℂ b * c).im at hh
    linarith only [hh]
  have hz : starRingEnd ℂ a * p = starRingEnd ℂ b := by
    apply Complex.ext
    · simpa only [← mul_assoc, Complex.mul_I_im] using hs Complex.I
    · simpa only [mul_one] using hs 1
  have hu : starRingEnd ℂ p * p = 1 := by
    rw [Complex.conj_mul', show ‖p‖ = 1 from Complex.norm_exp_ofReal_mul_I (θ i)]
    norm_num
  have hc := congrArg (starRingEnd ℂ) hz
  simp only [map_mul, starRingEnd_self_apply] at hc
  have he : a = p * b := by
    calc
      a = a * (starRingEnd ℂ p * p) := by rw [hu, mul_one]
      _ = b * p := by rw [← mul_assoc, hc]
      _ = p * b := mul_comm _ _
  exact he

/-- Polar transitivity for equal coordinate norms. The explicit angle
difference works at zero as well, so no quotient of coordinates is used. -/
theorem finitePlane_phase_transitive38 (Λ : Finset ℤ) (w v : Λ → ℂ)
    (h : ∀ i, ‖w i‖ ^ 2 = ‖v i‖ ^ 2) :
    finitePlanePhase38 Λ (fun i => (v i).arg - (w i).arg) w = v := by
  ext i
  have hn : ‖w i‖ = ‖v i‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h i)
  change Complex.exp ((((v i).arg - (w i).arg : ℝ) : ℂ) * Complex.I) * w i = v i
  calc
    _ = Complex.exp ((((v i).arg - (w i).arg : ℝ) : ℂ) * Complex.I) *
        ((‖w i‖ : ℂ) * Complex.exp (((w i).arg : ℂ) * Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖w i‖ : ℂ) * Complex.exp (((v i).arg : ℂ) * Complex.I) := by
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      push_cast
      ring
    _ = v i := by rw [hn, Complex.norm_mul_exp_arg_mul_I]

set_option maxHeartbeats 400000 in
/-- Equal finite-plane actions give the radial cross-multiplication identity;
zero-coordinate isotropy forces zero velocity, and each velocity is tangent
to its action circle. All three assertions include collapsed coordinates. -/
theorem YLambda_radial_equivariant38 :
    ∀ (Λ : Finset ℤ) (w v : Λ → ℂ),
      (∀ i, ‖w i‖ ^ 2 = ‖v i‖ ^ 2) →
      (∀ i, YΛ Λ v i * w i = YΛ Λ w i * v i) ∧
      (∀ i, w i = 0 → YΛ Λ w i = 0) ∧
      (∀ i, (starRingEnd ℂ (w i) * YΛ Λ w i).re = 0) := by
  intro Λ w v h
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have he := YLambda_phase_equivariant38 Λ w
      (fun j => (v j).arg - (w j).arg) i
    rw [finitePlane_phase_transitive38 Λ w v h] at he
    have hv := congrFun (finitePlane_phase_transitive38 Λ w v h) i
    change Complex.exp ((((v i).arg - (w i).arg : ℝ) : ℂ) * Complex.I) * w i = v i at hv
    calc
      YΛ Λ v i * w i =
          (Complex.exp ((((v i).arg - (w i).arg : ℝ) : ℂ) * Complex.I) *
            YΛ Λ w i) * w i := congrArg (fun z : ℂ => z * w i) he
      _ = YΛ Λ w i *
          (Complex.exp ((((v i).arg - (w i).arg : ℝ) : ℂ) * Complex.I) * w i) := by ring
      _ = YΛ Λ w i * v i := congrArg (fun z : ℂ => YΛ Λ w i * z) hv
  · intro i hi
    let θ : Λ → ℝ := fun j => if j = i then Real.pi else 0
    have he : finitePlanePhase38 Λ θ w = w := by
      ext j
      by_cases hj : j = i
      · subst j; simp [finitePlanePhase38, hi]
      · simp [finitePlanePhase38, θ, hj]
    have hh := YLambda_phase_equivariant38 Λ w θ i
    rw [he] at hh
    have hp : Complex.exp ((θ i : ℂ) * Complex.I) = -1 := by
      simpa only [θ, ite_true] using Complex.exp_pi_mul_I
    rw [hp, neg_one_mul] at hh
    have hz : 2 * YΛ Λ w i = 0 := by linear_combination hh
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  · intro i
    have hd := (differentiable_ZΛ38 Λ w 0).hasDerivAt.unique
      (finiteGap_actualODE38 Λ w 0)
    rw [ZΛ_zero38] at hd
    have hh := actual_finitePlane_action_tangent38 Λ w i
    rw [hd] at hh
    linarith only [hh]

end LiebLiniger.FixedPeriod.EXT
