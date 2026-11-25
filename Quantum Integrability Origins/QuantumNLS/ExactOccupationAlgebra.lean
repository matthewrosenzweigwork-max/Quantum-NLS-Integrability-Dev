import QuantumNLS.CartesianOccupationTransfer
import QuantumNLS.SymplecticBracket

/-! R-61E9CD1F. Whole-sector identities for the realized bounded transfers. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.ExactOccupationAlgebra
open OccupationHilbert BetheCoefficientTransform BetheOccupationGauge CartesianOccupationTransfer QuantumFourierSpecification
variable {N : ℕ} {L : ℝ} [Fact (0 < L)]

/-- The normalized count operator in the very same gauged COT1 basis. -/
def count (β : BetheBasis L N) (γ : Gauge) (j : ℤ) : HN L N →L[ℂ] HN L N :=
  physical β γ j j

theorem physical_comm (hN : 0 < N) (β : BetheBasis L N) (γ : Gauge) (a b c d : ℤ) :
    physical β γ a b * physical β γ c d - physical β γ c d * physical β γ a b =
      (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) • physical β γ c b -
        (if b = c then (1 : ℂ) else 0) • physical β γ a d) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply (coordinates β γ).injective
  have h := congrArg (fun A : H N →L[ℂ] H N => A (coordinates β γ ψ)) (E_comm hN a b c d)
  simpa only [sub_apply, mul_apply_eq_comp, smul_apply, map_sub, map_smul,
    physical_coordinates] using h

theorem count_comm (hN : 0 < N) (β : BetheBasis L N) (γ : Gauge) (j a b : ℤ) :
    count β γ j * physical β γ a b - physical β γ a b * count β γ j =
      (((if j = b then (1 : ℂ) else 0) - (if j = a then (1 : ℂ) else 0)) / N) •
        physical β γ a b := by
  apply ContinuousLinearMap.ext
  intro ψ
  have h := congrArg (fun T : HN L N →L[ℂ] HN L N => T ψ) (physical_comm hN β γ j j a b)
  simp only [sub_apply, mul_apply_eq_comp, smul_apply] at h
  simp only [count, sub_apply, mul_apply_eq_comp, smul_apply]
  by_cases hjb : j = b <;> by_cases hja : j = a <;> simp_all [div_eq_mul_inv]

/-- The corresponding coefficient-space count identity, with every coincidence. -/
theorem coefficient_count_comm (hN : 0 < N) (j a b : ℤ) :
    E N j j * E N a b - E N a b * E N j j =
      (((if j = b then (1 : ℂ) else 0) - (if j = a then (1 : ℂ) else 0)) / N) • E N a b := by
  apply ContinuousLinearMap.ext
  intro ψ
  have h := congrArg (fun T : H N →L[ℂ] H N => T ψ) (E_comm hN j j a b)
  simp only [sub_apply, mul_apply_eq_comp, smul_apply] at h ⊢
  by_cases hjb : j = b <;> by_cases hja : j = a <;> simp_all [div_eq_mul_inv]

theorem count_basis (β : BetheBasis L N) (γ : Gauge) (j : ℤ) (m : BetheLabels.MArr N) :
    count β γ j (gaugedBasis β γ m) =
      ((((marrArr N m).1 j : ℝ) / N : ℝ) : ℂ) • gaugedBasis β γ m :=
  physical_diag β γ j m

/-- EXT-001 enters only as the frozen explicit completeness hypothesis. -/
theorem selected_comm (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 0 < N) (a b c d : ℤ) :
    selectedPhysical hcont s L κ hκ N a b * selectedPhysical hcont s L κ hκ N c d -
      selectedPhysical hcont s L κ hκ N c d * selectedPhysical hcont s L κ hκ N a b =
    (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) • selectedPhysical hcont s L κ hκ N c b -
      (if b = c then (1 : ℂ) else 0) • selectedPhysical hcont s L κ hκ N a d) :=
  physical_comm hN _ _ a b c d

theorem meanField_comm (hcont : BetheConditionalBasis.AbstractContinuity) (s : UniversalSelection)
    (L : ℝ) [Fact (0 < L)] (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (a b c d : ℤ) :
    selectedMeanFieldPhysical hcont s L κ hκ N hN a b * selectedMeanFieldPhysical hcont s L κ hκ N hN c d -
      selectedMeanFieldPhysical hcont s L κ hκ N hN c d * selectedMeanFieldPhysical hcont s L κ hκ N hN a b =
    (N : ℂ)⁻¹ • ((if a = d then (1 : ℂ) else 0) • selectedMeanFieldPhysical hcont s L κ hκ N hN c b -
      (if b = c then (1 : ℂ) else 0) • selectedMeanFieldPhysical hcont s L κ hκ N hN a d) :=
  physical_comm (by omega) _ _ a b c d

/-- The source Dirac prefactor N/i, with the classical orientation. -/
theorem scaled_comm (hN : 0 < N) (β : BetheBasis L N) (γ : Gauge) (a b c d : ℤ) :
    ((N : ℂ) / Complex.I) •
      (physical β γ a b * physical β γ c d - physical β γ c d * physical β γ a b) =
    Complex.I • ((if b = c then (1 : ℂ) else 0) • physical β γ a d -
      (if a = d then (1 : ℂ) else 0) • physical β γ c b) := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hc : ((N : ℂ) / Complex.I) * (N : ℂ)⁻¹ = -Complex.I := by
    simp [div_eq_mul_inv, mul_comm, hn]
  rw [physical_comm hN, smul_smul, hc]
  simp only [neg_smul, smul_sub]
  abel

section Quadratic
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
attribute [local instance] InnerProductSpace.complexToReal
open SymplecticBracket

def quadratic (A : V →L[ℂ] V) (u : V) : ℂ := ⟪u, A u⟫_ℂ

omit [CompleteSpace V] in
theorem quadratic_fderiv (A : V →L[ℂ] V) (u h : V) :
    fderiv ℝ (quadratic A) u h = ⟪u, A h⟫_ℂ + ⟪h, A u⟫_ℂ := by
  have hd := (hasFDerivAt_id u).inner ℂ ((A.restrictScalars ℝ).hasFDerivAt)
  exact congrArg (fun f : V →L[ℝ] ℂ => f h) hd.fderiv

theorem gradient_quadratic_re (A : V →L[ℂ] V) (u : V) :
    SymplecticBracket.gradient (fun v => (quadratic A v).re) u = (2 : ℝ)⁻¹ • (A u + A.adjoint u) := by
  apply ext_inner_right ℝ
  intro h
  have hd := (Complex.reCLM.hasFDerivAt.comp u
    ((hasFDerivAt_id u).inner ℂ ((A.restrictScalars ℝ).hasFDerivAt))).fderiv
  have he := congrArg (fun f : V →L[ℝ] ℝ => f h) hd
  rw [fderiv_eq_two_inner_gradient] at he
  change 2 * inner ℝ (SymplecticBracket.gradient (fun v => (quadratic A v).re) u) h =
    (⟪u, A h⟫_ℂ + ⟪h, A u⟫_ℂ).re at he
  rw [real_inner_smul_left]
  simp only [real_inner_eq_re_inner ℂ, RCLike.re_to_complex, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, Complex.add_re] at he ⊢
  have hc := congrArg Complex.re (inner_conj_symm h (A u))
  simp only [Complex.conj_re] at hc
  linarith

theorem gradient_quadratic_im (A : V →L[ℂ] V) (u : V) :
    SymplecticBracket.gradient (fun v => (quadratic A v).im) u =
      (2 : ℝ)⁻¹ • ((-Complex.I) • (A u - A.adjoint u)) := by
  apply ext_inner_right ℝ
  intro h
  have hd := (Complex.imCLM.hasFDerivAt.comp u
    ((hasFDerivAt_id u).inner ℂ ((A.restrictScalars ℝ).hasFDerivAt))).fderiv
  have he := congrArg (fun f : V →L[ℝ] ℝ => f h) hd
  rw [fderiv_eq_two_inner_gradient] at he
  change 2 * inner ℝ (SymplecticBracket.gradient (fun v => (quadratic A v).im) u) h =
    (⟪u, A h⟫_ℂ + ⟪h, A u⟫_ℂ).im at he
  rw [real_inner_smul_left]
  simp only [real_inner_eq_re_inner ℂ, RCLike.re_to_complex, inner_smul_left,
    inner_sub_left, ContinuousLinearMap.adjoint_inner_left] at he ⊢
  have hc := congrArg Complex.im (inner_conj_symm h (A u))
  simp only [Complex.conj_im] at hc
  simp only [Complex.add_im] at he
  simp only [map_neg, Complex.conj_I, neg_neg, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, Complex.sub_im]
  linarith

/-- The actual DEF-015 complex bracket, derived from the Frechet gradients. -/
theorem quadratic_bracket (A B : V →L[ℂ] V) (u : V) :
    pbC (quadratic A) (quadratic B) u =
      -Complex.I * ⟪u, (A * B - B * A) u⟫_ℂ := by
  have hcross : ⟪A u, B.adjoint u⟫_ℂ = conj ⟪u, B (A u)⟫_ℂ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (inner_conj_symm (𝕜 := ℂ) (B (A u)) u).symm
  unfold pbC
  simp only [pbR_eq_omega, gradient_quadratic_re, gradient_quadratic_im, omega,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_left, inner_smul_right,
    inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_left, hcross]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.conj_re, Complex.conj_im] <;> norm_num <;> ring

/-- Orthogonal horizontal representative at unit mass. -/
def horizontal (u v : V) : V := v - ⟪u, v⟫_ℂ • u

omit [CompleteSpace V] in
theorem horizontal_orthogonal (u v : V) (hu : ‖u‖ = 1) :
    ⟪u, horizontal u v⟫_ℂ = 0 := by
  simp [horizontal, inner_self_eq_norm_sq_to_K, hu]

/- Removal of real radial components preserves exactly 2 Im of the pairing. -/
omit [CompleteSpace V] in
theorem horizontal_omega (u v w : V) (hv : (⟪u, v⟫_ℂ).im = 0)
    (hw : (⟪u, w⟫_ℂ).im = 0) :
    omega (horizontal u v) (horizontal u w) = omega v w := by
  have hc : (⟪v, u⟫_ℂ).im = 0 := by
    have ht := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ) u v)
    simp only [Complex.conj_im] at ht
    linarith
  simp only [horizontal, omega, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right]
  simp only [Complex.sub_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, hv, hw, hc]
  ring_nf
  rw [show (⟪u, u⟫_ℂ).im = 0 from inner_self_im (𝕜 := ℂ) u]
  ring

/-- A differentiable real common-phase invariant function has a real radial pairing. -/
theorem invariant_gradient_real (F : V → ℝ) (u : V) (hF : DifferentiableAt ℝ F u)
    (hinv : ∀ θ : ℝ, F (Complex.exp ((θ : ℂ) * Complex.I) • u) = F u) :
    (⟪u, SymplecticBracket.gradient F u⟫_ℂ).im = 0 := by
  have hp : HasDerivAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) • u)
      (Complex.I • u) 0 := by
    have he := (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).cexp.smul_const u)
    convert he using 1 <;> simp

  have hf : HasFDerivAt F (fderiv ℝ F u)
      (Complex.exp (((0 : ℝ) : ℂ) * Complex.I) • u) := by simpa using hF.hasFDerivAt
  have hd := hf.comp_hasDerivAt 0 hp
  have he : fderiv ℝ F u (Complex.I • u) = 0 := by
    have hc : (fun θ : ℝ => F (Complex.exp ((θ : ℂ) * Complex.I) • u)) = fun _ => F u :=
      funext hinv
    have hd' : HasDerivAt (fun θ : ℝ => F (Complex.exp ((θ : ℂ) * Complex.I) • u))
        (fderiv ℝ F u (Complex.I • u)) 0 := by convert hd using 1
                                               rfl
    rw [hc] at hd'
    exact hd'.unique (hasDerivAt_const 0 (F u))
  rw [fderiv_eq_two_inner_gradient, real_inner_eq_re_inner ℂ, inner_smul_right] at he
  have hc := congrArg Complex.im (inner_conj_symm (𝕜 := ℂ) u
    (SymplecticBracket.gradient F u))
  simp only [Complex.conj_im] at hc
  simp only [RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at he
  linarith

/-- Source reduction formula: the DEF-015 bracket equals the pairing of the
horizontal gradients, with no multiplier, at every unit-mass representative. -/
theorem reduced_bracket (F G : V → ℝ) (u : V) (hu : ‖u‖ = 1)
    (hF : DifferentiableAt ℝ F u) (hG : DifferentiableAt ℝ G u)
    (hFi : ∀ θ : ℝ, F (Complex.exp ((θ : ℂ) * Complex.I) • u) = F u)
    (hGi : ∀ θ : ℝ, G (Complex.exp ((θ : ℂ) * Complex.I) • u) = G u) :
    ⟪u, horizontal u (SymplecticBracket.gradient F u)⟫_ℂ = 0 ∧
    ⟪u, horizontal u (SymplecticBracket.gradient G u)⟫_ℂ = 0 ∧
    pbR F G u = omega (horizontal u (SymplecticBracket.gradient F u))
      (horizontal u (SymplecticBracket.gradient G u)) := by
  refine ⟨horizontal_orthogonal _ _ hu, horizontal_orthogonal _ _ hu, ?_⟩
  rw [horizontal_omega _ _ _ (invariant_gradient_real F u hF hFi)
    (invariant_gradient_real G u hG hGi), pbR_eq_omega]

/-- Common-phase invariance on the full Hilbert space, for real observables. -/
def PhaseInvariant (F : V → ℝ) : Prop := ∀ (z : ℂ), ‖z‖ = 1 → ∀ u, F (z • u) = F u

theorem unit_mul_conj (z : ℂ) (hz : ‖z‖ = 1) : z * conj z = 1 := by
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]

/-- Covariance of the actual Frechet gradient under the common phase. -/
theorem phase_gradient (F : V → ℝ) (hF : Differentiable ℝ F) (hi : PhaseInvariant F)
    (z : ℂ) (hz : ‖z‖ = 1) (u : V) :
    SymplecticBracket.gradient F (z • u) = z • SymplecticBracket.gradient F u := by
  let S : V →L[ℝ] V := (z • (ContinuousLinearMap.id ℂ V)).restrictScalars ℝ
  have heq : F ∘ (fun v : V => z • v) = F := funext (hi z hz)
  have hd := (hF (z • u)).hasFDerivAt.comp u S.hasFDerivAt
  rw [heq] at hd
  apply ext_inner_right ℝ
  intro v
  have he := congrArg (fun T : V →L[ℝ] ℝ => T (conj z • v)) hd.fderiv
  change fderiv ℝ F u (conj z • v) = fderiv ℝ F (z • u) (z • (conj z • v)) at he
  rw [smul_smul, unit_mul_conj z hz, one_smul] at he
  rw [fderiv_eq_two_inner_gradient, fderiv_eq_two_inner_gradient] at he
  simp only [real_inner_eq_re_inner ℂ, RCLike.re_to_complex, inner_smul_right,
    inner_smul_left] at he ⊢
  nlinarith

theorem phase_bracket (F G : V → ℝ) (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hiF : PhaseInvariant F) (hiG : PhaseInvariant G) (z : ℂ) (hz : ‖z‖ = 1) (u : V) :
    pbR F G (z • u) = pbR F G u := by
  rw [pbR_eq_omega, pbR_eq_omega, phase_gradient F hF hiF z hz,
    phase_gradient G hG hiG z hz]
  simp only [omega, inner_smul_left, inner_smul_right, ← mul_assoc,
    unit_mul_conj z hz, one_mul]

/-- Actual unit-mass sphere modulo the common unit phase. -/
def phaseSetoid (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V] :
    Setoid {u : V // ‖u‖ = 1} where
  r u v := ∃ z : ℂ, ‖z‖ = 1 ∧ v.1 = z • u.1
  iseqv := {
    refl := fun u => ⟨1, norm_one, by simp⟩
    symm := by
      intro u v h
      rcases h with ⟨z, hz, he⟩
      refine ⟨conj z, by simpa using hz, ?_⟩
      rw [he, smul_smul, mul_comm, unit_mul_conj z hz, one_smul]
    trans := by
      intro u v w h1 h2
      rcases h1 with ⟨z1, hz1, he1⟩
      rcases h2 with ⟨z2, hz2, he2⟩
      refine ⟨z2 * z1, by rw [norm_mul, hz1, hz2, one_mul], ?_⟩
      rw [he2, he1, smul_smul] }

/-- The bracket is well defined on the common-phase quotient, with no rescaling. -/
def quotientBracket (F G : V → ℝ) (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hiF : PhaseInvariant F) (hiG : PhaseInvariant G) : Quotient (phaseSetoid V) → ℝ :=
  Quotient.lift (fun u => pbR F G u.1) (by
    intro u v h
    rcases h with ⟨z, hz, he⟩
    rw [he, phase_bracket F G hF hG hiF hiG z hz])

theorem quotientBracket_mk (F G : V → ℝ) (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hiF : PhaseInvariant F) (hiG : PhaseInvariant G) (u : {u : V // ‖u‖ = 1}) :
    quotientBracket F G hF hG hiF hiG (Quotient.mk (phaseSetoid V) u) = pbR F G u.1 := rfl

/-- The descended bracket is precisely the horizontal bracket at mass one. -/
theorem quotient_horizontal (F G : V → ℝ) (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hiF : PhaseInvariant F) (hiG : PhaseInvariant G) (u : {u : V // ‖u‖ = 1}) :
    quotientBracket F G hF hG hiF hiG (Quotient.mk (phaseSetoid V) u) =
      omega (horizontal u.1 (SymplecticBracket.gradient F u.1))
        (horizontal u.1 (SymplecticBracket.gradient G u.1)) := by
  rw [quotientBracket_mk]
  exact (reduced_bracket F G u.1 u.2 (hF _) (hG _)
    (fun θ => hiF _ (Complex.norm_exp_ofReal_mul_I θ) u.1)
    (fun θ => hiG _ (Complex.norm_exp_ofReal_mul_I θ) u.1)).2.2

end Quadratic

open OccupationUnitary OccupationConjugacy

/-- Literal Cartesian coordinate symbol on the realized one-particle ell² space. -/
def cartesian (a b : ℤ) (u : OneParticle) : ℂ := u a * conj (u b)

theorem quadratic_matrixUnit (a b : ℤ) : quadratic (matrixUnit a b) = cartesian a b := by
  funext u
  simp only [quadratic, matrixUnit, InnerProductSpace.rankOne_apply, inner_smul_right,
    oneBasis_apply, lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    map_one, one_mul, mul_one, cartesian]

theorem matrixUnit_product (a b c d : ℤ) :
    matrixUnit a b * matrixUnit c d = (if a = d then (1 : ℂ) else 0) • matrixUnit c b := by
  change InnerProductSpace.rankOne ℂ (oneBasis b) (oneBasis a) ∘L
    InnerProductSpace.rankOne ℂ (oneBasis d) (oneBasis c) = _
  rw [InnerProductSpace.rankOne_comp_rankOne,
    orthonormal_iff_ite.mp oneBasis.orthonormal]
  rfl

theorem matrixUnit_comm (a b c d : ℤ) :
    matrixUnit a b * matrixUnit c d - matrixUnit c d * matrixUnit a b =
      (if a = d then (1 : ℂ) else 0) • matrixUnit c b -
        (if b = c then (1 : ℂ) else 0) • matrixUnit a d := by
  rw [matrixUnit_product, matrixUnit_product]
  simp only [eq_comm]

/-- The classical equation, valid on all Cartesian coordinates, including zero actions. -/
theorem cartesian_bracket (a b c d : ℤ) (u : OneParticle) :
    SymplecticBracket.pbC (cartesian a b) (cartesian c d) u =
      Complex.I * ((if b = c then (1 : ℂ) else 0) * cartesian a d u -
        (if a = d then (1 : ℂ) else 0) * cartesian c b u) := by
  rw [← quadratic_matrixUnit, ← quadratic_matrixUnit, quadratic_bracket, matrixUnit_comm]
  simp only [sub_apply, smul_apply, inner_sub_right, inner_smul_right]
  change -Complex.I * (_ * quadratic (matrixUnit c b) u - _ * quadratic (matrixUnit a d) u) = _
  rw [quadratic_matrixUnit, quadratic_matrixUnit]
  ring

def action (j : ℤ) (u : OneParticle) : ℝ := ‖u j‖ ^ 2

theorem cartesian_diag (j : ℤ) (u : OneParticle) : cartesian j j u = (action j u : ℂ) := by
  simp [cartesian, action, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem action_bracket (j a b : ℤ) (u : OneParticle) :
    SymplecticBracket.pbC (fun v => (action j v : ℂ)) (cartesian a b) u =
      Complex.I * ((if j = a then (1 : ℂ) else 0) -
        (if j = b then (1 : ℂ) else 0)) * cartesian a b u := by
  have he : (fun v => (action j v : ℂ)) = cartesian j j := funext (cartesian_diag j · |>.symm)
  rw [he, cartesian_bracket]
  by_cases hja : j = a <;> by_cases hjb : j = b <;> simp_all [eq_comm]

theorem conjugate_cartesian (a b : ℤ) :
    (fun u => conj (cartesian a b u)) = cartesian b a := by
  funext u; simp [cartesian, mul_comm]

/-- The pair formula includes every zero endpoint and requires no polar quotient. -/
theorem pair_bracket (a b : ℤ) (u : OneParticle) :
    SymplecticBracket.pbC (cartesian a b) (fun v => conj (cartesian a b v)) u =
      Complex.I * ((action a u : ℂ) - (action b u : ℂ)) := by
  rw [conjugate_cartesian, cartesian_bracket]
  simp [cartesian_diag]

/-- Literal identification with the frozen COT1 coordinate symbol. -/
theorem cartesian_COT1 (w : PhysicalField L → Coordinates) (a b : ℤ) (u : PhysicalField L) :
    cartesian a b (w u) = symbol w a b u := rfl

end QuantumNLS.ExactOccupationAlgebra

#print axioms QuantumNLS.ExactOccupationAlgebra.count
#print axioms QuantumNLS.ExactOccupationAlgebra.physical_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.count_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.coefficient_count_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.count_basis
#print axioms QuantumNLS.ExactOccupationAlgebra.selected_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.meanField_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.scaled_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.quadratic
#print axioms QuantumNLS.ExactOccupationAlgebra.quadratic_fderiv
#print axioms QuantumNLS.ExactOccupationAlgebra.gradient_quadratic_re
#print axioms QuantumNLS.ExactOccupationAlgebra.gradient_quadratic_im
#print axioms QuantumNLS.ExactOccupationAlgebra.quadratic_bracket
#print axioms QuantumNLS.ExactOccupationAlgebra.horizontal
#print axioms QuantumNLS.ExactOccupationAlgebra.horizontal_orthogonal
#print axioms QuantumNLS.ExactOccupationAlgebra.horizontal_omega
#print axioms QuantumNLS.ExactOccupationAlgebra.invariant_gradient_real
#print axioms QuantumNLS.ExactOccupationAlgebra.reduced_bracket
#print axioms QuantumNLS.ExactOccupationAlgebra.PhaseInvariant
#print axioms QuantumNLS.ExactOccupationAlgebra.unit_mul_conj
#print axioms QuantumNLS.ExactOccupationAlgebra.phase_gradient
#print axioms QuantumNLS.ExactOccupationAlgebra.phase_bracket
#print axioms QuantumNLS.ExactOccupationAlgebra.phaseSetoid
#print axioms QuantumNLS.ExactOccupationAlgebra.quotientBracket
#print axioms QuantumNLS.ExactOccupationAlgebra.quotientBracket_mk
#print axioms QuantumNLS.ExactOccupationAlgebra.quotient_horizontal
#print axioms QuantumNLS.ExactOccupationAlgebra.cartesian
#print axioms QuantumNLS.ExactOccupationAlgebra.quadratic_matrixUnit
#print axioms QuantumNLS.ExactOccupationAlgebra.matrixUnit_product
#print axioms QuantumNLS.ExactOccupationAlgebra.matrixUnit_comm
#print axioms QuantumNLS.ExactOccupationAlgebra.cartesian_bracket
#print axioms QuantumNLS.ExactOccupationAlgebra.action
#print axioms QuantumNLS.ExactOccupationAlgebra.cartesian_diag
#print axioms QuantumNLS.ExactOccupationAlgebra.action_bracket
#print axioms QuantumNLS.ExactOccupationAlgebra.conjugate_cartesian
#print axioms QuantumNLS.ExactOccupationAlgebra.pair_bracket
#print axioms QuantumNLS.ExactOccupationAlgebra.cartesian_COT1

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending := #[``QuantumNLS.ExactOccupationAlgebra.count,
    ``QuantumNLS.ExactOccupationAlgebra.physical_comm,
    ``QuantumNLS.ExactOccupationAlgebra.count_comm,
    ``QuantumNLS.ExactOccupationAlgebra.coefficient_count_comm,
    ``QuantumNLS.ExactOccupationAlgebra.count_basis,
    ``QuantumNLS.ExactOccupationAlgebra.selected_comm,
    ``QuantumNLS.ExactOccupationAlgebra.meanField_comm,
    ``QuantumNLS.ExactOccupationAlgebra.scaled_comm,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic_fderiv,
    ``QuantumNLS.ExactOccupationAlgebra.gradient_quadratic_re,
    ``QuantumNLS.ExactOccupationAlgebra.gradient_quadratic_im,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.horizontal,
    ``QuantumNLS.ExactOccupationAlgebra.horizontal_orthogonal,
    ``QuantumNLS.ExactOccupationAlgebra.horizontal_omega,
    ``QuantumNLS.ExactOccupationAlgebra.invariant_gradient_real,
    ``QuantumNLS.ExactOccupationAlgebra.reduced_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.PhaseInvariant,
    ``QuantumNLS.ExactOccupationAlgebra.unit_mul_conj,
    ``QuantumNLS.ExactOccupationAlgebra.phase_gradient,
    ``QuantumNLS.ExactOccupationAlgebra.phase_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.phaseSetoid,
    ``QuantumNLS.ExactOccupationAlgebra.quotientBracket,
    ``QuantumNLS.ExactOccupationAlgebra.quotientBracket_mk,
    ``QuantumNLS.ExactOccupationAlgebra.quotient_horizontal,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic_matrixUnit,
    ``QuantumNLS.ExactOccupationAlgebra.matrixUnit_product,
    ``QuantumNLS.ExactOccupationAlgebra.matrixUnit_comm,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.action,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian_diag,
    ``QuantumNLS.ExactOccupationAlgebra.action_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.conjugate_cartesian,
    ``QuantumNLS.ExactOccupationAlgebra.pair_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian_COT1]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ExactOccupationAlgebra." then
      pending := pending.push n
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Result nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
  let mut todo := #[``QuantumNLS.ExactOccupationAlgebra.count,
    ``QuantumNLS.ExactOccupationAlgebra.physical_comm,
    ``QuantumNLS.ExactOccupationAlgebra.count_comm,
    ``QuantumNLS.ExactOccupationAlgebra.coefficient_count_comm,
    ``QuantumNLS.ExactOccupationAlgebra.count_basis,
    ``QuantumNLS.ExactOccupationAlgebra.scaled_comm,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic_fderiv,
    ``QuantumNLS.ExactOccupationAlgebra.gradient_quadratic_re,
    ``QuantumNLS.ExactOccupationAlgebra.gradient_quadratic_im,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.horizontal,
    ``QuantumNLS.ExactOccupationAlgebra.horizontal_orthogonal,
    ``QuantumNLS.ExactOccupationAlgebra.horizontal_omega,
    ``QuantumNLS.ExactOccupationAlgebra.invariant_gradient_real,
    ``QuantumNLS.ExactOccupationAlgebra.reduced_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.PhaseInvariant,
    ``QuantumNLS.ExactOccupationAlgebra.unit_mul_conj,
    ``QuantumNLS.ExactOccupationAlgebra.phase_gradient,
    ``QuantumNLS.ExactOccupationAlgebra.phase_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.phaseSetoid,
    ``QuantumNLS.ExactOccupationAlgebra.quotientBracket,
    ``QuantumNLS.ExactOccupationAlgebra.quotientBracket_mk,
    ``QuantumNLS.ExactOccupationAlgebra.quotient_horizontal,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian,
    ``QuantumNLS.ExactOccupationAlgebra.quadratic_matrixUnit,
    ``QuantumNLS.ExactOccupationAlgebra.matrixUnit_product,
    ``QuantumNLS.ExactOccupationAlgebra.matrixUnit_comm,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.action,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian_diag,
    ``QuantumNLS.ExactOccupationAlgebra.action_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.conjugate_cartesian,
    ``QuantumNLS.ExactOccupationAlgebra.pair_bracket,
    ``QuantumNLS.ExactOccupationAlgebra.cartesian_COT1]
  let mut checked : Std.HashSet Lean.Name := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless checked.contains n do
      checked := checked.insert n
      if n == ``QuantumNLS.BetheConditionalBasis.AbstractContinuity then
        throwError "Generic definition reached EXT-001 premise: {n}"
      if let some ci := env.find? n then
        todo := todo ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          todo := todo ++ v.getUsedConstants
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; {checked.size} generic constants independent of EXT-001. Concrete instantiations require its explicit Prop hypothesis only."
