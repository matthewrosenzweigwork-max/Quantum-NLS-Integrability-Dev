import NlsGge.Birkhoff.F01Determinant38

/-! # L6: the Poisson bracket of `C¹` functionals on `h⁰` and its invariance

Piece L6 of the E01 plan (`campaign/E01_PLAN.md` §6.1, conventions §8).

## Sign convention (fixed here, checked against the sources)

`ω = stdSymplectic38`, `ω(ξ,η) = Σ_n Im(conj ξ_n · η_n)`, i.e. `ω = Σ dq_n ∧ dp_n` for
`ξ_n = q_n + i p_n`; on `h⁰`, `ω(ξ,η) = ⟪J ξ, η⟫` (`stdSymplectic38_eq_inner`).

Hamiltonian vector field of `H`: the unique `X_H` with `ω(X_H, ·) = dH`
(GK book, Appendix B, "Symplectic manifolds": `υ(X_H,·) = dH`); here `X_H = -J ∇H`.
Bracket: `{F,G} = ω(X_F, X_G) = ⟨dF, X_G⟩` (loc. cit.), `Ḟ = {F,H}` along `ż = X_H(z)`.
Since `ω(J a, J b) = ω(a, b)` this is
`{F,G}(x) = ω(J ∇F(x), J ∇G(x)) = ω(∇F(x), ∇G(x)) = ⟪J ∇F(x), ∇G(x)⟫`, which is the plan's
`poissonH0` (`stdSymplectic38 (J∇F) (J∇G)`).

Consequences (all proved below): `{Re x_n, Im x_n} = +1` (probe `poissonH0_re_im`); for
`H = ½|x_n|²` the Hamilton equation is `ż_n = -i z_n` (`hamField_halfSq`), which is the sign
of the NLS flow normalization of regression T4 (`single k a ↦ e^{-it((2πk)²+2|a|²)} a`),
and `{Re x_n, ½|x_n|²} = Im x_n` (`poissonH0_re_halfSq`).  The same sign: GK book, Appendix B,
the `ℝ^{2n}` example `{F,G} = F_q·G_p - F_p·G_q` with `υ = Σ dq∧dp`.

Remark on the sources (reported to the integrator): the printed GK book has `{G,H} = -i∫[∂G,∂H]`
(§8, Overview) and `{x_m, y_n} = -δ_{mn}` (Thm 18.8) for the real Birkhoff coordinates, because
`z_n = (x_n - i y_n)/√2` (reflected sign); `ω_std` here is in the coordinates `z_n = q_n + i p_n`
(the Lean carrier), where the bracket of `(Re z_n, Im z_n)` is `+1`.  Only the constant forms
`ω_std`, `ω_phys` enter Lean (plan §8).
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.GK38.Lib

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped InnerProductSpace

/-- The phase space `h⁰` (real Hilbert carrier). -/
abbrev H0Space38 : Type := SobolevCarrier38 ((0 : ℕ) : ℝ)

/-- Real gradient on `h⁰` (Riesz representative of the Fréchet derivative; `0` if `F` is not
differentiable at `x`). -/
def gradH0 (F : H0Space38 → ℝ) (x : H0Space38) : H0Space38 := gradient F x

/-- `J ∇F`, where `J` is multiplication by `i`. -/
def JgradH0 (F : H0Space38 → ℝ) (x : H0Space38) : H0Space38 := J38 _ (gradH0 F x)

/-- The Poisson bracket `{F,G}(x) = ω_std(J∇F(x), J∇G(x))` of two functionals on `h⁰`;
the sign convention is `{F,G} = ω(X_F, X_G) = dF(X_G)` (GK Appendix B), see the file header. -/
def poissonH0 (F G : H0Space38 → ℝ) (x : H0Space38) : ℝ :=
  stdSymplectic38 (carrierCoe38 _ (JgradH0 F x)) (carrierCoe38 _ (JgradH0 G x))

/-- The Hamiltonian vector field `X_G = -J ∇G`, the solution of `ω(X_G, ·) = dG`. -/
def hamFieldH0 (G : H0Space38 → ℝ) (x : H0Space38) : H0Space38 := -(JgradH0 G x)

/-! ## Basic identities -/

theorem inner_gradH0 (F : H0Space38 → ℝ) (x v : H0Space38) :
    ⟪gradH0 F x, v⟫_ℝ = fderiv ℝ F x v := inner_gradient_left

theorem stdSymplectic38_coe_eq (a b : H0Space38) :
    stdSymplectic38 (carrierCoe38 _ a) (carrierCoe38 _ b) = ⟪J38 _ a, b⟫_ℝ :=
  stdSymplectic38_eq_inner a b

theorem stdSymplectic38_J_J (a b : H0Space38) :
    stdSymplectic38 (carrierCoe38 _ (J38 _ a)) (carrierCoe38 _ (J38 _ b)) =
      stdSymplectic38 (carrierCoe38 _ a) (carrierCoe38 _ b) := by
  rw [stdSymplectic38_coe_eq, stdSymplectic38_coe_eq, J38_J38, inner_neg_left, inner_J38_left]


theorem poissonH0_eq_inner (F G : H0Space38 → ℝ) (x : H0Space38) :
    poissonH0 F G x = ⟪J38 _ (gradH0 F x), gradH0 G x⟫_ℝ := by
  unfold poissonH0 JgradH0
  rw [stdSymplectic38_J_J, stdSymplectic38_coe_eq]

/-- Appendix B of the GK book: `{F,G} = ⟨dF, X_G⟩`. -/
theorem poissonH0_eq_fderiv_hamField (F G : H0Space38 → ℝ) (x : H0Space38) :
    poissonH0 F G x = fderiv ℝ F x (hamFieldH0 G x) := by
  rw [poissonH0_eq_inner, ← inner_gradH0, hamFieldH0, JgradH0, inner_neg_right, inner_J38_left]

/-- Appendix B of the GK book: `υ(X_G, ·) = dG`. -/
theorem stdSymplectic38_hamField (G : H0Space38 → ℝ) (x η : H0Space38) :
    stdSymplectic38 (carrierCoe38 _ (hamFieldH0 G x)) (carrierCoe38 _ η) = fderiv ℝ G x η := by
  rw [stdSymplectic38_coe_eq, ← inner_gradH0, hamFieldH0, JgradH0, map_neg, J38_J38, neg_neg]

theorem poissonH0_antisymm (F G : H0Space38 → ℝ) (x : H0Space38) :
    poissonH0 G F x = -poissonH0 F G x := by
  rw [poissonH0_eq_inner, poissonH0_eq_inner, inner_J38_left, real_inner_comm]

theorem poissonH0_self (F : H0Space38 → ℝ) (x : H0Space38) : poissonH0 F F x = 0 := by
  have := poissonH0_antisymm F F x
  linarith

/-- Along `γ' = X_H(γ)`, `Ḟ = {F,H}` (GK Appendix B). -/
theorem hasDerivAt_comp_hamField {F H : H0Space38 → ℝ} {γ : ℝ → H0Space38} {t : ℝ}
    (hγ : HasDerivAt γ (hamFieldH0 H (γ t)) t) (hF : DifferentiableAt ℝ F (γ t)) :
    HasDerivAt (fun s => F (γ s)) (poissonH0 F H (γ t)) t := by
  rw [poissonH0_eq_fderiv_hamField]
  exact hF.hasFDerivAt.comp_hasDerivAt t hγ

theorem gradH0_of_not_differentiableAt {F : H0Space38 → ℝ} {x : H0Space38}
    (h : ¬ DifferentiableAt ℝ F x) : gradH0 F x = 0 :=
  gradient_eq_zero_of_not_differentiableAt h

theorem poissonH0_of_not_differentiableAt_left {F : H0Space38 → ℝ} {x : H0Space38}
    (h : ¬ DifferentiableAt ℝ F x) (G : H0Space38 → ℝ) : poissonH0 F G x = 0 := by
  rw [poissonH0_eq_inner, gradH0_of_not_differentiableAt h]; simp

theorem poissonH0_of_not_differentiableAt_right (F : H0Space38 → ℝ) {G : H0Space38 → ℝ}
    {x : H0Space38} (h : ¬ DifferentiableAt ℝ G x) : poissonH0 F G x = 0 := by
  rw [poissonH0_eq_inner, gradH0_of_not_differentiableAt h]; simp

/-! ## Invariance under symplectic maps -/

/-- `T` preserves `ω_std` at `x`: `DT(x)` is symplectic (the same form as the field
`BirkhoffInput38.canonical`). -/
def IsSymplecticAt38 (T : H0Space38 → H0Space38) (x : H0Space38) : Prop :=
  ∀ ξ η : H0Space38,
    stdSymplectic38 (carrierCoe38 _ (fderiv ℝ T x ξ)) (carrierCoe38 _ (fderiv ℝ T x η)) =
      stdSymplectic38 (carrierCoe38 _ ξ) (carrierCoe38 _ η)

/-- Linear algebra core: if `A` is a surjective symplectic operator and `a' = A^* a`
(`⟪a', ξ⟫ = ⟪a, Aξ⟫`), then `A (J a') = J a`. -/
theorem symplectic_adjoint_J (A : H0Space38 →L[ℝ] H0Space38) (hsurj : Function.Surjective A)
    (hA : ∀ ξ η : H0Space38, ⟪J38 _ (A ξ), A η⟫_ℝ = ⟪J38 _ ξ, η⟫_ℝ)
    (a a' : H0Space38) (h : ∀ ξ, ⟪a', ξ⟫_ℝ = ⟪a, A ξ⟫_ℝ) : A (J38 _ a') = J38 _ a := by
  have hz : ∀ ζ : H0Space38, ⟪J38 _ (A (J38 _ a') - J38 _ a), ζ⟫_ℝ = 0 := by
    intro ζ
    obtain ⟨η, rfl⟩ := hsurj ζ
    rw [map_sub, inner_sub_left, hA, J38_J38, J38_J38, inner_neg_left, inner_neg_left, h]
    ring
  have h0 : J38 _ (A (J38 _ a') - J38 _ a) = 0 :=
    ext_inner_right ℝ (fun v => by rw [hz v, inner_zero_left])
  have h1 : A (J38 _ a') - J38 _ a = 0 := by
    have := congrArg (J38 ((0 : ℕ) : ℝ)) h0
    rw [J38_J38, map_zero] at this
    exact neg_eq_zero.mp this
  exact sub_eq_zero.mp h1

/-- Pointwise invariance of the bracket under a map with surjective symplectic derivative. -/
theorem poissonH0_comp_of_symplectic_at {T : H0Space38 → H0Space38} {x : H0Space38}
    (hT : DifferentiableAt ℝ T x) (hsurj : Function.Surjective (fderiv ℝ T x))
    (hsymp : IsSymplecticAt38 T x) {F G : H0Space38 → ℝ}
    (hF : DifferentiableAt ℝ F (T x)) (hG : DifferentiableAt ℝ G (T x)) :
    poissonH0 (F ∘ T) (G ∘ T) x = poissonH0 F G (T x) := by
  have hA : ∀ ξ η : H0Space38, ⟪J38 _ (fderiv ℝ T x ξ), fderiv ℝ T x η⟫_ℝ =
      ⟪J38 _ ξ, η⟫_ℝ := fun ξ η => by
    rw [← stdSymplectic38_coe_eq, ← stdSymplectic38_coe_eq]; exact hsymp ξ η
  have hgrad : ∀ K : H0Space38 → ℝ, DifferentiableAt ℝ K (T x) → ∀ ξ,
      ⟪gradH0 (K ∘ T) x, ξ⟫_ℝ = ⟪gradH0 K (T x), fderiv ℝ T x ξ⟫_ℝ := fun K hK ξ => by
    rw [inner_gradH0, inner_gradH0, fderiv_comp x hK hT]; rfl
  have key := symplectic_adjoint_J (fderiv ℝ T x) hsurj hA _ _ (hgrad F hF)
  rw [poissonH0_eq_inner, poissonH0_eq_inner, real_inner_comm, hgrad G hG, key]
  exact real_inner_comm _ _

theorem differentiableAt_comp_homeomorph_iff (T : H0Space38 ≃ₜ H0Space38) (x : H0Space38)
    (hT : DifferentiableAt ℝ T x) (hTi : DifferentiableAt ℝ T.symm (T x))
    (F : H0Space38 → ℝ) : DifferentiableAt ℝ (F ∘ T) x ↔ DifferentiableAt ℝ F (T x) := by
  constructor
  · intro h
    have h' : DifferentiableAt ℝ (F ∘ T) (T.symm (T x)) := by rwa [T.symm_apply_apply]
    have := h'.comp (T x) hTi
    have e : (F ∘ T) ∘ T.symm = F := by funext y; simp
    rwa [e] at this
  · intro h; exact h.comp x hT

/-- **Invariance of the bracket under symplectic `C¹` diffeomorphisms of `h⁰`.**
`T` is a homeomorphism, `C¹` with `C¹` inverse, with symplectic derivative at every point. -/
theorem poissonH0_comp_symplectic (T : H0Space38 ≃ₜ H0Space38) (hT : ContDiff ℝ 1 T)
    (hTi : ContDiff ℝ 1 T.symm) (hsymp : ∀ x, IsSymplecticAt38 T x) (F G : H0Space38 → ℝ)
    (x : H0Space38) : poissonH0 (F ∘ T) (G ∘ T) x = poissonH0 F G (T x) := by
  have hd : DifferentiableAt ℝ T x := (hT.differentiable (by norm_num)) x
  have hdi : DifferentiableAt ℝ T.symm (T x) := (hTi.differentiable (by norm_num)) (T x)
  by_cases hF : DifferentiableAt ℝ F (T x)
  · by_cases hG : DifferentiableAt ℝ G (T x)
    · refine poissonH0_comp_of_symplectic_at hd ?_ (hsymp x) hF hG
      have h1 : HasFDerivAt T (fderiv ℝ T x) x := hd.hasFDerivAt
      have h2 : HasFDerivAt T.symm (fderiv ℝ T.symm (T x)) (T x) := hdi.hasFDerivAt
      have h3 : HasFDerivAt (T ∘ T.symm) ((fderiv ℝ T x).comp (fderiv ℝ T.symm (T x))) (T x) := by
        have := HasFDerivAt.comp (T x) (by rwa [T.symm_apply_apply]) h2
        exact this
      have e : (T ∘ T.symm) = id := by funext y; simp
      rw [e] at h3
      have h4 := h3.unique (hasFDerivAt_id (T x))
      intro y
      refine ⟨fderiv ℝ T.symm (T x) y, ?_⟩
      have := congrArg (fun L => L y) h4
      simpa using this
    · rw [poissonH0_of_not_differentiableAt_right _ hG, poissonH0_of_not_differentiableAt_right]
      rwa [differentiableAt_comp_homeomorph_iff T x hd hdi]
  · rw [poissonH0_of_not_differentiableAt_left hF, poissonH0_of_not_differentiableAt_left]
    rwa [differentiableAt_comp_homeomorph_iff T x hd hdi]

/-- A continuous linear isomorphism of `h⁰` with symplectic derivative (i.e. itself). -/
theorem poissonH0_comp_linear_symplectic (L : H0Space38 ≃L[ℝ] H0Space38)
    (hL : ∀ ξ η : H0Space38,
      stdSymplectic38 (carrierCoe38 _ (L ξ)) (carrierCoe38 _ (L η)) =
        stdSymplectic38 (carrierCoe38 _ ξ) (carrierCoe38 _ η))
    (F G : H0Space38 → ℝ) (x : H0Space38) :
    poissonH0 (F ∘ L) (G ∘ L) x = poissonH0 F G (L x) := by
  have hsymp : ∀ x, IsSymplecticAt38 L.toHomeomorph x := fun x => by
    show IsSymplecticAt38 (⇑L) x
    unfold IsSymplecticAt38
    rw [L.fderiv]
    exact hL
  exact poissonH0_comp_symplectic L.toHomeomorph L.contDiff L.symm.contDiff hsymp F G x


/-! ## Coordinate functionals and regression probes -/

/-- Single-mode vector `c · e_n ∈ h⁰`. -/
def modeVec0 (n : ℤ) (c : ℂ) : H0Space38 :=
  carrierMk38 _ (Pi.single n c) (finiteSupport_mem_seqSobolev38 _ _
    ((Set.finite_singleton n).subset (fun k hk => by
      by_contra h
      exact hk (by simp [show k ≠ n by simpa using h]))))

@[simp] theorem carrierCoe38_modeVec0 (n : ℤ) (c : ℂ) :
    carrierCoe38 _ (modeVec0 n c) = Pi.single n c := rfl

/-- The `n`-th coordinate functional `x ↦ Re x_n`. -/
def coordRe (n : ℤ) (x : H0Space38) : ℝ := (carrierCoe38 _ x n).re

/-- The `n`-th coordinate functional `x ↦ Im x_n`. -/
def coordIm (n : ℤ) (x : H0Space38) : ℝ := (carrierCoe38 _ x n).im

/-- `H = ½ |x_n|²`. -/
def halfSq (n : ℤ) (x : H0Space38) : ℝ := (1 / 2) * ‖carrierCoe38 _ x n‖ ^ 2

/-- The `n`-th coordinate as a continuous real-linear map `h⁰ → ℂ`. -/
def coordCLM0 (n : ℤ) : H0Space38 →L[ℝ] ℂ where
  toFun x := carrierCoe38 _ x n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_carrierCoe_apply38 _ n

@[simp] theorem coordCLM0_apply (n : ℤ) (x : H0Space38) :
    coordCLM0 n x = carrierCoe38 _ x n := rfl

theorem inner_modeVec0 (n : ℤ) (c : ℂ) (y : H0Space38) :
    ⟪modeVec0 n c, y⟫_ℝ = (starRingEnd ℂ c * carrierCoe38 _ y n).re := by
  have h := carrier_inner_hasSum38 ((0 : ℕ) : ℝ) (modeVec0 n c) y
  simp only [sobolevModeWeight_natCast_zero, one_mul] at h
  refine h.unique ?_
  convert hasSum_single n (f := fun k : ℤ =>
      (starRingEnd ℂ (carrierCoe38 ((0 : ℕ) : ℝ) (modeVec0 n c) k) *
        carrierCoe38 ((0 : ℕ) : ℝ) y k).re) (fun k hk => by simp [hk]) using 1
  simp

theorem J38_modeVec0 (n : ℤ) (c : ℂ) : J38 _ (modeVec0 n c) = modeVec0 n (Complex.I * c) := by
  apply carrierExt38
  funext k
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk]

theorem neg_modeVec0 (n : ℤ) (c : ℂ) : -modeVec0 n c = modeVec0 n (-c) := by
  apply carrierExt38
  funext k
  show -((Pi.single n c : ℤ → ℂ) k) = (Pi.single n (-c) : ℤ → ℂ) k
  by_cases hk : k = n
  · subst hk; simp
  · simp [hk]

theorem hasGradientAt_coordRe (n : ℤ) (x : H0Space38) :
    HasGradientAt (coordRe n) (modeVec0 n 1) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine ((Complex.reCLM.comp (coordCLM0 n)).hasFDerivAt (x := x)).congr_fderiv ?_
  ext y
  simp [InnerProductSpace.toDual_apply_apply, inner_modeVec0]

theorem hasGradientAt_coordIm (n : ℤ) (x : H0Space38) :
    HasGradientAt (coordIm n) (modeVec0 n Complex.I) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine ((Complex.imCLM.comp (coordCLM0 n)).hasFDerivAt (x := x)).congr_fderiv ?_
  ext y
  simp [InnerProductSpace.toDual_apply_apply, inner_modeVec0]

theorem hasGradientAt_halfSq (n : ℤ) (x : H0Space38) :
    HasGradientAt (halfSq n) (modeVec0 n (carrierCoe38 _ x n)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h0 : HasFDerivAt (fun z : H0Space38 => carrierCoe38 _ z n) (coordCLM0 n) x :=
    (coordCLM0 n).hasFDerivAt
  have h1 : HasFDerivAt (halfSq n) ((1 / 2 : ℝ) • (2 • ((innerSL ℝ) (carrierCoe38 _ x n)).comp
      (coordCLM0 n))) x := (h0.norm_sq).const_mul (1 / 2 : ℝ)
  refine h1.congr_fderiv ?_
  ext y
  simp [InnerProductSpace.toDual_apply_apply, inner_modeVec0, Complex.inner]
  ring

/-- **Probe (coordinate bracket).**  `{Re x_n, Im x_m} = δ_{nm}`: in particular
`{Re x_n, Im x_n} = +1` (the sign of `ω_std = Σ dq ∧ dp`, `x_n = q_n + i p_n`). -/
theorem poissonH0_re_im (n m : ℤ) (x : H0Space38) :
    poissonH0 (coordRe n) (coordIm m) x = if n = m then 1 else 0 := by
  rw [poissonH0_eq_inner, gradH0, gradH0, (hasGradientAt_coordRe n x).gradient,
    (hasGradientAt_coordIm m x).gradient, J38_modeVec0, inner_modeVec0]
  by_cases h : n = m
  · subst h; simp
  · simp [h]

theorem poissonH0_im_re (n m : ℤ) (x : H0Space38) :
    poissonH0 (coordIm n) (coordRe m) x = if n = m then -1 else 0 := by
  rw [poissonH0_antisymm, poissonH0_re_im]
  by_cases h : m = n
  · subst h; simp
  · simp [h, Ne.symm h]

theorem poissonH0_re_re (n m : ℤ) (x : H0Space38) : poissonH0 (coordRe n) (coordRe m) x = 0 := by
  rw [poissonH0_eq_inner, gradH0, gradH0, (hasGradientAt_coordRe n x).gradient,
    (hasGradientAt_coordRe m x).gradient, J38_modeVec0, inner_modeVec0]
  by_cases h : n = m
  · subst h; simp
  · simp [h]

theorem poissonH0_im_im (n m : ℤ) (x : H0Space38) : poissonH0 (coordIm n) (coordIm m) x = 0 := by
  rw [poissonH0_eq_inner, gradH0, gradH0, (hasGradientAt_coordIm n x).gradient,
    (hasGradientAt_coordIm m x).gradient, J38_modeVec0, inner_modeVec0]
  by_cases h : n = m
  · subst h; simp
  · simp [h]

/-- **Probe (T4 sign).**  The Hamiltonian field of `H = ½ |x_n|²` is `ż_n = -i x_n`, i.e.
`x_n(t) = e^{-it} x_n(0)`, the sign of the NLS plane-wave flow of regression T4. -/
theorem hamField_halfSq (n : ℤ) (x : H0Space38) :
    hamFieldH0 (halfSq n) x = modeVec0 n (-Complex.I * carrierCoe38 _ x n) := by
  rw [hamFieldH0, JgradH0, gradH0, (hasGradientAt_halfSq n x).gradient, J38_modeVec0,
    neg_modeVec0, neg_mul]

/-- Probe (sign and `½` of `hamilton_form`, T4): the vector `ż = -i(ω_n z_n)` satisfies
`ω_std(ż, η) = d(½ ω_n |z_n|²)(η)`; with `ham = ω_n |z_n|²` this is `½ d ham`. -/
theorem stdSymplectic38_dyn_halfSq (n : ℤ) (x η : H0Space38) :
    stdSymplectic38 (Pi.single n (-Complex.I * carrierCoe38 _ x n)) (carrierCoe38 _ η) =
      fderiv ℝ (halfSq n) x η := by
  rw [← stdSymplectic38_hamField, hamField_halfSq, carrierCoe38_modeVec0]

/-- `{Re x_m, ½|x_n|²} = δ_{mn} Im x_n`, equivalently `d/dt Re x_n = Im x_n` along `ż = -i x`. -/
theorem poissonH0_re_halfSq (m n : ℤ) (x : H0Space38) :
    poissonH0 (coordRe m) (halfSq n) x = if m = n then (carrierCoe38 _ x n).im else 0 := by
  rw [poissonH0_eq_inner, gradH0, gradH0, (hasGradientAt_coordRe m x).gradient,
    (hasGradientAt_halfSq n x).gradient, J38_modeVec0, inner_modeVec0]
  by_cases h : m = n
  · subst h; simp
  · simp [h]

/-! ### Invariance probes -/

/-- Probe: the identity map. -/
theorem probe_poissonH0_id (F G : H0Space38 → ℝ) (x : H0Space38) :
    poissonH0 (F ∘ (Homeomorph.refl H0Space38)) (G ∘ (Homeomorph.refl H0Space38)) x =
      poissonH0 F G x := by
  refine poissonH0_comp_symplectic (Homeomorph.refl H0Space38) contDiff_id contDiff_id
    (fun y ξ η => ?_) F G x
  simp

/-- The complex structure `J` as a continuous linear isomorphism (`J⁻¹ = -J`). -/
def JEquiv38 : H0Space38 ≃L[ℝ] H0Space38 :=
  ContinuousLinearEquiv.equivOfInverse (J38 _) (-(J38 _))
    (fun x => by simp [J38_J38]) (fun x => by simp [J38_J38])

@[simp] theorem JEquiv38_apply (x : H0Space38) : JEquiv38 x = J38 _ x := rfl

/-- Probe: a linear isomorphism (multiplication by `i`, which is symplectic). -/
theorem probe_poissonH0_J (F G : H0Space38 → ℝ) (x : H0Space38) :
    poissonH0 (F ∘ JEquiv38) (G ∘ JEquiv38) x = poissonH0 F G (J38 _ x) :=
  poissonH0_comp_linear_symplectic JEquiv38 (fun ξ η => stdSymplectic38_J_J ξ η) F G x

/-- Probe (linear isomorphism and coordinates together): `Re x_n ∘ J` and `Im x_n ∘ J` still
have bracket `1`, as predicted by invariance and `{Re x_n, Im x_n} = 1` at `J x`. -/
theorem probe_poissonH0_J_coord (n : ℤ) (x : H0Space38) :
    poissonH0 (coordRe n ∘ JEquiv38) (coordIm n ∘ JEquiv38) x = 1 := by
  rw [probe_poissonH0_J, poissonH0_re_im]; simp

end NlsGge.GK38.Lib
