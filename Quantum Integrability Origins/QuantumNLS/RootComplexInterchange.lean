import QuantumNLS.RootPoissonSeries

/-!
# R-C4F43CA8 `thm:root-involution`, part (2C-b1): the complex Poisson bracket of two summable series

Realized inputs (frozen): `RootPoissonSeries.hasSum_gradient_tsum`, `hasSum_inner_left'`, `hasSum_inner_right'`;
`SymplecticBracket.pbR`, `pbR_eq_omega`, `pbC` (DEF-015 complex bilinear extension).

Proved here (standard axioms only), for complex-valued series on a complex Hilbert space:
* `pbR_hasSum_tsum`: the strengthened real interchange (outer and inner `HasSum` forms, from `RootPoissonSeries`).
* `pbR_congr`: the real bracket depends only on the germ at `u`.
* `pbC_hasSum_tsum`: `HasSum (fun n => Σ'_m pbC(F_n, G_m)(u)) (pbC (Σ'_n F_n) (Σ'_m G_m) (u))`, hence
  `pbC (Σ F) (Σ G) u = Σ'_n Σ'_m pbC(F_n, G_m) u`.

Remainder (part 2C-b2, not here): the constant term, real scalars, the identification with the symbols
`productSymbol`, and the four real zero brackets.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace ComplexConjugate BigOperators
open Filter Topology Metric

attribute [local instance] InnerProductSpace.complexToReal

namespace QuantumNLS.RootComplexInterchange

open QuantumNLS.SymplecticBracket QuantumNLS.RootPoissonSeries

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pbR_hasSum_tsum (f g : ℕ → H → ℝ) (F' G' : ℕ → H → (H →L[ℝ] ℝ)) (a b : ℕ → ℝ) (u : H)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hfd : ∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (f n) (F' n x) x)
    (hgd : ∀ m, ∀ x ∈ ball u ρ, HasFDerivAt (g m) (G' m x) x)
    (hfb : ∀ n, ∀ x ∈ ball u ρ, ‖F' n x‖ ≤ a n) (hgb : ∀ m, ∀ x ∈ ball u ρ, ‖G' m x‖ ≤ b m)
    (ha : Summable a) (hb : Summable b) (hf0 : Summable fun n => f n u)
    (hg0 : Summable fun m => g m u) :
    HasSum (fun n => pbR (f n) (fun y => ∑' m, g m y) u) (pbR (fun y => ∑' n, f n y) (fun y => ∑' m, g m y) u)
      ∧ ∀ n, HasSum (fun m => pbR (f n) (g m) u) (pbR (f n) (fun y => ∑' m, g m y) u) := by
  have hA := hasSum_gradient_tsum f F' a u ρ hρ hfd hfb ha hf0
  have hB := hasSum_gradient_tsum g G' b u ρ hρ hgd hgb hb hg0
  have hom : ∀ F G : H → ℝ, pbR F G u =
      2 * (inner ℂ (SymplecticBracket.gradient F u) (SymplecticBracket.gradient G u)).im := by
    intro F G
    rw [pbR_eq_omega]
    rfl
  have hinner : ∀ n, HasSum (fun m => pbR (f n) (g m) u) (pbR (f n) (fun y => ∑' m, g m y) u) := by
    intro n
    have hm := hasSum_inner_right' (SymplecticBracket.gradient (f n) u) _ _ hB
    have hm2 := (Complex.imCLM.hasSum hm).mul_left 2
    have e1 : (fun m => pbR (f n) (g m) u) =
        fun m => 2 * (inner ℂ (SymplecticBracket.gradient (f n) u)
          (SymplecticBracket.gradient (g m) u)).im :=
      funext fun m => hom _ _
    rw [e1, hom]
    simpa [Complex.imCLM_apply] using hm2
  refine ⟨?_, hinner⟩
  have hout : ∀ n, ∑' m, pbR (f n) (g m) u = 2 * (inner ℂ (SymplecticBracket.gradient (f n) u)
      (SymplecticBracket.gradient (fun y => ∑' m, g m y) u)).im := fun n =>
    (hinner n).tsum_eq.trans (hom _ _)
  have h1 := hasSum_inner_left' _ _ hA (SymplecticBracket.gradient (fun y => ∑' m, g m y) u)
  have h2 := (Complex.imCLM.hasSum h1).mul_left 2
  have e2 : (fun n => pbR (f n) (fun y => ∑' m, g m y) u) =
      fun n => 2 * (inner ℂ (SymplecticBracket.gradient (f n) u)
        (SymplecticBracket.gradient (fun y => ∑' m, g m y) u)).im :=
    funext fun n => hom _ _
  rw [e2, hom]
  simpa [Complex.imCLM_apply] using h2

/-- The real bracket depends only on the germs at `u`. -/
theorem pbR_congr {F F' G G' : H → ℝ} {u : H} (hF : F =ᶠ[𝓝 u] F') (hG : G =ᶠ[𝓝 u] G') :
    pbR F G u = pbR F' G' u := by
  unfold pbR hamField SymplecticBracket.gradient
  rw [hF.fderiv_eq, hG.fderiv_eq]

theorem norm_reCLM_comp_le (L : H →L[ℝ] ℂ) : ‖Complex.reCLM.comp L‖ ≤ ‖L‖ := by
  have hre1 : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
      rw [one_mul, Complex.reCLM_apply, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm z)
  calc ‖Complex.reCLM.comp L‖ ≤ ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right hre1 (norm_nonneg _)
    _ = ‖L‖ := one_mul _

theorem norm_imCLM_comp_le (L : H →L[ℝ] ℂ) : ‖Complex.imCLM.comp L‖ ≤ ‖L‖ := by
  have him1 : ‖(Complex.imCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
      rw [one_mul, Complex.imCLM_apply, Real.norm_eq_abs]
      exact Complex.abs_im_le_norm z)
  calc ‖Complex.imCLM.comp L‖ ≤ ‖(Complex.imCLM : ℂ →L[ℝ] ℝ)‖ * ‖L‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖L‖ := mul_le_mul_of_nonneg_right him1 (norm_nonneg _)
    _ = ‖L‖ := one_mul _

/-- **Complex interchange.** For complex series with summable derivatives on a ball around `u` and
pointwise summability on the ball, the complex bracket of the sums is the iterated sum of the complex brackets. -/
theorem pbC_hasSum_tsum (F G : ℕ → H → ℂ) (F' G' : ℕ → H → (H →L[ℝ] ℂ)) (a b : ℕ → ℝ) (u : H)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hFd : ∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (F n) (F' n x) x)
    (hGd : ∀ m, ∀ x ∈ ball u ρ, HasFDerivAt (G m) (G' m x) x)
    (hFb : ∀ n, ∀ x ∈ ball u ρ, ‖F' n x‖ ≤ a n) (hGb : ∀ m, ∀ x ∈ ball u ρ, ‖G' m x‖ ≤ b m)
    (ha : Summable a) (hb : Summable b)
    (hFs : ∀ y ∈ ball u ρ, Summable fun n => F n y)
    (hGs : ∀ y ∈ ball u ρ, Summable fun m => G m y) :
    HasSum (fun n => ∑' m, pbC (F n) (G m) u)
      (pbC (fun y => ∑' n, F n y) (fun y => ∑' m, G m y) u) := by
  have hu : u ∈ ball u ρ := mem_ball_self hρ
  -- real and imaginary parts of the terms
  have hRd : ∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (fun y => (F n y).re)
      (Complex.reCLM.comp (F' n x)) x := fun n x hx =>
    (Complex.reCLM.hasFDerivAt).comp x (hFd n x hx)
  have hId : ∀ n, ∀ x ∈ ball u ρ, HasFDerivAt (fun y => (F n y).im)
      (Complex.imCLM.comp (F' n x)) x := fun n x hx =>
    (Complex.imCLM.hasFDerivAt).comp x (hFd n x hx)
  have hRe' : ∀ m, ∀ x ∈ ball u ρ, HasFDerivAt (fun y => (G m y).re)
      (Complex.reCLM.comp (G' m x)) x := fun m x hx =>
    (Complex.reCLM.hasFDerivAt).comp x (hGd m x hx)
  have hIm' : ∀ m, ∀ x ∈ ball u ρ, HasFDerivAt (fun y => (G m y).im)
      (Complex.imCLM.comp (G' m x)) x := fun m x hx =>
    (Complex.imCLM.hasFDerivAt).comp x (hGd m x hx)
  have hRb : ∀ n, ∀ x ∈ ball u ρ, ‖Complex.reCLM.comp (F' n x)‖ ≤ a n := fun n x hx =>
    (norm_reCLM_comp_le _).trans (hFb n x hx)
  have hIb : ∀ n, ∀ x ∈ ball u ρ, ‖Complex.imCLM.comp (F' n x)‖ ≤ a n := fun n x hx =>
    (norm_imCLM_comp_le _).trans (hFb n x hx)
  have hRb' : ∀ m, ∀ x ∈ ball u ρ, ‖Complex.reCLM.comp (G' m x)‖ ≤ b m := fun m x hx =>
    (norm_reCLM_comp_le _).trans (hGb m x hx)
  have hIb' : ∀ m, ∀ x ∈ ball u ρ, ‖Complex.imCLM.comp (G' m x)‖ ≤ b m := fun m x hx =>
    (norm_imCLM_comp_le _).trans (hGb m x hx)
  -- summability of the real and imaginary parts, pointwise on the ball
  have hRs : ∀ (K : ℕ → H → ℂ), (∀ y ∈ ball u ρ, Summable fun n => K n y) →
      ∀ y ∈ ball u ρ, Summable fun n => (K n y).re := fun K hK y hy => by
    simpa using Complex.reCLM.summable (hK y hy)
  have hIs : ∀ (K : ℕ → H → ℂ), (∀ y ∈ ball u ρ, Summable fun n => K n y) →
      ∀ y ∈ ball u ρ, Summable fun n => (K n y).im := fun K hK y hy => by
    simpa using Complex.imCLM.summable (hK y hy)
  -- real and imaginary parts of a convergent complex series
  have hEqR : ∀ (K : ℕ → H → ℂ), (∀ y ∈ ball u ρ, Summable fun n => K n y) →
      ∀ y ∈ ball u ρ, (∑' n, K n y).re = ∑' n, (K n y).re := fun K hK y hy => by
    have := Complex.reCLM.map_tsum (hK y hy)
    simpa using this
  have hEqI : ∀ (K : ℕ → H → ℂ), (∀ y ∈ ball u ρ, Summable fun n => K n y) →
      ∀ y ∈ ball u ρ, (∑' n, K n y).im = ∑' n, (K n y).im := fun K hK y hy => by
    have := Complex.imCLM.map_tsum (hK y hy)
    simpa using this
  have gR : ∀ (K : ℕ → H → ℂ), (∀ y ∈ ball u ρ, Summable fun n => K n y) →
      (fun y => (∑' n, K n y).re) =ᶠ[𝓝 u] (fun y => ∑' n, (K n y).re) := fun K hK =>
    eventually_of_mem (ball_mem_nhds u hρ) (fun y hy => hEqR K hK y hy)
  have gI : ∀ (K : ℕ → H → ℂ), (∀ y ∈ ball u ρ, Summable fun n => K n y) →
      (fun y => (∑' n, K n y).im) =ᶠ[𝓝 u] (fun y => ∑' n, (K n y).im) := fun K hK =>
    eventually_of_mem (ball_mem_nhds u hρ) (fun y hy => hEqI K hK y hy)
  -- the four real interchanges
  have P_RR := pbR_hasSum_tsum (fun n y => (F n y).re) (fun m y => (G m y).re)
    (fun n x => Complex.reCLM.comp (F' n x)) (fun m x => Complex.reCLM.comp (G' m x)) a b u ρ hρ
    (fun n x hx => hRd n x hx) (fun m x hx => hRe' m x hx) (fun n x hx => hRb n x hx)
    (fun m x hx => hRb' m x hx) ha hb (hRs F hFs u hu) (hRs G hGs u hu)
  have P_II := pbR_hasSum_tsum (fun n y => (F n y).im) (fun m y => (G m y).im)
    (fun n x => Complex.imCLM.comp (F' n x)) (fun m x => Complex.imCLM.comp (G' m x)) a b u ρ hρ
    (fun n x hx => hId n x hx) (fun m x hx => hIm' m x hx) (fun n x hx => hIb n x hx)
    (fun m x hx => hIb' m x hx) ha hb (hIs F hFs u hu) (hIs G hGs u hu)
  have P_IR := pbR_hasSum_tsum (fun n y => (F n y).im) (fun m y => (G m y).re)
    (fun n x => Complex.imCLM.comp (F' n x)) (fun m x => Complex.reCLM.comp (G' m x)) a b u ρ hρ
    (fun n x hx => hId n x hx) (fun m x hx => hRe' m x hx) (fun n x hx => hIb n x hx)
    (fun m x hx => hRb' m x hx) ha hb (hIs F hFs u hu) (hRs G hGs u hu)
  have P_RI := pbR_hasSum_tsum (fun n y => (F n y).re) (fun m y => (G m y).im)
    (fun n x => Complex.reCLM.comp (F' n x)) (fun m x => Complex.imCLM.comp (G' m x)) a b u ρ hρ
    (fun n x hx => hRd n x hx) (fun m x hx => hIm' m x hx) (fun n x hx => hRb n x hx)
    (fun m x hx => hIb' m x hx) ha hb (hRs F hFs u hu) (hIs G hGs u hu)
  -- germs of the complex sums
  have eRR := pbR_congr (gR F hFs) (gR G hGs)
  have eII := pbR_congr (gI F hFs) (gI G hGs)
  have eIR := pbR_congr (gI F hFs) (gR G hGs)
  have eRI := pbR_congr (gR F hFs) (gI G hGs)
  -- the complex bracket of the sums, in real components
  have hpbC : pbC (fun y => ∑' n, F n y) (fun y => ∑' m, G m y) u =
      Complex.mk (pbR (fun y => ∑' n, (F n y).re) (fun y => ∑' m, (G m y).re) u -
          pbR (fun y => ∑' n, (F n y).im) (fun y => ∑' m, (G m y).im) u)
        (pbR (fun y => ∑' n, (F n y).im) (fun y => ∑' m, (G m y).re) u +
          pbR (fun y => ∑' n, (F n y).re) (fun y => ∑' m, (G m y).im) u) := by
    simp only [pbC]
    rw [eRR, eII, eIR, eRI]
  -- the terms of the outer series
  let K : ℕ → ℂ := fun n => Complex.mk
    (pbR (fun y => (F n y).re) (fun y => ∑' m, (G m y).re) u -
      pbR (fun y => (F n y).im) (fun y => ∑' m, (G m y).im) u)
    (pbR (fun y => (F n y).im) (fun y => ∑' m, (G m y).re) u +
      pbR (fun y => (F n y).re) (fun y => ∑' m, (G m y).im) u)
  have hK : ∀ n, HasSum (fun m => pbC (F n) (G m) u) (K n) := by
    intro n
    refine (Complex.hasSum_iff _ _).2 ⟨?_, ?_⟩
    · exact (P_RR.2 n).sub (P_II.2 n)
    · exact (P_IR.2 n).add (P_RI.2 n)
  have hout : HasSum K (pbC (fun y => ∑' n, F n y) (fun y => ∑' m, G m y) u) := by
    rw [hpbC]
    refine (Complex.hasSum_iff _ _).2 ⟨?_, ?_⟩
    · exact P_RR.1.sub P_II.1
    · exact P_IR.1.add P_RI.1
  have hfun : (fun n => ∑' m, pbC (F n) (G m) u) = K :=
    funext fun n => (hK n).tsum_eq
  rw [hfun]
  exact hout

end QuantumNLS.RootComplexInterchange

#print axioms QuantumNLS.RootComplexInterchange.pbR_hasSum_tsum
#print axioms QuantumNLS.RootComplexInterchange.pbR_congr
#print axioms QuantumNLS.RootComplexInterchange.pbC_hasSum_tsum
