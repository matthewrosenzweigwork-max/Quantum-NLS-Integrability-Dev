import QuantumNLS.Prop019Linearization

/-!
# PROP-020 (`Q7A:thm:main`), input 2: the parametrized window contour is the rectangle contour integral

The PROP-026 operators integrate over the parameter space `Θ = Fin 6 × [0,1]` of `MPContour.rectPieces a h ω`
(`ν = count ⊗ Lebesgue`, `u_θ = −(2πκ)^{−1} ω(z_θ) γ'`); the PROP-018 eigenvalues are rectangle contour integrals
`LabelExactPeriod.rectIntegral` over `Γ = ∂([−a,a] × [−h,h])`. This module proves, for `F` continuous on `Γ`:

`∫_Θ u_θ F(z_θ) dν = −(2πκ)^{−1} ∮_Γ ω(z) F(z) dz`  (`theta_integral_rect`),

piece by piece (affine changes of variables; the two vertical sides are split at the real axis exactly as `rectPieces`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory Set Complex

noncomputable section

namespace QuantumNLS.Prop020Contour

open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ affinePiece rectPieces continuous_zθ continuous_uθ)
open QuantumNLS.Prop019Linearization (rect_re_im)

lemma cv (Φ : ℝ → ℂ) (c d : ℝ) (hc : c ≠ 0) :
    ∫ τ in (0:ℝ)..1, Φ (c * τ + d) * (c : ℂ) = ∫ x in d..(c + d), Φ x := by
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_mul_add Φ hc d]
  simp only [mul_zero, zero_add, mul_one]
  rw [← Complex.coe_smul, smul_eq_mul, mul_comm, ← mul_assoc]
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  push_cast
  field_simp

lemma piece_h (Φ : ℂ → ℂ) (p q : ℂ) (c d y0 : ℝ) (hc : c ≠ 0)
    (hp : ∀ τ : ℝ, p + (τ : ℂ) * (q - p) = ((c * τ + d : ℝ) : ℂ) + (y0 : ℂ) * I) (hqp : q - p = (c : ℂ)) :
    ∫ τ in (0:ℝ)..1, Φ (p + (τ : ℂ) * (q - p)) * (q - p) = ∫ x in d..(c + d), Φ (x + (y0 : ℂ) * I) := by
  rw [← cv (fun x : ℝ => Φ (x + (y0 : ℂ) * I)) c d hc]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [hp τ, hqp]

lemma piece_v (Φ : ℂ → ℂ) (p q : ℂ) (c d x0 : ℝ) (hc : c ≠ 0)
    (hp : ∀ τ : ℝ, p + (τ : ℂ) * (q - p) = (x0 : ℂ) + ((c * τ + d : ℝ) : ℂ) * I) (hqp : q - p = I * c) :
    ∫ τ in (0:ℝ)..1, Φ (p + (τ : ℂ) * (q - p)) * (q - p) = I • ∫ y in d..(c + d), Φ (x0 + (y : ℂ) * I) := by
  rw [← cv (fun y : ℝ => Φ (x0 + (y : ℂ) * I)) c d hc, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  rw [hp τ, hqp, smul_eq_mul]
  ring

set_option linter.unusedTactic false in
/-- The six piece integrals of `rectPieces` sum to the rectangle integral. -/
theorem pieces_sum {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (ω : ℂ → ℂ) (hω : Continuous ω) (Φ : ℂ → ℂ)
    (hv1 : IntervalIntegrable (fun y : ℝ => Φ (a + y * I)) volume (-h) 0)
    (hv2 : IntervalIntegrable (fun y : ℝ => Φ (a + y * I)) volume 0 h)
    (hv3 : IntervalIntegrable (fun y : ℝ => Φ (((-a : ℝ) : ℂ) + y * I)) volume (-h) 0)
    (hv4 : IntervalIntegrable (fun y : ℝ => Φ (((-a : ℝ) : ℂ) + y * I)) volume 0 h) :
    ∑ i : Fin 6, ∫ τ in (0:ℝ)..1, Φ ((rectPieces a h ω hω i).γ τ) * (rectPieces a h ω hω i).γ' τ =
      rectIntegral Φ (-a) a h := by
  have h2a : (2 * a) ≠ 0 := by positivity
  have hn2a : (-(2 * a)) ≠ 0 := by intro h0; apply h2a; linarith
  have hh0 : h ≠ 0 := hh.ne'
  have hnh : (-h) ≠ 0 := neg_ne_zero.2 hh0
  rw [Fin.sum_univ_six]
  change (∫ τ in (0:ℝ)..1, Φ (((-a : ℂ) - h * I) + (τ : ℂ) * (((a : ℂ) - h * I) - ((-a : ℂ) - h * I))) *
        (((a : ℂ) - h * I) - ((-a : ℂ) - h * I))) +
    (∫ τ in (0:ℝ)..1, Φ (((a : ℂ) - h * I) + (τ : ℂ) * ((a : ℂ) - ((a : ℂ) - h * I))) *
        ((a : ℂ) - ((a : ℂ) - h * I))) +
    (∫ τ in (0:ℝ)..1, Φ ((a : ℂ) + (τ : ℂ) * (((a : ℂ) + h * I) - (a : ℂ))) * (((a : ℂ) + h * I) - (a : ℂ))) +
    (∫ τ in (0:ℝ)..1, Φ (((a : ℂ) + h * I) + (τ : ℂ) * (((-a : ℂ) + h * I) - ((a : ℂ) + h * I))) *
        (((-a : ℂ) + h * I) - ((a : ℂ) + h * I))) +
    (∫ τ in (0:ℝ)..1, Φ (((-a : ℂ) + h * I) + (τ : ℂ) * ((-a : ℂ) - ((-a : ℂ) + h * I))) *
        ((-a : ℂ) - ((-a : ℂ) + h * I))) +
    (∫ τ in (0:ℝ)..1, Φ ((-a : ℂ) + (τ : ℂ) * (((-a : ℂ) - h * I) - (-a : ℂ))) * (((-a : ℂ) - h * I) - (-a : ℂ))) = _
  rw [piece_h Φ _ _ (2 * a) (-a) (-h) h2a (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ h (-h) a hh0 (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ h 0 a hh0 (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_h Φ _ _ (-(2 * a)) a h hn2a (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ (-h) h (-a) hnh (fun τ => by push_cast; ring) (by push_cast; ring),
    piece_v Φ _ _ (-h) 0 (-a) hnh (fun τ => by push_cast; ring) (by push_cast; ring)]
  unfold rectIntegral
  have e1 : 2 * a + -a = a := by ring
  have e2 : h + -h = (0:ℝ) := by ring
  have e3 : -(2 * a) + a = -a := by ring
  have e4 : -h + h = (0:ℝ) := by ring
  rw [e1, e2, e3, e4, add_zero, add_zero, ← intervalIntegral.integral_add_adjacent_intervals hv1 hv2,
    ← intervalIntegral.integral_add_adjacent_intervals hv3 hv4, intervalIntegral.integral_symm (-a) a,
    intervalIntegral.integral_symm 0 h, intervalIntegral.integral_symm (-h) 0]
  simp only [smul_eq_mul]
  ring

lemma integral_unitInterval (g : ℝ → ℂ) : ∫ τ : unitInterval, g τ = ∫ τ in (0:ℝ)..1, g τ := by
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  exact integral_subtype_comap measurableSet_Icc _

/-- The points of `rectPieces` lie on `Γ = Gam (−a) a h`. -/
lemma rect_mem_Gam {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (ω : ℂ → ℂ) (hω : Continuous ω) (i : Fin 6) {τ : ℝ}
    (hτ : τ ∈ Icc (0 : ℝ) 1) : (rectPieces a h ω hω i).γ τ ∈ Gam (-a) a h := by
  obtain ⟨h0, h1⟩ := hτ
  obtain ⟨hre, him⟩ := rect_re_im a h ω hω i τ
  generalize (rectPieces a h ω hω i).γ τ = z at hre him ⊢
  simp only [Gam, mem_union, Set.mem_ofPred_eq, mem_Icc]
  fin_cases i <;> simp at hre him <;> rw [hre, him]
  · exact Or.inl ⟨⟨by nlinarith, by nlinarith⟩, Or.inl rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inr rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inr rfl⟩
  · exact Or.inl ⟨⟨by nlinarith, by nlinarith⟩, Or.inr rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inl rfl⟩
  · exact Or.inr ⟨⟨by nlinarith, by nlinarith⟩, Or.inl rfl⟩

/-- **The parametrized contour integral is the rectangle integral**: for `F` continuous at every point of `Γ`,
`∫_Θ u_θ F(z_θ) dν = −(2πκ)^{−1} ∮_Γ ω F dz`. -/
theorem theta_integral_rect {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (κ : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω)
    (F : ℂ → ℂ) (hF : ∀ z ∈ Gam (-a) a h, ContinuousAt F z) :
    ∫ θ, uθ κ (rectPieces a h ω hω) θ * F (zθ (rectPieces a h ω hω) θ) ∂(nu 6) =
      -((((2 * Real.pi * κ)⁻¹ : ℝ)) : ℂ) * rectIntegral (fun z => ω z * F z) (-a) a h := by
  set P := rectPieces a h ω hω with hP
  have hmem : ∀ θ : ThetaSpace 6, zθ P θ ∈ Gam (-a) a h := fun θ =>
    rect_mem_Gam ha.le hh.le ω hω θ.1 ⟨θ.2.2.1, θ.2.2.2⟩
  have hcont : Continuous fun θ : ThetaSpace 6 => uθ κ P θ * F (zθ P θ) := by
    refine (continuous_uθ κ P).mul ?_
    exact continuous_iff_continuousAt.2 fun θ => (hF _ (hmem θ)).comp (continuous_zθ P).continuousAt
  have hint : Integrable (fun θ : ThetaSpace 6 => uθ κ P θ * F (zθ P θ)) (nu 6) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold nu at hint ⊢
  rw [integral_prod _ hint, integral_count]
  have hpiece : ∀ i : Fin 6, ∫ τ : unitInterval, uθ κ P (i, τ) * F (zθ P (i, τ)) =
      -((((2 * Real.pi * κ)⁻¹ : ℝ)) : ℂ) *
        ∫ τ in (0:ℝ)..1, (fun z => ω z * F z) ((P i).γ τ) * (P i).γ' τ := by
    intro i
    rw [← intervalIntegral.integral_const_mul, ← integral_unitInterval]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [uθ, zθ, hP, QuantumNLS.Prop019Linearization.rect_ω]
    ring
  simp_rw [hpiece]
  rw [← Finset.mul_sum]
  congr 1
  have hcv : ∀ x0 : ℝ, (x0 = a ∨ x0 = -a) → ∀ c d : ℝ, -h ≤ c → c ≤ h → -h ≤ d → d ≤ h →
      IntervalIntegrable (fun y : ℝ => ω (x0 + y * I) * F (x0 + y * I)) volume c d := by
    intro x0 hx0 c d hc1 hc2 hd1 hd2
    refine ContinuousOn.intervalIntegrable fun y hy => ?_
    have hy' : y ∈ Icc (-h) h := by
      rcases uIcc_subset_Icc ⟨hc1, hc2⟩ ⟨hd1, hd2⟩ hy with ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    have hmemy : (x0 : ℂ) + y * I ∈ Gam (-a) a h := by
      refine Or.inr ⟨by simpa using hy', ?_⟩
      rcases hx0 with rfl | rfl <;> simp
    have hc : ContinuousAt (fun y : ℝ => (x0 : ℂ) + y * I) y := by fun_prop
    exact ((hω.continuousAt.mul (hF _ hmemy)).comp (f := fun y : ℝ => (x0 : ℂ) + y * I) hc).continuousWithinAt
  exact pieces_sum ha hh ω hω (fun z => ω z * F z)
    (hcv a (Or.inl rfl) _ _ le_rfl (by linarith) (by linarith) hh.le)
    (hcv a (Or.inl rfl) _ _ (by linarith) hh.le (by linarith) le_rfl)
    (hcv (-a) (Or.inr rfl) _ _ le_rfl (by linarith) (by linarith) hh.le)
    (hcv (-a) (Or.inr rfl) _ _ (by linarith) hh.le (by linarith) le_rfl)

end QuantumNLS.Prop020Contour

#print axioms QuantumNLS.Prop020Contour.pieces_sum
#print axioms QuantumNLS.Prop020Contour.theta_integral_rect
