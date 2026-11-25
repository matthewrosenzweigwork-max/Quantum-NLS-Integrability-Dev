import NlsGge.GK38.Lib.EntireProductsParamb

/-!
# L4c, part 1c: book Lemma C.1, jointly analytic form

The map `(λ, σ̃) ↦ ∏'[symmetricIcc ℤ] m, (σ_m - λ)/π_m`, `σ = σ° + σ̃`, is analytic on `ℂ × ℓ²`.

Route (book proof of Lemma C.1 + Thm A.4, adapted to the L3a API).  Weak analyticity is a
statement about complex lines `ζ ↦ (λ₀ + ζ μ, σ̃₀ + ζ h̃)`; along a line the paired terms have the
summable majorant `pairMaj (2|σ̃₀|² + 2|h̃|²)` (uniform for `|ζ| ≤ 1`), so the product is a
locally uniform limit of entire functions of `ζ` (Weierstrass, as in L4a's
`differentiableOn_tprod_one_add`).  Local boundedness on balls is `norm_entProd_le`.  Then
`analyticOnNhd_of_weak_of_locBdd` (L3a) gives analyticity on all of `ℂ × ℓ²`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-- The product as a function of `(λ, σ̃) ∈ ℂ × ℓ²`. -/
def entProdJ (p : ℂ × L2Seq) : ℂ := ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf p.2) p.1 m

theorem entProdJ_eq (z : ℂ) (s : L2Seq) :
    entProdJ (z, s) = ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf s) z m := rfl

theorem sigmaOf_line (s0 hs : L2Seq) (ζ : ℂ) (n : ℤ) :
    sigmaOf (s0 + ζ • hs) n = sigmaOf s0 n + ζ * hs n := by
  simp only [sigmaOf, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem differentiable_pairTerm_line (z0 hz : ℂ) (s0 hs : L2Seq) (m : ℕ) :
    Differentiable ℂ fun ζ : ℂ => pairTerm (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) m := by
  unfold pairTerm prodFactor
  simp only [sigmaOf_line]
  fun_prop

theorem differentiable_prodFactor_line (z0 hz : ℂ) (s0 hs : L2Seq) (m : ℤ) :
    Differentiable ℂ fun ζ : ℂ => prodFactor (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) m := by
  unfold prodFactor
  simp only [sigmaOf_line]
  fun_prop

/-- Along a complex line the product is differentiable on the unit disc. -/
theorem differentiableOn_entProd_line (z0 hz : ℂ) (s0 hs : L2Seq) :
    DifferentiableOn ℂ (fun ζ : ℂ => entProdJ (z0 + ζ * hz, s0 + ζ • hs)) (ball 0 1) := by
  set d : ℤ → ℝ := fun n => 2 * ‖s0 n‖ ^ 2 + 2 * ‖hs n‖ ^ 2 with hd
  have hdS : Summable d :=
    (((hasSum_sq_l2 s0).summable.mul_left 2).add ((hasSum_sq_l2 hs).summable.mul_left 2))
  set R : ℝ := ‖z0‖ + ‖hz‖ with hR
  have hbd : ∀ (m : ℕ) (ζ : ℂ), ‖ζ‖ ≤ 1 →
      ‖pairTerm (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) m‖ ≤ pairMaj d R m := by
    intro m ζ hζ
    refine pairTerm_le_maj ?_ ?_ m
    · calc ‖z0 + ζ * hz‖ ≤ ‖z0‖ + ‖ζ * hz‖ := norm_add_le _ _
        _ ≤ R := by
          rw [norm_mul]
          have := mul_le_mul_of_nonneg_right hζ (norm_nonneg hz)
          linarith
    · intro n
      rw [dev_sigmaOf, hd]
      simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 : ‖s0 n + ζ * hs n‖ ≤ ‖s0 n‖ + ‖hs n‖ := by
        calc ‖s0 n + ζ * hs n‖ ≤ ‖s0 n‖ + ‖ζ * hs n‖ := norm_add_le _ _
          _ ≤ ‖s0 n‖ + ‖hs n‖ := by
            rw [norm_mul]
            have := mul_le_mul_of_nonneg_right hζ (norm_nonneg (hs n))
            linarith
      have h2 : ‖s0 n + ζ * hs n‖ ^ 2 ≤ (‖s0 n‖ + ‖hs n‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖s0 n‖ - ‖hs n‖)]
  have hT : DifferentiableOn ℂ
      (fun ζ : ℂ => ∏' m : ℕ, (1 + pairTerm (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) m))
      (ball 0 1) :=
    differentiableOn_tprod_one_add (b := fun m ζ => pairTerm (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) m)
      (fun m => differentiable_pairTerm_line z0 hz s0 hs m) (summable_pairMaj hdS R) hbd
  have e : (fun ζ : ℂ => entProdJ (z0 + ζ * hz, s0 + ζ • hs))
      = fun ζ => prodFactor (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) 0 *
        ∏' m : ℕ, (1 + pairTerm (sigmaOf (s0 + ζ • hs)) (z0 + ζ * hz) m) := by
    funext ζ
    exact tprod_prodFactor (summable_dev_sigmaOf _) _
  rw [e]
  exact (differentiable_prodFactor_line z0 hz s0 hs 0).differentiableOn.mul hT

/-- Weak analyticity of the product on `ℂ × ℓ²`. -/
theorem weaklyAnalyticOn_entProdJ : WeaklyAnalyticOn entProdJ (Set.univ : Set (ℂ × L2Seq)) := by
  intro x _ h ℓ
  have hline : AnalyticAt ℂ (fun ζ : ℂ => entProdJ (x + ζ • h)) 0 := by
    have hd := differentiableOn_entProd_line x.1 h.1 x.2 h.2
    have hopen : ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 one_pos
    have : DifferentiableOn ℂ (fun ζ : ℂ => entProdJ (x + ζ • h)) (ball 0 1) := by
      refine hd.congr fun ζ _ => ?_
      rfl
    exact this.analyticAt hopen
  exact (ℓ.analyticAt _).comp hline

/-- **Book Lemma C.1 (jointly analytic form).**  `(λ, σ̃) ↦ ∏ (σ_m - λ)/π_m` is analytic on
`ℂ × ℓ²`. -/
theorem analyticOnNhd_entProd_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × L2Seq => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf p.2) p.1 m)
      Set.univ := by
  refine analyticOnNhd_of_weak_of_locBdd isOpen_univ weaklyAnalyticOn_entProdJ ?_
  intro x _
  refine ⟨1, one_pos, 2 * (‖x‖ + 1) * Real.exp (2 * majC1 * (‖x‖ + 1) ^ 2
    + majC2 (‖x‖ + 1) * sumInvSq), fun y hy => ?_⟩
  have hy' : ‖y‖ ≤ ‖x‖ + 1 := by
    have := mem_ball_iff_norm.mp hy
    calc ‖y‖ = ‖(y - x) + x‖ := by simp
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by linarith
  exact norm_entProd_le (le_trans (norm_fst_le y) hy') (le_trans (norm_snd_le y) hy')

end

end NlsGge.GK38.Lib
