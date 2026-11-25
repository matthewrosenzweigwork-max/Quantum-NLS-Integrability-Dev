import QuantumNLS.ProductTorusComplexMultilinear
import QuantumNLS.ComplexifiedDiscriminant

/-!
# Complexified analytic infrastructure, stage X4: `Cx F ≅ F × F` and the complexified conjugation

Item (ii) of the R-3FEAD88B E5 assignment. Let `F` be a complex inner product space, viewed as a real one, and
`J` a conjugation on `F` (conjugate-linear, involutive, isometric; `Conj F`). For the complexification `Cx F` of the
real space `F` (stage C1), `phiCLE J : Cx F ≃L[ℂ] F × F`, `a + i b ↦ (a + i b, J a + i J b)`, is a complex-linear
topological isomorphism (`f ⊗ λ ↦ (λ f, λ J f)`), with
* `phi_ι`: the real points go to the real slice, `ι f ↦ (f, J f)`;
* `phi_conj`: the complexified conjugation `a + i b ↦ J a + i J b` becomes the swap `(u, v) ↦ (v, u)`;
* inverse `(u, v) ↦ (½(u + J v)) + i (−(i/2)(u − J v))`.
Instance: `starConj`, the pointwise conjugation `star` on `L²(𝕋_L)`. Combined with stage X3:
`cxDisc_cx`: `q ↦ cxDisc κ (Φ q.1).1 (Φ q.1).2 q.2` is complex analytic on all of `Cx(L²(𝕋_L)) × ℂ` and equals the
physical discriminant at `(ι u, z)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

open ComplexConjugate MeasureTheory Set

namespace QuantumNLS.ComplexifiedConjugation

open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear

-- Real structures are the given ones; do not derive them from the complex structures.
attribute [-instance] NormedSpace.complexToReal NormedAlgebra.complexToReal Module.complexToReal
  Algebra.complexToReal

/-- A conjugation on a complex normed space: conjugate-linear, involutive, isometric. -/
structure Conj (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] where
  J : F →ₗ⋆[ℂ] F
  invol : ∀ x, J (J x) = x
  norm_eq : ∀ x, ‖J x‖ = ‖x‖

section Generic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

variable (C : Conj F)

theorem hr (r : ℝ) (x : F) : r • x = (r : ℂ) • x := (ofReal_smul' r x).symm

omit [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem J_ofReal (r : ℝ) (x : F) : C.J ((r : ℂ) • x) = (r : ℂ) • C.J x := by
  rw [map_smulₛₗ, Complex.conj_ofReal]

/-- `Φ (a + i b) = (a + i b, J a + i J b)`. -/
def phiLin : Cx F →ₗ[ℂ] F × F where
  toFun z := (Cx.re z + Complex.I • Cx.im z, C.J (Cx.re z) + Complex.I • C.J (Cx.im z))
  map_add' z w := by
    ext
    · simp only [Cx.re_add, Cx.im_add, smul_add, Prod.fst_add]
      abel
    · simp only [Cx.re_add, Cx.im_add, map_add, smul_add, Prod.snd_add]
      abel
  map_smul' c z := by
    ext
    · simp only [Cx.re_smul, Cx.im_smul, Prod.smul_fst, RingHom.id_apply]
      erw [hr c.re (Cx.re z), hr c.im (Cx.im z), hr c.re (Cx.im z), hr c.im (Cx.re z)]
      conv_rhs => rw [← Complex.re_add_im c]
      match_scalars <;> (try simp only [Complex.coe_algebraMap]) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)
    · simp only [Cx.re_smul, Cx.im_smul, Prod.smul_snd, RingHom.id_apply]
      erw [hr c.re (Cx.re z), hr c.im (Cx.im z), hr c.re (Cx.im z), hr c.im (Cx.re z)]
      simp only [map_add, map_sub, J_ofReal]
      conv_rhs => rw [← Complex.re_add_im c]
      match_scalars <;> (try simp only [Complex.coe_algebraMap]) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)

/-- The inverse `(u, v) ↦ ½(u + J v) + i(−(i/2)(u − J v))`. -/
def psi (w : F × F) : Cx F :=
  Cx.mk ((1 / 2 : ℂ) • (w.1 + C.J w.2)) ((-(Complex.I / 2)) • (w.1 - C.J w.2))

theorem phi_psi (w : F × F) : phiLin C (psi C w) = w := by
  ext
  · show (1 / 2 : ℂ) • (w.1 + C.J w.2) + Complex.I • ((-(Complex.I / 2)) • (w.1 - C.J w.2)) = w.1
    match_scalars <;> (try simp only [Complex.coe_algebraMap]) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)
  · show C.J ((1 / 2 : ℂ) • (w.1 + C.J w.2)) + Complex.I • C.J ((-(Complex.I / 2)) • (w.1 - C.J w.2)) = w.2
    simp only [map_smulₛₗ, map_add, map_sub, C.invol, map_div₀, map_one, map_ofNat, map_neg, Complex.conj_I]
    match_scalars <;> (try simp only [Complex.coe_algebraMap]) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)

theorem psi_phi (z : Cx F) : psi C (phiLin C z) = z := by
  refine Cx.ext ?_ ?_
  · show (1 / 2 : ℂ) • ((Cx.re z + Complex.I • Cx.im z) + C.J (C.J (Cx.re z) + Complex.I • C.J (Cx.im z))) = Cx.re z
    simp only [map_smulₛₗ, map_add, C.invol, Complex.conj_I]
    match_scalars <;> (try simp only [Complex.coe_algebraMap]) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)
  · show (-(Complex.I / 2)) • ((Cx.re z + Complex.I • Cx.im z) - C.J (C.J (Cx.re z) + Complex.I • C.J (Cx.im z))) =
      Cx.im z
    simp only [map_smulₛₗ, map_add, C.invol, Complex.conj_I]
    match_scalars <;> (try simp only [Complex.coe_algebraMap]) <;> (ring_nf; try simp only [Complex.I_sq]; try ring_nf)

omit [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F] in
theorem norm_le_re_add_im (z : Cx F) : ‖z‖ ≤ ‖Cx.re z‖ + ‖Cx.im z‖ := by
  have h := Cx.norm_sq z
  nlinarith [norm_nonneg z, norm_nonneg (Cx.re z), norm_nonneg (Cx.im z)]

/-- **`Cx F ≃L[ℂ] F × F`**, `a + i b ↦ (a + i b, J a + i J b)`. -/
def phiCLE : Cx F ≃L[ℂ] F × F :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { phiLin C with invFun := psi C, left_inv := psi_phi C, right_inv := phi_psi C } 2 2
    (fun z => by
      show ‖phiLin C z‖ ≤ 2 * ‖z‖
      refine (norm_prod_le_iff.2 ⟨?_, ?_⟩)
      · show ‖Cx.re z + Complex.I • Cx.im z‖ ≤ 2 * ‖z‖
        rw [two_mul]
        refine (norm_add_le _ _).trans (add_le_add (norm_re_le z) ?_)
        rw [norm_smul, Complex.norm_I, one_mul]
        exact norm_im_le z
      · show ‖C.J (Cx.re z) + Complex.I • C.J (Cx.im z)‖ ≤ 2 * ‖z‖
        rw [two_mul]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [C.norm_eq]
          exact norm_re_le z
        · rw [norm_smul, Complex.norm_I, one_mul, C.norm_eq]
          exact norm_im_le z)
    (fun w => by
      show ‖psi C w‖ ≤ 2 * ‖w‖
      refine (norm_le_re_add_im _).trans ?_
      have h1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
      have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
      have hJ := C.norm_eq w.2
      have ha : ‖(1 / 2 : ℂ) • (w.1 + C.J w.2)‖ ≤ ‖w‖ := by
        rw [norm_smul]
        have := norm_add_le w.1 (C.J w.2)
        have hn : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
        rw [hn]
        nlinarith
      have hb : ‖(-(Complex.I / 2)) • (w.1 - C.J w.2)‖ ≤ ‖w‖ := by
        rw [norm_smul]
        have := norm_sub_le w.1 (C.J w.2)
        have hn : ‖-(Complex.I / 2)‖ = 1 / 2 := by simp
        rw [hn]
        nlinarith
      exact (add_le_add ha hb).trans (by linarith))

theorem phi_apply (z : Cx F) :
    phiCLE C z = (Cx.re z + Complex.I • Cx.im z, C.J (Cx.re z) + Complex.I • C.J (Cx.im z)) := rfl

/-- Real points go to the real slice: `Φ (ι f) = (f, J f)`. -/
theorem phi_ι (f : F) : phiCLE C (Cx.ι f) = (f, C.J f) := by
  simp only [phi_apply, Cx.re_ι, Cx.im_ι, map_zero, smul_zero, add_zero]

/-- The complexified conjugation `a + i b ↦ J a + i J b`. -/
def conjC (z : Cx F) : Cx F := Cx.mk (C.J (Cx.re z)) (C.J (Cx.im z))

/-- Under `Φ` the complexified conjugation is the swap. -/
theorem phi_conj (z : Cx F) : phiCLE C (conjC C z) = (phiCLE C z).swap := by
  rw [phi_apply, phi_apply]
  simp only [conjC, Cx.re_mk, Cx.im_mk, C.invol, Prod.swap_prod_mk]

end Generic

section L2

variable {L : ℝ} [Fact (0 < L)]

open PhysicalTensor (L2T)

theorem star_add' (f g : L2T L) : star (f + g) = star f + star g := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (f + g), Lp.coeFn_add (star f) (star g), Lp.coeFn_star f, Lp.coeFn_star g,
    Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.star_apply, Pi.add_apply, star_add]

theorem star_smul' (c : ℂ) (f : L2T L) : star (c • f) = conj c • star f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul (conj c) (star f), Lp.coeFn_star f,
    Lp.coeFn_smul c f] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Complex.star_def]

theorem norm_star' (f : L2T L) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star f)]
  have e : (fun x => ‖(star (⇑f)) x‖) = fun x => ‖f x‖ := funext fun x => norm_star (f x)
  rw [← eLpNorm_norm (star (⇑f)), e, eLpNorm_norm]
  all_goals first
    | exact Lp.aestronglyMeasurable f
    | exact continuous_star.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)

/-- The pointwise conjugation on `L²(𝕋_L)` as a conjugation. -/
def starConj : Conj (L2T L) where
  J := { toFun := star, map_add' := star_add', map_smul' := star_smul' }
  invol := star_star
  norm_eq := norm_star'

/-- **The discriminant on `Cx(L²(𝕋_L)) × ℂ`**: `cxDisc ∘ Φ` is complex analytic everywhere and equals the physical
discriminant at real points `(ι u, z)`. -/
theorem cxDisc_cx (κ : ℝ) :
    AnalyticOnNhd ℂ (fun q : Cx (L2T L) × ℂ =>
      ComplexifiedDiscriminant.cxDisc κ (phiCLE starConj q.1).1 (phiCLE starConj q.1).2 q.2) univ ∧
    ∀ (u : L2T L) (z : ℂ), ComplexifiedDiscriminant.cxDisc κ (phiCLE starConj (Cx.ι u)).1
      (phiCLE starConj (Cx.ι u)).2 z = L2SpatialTransfer.discriminant κ u z := by
  refine ⟨fun q _ => ?_, fun u z => ?_⟩
  · let P : Cx (L2T L) →L[ℂ] L2T L × L2T L := (phiCLE starConj).toContinuousLinearMap
    let g : Cx (L2T L) × ℂ →L[ℂ] L2T L × L2T L × ℂ :=
      ((ContinuousLinearMap.fst ℂ (L2T L) (L2T L)).comp (P.comp (ContinuousLinearMap.fst ℂ (Cx (L2T L)) ℂ))).prod
        (((ContinuousLinearMap.snd ℂ (L2T L) (L2T L)).comp
          (P.comp (ContinuousLinearMap.fst ℂ (Cx (L2T L)) ℂ))).prod (ContinuousLinearMap.snd ℂ (Cx (L2T L)) ℂ))
    change AnalyticAt ℂ ((fun p : L2T L × L2T L × ℂ => ComplexifiedDiscriminant.cxDisc κ p.1 p.2.1 p.2.2) ∘ g) q
    exact (ComplexifiedDiscriminant.analyticOnNhd_cxDisc κ (g q) (mem_univ _)).comp (g.analyticAt q)
  · rw [phi_ι]
    exact ComplexifiedDiscriminant.cxDisc_star κ u z

end L2

end QuantumNLS.ComplexifiedConjugation

#print axioms QuantumNLS.ComplexifiedConjugation.phiCLE
#print axioms QuantumNLS.ComplexifiedConjugation.phi_ι
#print axioms QuantumNLS.ComplexifiedConjugation.phi_conj
#print axioms QuantumNLS.ComplexifiedConjugation.starConj
#print axioms QuantumNLS.ComplexifiedConjugation.cxDisc_cx
