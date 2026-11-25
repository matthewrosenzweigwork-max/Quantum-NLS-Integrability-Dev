import Mathlib
import QuantumNLS.FunctionalLinearization

/-!
# PROP-014 `lem:A4-functional-linearization`: the integral-over-parameter clause

Source: `source/chapters/propagation/spectral_calculus.tex`, lines 497-598, label
`lem:A4-functional-linearization`, `\ReportID{PROP-014}`: the last sentence of the statement and
the last paragraph of the proof ("the same bound holds for `H_N = N ∫ F_θ(B_θ) dν(θ)` over a finite
measure space of such functions whose spectral coordinates commute across parameters, with
`C = ν(Θ) sup_θ C_F(F_θ)`; `C_F` is uniform when the cube, `b_θ` and finitely many derivatives of a
smooth extension of `F_θ` are uniformly bounded").  This module imports the frozen module
`QuantumNLS.FunctionalLinearization` (single-`F` estimate `functional_linearization`, `time_bound`,
`Phi_remC_bound`, `CF`, `CF_le_seminorms`, ...) read-only and closes the clause it listed as not
formalised.

## Setting (all data explicit)
`(Θ, ν)` a finite measure space; a common compact `K ⊂ ℝ^d`; for each `θ` a joint functional
calculus `Φ θ : C(K,ℂ) →⋆ₐ[ℂ] B(H)` (`B_{θ,j} := Φ θ (coordC j)`; `exists_functional_calculus`
produces one for any commuting tuple, and any compact `K' ⊇ K` gives the same operators).  Mutual
commutation of the spectral coordinates across parameters is the hypothesis
`hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j'))`.
* `HnlP ν Φ F hF N := N • ∫ θ, Fop (Φ θ) (F θ) _ ∂ν`   (`H_N = N ∫ F_θ(B_θ) dν`, Bochner integral
  in the Banach algebra `B(H)`),
* `HlinP ν Φ F b N := N • ∫ θ, LinOp (Φ θ) (F θ) (b θ) ∂ν`,
  `LinOp Φ F b = ∑_j ∂_jF(b) Φ(x_j)` (`H_N^lin = N ∫ ∑_j ∂_jF_θ(b_θ) B_{θ,j} dν`).
The two integrands are required to be Bochner integrable as explicit hypotheses `hA`, `hL`.

## Main results (all proved)
* `functional_linearization_param` (`F_θ` `C^∞` with compact support, `CF(F_θ) ≤ Cb` for all `θ`,
  `|t| ≤ T`, unit `ψ` with `‖(B_{θ,j} − b_{θ,j})ψ‖ ≤ δ` for all `θ, j`, `‖[B_{θ,j}, J]‖ ≤ C_J/N`):
  `|⟨e^{-itH_N}ψ, J e^{-itH_N}ψ⟩ − ⟨e^{-itH^lin}ψ, J e^{-itH^lin}ψ⟩| ≤ ν(Θ) · Cb · T · C_J · δ`
  — the printed `C = ν(Θ) sup_θ C_F(F_θ)`.
* `functional_linearization_param_sup`: the same bound for `⨆ t ∈ [-T,T]` (Terra qualification (c)).
* `functional_linearization_param_seminorm`: the constant is `ν(Θ) · C₀ · M` where `M` bounds a
  fixed finite sup of Schwartz seminorms of all `F_θ` and `C₀` depends only on `d`.
* `functional_linearization_param_family` (Terra qualification (b), family uniformity): for a
  fixed compact `Q` inside a fixed open `U` there is `C₁(Q,U,d)` such that, for all families with
  `‖D^i F_θ‖ ≤ M` on `U` for `i ≤ m(d)`, the bound holds with `ν(Θ) · C₀ C₁ M`; the extension is the
  *canonical* `χ F_θ` with a cutoff `χ` depending only on `(Q,U)` (`exists_cutoff`,
  `sup_seminorm_cutoff_le`, Leibniz `norm_iteratedFDeriv_mul_le`, `CF_le_seminorms`).  `H_N`,
  `H^lin` are built from the original `F_θ` (they coincide with those of `χ F_θ` because
  `χ = 1` near `Q ⊇ K ∪ {b_θ}`).
* Terra qualification (a), `b ∈ cube`: `infDist_le_deviation` proves `dist(b_θ, K) ≤ √d δ`
  from `‖(B_j − b_j)ψ‖ ≤ δ` (via `Φ(∑(x_j − b_j)²) = ∑ (B_j − b_j)²`); in
  `functional_linearization_param_family` the hypothesis `hQK` (`Q` contains the closed
  `√d δ`-neighbourhood of `K`) therefore *derives* `b_θ ∈ Q`; and `mem_of_deviation_tendsto` shows
  `b ∈ K` exactly when `δ_N → 0` (same compact `K`, closed).  For a single fixed `N` with `δ > 0`
  `b` need not lie in `K`, so some margin hypothesis such as `hQK` is genuinely needed.
* Support lemmas: `commute_images` (`Φ₁(g₁)` commutes with `Φ₂(g₂)` once the coordinates do, by
  Stone–Weierstrass and `Phi_mem_centralizer`), `commute_integral_left/right`, `integral_commEv`,
  `isSelfAdjoint_integral`, `Fop_sub_LinOp`.

## Proof route
`G_θ := F_θ(B_θ) − ∑_j ∂_jF_θ(b_θ) B_{θ,j}`, `D := H_N − H^lin = N ∫ G_θ dν` (linearity of the
Bochner integral).  `D` and `H^lin` are self-adjoint (`isSelfAdjoint_integral`), commute with each
other, and each `B_{θ,j} − b_{θ,j}` commutes with both (`commute_images` makes every `G_θ`, `L_θ`
commute with every coordinate of every other parameter; `commute_integral_left/right` pass this
through the integral).  Hence `e^{-itH_N} = e^{-isD} e^{-itH^lin}` factorisation and the deviation
hypothesis is preserved along `φ(s) = e^{-isD}e^{-itH^lin}ψ` exactly as in the single-`F` `time_bound`.
Pointwise, `G_θ = Φ_θ(rem F_θ b_θ) + const·1` (`Fop_sub_LinOp`), and `Phi_remC_bound` gives
`|⟨φ,[G_θ,J]φ⟩| ≤ Cb δ C_J/N` (the constant commutes with `J`).  `integral_commEv` identifies
`⟨φ,[∫G_θ,J]φ⟩ = ∫⟨φ,[G_θ,J]φ⟩`, `norm_integral_le_of_norm_le_const` gives the factor
`ν(Θ)`, the prefactor `N` cancels `1/N`, and `time_bound` supplies the factor `T`.

## Gaps and exact deviations (nothing hidden)
* `hA`, `hL` (Bochner integrability of the two operator-valued integrands) are explicit hypotheses
  rather than derived from measurability of `θ ↦ Φ θ`; strong measurability of `Φ θ g` is a
  property of the physical parameter family, not of the abstract functional calculus.
* One common compact `K` and `Φ θ` per `θ`; `F_θ` must be globally `C^∞` (compactly supported in
  `functional_linearization_param`, global with derivative bounds on `U` in the `_family` form).
  `b_θ ∈ Q` in the `_family` form is derived from `hQK`, not assumed.
* The family constants `s`, `C₀` depend only on `d`; `C₁` depends on `(Q, U, d)` through `χ`
  (it is not given in closed form).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

section FLParamPart1

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Comm

variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem adjoin_coord_top :
    (StarAlgebra.adjoin ℂ (Set.range (coordC (K := K)))).topologicalClosure = ⊤ := by
  have hsep : (StarAlgebra.adjoin ℂ (Set.range (coordC (K := K)))).SeparatesPoints := by
    intro x y hxy
    have : ∃ j, (x : EuclideanSpace ℝ (Fin d)) j ≠ (y : EuclideanSpace ℝ (Fin d)) j := by
      by_contra hcon
      push_neg at hcon
      exact hxy (Subtype.ext (by ext j; exact hcon j))
    obtain ⟨j, hj⟩ := this
    refine ⟨_, ⟨coordC j, StarAlgebra.subset_adjoin ℂ _ ⟨j, rfl⟩, rfl⟩, ?_⟩
    simpa [coordC, liftC] using hj
  exact ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep

/-- If the coordinates' images commute (with a set and its star), so do all images. -/
theorem Phi_mem_centralizer (Ψ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : Set (H →L[ℂ] H))
    (h : ∀ j, Ψ (coordC j) ∈ StarSubalgebra.centralizer ℂ T) (g : C(K, ℂ)) :
    Ψ g ∈ StarSubalgebra.centralizer ℂ T := by
  let S : StarSubalgebra ℂ C(K, ℂ) := (StarSubalgebra.centralizer ℂ T).comap Ψ
  have hle : StarAlgebra.adjoin ℂ (Set.range (coordC (K := K))) ≤ S := by
    rw [StarAlgebra.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    exact h j
  have hcl : IsClosed (S : Set C(K, ℂ)) := by
    have : (S : Set C(K, ℂ)) = Ψ ⁻¹' (T ∪ star T).centralizer := rfl
    rw [this]
    exact (Set.isClosed_centralizer _).preimage (Phi_continuous Ψ)
  have h2 := StarSubalgebra.topologicalClosure_minimal hle hcl
  rw [adjoin_coord_top] at h2
  exact h2 StarSubalgebra.mem_top

/-- Commutation of the coordinate operators (at two parameter values) implies commutation of
all functions of them. -/
theorem commute_images (Φ1 Φ2 : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (h : ∀ j j', Commute (Φ1 (coordC j)) (Φ2 (coordC j'))) (g1 g2 : C(K, ℂ)) :
    Commute (Φ1 g1) (Φ2 g2) := by
  have hsa : ∀ (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) j, star (Φ (coordC j)) = Φ (coordC j) := fun Φ j => by
    rw [← map_star]; congr 1
    exact (isSelfAdjoint_coordC (K := K) j).star_eq
  -- step 1: every `Φ2 g` commutes with every `Φ1 (coordC j)`
  have step1 : ∀ j g, Commute (Φ2 g) (Φ1 (coordC j)) := by
    intro j g
    have := Phi_mem_centralizer Φ2 {Φ1 (coordC j)} (fun j' => by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨(h j j').eq, ?_⟩
      rw [hsa Φ1 j]; exact (h j j').eq) g
    rw [StarSubalgebra.mem_centralizer_iff] at this
    exact (this _ rfl).1.symm
  have := Phi_mem_centralizer Φ1 {Φ2 g2} (fun j => by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine ⟨(step1 j g2).eq.symm.symm, ?_⟩
    rw [← map_star]
    exact (step1 j (star g2)).eq) g1
  rw [StarSubalgebra.mem_centralizer_iff] at this
  exact (this _ rfl).1.symm

end Comm

end QuantumNLS.FunctionalLinearization

end

end FLParamPart1

section FLParamPart2

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace ContDiff

noncomputable section

namespace QuantumNLS.FunctionalLinearization

section Integral

variable {Θ : Type*} [MeasurableSpace Θ] {ν : Measure Θ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem commute_integral_right {X : H →L[ℂ] H} {f : Θ → H →L[ℂ] H} (hf : Integrable f ν)
    (h : ∀ θ, Commute X (f θ)) : Commute X (∫ θ, f θ ∂ν) := by
  have h1 := ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.mul ℂ (H →L[ℂ] H) X) hf
  have h2 := ContinuousLinearMap.integral_comp_comm
    ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip X) hf
  unfold Commute SemiconjBy
  have e1 : X * ∫ θ, f θ ∂ν = ∫ θ, X * f θ ∂ν := h1.symm
  have e2 : (∫ θ, f θ ∂ν) * X = ∫ θ, f θ * X ∂ν := h2.symm
  rw [e1, e2]
  congr 1
  funext θ
  exact (h θ).eq

theorem commute_integral_left {X : H →L[ℂ] H} {f : Θ → H →L[ℂ] H} (hf : Integrable f ν)
    (h : ∀ θ, Commute (f θ) X) : Commute (∫ θ, f θ ∂ν) X :=
  (commute_integral_right hf (fun θ => (h θ).symm)).symm

/-- The linear functional `A ↦ ⟨φ, (A J − J A) φ⟩`. -/
def commEv (J : H →L[ℂ] H) (φ : H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  (innerSL ℂ φ).comp ((ContinuousLinearMap.apply ℂ H φ).comp
    ((ContinuousLinearMap.mul ℂ (H →L[ℂ] H)).flip J - ContinuousLinearMap.mul ℂ (H →L[ℂ] H) J))

theorem commEv_apply (J : H →L[ℂ] H) (φ : H) (A : H →L[ℂ] H) :
    commEv J φ A = ⟪φ, (A * J - J * A) φ⟫_ℂ := by
  simp [commEv]

theorem integral_commEv {f : Θ → H →L[ℂ] H} (hf : Integrable f ν) (J : H →L[ℂ] H) (φ : H) :
    ⟪φ, ((∫ θ, f θ ∂ν) * J - J * (∫ θ, f θ ∂ν)) φ⟫_ℂ =
      ∫ θ, ⟪φ, (f θ * J - J * f θ) φ⟫_ℂ ∂ν := by
  rw [← commEv_apply, ← ContinuousLinearMap.integral_comp_comm (commEv J φ) hf]
  simp only [commEv_apply]

theorem isSelfAdjoint_integral {f : Θ → H →L[ℂ] H} (hf : Integrable f ν)
    (hs : ∀ θ, IsSelfAdjoint (f θ)) : IsSelfAdjoint (∫ θ, f θ ∂ν) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro a b
  have hsym : ∀ θ, ⟪f θ a, b⟫_ℂ = ⟪a, f θ b⟫_ℂ :=
    fun θ => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hs θ) a b
  let Λ : H → H → (H →L[ℂ] H) →L[ℂ] ℂ := fun x y =>
    (innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ H x)
  have hΛ : ∀ x y (A : H →L[ℂ] H), Λ x y A = ⟪y, A x⟫_ℂ := fun x y A => by simp [Λ]
  have h1 : ⟪b, (∫ θ, f θ ∂ν) a⟫_ℂ = ∫ θ, ⟪b, f θ a⟫_ℂ ∂ν := by
    rw [← hΛ, ← ContinuousLinearMap.integral_comp_comm (Λ a b) hf]
    simp only [hΛ]
  have h2 : ⟪a, (∫ θ, f θ ∂ν) b⟫_ℂ = ∫ θ, ⟪a, f θ b⟫_ℂ ∂ν := by
    rw [← hΛ, ← ContinuousLinearMap.integral_comp_comm (Λ b a) hf]
    simp only [hΛ]
  calc ⟪(∫ θ, f θ ∂ν) a, b⟫_ℂ = conj ⟪b, (∫ θ, f θ ∂ν) a⟫_ℂ := (inner_conj_symm _ _).symm
    _ = conj (∫ θ, ⟪b, f θ a⟫_ℂ ∂ν) := by rw [h1]
    _ = ∫ θ, conj ⟪b, f θ a⟫_ℂ ∂ν := (integral_conj).symm
    _ = ∫ θ, ⟪a, f θ b⟫_ℂ ∂ν := by
        congr 1; funext θ; rw [inner_conj_symm, hsym]
    _ = ⟪a, (∫ θ, f θ ∂ν) b⟫_ℂ := h2.symm

end Integral

end QuantumNLS.FunctionalLinearization

end

end FLParamPart2

section FLParamPart3

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section PerTheta

variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- `∑_j ∂_jF(b) B_j`. -/
def LinOp (F : EuclideanSpace ℝ (Fin d) → ℝ) (b : EuclideanSpace ℝ (Fin d)) : H →L[ℂ] H :=
  ∑ j : Fin d, ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) • Φ (coordC j)

theorem isSelfAdjoint_Fop (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : Continuous F) :
    IsSelfAdjoint (Fop Φ F hF) := by
  have : IsSelfAdjoint (liftC (K := K) (fun x => ((F x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hF)) := by
    unfold IsSelfAdjoint
    ext x
    simp [liftC, ContinuousMap.star_apply]
  exact this.map Φ

theorem LinOp_eq (F : EuclideanSpace ℝ (Fin d) → ℝ) (b : EuclideanSpace ℝ (Fin d)) :
    LinOp Φ F b = Φ (∑ j : Fin d, ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) •
      coordC (K := K) j) := by
  simp only [LinOp, map_sum, map_smul]

theorem isSelfAdjoint_LinOp (F : EuclideanSpace ℝ (Fin d) → ℝ) (b : EuclideanSpace ℝ (Fin d)) :
    IsSelfAdjoint (LinOp Φ F b) := by
  rw [LinOp_eq]
  have : IsSelfAdjoint (∑ j : Fin d, ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) •
      coordC (K := K) j) := by
    unfold IsSelfAdjoint
    ext x
    simp [coordC, liftC, ContinuousMap.star_apply, Finset.sum_apply, map_sum]
  exact this.map Φ

/-- `F(B) − ∑ ∂_jF(b)B_j = Φ(Taylor remainder) + const`. -/
theorem Fop_sub_LinOp (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hFc : HasCompactSupport F) (b : EuclideanSpace ℝ (Fin d)) :
    Fop Φ F hF.continuous - LinOp Φ F b =
      Φ (remC (K := K) (schwartzOfReal F hF hFc) b) +
        (((F b : ℝ) : ℂ) - ∑ j : Fin d, ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) *
          ((b j : ℝ) : ℂ)) • (1 : H →L[ℂ] H) := by
  set f := schwartzOfReal F hF hFc with hf
  have hfc : ∀ x, (f : EuclideanSpace ℝ (Fin d) → ℂ) x = ((F x : ℝ) : ℂ) := fun x => rfl
  have hfd : ∀ j : Fin d, fderiv ℝ (f : EuclideanSpace ℝ (Fin d) → ℂ) b (EuclideanSpace.single j 1) =
      ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) := fun j => fderiv_ofReal F hF b _
  have hg : liftC (K := K) (fun x => ((F x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hF.continuous) -
      ∑ j : Fin d, ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) • coordC (K := K) j =
      remC (K := K) f b + (((F b : ℝ) : ℂ) - ∑ j : Fin d,
        ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) * ((b j : ℝ) : ℂ)) • (1 : C(K, ℂ)) := by
    ext x
    simp only [remC, liftC, coordC, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, ContinuousMap.coe_mk, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.one_apply, smul_eq_mul, hfd, hfc, mul_one, mul_sub, Finset.sum_sub_distrib]
    ring
  have h1 : Fop Φ F hF.continuous - LinOp Φ F b = Φ (liftC (K := K) (fun x => ((F x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hF.continuous) - ∑ j : Fin d,
        ((fderiv ℝ F b (EuclideanSpace.single j 1) : ℝ) : ℂ) • coordC (K := K) j) := by
    rw [map_sub, ← LinOp_eq]; rfl
  rw [h1, hg, map_add, map_smul, map_one]

end PerTheta

end QuantumNLS.FunctionalLinearization

end

end FLParamPart3

section FLParamPart4

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Main

variable {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν]
variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- `H_N = N ∫ F_θ(B_θ) dν(θ)` (operator-valued Bochner integral). -/
def HnlP (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, Continuous (F θ)) (N : ℝ) :
    H →L[ℂ] H := (N : ℂ) • ∫ θ, Fop (Φ θ) (F θ) (hF θ) ∂ν

/-- `H_N^lin = N ∫ ∑_j ∂_jF_θ(b_θ) B_{θ,j} dν(θ)`. -/
def HlinP (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (b : Θ → EuclideanSpace ℝ (Fin d)) (N : ℝ) :
    H →L[ℂ] H := (N : ℂ) • ∫ θ, LinOp (Φ θ) (F θ) (b θ) ∂ν

theorem comm_add_smul_one (R J : H →L[ℂ] H) (z : ℂ) :
    (R + z • (1 : H →L[ℂ] H)) * J - J * (R + z • (1 : H →L[ℂ] H)) = R * J - J * R := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  abel

/-- **PROP-014, integral-over-parameter clause.** -/
theorem functional_linearization_param
    (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiff ℝ ∞ (F θ))
    (hFc : ∀ θ, HasCompactSupport (F θ)) (b : Θ → EuclideanSpace ℝ (Fin d))
    (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
    (hA : Integrable (fun θ => Fop (Φ θ) (F θ) (hF θ).continuous) ν)
    (hL : Integrable (fun θ => LinOp (Φ θ) (F θ) (b θ)) ν)
    (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ)
    (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
    (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ θ, CF (schwartzOfReal (F θ) (hF θ) (hFc θ)) ≤ Cb)
    (t T : ℝ) (ht : |t| ≤ T) :
    ‖⟪evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ,
        J (evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ)⟫_ℂ -
      ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖ ≤
      (ν Set.univ).toReal * Cb * T * CJ * δ := by
  have : Nontrivial H := ⟨⟨ψ, 0, fun h => by rw [h] at hψ; simp at hψ⟩⟩
  have hcommI : ∀ θ θ' (g g' : C(K, ℂ)), Commute (Φ θ g) (Φ θ' g') :=
    fun θ θ' g g' => commute_images (Φ θ) (Φ θ') (hcomm θ θ') g g'
  set A : Θ → H →L[ℂ] H := fun θ => Fop (Φ θ) (F θ) (hF θ).continuous with hAdef
  set L : Θ → H →L[ℂ] H := fun θ => LinOp (Φ θ) (F θ) (b θ) with hLdef
  have hG : Integrable (fun θ => A θ - L θ) ν := hA.sub hL
  set D : H →L[ℂ] H := (N : ℂ) • ∫ θ, (A θ - L θ) ∂ν with hDdef
  have hHD : HnlP ν Φ F (fun θ => (hF θ).continuous) N - HlinP ν Φ F b N = D := by
    unfold HnlP HlinP
    rw [← smul_sub, ← integral_sub hA hL]
  have hNsa : IsSelfAdjoint (N : ℂ) := by simp [IsSelfAdjoint]
  have hGs : ∀ θ, IsSelfAdjoint (A θ - L θ) := fun θ =>
    (isSelfAdjoint_Fop (Φ θ) (F θ) (hF θ).continuous).sub (isSelfAdjoint_LinOp (Φ θ) (F θ) (b θ))
  have hDsa : IsSelfAdjoint D := hNsa.smul (isSelfAdjoint_integral hG hGs)
  have hLsa : IsSelfAdjoint (HlinP ν Φ F b N) :=
    hNsa.smul (isSelfAdjoint_integral hL (fun θ => isSelfAdjoint_LinOp (Φ θ) (F θ) (b θ)))
  -- commutation
  have hLim : ∀ θ, ∃ g : C(K, ℂ), L θ = Φ θ g := fun θ => ⟨_, LinOp_eq (Φ θ) (F θ) (b θ)⟩
  have hGim : ∀ θ, ∃ g : C(K, ℂ), A θ - L θ = Φ θ g := by
    intro θ
    obtain ⟨g, hg⟩ := hLim θ
    exact ⟨liftC (fun x => ((F θ x : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hF θ).continuous) - g, by
      rw [map_sub, ← hg]; rfl⟩
  have hGL : ∀ θ θ', Commute (A θ - L θ) (L θ') := by
    intro θ θ'
    obtain ⟨g, hg⟩ := hGim θ
    obtain ⟨g', hg'⟩ := hLim θ'
    rw [hg, hg']; exact hcommI _ _ _ _
  have hGLint : Commute (∫ θ, (A θ - L θ) ∂ν) (∫ θ, L θ ∂ν) :=
    commute_integral_left hG (fun θ => commute_integral_right hL (fun θ' => hGL θ θ'))
  have hcommDH : Commute D (HlinP ν Φ F b N) := (hGLint.smul_left _).smul_right _
  have hXim : ∀ θ j, Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H) =
      Φ θ (coordC j - ((b θ j : ℝ) : ℂ) • (1 : C(K, ℂ))) := fun θ j => by
    rw [map_sub, map_smul, map_one]
  have hXG : ∀ θ j θ', Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (A θ' - L θ') := by
    intro θ j θ'
    obtain ⟨g, hg⟩ := hGim θ'
    rw [hXim, hg]; exact hcommI _ _ _ _
  have hXL : ∀ θ j θ', Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (L θ') := by
    intro θ j θ'
    obtain ⟨g, hg⟩ := hLim θ'
    rw [hXim, hg]; exact hcommI _ _ _ _
  have hXD : ∀ θ j, Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) D :=
    fun θ j => (commute_integral_right hG (fun θ' => hXG θ j θ')).smul_right _
  have hXLin : ∀ θ j, Commute (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H))
      (HlinP ν Φ F b N) :=
    fun θ j => (commute_integral_right hL (fun θ' => hXL θ j θ')).smul_right _
  have hcl : ∀ θ, ∃ R : ℝ, 0 ≤ R ∧ ∀ x : K, ‖(x : EuclideanSpace ℝ (Fin d)) - b θ‖ ≤ R := by
    intro θ
    obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set K)).exists_bound_of_continuousOn
      (f := fun x : K => (x : EuclideanSpace ℝ (Fin d)) - b θ)
      (by fun_prop : Continuous fun x : K => (x : EuclideanSpace ℝ (Fin d)) - b θ).continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x (Set.mem_univ x)).trans (le_max_left _ _)⟩
  have hper : ∀ φ : H, ‖φ‖ ≤ 1 →
      (∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ‖ ≤ δ) → ∀ θ,
      ‖⟪φ, ((A θ - L θ) * J - J * (A θ - L θ)) φ⟫_ℂ‖ ≤ Cb * δ * (CJ / N) := by
    intro φ hφ hX θ
    obtain ⟨R, hR0, hR⟩ := hcl θ
    have hrem := Phi_remC_bound (Φ θ) (schwartzOfReal (F θ) (hF θ) (hFc θ)) (b θ) hR0 hR J φ hφ
      hδ (div_nonneg hCJ hN.le) (hX θ) (hJ θ)
    have e : A θ - L θ = Φ θ (remC (K := K) (schwartzOfReal (F θ) (hF θ) (hFc θ)) (b θ)) +
        (((F θ (b θ) : ℝ) : ℂ) - ∑ j : Fin d, ((fderiv ℝ (F θ) (b θ) (EuclideanSpace.single j 1) : ℝ) : ℂ) *
          ((b θ j : ℝ) : ℂ)) • (1 : H →L[ℂ] H) := Fop_sub_LinOp (Φ θ) (F θ) (hF θ) (hFc θ) (b θ)
    rw [e, comm_add_smul_one]
    refine hrem.trans ?_
    have h0 : 0 ≤ CJ / N := div_nonneg hCJ hN.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCb θ) hδ) h0
  have hmain : ∀ s : ℝ, ‖⟪evol D s (evol (HlinP ν Φ F b N) t ψ), (D * J - J * D)
      (evol D s (evol (HlinP ν Φ F b N) t ψ))⟫_ℂ‖ ≤ (ν Set.univ).toReal * Cb * δ * CJ := by
    intro s
    set w := evol (HlinP ν Φ F b N) t ψ with hw
    set φ := evol D s w with hφ
    have n1 : ‖evol D s‖ ≤ 1 := by unfold evol; exact norm_exp_le hDsa (-s)
    have n2 : ‖evol (HlinP ν Φ F b N) t‖ ≤ 1 := by unfold evol; exact norm_exp_le hLsa (-t)
    have hw1 : ‖w‖ ≤ 1 := by
      calc ‖w‖ ≤ ‖evol (HlinP ν Φ F b N) t‖ * ‖ψ‖ := (evol (HlinP ν Φ F b N) t).le_opNorm ψ
        _ ≤ 1 * 1 := by rw [hψ]; gcongr
        _ = 1 := one_mul 1
    have hφ1 : ‖φ‖ ≤ 1 := by
      calc ‖φ‖ ≤ ‖evol D s‖ * ‖w‖ := (evol D s).le_opNorm w
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    have hX : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ‖ ≤ δ := by
      intro θ j
      have h1 := (commute_evol (hXD θ j) s).eq
      have h2 := (commute_evol (hXLin θ j) t).eq
      have e : (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) φ =
          evol D s (evol (HlinP ν Φ F b N) t
            ((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ)) := by
        rw [hφ, hw]
        calc _ = ((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) * evol D s)
              (evol (HlinP ν Φ F b N) t ψ) := rfl
          _ = (evol D s * (Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)))
              (evol (HlinP ν Φ F b N) t ψ) := by rw [h1]
          _ = evol D s (((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) *
              evol (HlinP ν Φ F b N) t) ψ) := rfl
          _ = _ := by rw [h2]; rfl
      rw [e]
      calc _ ≤ ‖evol D s‖ * ‖evol (HlinP ν Φ F b N) t
            ((Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ)‖ := (evol D s).le_opNorm _
        _ ≤ 1 * (1 * ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖) := by
            gcongr
            exact ((evol (HlinP ν Φ F b N) t).le_opNorm _).trans (by gcongr)
        _ ≤ δ := by simpa using hψδ θ j
    have hDJ : D * J - J * D = (N : ℂ) • ((∫ θ, (A θ - L θ) ∂ν) * J - J * (∫ θ, (A θ - L θ) ∂ν)) := by
      rw [hDdef, smul_mul_assoc, mul_smul_comm, smul_sub]
    have hint := integral_commEv hG J φ
    rw [hDJ, smul_apply, inner_smul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hN, hint]
    have hb := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun θ => ⟪φ, ((A θ - L θ) * J - J * (A θ - L θ)) φ⟫_ℂ) (C := Cb * δ * (CJ / N))
      (Filter.Eventually.of_forall (hper φ hφ1 hX))
    calc N * ‖∫ θ, ⟪φ, ((A θ - L θ) * J - J * (A θ - L θ)) φ⟫_ℂ ∂ν‖ ≤
          N * (Cb * δ * (CJ / N) * (ν Set.univ).toReal) := by gcongr; exact hb
      _ = (ν Set.univ).toReal * Cb * δ * CJ := by field_simp
  have hfin := time_bound hDsa hcommDH ψ J t hmain
  have hH : HnlP ν Φ F (fun θ => (hF θ).continuous) N = D + HlinP ν Φ F b N :=
    sub_eq_iff_eq_add.mp hHD
  rw [hH]
  refine hfin.trans ?_
  have h0 : 0 ≤ (ν Set.univ).toReal * Cb * δ * CJ := by positivity
  calc (ν Set.univ).toReal * Cb * δ * CJ * |t| ≤ (ν Set.univ).toReal * Cb * δ * CJ * T := by gcongr
    _ = (ν Set.univ).toReal * Cb * T * CJ * δ := by ring

end Main

end QuantumNLS.FunctionalLinearization

end

end FLParamPart4

section FLParamPart5

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace ContDiff

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Dist

variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- **`b` is within `√d δ` of the joint spectral set.**  If `‖(B_j − b_j)ψ‖ ≤ δ` for a unit `ψ`,
then `dist(b, K) ≤ √d δ`. -/
theorem infDist_le_deviation (hK : K.Nonempty) (b : EuclideanSpace ℝ (Fin d)) (ψ : H)
    (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hψδ : ∀ j, ‖(Φ (coordC j) - ((b j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ) :
    Metric.infDist b K ≤ Real.sqrt d * δ := by
  set r := Metric.infDist b K with hr
  have hr0 : 0 ≤ r := Metric.infDist_nonneg
  have hrx : ∀ x : K, r ≤ ‖(x : EuclideanSpace ℝ (Fin d)) - b‖ := fun x => by
    rw [← dist_eq_norm]; exact (Metric.infDist_le_dist_of_mem x.2).trans_eq (dist_comm _ _)
  set X : Fin d → H →L[ℂ] H := fun j => Φ (coordC j) - ((b j : ℝ) : ℂ) • (1 : H →L[ℂ] H) with hX
  have hXsa : ∀ j, IsSelfAdjoint (X j) := fun j => by
    have h1 : IsSelfAdjoint (Φ (coordC (K := K) j)) := (isSelfAdjoint_coordC j).map Φ
    have h2 : IsSelfAdjoint (((b j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) :=
      (by simp [IsSelfAdjoint] : IsSelfAdjoint (((b j : ℝ) : ℂ))).smul (IsSelfAdjoint.one _)
    exact h1.sub h2
  let g : C(K, ℂ) := liftC (fun y => ((‖y - b‖ ^ 2 : ℝ) : ℂ)) (by fun_prop)
  let h : C(K, ℂ) := liftC (fun y => ((Real.sqrt (‖y - b‖ ^ 2 - r ^ 2) : ℝ) : ℂ)) (by fun_prop)
  have hgsum : g = ∑ j : Fin d, (coordC (K := K) j - ((b j : ℝ) : ℂ) • (1 : C(K, ℂ))) *
      (coordC j - ((b j : ℝ) : ℂ) • (1 : C(K, ℂ))) := by
    ext x
    simp only [g, liftC, coordC, ContinuousMap.coe_mk, ContinuousMap.sum_apply,
      ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, smul_eq_mul, mul_one, ContinuousMap.coe_sum, Finset.sum_apply]
    rw [EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [PiLp.sub_apply, Complex.norm_real, Real.norm_eq_abs]
    rw [← Complex.ofReal_pow, sq_abs]; push_cast; ring
  have hgh : g = ((r ^ 2 : ℝ) : ℂ) • (1 : C(K, ℂ)) + h * h := by
    ext x
    have := hrx x
    have h0 : 0 ≤ ‖(x : EuclideanSpace ℝ (Fin d)) - b‖ ^ 2 - r ^ 2 := by nlinarith
    simp only [g, h, liftC, ContinuousMap.coe_mk, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.mul_apply, smul_eq_mul, mul_one]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
    push_cast; ring
  have hhsa : IsSelfAdjoint (Φ h) := by
    have : IsSelfAdjoint h := by
      unfold IsSelfAdjoint; ext x; simp [h, liftC, ContinuousMap.star_apply]
    exact this.map Φ
  have e1 : Φ g = ∑ j : Fin d, X j * X j := by
    rw [hgsum, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_mul, map_sub, map_smul, map_one]
  have e2 : Φ g = ((r ^ 2 : ℝ) : ℂ) • (1 : H →L[ℂ] H) + Φ h * Φ h := by
    rw [hgh, map_add, map_smul, map_one, map_mul]
  have hsymm : ∀ (S : H →L[ℂ] H), IsSelfAdjoint S → ∀ a b : H, ⟪S a, b⟫_ℂ = ⟪a, S b⟫_ℂ :=
    fun S hS => ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hS
  have i1 : ⟪ψ, Φ g ψ⟫_ℂ = ((∑ j : Fin d, ‖X j ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1, ContinuousLinearMap.sum_apply, inner_sum]
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change ⟪ψ, X j (X j ψ)⟫_ℂ = _
    rw [← hsymm _ (hXsa j) ψ (X j ψ), inner_self_eq_norm_sq_to_K]
    simp
  have i2 : ⟪ψ, Φ g ψ⟫_ℂ = ((r ^ 2 : ℝ) : ℂ) + ((‖Φ h ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2, ContinuousLinearMap.add_apply, inner_add_right, ContinuousLinearMap.smul_apply,
      inner_smul_right]
    change _ + ⟪ψ, Φ h (Φ h ψ)⟫_ℂ = _
    rw [← hsymm _ hhsa ψ (Φ h ψ), inner_self_eq_norm_sq_to_K]
    simp [hψ]
  have key : r ^ 2 ≤ ∑ j : Fin d, ‖X j ψ‖ ^ 2 := by
    have := i1.symm.trans i2
    have h3 : (r ^ 2 + ‖Φ h ψ‖ ^ 2 : ℝ) = ∑ j : Fin d, ‖X j ψ‖ ^ 2 := by
      exact_mod_cast this.symm
    nlinarith [sq_nonneg ‖Φ h ψ‖]
  have key2 : ∑ j : Fin d, ‖X j ψ‖ ^ 2 ≤ d * δ ^ 2 := by
    calc ∑ j : Fin d, ‖X j ψ‖ ^ 2 ≤ ∑ j : Fin d, δ ^ 2 :=
          Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hψδ j) 2)
      _ = d * δ ^ 2 := by simp
  have : r ^ 2 ≤ (Real.sqrt d * δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; exact key.trans key2
  exact abs_le_of_sq_le_sq' this (by positivity) |>.2

/-- **`b` lies in the closed spectral set once the deviations tend to zero.**  If, for each `n`,
`Φ_n` is a functional calculus on the *same* compact set `K` and `ψ_n` is a unit vector with
`‖(B_{n,j} − b_j)ψ_n‖ ≤ δ_n → 0`, then `b ∈ K`.  (For a single `n`, only `dist(b,K) ≤ √d δ_n` holds,
`infDist_le_deviation`.) -/
theorem mem_of_deviation_tendsto (hK : K.Nonempty) (b : EuclideanSpace ℝ (Fin d))
    (Φs : ℕ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ψ : ℕ → H) (hψ : ∀ n, ‖ψ n‖ = 1) (δ : ℕ → ℝ)
    (hδ0 : ∀ n, 0 ≤ δ n) (hδ : Filter.Tendsto δ Filter.atTop (nhds 0))
    (hdev : ∀ n j, ‖(Φs n (coordC j) - ((b j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) (ψ n)‖ ≤ δ n) :
    b ∈ K := by
  have hKc : IsClosed K := (isCompact_iff_compactSpace.mpr ‹CompactSpace K›).isClosed
  have h1 : ∀ n, Metric.infDist b K ≤ Real.sqrt d * δ n := fun n =>
    infDist_le_deviation (Φs n) hK b (ψ n) (hψ n) (hδ0 n) (hdev n)
  have h2 : Filter.Tendsto (fun n => Real.sqrt d * δ n) Filter.atTop (nhds (Real.sqrt d * 0)) :=
    hδ.const_mul _
  rw [mul_zero] at h2
  have h3 : Metric.infDist b K ≤ 0 := ge_of_tendsto' h2 h1
  exact (hKc.mem_iff_infDist_zero hK).mpr (le_antisymm h3 Metric.infDist_nonneg)

end Dist

section Packaged

/-- **PROP-014 parameter clause with the explicit Schwartz-seminorm constant.**  There are a finite
set `s` of seminorm indices and a constant `C₀` depending only on `d` such that, whenever the
extensions `F_θ` satisfy `sup_{s} seminorm(F_θ) ≤ M` for all `θ`, the estimate of
`functional_linearization_param` holds with `C = ν(Θ) · C₀ M`. -/
theorem functional_linearization_param_seminorm (d : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C0 : ℝ), 0 ≤ C0 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : MeasureTheory.Measure Θ)
        [MeasureTheory.IsFiniteMeasure ν] {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiff ℝ ∞ (F θ))
        (hFc : ∀ θ, HasCompactSupport (F θ)) (b : Θ → EuclideanSpace ℝ (Fin d))
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hA : MeasureTheory.Integrable (fun θ => Fop (Φ θ) (F θ) (hF θ).continuous) ν)
        (hL : MeasureTheory.Integrable (fun θ => LinOp (Φ θ) (F θ) (b θ)) ν)
        (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
        (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ)
        (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hM : ∀ θ, (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ))
          (schwartzOfReal (F θ) (hF θ) (hFc θ)) ≤ M) (t T : ℝ) (ht : |t| ≤ T),
        ‖⟪evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ,
            J (evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ)⟫_ℂ -
          ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖ ≤
          (ν Set.univ).toReal * (C0 * M) * T * CJ * δ := by
  obtain ⟨s, C0, hC0, h⟩ := CF_le_seminorms d
  refine ⟨s, C0, hC0, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF hFc b hcomm hA hL N hN ψ hψ {δ} hδ hψδ
    J {CJ} hCJ hJ {M} hM0 hM t T ht => ?_⟩
  exact functional_linearization_param ν Φ F hF hFc b hcomm hA hL N hN ψ hψ hδ hψδ J hCJ hJ
    (Cb := C0 * M) (mul_nonneg hC0 hM0)
    (fun θ => (h _).trans (mul_le_mul_of_nonneg_left (hM θ) hC0)) t T ht

end Packaged


section SupTime

variable {Θ : Type*} [MeasurableSpace Θ] (ν : MeasureTheory.Measure Θ)
  [MeasureTheory.IsFiniteMeasure ν]
variable {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))

/-- **PROP-014 parameter clause, uniform in time.**  The supremum over `t ∈ [-T, T]` of the
difference of the two Heisenberg expectations is bounded by `ν(Θ) · C · T · C_J · δ`. -/
theorem functional_linearization_param_sup
    (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiff ℝ ∞ (F θ))
    (hFc : ∀ θ, HasCompactSupport (F θ)) (b : Θ → EuclideanSpace ℝ (Fin d))
    (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
    (hA : MeasureTheory.Integrable (fun θ => Fop (Φ θ) (F θ) (hF θ).continuous) ν)
    (hL : MeasureTheory.Integrable (fun θ => LinOp (Φ θ) (F θ) (b θ)) ν)
    (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ)
    (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
    (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
    {Cb : ℝ} (hCb0 : 0 ≤ Cb) (hCb : ∀ θ, CF (schwartzOfReal (F θ) (hF θ) (hFc θ)) ≤ Cb)
    {T : ℝ} (hT : 0 ≤ T) :
    (⨆ t : Set.Icc (-T) T,
      ‖⟪evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ,
          J (evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ)⟫_ℂ -
        ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖) ≤
      (ν Set.univ).toReal * Cb * T * CJ * δ := by
  refine Real.iSup_le (fun t => ?_) ?_
  · refine functional_linearization_param ν Φ F hF hFc b hcomm hA hL N hN ψ hψ hδ hψδ J hCJ hJ
      hCb0 hCb t.1 T ?_
    rw [abs_le]; exact ⟨by linarith [t.2.1], t.2.2⟩
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hCb0) hT) hCJ) hδ

end SupTime

end QuantumNLS.FunctionalLinearization

end

end FLParamPart5

section FLParamPart6

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Cutoff

/-- A canonical cutoff: a `C^∞` compactly supported `χ`, `tsupport χ ⊆ U`, equal to `1` on an open
neighbourhood of the compact set `Q ⊆ U`.  It depends only on `(Q, U)`. -/
theorem exists_cutoff {U Q : Set (EuclideanSpace ℝ (Fin d))} (hU : IsOpen U) (hQ : IsCompact Q)
    (hQU : Q ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∃ W : Set (EuclideanSpace ℝ (Fin d)), IsOpen W ∧ Q ⊆ W ∧ ∀ x ∈ W, χ x = 1 := by
  obtain ⟨L, hLc, hQL, hLU⟩ := exists_compact_between hQ hU hQU
  obtain ⟨L2, hL2c, hQL2, hL2L⟩ := exists_compact_between hQ isOpen_interior hQL
  obtain ⟨χ, hχ, -, hχs, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_interior : IsOpen (interior L)) hL2c.isClosed hL2L
  have hcl : closure (interior L) ⊆ L := closure_minimal interior_subset hLc.isClosed
  have hts : tsupport χ ⊆ L := by
    unfold tsupport; rw [hχs]; exact hcl
  refine ⟨χ, hχ, ?_, hts.trans hLU, interior L2, isOpen_interior, hQL2, fun x hx => ?_⟩
  · exact HasCompactSupport.of_support_subset_isCompact hLc
      (subset_closure.trans hts)
  · exact (hχ1 x).mp (interior_subset hx)

end Cutoff

section SeminormBound

variable {U : Set (EuclideanSpace ℝ (Fin d))}

/-- **Uniform Schwartz-seminorm bound for the canonical extension `χ F`.**  Fix a cutoff `χ` and a
finite set `s` of seminorm indices.  There is a constant `C₁` (depending only on `χ`, `s`) such that
for every smooth `F` whose derivatives up to order `m = max_s n` are bounded by `M` on `U ⊇ tsupport χ`
the seminorms of `χ F` are bounded by `C₁ M`. -/
theorem sup_seminorm_cutoff_le (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (s : Finset (ℕ × ℕ)) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiff ℝ ∞ F) (M : ℝ)
      (hM0 : 0 ≤ M)
      (hFb : ∀ i ≤ s.sup Prod.snd, ∀ x ∈ U, ‖iteratedFDeriv ℝ i F x‖ ≤ M),
      (s.sup (schwartzSeminormFamily ℂ (EuclideanSpace ℝ (Fin d)) ℂ))
        (schwartzOfReal (fun x => χ x * F x) (hχ.mul hF) (hχc.mul_right)) ≤ C1 * M := by
  classical
  obtain ⟨R, hR⟩ := hχc.isCompact.isBounded.exists_norm_le
  set R0 : ℝ := max R 0 with hR0
  have hR0nn : 0 ≤ R0 := le_max_right _ _
  have hBex : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B := by
    intro i
    obtain ⟨C, hC⟩ := (hχc.iteratedFDeriv (𝕜 := ℝ) i).exists_bound_of_continuous
      (hχ.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top))
    exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩
  choose B hB0 hB using hBex
  set c : ℕ × ℕ → ℝ := fun p => R0 ^ p.1 *
    ∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) * B i with hc
  have hc0 : ∀ p, 0 ≤ c p := fun p => by
    rw [hc]; refine mul_nonneg (pow_nonneg hR0nn _) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (Nat.cast_nonneg _) (hB0 i)
  refine ⟨∑ p ∈ s, c p, Finset.sum_nonneg fun p _ => hc0 p, ?_⟩
  intro F hF M hM0 hFb
  have hCnn : 0 ≤ (∑ p ∈ s, c p) * M := mul_nonneg (Finset.sum_nonneg fun p _ => hc0 p) hM0
  refine Seminorm.finset_sup_apply_le hCnn (fun p hp => ?_)
  have hpm : p.2 ≤ s.sup Prod.snd := Finset.le_sup (f := Prod.snd) hp
  have hcle : c p ≤ ∑ p ∈ s, c p := Finset.single_le_sum (f := c) (fun p _ => hc0 p) hp
  refine le_trans ?_ (mul_le_mul_of_nonneg_right hcle hM0)
  show SchwartzMap.seminorm ℂ p.1 p.2 _ ≤ _
  refine SchwartzMap.seminorm_le_bound ℂ p.1 p.2 _ (mul_nonneg (hc0 p) hM0) (fun x => ?_)
  have hprod : ContDiff ℝ ∞ (fun x => χ x * F x) := hχ.mul hF
  have hcoe : ⇑(schwartzOfReal (fun x => χ x * F x) hprod (hχc.mul_right)) =
      Complex.ofRealLI ∘ (fun x => χ x * F x) := rfl
  rw [hcoe, LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI hprod.contDiffAt
    (by exact_mod_cast le_top)]
  by_cases hx : x ∈ tsupport χ
  · have hxR : ‖x‖ ≤ R0 := (hR x hx).trans (le_max_left _ _)
    have hxU : x ∈ U := hχU hx
    have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ∞) hχ hF x (n := p.2)
      (by exact_mod_cast le_top)
    have hsum : ∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i χ x‖ * ‖iteratedFDeriv ℝ (p.2 - i) F x‖ ≤
        (∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) * B i) * M := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : i ≤ p.2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have h1 : ‖iteratedFDeriv ℝ i χ x‖ ≤ B i := hB i x
      have h2 : ‖iteratedFDeriv ℝ (p.2 - i) F x‖ ≤ M :=
        hFb _ ((Nat.sub_le _ _).trans hpm) x hxU
      calc (p.2.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ * ‖iteratedFDeriv ℝ (p.2 - i) F x‖
          ≤ (p.2.choose i : ℝ) * B i * M := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2
              (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
        _ = _ := by ring
    calc ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (fun x => χ x * F x) x‖
        ≤ R0 ^ p.1 * ((∑ i ∈ Finset.range (p.2 + 1), (p.2.choose i : ℝ) * B i) * M) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hxR _) (hL.trans hsum) (norm_nonneg _)
            (pow_nonneg hR0nn _)
      _ = c p * M := by rw [hc]; ring
  · have hxs : x ∉ tsupport (fun x => χ x * F x) := fun h => hx (tsupport_mul_subset_left h)
    have : iteratedFDeriv ℝ p.2 (fun x => χ x * F x) x = 0 := by
      by_contra hne
      exact hxs (support_iteratedFDeriv_subset p.2 hne)
    rw [this, norm_zero, mul_zero]
    exact mul_nonneg (hc0 p) hM0

end SeminormBound

end QuantumNLS.FunctionalLinearization

end

end FLParamPart6

section FLParamPart7

open NormedSpace ComplexConjugate MeasureTheory
open scoped InnerProductSpace ContDiff FourierTransform

noncomputable section

namespace QuantumNLS.FunctionalLinearization

variable {d : ℕ}

section Family

/-- **PROP-014, parameter clause for a uniform family on a fixed neighbourhood.**
There are `s` (finite set of Schwartz seminorm indices) and `C₀ ≥ 0`, depending only on `d`, such that
for every compact `Q ⊆ U` (`U` open) there is `C₁ ≥ 0` depending only on `(Q, U, d)` (through the
canonical cutoff `χ`) with the following property.  Let `F_θ` be smooth on `E` with
`‖D^i F_θ‖ ≤ M` on `U` for `i ≤ m := max_{(k,n)∈s} n`, let `Q ⊇ {x : dist(x,K) ≤ √d δ}` (so that, by
`infDist_le_deviation`, `b_θ ∈ Q` is a *consequence* of the deviation hypothesis), and let the other
hypotheses of `functional_linearization_param` hold.  Then the two Heisenberg expectations differ by
at most `ν(Θ) · (C₀ C₁ M) · T · C_J · δ`.  Here `H_N = N ∫ F_θ(B_θ) dν` uses `F_θ` itself and
`H_N^lin` uses `∂_jF_θ(b_θ)`; the compactly supported extension `χ F_θ` only enters the proof. -/
theorem functional_linearization_param_family (d : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C0 : ℝ), 0 ≤ C0 ∧
      ∀ {U Q : Set (EuclideanSpace ℝ (Fin d))}, IsOpen U → IsCompact Q → Q ⊆ U →
      ∃ C1 : ℝ, 0 ≤ C1 ∧
      ∀ {Θ : Type*} [MeasurableSpace Θ] (ν : MeasureTheory.Measure Θ)
        [MeasureTheory.IsFiniteMeasure ν] {K : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace K]
        {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (Φ : Θ → C(K, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
        (F : Θ → EuclideanSpace ℝ (Fin d) → ℝ) (hF : ∀ θ, ContDiff ℝ ∞ (F θ))
        (b : Θ → EuclideanSpace ℝ (Fin d))
        (hcomm : ∀ θ θ' j j', Commute (Φ θ (coordC j)) (Φ θ' (coordC j')))
        (hA : MeasureTheory.Integrable (fun θ => Fop (Φ θ) (F θ) (hF θ).continuous) ν)
        (hL : MeasureTheory.Integrable (fun θ => LinOp (Φ θ) (F θ) (b θ)) ν)
        (N : ℝ) (hN : 0 < N) (ψ : H) (hψ : ‖ψ‖ = 1) {δ : ℝ} (hδ : 0 ≤ δ)
        (hQK : ∀ x, Metric.infDist x K ≤ Real.sqrt d * δ → x ∈ Q)
        (hψδ : ∀ θ j, ‖(Φ θ (coordC j) - ((b θ j : ℝ) : ℂ) • (1 : H →L[ℂ] H)) ψ‖ ≤ δ)
        (J : H →L[ℂ] H) {CJ : ℝ} (hCJ : 0 ≤ CJ)
        (hJ : ∀ θ j, ‖Φ θ (coordC j) * J - J * Φ θ (coordC j)‖ ≤ CJ / N)
        {M : ℝ} (hM0 : 0 ≤ M)
        (hFb : ∀ θ, ∀ i ≤ s.sup Prod.snd, ∀ x ∈ U, ‖iteratedFDeriv ℝ i (F θ) x‖ ≤ M)
        (t T : ℝ) (ht : |t| ≤ T),
        ‖⟪evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ,
            J (evol (HnlP ν Φ F (fun θ => (hF θ).continuous) N) t ψ)⟫_ℂ -
          ⟪evol (HlinP ν Φ F b N) t ψ, J (evol (HlinP ν Φ F b N) t ψ)⟫_ℂ‖ ≤
          (ν Set.univ).toReal * (C0 * (C1 * M)) * T * CJ * δ := by
  obtain ⟨s, C0, hC0, hCF⟩ := CF_le_seminorms d
  refine ⟨s, C0, hC0, fun {U Q} hU hQ hQU => ?_⟩
  obtain ⟨χ, hχ, hχc, hχU, W, hWo, hQW, hχW⟩ := exists_cutoff hU hQ hQU
  obtain ⟨C1, hC1, hC1b⟩ := sup_seminorm_cutoff_le (U := U) χ hχ hχc hχU s
  refine ⟨C1, hC1, fun {Θ} _ ν _ {K} _ {H} _ _ _ Φ F hF b hcomm hA hL N hN ψ hψ {δ} hδ hQK hψδ
    J {CJ} hCJ hJ {M} hM0 hFb t T ht => ?_⟩
  have : Nontrivial H := ⟨⟨ψ, 0, fun h => by rw [h] at hψ; simp at hψ⟩⟩
  -- the spectral deviation puts `b θ` and `K` inside `Q`
  have hbQ : ∀ θ, b θ ∈ Q := fun θ => hQK _ (by
    by_cases hKne : K.Nonempty
    · exact infDist_le_deviation (Φ θ) hKne (b θ) ψ hψ hδ (hψδ θ)
    · have : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
      subst this
      simp only [Metric.infDist_empty]
      positivity)
  have hKQ : ∀ x ∈ K, x ∈ Q := fun x hx => hQK x (by
    rw [Metric.infDist_zero_of_mem hx]; positivity)
  set F' : Θ → EuclideanSpace ℝ (Fin d) → ℝ := fun θ x => χ x * F θ x with hF'def
  have hF' : ∀ θ, ContDiff ℝ ∞ (F' θ) := fun θ => hχ.mul (hF θ)
  have hF'c : ∀ θ, HasCompactSupport (F' θ) := fun θ => hχc.mul_right
  have hFF' : ∀ θ, ∀ x ∈ W, F' θ x = F θ x := fun θ x hx => by
    simp only [hF'def, hχW x hx, one_mul]
  have hFop : ∀ θ, Fop (Φ θ) (F' θ) (hF' θ).continuous = Fop (Φ θ) (F θ) (hF θ).continuous := by
    intro θ
    unfold Fop
    congr 1
    ext x
    simp only [liftC, ContinuousMap.coe_mk]
    rw [hFF' θ x.1 (hQW (hKQ x.1 x.2))]
  have hLin : ∀ θ, LinOp (Φ θ) (F' θ) (b θ) = LinOp (Φ θ) (F θ) (b θ) := by
    intro θ
    unfold LinOp
    have hev : F' θ =ᶠ[nhds (b θ)] F θ := by
      filter_upwards [hWo.mem_nhds (hQW (hbQ θ))] with y hy using hFF' θ y hy
    rw [hev.fderiv_eq]
  have hHn : HnlP ν Φ F' (fun θ => (hF' θ).continuous) N =
      HnlP ν Φ F (fun θ => (hF θ).continuous) N := by
    unfold HnlP; simp only [hFop]
  have hHl : HlinP ν Φ F' b N = HlinP ν Φ F b N := by
    unfold HlinP; simp only [hLin]
  have hA' : MeasureTheory.Integrable (fun θ => Fop (Φ θ) (F' θ) (hF' θ).continuous) ν := by
    simpa only [hFop] using hA
  have hL' : MeasureTheory.Integrable (fun θ => LinOp (Φ θ) (F' θ) (b θ)) ν := by
    simpa only [hLin] using hL
  have hCb : ∀ θ, CF (schwartzOfReal (F' θ) (hF' θ) (hF'c θ)) ≤ C0 * (C1 * M) := fun θ =>
    (hCF _).trans (mul_le_mul_of_nonneg_left (hC1b (F θ) (hF θ) M hM0 (hFb θ)) hC0)
  have := functional_linearization_param ν Φ F' hF' hF'c b hcomm hA' hL' N hN ψ hψ hδ hψδ J hCJ hJ
    (Cb := C0 * (C1 * M)) (mul_nonneg hC0 (mul_nonneg hC1 hM0)) hCb t T ht
  rwa [hHn, hHl] at this

end Family

end QuantumNLS.FunctionalLinearization

end

end FLParamPart7

/-! Axiom audit: each must print only `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms QuantumNLS.FunctionalLinearization.commute_integral_right
#print axioms QuantumNLS.FunctionalLinearization.commute_integral_left
#print axioms QuantumNLS.FunctionalLinearization.commEv_apply
#print axioms QuantumNLS.FunctionalLinearization.integral_commEv
#print axioms QuantumNLS.FunctionalLinearization.isSelfAdjoint_integral
#print axioms QuantumNLS.FunctionalLinearization.adjoin_coord_top
#print axioms QuantumNLS.FunctionalLinearization.Phi_mem_centralizer
#print axioms QuantumNLS.FunctionalLinearization.commute_images
#print axioms QuantumNLS.FunctionalLinearization.HnlP
#print axioms QuantumNLS.FunctionalLinearization.HlinP
#print axioms QuantumNLS.FunctionalLinearization.comm_add_smul_one
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param
#print axioms QuantumNLS.FunctionalLinearization.LinOp
#print axioms QuantumNLS.FunctionalLinearization.isSelfAdjoint_Fop
#print axioms QuantumNLS.FunctionalLinearization.LinOp_eq
#print axioms QuantumNLS.FunctionalLinearization.isSelfAdjoint_LinOp
#print axioms QuantumNLS.FunctionalLinearization.Fop_sub_LinOp
#print axioms QuantumNLS.FunctionalLinearization.exists_cutoff
#print axioms QuantumNLS.FunctionalLinearization.sup_seminorm_cutoff_le
#print axioms QuantumNLS.FunctionalLinearization.infDist_le_deviation
#print axioms QuantumNLS.FunctionalLinearization.mem_of_deviation_tendsto
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_seminorm
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_sup
#print axioms QuantumNLS.FunctionalLinearization.functional_linearization_param_family
