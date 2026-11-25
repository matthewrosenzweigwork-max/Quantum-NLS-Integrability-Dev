import Mathlib
import QuantumNLS.RiccatiPicardBranch
import QuantumNLS.ComplexifiedSobolevField

/-!
# R-3FEAD88B stage (b): first-derivative bounds on the real slice (`RiccatiC1`)

Frozen inputs (imported, not edited): `RiccatiPicardBranch` (`riccati_local_analytic_branch`, a PROVED
frozen theorem, used as given), `ComplexifiedSobolevField` (`jEll`, `norm_jEll`).

Proved here, for a complex normed space `E` and a complex-differentiable `F : E × E → G`:
* `norm_fderiv_le_of_circle`: one-variable Cauchy estimate along a complex line, from
  `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`: `‖fderiv F p₀ d‖ ≤ C / R` if `‖F (p₀ + t • d)‖ ≤ C` on `|t| = R`.
* `norm_fderiv_le_of_ball`: directional bound `‖fderiv F p₀ d‖ ≤ C ‖d‖ / ρ` from a sup bound on the ball of radius `ρ`.
* `slice_hasFDerivAt`: for a real-linear isometry `J` (here `J = jEll` on `Ell2`), the map `φ ↦ F (φ, J φ)` has
  Fréchet derivative `L` at `φ₀` (`HasFDerivAt` over `ℝ`), with the printed real-slice formula
  `L h = D_u F[h] + D_v F[J h]`, where `D_u F[h] = fderiv F p (h, 0)` and `D_v F[k] = fderiv F p (0, k)`.
* `slice_deriv_bound`: the locally uniform bound `‖L h‖ ≤ (4 C / ρ) ‖h‖` on the half-ball around `p₀`.
* `riccati_C1_slice` (`Ell2` instance, `J = jR = jEll`): the same statement for `E = Ell2`.
* `riccati_branch_slice`: the frozen branch `riccati_local_analytic_branch` gives an analytic `ψ` near any admissible `p₀`,
  and its real-slice derivative at `φ₀` with `p₀ = (φ₀, jEll φ₀)` exists with the printed formula.

No `sorry`, `admit`, or custom axioms. The remainder bound itself (the `O(|z|^{-M-1})` clause for the first
derivative of the expansion) is not in this module; it needs the uniform holomorphic branch of stage (c).
-/

open Set Metric Filter Topology
open ComplexConjugate

namespace QuantumNLS.RiccatiC1

section Cauchy

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- One-variable Cauchy estimate along a complex line through `p₀` in direction `d`. -/
theorem norm_fderiv_le_of_circle {F : E → G} {p₀ d : E} {R C : ℝ} (hR : 0 < R)
    (hdiff : ∀ t : ℂ, ‖t‖ ≤ R → DifferentiableAt ℂ F (p₀ + t • d))
    (hC : ∀ t : ℂ, ‖t‖ = R → ‖F (p₀ + t • d)‖ ≤ C) :
    ‖fderiv ℂ F p₀ d‖ ≤ C / R := by
  set g : ℂ → G := fun t => F (p₀ + t • d) with hg
  have hgd : ∀ t : ℂ, ‖t‖ ≤ R → DifferentiableAt ℂ g t := fun t ht =>
    (hdiff t ht).comp t (((differentiableAt_id).smul_const d).const_add p₀)
  have hDC : DiffContOnCl ℂ g (ball (0 : ℂ) R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) hR.ne']
    intro t ht
    exact (hgd t (by simpa [mem_closedBall, dist_zero_right] using ht)).differentiableWithinAt
  have hCs : ∀ t ∈ sphere (0 : ℂ) R, ‖g t‖ ≤ C := fun t ht =>
    hC t (by simpa [mem_sphere_zero_iff_norm] using ht)
  have h1 := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hDC hCs
  have hF0 : HasFDerivAt F (fderiv ℂ F p₀) (p₀ + (0 : ℂ) • d) :=
    by simpa using (hdiff 0 (by simp [hR.le])).hasFDerivAt
  have hl : HasDerivAt (fun t : ℂ => p₀ + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const d).const_add p₀
  have hd : HasDerivAt g (fderiv ℂ F p₀ d) 0 := by
    have h2 := hF0.comp_hasDerivAt (0 : ℂ) hl
    exact h2
  rw [hd.deriv] at h1
  exact h1

/-- Directional bound from a sup bound on the closed ball of radius `ρ`. -/
theorem norm_fderiv_le_of_ball {F : E → G} {p₀ : E} {ρ C : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ q : E, dist q p₀ ≤ ρ → DifferentiableAt ℂ F q)
    (hbd : ∀ q : E, dist q p₀ ≤ ρ → ‖F q‖ ≤ C) (d : E) :
    ‖fderiv ℂ F p₀ d‖ ≤ C * ‖d‖ / ρ := by
  by_cases hd0 : d = 0
  · subst hd0
    simp
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd0
  set R : ℝ := ρ / ‖d‖ with hR_def
  have hR : 0 < R := div_pos hρ hdn
  have hdist : ∀ t : ℂ, ‖t‖ ≤ R → dist (p₀ + t • d) p₀ ≤ ρ := by
    intro t ht
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul]
    have : ‖t‖ * ‖d‖ ≤ R * ‖d‖ := mul_le_mul_of_nonneg_right ht hdn.le
    have hRd : R * ‖d‖ = ρ := by
      rw [hR_def]; field_simp
    calc ‖t‖ * ‖d‖ ≤ R * ‖d‖ := this
      _ = ρ := hRd
  have key := norm_fderiv_le_of_circle (F := F) (p₀ := p₀) (d := d) (R := R) (C := C) hR
    (fun t ht => hdiff _ (hdist t ht))
    (fun t ht => hbd _ (hdist t (le_of_eq ht)))
  calc ‖fderiv ℂ F p₀ d‖ ≤ C / R := key
    _ = C * ‖d‖ / ρ := by
      rw [hR_def]
      field_simp

end Cauchy

section Slice

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The real-slice derivative `L` of `φ ↦ F (φ, J φ)` at `φ₀`, as a real Fréchet derivative. -/
theorem slice_hasFDerivAt (J : E →L[ℝ] E) (F : E × E → G) (φ₀ : E)
    (hF : DifferentiableAt ℂ F (φ₀, J φ₀)) :
    HasFDerivAt (fun φ : E => F (φ, J φ))
      (((fderiv ℂ F (φ₀, J φ₀)).restrictScalars ℝ).comp
        ((ContinuousLinearMap.id ℝ E).prod J)) φ₀ := by
  have hΦ : HasFDerivAt (fun φ : E => (φ, J φ)) ((ContinuousLinearMap.id ℝ E).prod J) φ₀ :=
    (hasFDerivAt_id φ₀).prodMk J.hasFDerivAt
  have hFr : HasFDerivAt F ((fderiv ℂ F (φ₀, J φ₀)).restrictScalars ℝ) (φ₀, J φ₀) :=
    hF.hasFDerivAt.restrictScalars ℝ
  exact hFr.comp φ₀ hΦ

/-- The real-slice formula `L h = D_u F[h] + D_v F[J h]` (the printed `D_φF[h] = D_uF[h] + D_vF[h̄]`). -/
theorem slice_deriv_formula (J : E →L[ℝ] E) (F : E × E → G) (p : E × E) (h : E) :
    (((fderiv ℂ F p).restrictScalars ℝ).comp ((ContinuousLinearMap.id ℝ E).prod J)) h
      = fderiv ℂ F p (h, 0) + fderiv ℂ F p (0, J h) := by
  show fderiv ℂ F p (h, J h) = fderiv ℂ F p (h, 0) + fderiv ℂ F p (0, J h)
  have hsplit : ((h, J h) : E × E) = (h, 0) + (0, J h) := Prod.ext (by simp) (by simp)
  rw [hsplit, map_add]

/-- Locally uniform first-derivative bound on the real slice: if `F` is complex-differentiable on the closed ball of
radius `ρ` about `p₀` and bounded there by `C`, and `‖(φ₀, J φ₀) − p₀‖ ≤ ρ/2` with `J` isometric, then the slice
derivative exists and `‖L h‖ ≤ (4 C / ρ) ‖h‖`. -/
theorem slice_deriv_bound (J : E →L[ℝ] E) (hJ : ∀ x : E, ‖J x‖ = ‖x‖)
    (F : E × E → G) {p₀ : E × E} {ρ C : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ q : E × E, dist q p₀ ≤ ρ → DifferentiableAt ℂ F q)
    (hbd : ∀ q : E × E, dist q p₀ ≤ ρ → ‖F q‖ ≤ C) (φ₀ : E)
    (hbase : dist (φ₀, J φ₀) p₀ ≤ ρ / 2) :
    HasFDerivAt (fun φ : E => F (φ, J φ))
        (((fderiv ℂ F (φ₀, J φ₀)).restrictScalars ℝ).comp
          ((ContinuousLinearMap.id ℝ E).prod J)) φ₀
      ∧ (∀ h : E, (((fderiv ℂ F (φ₀, J φ₀)).restrictScalars ℝ).comp
            ((ContinuousLinearMap.id ℝ E).prod J)) h
          = fderiv ℂ F (φ₀, J φ₀) (h, 0) + fderiv ℂ F (φ₀, J φ₀) (0, J h))
      ∧ (∀ h : E, ‖(((fderiv ℂ F (φ₀, J φ₀)).restrictScalars ℝ).comp
            ((ContinuousLinearMap.id ℝ E).prod J)) h‖ ≤ 4 * C / ρ * ‖h‖) := by
  set p : E × E := (φ₀, J φ₀) with hp
  have hball : ∀ q : E × E, dist q p ≤ ρ / 2 → dist q p₀ ≤ ρ := by
    intro q hq
    have := dist_triangle q p p₀
    linarith
  have hF : DifferentiableAt ℂ F p := hdiff p (by linarith [hbase, hball])
  have hsl := slice_hasFDerivAt J F φ₀ hF
  have hd : ∀ q : E × E, dist q p ≤ ρ / 2 → DifferentiableAt ℂ F q :=
    fun q hq => hdiff q (hball q hq)
  have hb : ∀ q : E × E, dist q p ≤ ρ / 2 → ‖F q‖ ≤ C :=
    fun q hq => hbd q (hball q hq)
  have hρ2 : 0 < ρ / 2 := by linarith
  have hfd : ∀ d : E × E, ‖fderiv ℂ F p d‖ ≤ C * ‖d‖ / (ρ / 2) :=
    fun d => norm_fderiv_le_of_ball hρ2 hd hb d
  refine ⟨hsl, fun h => slice_deriv_formula J F p h, fun h => ?_⟩
  rw [slice_deriv_formula J F p h]
  have h1 : ‖fderiv ℂ F p (h, 0)‖ ≤ C * ‖h‖ / (ρ / 2) := by
    have := hfd (h, 0)
    simpa [Prod.norm_def, norm_zero] using this
  have h2 : ‖fderiv ℂ F p (0, J h)‖ ≤ C * ‖h‖ / (ρ / 2) := by
    have := hfd (0, J h)
    simpa [Prod.norm_def, norm_zero, hJ h] using this
  have hsum := norm_add_le (fderiv ℂ F p (h, 0)) (fderiv ℂ F p (0, J h))
  have hCsum : C * ‖h‖ / (ρ / 2) + C * ‖h‖ / (ρ / 2) = 4 * C / ρ * ‖h‖ := by
    field_simp
    ring
  linarith [hsum, h1, h2, hCsum]

end Slice

section Ell2

open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField

/-- The conjugation `φ ↦ jEll φ` on `Ell2` as a real-linear isometry `jR`. -/
noncomputable def jR : Ell2 →L[ℝ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := jEll
      map_add' := fun x y => by
        ext k
        simp
      map_smul' := fun r x => by
        ext k
        simp [Complex.real_smul] }
    1 (fun x => by simp [norm_jEll])

theorem jR_apply (x : Ell2) : jR x = jEll x := rfl

theorem norm_jR (x : Ell2) : ‖jR x‖ = ‖x‖ := by
  rw [jR_apply, norm_jEll]

/-- **Stage (b) main statement on `Ell2 × Ell2`.** Locally uniform real-slice first-derivative bound for a
complex-differentiable `F`, with `J = jR`. -/
theorem riccati_C1_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (F : Ell2 × Ell2 → G) {p₀ : Ell2 × Ell2} {ρ C : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ q : Ell2 × Ell2, dist q p₀ ≤ ρ → DifferentiableAt ℂ F q)
    (hbd : ∀ q : Ell2 × Ell2, dist q p₀ ≤ ρ → ‖F q‖ ≤ C) (φ₀ : Ell2)
    (hbase : dist (φ₀, jR φ₀) p₀ ≤ ρ / 2) :
    HasFDerivAt (fun φ : Ell2 => F (φ, jR φ))
        (((fderiv ℂ F (φ₀, jR φ₀)).restrictScalars ℝ).comp
          ((ContinuousLinearMap.id ℝ Ell2).prod jR)) φ₀
      ∧ (∀ h : Ell2, (((fderiv ℂ F (φ₀, jR φ₀)).restrictScalars ℝ).comp
            ((ContinuousLinearMap.id ℝ Ell2).prod jR)) h
          = fderiv ℂ F (φ₀, jR φ₀) (h, 0) + fderiv ℂ F (φ₀, jR φ₀) (0, jR h))
      ∧ (∀ h : Ell2, ‖(((fderiv ℂ F (φ₀, jR φ₀)).restrictScalars ℝ).comp
            ((ContinuousLinearMap.id ℝ Ell2).prod jR)) h‖ ≤ 4 * C / ρ * ‖h‖) :=
  slice_deriv_bound jR norm_jR F hρ hdiff hbd φ₀ hbase

/-- The frozen branch `riccati_local_analytic_branch` (used as given) gives an analytic `ψ` at `p₀`; its real-slice
derivative at `φ₀` (with `p₀ = (φ₀, jEll φ₀)`) exists with the printed formula. -/
theorem riccati_branch_slice {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ}
    (hz : 0 < z.im) (κ β : ℝ) (hβ : 0 < β)
    (hκ : 16 * |κ| * QuantumNLS.RiccatiSobolevBanach.Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2)
    (p₀ : Ell2 × Ell2) (hp0u : ‖p₀.1‖ < β) (hp0v : ‖p₀.2‖ < β) :
    ∃ ψ : Ell2 × Ell2 → Ell2, AnalyticAt ℂ ψ p₀ ∧
      ∀ φ₀ : Ell2, p₀ = (φ₀, jR φ₀) →
        ∃ Lr : Ell2 →L[ℝ] Ell2, HasFDerivAt (fun φ : Ell2 => ψ (φ, jR φ)) Lr φ₀
          ∧ ∀ h : Ell2, Lr h = fderiv ℂ ψ p₀ (h, 0) + fderiv ℂ ψ p₀ (0, jR h) := by
  obtain ⟨ψ, hψan, -⟩ := QuantumNLS.RiccatiPicardBranch.riccati_local_analytic_branch hL ha hz κ β hβ
    hκ p₀ hp0u hp0v
  refine ⟨ψ, hψan, fun φ₀ hp => ?_⟩
  have hdiff : DifferentiableAt ℂ ψ (φ₀, jR φ₀) := by
    rw [← hp]
    exact hψan.differentiableAt
  refine ⟨_, slice_hasFDerivAt jR ψ φ₀ hdiff, fun h => ?_⟩
  subst hp
  exact slice_deriv_formula jR ψ (φ₀, jR φ₀) h

end Ell2

end QuantumNLS.RiccatiC1

#print axioms QuantumNLS.RiccatiC1.norm_fderiv_le_of_circle
#print axioms QuantumNLS.RiccatiC1.norm_fderiv_le_of_ball
#print axioms QuantumNLS.RiccatiC1.slice_hasFDerivAt
#print axioms QuantumNLS.RiccatiC1.slice_deriv_formula
#print axioms QuantumNLS.RiccatiC1.slice_deriv_bound
#print axioms QuantumNLS.RiccatiC1.norm_jR
#print axioms QuantumNLS.RiccatiC1.riccati_C1_slice
#print axioms QuantumNLS.RiccatiC1.riccati_branch_slice
