import Mathlib
import QuantumNLS.LossDyadic

/-!
# R-8C922B25 `lem:loss` (`DYNAMICS_LEMMAS.tex:13`), part 4: multilinear lifting and interpolation

`lift_multilinear`: a continuous multilinear map into `Y^0` whose values on unit vectors lie in the image of the injective embedding with a uniform norm bound
lifts uniquely to a continuous multilinear map into the lower level (printed: "real polarization ... gives a bounded symmetric `j`-linear map
`X^j → Y^q`, equal to the original derivative after embedding into `Y^0`"; here the mixed differences of part 3 already give the multilinear values, so
no polarization is needed, and multilinearity follows from injectivity).
`mult_interp`: the interpolation inequality for multilinear operator norms (printed: "interpolation, evaluation on unit vectors, and then taking the
supremum imply ‖D^jf(x) − D^jf(y)‖_{L^j(X;Y^q)} ≤ C ‖·‖_{L^j(X;Y^0)}^{1−q/q'}").  Mathlib only; no EXT-025 contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option linter.unusedSectionVars false
open scoped ContDiff
open Filter Topology Set Metric
noncomputable section
namespace QuantumNLS.Loss

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

section Mult

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Lifting a continuous multilinear map through an injective embedding, with the norm bound tested on unit vectors. -/
theorem lift_multilinear {j : ℕ} (ι : Z →L[ℝ] F) (hι : Function.Injective ι)
    (Pj : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) F) (B : ℝ)
    (h : ∀ v : Fin j → X, (∀ i, ‖v i‖ ≤ 1) → ∃ L : Z, ι L = Pj v ∧ ‖L‖ ≤ B) :
    ∃ T : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z, (∀ v, ι (T v) = Pj v) ∧ ‖T‖ ≤ B := by
  have hB : 0 ≤ B := by
    obtain ⟨L, -, hL⟩ := h 0 (fun i => by simp)
    exact (norm_nonneg _).trans hL
  have hex : ∀ v : Fin j → X, ∃ L : Z, ι L = Pj v ∧ ‖L‖ ≤ B * ∏ i, ‖v i‖ := by
    intro v
    by_cases hz : ∀ i, v i ≠ 0
    · have hn : ∀ i, ‖v i‖ ≠ 0 := fun i => norm_ne_zero_iff.2 (hz i)
      set u : Fin j → X := fun i => (‖v i‖)⁻¹ • v i with hu
      have hu1 : ∀ i, ‖u i‖ ≤ 1 := fun i => by
        simp only [hu, norm_smul, norm_inv, norm_norm]; rw [inv_mul_cancel₀ (hn i)]
      obtain ⟨L, hL1, hL2⟩ := h u hu1
      refine ⟨(∏ i, ‖v i‖) • L, ?_, ?_⟩
      · rw [map_smul, hL1]
        have : (fun i => ‖v i‖ • u i) = v := by
          funext i; simp only [hu, smul_smul, mul_inv_cancel₀ (hn i), one_smul]
        have h2 := Pj.map_smul_univ (fun i => ‖v i‖) u
        rw [this] at h2
        exact h2.symm
      · have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp, mul_comm]
        exact mul_le_mul_of_nonneg_right hL2 hp
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      refine ⟨0, ?_, ?_⟩
      · rw [map_zero]; exact (Pj.map_coord_zero i hi).symm
      · have : ∏ i, ‖v i‖ = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
        simp [this]
  choose L hL1 hL2 using hex
  let T0 : MultilinearMap ℝ (fun _ : Fin j => X) Z :=
    { toFun := L
      map_update_add' := fun v i a b => by
        apply hι
        rw [map_add, hL1, hL1, hL1, Pj.map_update_add]
      map_update_smul' := fun v i c a => by
        apply hι
        rw [map_smul, hL1, hL1, Pj.map_update_smul] }
  refine ⟨T0.mkContinuous B hL2, fun v => hL1 v, ?_⟩
  exact MultilinearMap.mkContinuous_norm_le _ hB _

/-- Interpolation for multilinear maps (the printed "evaluation on unit vectors, then taking the supremum"). -/
theorem mult_interp {j : ℕ} {Zq : Type*} [NormedAddCommGroup Zq] [NormedSpace ℝ Zq]
    (ιpq : Z →L[ℝ] Zq) (ιp0 : Z →L[ℝ] F) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hint : ∀ y : Z, ‖ιpq y‖ ≤ ‖ιp0 y‖ ^ (1 - θ) * ‖y‖ ^ θ)
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin j => X) Z) :
    ‖ιpq.compContinuousMultilinearMap D‖ ≤
      ‖ιp0.compContinuousMultilinearMap D‖ ^ (1 - θ) * ‖D‖ ^ θ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v => ?_)
  have hp : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have h1 : ‖ιp0 (D v)‖ ≤ ‖ιp0.compContinuousMultilinearMap D‖ * ∏ i, ‖v i‖ :=
    (ιp0.compContinuousMultilinearMap D).le_opNorm v
  have h2 : ‖D v‖ ≤ ‖D‖ * ∏ i, ‖v i‖ := D.le_opNorm v
  calc ‖ιpq.compContinuousMultilinearMap D v‖ = ‖ιpq (D v)‖ := rfl
    _ ≤ ‖ιp0 (D v)‖ ^ (1 - θ) * ‖D v‖ ^ θ := hint _
    _ ≤ (‖ιp0.compContinuousMultilinearMap D‖ * ∏ i, ‖v i‖) ^ (1 - θ) * (‖D‖ * ∏ i, ‖v i‖) ^ θ :=
        rpow_mul_rpow_le (norm_nonneg _) (norm_nonneg _) h1 h2 hθ0.le hθ1.le
    _ = ‖ιp0.compContinuousMultilinearMap D‖ ^ (1 - θ) * ‖D‖ ^ θ * ∏ i, ‖v i‖ := by
        rw [Real.mul_rpow (norm_nonneg _) hp, Real.mul_rpow (norm_nonneg _) hp]
        have : (∏ i, ‖v i‖) ^ (1 - θ) * (∏ i, ‖v i‖) ^ θ = ∏ i, ‖v i‖ := by
          rw [← Real.rpow_add' hp (by linarith)]
          simp
        calc _ = ‖ιp0.compContinuousMultilinearMap D‖ ^ (1 - θ) * ‖D‖ ^ θ *
              ((∏ i, ‖v i‖) ^ (1 - θ) * (∏ i, ‖v i‖) ^ θ) := by ring
          _ = _ := by rw [this]

end Mult

end QuantumNLS.Loss

#print axioms QuantumNLS.Loss.lift_multilinear
#print axioms QuantumNLS.Loss.mult_interp
