import QuantumNLS.RephasingFlow
import QuantumNLS.RealAnalyticDef

/-! integrator-authored trusted spec for R-8DD5AE6E `norm:rephasing`
(global/scaling_and_phase_freedom.tex:52). On ℓ²(ℤ) with c ≠ 0, κ > 0,
F_κ(z) = cκ[(Σ|z_n|²)² − Σ|z_n|⁴]. ANY family Φ given by the printed formula
Φ_t(z)_n = exp(−2icκt(‖z‖² − |z_n|²)) z_n is: the complete Hamiltonian flow of F_κ for the DEF-015
convention (X_F = −i∇F), with uniqueness; for every t a strong symplectic diffeomorphism (inverse Φ_{−t},
differentiable, derivative a continuous linear equivalence preserving Ω = 2 Im⟨·,·⟩), real analytic at
every point in DEF-017's polynomial-series sense, preserving every action |z_n|²; at time one: identity
differential at 0, fixes every single-mode vector, commutes with independent coordinate rotations and
index permutations; and does not commute with complex conjugation, and changes a relative Cartesian
product. Rotations/permutations/conjugation are pinned by their coordinate formulas. -/

open scoped ComplexConjugate
open QuantumNLS.RephasingFlow

namespace QuantumNLS.R8DD5Spec

def Spec : Prop :=
  ∀ (c κ : ℝ), c ≠ 0 → 0 < κ → ∀ Φ : ℝ → E → E,
    (∀ t z n, Φ t z n = Complex.exp (-(2 * Complex.I * c * κ * t) * ((‖z‖ ^ 2 - ‖z n‖ ^ 2 : ℝ) : ℂ)) * z n) →
    -- coordinate operations pinned by formula
    (∀ θ z n, rotE θ z n = Complex.exp ((θ n : ℂ) * Complex.I) * z n) ∧
    (∀ (σ : ℤ ≃ ℤ) z n, permE σ z n = z (σ n)) ∧ (∀ z n, conjE z n = conj (z n)) ∧
    -- the functional and its DEF-015 gradient
    (∀ z, F c κ z = c * κ * ((∑' n, ‖z n‖ ^ 2) ^ 2 - ∑' n, ‖z n‖ ^ 4)) ∧
    (∃ Q : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ, ∀ z, F c κ z = Q (fun _ => z)) ∧
    (∀ u n, SymplecticBracket.gradient (F c κ) u n = ((2 * c * κ * (‖u‖ ^ 2 - ‖u n‖ ^ 2) : ℝ) : ℂ) * u n) ∧
    -- complete Hamiltonian flow with uniqueness
    (∀ z, Φ 0 z = z) ∧ (∀ s t z, Φ s (Φ t z) = Φ (s + t) z) ∧
    (∀ z t, HasDerivAt (fun s => Φ s z) (SymplecticBracket.hamField (F c κ) (Φ t z)) t) ∧
    (∀ γ : ℝ → E, (∀ t, HasDerivAt γ (SymplecticBracket.hamField (F c κ) (γ t)) t) → ∀ t, γ t = Φ t (γ 0)) ∧
    -- every time
    (∀ t : ℝ,
      (∀ z, Φ (-t) (Φ t z) = z) ∧ (∀ w, Φ t (Φ (-t) w) = w) ∧
      (∀ z, DifferentiableAt ℝ (Φ t) z) ∧
      (∀ z, ∃ e : E ≃L[ℝ] E, (e : E → E) = fderiv ℝ (Φ t) z) ∧
      (∀ z h k, SymplecticBracket.omega (fderiv ℝ (Φ t) z h) (fderiv ℝ (Φ t) z k) =
        SymplecticBracket.omega h k) ∧
      (∀ x, QuantumNLS.RealAnalyticDef.IsRealAnalyticPoly (Φ t) x) ∧
      (∀ z n, ‖Φ t z n‖ ^ 2 = ‖z n‖ ^ 2)) ∧
    -- time one
    (fderiv ℝ (Φ 1) 0 = ContinuousLinearMap.id ℝ E ∧
      (∀ m w, Φ 1 (lp.single (E := fun _ : ℤ => ℂ) 2 m w) = lp.single (E := fun _ : ℤ => ℂ) 2 m w) ∧
      (∀ θ z, Φ 1 (rotE θ z) = rotE θ (Φ 1 z)) ∧
      (∀ (σ : ℤ ≃ ℤ) z, Φ 1 (permE σ z) = permE σ (Φ 1 z))) ∧
    -- general inputs
    ((∃ z, Φ 1 (conjE z) ≠ conjE (Φ 1 z)) ∧
      (∃ z, (Φ 1 z 0).re * (Φ 1 z 1).re ≠ (z 0).re * (z 1).re))

theorem spec : Spec := by
  intro c κ hc hκ Φ hΦ
  have hU : Φ = U c κ := by
    funext t z; apply lp.ext; funext n; rw [hΦ, U_apply]
  subst hU
  obtain ⟨⟨hQ, hgrad⟩, ⟨-, h0, hadd, hder, huniq⟩, hall, ⟨hd0, hsingle, hrot, hperm, -, -⟩,
    ⟨hconj, hcart⟩⟩ := norm_rephasing c κ hc hκ
  refine ⟨rotE_apply, permE_apply, conjE_apply, fun z => rfl, hQ, hgrad, h0, hadd, hder, huniq,
    fun t => ?_, ⟨hd0, hsingle, hrot, hperm⟩, ⟨hconj, hcart⟩⟩
  obtain ⟨hs, -, -, hact, hinv⟩ := hall t
  refine ⟨hinv, U_neg_right c κ t, hs.differentiable, hs.deriv_iso, hs.symplectic, fun x => ?_, hact⟩
  exact (QuantumNLS.RealAnalyticDef.analyticAt_iff_isRealAnalyticPoly _ x).1 (U_analyticAt c κ t x)

end QuantumNLS.R8DD5Spec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R8DD5Spec.spec
  IO.println s!"R8DD5Spec.spec axioms: {ax}"
