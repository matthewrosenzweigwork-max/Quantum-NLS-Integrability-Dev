import Mathlib
import QuantumNLS.MixedQuadratures

/-!
# PROP-026: the operators `C_{0,N}` and `L_N` of `eq:MP-C0`, `eq:MP-L` as contour integrals, and their identification

New module.  Generic complex Hilbert space `H` (applied to the physical `H = Sym^N`; the generic form avoids the
`SymSector` instance-synthesis failures: all `Integrable`/`cfc` statements are produced from the generic `[NormedAddCommGroup H]
[InnerProductSpace ℂ H] [CompleteSpace H]` parameters, and the concrete space only supplies those instances).

* `C0op ν S u g = Re ∫ u_θ g_θ(S_θ) dν` (`g_θ(S_θ) = cfc g_θ S_θ`) and `Lop ν S u d = Re ∫ u_θ d_θ S_θ dν`:
  the printed `C_{0,N}` (`eq:MP-C0`) and `L_N` (`eq:MP-L`, `d_θ = D(z_θ)⁻¹`);
* **`C0N_eq_C0op`**: `C0N ν Φ F = C0op ν S u g` for `Φ_θ = quadHom S_θ`, `F_θ = quadF u_θ g_θ`, **with the integrability hypothesis
  of `C0N_eq_reOp` proved** from measurability of `θ ↦ F_θ|_K` and of `θ ↦ (-i u_θ)`-twisted family (so that
  `X = Re X + i Re(-iX)`), via `integrable_apply_comp` (the Stone-Weierstrass based measurability of `θ ↦ Φ_θ(h_θ)`);
* **`LN_eq_Lop`**: `LN ν Φ F (ι ∘ s) = Lop ν S u d` given `HasDerivAt (g θ) (d θ) (s θ)` and integrability of the integrand.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.MPOps

open QuantumNLS.MixedQuadratures QuantumNLS.FunctionalLinearization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {Θ : Type*} [MeasurableSpace Θ]

/-- `C_{0,N} = Re ∫ u_θ f_{z_θ}(S_N(z_θ)) dν` (`eq:MP-C0`). -/
def C0op (ν : Measure Θ) (S : Θ → H →L[ℂ] H) (u : Θ → ℂ) (g : Θ → ℂ → ℂ) : H →L[ℂ] H :=
  reOp (∫ θ, u θ • cfc (g θ) (S θ) ∂ν)

/-- `L_N = Re ∫ u_θ D(z_θ)⁻¹ S_N(z_θ) dν` (`eq:MP-L`). -/
def Lop (ν : Measure Θ) (S : Θ → H →L[ℂ] H) (u d : Θ → ℂ) : H →L[ℂ] H :=
  reOp (∫ θ, (u θ * d θ) • S θ ∂ν)

theorem eq_reOp_add (X : H →L[ℂ] H) :
    X = reOp X + Complex.I • reOp ((-Complex.I) • X) := by
  unfold reOp
  have h1 : ContinuousLinearMap.adjoint ((-Complex.I) • X) = Complex.I • ContinuousLinearMap.adjoint X := by
    rw [map_smulₛₗ]; simp
  rw [h1]
  match_scalars <;> (try ring_nf) <;> (try simp only [Complex.I_sq]) <;> (try ring_nf)

variable (ν : Measure Θ) (R : ℝ) (S : Θ → H →L[ℂ] H) (hS : ∀ θ, IsStarNormal (S θ)) (hR : ∀ θ, ‖S θ‖ ≤ R)

/-- **`C_{0,N}` identified, with the integrability hypothesis proved.** -/
theorem C0N_eq_C0op [IsFiniteMeasure ν] (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (hg : ∀ θ, Continuous (g θ))
    (hB : ∀ j, AEStronglyMeasurable
      (fun θ => quadHom (S θ) (hS θ) R (hR θ) (coordC (d := 2) (K := Kdisc R) j)) ν)
    (hF1 : AEStronglyMeasurable (fun θ => resKd (Kdisc R) (quadF (u θ) (g θ))) ν)
    (hF2 : AEStronglyMeasurable (fun θ => resKd (Kdisc R) (quadF ((-Complex.I) * u θ) (g θ))) ν)
    {C : ℝ} (hC1 : ∀ θ, ‖resKd (Kdisc R) (quadF (u θ) (g θ))‖ ≤ C)
    (hC2 : ∀ θ, ‖resKd (Kdisc R) (quadF ((-Complex.I) * u θ) (g θ))‖ ≤ C) :
    C0N ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) (fun θ => quadF (u θ) (g θ)) = C0op ν S u g := by
  have hint : Integrable (fun θ => u θ • cfc (g θ) (S θ)) ν := by
    have i1 := integrable_apply_comp ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) hB _ hF1 hC1
    have i2 := integrable_apply_comp ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) hB _ hF2 hC2
    refine (Integrable.add i1 (Integrable.smul Complex.I i2)).congr (Eventually.of_forall fun θ => ?_)
    have e1 : quadHom (S θ) (hS θ) R (hR θ) (resKd (Kdisc R) (quadF (u θ) (g θ))) =
        reOp (u θ • cfc (g θ) (S θ)) := quadHom_quadF _ _ _ _ (u θ) (hg θ)
    have e2 : quadHom (S θ) (hS θ) R (hR θ) (resKd (Kdisc R) (quadF ((-Complex.I) * u θ) (g θ))) =
        reOp (((-Complex.I) * u θ) • cfc (g θ) (S θ)) := quadHom_quadF _ _ _ _ ((-Complex.I) * u θ) (hg θ)
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [e1, e2, ← smul_smul]
    exact (eq_reOp_add (u θ • cfc (g θ) (S θ))).symm
  exact C0N_eq_reOp ν R S hS hR u g hg hint

/-- **`L_N` identified.** -/
theorem LN_eq_Lop (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (d s : Θ → ℂ) (hg : ∀ θ, HasDerivAt (g θ) (d θ) (s θ))
    (hint : Integrable (fun θ => (u θ * d θ) • S θ) ν) :
    LN ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) (fun θ => quadF (u θ) (g θ))
      (fun θ => isoR2 (s θ)) = Lop ν S u d :=
  LN_eq_reOp ν R S hS hR u g d s hg hint

end QuantumNLS.MPOps

#print axioms QuantumNLS.MPOps.eq_reOp_add
#print axioms QuantumNLS.MPOps.C0N_eq_C0op
#print axioms QuantumNLS.MPOps.LN_eq_Lop
