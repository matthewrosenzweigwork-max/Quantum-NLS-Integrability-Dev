import QuantumNLS.FidelitySource
/-!
Trusted statements, written by the integrator (not the prover) from
`source/chapters/core/projective_reconstruction.tex:107–181`.
Trace and trace norm are the TraceClass TC6 objects (Terra-reviewed support, integrator-verified):
`posTrace T = Σ_i re⟨b_i, T b_i⟩` (basis-independent on positive T, `posTrace_eq`), and `traceNorm A = posTrace |A|` with
|A| = `CFC.abs A`, i.e. ‖A‖₁ = Tr|A|. `|z⟩⟨z|` is `rankOne ℂ z z` (f ↦ ⟨z,f⟩ z; inner product linear in the 2nd slot).
-/
open QuantumNLS.TraceClass
open scoped InnerProductSpace ENNReal ComplexConjugate

/-- R-828C5F7E `lem:fidelity`: A ≥ 0 trace class, Tr A = 1, ‖z‖ = 1 ⇒ ‖A − |z⟩⟨z|‖₁ ≤ 2√(1 − ⟨z,Az⟩).
(⟨z,Az⟩ is real for A ≥ 0; its real part is written.) Stated on every complete complex inner-product space. -/
def FidelitySpec : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E), A.IsPositive → IsTraceClass A → posTrace A = 1 →
    ∀ z : E, ‖z‖ = 1 →
      traceNorm (A - InnerProductSpace.rankOne ℂ z z) ≤ ENNReal.ofReal (2 * Real.sqrt (1 - RCLike.re ⟪z, A z⟫_ℂ))

/-- spec-side ℓ²(ℤ), coordinate vectors, matrix entries, coordinate projection. -/
abbrev SL2 : Type := lp (fun _ : ℤ => ℂ) 2
noncomputable def sE (a : ℤ) : SL2 := lp.single 2 a (1 : ℂ)
noncomputable def sEntry (A : SL2 →L[ℂ] SL2) (a b : ℤ) : ℂ := ⟪sE a, A (sE b)⟫_ℂ
noncomputable def sP (F : Finset ℤ) (z : SL2) : SL2 := ∑ a ∈ F, z a • sE a

/-- R-849FDB99 `lem:uniform-upgrade`, literal inf_F sup_t tightness and uniform entry convergence. -/
def UniformUpgradeSpec : Prop :=
  ∀ {T : Type} (A : ℕ → T → SL2 →L[ℂ] SL2) (z : T → SL2),
    (∀ N t, (A N t).IsPositive) → (∀ N t, posTrace (A N t) = 1) → (∀ t, ‖z t‖ = 1) →
    (⨅ F : Finset ℤ, ⨆ t, ‖z t - sP F (z t)‖ = 0) →
    (∀ a b, Filter.Tendsto (fun N => ⨆ t, ‖sEntry (A N t) a b - z t a * conj (z t b)‖) Filter.atTop (nhds 0)) →
    Filter.Tendsto (fun N => ⨆ t, traceNorm (A N t - InnerProductSpace.rankOne ℂ (z t) (z t))) Filter.atTop (nhds 0)

theorem fidelity_spec : FidelitySpec := by
  intro E _ _ _ A hA htc hTr z hz
  exact QuantumNLS.FidelitySource.fidelity_source A hA htc hTr z hz

theorem uniform_upgrade_spec : UniformUpgradeSpec := by
  intro T A z hA hTr hz htight hent
  exact QuantumNLS.Fidelity.uniform_upgrade A z hA hTr hz htight hent

#print axioms fidelity_spec
#print axioms uniform_upgrade_spec
