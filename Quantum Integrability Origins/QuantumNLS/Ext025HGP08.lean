import QuantumNLS.Ext025B9Bridges
import QuantumNLS.Ext025B8BorelLaws

/-! EXT-025 layer A (part 2), haiku_inventory. Contract GP-08, REPAIRED text
(implementation/ops/contracts/OWNER_CONTRACT_REPAIRS_2026-11-16.md,
FIN-EXT025-GP-08 corrected), which supersedes the literal record for acceptance:
  Unchanged: real spectral multipliers are selfadjoint on their EXACT MAXIMAL
  domains; bounded multipliers form a *-calculus; uniformly bounded pointwise
  convergence gives strong convergence; functions of one common spectral
  resolution commute (strongly).
  Restricted: form-domain preservation f(H) Q(H0) ⊆ Q(H0) is claimed ONLY for
  BOUNDED common spectral multipliers f. Unbounded multipliers keep exact maximal
  domains with no form-domain claim (no clause below is made for them).
Setting: a projection-valued measure P on a complex Hilbert space E
(QuantumNLS.BetheChargeResolution.ProjectionMeasure), the arbitrary-PVM
spectral calculus of Ext025B6PVM/B8/B9. Real Borel multipliers are real-valued
measurable functions on ℝ. Q(H0) for a nonnegative multiplier h is the form
domain {x | ∫ h dμ_x < ∞}, i.e. the spectral energy of x, FormDomain P (ofReal ∘ h) x.
Each clause is a frozen theorem; this module only assembles them. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace QuantumNLS.Ext025HGP08

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded Borel calculus does not depend on the numerical bound data, only on the
symbol (the bound enters only through the proof obligations). -/
theorem bounded_congr (P : QuantumNLS.BetheChargeResolution.ProjectionMeasure E)
    {h₁ h₂ : ℝ → ℂ} (e : h₁ = h₂) (m₁ : Measurable h₁) (m₂ : Measurable h₂)
    (C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (b₁ : ∀ t, ‖h₁ t‖ ≤ C₁) (b₂ : ∀ t, ‖h₂ t‖ ≤ C₂) :
    QuantumNLS.Ext025B8BorelCalculus.bounded P h₁ m₁ C₁ hC₁ b₁ =
      QuantumNLS.Ext025B8BorelCalculus.bounded P h₂ m₂ C₂ hC₂ b₂ := by
  subst e
  rfl

/-- Exact contract GP-08 (repaired). Clauses (1)-(5) follow the repaired text in order. -/
theorem contract_GP08 (P : QuantumNLS.BetheChargeResolution.ProjectionMeasure E) :
    -- (1) real multipliers are selfadjoint on their exact maximal domains
    (∀ (f : ℝ → ℝ) (hf : Measurable f),
      IsSelfAdjoint (QuantumNLS.Ext025B9MaximalIntegral.operator P (fun t => (f t : ℂ))
        (Complex.measurable_ofReal.comp hf)) ∧
      ∀ x : E, x ∈ (QuantumNLS.Ext025B9MaximalIntegral.operator P (fun t => (f t : ℂ))
          (Complex.measurable_ofReal.comp hf)).domain ↔
        ∫⁻ t, ENNReal.ofReal (‖(f t : ℂ)‖ ^ 2) ∂(QuantumNLS.Ext025B6PVM.scalarMeasure P x) ≠ ⊤) ∧
    -- (2) bounded multipliers form a *-calculus
    (∀ (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
      (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) (hfg : ∀ t, ‖(f + g) t‖ ≤ C + D),
      QuantumNLS.Ext025B8BorelCalculus.bounded P (f + g) (hf.add hg) (C + D) (add_nonneg hC hD) hfg =
        QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb +
          QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc) ∧
    (∀ (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
      (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D) (hfg : ∀ t, ‖(f * g) t‖ ≤ C * D),
      QuantumNLS.Ext025B8BorelCalculus.bounded P (f * g) (hf.mul hg) (C * D) (mul_nonneg hC hD) hfg =
        QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb *
          QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc) ∧
    (∀ (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) (c : ℂ)
      (hm : Measurable (c • f)) (hcb : ∀ t, ‖(c • f) t‖ ≤ ‖c‖ * C),
      QuantumNLS.Ext025B8BorelCalculus.bounded P (c • f) hm (‖c‖ * C)
          (mul_nonneg (norm_nonneg _) hC) hcb =
        c • QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb) ∧
    (QuantumNLS.Ext025B8BorelCalculus.bounded P (fun _ => (1 : ℂ)) measurable_const 1 zero_le_one
        (fun _ => by simp) = 1) ∧
    (∀ (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C)
      (hm : Measurable (fun t => star (f t))) (hbs : ∀ t, ‖star (f t)‖ ≤ C),
      (QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb).adjoint =
        QuantumNLS.Ext025B8BorelCalculus.bounded P (fun t => star (f t)) hm C hC hbs) ∧
    -- (3) uniformly bounded pointwise convergence gives strong convergence
    (∀ {J : Type*} {l : Filter J} [l.IsCountablyGenerated]
      (f : J → ℝ → ℂ) (g : ℝ → ℂ) (hf : ∀ j, Measurable (f j)) (hg : Measurable g)
      (C : ℝ) (hC : 0 ≤ C) (hb : ∀ j t, ‖f j t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ C)
      (hl : ∀ t, Tendsto (fun j => f j t) l (𝓝 (g t))) (x : E),
      Tendsto (fun j => QuantumNLS.Ext025B8BorelCalculus.bounded P (f j) (hf j) C hC (hb j) x) l
        (𝓝 (QuantumNLS.Ext025B8BorelCalculus.bounded P g hg C hC hc x))) ∧
    -- (4) functions of one common spectral resolution commute (strongly)
    (∀ (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C),
      QuantumNLS.Ext025B7PVMForms.Commutes P
        (QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb)) ∧
    (∀ (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
      (hb : ∀ t, ‖f t‖ ≤ C) (hc : ∀ t, ‖g t‖ ≤ D),
      QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb *
          QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc =
        QuantumNLS.Ext025B8BorelCalculus.bounded P g hg D hD hc *
          QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb) ∧
    (∀ (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g) (s t : Set ℝ),
      MeasurableSet s → MeasurableSet t →
      P.toFun (f ⁻¹' s) * P.toFun (g ⁻¹' t) = P.toFun (g ⁻¹' t) * P.toFun (f ⁻¹' s)) ∧
    -- (5) form-domain preservation, for BOUNDED common multipliers only
    (∀ (h : ℝ → ℝ) (_hh : ∀ t, 0 ≤ h t) (f : ℝ → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
      (hb : ∀ t, ‖f t‖ ≤ C) (x : E),
      QuantumNLS.Ext025B7PVMForms.FormDomain P (fun t => ENNReal.ofReal (h t)) x →
      QuantumNLS.Ext025B7PVMForms.FormDomain P (fun t => ENNReal.ofReal (h t))
        (QuantumNLS.Ext025B8BorelCalculus.bounded P f hf C hC hb x)) := by
  refine ⟨fun f hf => ⟨QuantumNLS.Ext025B9SelfAdjoint.real_selfAdjoint P f hf, fun x => Iff.rfl⟩,
    fun f g hf hg C D hC hD hb hc hfg =>
      QuantumNLS.Ext025B8BorelCalculus.bounded_add P f g hf hg C D hC hD hb hc,
    fun f g hf hg C D hC hD hb hc hfg =>
      QuantumNLS.Ext025B8BorelLaws.bounded_mul P f g hf hg C D hC hD hb hc,
    fun f hf C hC hb c hm hcb =>
      QuantumNLS.Ext025B8BorelCalculus.bounded_smul P f hf C hC hb c,
    QuantumNLS.Ext025B8BorelCalculus.bounded_one P,
    fun f hf C hC hb hm hbs => QuantumNLS.Ext025B8BorelLaws.bounded_star P f hf C hC hb,
    fun {J} {l} _ f g hf hg C hC hb hc hl x =>
      QuantumNLS.Ext025B8BorelCalculus.bounded_strong P f g hf hg C hC hb hc hl x,
    fun f hf C hC hb => QuantumNLS.Ext025B8BorelLaws.bounded_commutes P f hf C hC hb,
    ?_, ?_, ?_⟩
  · -- commutation of two bounded calculi, via the *-calculus law and f*g = g*f
    intro f g hf hg C D hC hD hb hc
    have m1 := QuantumNLS.Ext025B8BorelLaws.bounded_mul P f g hf hg C D hC hD hb hc
    have m2 := QuantumNLS.Ext025B8BorelLaws.bounded_mul P g f hg hf D C hD hC hc hb
    rw [← m1, ← m2]
    exact bounded_congr P (mul_comm f g) _ _ _ _ _ _ _ _
  · -- spectral projections of two real functions of one resolution commute
    intro f g hf hg s t hs ht
    rw [P.inter _ _ (hf hs) (hg ht), P.inter _ _ (hg ht) (hf hs), Set.inter_comm]
  · -- form-domain preservation for bounded multipliers
    intro h hh f hf C hC hb x hx
    exact QuantumNLS.Ext025B8BorelLaws.bounded_form_domain P f hf C hC hb
      (fun t => ENNReal.ofReal (h t)) x hx

end QuantumNLS.Ext025HGP08

#print axioms QuantumNLS.Ext025HGP08.contract_GP08
