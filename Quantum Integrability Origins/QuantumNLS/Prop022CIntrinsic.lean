import Mathlib
import QuantumNLS.Prop022CWeyl
import QuantumNLS.Prop022CQuadTorus
import QuantumNLS.Prop022BMain
import QuantumNLS.Prop022SymplecticR123
import QuantumNLS.Prop022SmoothDomainR126

/-! PROP-022 route A, round 4, stage C8: the INTRINSIC H-level Fock-side conclusions.

`IntrinsicFock V aS bS S Ω numE` packages printed conclusions 4-6 of Q7B:lem:pair with the INTRINSIC
`Fock(H)` operators: the Weyl operators are `exp(a*(v) - a(v))` characterized by Stone (`IsWeylOp`), the
quadratic Hamiltonian is `dΓ(a) + ½(a*(b)+a(b))` (`QRel`/`QPrint`), the evolved vacuum is pure quasifree in the
Bogoliubov-implementer sense (`PureQuasifreeH`) with the printed number identity.

`intrinsic_of_U` / `intrinsic_of_J` derive it from the frozen transported / compressed statements
(`PROP022_fock_transport`, `PROP022_fock_J`) plus the C-stage bridges:
`WH_isWeylOp`/`WJ_isWeylOp` (Weyl), `QH_QRel`/`QJ_QRel` (Hamiltonian), second-moment-domain invariance of the
propagator, symplecticity of `S`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022CIntrinsic
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022AIsoTensor
open QuantumNLS.Prop022BIso QuantumNLS.Prop022CCanon QuantumNLS.Prop022BFock1
open QuantumNLS.Prop022CWeyl QuantumNLS.Prop022CQuad QuantumNLS.Prop022CQuadTorus
open PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A vacuum vector: a unit vector in the zero-particle sector. -/
def IsVacuum (Ω : FockSpace E) : Prop := ‖Ω‖ = 1 ∧ ∀ n, n ≠ 0 → Ω n = 0

/-- **Intrinsic pure quasifree vector**: `ξ = V Ω` for a vacuum `Ω` and a unitary `V` of `Fock(E)` that
implements a bounded real-linear symplectic map `S` of `E` on the intrinsic Weyl operators
(`V W(v) V⁻¹ = W(S v)`, `W(v) = exp(a*(v) - a(v))`). -/
def PureQuasifreeH (ξ : FockSpace E) : Prop :=
  ∃ (Ω : FockSpace E) (S : E →L[ℝ] E) (V : FockSpace E ≃ₗᵢ[ℂ] FockSpace E),
    IsVacuum Ω ∧ (∀ x y, (⟪S x, S y⟫_ℂ).im = (⟪x, y⟫_ℂ).im) ∧
    (∀ v, ∃ W W', IsWeylOp v W ∧ IsWeylOp (S v) W' ∧ ∀ x, V (W x) = W' (V x)) ∧ ξ = V Ω

/-- Intrinsic form of printed conclusions 4-6. -/
structure IntrinsicFock (V : ℝ → ℝ → FockSpace E ≃ₗᵢ[ℂ] FockSpace E)
    (aS : ℝ → SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) (bS : ℝ → SymSector ℂ E 2)
    (S : ℝ → ℝ → E →L[ℝ] E) (Ω : FockSpace E) (numE : ℝ → ℝ≥0∞) : Prop where
  weyl_exists : ∀ v : E, ∃ W, IsWeylOp v W
  domain : ∀ s t (x : FockSpace E), (∀ j : ℕ, x ∈ Prop022AFock.momentDomainH j) →
    ∀ j : ℕ, V t s x ∈ Prop022AFock.momentDomainH j
  schrodinger : ∀ s t (x : FockSpace E), (∀ j : ℕ, x ∈ Prop022AFock.momentDomainH j) →
    QRel (aS t) (bS t) (V t s x) (QPrint (aS t) (bS t) (V t s x)) ∧
      HasDerivAt (fun r => V r s x) ((-Complex.I) • QPrint (aS t) (bS t) (V t s x)) t
  implement : ∀ s t (v : E) (W W' : FockSpace E ≃ₗᵢ[ℂ] FockSpace E), IsWeylOp v W →
    IsWeylOp (S t s v) W' → ∀ x, V t s (W ((V t s).symm x)) = W' x
  quasifree : ∀ t, PureQuasifreeH (V t 0 Ω) ∧ ‖V t 0 Ω‖ = 1 ∧
    Prop022AFock.numExpH (V t 0 Ω) = numE t

theorem intrinsicFock_of_data
    (V : ℝ → ℝ → FockSpace E ≃ₗᵢ[ℂ] FockSpace E)
    (aS : ℝ → SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) (bS : ℝ → SymSector ℂ E 2)
    (S : ℝ → ℝ → E →L[ℝ] E) (Ω : FockSpace E) (numE : ℝ → ℝ≥0∞)
    (Wf : E → FockSpace E ≃ₗᵢ[ℂ] FockSpace E)
    (Qf : (SymSector ℂ E 1 →L[ℂ] SymSector ℂ E 1) → SymSector ℂ E 2 → FockSpace E → FockSpace E)
    (hWf : ∀ v, IsWeylOp v (Wf v))
    (hQ : ∀ a b y, y ∈ Prop022AFock.momentDomainH 2 → QRel a b y (Qf a b y))
    (hdom : ∀ s t (x : FockSpace E), (∀ j : ℕ, x ∈ Prop022AFock.momentDomainH j) →
      ∀ j : ℕ, V t s x ∈ Prop022AFock.momentDomainH j)
    (hSchr : ∀ s t (x : FockSpace E), (∀ j : ℕ, x ∈ Prop022AFock.momentDomainH j) →
      HasDerivAt (fun r => V r s x) ((-Complex.I) • Qf (aS t) (bS t) (V t s x)) t)
    (himpl : ∀ s t (v : E) (x : FockSpace E), V t s (Wf v ((V t s).symm x)) = Wf (S t s v) x)
    (hΩ : IsVacuum Ω) (hS : ∀ t s x y, (⟪S t s x, S t s y⟫_ℂ).im = (⟪x, y⟫_ℂ).im)
    (hqf : ∀ t, ‖V t 0 Ω‖ = 1 ∧ Prop022AFock.numExpH (V t 0 Ω) = numE t) :
    IntrinsicFock V aS bS S Ω numE where
  weyl_exists v := ⟨Wf v, hWf v⟩
  domain := hdom
  schrodinger s t x hx := by
    have hq := QPrint_eq (hQ (aS t) (bS t) (V t s x) (hdom s t x hx 2))
    refine ⟨?_, ?_⟩
    · rw [hq]; exact hQ _ _ _ (hdom s t x hx 2)
    · rw [hq]; exact hSchr s t x hx
  implement s t v W W' hW hW' x := by
    rw [weylOp_unique hW (hWf v), weylOp_unique hW' (hWf (S t s v))]
    exact himpl s t v x
  quasifree t := by
    refine ⟨⟨Ω, S t 0, V t 0, hΩ, hS t 0, fun v => ⟨Wf v, Wf (S t 0 v), hWf v, hWf _, fun x => ?_⟩, rfl⟩,
      hqf t⟩
    have h := himpl 0 t v (V t 0 x)
    rw [LinearIsometryEquiv.symm_apply_apply] at h
    exact h

end Generic

end QuantumNLS.Prop022CIntrinsic

#print axioms QuantumNLS.Prop022CIntrinsic.intrinsicFock_of_data
