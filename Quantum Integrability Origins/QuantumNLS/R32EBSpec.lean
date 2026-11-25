import QuantumNLS.PhaseQuotientBracket

/-! integrator-authored trusted spec for R-32EBD5C1 `lem:root-overlap`
(foundations/ROOT_transfer_involution.tex:18-38). Q_{N,p} is the realized DEF-009 placement `genericU_N_r`
(P_N(A⊗1)P_N on Sym^N H; Terra-accepted KernelDefinition 4e269427). For bounded kernels A on Sym^p H and B on
Sym^q H:
(1) N‖[Q_{N,p}(A), Q_{N,q}(B)]‖ ≤ 2pq‖A‖‖B‖ for p, q ≤ N (eq:root-overlap-bound);
(2) for fixed p, q and every unit u, −iN⟨u^{⊗N}, [Q_{N,p}(A), Q_{N,q}(B)] u^{⊗N}⟩ → {a,b}(u), with
    a(v) = ⟨v^{⊗p}, A v^{⊗p}⟩, b(v) = ⟨v^{⊗q}, B v^{⊗q}⟩ and {·,·} the realized DEF-015 (complexified) bracket
    (eq:root-overlap-limit);
(3) the bracket may equally be computed on the phase quotient S/U(1) of the unit sphere: the symbols are
    phase invariant and descend, the quotient bracket (horizontal-gradient recipe, well defined on the
    quotient by construction) of the descended symbols equals the full-space bracket at every unit u, and the
    limit in (2) equals that quotient bracket. -/

open Filter Topology
open scoped InnerProductSpace
open QuantumNLS.TensorCarrier QuantumNLS.KernelDefinition QuantumNLS.PhaseQuotientBracket

namespace QuantumNLS.R32EBSpec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def sComm (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p)
    (B : BoundedSymmetricKernel H q) : SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  (genericU_N_r N p hp A).comp (genericU_N_r N q hq B) - (genericU_N_r N q hq B).comp (genericU_N_r N p hp A)

noncomputable def sSeq (p q : ℕ) (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H)
    (N : ℕ) : ℂ :=
  if h : p ≤ N ∧ q ≤ N then (-Complex.I) * (N : ℂ) *
    ⟪(htpow N u : HilbertTensorPower ℂ H N),
      ((sComm N p q h.1 h.2 A B ⟨htpow N u, htpow_mem_symSector N u⟩ : SymSector ℂ H N) :
        HilbertTensorPower ℂ H N)⟫_ℂ else 0

theorem spec :
    (∀ (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q),
      (N : ℝ) * ‖sComm N p q hp hq A B‖ ≤ 2 * (p * q : ℝ) * ‖A‖ * ‖B‖) ∧
    (∀ (p q : ℕ) (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : H), ‖u‖ = 1 →
      Tendsto (sSeq p q A B u) atTop
        (𝓝 (QuantumNLS.SymplecticBracket.pbC (kernelProductSymbol A) (kernelProductSymbol B) u))) ∧
    (∀ (p q : ℕ) (A : BoundedSymmetricKernel H p) (B : BoundedSymmetricKernel H q) (u : Sph H),
      qbrC (descend (kernelProductSymbol A) (kps_phaseInv A)) (descend (kernelProductSymbol B) (kps_phaseInv B))
          (proj u) =
        QuantumNLS.SymplecticBracket.pbC (kernelProductSymbol A) (kernelProductSymbol B) u.1 ∧
      Tendsto (sSeq p q A B u.1) atTop
        (𝓝 (qbrC (descend (kernelProductSymbol A) (kps_phaseInv A))
          (descend (kernelProductSymbol B) (kps_phaseInv B)) (proj u)))) := by
  refine ⟨fun N p q hp hq A B => RootOverlapCommutator.root_overlap_bound N p q hp hq A B,
    fun p q A B u hu => RootOverlapLimit.root_overlap_limit p q A B u hu,
    fun p q A B u => ⟨qbrC_kps A B u, root_overlap_limit_quotient p q A B u⟩⟩

end QuantumNLS.R32EBSpec

open Lean in
#eval show CoreM Unit from do
  let ax ← Lean.collectAxioms ``QuantumNLS.R32EBSpec.spec
  IO.println s!"R32EBSpec.spec axioms: {ax}"
