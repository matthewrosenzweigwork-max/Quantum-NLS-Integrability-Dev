import QuantumNLS.TerraMultiRound89FormDomain
import QuantumNLS.TerraMultiRound89FormCore

/-! Identify a Hamiltonian eigenvector with the corresponding variational
resolvent representative in the physical form domain. -/
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
namespace QuantumNLS.TerraMultiRound89EigenForm
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

/-- The contact resolvent maps `(1+e)x` to `x` for every operator-domain
eigenvector, with the full variational identity. -/
theorem eigen_resolvent_form (hc : 0 ≤ c) (x : SymL2 L N)
    (hx : x ∈ (Hop (L := L) (N := N) c hc).domain) (e : ℝ)
    (he : Hop c hc ⟨x,hx⟩ = (e : ℂ) • x) :
    valSym (psi c hc (((e + 1 : ℝ) : ℂ) • x)) = x ∧
    ∀ z : VSym L N, q c z.1 (psi c hc (((e + 1 : ℝ) : ℂ) • x)).1 =
      (e : ℂ) * ⟪valSym z, x⟫_ℂ := by
  have hxcopy := hx
  obtain ⟨g, hg⟩ : ∃ g : SymL2 L N, Rop c hc g = x := hxcopy
  have hT : Tinv c hc ⟨x,hx⟩ = g := Tinv_apply_of_eq hc ⟨x,hx⟩ g hg
  have hH : Hop c hc ⟨x,hx⟩ = g - x := by
    change Tinv c hc ⟨x,hx⟩ - x = g - x
    rw [hT]
  have hge : g = (((e + 1 : ℝ) : ℂ) • x) := by
    calc
      g = (g - x) + x := by abel
      _ = (e : ℂ) • x + x := by rw [← hH, he]
      _ = (((e + 1 : ℝ) : ℂ) • x) := by push_cast; module
  have hR : Rop c hc (((e + 1 : ℝ) : ℂ) • x) = x := by rw [← hge]; exact hg
  refine ⟨(Rop_eq_valSym_psi hc _).symm.trans hR, fun z => ?_⟩
  have h := variational_of_domain hc (((e + 1 : ℝ) : ℂ) • x) z
  rw [hR] at h
  convert h using 1
  rw [inner_sub_right]
  have hs : ⟪valSym z, (((e + 1 : ℝ) : ℂ) • x)⟫_ℂ =
      (((e + 1 : ℝ) : ℂ) * ⟪valSym z, x⟫_ℂ) :=
    inner_smul_right (valSym z) x (((e + 1 : ℝ) : ℂ))
  rw [hs]
  push_cast
  ring

#print axioms eigen_resolvent_form
end QuantumNLS.TerraMultiRound89EigenForm
