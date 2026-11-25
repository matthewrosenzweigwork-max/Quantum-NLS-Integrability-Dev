import QuantumNLS.TerraMultiRound91Parseval
import QuantumNLS.TerraMultiRound88Markov

/-! Contact-form first moment, using the form core and no operator-domain
assumption on the vector being expanded. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm
open QuantumNLS.TerraMultiRound91Parseval QuantumNLS.Ext025B3DiagonalForms
namespace QuantumNLS.TerraMultiRound91Moment
variable {L : ℝ} [Fact (0 < L)] {N : ℕ} {c : ℝ}

theorem form_first_moment {ι : Type*} (hc : 0 ≤ c)
    (b : HilbertBasis ι ℂ (SymL2 L N)) (ev : ι → ℝ) (hev : ∀ i, 0 ≤ ev i)
    (y : ι → VSym L N) (hy : ∀ i, valSym (y i) = b i)
    (hpair : ∀ i (z : VSym L N), q c z.1 (y i).1 = (ev i : ℂ) * ⟪valSym z, b i⟫_ℂ)
    (hdense : Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N)))
    (z : VSym L N) :
    ∃ hv : InFormDomain ev (b.repr (valSym z)),
      ‖formRoot ev (b.repr (valSym z)) hv‖ ^ 2 = (q c z.1 z.1).re := by
  obtain ⟨hsw, hw⟩ := shifted_parseval hc b ev hev y hy hpair hdense z
  have hs0 := ExactShiftResidual.summable_norm_sq (b.repr (valSym z))
  have hsm : Summable (fun i => ev i * ‖b.repr (valSym z) i‖ ^ 2) := by
    convert hsw.sub hs0 using 1
    ext i
    simp only [Pi.sub_apply]
    ring
  have hv : InFormDomain ev (b.repr (valSym z)) := (formDomain_iff ev hev _).mpr hsm
  refine ⟨hv, ?_⟩
  rw [formRoot_norm_sq ev hev _ hv]
  have hsplit : (∑' i, (ev i + 1) * ‖b.repr (valSym z) i‖ ^ 2) =
      (∑' i, ev i * ‖b.repr (valSym z) i‖ ^ 2) +
      (∑' i, ‖b.repr (valSym z) i‖ ^ 2) := by
    rw [← hsm.tsum_add hs0]
    apply tsum_congr
    intro i
    ring
  have hnorm : (∑' i, ‖b.repr (valSym z) i‖ ^ 2) = ‖valSym z‖ ^ 2 := by
    rw [← ExactShiftResidual.norm_sq_tsum, b.repr.norm_map]
  have hB : (Bform c z z).re = (q c z.1 z.1).re + ‖valSym z‖ ^ 2 := by
    rw [Bform, Complex.add_re]
    congr 1
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (valSym z)).symm
  rw [hsplit, hnorm] at hw
  rw [hB] at hw
  linarith

#print axioms form_first_moment
end QuantumNLS.TerraMultiRound91Moment
