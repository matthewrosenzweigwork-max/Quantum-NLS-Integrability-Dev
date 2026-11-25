import QuantumNLS.TerraMultiRound89BetheCore
import QuantumNLS.EnergyProjection

/-! Bind the abstract eigenbasis form core to the actual mean-field contact
Hamiltonian and its complete normalized Bethe basis. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped InnerProductSpace
open QuantumNLS.ContactOperator QuantumNLS.ContactForm QuantumNLS.EnergyProjection
open QuantumNLS.BetheConditionalBasis QuantumNLS.BetheFreeFamily
namespace QuantumNLS.TerraMultiRound89PhysicalCore
variable (L : ℝ) [Fact (0 < L)]

/-- The physical normalized-wave eigenvectors have form-dense representatives
with their exact contact-form pairings. -/
theorem physical_bethe_form_core (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) :
    let hc : 0 ≤ κ / (N : ℝ) := (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le
    ∃ (b : HilbertBasis (Label N) ℂ (SymL2 L N))
      (hmem : ∀ n, b n ∈ (Hop (L := L) (N := N) (κ / N) hc).domain),
      (∀ n, b n = normalizedWave L N ⟨κ / (N : ℝ), hc⟩ n) ∧
      let y := fun n => psi (κ / N) hc (((energyEig L κ N n + 1 : ℝ) : ℂ) • b n)
      Dense ((Submodule.span ℂ (Set.range y) : Submodule ℂ (VSym L N)) : Set (VSym L N)) ∧
      (∀ n, valSym (y n) = b n) ∧
      (∀ n (z : VSym L N), q (κ / N) z.1 (y n).1 =
        (energyEig L κ N n : ℂ) * ⟪valSym z, b n⟫_ℂ) := by
  have hn : 0 < N := by omega
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hn)
  obtain ⟨-, -, -, -, -, hortho, hdense, heig⟩ :=
    QuantumNLS.UnconditionalBetheBasis.basis L N hN (κ / (N : ℝ)) hc
  let b := HilbertBasis.mk hortho hdense.ge
  have hb : ∀ n, b n = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n := fun n =>
    congrFun (HilbertBasis.coe_mk hortho hdense.ge) n
  have hmem : ∀ n, b n ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := by
    intro n
    rw [hb n]
    exact (heig n).choose
  have hval : ∀ n, Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le ⟨b n, hmem n⟩ =
      ((energyEig L κ N n : ℝ) : ℂ) • b n := by
    intro n
    have hv := (heig n).choose_spec
    have key : ∀ (x : SymL2 L N) (hx : x ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain),
        x = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n →
        Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le ⟨x, hx⟩ =
          ((energyEig L κ N n : ℝ) : ℂ) • x := by
      rintro x hx rfl
      exact hv
    exact key (b n) (hmem n) (hb n)
  refine ⟨b, hmem, hb, ?_⟩
  exact TerraMultiRound89BetheCore.eigenbasis_form_core hc.le b (energyEig L κ N)
    (energyEig_nonneg L κ N) hmem hval

#print axioms physical_bethe_form_core
end QuantumNLS.TerraMultiRound89PhysicalCore
