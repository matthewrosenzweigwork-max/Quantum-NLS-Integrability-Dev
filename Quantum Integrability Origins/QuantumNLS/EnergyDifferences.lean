/-
QuantumNLS.EnergyDifferences — energy trace norm of DIFFERENCES `D = ρ₁ − ρ₂` of positive
finite-energy operators (owner: opus_tensor).

Source: DEF-031 (definitions.tex:187) "The additive energy trace norm of a difference D is
‖A_k^{1/2} D A_k^{1/2}‖₁, defined through the corresponding trace-class form realization";
energy_trace.tex:18–26 (positive ρ with Tr(A_k ρ) < ∞) and :40–45 (eq:A1R-weighted-limit, applied
to `D = γ_N^{(k)}(t) − |v^{⊗k}⟩⟨v^{⊗k}|`).

Frozen import, read-only: EnergyRealization ER1 (sha256 d6805d9d…40f6), which brings EnergyForm
EF1, EnergyMultiplier 7394da58 and the trace-class chain.  PhysicalEnergy (the formalization) is NOT imported:
no frozen checkpoint was published.  So everything here is in the Fourier representation
`ℓ²(ι)` / `ℓ²(ℤ^k)`, and transport to the physical carrier is pending.

Content (generic multiplier `m ≥ 1`; kinetic instance `m = √a_k` at the end):
* `realOf ρ`: the (unique, EF1) positive trace-class realization of a positive finite-energy `ρ`;
* `ρ₁ − ρ₂ = W (T₁ − T₂) W`, `energyTraceNorm W (ρ₁ − ρ₂) = ‖T₁ − T₂‖₁ ≤ Tr(Aρ₁) + Tr(Aρ₂)`;
* comparison `‖ρ₁ − ρ₂‖₁ ≤ energyTraceNorm W (ρ₁ − ρ₂)` (since `‖A^{-1/2}‖ ≤ 1`);
* sequences: `energyTraceNorm W (ρ_N − ρ) → 0 ↔ ‖T_N − T‖₁ → 0`, and either implies
  `‖ρ_N − ρ‖₁ → 0`.
R-828C5F7E S2 hold unchanged.
-/
import QuantumNLS.EnergyRealization

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass QuantumNLS.EnergyForm QuantumNLS.EnergyRealization QuantumNLS.Energy
open Filter Topology

noncomputable section

namespace QuantumNLS.EnergyDifferences

section Generic

variable {ι : Type*} (m : ι → ℝ) (hm : ∀ n, 1 ≤ m n)

/-- The realization `A^{1/2} ρ A^{1/2}` of a positive finite-energy `ρ` (chosen from
`exists_realization`; unique by `EnergyForm.eq_of_mul_mul_eq`). -/
def realOf {ρ : L2 ι →L[ℂ] L2 ι} (hρ : ρ.IsPositive) (hE : formTrace m ρ ≠ ⊤) :
    L2 ι →L[ℂ] L2 ι :=
  Classical.choose (exists_realization m hm hρ hE)

variable {m hm}
variable {ρ : L2 ι →L[ℂ] L2 ι} (hρ : ρ.IsPositive) (hE : formTrace m ρ ≠ ⊤)

theorem realOf_isPositive : (realOf m hm hρ hE).IsPositive :=
  (Classical.choose_spec (exists_realization m hm hρ hE)).1

theorem realOf_isTraceClass : IsTraceClass (realOf m hm hρ hE) :=
  (Classical.choose_spec (exists_realization m hm hρ hE)).2.1

theorem realOf_spec : ρ = invCLM m hm * realOf m hm hρ hE * invCLM m hm :=
  (Classical.choose_spec (exists_realization m hm hρ hE)).2.2.1

theorem posTrace_realOf : posTrace (realOf m hm hρ hE) = formTrace m ρ :=
  (Classical.choose_spec (exists_realization m hm hρ hE)).2.2.2

theorem traceNorm_realOf : traceNorm (realOf m hm hρ hE) = formTrace m ρ := by
  rw [traceNorm_of_isPositive (realOf_isPositive hρ hE), posTrace_realOf]

/-- Any realization equals `realOf` (uniqueness, EF1). -/
theorem eq_realOf {T : L2 ι →L[ℂ] L2 ι} (hT : ρ = invCLM m hm * T * invCLM m hm) :
    T = realOf m hm hρ hE :=
  eq_of_mul_mul_eq (invCLM_injective m hm) (invCLM_denseRange m hm)
    (hT.symm.trans (realOf_spec hρ hE))

variable {ρ₁ ρ₂ : L2 ι →L[ℂ] L2 ι} (h₁ : ρ₁.IsPositive) (hE₁ : formTrace m ρ₁ ≠ ⊤)
  (h₂ : ρ₂.IsPositive) (hE₂ : formTrace m ρ₂ ≠ ⊤)

/-- **Difference realization:** `ρ₁ − ρ₂ = W (T₁ − T₂) W`. -/
theorem sub_spec : ρ₁ - ρ₂ =
    invCLM m hm * (realOf m hm h₁ hE₁ - realOf m hm h₂ hE₂) * invCLM m hm := by
  conv_lhs => rw [realOf_spec (hm := hm) h₁ hE₁, realOf_spec (hm := hm) h₂ hE₂]
  rw [mul_sub, sub_mul]

/-- `T₁ − T₂` is trace class. -/
theorem isTraceClass_sub : IsTraceClass (realOf m hm h₁ hE₁ - realOf m hm h₂ hE₂) := by
  have hneg : traceNorm (-realOf m hm h₂ hE₂) = traceNorm (realOf m hm h₂ hE₂) := by
    rw [show -realOf m hm h₂ hE₂ = (-1 : ℂ) • realOf m hm h₂ hE₂ from (neg_one_smul ℂ _).symm, traceNorm_smul]
    simp
  rw [IsTraceClass, sub_eq_add_neg]
  exact lt_of_le_of_lt (traceNorm_add_le _ _)
    (ENNReal.add_lt_top.mpr ⟨realOf_isTraceClass h₁ hE₁, by
      rw [hneg]; exact realOf_isTraceClass h₂ hE₂⟩)

/-- **Energy trace norm of a difference** = `‖T₁ − T₂‖₁` (the realization of `D`). -/
theorem energyTraceNorm_sub_eq :
    energyTraceNorm (invCLM m hm) (ρ₁ - ρ₂) =
      traceNorm (realOf m hm h₁ hE₁ - realOf m hm h₂ hE₂) :=
  energyTraceNorm_eq (invCLM_injective m hm) (invCLM_denseRange m hm) (sub_spec h₁ hE₁ h₂ hE₂)

include h₁ hE₁ h₂ hE₂ in
/-- **Bound:** `energyTraceNorm W (ρ₁ − ρ₂) ≤ Tr(Aρ₁) + Tr(Aρ₂)`. -/
theorem energyTraceNorm_sub_le :
    energyTraceNorm (invCLM m hm) (ρ₁ - ρ₂) ≤ formTrace m ρ₁ + formTrace m ρ₂ := by
  rw [energyTraceNorm_sub_eq h₁ hE₁ h₂ hE₂, sub_eq_add_neg]
  refine (traceNorm_add_le _ _).trans (le_of_eq ?_)
  rw [traceNorm_realOf h₁ hE₁,
    show -realOf m hm h₂ hE₂ = (-1 : ℂ) • realOf m hm h₂ hE₂ from (neg_one_smul ℂ _).symm, traceNorm_smul,
    traceNorm_realOf h₂ hE₂]
  simp

omit h₁ hE₁ h₂ hE₂ in
/-- **Comparison:** `‖ρ₁ − ρ₂‖₁ ≤ energyTraceNorm W (ρ₁ − ρ₂)` (because `‖A^{-1/2}‖ ≤ 1`). -/
theorem traceNorm_sub_le_energy :
    traceNorm (ρ₁ - ρ₂) ≤ energyTraceNorm (invCLM m hm) (ρ₁ - ρ₂) := by
  refine (traceNorm_le_energyTraceNorm (invCLM_injective m hm) (invCLM_denseRange m hm) _).trans ?_
  have h1 : ENNReal.ofReal (‖invCLM m hm‖ ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have := norm_invCLM_le (m := m) hm
    nlinarith [norm_nonneg (invCLM m hm)]
  calc ENNReal.ofReal (‖invCLM m hm‖ ^ 2) * energyTraceNorm (invCLM m hm) (ρ₁ - ρ₂)
      ≤ 1 * energyTraceNorm (invCLM m hm) (ρ₁ - ρ₂) := by gcongr
    _ = energyTraceNorm (invCLM m hm) (ρ₁ - ρ₂) := one_mul _

end Generic

/-! ## Convergence along a family of states -/

section Convergence

variable {ι : Type*} {m : ι → ℝ} {hm : ∀ n, 1 ≤ m n}
variable {α : Type*} {l : Filter α}
variable {ρN : α → L2 ι →L[ℂ] L2 ι} (hN : ∀ a, (ρN a).IsPositive)
  (hEN : ∀ a, formTrace m (ρN a) ≠ ⊤)
variable {ρ : L2 ι →L[ℂ] L2 ι} (hρ : ρ.IsPositive) (hE : formTrace m ρ ≠ ⊤)

/-- Energy-trace convergence is exactly trace-norm convergence of the realizations. -/
theorem tendsto_energy_iff_realOf :
    Tendsto (fun a => energyTraceNorm (invCLM m hm) (ρN a - ρ)) l (𝓝 0) ↔
      Tendsto (fun a => traceNorm (realOf m hm (hN a) (hEN a) - realOf m hm hρ hE)) l (𝓝 0) := by
  have e : ∀ a, energyTraceNorm (invCLM m hm) (ρN a - ρ) =
      traceNorm (realOf m hm (hN a) (hEN a) - realOf m hm hρ hE) :=
    fun a => energyTraceNorm_sub_eq (hN a) (hEN a) hρ hE
  simp_rw [e]

/-- **Energy-trace convergence implies trace-norm convergence** (valid for any family; no
positivity needed for this direction). -/
theorem tendsto_traceNorm_of_energy_sub
    (h : Tendsto (fun a => energyTraceNorm (invCLM m hm) (ρN a - ρ)) l (𝓝 0)) :
    Tendsto (fun a => traceNorm (ρN a - ρ)) l (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
    fun _ => traceNorm_sub_le_energy (hm := hm)

end Convergence

/-! ## The kinetic instance `A_k = 1 + Σ D_j²` on `ℓ²(ℤ^k)` -/

section Kinetic

variable (L : ℝ) (k : ℕ) {ρ₁ ρ₂ : L2 (Mom k) →L[ℂ] L2 (Mom k)}

/-- **DEF-031 for differences (Fourier representation).**  For positive `ρ₁, ρ₂` with
`Tr(A_k ρᵢ) < ∞`: `D = ρ₁ − ρ₂` has the trace-class realization `T₁ − T₂`,
`‖A_k^{1/2} D A_k^{1/2}‖₁ = ‖T₁ − T₂‖₁ ≤ Tr(A_kρ₁) + Tr(A_kρ₂)`, and `‖D‖₁ ≤ ‖A_k^{1/2} D A_k^{1/2}‖₁`. -/
theorem kinetic_difference (h₁ : ρ₁.IsPositive) (hE₁ : kinTrace L k ρ₁ ≠ ⊤)
    (h₂ : ρ₂.IsPositive) (hE₂ : kinTrace L k ρ₂ ≠ ⊤) :
    ∃ T : L2 (Mom k) →L[ℂ] L2 (Mom k), IsTraceClass T ∧
      ρ₁ - ρ₂ = AhalfInv L k * T * AhalfInv L k ∧
      energyTraceNorm (AhalfInv L k) (ρ₁ - ρ₂) = traceNorm T ∧
      energyTraceNorm (AhalfInv L k) (ρ₁ - ρ₂) ≤ kinTrace L k ρ₁ + kinTrace L k ρ₂ ∧
      traceNorm (ρ₁ - ρ₂) ≤ energyTraceNorm (AhalfInv L k) (ρ₁ - ρ₂) := by
  rw [kinTrace_eq_formTrace] at hE₁ hE₂ ⊢
  rw [kinTrace_eq_formTrace]
  exact ⟨_, isTraceClass_sub (hm := one_le_kinSqrt L k) h₁ hE₁ h₂ hE₂,
    sub_spec h₁ hE₁ h₂ hE₂, energyTraceNorm_sub_eq h₁ hE₁ h₂ hE₂,
    energyTraceNorm_sub_le h₁ hE₁ h₂ hE₂, traceNorm_sub_le_energy⟩

/-- **Kinetic energy-trace convergence implies trace-norm convergence** (Fourier representation). -/
theorem kinetic_tendsto_traceNorm {α : Type*} {l : Filter α}
    {ρN : α → L2 (Mom k) →L[ℂ] L2 (Mom k)} {ρ : L2 (Mom k) →L[ℂ] L2 (Mom k)}
    (h : Tendsto (fun a => energyTraceNorm (AhalfInv L k) (ρN a - ρ)) l (𝓝 0)) :
    Tendsto (fun a => traceNorm (ρN a - ρ)) l (𝓝 0) :=
  tendsto_traceNorm_of_energy_sub (hm := one_le_kinSqrt L k) h

end Kinetic

end QuantumNLS.EnergyDifferences

#print axioms QuantumNLS.EnergyDifferences.sub_spec
#print axioms QuantumNLS.EnergyDifferences.isTraceClass_sub
#print axioms QuantumNLS.EnergyDifferences.energyTraceNorm_sub_eq
#print axioms QuantumNLS.EnergyDifferences.energyTraceNorm_sub_le
#print axioms QuantumNLS.EnergyDifferences.traceNorm_sub_le_energy
#print axioms QuantumNLS.EnergyDifferences.tendsto_energy_iff_realOf
#print axioms QuantumNLS.EnergyDifferences.tendsto_traceNorm_of_energy_sub
#print axioms QuantumNLS.EnergyDifferences.kinetic_difference
#print axioms QuantumNLS.EnergyDifferences.kinetic_tendsto_traceNorm
