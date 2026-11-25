import QuantumNLS.DiagSelfAdjointCommute
import QuantumNLS.LinearTailCommute
import QuantumNLS.UnconditionalBetheBasis
import QuantumNLS.ContactOperator

/-!
# R-36C23346 QG:lem:haar-linear-tail, Part 4: commutation of `L_N(t)` with the contact Hamiltonian `H_N`

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:798-830`, clause (b) (commutation with `H_N`).

Realized inputs (read-only, accepted or frozen):
* `UnconditionalBetheBasis.basis` (accepted R-8E4D05E7, ae212789): `BasisConclusion` at `c = κ/N`, which gives orthonormal
  normalized waves `normalizedWave L N c n` in `SymL2 L N` with `Hop c` eigenrelation `Hop c (normalizedWave n) = (Σ_j
  sourceRoots_j²) • normalizedWave n` and dense span;
* `UnconditionalBetheBasis.physicalBasis_position`: the physical basis is identified with the normalized waves through
  `symmetricPosition` and `labelArr`;
* `ContactOperator.Hop` and `Hop_isSelfAdjoint` (`H_{N,c}` is selfadjoint on `SymL2 L N`);
* `LinearTailCommute.genSum_meanField`, `genEigen` (frozen Part 3); `DiagSelfAdjointCommute.diag_selfAdjoint_commute`
  (frozen Part 4a, 678f886d).

Realization: `Sym^N L²(𝕋_L)` is realized as `SymL2 L N` through the isometry `symmetricPosition`. `L_N(t)` is transported to
`SymL2 L N` by `symGen`. The statement is for the contact operator `H_N = Hop (κ/N)` on that realization.

Proved here (standard axioms only): `genSum_commutes_contactHamiltonian`: for every `ψ` in the domain of `H_N`, `symGen ψ`
is in the domain of `H_N` and `H_N (symGen ψ) = symGen (H_N ψ)`.

Not in this module: clause (c), the marginal estimate (OPEN, exact statement in the report).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.LinearTailHamiltonian

open QuantumNLS.BethePhysicalTransfer QuantumNLS.ContactOperator QuantumNLS.BetheConditionalBasis
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BetheFreeFamily
open QuantumNLS.LinearTailGenerator QuantumNLS.LinearTailCommute QuantumNLS.GridEigen

variable (L : ℝ) [Fact (0 < L)]

/-- `L_N(t)` transported to the `SymL2` realization of `Sym^N L²(𝕋_L)`. -/
def symGen (κ : ℝ) (N : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) : SymL2 L N →L[ℂ] SymL2 L N :=
  (symmetricPosition L N).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((genSum L κ N s t).comp (symmetricPosition L N).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem symGen_sp (κ : ℝ) (N : ℕ) (s : Finset ℤ) (t : ℤ → ℝ) (x : SymSector ℂ (L2T L) N) :
    symGen L κ N s t (symmetricPosition L N x) = symmetricPosition L N (genSum L κ N s t x) := by
  unfold symGen
  simp

/-- **Commutation of `L_N(t)` with the contact Hamiltonian `H_N = Hop (κ/N)`** (`QG:lem:haar-linear-tail`, clause (b)).
On the `SymL2` realization of `Sym^N L²(𝕋_L)`: the domain of `H_N` is preserved and `H_N` intertwines `symGen`. -/
theorem genSum_commutes_contactHamiltonian (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N)
    (s : Finset ℤ) (t : ℤ → ℝ) :
    ∀ (ψ : SymL2 L N) (hψ : ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
        (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain),
      ∃ h : symGen L κ N s t ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
          (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain,
        Hop (L := L) (N := N) (κ / (N : ℝ)) (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le
            ⟨symGen L κ N s t ψ, h⟩ =
          symGen L κ N s t (Hop (L := L) (N := N) (κ / (N : ℝ))
            (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨ψ, hψ⟩) := by
  classical
  have hN0 : 0 < N := by omega
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN0)
  obtain ⟨-, -, -, -, -, hortho, hdense, heig⟩ :=
    QuantumNLS.UnconditionalBetheBasis.basis L N hN (κ / (N : ℝ)) hc
  let Bn := HilbertBasis.mk hortho hdense.ge
  have hB : ∀ n, Bn n = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n := fun n =>
    congrFun (HilbertBasis.coe_mk hortho hdense.ge) n
  have hmem : ∀ n, Bn n ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := fun n => by
    have key0 : ∀ x : SymL2 L N, x = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n →
        x ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := by
      rintro x rfl
      exact (heig n).choose
    exact key0 (Bn n) (hB n)
  let e : Label N → ℝ := fun n => ∑ j, (BetheSmooth.sourceRoots L n.val (κ / (N : ℝ)) j) ^ 2
  have hval : ∀ n, (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le) ⟨Bn n, hmem n⟩ = (e n : ℂ) • Bn n := by
    intro n
    have hv : (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le)
        ⟨normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n, (heig n).choose⟩ =
        (e n : ℂ) • normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n := (heig n).choose_spec
    have key1 : ∀ (x : SymL2 L N) (hx : x ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain),
        x = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n →
        (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le) ⟨x, hx⟩ = (e n : ℂ) • x := by
      rintro x hx rfl
      exact hv
    exact key1 (Bn n) (hmem n) (hB n)
  let lam : Label N → ℂ := fun n =>
    genEigen L κ hκ N hN0 s t (QuantumNLS.BetheConditionalBasis.labelArr N n)
  have hpos : ∀ n : Label N, normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n =
      symmetricPosition L N (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ
        (QuantumNLS.BetheConditionalBasis.labelArr N n)) := by
    intro n
    have h := QuantumNLS.UnconditionalBetheBasis.physicalBasis_position L N hN (κ / (N : ℝ)) hc
      (QuantumNLS.BetheConditionalBasis.labelArr N n)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  have hT : ∀ n : Label N, (symGen L κ N s t) (Bn n) = lam n • Bn n := by
    intro n
    rw [hB n, hpos n, symGen_sp, genSum_meanField L κ hκ N hN s t, map_smul]
  have key := QuantumNLS.DiagSelfAdjointCommute.diag_selfAdjoint_commute Bn
    (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le) (Hop_isSelfAdjoint (L := L) (N := N) (c := κ / (N : ℝ)) hc.le) e hmem hval
    (symGen L κ N s t) lam hT
  intro ψ hψ
  exact key ψ hψ

end QuantumNLS.LinearTailHamiltonian

#print axioms QuantumNLS.LinearTailHamiltonian.genSum_commutes_contactHamiltonian
