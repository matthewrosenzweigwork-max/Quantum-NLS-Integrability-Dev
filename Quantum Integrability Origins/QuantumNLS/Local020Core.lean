import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs

/-! LOCAL-020 stage S0b: the abstract intertwining lemma specialised to the DEF-049 objects
(`resolvent`, `rieszProj`, `dressedIntegral`, `compressionMatrix`, `normalizedIsometry2`, `reducedMatrix2`).

If a unitary `W` of `H2 L = L²(0,L;ℂ²)` carries the graph of `𝓛_u` on `D_{(-1)^n}` to the graph of `𝓛_{u'}` on
`D_{(-1)^{n'}}` by `(f,φ) ↦ (Wf, εWφ + cWf)` (`ε = ±1`), the centres satisfy
`p_{n'} = c + ε p_n`, and `W` carries the ordered doublet at `n` to the one at `n'` up to a unitary `M` of `ℂ²`
(`E' M = W E`), then the polar-normalized reduced matrices are related by
`B' = p_{n'} 1 + ε M (B - p_n 1) M⁻¹`, and `SmallCompression` is equivalent at both indices. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open QuantumNLS.LocalSpectral QuantumNLS.Local020Abs

namespace QuantumNLS.Local020Core

variable {L κ : ℝ}

theorem resolvent_eq (u : ℝ → ℂ) (σ : ℤˣ) (z : ℂ) :
    resolvent L κ u σ z = res (LuGraph L κ u σ) z := rfl

/-- Transport of the Riesz projection. -/
theorem rieszProj_transport {u u' : ℝ → ℂ} {σ σ' : ℤˣ} {n n' : ℤ} (r : ℝ)
    {W : H2 L ≃ₗᵢ[ℂ] H2 L} {ε c : ℂ} (h : Inter (LuGraph L κ u σ) (LuGraph L κ u' σ') W ε c)
    (hε : ε = 1 ∨ ε = -1) (hn : center L n' = c + ε * center L n) :
    rieszProj L κ u' σ' n' r = cjE W (rieszProj L κ u σ n r) := by
  unfold rieszProj
  rw [map_smul, hn]
  congr 1
  exact riesz_transport h hε (center L n) r

/-- Transport of the dressed integral (factor `ε`). -/
theorem dressedIntegral_transport {u u' : ℝ → ℂ} {n n' : ℤ} (r : ℝ)
    {W : H2 L ≃ₗᵢ[ℂ] H2 L} {ε c : ℂ}
    (h : Inter (LuGraph L κ u (parity n)) (LuGraph L κ u' (parity n')) W ε c)
    (hε : ε = 1 ∨ ε = -1) (hn : center L n' = c + ε * center L n) :
    dressedIntegral L κ u' n' r = ε • cjE W (dressedIntegral L κ u n r) := by
  unfold dressedIntegral
  rw [map_smul, smul_comm, hn]
  congr 1
  exact dressed_transport h hε (center L n) r

/-- The unitary `M` relating the embeddings of the doublets at `n` and `n'`. -/
def DoubletRel (W : H2 L ≃ₗᵢ[ℂ] H2 L) (M : E2 ≃ₗᵢ[ℂ] E2) (n n' : ℤ) : Prop :=
  (embed L n').comp (ic M) = (ic W).comp (embed L n)

/-- **Core transport.**  Both the smallness of the compression and the reduced matrix transform as stated. -/
theorem reduced_transport {u u' : ℝ → ℂ} {n n' : ℤ} (r : ℝ)
    {W : H2 L ≃ₗᵢ[ℂ] H2 L} {M : E2 ≃ₗᵢ[ℂ] E2} {ε c : ℂ}
    (h : Inter (LuGraph L κ u (parity n)) (LuGraph L κ u' (parity n')) W ε c)
    (hε : ε = 1 ∨ ε = -1) (hn : center L n' = c + ε * center L n) (hE : DoubletRel W M n n') :
    (SmallCompression L κ u' n' r ↔ SmallCompression L κ u n r) ∧
    ∀ (h' : SmallCompression L κ u' n' r) (hh : SmallCompression L κ u n r),
      reducedMatrix2 L κ u' n' r h' =
        (pm L n' : ℂ) • ContinuousLinearMap.id ℂ E2 +
          ε • cjE M (reducedMatrix2 L κ u n r hh - (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2) := by
  have hP : perturbedProj L κ u' n' r = cjE W (perturbedProj L κ u n r) :=
    rieszProj_transport r h hε hn
  have hC : compressionMatrix L κ u' n' r = cjE M (compressionMatrix L κ u n r) := by
    have := cmpM_transport W M (perturbedProj L κ u n r) (embed L n) (embed L n') hE
    rw [← hP] at this
    exact this
  refine ⟨?_, fun h' hh => ?_⟩
  · unfold SmallCompression
    rw [hC, show cjE M (compressionMatrix L κ u n r) - 1 = cjE M (compressionMatrix L κ u n r - 1) by
      rw [map_sub, cjE_one], norm_cjE]
  · have hD : dressedIntegral L κ u' n' r = ε • cjE W (dressedIntegral L κ u n r) :=
      dressedIntegral_transport r h hε hn
    have key := redM_transport W M (perturbedProj L κ u n r) (dressedIntegral L κ u n r) (embed L n)
      (embed L n') (fun k => (invSqrtCoeff k : ℂ)) ε (pm L n : ℂ) (pm L n' : ℂ) hE
      (by rcases hε with rfl | rfl <;> simp)
    rw [← hP, ← hD] at key
    exact key

end QuantumNLS.Local020Core

#print axioms QuantumNLS.Local020Core.reduced_transport
