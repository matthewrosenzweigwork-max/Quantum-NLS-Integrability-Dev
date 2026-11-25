import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Abs
import QuantumNLS.Local020AbsA

/-! LOCAL-020 stage S5b: the antiunitary intertwining specialised to the DEF-049 objects (analogue of
`Local020Core.reduced_transport`).  Hypotheses: `Inter` for the graphs with `(f, φ) ↦ (Kf, -Kφ)`, centres
`p_{n'} = -conj p_n`, and `embed (n') = K_E embed(n) K_H`-type relation.  Conclusion: `SmallCompression` equivalent and
`B' = p_{n'} 1 - K_E (B - p_n 1) K_E`. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open QuantumNLS.LocalSpectral QuantumNLS.Local020Abs QuantumNLS.Local020AbsA ComplexConjugate

namespace QuantumNLS.Local020CoreA

variable {L κ : ℝ}

theorem conj_inv_2pi : conj ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) = -((2 * (Real.pi : ℂ) * Complex.I)⁻¹) := by
  rw [map_inv₀]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  have : (2 : ℂ) * (Real.pi : ℂ) * -Complex.I = -(2 * (Real.pi : ℂ) * Complex.I) := by ring
  rw [this, inv_neg]

theorem resolvent_eq' (u : ℝ → ℂ) (σ : ℤˣ) :
    (fun z => LocalSpectral.resolvent L κ u σ z) = fun z => res (LuGraph L κ u σ) z := rfl

theorem rieszProj_transportA {u u' : ℝ → ℂ} {σ σ' : ℤˣ} {n n' : ℤ} (r : ℝ) {K : AntiU (H2 L)}
    (h : InterA (LuGraph L κ u σ) (LuGraph L κ u' σ') K) (hn : center L n' = -(conj (center L n))) :
    rieszProj L κ u' σ' n' r = cjT K K (rieszProj L κ u σ n r) := by
  unfold rieszProj
  rw [hn, resolvent_eq', resolvent_eq', riesz_transportA h, cjT_smul, conj_inv_2pi, smul_neg, neg_smul]

theorem dressedIntegral_transportA {u u' : ℝ → ℂ} {n n' : ℤ} (r : ℝ) {K : AntiU (H2 L)}
    (h : InterA (LuGraph L κ u (parity n)) (LuGraph L κ u' (parity n')) K)
    (hn : center L n' = -(conj (center L n))) :
    dressedIntegral L κ u' n' r = -(cjT K K (dressedIntegral L κ u n r)) := by
  unfold dressedIntegral
  have e : (fun z => (z - center L n') • LocalSpectral.resolvent L κ u' (parity n') z) =
      fun z => (z - (-(conj (center L n)))) • res (LuGraph L κ u' (parity n')) z := by
    rw [hn]; rfl
  rw [e, hn, dressed_transportA h, cjT_smul, conj_inv_2pi, neg_smul, neg_neg]
  rfl

theorem reduced_transportA {u u' : ℝ → ℂ} {n n' : ℤ} (r : ℝ) {K : AntiU (H2 L)} {KE : AntiU E2}
    (h : InterA (LuGraph L κ u (parity n)) (LuGraph L κ u' (parity n')) K)
    (hn : center L n' = -(conj (center L n))) (hE : embed L n' = cjT KE K (embed L n)) :
    (SmallCompression L κ u' n' r ↔ SmallCompression L κ u n r) ∧
    ∀ (h' : SmallCompression L κ u' n' r) (hh : SmallCompression L κ u n r),
      reducedMatrix2 L κ u' n' r h' =
        (pm L n' : ℂ) • ContinuousLinearMap.id ℂ E2 -
          cjT KE KE (reducedMatrix2 L κ u n r hh - (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2) := by
  have hP : perturbedProj L κ u' n' r = cjT K K (perturbedProj L κ u n r) :=
    rieszProj_transportA r h hn
  have hD : dressedIntegral L κ u' n' r = -(cjT K K (dressedIntegral L κ u n r)) :=
    dressedIntegral_transportA r h hn
  have hcf : ∀ k : ℕ, conj ((invSqrtCoeff k : ℝ) : ℂ) = ((invSqrtCoeff k : ℝ) : ℂ) :=
    fun k => Complex.conj_ofReal _
  have hC : compressionMatrix L κ u' n' r = cjT KE KE (compressionMatrix L κ u n r) := by
    have := cmpM_transportA K KE (perturbedProj L κ u n r) (embed L n) (embed L n') hE
    rw [← hP] at this
    exact this
  refine ⟨?_, fun h' hh => ?_⟩
  · unfold SmallCompression
    rw [hC, show cjT KE KE (compressionMatrix L κ u n r) - 1 =
      cjT KE KE (compressionMatrix L κ u n r - 1) by rw [cjT_sub, cjT_one], norm_cjT]
  · have key := redM_transportA K KE (fun k => ((invSqrtCoeff k : ℝ) : ℂ)) (perturbedProj L κ u n r)
      (dressedIntegral L κ u n r) (embed L n) (embed L n') hcf (pm L n : ℂ) (pm L n' : ℂ) hE
    rw [← hP, ← hD] at key
    exact key

#print axioms QuantumNLS.Local020CoreA.reduced_transportA
end QuantumNLS.Local020CoreA
