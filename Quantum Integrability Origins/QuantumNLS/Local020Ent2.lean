import Mathlib
import QuantumNLS.LocalSpectralReduced
import QuantumNLS.Local020Entry
import QuantumNLS.Local020Refl
import QuantumNLS.Local020Conj

/-! LOCAL-020 stage S8d (part 1): the upper-left entry `a = (B e₀)₀` of the reduced matrix under reflection and
conjugation: `a_{-n}(u(L-·)) = -a_n(u)`, `a_{-n}(ū) = - conj a_n(u)` (companion of `refl_reduced`, `conj_reduced`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option synthInstance.maxHeartbeats 400000
noncomputable section

open QuantumNLS.LocalSpectral QuantumNLS.Local020Abs QuantumNLS.Local020AbsA ComplexConjugate

namespace QuantumNLS.Local020Ent2

variable {L κ : ℝ}

/-- The upper-left entry `(B e₀)₀`. -/
def aentry (B : E2 →L[ℂ] E2) : ℂ := (B (vec2 1 0)) 0

theorem aentry_id (p : ℂ) : aentry (p • ContinuousLinearMap.id ℂ E2) = p := by
  simp [aentry, vec2]

theorem aentry_add (A B : E2 →L[ℂ] E2) : aentry (A + B) = aentry A + aentry B := by
  simp [aentry]

theorem aentry_sub (A B : E2 →L[ℂ] E2) : aentry (A - B) = aentry A - aentry B := by
  simp [aentry]

theorem aentry_neg (A : E2 →L[ℂ] E2) : aentry (-A) = -aentry A := by
  simp [aentry]

theorem aentry_smul (c : ℂ) (A : E2 →L[ℂ] E2) : aentry (c • A) = c * aentry A := by
  simp [aentry]

theorem aentry_cjE (M : E2 ≃ₗᵢ[ℂ] E2) (m0 m1 : ℂ) (hm : ∀ v : E2, M v = vec2 (m0 * v 0) (m1 * v 1))
    (h0 : starRingEnd ℂ m0 * m0 = 1) (B : E2 →L[ℂ] E2) : aentry (cjE M B) = aentry B := by
  have hs : M.symm (vec2 1 0) = starRingEnd ℂ m0 • vec2 1 0 := by
    apply M.injective
    rw [M.apply_symm_apply, map_smul, hm]
    ext i
    fin_cases i <;> simp [vec2]
    exact h0.symm
  unfold aentry
  rw [cjE_apply, hs, map_smul, hm, vec2_zero]
  simp only [PiLp.smul_apply, smul_eq_mul]
  linear_combination (B (vec2 1 0)).ofLp 0 * h0

theorem aentry_cjT (B : E2 →L[ℂ] E2) :
    aentry (cjT QuantumNLS.Local020Conj.AE2 QuantumNLS.Local020Conj.AE2 B) = conj (aentry B) := by
  unfold aentry
  rw [cjT_apply]
  have h : QuantumNLS.Local020Conj.AE2.K (vec2 1 0) = vec2 1 0 := by
    show QuantumNLS.Local020Conj.kE (vec2 1 0) = vec2 1 0
    ext i; fin_cases i <;> simp [QuantumNLS.Local020Conj.kE, vec2]
  rw [h]
  show QuantumNLS.Local020Conj.kE (B (vec2 1 0)) 0 = _
  exact QuantumNLS.Local020Conj.kE_apply _ 0

theorem refl_reduced_a (hL : 0 < L) (n : ℤ) (r : ℝ) (u : ℝ → ℂ)
    (h' : SmallCompression L κ (fun x => u (L - x)) (-n) r) (hh : SmallCompression L κ u n r) :
    aentry (reducedMatrix2 L κ (fun x => u (L - x)) (-n) r h') = -aentry (reducedMatrix2 L κ u n r hh) := by
  have h : Inter (LuGraph L κ u (parity n)) (LuGraph L κ (fun x => u (L - x)) (parity (-n)))
      (QuantumNLS.Local020Refl.Wr hL) (-1) 0 := by
    rw [QuantumNLS.Local020Refl.parity_neg' n]; exact QuantumNLS.Local020Refl.inter_refl hL u (parity n)
  have hn : center L (-n) = 0 + (-1) * center L n := by
    unfold QuantumNLS.LocalSpectral.center; rw [QuantumNLS.Local020Refl.pm_neg']; push_cast; ring
  obtain ⟨-, hr⟩ := QuantumNLS.Local020Core.reduced_transport (κ := κ) r h (Or.inr rfl) hn
    (QuantumNLS.Local020Refl.doublet_rel hL n)
  rw [hr h' hh]
  have hs0 : starRingEnd ℂ (((parity n : ℤˣ) : ℤ) : ℂ) * (((parity n : ℤˣ) : ℤ) : ℂ) = 1 := by
    rw [map_intCast]; exact QuantumNLS.Local020Refl.sq_unit _
  have hc := aentry_cjE (QuantumNLS.Local020Refl.Mr n) _ _ (QuantumNLS.Local020Refl.Mr_apply n) hs0
    (reducedMatrix2 L κ u n r hh - (pm L n : ℂ) • ContinuousLinearMap.id ℂ E2)
  rw [aentry_add, aentry_id, aentry_smul, hc, aentry_sub, aentry_id, QuantumNLS.Local020Refl.pm_neg']
  push_cast
  ring

theorem conj_reduced_a (hL : 0 < L) (n : ℤ) (r : ℝ) (u : ℝ → ℂ)
    (h' : SmallCompression L κ (fun x => conj (u x)) (-n) r) (hh : SmallCompression L κ u n r) :
    aentry (reducedMatrix2 L κ (fun x => conj (u x)) (-n) r h') = -conj (aentry (reducedMatrix2 L κ u n r hh)) := by
  have h : InterA (LuGraph L κ u (parity n)) (LuGraph L κ (fun x => conj (u x)) (parity (-n)))
      QuantumNLS.Local020Conj.AH := by
    rw [QuantumNLS.Local020Refl.parity_neg' n]; exact QuantumNLS.Local020Conj.inter_conj hL u (parity n)
  have hn : center L (-n) = -(conj (center L n)) := by
    unfold QuantumNLS.LocalSpectral.center
    rw [QuantumNLS.Local020Refl.pm_neg', Complex.conj_ofReal]; push_cast; ring
  obtain ⟨-, hr⟩ := QuantumNLS.Local020CoreA.reduced_transportA (κ := κ) (KE := QuantumNLS.Local020Conj.AE2) r h hn
    (QuantumNLS.Local020Conj.embed_conj n)
  rw [hr h' hh, sub_eq_add_neg, aentry_add, aentry_id, aentry_neg, aentry_cjT, aentry_sub, aentry_id,
    QuantumNLS.Local020Refl.pm_neg', map_sub, Complex.conj_ofReal]
  push_cast
  ring

end QuantumNLS.Local020Ent2

#print axioms QuantumNLS.Local020Ent2.refl_reduced_a
#print axioms QuantumNLS.Local020Ent2.conj_reduced_a
