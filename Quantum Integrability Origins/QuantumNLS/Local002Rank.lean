import Mathlib
import QuantumNLS.Local002Free
import QuantumNLS.Local002Idem

/-! LOCAL-002 stage F: idempotence and rank two of `P_n(u)` from `FreeResolventHyp`.

`Cconst_le`: the printed constant `C_{L,s}` is bounded on `[r₁, 2π/L)` by an explicit constant
(termwise comparison of the series).  `proj_idem` and `proj_rank`: if `q* = 2√κ C_max ‖u‖ < 1/2` then
`P_n(u)` is idempotent (`annulus_idem` on `r/2 ≤ |z-p_n| ≤ r`) and has rank two
(`finrank_range_eq_of_close` against `P_n(0) = E E^†` and `proj_diff_bound`). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal ComplexConjugate
namespace QuantumNLS.Local002Rank
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Idem

variable {L κ : ℝ}

/-- The comparison series `∑ (2π(k+1)/L)^{-2}`. -/
def Tstar (L : ℝ) : ℝ := ∑' k : ℕ, (2 * Real.pi * ((k : ℝ) + 1) / L)⁻¹ ^ 2

/-- A uniform bound for `C_{L,s}`, `r₁ ≤ s < 2π/L`. -/
def Cmax (L r1 : ℝ) : ℝ := Real.sqrt (L⁻¹ * (r1⁻¹ ^ 2 + 2 * Tstar L))

lemma summable_Tstar (hL : 0 < L) : Summable fun k : ℕ => (2 * Real.pi * ((k : ℝ) + 1) / L)⁻¹ ^ 2 := by
  have h1 : Summable fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ)) ^ 2 :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  have h2 := h1.mul_left ((L / (2 * Real.pi)) ^ 2)
  refine h2.congr fun k => ?_
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

lemma Cconst_le (hL : 0 < L) {r1 s : ℝ} (hr1 : 0 < r1) (h1 : r1 ≤ s) (hs : s < 2 * Real.pi / L) :
    Cconst L s ≤ Cmax L r1 := by
  unfold Cconst Cmax
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hL.le)
  have hs0 : 0 < s := hr1.trans_le h1
  have e1 : s⁻¹ ^ 2 ≤ r1⁻¹ ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hs0.le) (inv_anti₀ hr1 h1) 2
  have hterm : ∀ k : ℕ, ((4 * Real.pi / L) * ((k : ℝ) + 1) - s)⁻¹ ^ 2 ≤
      (2 * Real.pi * ((k : ℝ) + 1) / L)⁻¹ ^ 2 := fun k => by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hpos : 0 < 2 * Real.pi * ((k : ℝ) + 1) / L := by positivity
    have hle : 2 * Real.pi * ((k : ℝ) + 1) / L ≤ (4 * Real.pi / L) * ((k : ℝ) + 1) - s := by
      have h2 : 2 * Real.pi / L ≤ 2 * Real.pi * ((k : ℝ) + 1) / L := by
        rw [div_le_div_iff_of_pos_right hL]; nlinarith [Real.pi_pos]
      have h3 : (4 * Real.pi / L) * ((k : ℝ) + 1) = 2 * (2 * Real.pi * ((k : ℝ) + 1) / L) := by ring
      linarith
    exact pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le hpos hle).le) (inv_anti₀ hpos hle) 2
  have hsum2 := summable_Tstar hL
  have hsum1 : Summable fun k : ℕ => ((4 * Real.pi / L) * ((k : ℝ) + 1) - s)⁻¹ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) hterm hsum2
  have e2 : ∑' k : ℕ, ((4 * Real.pi / L) * ((k : ℝ) + 1) - s)⁻¹ ^ 2 ≤ Tstar L :=
    Summable.tsum_le_tsum hterm hsum1 hsum2
  linarith

theorem proj_idem (hyp : FreeResolventHyp L κ) (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ < 1) :
    perturbedProj L κ (u : ℝ → ℂ) n r * perturbedProj L κ (u : ℝ → ℂ) n r =
      perturbedProj L κ (u : ℝ → ℂ) n r := by
  have hqn : ∀ s : ℝ, r / 2 ≤ s → s < 2 * Real.pi / L →
      qpar κ L s u ≤ 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ := fun s h1 hs2 => by
    have hC : Cconst L s ≤ Cmax L (r / 2) := Cconst_le hL (by positivity) h1 hs2
    unfold qpar
    have : 0 ≤ 2 * Real.sqrt κ := by positivity
    have h2 := mul_le_mul_of_nonneg_left hC this
    exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  have hM : ∀ z : ℂ, r / 2 ≤ ‖z - center L n‖ → ‖z - center L n‖ ≤ r →
      ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R ∧
        ‖R‖ ≤ (r / 2)⁻¹ * (1 - 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖)⁻¹ := by
    intro z h1 h2
    have hs0 : 0 < ‖z - center L n‖ := lt_of_lt_of_le (by positivity) h1
    have hs2 : ‖z - center L n‖ < 2 * Real.pi / L := lt_of_le_of_lt h2 hr2
    have hqs := hqn _ h1 hs2
    have hq1 : qpar κ L ‖z - center L n‖ u < 1 := lt_of_le_of_lt hqs hq
    obtain ⟨R0, R, -, hR, -, hRn, -⟩ := perturbed_resolvent hyp hs0 hs2 n (z := z) rfl u hq1
    refine ⟨R, hR, hRn.trans ?_⟩
    have hpos1 : 0 < 1 - 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ := by linarith
    have hpos2 : 0 < 1 - qpar κ L ‖z - center L n‖ u := by linarith
    apply mul_le_mul (inv_anti₀ (by positivity) h1) (inv_anti₀ hpos1 (by linarith))
      (inv_nonneg.2 hpos2.le) (inv_nonneg.2 (by positivity))
  exact (annulus_idem (u := (u : ℝ → ℂ)) (σ := parity n) (n := n) (r1 := r / 2) (r2 := r)
    (by positivity) (by linarith) hM).2

theorem proj_rank (hyp : FreeResolventHyp L κ) (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) (n : ℤ) (u : Lp ℂ 2 (μI L))
    (hq : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ < 1 / 2) :
    Module.finrank ℂ (rng (perturbedProj L κ (u : ℝ → ℂ) n r)) = 2 := by
  have hq1 : 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ < 1 := by linarith
  have hP := proj_idem hyp hL hr hr2 n u hq1
  have hres : ∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r → ∃ R : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r := fun z hz =>
    hyp.res r n z hr hr2 hz
  have hQ : freeProj L κ n r * freeProj L κ n r = freeProj L κ n r := by
    rw [freeProj_eq hL hr hr2 n hres]
    have hinv := adjoint_embed_comp_embed hL n
    ext1 v
    have := congrArg (fun A : E2 →L[ℂ] E2 => A (ContinuousLinearMap.adjoint (embed L n) v)) hinv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at this
    show embed L n (ContinuousLinearMap.adjoint (embed L n)
      (embed L n (ContinuousLinearMap.adjoint (embed L n) v))) =
        embed L n (ContinuousLinearMap.adjoint (embed L n) v)
    rw [this]
  have hrk := finrank_freeProj (κ := κ) hL hr hr2 n hres
  have hfin : Module.Finite ℂ (rng (freeProj L κ n r)) :=
    Module.finite_of_finrank_pos (by rw [hrk]; norm_num)
  have hqq : qpar κ L r u < 1 / 2 := by
    have : qpar κ L r u ≤ 2 * Real.sqrt κ * Cmax L (r / 2) * ‖u‖ := by
      have hC : Cconst L r ≤ Cmax L (r / 2) := Cconst_le hL (by positivity) (by linarith) hr2
      unfold qpar
      have : 0 ≤ 2 * Real.sqrt κ := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC this) (norm_nonneg _)
    linarith
  have hd := proj_diff_bound hyp hr hr2 n u (by linarith)
  have hclose : ‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ < 1 := by
    refine lt_of_le_of_lt hd ?_
    have hq0 := qpar_nonneg κ L r u
    rw [div_lt_one (by linarith)]
    linarith
  have := (finrank_range_eq_of_close (P := perturbedProj L κ (u : ℝ → ℂ) n r)
    (Q := freeProj L κ n r) hP hQ hclose hfin).2
  rw [this, hrk]

end QuantumNLS.Local002Rank
#print axioms QuantumNLS.Local002Rank.proj_idem
#print axioms QuantumNLS.Local002Rank.proj_rank
