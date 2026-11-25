import Mathlib
import QuantumNLS.Local001FinalB
import QuantumNLS.Local002Final

/-! LOCAL-002 `lem:reset-analytic-projections` (spectral_reduction.tex:57), hypothesis-free.

`Local002Final.reset_analytic_projections` is stated under the single hypothesis `FreeResolventHyp L κ`
(the printed LOCAL-001, `lem:reset-free-resolvent`, spectral_reduction.tex:36-50).  Here that
hypothesis is PROVED from the accepted LOCAL-001 theorem
`QuantumNLS.ResetFreeResolventLOCAL001.reset_free_resolvent_estimates` (`Local001FinalB`, read-only import).

Reconciliation of the objects:
* resolvent: both modules use the same frozen `LocalSpectral.IsResolvent` / `LocalSpectral.resolvent`
  of `LocalSpectralOperator`; `Local002.resolvent_eq` identifies any `IsResolvent` witness with
  `LocalSpectral.resolvent` (uniqueness);
* constant: `Local002.Cconst L r` (series over `ℕ`, `4π/L (k+1)`) equals the LOCAL-001
  `resolventConstant L r` (series over `ℕ+`, `spacing L = 4π/L`) by `tsum_pnat_eq_tsum_succ`;
* the `V_u R` output: `Local002.Vpt κ w g = lopPt κ w 0 g` equals the LOCAL-001 `potentialPt κ w g`;
  `potentialResolventOutput` is the `L²` class of `x ↦ potentialPt κ (u x) (R φ x)`;
* the contour: `‖z - p_n‖ = r` is `OnGamma L r n z`; `r < 2π/L` is `r < spacing L / 2`;
* the parameter `κ`: LOCAL-001 is stated for `κ > 0`.  The free graph `LuGraph L κ 0 σ` does not depend on `κ`
  (`lopPt κ 0 d g = 2iJ d`), so `res` and `sup` for any real `κ` follow from `κ = 1`, and for `κ ≤ 0` the
  potential matrix vanishes (`√κ = 0`), so `pot` is trivial.  Hence `FreeResolventHyp L κ` holds for every `L κ`
  (a contour `0 < r < 2π/L` forces `L > 0`). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002Discharge
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA

variable {L κ : ℝ}

/-- The free graph does not depend on `κ`. -/
lemma freeGraph_kappa (L κ κ' : ℝ) (σ : ℤˣ) :
    LuGraph L κ (fun _ => 0) σ = LuGraph L κ' (fun _ => 0) σ := by
  ext p
  simp only [LuGraph, Set.mem_setOf_eq, lopPt_zero_pot]

lemma isResolvent_free_kappa (κ' : ℝ) {σ : ℤˣ} {z : ℂ} {R : H2 L →L[ℂ] H2 L} :
    IsResolvent L κ (fun _ => 0) σ z R ↔ IsResolvent L κ' (fun _ => 0) σ z R := by
  unfold IsResolvent
  rw [freeGraph_kappa L κ κ' σ]

/-- `Vpt` is the LOCAL-001 potential matrix. -/
lemma Vpt_eq_potentialPt (κ : ℝ) (w : ℂ) (g : E2) :
    Vpt κ w g = QuantumNLS.ResetFreeResolventLOCAL001.potentialPt κ w g := by
  unfold Vpt lopPt QuantumNLS.ResetFreeResolventLOCAL001.potentialPt
  rw [Jm_zero]; simp

lemma Vpt_nonpos (hκ : κ ≤ 0) (w : ℂ) (g : E2) : Vpt κ w g = 0 := by
  unfold Vpt lopPt
  rw [Jm_zero]
  ext i; fin_cases i <;> simp [vec2, Real.sqrt_eq_zero_of_nonpos hκ]

/-- The two constants agree. -/
lemma Cconst_eq (L r : ℝ) :
    Cconst L r = QuantumNLS.ResetFreeResolventLOCAL001.resolventConstant L r := by
  unfold Cconst QuantumNLS.ResetFreeResolventLOCAL001.resolventConstant
    QuantumNLS.ResetFreeResolventLOCAL001.resolventConstantSq QuantumNLS.ResetFreeResolventLOCAL001.spacing
  congr 3
  have h := tsum_pnat_eq_tsum_succ (f := fun k : ℕ => ((4 * Real.pi / L) * (k : ℝ) - r)⁻¹ ^ 2)
  rw [h]
  simp

lemma hsmall_of {L : ℝ} {r : ℝ} (hr2 : r < 2 * Real.pi / L) :
    r < QuantumNLS.ResetFreeResolventLOCAL001.spacing L / 2 := by
  unfold QuantumNLS.ResetFreeResolventLOCAL001.spacing
  have : 4 * Real.pi / L / 2 = 2 * Real.pi / L := by ring
  rw [this]; exact hr2

/-- The three fields of `FreeResolventHyp`, for `κ > 0`, from the accepted LOCAL-001 theorem. -/
lemma key (hL : 0 < L) (hκ : 0 < κ) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) {n : ℤ} {z : ℂ}
    (hz : ‖z - (pm L n : ℂ)‖ = r) :
    (∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (fun _ => 0) (parity n) z R ∧ ‖R‖ ≤ 1 / r) ∧
    (∀ (R : H2 L →L[ℂ] H2 L), IsResolvent L κ (fun _ => 0) (parity n) z R → ∀ φ : H2 L,
      ∀ᵐ x ∂(μI L), ‖(R φ : ℝ → E2) x‖ ≤ Cconst L r * ‖φ‖) ∧
    (∀ (R : H2 L →L[ℂ] H2 L), IsResolvent L κ (fun _ => 0) (parity n) z R →
      ∀ (u : Lp ℂ 2 (μI L)) (φ : H2 L),
        ∃ hm : MemLp (fun x => Vpt κ ((u : ℝ → ℂ) x) ((R φ : ℝ → E2) x)) 2 (μI L),
          ‖hm.toLp _‖ ≤ 2 * Real.sqrt κ * Cconst L r * ‖u‖ * ‖φ‖) := by
  have : Fact (0 < L) := ⟨hL⟩
  have hsmall := hsmall_of hr2
  have hz' : QuantumNLS.ResetFreeResolventLOCAL001.OnGamma L r n z := hz
  have hest := QuantumNLS.ResetFreeResolventLOCAL001.reset_free_resolvent_estimates (L := L) (r := r)
    κ hL hκ n hr hsmall hz' (0 : Lp ℂ 2 (μI L))
  have hcand := QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.freeResolventCandidate_isResolvent
    (L := L) (r := r) κ hL hr hsmall hz'
  have hreseq := resolvent_eq hcand
  refine ⟨⟨resolvent L κ (fun _ => 0) (parity n) z, ?_, ?_⟩, ?_, ?_⟩
  · rw [hreseq]; exact hcand
  · rw [one_div]; exact hest.1
  · intro R hR φ
    rw [Cconst_eq]
    have h2 := hest.2.1 φ
    rw [resolvent_eq hR] at h2
    exact h2
  · intro R hR u φ
    have hRr := resolvent_eq hR
    have hcoe := QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.potentialResolventOutput_coe
      (L := L) (r := r) κ hκ.le hL n hr hsmall hz' u φ
    have hmem : MemLp (fun x => Vpt κ ((u : ℝ → ℂ) x) ((R φ : ℝ → E2) x)) 2 (μI L) := by
      have h0 := (Lp.memLp (QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.potentialResolventOutput
        κ hκ.le hL n hr hsmall hz' u φ))
      refine h0.ae_eq ?_
      filter_upwards [hcoe] with x hx
      rw [hx, Vpt_eq_potentialPt]
      change QuantumNLS.ResetFreeResolventLOCAL001.potentialPt κ (u x) ((resolvent L κ (fun _ => 0) (parity n) z φ : ℝ → E2) x) = _
      rw [hRr]
    refine ⟨hmem, ?_⟩
    have heq : hmem.toLp _ = QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.potentialResolventOutput
        κ hκ.le hL n hr hsmall hz' u φ := by
      apply Lp.ext
      filter_upwards [hmem.coeFn_toLp, hcoe] with x h1 h2
      rw [h1, h2, Vpt_eq_potentialPt]
      change QuantumNLS.ResetFreeResolventLOCAL001.potentialPt κ (u x) ((R φ : ℝ → E2) x) =
        QuantumNLS.ResetFreeResolventLOCAL001.potentialPt κ (u x) ((resolvent L κ (fun _ => 0) (parity n) z φ : ℝ → E2) x)
      rw [hRr]
    rw [heq, Cconst_eq]
    have h4 := (QuantumNLS.ResetFreeResolventLOCAL001.reset_free_resolvent_estimates (L := L) (r := r)
      κ hL hκ n hr hsmall hz' u).2.2.2
    calc ‖QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.potentialResolventOutput
          κ hκ.le hL n hr hsmall hz' u φ‖
        = ‖QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.potentialResolvent
            κ hκ.le hL n hr hsmall hz' u φ‖ := rfl
      _ ≤ ‖QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.potentialResolvent
            κ hκ.le hL n hr hsmall hz' u‖ * ‖φ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (2 * Real.sqrt κ * QuantumNLS.ResetFreeResolventLOCAL001.resolventConstant L r * ‖u‖) * ‖φ‖ :=
          mul_le_mul_of_nonneg_right h4 (norm_nonneg _)

/-- **LOCAL-001 (`lem:reset-free-resolvent`) PROVED in the `FreeResolventHyp` encoding, for every `L`, `κ`.** -/
theorem free_resolvent_hyp (L κ : ℝ) : FreeResolventHyp L κ := by
  have hLpos : ∀ r : ℝ, 0 < r → r < 2 * Real.pi / L → 0 < L := by
    intro r hr hr2
    by_contra hneg
    push_neg at hneg
    have : 2 * Real.pi / L ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  -- a positive parameter agreeing with `κ` when `κ > 0`
  obtain ⟨κ₁, hκ₁, hκκ₁⟩ : ∃ κ₁ : ℝ, 0 < κ₁ ∧ (0 < κ → κ₁ = κ) :=
    ⟨if 0 < κ then κ else 1, by split_ifs with h <;> linarith, fun h => by simp [h]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro r n z hr hr2 hz
    have hL := hLpos r hr hr2
    obtain ⟨R, hR, hb⟩ := (key hL hκ₁ hr hr2 hz).1
    exact ⟨R, (isResolvent_free_kappa κ).mp hR, hb⟩
  · intro r n z R hr hr2 hz hR φ
    have hL := hLpos r hr hr2
    exact (key hL hκ₁ hr hr2 hz).2.1 R ((isResolvent_free_kappa κ₁).mp hR) φ
  · intro r n z R hr hr2 hz hR u φ
    have hL := hLpos r hr hr2
    by_cases hκ : 0 < κ
    · have := (key hL hκ hr hr2 hz).2.2 R hR u φ
      exact this
    · have hκ0 : κ ≤ 0 := not_lt.mp hκ
      have hsq : Real.sqrt κ = 0 := Real.sqrt_eq_zero_of_nonpos hκ0
      have h0 : (fun x => Vpt κ ((u : ℝ → ℂ) x) ((R φ : ℝ → E2) x)) = fun _ => (0 : E2) :=
        funext fun x => Vpt_nonpos hκ0 _ _
      have hm : MemLp (fun x => Vpt κ ((u : ℝ → ℂ) x) ((R φ : ℝ → E2) x)) 2 (μI L) := by
        rw [h0]; exact MemLp.zero
      refine ⟨hm, ?_⟩
      have : hm.toLp _ = 0 := by
        apply Lp.ext
        filter_upwards [hm.coeFn_toLp, Lp.coeFn_zero E2 2 (μI L)] with x h1 h2
        rw [h1, h2]; simp [Vpt_nonpos hκ0]
      rw [this, hsq]; simp

/-- **LOCAL-002 `lem:reset-analytic-projections`, with NO hypothesis beyond `0 < L` and the contour radius.**
Identical conclusion to `Local002Final.reset_analytic_projections`; `FreeResolventHyp L κ` is discharged
by `free_resolvent_hyp` from the accepted LOCAL-001. -/
theorem reset_analytic_projections (hL : 0 < L) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n : ℤ,
      (∀ u : Lp ℂ 2 (μI L), ‖u‖ < ρ →
        IsSelfAdjointGraph (LuGraph L κ (u : ℝ → ℂ) (parity n)) ∧
        (∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r →
          ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) z R) ∧
        Module.finrank ℂ (LinearMap.range
          (perturbedProj L κ (u : ℝ → ℂ) n r : H2 L →ₗ[ℂ] H2 L)) = 2 ∧
        ‖perturbedProj L κ (u : ℝ → ℂ) n r - freeProj L κ n r‖ ≤ C * ‖u‖) ∧
      AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => perturbedProj L κ (u : ℝ → ℂ) n r) (ball 0 ρ) :=
  QuantumNLS.Local002Final.reset_analytic_projections (free_resolvent_hyp L κ) hL hr hr2

end QuantumNLS.Local002Discharge
#print axioms QuantumNLS.Local002Discharge.free_resolvent_hyp
#print axioms QuantumNLS.Local002Discharge.reset_analytic_projections
