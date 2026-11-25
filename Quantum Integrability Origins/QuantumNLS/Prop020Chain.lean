import QuantumNLS.Prop020Vector
import QuantumNLS.Prop019Linearization

/-!
# PROP-020 (`Q7A:thm:main`), Z3b part 2: the phase step, the trace-norm chain and the rate exponents

Source: proof of `Q7A:thm:main` (`window_reconstruction.tex:254`): "All these operators share their spectral resolution, so
the inequality `|e^{−ix} − e^{−iy}| ≤ |x − y|` gives the same Hilbert-norm error for the time-one evolutions. The scalar drops
out of their rank-one projectors. ... partial trace is contractive and, for normalized vectors `v, w`,
`‖|v⟩⟨v| − |w⟩⟨w|‖₁ ≤ 2‖v − w‖`. Apply this twice to replace `Φ_N` by `u^{⊗N}`, and once to replace the full initial tensor by
`Ψ_N`. This proves `eq:finalrate`." Generic Hilbert-space statements (Z3a `Prop020Vector`, Z1 `Prop020Diag`):

* `evolution_basis`: the joint charge evolution acts on the actual Bethe vectors by `e^{−it Σ_r t_r Q_r(m)}`;
* `phase_step`: Hilbert-norm error of the time-one evolutions from an eigenvalue bound on `𝓔_N`
  (`diag_apply_le`, `norm_exp_sub_le`);
* `chain`: the trace-norm chain (`traceNorm_add_le`, `traceNorm_gamma_sub_le`, `reducedDensityPower_phase`);
* `pco`, `pw_pco`, `sum_pco`, `sum_abs_pco`: a collection of charge orders and a joint time as a coefficient vector;
* `rate_le`, `rate_tendsto`: the exponents of `eq:finalrate` (`cut_bounds`).
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop020Chain

open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.PROP018Probability (cutN cut_bounds)
open QuantumNLS.Prop019Linearization (pw)
open QuantumNLS.Prop020Vector (norm_exp_sub_le diag_apply_le traceNorm_gamma_sub_le)
open QuantumNLS.Prop020Diag (evol_eigen reducedDensityPower_phase)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.TraceClass (traceNorm traceNorm_add_le)

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. The phase step (Hilbert-norm error of the time-one evolutions) -/

theorem evolution_basis {N : ℕ} (bs : HilbertBasis (MArr N) ℂ (QuantumNLS.PhysicalTensor.physSector L N))
    (ev : MArr N → ℝ) (t : ℝ) (m : MArr N) :
    QuantumNLS.BetheSpectralCharges.evolution bs ev t (bs m) = QuantumNLS.DiagonalMultiplier.phase ev t m • bs m := by
  apply bs.repr.injective
  ext m'
  simp only [HilbertBasis.repr_apply_apply, QuantumNLS.BetheSpectralCharges.evolution_coord, inner_smul_right]
  by_cases hm : m' = m
  · rw [hm]
  · rw [bs.orthonormal.inner_eq_zero hm, mul_zero, mul_zero]

/-- **The phase step** (source: "All these operators share their spectral resolution, so the inequality
`|e^{−ix} − e^{−iy}| ≤ |x − y|` gives the same Hilbert-norm error for the time-one evolutions"): if `U_Q` and `T₀` are diagonal
in the basis with eigenvalues `e^{−i e_m}` and `x_m`, and `|e_m − c − x_m| ≤ δ` on `S`, then for a unit vector supported on `S`,
`‖U_Q Φ − e^{−ic} e^{−iT₀} Φ‖ ≤ δ`. -/
theorem phase_step {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (bs : HilbertBasis ι ℂ H) (UQ : H ≃ₗᵢ[ℂ] H) (e : ι → ℝ)
    (hUQ : ∀ m, UQ (bs m) = Complex.exp (-((e m : ℝ) : ℂ) * Complex.I) • bs m)
    (T0 : H →L[ℂ] H) (x : ι → ℝ) (hT0 : ∀ m, T0 (bs m) = ((x m : ℝ) : ℂ) • bs m) (cs : ℝ) (S : Set ι) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : ∀ m ∈ S, |e m - cs - x m| ≤ δ) (Φ : H) (hΦ : ‖Φ‖ = 1)
    (hsupp : ∀ m ∉ S, ⟪bs m, Φ⟫_ℂ = 0) :
    ‖UQ Φ - Complex.exp (-((cs : ℝ) : ℂ) * Complex.I) • evol T0 1 Φ‖ ≤ δ := by
  set c := Complex.exp (-((cs : ℝ) : ℂ) * Complex.I) with hc
  let Dop : H →L[ℂ] H := UQ.toLinearIsometry.toContinuousLinearMap - c • evol T0 1
  have hDapp : ∀ v, Dop v = UQ v - c • evol T0 1 v := fun v => rfl
  have hD : ∀ m, Dop (bs m) = (Complex.exp (-((e m : ℝ) : ℂ) * Complex.I) -
      c * Complex.exp (-((1 : ℝ) : ℂ) * (Complex.I * ((x m : ℝ) : ℂ)))) • bs m := by
    intro m
    rw [hDapp, hUQ m, evol_eigen T0 (hT0 m) 1, smul_smul, ← sub_smul]
  have hb : ∀ m ∈ S, ‖Complex.exp (-((e m : ℝ) : ℂ) * Complex.I) -
      c * Complex.exp (-((1 : ℝ) : ℂ) * (Complex.I * ((x m : ℝ) : ℂ)))‖ ≤ δ := by
    intro m hm
    have e1 : c * Complex.exp (-((1 : ℝ) : ℂ) * (Complex.I * ((x m : ℝ) : ℂ))) =
        Complex.exp (-((cs + x m : ℝ) : ℂ) * Complex.I) := by
      rw [hc, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1]
    refine (norm_exp_sub_le (e m) (cs + x m)).trans ?_
    have := hδ m hm
    rwa [show e m - (cs + x m) = e m - cs - x m by ring]
  have := diag_apply_le bs Dop _ hD S hδ0 hb Φ hsupp
  rw [hΦ, mul_one, hDapp] at this
  exact this

/-! ## 2. The trace-norm chain -/

section Chain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `γ^{(k)}` of a symmetric vector. -/
def gam (k q : ℕ) (v : SymSector ℂ E (k + q)) :=
  reducedDensityPower k q (v : HilbertTensorPower ℂ E (k + q))

theorem gam_le (k q : ℕ) (x y : SymSector ℂ E (k + q)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    traceNorm (gam k q x - gam k q y) ≤ ENNReal.ofReal (2 * ‖x - y‖) := by
  have h := traceNorm_gamma_sub_le k q (x : HilbertTensorPower ℂ E (k + q)) (y : HilbertTensorPower ℂ E (k + q))
    (by rw [Submodule.norm_coe]; exact hx) (by rw [Submodule.norm_coe]; exact hy)
  rwa [← Submodule.coe_sub, Submodule.norm_coe] at h

/-- **The trace-norm chain of the proof of `Q7A:thm:main`**: replace `Ψ_N` by `u^{⊗N}` and then by `Φ_N` under the charge
evolution, compare with `e^{−ic}e^{−iNC₀}Φ_N` (phase step; the scalar drops out of the projector), apply PROP-019, and replace
`Φ_N` by `u^{⊗N}` under the linear evolution. -/
theorem chain (k q : ℕ) (UQ : SymSector ℂ E (k + q) ≃ₗᵢ[ℂ] SymSector ℂ E (k + q))
    (UC UL : SymSector ℂ E (k + q) →L[ℂ] SymSector ℂ E (k + q)) (hUC : ∀ x, ‖UC x‖ = ‖x‖)
    (hUL : ∀ x, ‖UL x‖ = ‖x‖) (Ψ w Φ : SymSector ℂ E (k + q)) (hΨ : ‖Ψ‖ = 1) (hw : ‖w‖ = 1)
    (hΦ : ‖Φ‖ = 1) (c : ℂ) (hc : ‖c‖ = 1) (δ1 δ4 : ℝ) (h1 : ‖UQ Φ - c • UC Φ‖ ≤ δ1) (hδ4 : 0 ≤ δ4)
    (h4 : traceNorm (gam k q (UC Φ) - gam k q (UL Φ)) ≤ ENNReal.ofReal δ4) :
    traceNorm (gam k q (UQ Ψ) - gam k q (UL w)) ≤
      ENNReal.ofReal (2 * ‖Ψ - w‖ + 4 * ‖w - Φ‖ + 2 * δ1 + δ4) := by
  have hUQ : ∀ x, ‖UQ x‖ = ‖x‖ := fun x => UQ.norm_map x
  have nUQ : ∀ x y, ‖UQ x - UQ y‖ = ‖x - y‖ := fun x y => by rw [← map_sub, hUQ]
  have nUL : ∀ x y, ‖UL x - UL y‖ = ‖x - y‖ := fun x y => by rw [← map_sub, hUL]
  have hδ1 : 0 ≤ δ1 := (norm_nonneg _).trans h1
  have t1 : traceNorm (gam k q (UQ Ψ) - gam k q (UQ w)) ≤ ENNReal.ofReal (2 * ‖Ψ - w‖) := by
    have := gam_le k q (UQ Ψ) (UQ w) (by rw [hUQ, hΨ]) (by rw [hUQ, hw])
    rwa [nUQ] at this
  have t2 : traceNorm (gam k q (UQ w) - gam k q (UQ Φ)) ≤ ENNReal.ofReal (2 * ‖w - Φ‖) := by
    have := gam_le k q (UQ w) (UQ Φ) (by rw [hUQ, hw]) (by rw [hUQ, hΦ])
    rwa [nUQ] at this
  have t3 : traceNorm (gam k q (UQ Φ) - gam k q (UC Φ)) ≤ ENNReal.ofReal (2 * δ1) := by
    have hph : gam k q (UC Φ) = gam k q (c • UC Φ) := by
      unfold gam
      rw [Submodule.coe_smul,
        reducedDensityPower_phase k q ((UC Φ : SymSector ℂ E (k + q)) : HilbertTensorPower ℂ E (k + q)) hc]
    rw [hph]
    refine (gam_le k q _ _ (by rw [hUQ, hΦ]) (by rw [norm_smul, hc, one_mul, hUC, hΦ])).trans
      (ENNReal.ofReal_le_ofReal (by linarith))
  have t5 : traceNorm (gam k q (UL Φ) - gam k q (UL w)) ≤ ENNReal.ofReal (2 * ‖w - Φ‖) := by
    have := gam_le k q (UL Φ) (UL w) (by rw [hUL, hΦ]) (by rw [hUL, hw])
    rwa [nUL, norm_sub_rev] at this
  set X1 := gam k q (UQ Ψ) with hX1
  set X2 := gam k q (UQ w) with hX2
  set X3 := gam k q (UQ Φ) with hX3
  set X4 := gam k q (UC Φ) with hX4
  set X5 := gam k q (UL Φ) with hX5
  set X6 := gam k q (UL w) with hX6
  have e : X1 - X6 = (X1 - X2) + (X2 - X3) + (X3 - X4) + (X4 - X5) + (X5 - X6) := by
    rw [sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel, sub_add_sub_cancel]
  have a1 := traceNorm_add_le ((X1 - X2) + (X2 - X3) + (X3 - X4) + (X4 - X5)) (X5 - X6)
  have a2 := traceNorm_add_le ((X1 - X2) + (X2 - X3) + (X3 - X4)) (X4 - X5)
  have a3 := traceNorm_add_le ((X1 - X2) + (X2 - X3)) (X3 - X4)
  have a4 := traceNorm_add_le (X1 - X2) (X2 - X3)
  have hsum : traceNorm (X1 - X6) ≤ traceNorm (X1 - X2) + traceNorm (X2 - X3) + traceNorm (X3 - X4) +
      traceNorm (X4 - X5) + traceNorm (X5 - X6) := by
    rw [e]
    calc _ ≤ _ := a1
      _ ≤ _ := add_le_add a2 le_rfl
      _ ≤ _ := add_le_add (add_le_add a3 le_rfl) le_rfl
      _ ≤ _ := add_le_add (add_le_add (add_le_add a4 le_rfl) le_rfl) le_rfl
  refine hsum.trans ((add_le_add (add_le_add (add_le_add (add_le_add t1 t2) t3) h4) t5).trans ?_)
  have hn1 := norm_nonneg (Ψ - w)
  have hn2 := norm_nonneg (w - Φ)
  have s : ENNReal.ofReal (2 * ‖Ψ - w‖) + ENNReal.ofReal (2 * ‖w - Φ‖) + ENNReal.ofReal (2 * δ1) +
      ENNReal.ofReal δ4 + ENNReal.ofReal (2 * ‖w - Φ‖) =
      ENNReal.ofReal (2 * ‖Ψ - w‖ + 2 * ‖w - Φ‖ + 2 * δ1 + δ4 + 2 * ‖w - Φ‖) := by
    rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> linarith
  rw [s]
  exact ENNReal.ofReal_le_ofReal (le_of_eq (by ring))

end Chain

/-! ## 3. The joint time box as a coefficient vector -/

/-- The coefficients `p_t(x) = Σ_{r ∈ R} t_r x^r` of the joint generator, for a collection `R ⊆ {0,…,d}` of charge orders. -/
def pco (ords : Finset ℕ) (t : ℕ → ℝ) (r : ℕ) : ℝ := if r ∈ ords then t r else 0

theorem pw_pco (d : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (t : ℕ → ℝ) :
    pw d 1 (pco ords t) = fun z => ∑ r ∈ ords, ((t r : ℝ) : ℂ) * z ^ r := by
  funext z
  unfold pw
  calc ∑ r ∈ Finset.range (d + 1), ((1 * pco ords t r : ℝ) : ℂ) * z ^ r =
        ∑ r ∈ ords, ((1 * pco ords t r : ℝ) : ℂ) * z ^ r :=
        (Finset.sum_subset hords fun r _ hr => by simp [pco, hr]).symm
    _ = _ := Finset.sum_congr rfl fun r hr => by simp [pco, hr]

theorem sum_pco (d : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (t e : ℕ → ℝ) :
    ∑ r ∈ Finset.range (d + 1), pco ords t r * e r = ∑ r ∈ ords, t r * e r := by
  calc ∑ r ∈ Finset.range (d + 1), pco ords t r * e r = ∑ r ∈ ords, pco ords t r * e r :=
        (Finset.sum_subset hords fun r _ hr => by simp [pco, hr]).symm
    _ = _ := Finset.sum_congr rfl fun r hr => by simp [pco, hr]

theorem sum_abs_pco (d : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (t : ℕ → ℝ) :
    ∑ r ∈ Finset.range (d + 1), |pco ords t r| = ∑ r ∈ ords, |t r| := by
  calc ∑ r ∈ Finset.range (d + 1), |pco ords t r| = ∑ r ∈ ords, |pco ords t r| :=
        (Finset.sum_subset hords fun r _ hr => by simp [pco, hr]).symm
    _ = _ := Finset.sum_congr rfl fun r hr => by simp [pco, hr]

/-! ## 4. The exponents of `eq:finalrate` -/

/-- `(1 + a_N)^{d+1}(ε_N + R_N^{−b} + N^{−1}) ≤ C (N^{α(d+1)−γ} + N^{−α(b−d−1)} + N^{α(d+1)−1})` (`cut_bounds`). -/
theorem rate_le (hL : 0 < L) {α γ : ℝ} (hα : 0 < α) (d b : ℕ) {N : ℕ} (hN : 1 ≤ N) :
    (1 + cutN L α N) ^ (d + 1) * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ α) ^ b + 1 / (N : ℝ)) ≤
      (3 + 3 * Real.pi / L) ^ (d + 1) * ((N : ℝ) ^ (α * ((d : ℝ) + 1) - γ) +
        (N : ℝ) ^ (-(α * ((b : ℝ) - d - 1))) + (N : ℝ) ^ (α * ((d : ℝ) + 1) - 1)) := by
  have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : (0 : ℝ) < N := by linarith
  have hxa : 1 ≤ (N : ℝ) ^ α := Real.one_le_rpow hx1 hα.le
  have hcb := cut_bounds (θ := α) hL N
  have hpiL : 0 ≤ 3 * Real.pi / L := by positivity
  have h1 : 1 + cutN L α N ≤ (3 + 3 * Real.pi / L) * (N : ℝ) ^ α := by
    have := mul_le_mul_of_nonneg_left hxa hpiL
    nlinarith [hcb.2.1]
  have hA0 : 0 ≤ 1 + cutN L α N := by nlinarith [hcb.1]
  have hA : (1 + cutN L α N) ^ (d + 1) ≤ (3 + 3 * Real.pi / L) ^ (d + 1) * (N : ℝ) ^ (α * ((d : ℝ) + 1)) := by
    calc (1 + cutN L α N) ^ (d + 1) ≤ ((3 + 3 * Real.pi / L) * (N : ℝ) ^ α) ^ (d + 1) :=
          pow_le_pow_left₀ hA0 h1 _
      _ = (3 + 3 * Real.pi / L) ^ (d + 1) * (N : ℝ) ^ (α * ((d : ℝ) + 1)) := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ α) (d + 1), ← Real.rpow_mul hx0.le, Nat.cast_add,
            Nat.cast_one]
  have hδ0 : 0 ≤ (N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ α) ^ b + 1 / (N : ℝ) := by
    have : 0 < (N : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hx0 _
    have : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hx0 _
    positivity
  have e1 : (N : ℝ) ^ (α * ((d : ℝ) + 1)) * (N : ℝ) ^ (-γ) = (N : ℝ) ^ (α * ((d : ℝ) + 1) - γ) := by
    rw [← Real.rpow_add hx0, ← sub_eq_add_neg]
  have e2 : (N : ℝ) ^ (α * ((d : ℝ) + 1)) * (1 / ((N : ℝ) ^ α) ^ b) =
      (N : ℝ) ^ (-(α * ((b : ℝ) - d - 1))) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ α) b, ← Real.rpow_mul hx0.le, one_div, ← Real.rpow_neg hx0.le,
      ← Real.rpow_add hx0]
    congr 1; ring
  have e3 : (N : ℝ) ^ (α * ((d : ℝ) + 1)) * (1 / (N : ℝ)) = (N : ℝ) ^ (α * ((d : ℝ) + 1) - 1) := by
    rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hx0, ← sub_eq_add_neg]
  calc (1 + cutN L α N) ^ (d + 1) * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ α) ^ b + 1 / (N : ℝ)) ≤
        ((3 + 3 * Real.pi / L) ^ (d + 1) * (N : ℝ) ^ (α * ((d : ℝ) + 1))) *
          ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ α) ^ b + 1 / (N : ℝ)) := mul_le_mul_of_nonneg_right hA hδ0
    _ = (3 + 3 * Real.pi / L) ^ (d + 1) * ((N : ℝ) ^ (α * ((d : ℝ) + 1)) * (N : ℝ) ^ (-γ) +
          (N : ℝ) ^ (α * ((d : ℝ) + 1)) * (1 / ((N : ℝ) ^ α) ^ b) +
          (N : ℝ) ^ (α * ((d : ℝ) + 1)) * (1 / (N : ℝ))) := by ring
    _ = _ := by rw [e1, e2, e3]

/-- All three exponents are negative under `(d+1)α < γ`, `d + 1 < b`, `(d+1)α < 1`. -/
theorem rate_tendsto {α γ : ℝ} (hα : 0 < α) (d b : ℕ) (hγ : α * ((d : ℝ) + 1) < γ) (hb : (d : ℝ) + 1 < b)
    (h1 : α * ((d : ℝ) + 1) < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (α * ((d : ℝ) + 1) - γ) + (N : ℝ) ^ (-(α * ((b : ℝ) - d - 1))) +
      (N : ℝ) ^ (α * ((d : ℝ) + 1) - 1)) atTop (𝓝 0) := by
  have t1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (α * ((d : ℝ) + 1) - γ)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < γ - α * ((d : ℝ) + 1) by linarith)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, neg_sub]
  have t2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(α * ((b : ℝ) - d - 1)))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (mul_pos hα (by linarith))).comp tendsto_natCast_atTop_atTop
  have t3 : Tendsto (fun N : ℕ => (N : ℝ) ^ (α * ((d : ℝ) + 1) - 1)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (show 0 < 1 - α * ((d : ℝ) + 1) by linarith)).comp
      tendsto_natCast_atTop_atTop
    refine this.congr fun N => ?_
    simp only [Function.comp_apply, neg_sub]
  have := (t1.add t2).add t3
  rwa [add_zero, add_zero] at this


end QuantumNLS.Prop020Chain

#print axioms QuantumNLS.Prop020Chain.evolution_basis
#print axioms QuantumNLS.Prop020Chain.phase_step
#print axioms QuantumNLS.Prop020Chain.chain
#print axioms QuantumNLS.Prop020Chain.pw_pco
#print axioms QuantumNLS.Prop020Chain.sum_pco
#print axioms QuantumNLS.Prop020Chain.sum_abs_pco
#print axioms QuantumNLS.Prop020Chain.rate_le
#print axioms QuantumNLS.Prop020Chain.rate_tendsto
