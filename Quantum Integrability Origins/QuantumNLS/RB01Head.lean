import Mathlib
import QuantumNLS.RB01CxDensity
import QuantumNLS.RB01SpecEig
import QuantumNLS.ComplexifiedTarget
import QuantumNLS.TerraMultiRound31FiniteActions

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01Head: the bounded holomorphic extensions of the theorem
(source `collective_actions.tex:49-66`: "They have bounded holomorphic extensions on a complexification of a possibly
smaller neighborhood. Each of the finitely many complementary actions has a holomorphic extension there as well.").

All extensions live on the one complexification `Cx(L²(𝕋_L))` (frozen `ProductTorusComplexification.Cx`) near
`ι u₀`; the real points are `ι u`.
* `trunc S`: the complex-linear truncation `x ↦ x − Σ_{n ∈ S} x_n e_n` of `ℓᵖ(ℤ; ℂ)` (`trunc_apply`), used to put
  `g` and `r` on `ℓ²({n ∉ S})`, `ℓ∞({n ∉ S})`, extended by zero.
* **`head_ext`** (complementary actions): for every finite `S ⊂ ℤ` there are `R > 0`, `M` and `I^c_n`, `n ∈ S`,
  complex analytic and bounded by `M` on `B(ι u₀, R)`, with `I^c_n(ι x) = I_n(x)` on `B(u₀, R)`. Via the frozen
  `ComplexifiedTarget.holomorphic_extension_of_analyticAt` applied to the finitely many real-analytic actions
  (`TerraMultiRound31CoordinateHessian.coordinate_analytic`), as one `ℂ^S`-valued map.
* **`ext_of_analyticAt`** (used for `g`): a real-analytic `T : L²(𝕋_L) → W` at `u₀`, `W` complex Banach, and every
  complex-linear image `A ∘ T`, have one bounded holomorphic extension on some `B(ι u₀, R)`.
* **`r_ext`** (transport of `r`): with `G` the frozen `RB01CxDensity.r_linf` map on `L² × L²`, the map
  `z ↦ trunc S (G (Φ z))`, `Φ = ComplexifiedConjugation.phiCLE starConj` (`Φ (ι u) = (u, ū)`), is complex analytic and
  bounded on `B(ι u₀, R)` and equals `trunc S (G (x, x̄))` at `ι x`. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Set Metric
open scoped ENNReal

namespace QuantumNLS.RB01Head

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.ProductTorusComplexification (Cx)
open QuantumNLS.TerraMultiRound30HessianBridge (Actions)

/-! ## Truncation -/

/-- `x ↦ x − Σ_{n ∈ S} x_n e_n` on `ℓᵖ(ℤ; ℂ)`. -/
def trunc (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : Finset ℤ) : lp (fun _ : ℤ => ℂ) p →L[ℂ] lp (fun _ : ℤ => ℂ) p :=
  ContinuousLinearMap.id ℂ _ - ∑ n ∈ S,
    (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p n).comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n)

theorem trunc_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (S : Finset ℤ) (x : lp (fun _ : ℤ => ℂ) p) (m : ℤ) :
    (trunc p S x : ℤ → ℂ) m = if m ∈ S then 0 else x m := by
  simp only [trunc, sub_apply, ContinuousLinearMap.id_apply, FunLike.coe_sum,
    Finset.sum_apply, ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, lp.coeFn_sub,
    Pi.sub_apply, lp.coeFn_sum]
  have h : ∀ n ∈ S, (lp.single p n (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n x) : ℤ → ℂ) m =
      if m = n then x m else 0 := by
    intro n _
    rw [lp.single_apply]
    by_cases hmn : m = n
    · subst hmn; simp [lp.evalCLM]
    · simp [hmn]
  rw [Finset.sum_congr rfl h, Finset.sum_ite_eq]
  split_ifs <;> simp

/-! ## Head actions -/

variable {L κ : ℝ} [Fact (0 < L)]

/-- **Holomorphic extensions of finitely many actions** on one complex ball around `ι u₀`. -/
theorem head_ext (hκ : 0 < κ) (u₀ : L2T L) (S : Finset ℤ) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∃ Ic : ℤ → Cx (L2T L) → ℂ, ∀ n ∈ S,
      AnalyticOnNhd ℂ (Ic n) (ball (Cx.ι u₀) R) ∧ (∀ z ∈ ball (Cx.ι u₀) R, ‖Ic n z‖ ≤ M) ∧
      ∀ x ∈ ball u₀ R, Ic n (Cx.ι x) = ((Actions hκ x n : ℝ) : ℂ) := by
  classical
  let T : L2T L → (S → ℂ) := fun u i => ((Actions hκ u i : ℝ) : ℂ)
  have hT : AnalyticAt ℝ T u₀ := by
    refine AnalyticAt.pi (fun i => ?_)
    exact Complex.ofRealCLM.analyticAt _ |>.comp
      (QuantumNLS.TerraMultiRound31CoordinateHessian.coordinate_analytic hκ (i : ℤ) u₀)
  obtain ⟨R, hR, M, Tc, -, hTa, hTb, hTe⟩ :=
    QuantumNLS.ComplexifiedTarget.holomorphic_extension_of_analyticAt (F := L2T L) hT
  refine ⟨R, hR, M, fun n z => if h : n ∈ S then Tc z ⟨n, h⟩ else 0, fun n hn => ⟨?_, ?_, ?_⟩⟩
  · intro z hz
    simp only [hn, ↓reduceDIte]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S => ℂ) ⟨n, hn⟩).analyticAt _ |>.comp (hTa z hz)
  · intro z hz
    simp only [hn, ↓reduceDIte]
    exact (norm_le_pi_norm (Tc z) ⟨n, hn⟩).trans (hTb z hz)
  · intro x hx
    simp only [hn, ↓reduceDIte, hTe x hx, T]

/-! ## Extensions of real-analytic maps -/

/-- A real-analytic map into a complex Banach space, followed by a complex-linear map, has one bounded holomorphic
extension near `ι u₀`. -/
theorem ext_of_analyticAt {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W]
    [IsScalarTower ℝ ℂ W] [CompleteSpace W] [NormedAddCommGroup W'] [NormedSpace ℂ W'] [NormedSpace ℝ W']
    [IsScalarTower ℝ ℂ W']
    {T : L2T L → W} {u₀ : L2T L} (hT : AnalyticAt ℝ T u₀) (A : W →L[ℂ] W') :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∃ Tc : Cx (L2T L) → W',
      AnalyticOnNhd ℂ Tc (ball (Cx.ι u₀) R) ∧ (∀ z ∈ ball (Cx.ι u₀) R, ‖Tc z‖ ≤ M) ∧
      ∀ x ∈ ball u₀ R, Tc (Cx.ι x) = A (T x) := by
  obtain ⟨R, hR, M, Tc, -, hTa, hTb, hTe⟩ :=
    QuantumNLS.ComplexifiedTarget.holomorphic_extension_of_analyticAt (F := L2T L) hT
  refine ⟨R, hR, ‖A‖ * M, fun z => A (Tc z), fun z hz => (A.analyticAt _).comp (hTa z hz), fun z hz => ?_,
    fun x hx => by show A (Tc (Cx.ι x)) = A (T x); rw [hTe x hx]⟩
  exact (A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hTb z hz) (norm_nonneg _))

/-! ## Transport of `r` -/

theorem ι_sub (x y : L2T L) : Cx.ι x - Cx.ι y = Cx.ι (x - y) := by
  have h := QuantumNLS.ProductTorusComplexification.Cx.ι_add (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem phi_ι' (x : L2T L) :
    QuantumNLS.ComplexifiedConjugation.phiCLE QuantumNLS.ComplexifiedConjugation.starConj (Cx.ι x) =
      (x, star x) := by
  rw [QuantumNLS.ComplexifiedConjugation.phi_ι]
  rfl

/-- **`r` on the complexification**: the frozen `r_linf` map `G` composed with `Φ = phiCLE starConj`, truncated. -/
theorem r_ext (hκ : 0 < κ) (u₀ : L2T L) :
    ∃ N : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : L2T L × L2T L → QuantumNLS.RB01LinfLift.Linf ℤ,
      (∀ x ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ, ∀ n : ℤ, ¬ (N : ℝ) < |(n : ℝ)| → G x n = 0) ∧
      (∀ u : L2T L, ‖u - u₀‖ < ρ → AnalyticAt ℝ (fun u' : L2T L => G (u', star u')) u) ∧
      (∀ u : L2T L, ‖u - u₀‖ < ρ → ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| →
        G (u, star u) n = QuantumNLS.RB01Density.rn hκ u n ∧ (QuantumNLS.RB01Density.rn hκ u n).im = 0 ∧
        1 / 2 < (QuantumNLS.RB01Density.rn hκ u n).re ∧ (QuantumNLS.RB01Density.rn hκ u n).re < 3 / 2) ∧
      ∀ S : Finset ℤ, ∃ R > (0 : ℝ), R ≤ ρ ∧ ∃ M : ℝ, ∃ rc : Cx (L2T L) → QuantumNLS.RB01LinfLift.Linf ℤ,
        AnalyticOnNhd ℂ rc (ball (Cx.ι u₀) R) ∧ (∀ z ∈ ball (Cx.ι u₀) R, ‖rc z‖ ≤ M) ∧
        ∀ x ∈ ball u₀ R, rc (Cx.ι x) = trunc ∞ S (G (x, star x)) := by
  obtain ⟨N, ρ, hρ, M, hM, G, hGa, hGb, -, hG0, hGr, hGs⟩ := QuantumNLS.RB01CxDensity.r_linf hκ u₀
  refine ⟨N, ρ, hρ, G, hG0, hGr, hGs, fun S => ?_⟩
  set Φ : Cx (L2T L) →L[ℂ] L2T L × L2T L :=
    (QuantumNLS.ComplexifiedConjugation.phiCLE QuantumNLS.ComplexifiedConjugation.starConj).toContinuousLinearMap
    with hΦ
  have hΦι : ∀ x, Φ (Cx.ι x) = (x, star x) := fun x => phi_ι' x
  set R := ρ / (‖Φ‖ + 1) with hRdef
  have hΦ0 := norm_nonneg Φ
  have hR : 0 < R := by positivity
  have hRρ : R ≤ ρ := by
    rw [hRdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hmem : ∀ z ∈ ball (Cx.ι u₀) R, Φ z ∈ ball ((u₀, star u₀) : L2T L × L2T L) ρ := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz ⊢
    rw [← hΦι, ← map_sub]
    calc ‖Φ (z - Cx.ι u₀)‖ ≤ ‖Φ‖ * ‖z - Cx.ι u₀‖ := Φ.le_opNorm _
      _ ≤ (‖Φ‖ + 1) * ‖z - Cx.ι u₀‖ := by nlinarith [norm_nonneg (z - Cx.ι u₀)]
      _ < (‖Φ‖ + 1) * R := by gcongr
      _ = ρ := by rw [hRdef]; field_simp
  refine ⟨R, hR, hRρ, ‖trunc ∞ S‖ * M, fun z => trunc ∞ S (G (Φ z)), fun z hz => ?_, fun z hz => ?_,
    fun x hx => ?_⟩
  · exact ((trunc ∞ S).analyticAt _).comp ((hGa _ (hmem z hz)).comp (Φ.analyticAt z))
  · exact ((trunc ∞ S).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hGb _ (hmem z hz)) (norm_nonneg _))
  · simp only [hΦι]

end QuantumNLS.RB01Head

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.RB01Head.trunc_apply
#print axioms QuantumNLS.RB01Head.head_ext
#print axioms QuantumNLS.RB01Head.ext_of_analyticAt
#print axioms QuantumNLS.RB01Head.r_ext
