import NlsGge.Hierarchy.RiccatiQ6Scaling38
import NlsGge.Hierarchy.RiccatiQ6CuspNegative38
import NlsGge.Hierarchy.RiccatiRealTrigApproxC2_38
import Mathlib.Tactic

/-! Batch 38, A01 (`C:prop:negative`, paper/v2.tex lines 2427-2469): the
continuum `Q6` remainder `V₃` is unbounded below on the union of the real
trigonometric polynomial spaces, for arbitrary positive `β₀,…,β₃`.

`V₃ = remainderV38 3 β` is the literal expression
`Σ_{j≤3} β_j Q_{2j} - Σ_n (Σ_{j≤3} β_j (2πn)^{2j}) |û(n)|²` with `Q_{2j}` the
recursion-defined local charge (real part; it is real by
`formalChargeIntegrand_im_eq_zero38`). Identification with the spectral
charge (E06.06) is neither used nor claimed.

Route: source route with two recorded tactic-level variations (periodic cusp
`(sin²πx+ε²)^{3/8}`; uniform `C²` approximation in place of `H²` continuity). -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.HierarchyRiccati.Core

open scoped ContDiff

/-- Integer frequency scaling keeps real trigonometric polynomials. -/
theorem IsRealTrigPoly38.comp_nat_mul {P : ℝ → ℝ} (h : IsRealTrigPoly38 P) (k : ℕ) :
    IsRealTrigPoly38 (fun y => P (k * y)) := by
  classical
  obtain ⟨N, a, b, hP⟩ := h
  refine ⟨N * k,
    fun m => ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j * k = m), a j,
    fun m => ∑ j ∈ (Finset.range (N + 1)).filter (fun j => j * k = m), b j, fun y => ?_⟩
  show P (k * y) = _
  rw [hP]
  have hmaps : ∀ j ∈ Finset.range (N + 1), j * k ∈ Finset.range (N * k + 1) := by
    intro j hj
    have := Finset.mem_range.mp hj
    exact Finset.mem_range.mpr (by nlinarith)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j * k = m := (Finset.mem_filter.mp hj).2
  have harg : 2 * Real.pi * (j : ℝ) * ((k : ℝ) * y) = 2 * Real.pi * (m : ℝ) * y := by
    rw [← hjm]; push_cast; ring
  rw [harg]

private theorem iterDerivCont38' (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) (k : ℕ) :
    Continuous (iteratedDeriv k g) :=
  hg.continuous_iteratedDeriv k (by exact_mod_cast le_top)

/-- A01 (`C:prop:negative`): for arbitrary positive `β₀,…,β₃` and every real
`C`, some real trigonometric polynomial `P` has `V₃(P) < C`. -/
theorem realQ6Remainder_unbounded_below38 (β : ℕ → ℝ) (hβ : ∀ j ≤ 3, 0 < β j)
    (C : ℝ) :
    ∃ (P : ℝ → ℝ) (hP : IsRealTrigPoly38 P),
      remainderV38 3 β (fun y => ((P y : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp hP.contDiff)
        (fun y => by simp only [hP.periodic y]) < C := by
  -- A01.02–.04: a smooth periodic cusp with `F < 0`.
  obtain ⟨ε, hε, hneg⟩ := exists_periodicCusp38_q6QuarticF_neg
  set f := periodicCusp38 ε with hfdef
  have hf : ContDiff ℝ ∞ f := periodicCusp38_contDiff ε hε
  have hfper : Function.Periodic f 1 := periodicCusp38_periodic ε
  have hFf : (∫ x in (0:ℝ)..1, quarticDensity38 (f x) (deriv f x) (iteratedDeriv 2 f x)) < 0 := by
    simpa [q6QuarticF38, quarticDensity38] using hneg
  -- uniform bound on `f, f', f''` over `[0,1]`.
  have c0 : Continuous f := hf.continuous
  have c1 : Continuous (deriv f) := hf.continuous_deriv (by exact_mod_cast le_top)
  have c2 : Continuous (iteratedDeriv 2 f) := iterDerivCont38' f hf 2
  obtain ⟨R0, hR0⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((c0.abs.add (c1.abs.add c2.abs)).continuousOn)
  set R := max R0 0 with hR
  have hRnn : 0 ≤ R := le_max_right _ _
  have hfR : ∀ x ∈ Set.Icc (0:ℝ) 1,
      |f x| ≤ R ∧ |deriv f x| ≤ R ∧ |iteratedDeriv 2 f x| ≤ R := by
    intro x hx
    have h := hR0 x hx
    simp only [Pi.add_apply] at h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h
    have := le_max_left R0 0
    have := abs_nonneg (f x)
    have := abs_nonneg (deriv f x)
    have := abs_nonneg (iteratedDeriv 2 f x)
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  -- A01.05: trigonometric approximation keeping `F < 0`.
  set Ff := ∫ x in (0:ℝ)..1, quarticDensity38 (f x) (deriv f x) (iteratedDeriv 2 f x)
  set K : ℝ := 100 * (R + 1) ^ 3 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min 1 (-Ff / (2 * K)) with hδ
  have hδpos : 0 < δ := lt_min one_pos (div_pos (by linarith) (by positivity))
  obtain ⟨P, hPtrig, hclose⟩ := exists_realTrigPoly_C2_close38 f hf hfper δ hδpos
  have hPs : ContDiff ℝ ∞ P := hPtrig.contDiff
  have hPper : Function.Periodic P 1 := hPtrig.periodic
  have hdiff := quarticFunctional38_close f P hf hPs R δ hRnn hδpos.le (min_le_left _ _) hfR
    hclose
  have hFP : (∫ x in (0:ℝ)..1, quarticDensity38 (P x) (deriv P x) (iteratedDeriv 2 P x)) < 0 := by
    have hKδ : K * δ ≤ -Ff / 2 := by
      have : δ ≤ -Ff / (2 * K) := min_le_right _ _
      calc K * δ ≤ K * (-Ff / (2 * K)) := mul_le_mul_of_nonneg_left this hKpos.le
        _ = -Ff / 2 := by field_simp
    have := (abs_le.mp hdiff).2
    linarith
  -- A01.06–.07: frequency scaling.
  obtain ⟨k, hk, hlt⟩ := remainderV3_scaled_lt38 β (hβ 3 le_rfl) P hPs hPper hFP C
  exact ⟨fun y => P (k * y), hPtrig.comp_nat_mul k, hlt⟩

end NlsGge.HierarchyRiccati.Core

end
