import NlsGge.Hierarchy.ALQ4Ensemble38
import NlsGge.Hierarchy.ALFreeFields38
import Mathlib

/-! # L06b support: Gaussian infrastructure for the AL `Q₄` limit (paper/v2.tex l.2195-2218)

Variance convention: `complexGaussian a` has real-component variance `1/(2a)`, i.e. density
`(a/π) e^{-a|z|²}` and `E|z|² = 1/a`.  The "standard complex Gaussian" `g_k` is `complexGaussian 1`
(`E|g_k|² = 1`, `alFreeLaw38`), so `g_k a^{-1/2}` has law `complexGaussian a`
(`complexGaussian_scale38`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
namespace NlsGge.AblowitzLadik
open MeasureTheory ProbabilityTheory NlsGge.Measure NlsGge.HierarchyRiccati.Core

/-- Scaling: if `g ~ complexGaussian 1` then `a^{-1/2} g ~ complexGaussian a` (`a > 0`). -/
theorem complexGaussian_scale38 (a : ℝ) (ha : 0 < a) :
    (complexGaussian 1).map (fun z : ℂ => (((Real.sqrt a)⁻¹ : ℝ) : ℂ) * z) = complexGaussian a := by
  set c : ℝ := (Real.sqrt a)⁻¹ with hc
  have hc2 : c ^ 2 = a⁻¹ := by
    rw [hc, inv_pow, Real.sq_sqrt ha.le]
  have hvar : NNReal.mk (c ^ 2) (sq_nonneg c) * componentVariance 1 = componentVariance a := by
    apply NNReal.eq
    simp only [NNReal.coe_mul, NNReal.coe_mk]
    rw [componentVariance_coe 1 one_pos, componentVariance_coe a ha, hc2]
    field_simp
  have hmul : Measurable (fun x : ℝ => c * x) := measurable_const.mul measurable_id
  unfold complexGaussian
  have hcomp : (fun z : ℂ => ((c : ℝ) : ℂ) * z) ∘ Complex.measurableEquivRealProd.symm =
      Complex.measurableEquivRealProd.symm ∘ (Prod.map (fun x : ℝ => c * x) (fun x : ℝ => c * x)) := by
    funext p
    simp [Complex.measurableEquivRealProd]
    apply Complex.ext <;> simp
  rw [Measure.map_map (by fun_prop : Measurable (fun z : ℂ => ((c : ℝ) : ℂ) * z))
    Complex.measurableEquivRealProd.symm.measurable, hcomp,
    ← Measure.map_map Complex.measurableEquivRealProd.symm.measurable (hmul.prodMap hmul),
    ← Measure.map_prod_map _ _ hmul hmul, gaussianReal_map_const_mul, mul_zero, hvar]

/-- The scaled finite coordinates `û_k = a_{h,k}^{-1/2} g_k`, `|k| ≤ N` (`k` through `valMinAbs`). -/
def alQ4Hat38 (β₀ β₁ β₂ : ℝ) (N : ℕ) (g : ℤ → ℂ) : ZMod (2 * N + 1) → ℂ :=
  fun k => (((Real.sqrt (alSymbol38 β₀ β₁ β₂ N k.valMinAbs))⁻¹ : ℝ) : ℂ) * g k.valMinAbs

theorem valMinAbs_mem_Icc38 (N : ℕ) (k : ZMod (2 * N + 1)) :
    k.valMinAbs ∈ Finset.Icc (-(N : ℤ)) N := by
  have h1 := ZMod.natAbs_valMinAbs_le k
  have h2 : (2 * N + 1) / 2 = N := by omega
  rw [h2] at h1
  rw [Finset.mem_Icc]; omega

theorem valMinAbs_intCast38 (N : ℕ) (k : ℤ) (h1 : -(N : ℤ) ≤ k) (h2 : k ≤ N) :
    ((k : ℤ) : ZMod (2 * N + 1)).valMinAbs = k := by
  have hmem := valMinAbs_mem_Icc38 N ((k : ℤ) : ZMod (2 * N + 1))
  rw [Finset.mem_Icc] at hmem
  have hc := ZMod.coe_valMinAbs ((k : ℤ) : ZMod (2 * N + 1))
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hc
  obtain ⟨c, hc⟩ := hc
  have : ((2 * N + 1 : ℕ) : ℤ) = 2 * N + 1 := by push_cast; ring
  rw [this] at hc
  rcases lt_trichotomy c 0 with h | h | h
  · nlinarith
  · subst h; omega
  · nlinarith

theorem alQ4Hat_law38 (β₀ β₁ β₂ : ℝ) (N : ℕ)
    (hpos : ∀ k : ℤ, |k| ≤ (N : ℤ) → 0 < alSymbol38 β₀ β₁ β₂ N k) :
    (alFreeLaw38).map (alQ4Hat38 β₀ β₁ β₂ N) = alQ4Gauss38 β₀ β₁ β₂ N := by
  classical
  set U : Finset ℤ := Finset.Icc (-(N : ℤ)) N with hU
  let e : ZMod (2 * N + 1) ≃ U :=
    { toFun := fun k => ⟨k.valMinAbs, valMinAbs_mem_Icc38 N k⟩
      invFun := fun u => ((u : ℤ) : ZMod (2 * N + 1))
      left_inv := fun k => ZMod.coe_valMinAbs k
      right_inv := fun u => by
        apply Subtype.ext
        have hu : (u : ℤ) ∈ Finset.Icc (-(N : ℤ)) N := u.2
        rw [Finset.mem_Icc] at hu
        exact valMinAbs_intCast38 N u hu.1 hu.2 }
  have h1 := countableComplexGaussian_map_finiteRestriction (fun _ : ℤ => (1 : ℝ)) U
  have h2 := measurePreserving_arrowCongr' (fun u : U => complexGaussian ((fun _ : ℤ => (1 : ℝ)) u.1))
    (fun _ : ZMod (2 * N + 1) => complexGaussian 1) e.symm (MeasurableEquiv.refl ℂ)
    (fun u => by simp only [Equiv.apply_symm_apply]; exact MeasurePreserving.id _)
  set c : ZMod (2 * N + 1) → ℝ := fun k => (Real.sqrt (alSymbol38 β₀ β₁ β₂ N k.valMinAbs))⁻¹ with hc
  have hcomp : alQ4Hat38 β₀ β₁ β₂ N = (fun y : ZMod (2 * N + 1) → ℂ => fun k => ((c k : ℝ) : ℂ) * y k) ∘
      (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)) ∘ U.restrict := by
    funext g k; rfl
  have hmeas1 : Measurable (fun y : ZMod (2 * N + 1) → ℂ => fun k => ((c k : ℝ) : ℂ) * y k) := by
    fun_prop
  rw [hcomp, ← Measure.map_map hmeas1
    ((MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)).measurable.comp
      (Finset.measurable_restrict U)),
    ← Measure.map_map (MeasurableEquiv.arrowCongr' e.symm (MeasurableEquiv.refl ℂ)).measurable
      (Finset.measurable_restrict U)]
  unfold alFreeLaw38
  rw [h1, h2.map_eq, Measure.pi_map_pi (fun k => by fun_prop)]
  unfold alQ4Gauss38 alGauss38
  congr 1
  funext k
  have hk := hpos k.valMinAbs (by
    have := valMinAbs_mem_Icc38 N k
    rw [Finset.mem_Icc] at this; rw [abs_le]; exact this)
  rw [alRate38_poly38, ← complexGaussian_scale38 _ hk]

/-- The order-two coefficients `β = (β₀, β₁, β₂, β₂, …)`: only `β₀,β₁,β₂` enter `finiteHierarchyRate38 2`. -/
def alQ4Beta38 (β₀ β₁ β₂ : ℝ) : ℕ → ℝ := fun j => if j = 0 then β₀ else if j = 1 then β₁ else β₂

/-- Continuum symbol `a_k = W₂(2πk) = β₀ + β₁(2πk)² + β₂(2πk)⁴`. -/
def alQ4RateC38 (β₀ β₁ β₂ : ℝ) (k : ℤ) : ℝ :=
  β₀ + β₁ * (2 * Real.pi * (k : ℝ)) ^ 2 + β₂ * (2 * Real.pi * (k : ℝ)) ^ 4

theorem alQ4Rate_eq_hierarchy38 (β₀ β₁ β₂ : ℝ) (k : ℤ) :
    finiteHierarchyRate38 2 (alQ4Beta38 β₀ β₁ β₂) k = alQ4RateC38 β₀ β₁ β₂ k := by
  unfold finiteHierarchyRate38 finiteHierarchyW38 alQ4RateC38 alQ4Beta38
  simp [Finset.sum_range_succ]

/-- Continuum coefficients `U_k = a_k^{-1/2} g_k`. -/
def alQ4UCoef38 (β₀ β₁ β₂ : ℝ) (g : ℤ → ℂ) : ℤ → ℂ :=
  fun k => (((Real.sqrt (alQ4RateC38 β₀ β₁ β₂ k))⁻¹ : ℝ) : ℂ) * g k

/-- The coupling pushes the standard law to `γ₂ = gammaM38 2 β` (`B:eq:finitehierarchy`, `m = 2`). -/
theorem alQ4UCoef_law38 (β₀ β₁ β₂ : ℝ) (hpos : ∀ k : ℤ, 0 < alQ4RateC38 β₀ β₁ β₂ k) :
    (alFreeLaw38).map (alQ4UCoef38 β₀ β₁ β₂) = gammaM38 2 (alQ4Beta38 β₀ β₁ β₂) := by
  unfold alFreeLaw38 gammaM38 countableComplexGaussian
  have := Measure.infinitePi_map_pi (μ := fun _ : ℤ => complexGaussian (1 : ℝ))
    (f := fun k (z : ℂ) => (((Real.sqrt (alQ4RateC38 β₀ β₁ β₂ k))⁻¹ : ℝ) : ℂ) * z)
    (fun k => by fun_prop)
  unfold alQ4UCoef38
  rw [this]
  congr 1
  funext k
  rw [complexGaussian_scale38 _ (hpos k), alQ4Rate_eq_hierarchy38]

end NlsGge.AblowitzLadik

#check @NlsGge.AblowitzLadik.complexGaussian_scale38
#check @NlsGge.AblowitzLadik.alQ4Hat_law38
#check @NlsGge.AblowitzLadik.alQ4UCoef_law38
#print axioms NlsGge.AblowitzLadik.complexGaussian_scale38
#print axioms NlsGge.AblowitzLadik.alQ4Hat_law38
#print axioms NlsGge.AblowitzLadik.alQ4UCoef_law38
