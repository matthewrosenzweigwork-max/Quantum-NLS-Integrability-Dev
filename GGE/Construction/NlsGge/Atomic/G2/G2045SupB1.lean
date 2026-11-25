import Mathlib
import NlsGge.GK38.Defs

                                                                     
                                                                                
                                                                                                  
                                                                                                     
                                                                                            
                                                                                                
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- Complex-conjugation involution of the potential pair: `(p,q) ↦ (q̄, p̄)`; fixes `realSlice u`. -/
def potConj (φ : PotPair) : PotPair := (star φ.2, star φ.1)

theorem g2045b_star_smul (c : ℂ) (x : PhysicalL2) : star (c • x) = (starRingEnd ℂ c) • star x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (c • x), MeasureTheory.Lp.coeFn_smul c x,
    MeasureTheory.Lp.coeFn_smul (starRingEnd ℂ c) (star x), MeasureTheory.Lp.coeFn_star x]
    with z h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  simp [mul_comm]

theorem g2045b_star_star (x : PhysicalL2) : star (star x) = x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (star x), MeasureTheory.Lp.coeFn_star x] with z h1 h2
  simp only [h1, Pi.star_apply, h2, star_star]

theorem g2045b_star_add (x y : PhysicalL2) : star (x + y) = star x + star y :=
  map_add starLp x y

theorem g2045b_star_sub (x y : PhysicalL2) : star (x - y) = star x - star y :=
  map_sub starLp x y

theorem potConj_add (φ ψ : PotPair) : potConj (φ + ψ) = potConj φ + potConj ψ := by
  apply Prod.ext <;> simp [potConj, g2045b_star_add]

theorem potConj_smul (c : ℂ) (φ : PotPair) : potConj (c • φ) = (starRingEnd ℂ c) • potConj φ := by
  apply Prod.ext <;> simp [potConj, g2045b_star_smul]

theorem potConj_potConj (φ : PotPair) : potConj (potConj φ) = φ := by
  apply Prod.ext <;> simp [potConj, g2045b_star_star]

theorem potConj_realSlice (u : PhysicalL2) : potConj (realSlice u) = realSlice u := by
  apply Prod.ext <;> simp [potConj, g2045b_star_star]

/-- Decomposition `φ = realSlice a + I • realSlice b` with `potConj φ = realSlice a - I • realSlice b`. -/
theorem g2045b_decomp (k : PotPair) :
    ∃ a b : PhysicalL2, k = realSlice a + Complex.I • realSlice b ∧
      potConj k = realSlice a - Complex.I • realSlice b := by
  have hI1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  have hI2 : Complex.I * (Complex.I / 2) = -(1 / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
  have h2c : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
  have hc : starRingEnd ℂ (-Complex.I / 2) = Complex.I / 2 := by
    simp [map_div₀, h2c]
  have hc2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp [map_div₀, h2c]
  have hc3 : starRingEnd ℂ (Complex.I / 2) = -Complex.I / 2 := by
    simp [map_div₀, h2c]
  refine ⟨(1 / 2 : ℂ) • (k.1 + star k.2), (-Complex.I / 2) • (k.1 - star k.2), ?_, ?_⟩
  · apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, realSlice_fst, smul_smul, hI1]
      module
    · simp only [Prod.snd_add, Prod.smul_snd, realSlice_snd, g2045b_star_smul, g2045b_star_add,
        g2045b_star_sub, g2045b_star_star, smul_smul, hc, hc2, hI2]
      module
  · apply Prod.ext
    · simp only [potConj, Prod.fst_sub, Prod.smul_fst, realSlice_fst, smul_smul, hI1]
      module
    · simp only [potConj, Prod.snd_sub, Prod.smul_snd, realSlice_snd, g2045b_star_smul,
        g2045b_star_add, g2045b_star_sub, g2045b_star_star, smul_smul, hc, hc2, hI2]
      module

theorem g2045b_identity (V : Submodule ℂ PotPair) (S : Set PotPair)
    (hconv : Convex ℝ S) (hSV : S ⊆ (V : Set PotPair))
    (hcj : ∀ φ ∈ S, potConj φ ∈ S)
    (hopen : ∀ x ∈ V, ∀ A ∈ V, IsOpen {s : ℂ | x + s • A ∈ S})
    (f : PotPair → ℂ)
    (hf : ∀ x ∈ V, ∀ A ∈ V,
      AnalyticOnNhd ℂ (fun s : ℂ => f (x + s • A)) {s : ℂ | x + s • A ∈ S})
    (hr : ∀ u : PhysicalL2, realSlice u ∈ S → f (realSlice u) = 0) :
    ∀ φ ∈ S, f φ = 0 := by
  intro φ hφ
  obtain ⟨a, b, hk, hkc⟩ := g2045b_decomp φ
  have hx : realSlice a ∈ S := by
    have h := hconv hφ (hcj φ hφ) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    have e : (1/2 : ℝ) • φ + (1/2 : ℝ) • potConj φ = realSlice a := by
      rw [hkc, hk]
      module
    rwa [e] at h
  have hxV : realSlice a ∈ V := hSV hx
  have hφV : φ ∈ V := hSV hφ
  have hAV : realSlice b ∈ V := by
    have e : realSlice b = (-Complex.I) • (φ - realSlice a) := by
      rw [hk]
      have : (-Complex.I) • (realSlice a + Complex.I • realSlice b - realSlice a) =
          (-Complex.I * Complex.I) • realSlice b := by module
      rw [this]; simp
    rw [e]
    exact V.smul_mem _ (V.sub_mem hφV hxV)
  set D : Set ℂ := {s : ℂ | realSlice a + s • realSlice b ∈ S} with hD
  have hDopen : IsOpen D := hopen _ hxV _ hAV
  have hDconv : Convex ℝ D := by
    intro s hs s' hs' p q hp hq hpq
    have hm := hconv hs hs' hp hq hpq
    have e : realSlice a + (p • s + q • s') • realSlice b =
        p • (realSlice a + s • realSlice b) + q • (realSlice a + s' • realSlice b) := by
      have h1 : q = 1 - p := by linarith
      subst h1
      simp only [Complex.real_smul, smul_add, add_smul, mul_smul]
      module
    show realSlice a + (p • s + q • s') • realSlice b ∈ S
    rw [e]; exact hm
  have h0 : (0 : ℂ) ∈ D := by simpa [hD] using hx
  have hg : AnalyticOnNhd ℂ (fun s : ℂ => f (realSlice a + s • realSlice b)) D :=
    hf _ hxV _ hAV
  have hreal : ∀ r : ℝ, (r : ℂ) ∈ D → f (realSlice a + (r : ℂ) • realSlice b) = 0 := by
    intro r hrD
    have e : realSlice a + (r : ℂ) • realSlice b = realSlice (a + r • b) := by
      rw [Complex.coe_smul, map_add, map_smul]
      first | rfl | simp
    rw [e]
    refine hr _ ?_
    rw [← e]; exact hrD
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun s : ℂ => f (realSlice a + s • realSlice b)) z = 0 := by
    have h1 : ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), f (realSlice a + (x : ℂ) • realSlice b) = 0 := by
      have hn : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), (x : ℂ) ∈ D :=
        Complex.continuous_ofReal.continuousAt.eventually_mem (by simpa using hDopen.mem_nhds h0)
      exact Filter.Eventually.frequently
        ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hn).mono (fun x hx => hreal x hx))
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    exact Filter.Tendsto.frequently (p := fun z : ℂ => f (realSlice a + z • realSlice b) = 0) ht h1
  have hz := hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hDconv.isPreconnected h0 hfreq
  have hI : Complex.I ∈ D := by
    show realSlice a + Complex.I • realSlice b ∈ S
    rw [← hk]; exact hφ
  have := hz hI
  simp only [Pi.zero_apply] at this
  rwa [← hk] at this

end
end NlsGge.GKDefinitionDesign
