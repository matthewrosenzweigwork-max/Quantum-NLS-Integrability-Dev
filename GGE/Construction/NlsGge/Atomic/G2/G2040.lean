import Mathlib
import NlsGge.Atomic.G2.G2036
import NlsGge.Atomic.G6.G6004
import NlsGge.GK38.ActionRealBridge
import NlsGge.GK38.IsolatingFamily
import NlsGge.GK38.PairPotential
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic

                                                                                                                                         
                                                                                                                                                                        
                                                                                                                                           
                                                                                                                                                                 
                                                                                                                                                                     
                                                                                                                                                                        
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem g2040_star_smul (c : ℂ) (x : PhysicalL2) : star (c • x) = (starRingEnd ℂ c) • star x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (c • x), MeasureTheory.Lp.coeFn_smul c x,
    MeasureTheory.Lp.coeFn_smul (starRingEnd ℂ c) (star x), MeasureTheory.Lp.coeFn_star x]
    with z h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.star_apply, Pi.smul_apply, smul_eq_mul]
  simp [mul_comm]

theorem g2040_star_add (x y : PhysicalL2) : star (x + y) = star x + star y :=
  map_add starLp x y

theorem g2040_star_sub (x y : PhysicalL2) : star (x - y) = star x - star y :=
  map_sub starLp x y

theorem g2040_star_star (x : PhysicalL2) : star (star x) = x := by
  apply MeasureTheory.Lp.ext
  filter_upwards [MeasureTheory.Lp.coeFn_star (star x), MeasureTheory.Lp.coeFn_star x] with z h1 h2
  simp only [h1, Pi.star_apply, h2, star_star]

def g2040B : PhysicalL2 →L[ℂ] PhysicalL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun x y : PhysicalL2 => inner ℂ (star x) y)
      (fun x₁ x₂ y => by rw [g2040_star_add, inner_add_left])
      (fun c x y => by rw [g2040_star_smul, inner_smul_left]; simp)
      (fun x y₁ y₂ => by rw [inner_add_right])
      (fun c x y => by rw [inner_smul_right]; simp))
    1 (fun x y => by
      show ‖inner ℂ (star x) y‖ ≤ 1 * ‖x‖ * ‖y‖
      have h := norm_inner_le_norm (𝕜 := ℂ) (star x) y
      rw [show ‖star x‖ = ‖x‖ from starLp.norm_map x] at h
      linarith)

theorem g2040B_eq (x y : PhysicalL2) :
    g2040B x y = ∫ z : PhysicalCircle, x z * y z ∂spatialMeasure := by
  show inner ℂ (star x) y = _
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MeasureTheory.Lp.coeFn_star x] with z hz
  rw [hz]
  simp [RCLike.inner_apply, mul_comm]

theorem g2040_Q_analytic :
    AnalyticOnNhd ℂ (fun φ : PotPair => ∫ z : PhysicalCircle, φ.1 z * φ.2 z ∂spatialMeasure)
      univ := by
  intro φ _
  have h : AnalyticAt ℂ (fun p : PotPair => g2040B p.1 p.2) φ := g2040B.analyticAt_bilinear φ
  have e : (fun p : PotPair => ∫ z : PhysicalCircle, p.1 z * p.2 z ∂spatialMeasure) =
      fun p : PotPair => g2040B p.1 p.2 := funext fun p => (g2040B_eq p.1 p.2).symm
  rw [e]
  exact h

theorem g2040_real_mass (u : PhysicalL2) :
    Integrable (fun x : PhysicalCircle => (realSlice u).1 x * (realSlice u).2 x)
      spatialMeasure ∧
    HasSum (fun n : ℤ => gkActionC38 (realSlice u) n)
      (∫ x : PhysicalCircle, (realSlice u).1 x * (realSlice u).2 x ∂spatialMeasure) ∧
    (∫ x : PhysicalCircle, (realSlice u).1 x * (realSlice u).2 x ∂spatialMeasure) =
      (‖u‖^2 : ℂ) := by
  have hint : Integrable (fun x : PhysicalCircle => (realSlice u).1 x * (realSlice u).2 x)
      spatialMeasure :=
    MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp (realSlice u).1) (Lp.memLp (realSlice u).2)
  have hval : (∫ x : PhysicalCircle, (realSlice u).1 x * (realSlice u).2 x ∂spatialMeasure) =
      ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    have hin : inner ℂ u u = ∫ x : PhysicalCircle, inner ℂ (u x) (u x) ∂spatialMeasure :=
      MeasureTheory.L2.inner_def u u
    rw [inner_self_eq_norm_sq_to_K] at hin
    push_cast
    rw [show ((‖u‖ : ℝ) : ℂ) ^ 2 = RCLike.ofReal (K := ℂ) ‖u‖ ^ 2 from rfl, hin]
    refine integral_congr_ae ?_
    filter_upwards [realSlice_snd_ae u] with x hx
    rw [realSlice_fst, hx]
    simp [RCLike.inner_apply, mul_comm]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  refine ⟨hint, ?_, by rw [hval]; push_cast; ring⟩
  rw [hval]
  have h := Complex.hasSum_ofReal.2 (NlsGge.GKDefinitionDesign.g6_action_hasSum u)
  have e : (fun n : ℤ => gkActionC38 (realSlice u) n) =
      fun n : ℤ => ((actualGapActionAllE02_38 u n : ℝ) : ℂ) :=
    funext (NlsGge.GK38.ActionRealBridge.action_real_bridge u)
  rw [e]
  exact h

theorem g2040_decomp (k : PotPair) :
    ∃ a b : PhysicalL2, ‖a‖ ≤ ‖k‖ ∧ ‖b‖ ≤ ‖k‖ ∧ k = realSlice a + Complex.I • realSlice b := by
  have h1 : ‖k.1‖ ≤ ‖k‖ := norm_fst_le k
  have h2 : ‖k.2‖ ≤ ‖k‖ := norm_snd_le k
  have hs : ‖star k.2‖ = ‖k.2‖ := starLp.norm_map k.2
  have hI1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    linear_combination (-1 / 2 : ℂ) * Complex.I_mul_I
  have hI2 : Complex.I * (Complex.I / 2) = -(1 / 2) := by
    linear_combination (1 / 2 : ℂ) * Complex.I_mul_I
  have h2c : starRingEnd ℂ (2 : ℂ) = 2 := map_ofNat _ 2
  have hc : starRingEnd ℂ (-Complex.I / 2) = Complex.I / 2 := by
    simp [map_div₀, h2c]
  have hc2 : starRingEnd ℂ (1 / 2 : ℂ) = 1 / 2 := by simp [map_div₀, h2c]
  refine ⟨(1 / 2 : ℂ) • (k.1 + star k.2), (-Complex.I / 2) • (k.1 - star k.2), ?_, ?_, ?_⟩
  · rw [norm_smul]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    have := norm_add_le k.1 (star k.2)
    linarith
  · rw [norm_smul]
    have : ‖(-Complex.I / 2 : ℂ)‖ = 1 / 2 := by simp
    rw [this]
    have := norm_sub_le k.1 (star k.2)
    linarith
  · apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, realSlice_fst, smul_smul, hI1]
      module
    · simp only [Prod.snd_add, Prod.smul_snd, realSlice_snd, g2040_star_smul, g2040_star_add,
        g2040_star_sub, g2040_star_star, smul_smul, hc, hc2, hI2]
      module

theorem g2040_one_var (φ : ℂ → ℂ) (hφ : AnalyticOnNhd ℂ φ (ball (0 : ℂ) 2))
    (hr : ∀ x : ℝ, |x| < 2 → φ (x : ℂ) = 0) : ∀ z ∈ ball (0 : ℂ) 2, φ z = 0 := by
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), φ z = 0 := by
    have h1 : ∃ᶠ x : ℝ in 𝓝[≠] (0 : ℝ), φ (x : ℂ) = 0 := by
      have hopen : IsOpen {x : ℝ | |x| < 2} := isOpen_lt continuous_abs continuous_const
      have hn : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), |x| < 2 := hopen.mem_nhds (by simp)
      exact Filter.Eventually.frequently
        ((Filter.Eventually.filter_mono nhdsWithin_le_nhds hn).mono (fun x hx => hr x hx))
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using hx
    exact Filter.Tendsto.frequently (p := fun z : ℂ => φ z = 0) ht h1
  intro z hz
  exact hφ.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball _ _).isPreconnected
    (mem_ball_self (by norm_num)) hfreq hz

theorem g2040_line {f : PotPair → ℂ} {c : PotPair} {ρ : ℝ}
    (hf : AnalyticOnNhd ℂ f (ball c ρ)) (x0 A : PotPair)
    (hm : ∀ s ∈ ball (0 : ℂ) 2, x0 + s • A ∈ ball c ρ) :
    AnalyticOnNhd ℂ (fun s : ℂ => f (x0 + s • A)) (ball (0 : ℂ) 2) := by
  have hl : AnalyticOnNhd ℂ (fun s : ℂ => x0 + s • A) (ball (0 : ℂ) 2) := by
    intro s _
    exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact hf.comp hl hm

theorem g2040_zero_near (f : PotPair → ℂ) (u : PhysicalL2) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (ball (realSlice u) ρ))
    (hr : ∀ v : PhysicalL2, realSlice v ∈ ball (realSlice u) ρ → f (realSlice v) = 0) :
    ∀ h ∈ ball (realSlice u) (ρ / 4), f h = 0 := by
  intro h hh
  have hkn : ‖h - realSlice u‖ < ρ / 4 := by
    rwa [mem_ball_iff_norm] at hh
  obtain ⟨a, b, ha, hb, hk⟩ := g2040_decomp (h - realSlice u)
  have hA : ‖realSlice a‖ < ρ / 4 := by rw [norm_realSlice]; linarith
  have hB : ‖realSlice b‖ < ρ / 4 := by rw [norm_realSlice]; linarith
  have hmem : ∀ s t : ℂ, ‖s‖ < 2 → ‖t‖ < 2 →
      realSlice u + s • realSlice a + t • realSlice b ∈ ball (realSlice u) ρ := by
    intro s t hs ht
    rw [mem_ball_iff_norm]
    have e : realSlice u + s • realSlice a + t • realSlice b - realSlice u =
        s • realSlice a + t • realSlice b := by abel
    rw [e]
    have h1 : ‖s‖ * ‖realSlice a‖ ≤ 2 * ‖realSlice a‖ :=
      mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
    have h2 : ‖t‖ * ‖realSlice b‖ ≤ 2 * ‖realSlice b‖ :=
      mul_le_mul_of_nonneg_right ht.le (norm_nonneg _)
    calc ‖s • realSlice a + t • realSlice b‖ ≤ ‖s • realSlice a‖ + ‖t • realSlice b‖ :=
          norm_add_le _ _
      _ = ‖s‖ * ‖realSlice a‖ + ‖t‖ * ‖realSlice b‖ := by rw [norm_smul, norm_smul]
      _ < ρ := by linarith
  have hmem' : ∀ s t : ℂ, s ∈ ball (0 : ℂ) 2 → t ∈ ball (0 : ℂ) 2 →
      realSlice u + s • realSlice a + t • realSlice b ∈ ball (realSlice u) ρ := by
    intro s t hs ht
    rw [mem_ball_zero_iff] at hs ht
    exact hmem s t hs ht
  -- the function of two complex variables
  let G : ℂ → ℂ → ℂ := fun s t => f (realSlice u + s • realSlice a + t • realSlice b)
  have hGreal : ∀ r t0 : ℝ, |r| < 2 → |t0| < 2 → G (r : ℂ) (t0 : ℂ) = 0 := by
    intro r t0 hr1 ht1
    have e : realSlice u + (r : ℂ) • realSlice a + (t0 : ℂ) • realSlice b =
        realSlice (u + r • a + t0 • b) := by
      rw [Complex.coe_smul, Complex.coe_smul, map_add, map_add, map_smul, map_smul]
      rfl
    have hm : realSlice (u + r • a + t0 • b) ∈ ball (realSlice u) ρ := by
      rw [← e]
      exact hmem _ _ (by simpa using hr1) (by simpa using ht1)
    show f (realSlice u + (r : ℂ) • realSlice a + (t0 : ℂ) • realSlice b) = 0
    rw [e]
    exact hr _ hm
  have hstep1 : ∀ t0 : ℝ, |t0| < 2 → ∀ s ∈ ball (0 : ℂ) 2, G s (t0 : ℂ) = 0 := by
    intro t0 ht0
    have hl := g2040_line hf (realSlice u + (t0 : ℂ) • realSlice b) (realSlice a)
      (fun s hs => by
        have := hmem' s (t0 : ℂ) hs (by rw [mem_ball_zero_iff]; simpa using ht0)
        rwa [add_right_comm] at this)
    have e : (fun s : ℂ => G s (t0 : ℂ)) =
        fun s : ℂ => f ((realSlice u + (t0 : ℂ) • realSlice b) + s • realSlice a) := by
      funext s; simp only [G]; rw [add_right_comm]
    exact g2040_one_var (fun s : ℂ => G s (t0 : ℂ)) (by rw [e]; exact hl)
      (fun r hr1 => hGreal r t0 hr1 ht0)
  have hstep2 : ∀ s ∈ ball (0 : ℂ) 2, ∀ t ∈ ball (0 : ℂ) 2, G s t = 0 := by
    intro s hs
    have hl := g2040_line hf (realSlice u + s • realSlice a) (realSlice b)
      (fun t ht => hmem' s t hs ht)
    exact g2040_one_var (fun t => G s t) hl (fun t0 ht0 => hstep1 t0 ht0 s hs)
  have hone : (1 : ℂ) ∈ ball (0 : ℂ) 2 := by rw [mem_ball_zero_iff]; simp
  have hI : Complex.I ∈ ball (0 : ℂ) 2 := by rw [mem_ball_zero_iff]; simp
  have e : h = realSlice u + (1 : ℂ) • realSlice a + Complex.I • realSlice b := by
    rw [one_smul, add_assoc, ← hk]; abel
  rw [e]
  exact hstep2 1 hone Complex.I hI

theorem g2040_complex_eq (φ : PotPair) (hφ : φ ∈ gkW) :
    ∑' n : ℤ, gkActionC38 φ n = ∫ x : PhysicalCircle, φ.1 x * φ.2 x ∂spatialMeasure := by
  obtain ⟨u, ρ, hc, hmem⟩ := hφ
  have hρ : 0 < ρ := hc.1
  have hball : ball (realSlice u) ρ ⊆ gkW := fun ψ hψ => ⟨u, ρ, hc, hψ⟩
  let f : PotPair → ℂ := fun ψ => (∑' n : ℤ, gkActionC38 ψ n) -
    ∫ x : PhysicalCircle, ψ.1 x * ψ.2 x ∂spatialMeasure
  have hfan : AnalyticOnNhd ℂ f (ball (realSlice u) ρ) :=
    (G2_036.2.2.2.sub (g2040_Q_analytic.mono (subset_univ _)) |>.mono hball :
      AnalyticOnNhd ℂ f (ball (realSlice u) ρ))
  have hr : ∀ v : PhysicalL2, realSlice v ∈ ball (realSlice u) ρ → f (realSlice v) = 0 := by
    intro v _
    exact sub_eq_zero.2 (g2040_real_mass v).2.1.tsum_eq
  have hz := g2040_zero_near f u ρ hρ hfan hr
  have hev : f =ᶠ[𝓝 (realSlice u)] (fun _ => (0 : ℂ)) :=
    Filter.eventually_of_mem (ball_mem_nhds _ (by positivity)) hz
  have h0 := hfan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball _ _).isPreconnected (mem_ball_self hρ) hev hmem
  exact sub_eq_zero.1 h0

theorem G2_040 :
    (∀ φ ∈ sourceW,
      Integrable (fun x : PhysicalCircle => φ.1 x * φ.2 x) spatialMeasure ∧
      HasSum (fun n : ℤ => gkActionC38 φ n)
        (∫ x : PhysicalCircle, φ.1 x * φ.2 x ∂spatialMeasure)) ∧
    (∀ u : PhysicalL2,
      HasSum (actualGapActionAllE02_38 u) (‖u‖^2) ∧
      potNormSq38 (realSlice u) = 2*‖u‖^2 ∧
      (∑' n : ℤ, gkActionC38 (realSlice u) n) =
        ((potNormSq38 (realSlice u)/2 : ℝ) : ℂ)) := by
  refine ⟨fun φ hφ => ?_, fun u => ?_⟩
  · have hgk : φ ∈ gkW := sourceFamily.W_gk hφ
    refine ⟨MemLp.integrable_mul (p := 2) (q := 2) (Lp.memLp φ.1) (Lp.memLp φ.2), ?_⟩
    rw [← g2040_complex_eq φ hgk]
    exact (G2_036.1 φ hgk).of_norm.hasSum
  · refine ⟨g6_action_hasSum u, potNormSq38_realSlice u, ?_⟩
    rw [(g2040_real_mass u).2.1.tsum_eq, (g2040_real_mass u).2.2, potNormSq38_realSlice]
    push_cast
    ring

end
end NlsGge.GKDefinitionDesign
