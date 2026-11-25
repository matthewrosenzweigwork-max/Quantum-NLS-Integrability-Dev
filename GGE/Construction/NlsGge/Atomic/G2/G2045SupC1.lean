import Mathlib
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.GK38.IsolatingDefs
import NlsGge.Atomic.G2.G2045SupB2
import NlsGge.Atomic.G2.G2045SupB4
-- WRAPPER-IMPORTS-BEGIN
import NlsGge.Atomic.G2.G2042
import NlsGge.Atomic.G2.G2043
import NlsGge.Atomic.G2.G2075
-- WRAPPER-IMPORTS-END

                                                                     
                                                                                
                                                                                                           
                                                                                         
                                                                                                    
                                                                                                          
                                                                                                          
                                                  
                                                                                                            
                                                                                                           
                                                                                                                                  
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign

/-- The statement of `G2_043 k hk` with `sourceW` replaced by an arbitrary set `W`. -/
def g2045c_H43 (k : ℕ) (W : Set PotPair) : Prop :=
  ∀ φ₀ : PotPair, φ₀ ∈ W → pairSobolev ((k - 1 : ℕ) : ℝ) φ₀ →
    Summable (fun n : ℤ => ‖higherAction k φ₀ n‖) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ S₀ : Finset ℤ,
      ∀ φ : PotPair, pairSobolev ((k - 1 : ℕ) : ℝ) φ →
        pairSobolevNorm ((k - 1 : ℕ) : ℝ) (φ - φ₀) < δ →
        φ ∈ W ∧ Summable (fun n : ℤ => ‖higherAction k φ n‖) ∧
        ∀ S : Finset ℤ, S₀ ⊆ S →
          ‖(∑' n : ℤ, higherAction k φ n) - ∑ n ∈ S, higherAction k φ n‖ < ε ∧
          |(∑' n : ℤ, ‖higherAction k φ n‖) - ∑ n ∈ S, ‖higherAction k φ n‖| < ε

theorem g2045c_line_analytic (x A : PotPair) :
    AnalyticOnNhd ℂ (fun s : ℂ => x + s • A) Set.univ := by
  intro s _
  have h1 : AnalyticAt ℂ (fun s : ℂ => s • A) s :=
    (((ContinuousLinearMap.id ℂ ℂ).smulRight A).analyticAt s)
  exact analyticAt_const.add h1

theorem g2045c_line_continuous (x A : PotPair) : Continuous (fun s : ℂ => x + s • A) := by
  fun_prop

theorem g2045c_line_open (W : Set PotPair) (hWo : IsOpen W) (x A : PotPair) :
    IsOpen {s : ℂ | x + s • A ∈ W} :=
  hWo.preimage (g2045c_line_continuous x A)

theorem g2045c_term_analytic (k : ℕ) (W : Set PotPair) (hWgk : W ⊆ gkW)
    (h042 : ∀ n : ℤ, AnalyticOnNhd ℂ (fun φ : PotPair => higherAction k φ n) gkW)
    (x A : PotPair) (n : ℤ) :
    AnalyticOnNhd ℂ (fun s : ℂ => higherAction k (x + s • A) n) {s : ℂ | x + s • A ∈ W} :=
  (h042 n).comp ((g2045c_line_analytic x A).mono (subset_univ _)) (fun s hs => hWgk hs)

/-- Line analyticity of `F φ = ∑' n, higherAction k φ n` on `{s | x + s•A ∈ W}`, for `x, A ∈ H^(k-1)`. -/
theorem g2045c_F_line_analytic_core (k : ℕ) (W : Set PotPair) (hWo : IsOpen W) (hWgk : W ⊆ gkW)
    (h042 : ∀ n : ℤ, AnalyticOnNhd ℂ (fun φ : PotPair => higherAction k φ n) gkW)
    (h043 : g2045c_H43 k W) (x A : PotPair)
    (hx : pairSobolev ((k - 1 : ℕ) : ℝ) x) (hA : pairSobolev ((k - 1 : ℕ) : ℝ) A) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℤ, higherAction k (x + s • A) n)
      {s : ℂ | x + s • A ∈ W} := by
  set N : ℕ := k - 1 with hN
  set T : Set ℂ := {s | x + s • A ∈ W} with hT
  have hTo : IsOpen T := g2045c_line_open W hWo x A
  have hmem : ∀ s : ℂ, pairSobolev (N : ℝ) (x + s • A) := fun s =>
    (pairSobolevSub N).add_mem hx ((pairSobolevSub N).smul_mem s hA)
  have hdiff : ∀ S : Finset ℤ,
      DifferentiableOn ℂ (fun s : ℂ => ∑ n ∈ S, higherAction k (x + s • A) n) T := by
    intro S
    exact DifferentiableOn.fun_sum
      (fun n _ => (g2045c_term_analytic k W hWgk h042 x A n).differentiableOn)
  have hlim : TendstoLocallyUniformlyOn
      (fun (S : Finset ℤ) (s : ℂ) => ∑ n ∈ S, higherAction k (x + s • A) n)
      (fun s : ℂ => ∑' n : ℤ, higherAction k (x + s • A) n) atTop T := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε s₁ hs₁
    obtain ⟨-, hε'⟩ := h043 (x + s₁ • A) hs₁ (hmem s₁)
    obtain ⟨δ, hδ, S₀, hS₀⟩ := hε' ε hε
    set a : ℝ := pairSobolevNorm (N : ℝ) A with ha
    have ha0 : 0 ≤ a := g2045b_pn_nonneg _ _
    refine ⟨Metric.ball s₁ (δ / (a + 1)),
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ (by positivity)), ?_⟩
    filter_upwards [eventually_ge_atTop S₀] with S hS s hs
    have hs' : ‖s - s₁‖ < δ / (a + 1) := by simpa [dist_eq_norm] using hs
    have hnorm : pairSobolevNorm (N : ℝ) (x + s • A - (x + s₁ • A)) < δ := by
      have e : x + s • A - (x + s₁ • A) = (s - s₁) • A := by module
      rw [e, g2045b_pn_smul]
      have h1 : ‖s - s₁‖ * (a + 1) < δ :=
        (lt_div_iff₀ (by positivity : (0 : ℝ) < a + 1)).1 hs'
      nlinarith [norm_nonneg (s - s₁)]
    rw [dist_eq_norm]
    exact ((hS₀ (x + s • A) (hmem s) hnorm).2.2 S hS).1
  exact (hlim.differentiableOn (Eventually.of_forall hdiff) hTo).analyticOnNhd hTo

-- WRAPPER-BEGIN
theorem g2045c_F_line_analytic (k : ℕ) (hk : 2 ≤ k) (x A : PotPair)
    (hx : pairSobolev ((k - 1 : ℕ) : ℝ) x) (hA : pairSobolev ((k - 1 : ℕ) : ℝ) A) :
    AnalyticOnNhd ℂ (fun s : ℂ => ∑' n : ℤ, higherAction k (x + s • A) n)
      {s : ℂ | x + s • A ∈ sourceW} :=
  g2045c_F_line_analytic_core k sourceW G2_075.1 G2_075.2.2.1 (G2_042 k hk).1 (G2_043 k hk) x A hx hA
-- WRAPPER-END

end NlsGge.GKDefinitionDesign
end
