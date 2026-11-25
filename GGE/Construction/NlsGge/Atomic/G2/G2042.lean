import Mathlib
import NlsGge.ThirdConsultation.G2.G2042Host
import NlsGge.ThirdConsultation.G2.G2042Support1
import NlsGge.ThirdConsultation.G2.G2042MomentB

                                                                                                                                               
                                                                                                                         
                                                                                                                      
                                                                                                          
                                                                                     
                                                                                                          
                                                                                             
                                                                                                    
                                                                                                     
                                                                                                           
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open scoped BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2042Pkt

/-- Binomial splitting of `z^k` about `λ̇` on the moment integrand. -/
theorem binom_split (k : ℕ) (φ : PotPair) (n : ℤ) (z : ℂ) :
    z ^ k * deriv (discrim φ) z / canonRoot38 φ z =
      ∑ m ∈ Finset.range (k + 1),
        ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) *
          ((z - lamDot φ n) ^ m * deriv (discrim φ) z / canonRoot38 φ z) := by
  have h := add_pow (z - lamDot φ n) (lamDot φ n) k
  rw [sub_add_cancel] at h
  rw [h, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Finite sums commute with circle integrals (each term circle integrable). -/
theorem circle_sum_eq {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (h : ∀ i ∈ s, CircleIntegrable (F i) c R) :
    circleIntegral (fun z => ∑ i ∈ s, F i z) c R = ∑ i ∈ s, circleIntegral (F i) c R := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [circleIntegral]
  · intro a s ha ih h
    have hA : CircleIntegrable (F a) c R := h a (Finset.mem_insert_self a s)
    have hS : ∀ i ∈ s, CircleIntegrable (F i) c R := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hSum : CircleIntegrable (fun z => ∑ i ∈ s, F i z) c R := by
      have h0 : CircleIntegrable (∑ i ∈ s, F i) c R := CircleIntegrable.sum s hS
      rwa [Finset.sum_fn] at h0
    have hfun : (fun z => ∑ i ∈ insert a s, F i z) = fun z => F a z + ∑ i ∈ s, F i z := by
      funext z
      rw [Finset.sum_insert ha]
    rw [hfun, circleIntegral.integral_add hA hSum, ih hS, Finset.sum_insert ha]

end G2042Pkt

theorem G2_042 (k : ℕ) (hk : 2 ≤ k) :
    (∀ n : ℤ,
      AnalyticOnNhd ℂ
        (fun φ : PotPair => higherAction k φ n) gkW) ∧
    (∀ φ ∈ gkW, ∀ n : ℤ,
      CircleIntegrable
        (fun z : ℂ =>
          z^k * deriv (discrim φ) z / canonRoot38 φ z)
        (discC φ n) (discR φ n)) ∧
    ∀ φ₀ ∈ gkW, ∃ U : Set PotPair,
      IsOpen U ∧ φ₀ ∈ U ∧ U ⊆ gkW ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ φ ∈ U, ∀ n : ℤ,
          ‖higherAction k φ n‖ ≤
            C * (japaneseBracket n)^(k-1) * ‖gamma2 φ n‖
  := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) analyticity in φ on a fixed isolating family, then contour independence
    intro n φ hφ
    obtain ⟨V, hV, hVW, hVo, -, C, R, hf⟩ := local_isolatingFamily φ hφ
    have hφV : φ ∈ V := mem_of_mem_nhds hV
    have hF : AnalyticOnNhd ℂ (Function.uncurry
        (fun (ψ : PotPair) (z : ℂ) => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z))
        (V ×ˢ Metric.sphere (C n) (R n)) := by
      rintro ⟨ψ, z⟩ ⟨hψ, hz⟩
      have hzg : z ∉ gapSegments38 ψ := fixed_sphere_subset ψ C R (hf ψ hψ) n hz
      have hp : (ψ, z) ∈ rootDomain38 := ⟨hVW hψ, hzg⟩
      have h1 : AnalyticAt ℂ (fun p : PotPair × ℂ => deriv (discrim p.1) p.2) (ψ, z) :=
        analyticOnNhd_discrimDeriv_joint38 (ψ, z) (Set.mem_univ _)
      have h2 : AnalyticAt ℂ (fun p : PotPair × ℂ => canonRoot38 p.1 p.2) (ψ, z) :=
        canonRoot_analytic38 (ψ, z) hp
      exact (((analyticAt_snd.pow k).mul h1).div h2 (canonRoot_ne_zero38 ψ hp.1 z hp.2))
    have hA := Lib.parametricCircleAnalytic38 PotPair V (C n) (R n)
      (fun (ψ : PotPair) (z : ℂ) => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z)
      hVo (isolating_radius_pos38 (hf φ hφV) n) hF
    have hHom : ∀ ψ ∈ V,
        circleIntegral (fun z : ℂ => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z)
          (discC ψ n) (discR ψ n) =
        circleIntegral (fun z : ℂ => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z) (C n) (R n) := by
      intro ψ hψ
      have hψg : ψ ∈ gkW := hVW hψ
      have hsph : ∀ t ∈ Set.Icc (0:ℝ) 1,
          Metric.sphere (((1 - t) : ℝ) • discC ψ n + t • C n) ((1 - t) * discR ψ n + t * R n)
            ⊆ actionCutDomain38 ψ :=
        fun t ht => action_contour_sphere_subset38 ψ (discC ψ) C (discR ψ) R
          (isolating_family38 ψ hψg) (hf ψ hψ) n t ht
      have hfa : AnalyticOnNhd ℂ (fun z : ℂ => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z)
          (actionCutDomain38 ψ) := by
        intro z hz
        have hp : (ψ, z) ∈ rootDomain38 := ⟨hψg, hz⟩
        have h1 : AnalyticAt ℂ (fun w : ℂ => deriv (discrim ψ) w) z :=
          AnalyticAt.comp (g := fun p : PotPair × ℂ => deriv (discrim p.1) p.2)
            (f := fun w : ℂ => (ψ, w))
            (analyticOnNhd_discrimDeriv_joint38 (ψ, z) (Set.mem_univ _))
            (analyticAt_const.prod analyticAt_id)
        have h2 : AnalyticAt ℂ (fun w : ℂ => canonRoot38 ψ w) z :=
          AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
            (f := fun w : ℂ => (ψ, w))
            (canonRoot_analytic38 (ψ, z) hp)
            (analyticAt_const.prod analyticAt_id)
        exact (((analyticAt_id.pow k).mul h1).div h2 (canonRoot_ne_zero38 ψ hψg z hz))
      exact (NlsGge.Analysis.circleIntegral_eq_of_affine_circle_homotopy
        (isOpen_actionCutDomain38 ψ hψg) hfa (isolating_radius_pos38 (isolating_family38 ψ hψg) n)
        (isolating_radius_pos38 (hf ψ hψ) n) hsph).2.2
    have hcong : (fun ψ : PotPair => (1 / (Real.pi : ℂ)) *
        circleIntegral (fun z : ℂ => z ^ k * deriv (discrim ψ) z / canonRoot38 ψ z) (C n) (R n))
        =ᶠ[𝓝 φ] (fun ψ : PotPair => higherAction k ψ n) := by
      filter_upwards [hV] with ψ hψ
      simp only [higherAction]
      rw [hHom ψ hψ]
    exact (analyticAt_const.mul (hA.2 φ hφV)).congr hcong
  · -- (b) circle integrability on the sphere (inside the cut domain)
    intro φ hφ n
    have hf := isolating_family38 φ hφ
    apply ContinuousOn.circleIntegrable (isolating_radius_pos38 hf n).le
    intro z hz
    have hzg : z ∉ gapSegments38 φ := fixed_sphere_subset φ (discC φ) (discR φ) hf n hz
    have hp : (φ, z) ∈ rootDomain38 := ⟨hφ, hzg⟩
    have h1 : AnalyticAt ℂ (fun w : ℂ => deriv (discrim φ) w) z :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => deriv (discrim p.1) p.2)
        (f := fun w : ℂ => (φ, w))
        (analyticOnNhd_discrimDeriv_joint38 (φ, z) (Set.mem_univ _))
        (analyticAt_const.prod analyticAt_id)
    have h2 : AnalyticAt ℂ (fun w : ℂ => canonRoot38 φ w) z :=
      AnalyticAt.comp (g := fun p : PotPair × ℂ => canonRoot38 p.1 p.2)
        (f := fun w : ℂ => (φ, w))
        (canonRoot_analytic38 (φ, z) hp)
        (analyticAt_const.prod analyticAt_id)
    exact (((analyticAt_id.pow k).mul h1).div h2 (canonRoot_ne_zero38 φ hφ z hzg)).continuousAt.continuousWithinAt
  · -- (c) the uniform weighted bound
    intro φ₀ hφ₀
    obtain ⟨V1, hV1, hV1W, B, hB0, hB⟩ := G2042S1.lamDot_growth_local φ₀ hφ₀
    obtain ⟨U0, hU0o, hφU0, hU0W, C, hC0, hU⟩ :=
      G2042MomentB.criticalMoment_uniform_bound k (by omega) φ₀ hφ₀
    obtain ⟨Bm, hBm⟩ : ∃ b : ℝ, b = max 1 B := ⟨_, rfl⟩
    have hBm1 : 1 ≤ Bm := by rw [hBm]; exact le_max_left _ _
    have hBm0 : 0 ≤ Bm := by linarith
    have hBmB : B ≤ Bm := by rw [hBm]; exact le_max_right _ _
    obtain ⟨Cf, hCf⟩ : ∃ c : ℝ, c = (k : ℝ) * (2 ^ k * Bm ^ k * C) + 1 := ⟨_, rfl⟩
    have hCf0 : 0 < Cf := by
      rw [hCf]
      have : 0 ≤ (k : ℝ) * (2 ^ k * Bm ^ k * C) :=
        mul_nonneg (Nat.cast_nonneg k) (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hBm0 k)) hC0.le)
      linarith
    have hWn : V1 ∩ U0 ∈ 𝓝 φ₀ := inter_mem hV1 (hU0o.mem_nhds hφU0)
    refine ⟨interior (V1 ∩ U0), isOpen_interior, mem_interior_iff_mem_nhds.mpr hWn,
      fun φ hφ => hU0W (interior_subset hφ).2, Cf, hCf0, ?_⟩
    intro φ hφ n
    have hφW := interior_subset hφ
    have hφV1 : φ ∈ V1 := hφW.1
    have hφU0' : φ ∈ U0 := hφW.2
    have hφg : φ ∈ gkW := hU0W hφU0'
    have hJ1 : 1 ≤ japaneseBracket n := G2042S1.one_le_japaneseBracket_G2042 n
    have hJ0 : 0 ≤ japaneseBracket n := by linarith
    have hlamb : ‖lamDot φ n‖ ≤ Bm * japaneseBracket n := by
      have h1 := hB φ hφV1 n
      have h2 : B * japaneseBracket n ≤ Bm * japaneseBracket n :=
        mul_le_mul_of_nonneg_right hBmB hJ0
      linarith
    -- binomial expansion with the zero mode removed
    have hzero : G2042MomentA.criticalMoment 0 φ n = 0 := by
      unfold G2042MomentA.criticalMoment
      simp only [pow_zero, one_mul]
      rw [G2042S1.zeroPeriod_gkW φ hφg (discC φ) (discR φ) (isolating_family38 φ hφg) n, mul_zero]
    have hexp : higherAction k φ n = ∑ m ∈ Finset.range (k + 1),
        ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) * G2042MomentA.criticalMoment m φ n := by
      have hsplit : circleIntegral (fun z : ℂ => z ^ k * deriv (discrim φ) z / canonRoot38 φ z)
          (discC φ n) (discR φ n) = ∑ m ∈ Finset.range (k + 1),
            ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) *
              circleIntegral (fun z : ℂ => (z - lamDot φ n) ^ m * deriv (discrim φ) z / canonRoot38 φ z)
                (discC φ n) (discR φ n) := by
        have hfun : (fun z : ℂ => z ^ k * deriv (discrim φ) z / canonRoot38 φ z) =
            (fun z : ℂ => ∑ m ∈ Finset.range (k + 1),
              ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) *
                ((z - lamDot φ n) ^ m * deriv (discrim φ) z / canonRoot38 φ z)) :=
          funext (fun z => G2042Pkt.binom_split k φ n z)
        rw [hfun]
        rw [G2042Pkt.circle_sum_eq (Finset.range (k + 1))
          (fun m z => ((k.choose m : ℂ) * lamDot φ n ^ (k - m)) *
            ((z - lamDot φ n) ^ m * deriv (discrim φ) z / canonRoot38 φ z)) (discC φ n) (discR φ n)
          (fun m _ => (G2042MomentA.circleIntegrable_moment m φ hφg n).const_mul _)]
        apply Finset.sum_congr rfl
        intro m _
        rw [circleIntegral.integral_const_mul]
      unfold higherAction G2042MomentA.criticalMoment
      rw [hsplit, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [hexp, Finset.sum_range_succ']
    simp only [hzero, mul_zero, add_zero]
    -- termwise bound for m + 1 ∈ [1, k]
    have hterm : ∀ m ∈ Finset.range k,
        ‖((k.choose (m + 1) : ℂ) * lamDot φ n ^ (k - (m + 1))) *
            G2042MomentA.criticalMoment (m + 1) φ n‖ ≤
          (2 ^ k * (Bm ^ k * japaneseBracket n ^ (k - 1))) * (C * ‖gamma2 φ n‖) := by
      intro m hm
      have hm' : m < k := Finset.mem_range.mp hm
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      apply mul_le_mul _ (hU φ hφU0' n (m + 1) (by omega) (by omega)) (norm_nonneg _)
      · exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hBm0 _) (pow_nonneg hJ0 _))
      · have hch : ((k.choose (m + 1) : ℕ) : ℝ) ≤ 2 ^ k := by
          exact_mod_cast Nat.choose_le_two_pow k (m + 1)
        have hnorm : ‖lamDot φ n‖ ^ (k - (m + 1)) ≤ (Bm * japaneseBracket n) ^ (k - (m + 1)) :=
          pow_le_pow_left₀ (norm_nonneg _) hlamb _
        have hpow1 : (Bm * japaneseBracket n) ^ (k - (m + 1)) =
            Bm ^ (k - (m + 1)) * japaneseBracket n ^ (k - (m + 1)) := mul_pow _ _ _
        have hpow2 : Bm ^ (k - (m + 1)) ≤ Bm ^ k := pow_le_pow_right₀ hBm1 (by omega)
        have hpow3 : japaneseBracket n ^ (k - (m + 1)) ≤ japaneseBracket n ^ (k - 1) :=
          pow_le_pow_right₀ hJ1 (by omega)
        calc ((k.choose (m + 1) : ℕ) : ℝ) * ‖lamDot φ n‖ ^ (k - (m + 1))
            ≤ 2 ^ k * ‖lamDot φ n‖ ^ (k - (m + 1)) :=
              mul_le_mul_of_nonneg_right hch (pow_nonneg (norm_nonneg _) _)
          _ ≤ 2 ^ k * (Bm ^ k * japaneseBracket n ^ (k - 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              calc ‖lamDot φ n‖ ^ (k - (m + 1)) ≤ (Bm * japaneseBracket n) ^ (k - (m + 1)) := hnorm
                _ = Bm ^ (k - (m + 1)) * japaneseBracket n ^ (k - (m + 1)) := hpow1
                _ ≤ Bm ^ k * japaneseBracket n ^ (k - 1) :=
                    mul_le_mul hpow2 hpow3 (pow_nonneg hJ0 _) (pow_nonneg hBm0 _)
    calc ‖∑ m ∈ Finset.range k, ((k.choose (m + 1) : ℂ) * lamDot φ n ^ (k - (m + 1))) *
            G2042MomentA.criticalMoment (m + 1) φ n‖
        ≤ ∑ m ∈ Finset.range k, ‖((k.choose (m + 1) : ℂ) * lamDot φ n ^ (k - (m + 1))) *
            G2042MomentA.criticalMoment (m + 1) φ n‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.range k, (2 ^ k * (Bm ^ k * japaneseBracket n ^ (k - 1))) *
            (C * ‖gamma2 φ n‖) := Finset.sum_le_sum (fun m hm => hterm m hm)
      _ = (k : ℝ) * ((2 ^ k * (Bm ^ k * japaneseBracket n ^ (k - 1))) *
            (C * ‖gamma2 φ n‖)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ Cf * japaneseBracket n ^ (k - 1) * ‖gamma2 φ n‖ := by
          have hX0 : 0 ≤ japaneseBracket n ^ (k - 1) * ‖gamma2 φ n‖ :=
            mul_nonneg (pow_nonneg hJ0 _) (norm_nonneg _)
          have hK : (k : ℝ) * ((2 ^ k * (Bm ^ k * japaneseBracket n ^ (k - 1))) *
              (C * ‖gamma2 φ n‖)) = ((k : ℝ) * (2 ^ k * Bm ^ k * C)) *
                (japaneseBracket n ^ (k - 1) * ‖gamma2 φ n‖) := by ring
          rw [hK, hCf]
          nlinarith [hX0]

end

end NlsGge.GKDefinitionDesign
