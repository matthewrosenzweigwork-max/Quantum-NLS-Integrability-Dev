import NlsGge.ThirdConsultation.R.RamerSetting06

                                                                                                          
                                                                                                                   
                                                                                                                         
                                                         
                                                                                                                        
                                                                                                                          
                                                                                                                  
                                                                                                                          
                                                                                                                        
set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology

namespace NlsGge.ThirdConsultation.R
noncomputable section

namespace R034Aux

theorem core
    {E₀ H₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup H₀] [NormedSpace ℝ H₀] [CompleteSpace H₀]
    (i : H₀ →L[ℝ] E₀) (Φ : E₀ → H₀) (ε : ℝ) (hε : 0 < ε)
    (hdiff : ∀ y ∈ closedBall (0 : E₀) ε, DifferentiableAt ℝ Φ y)
    (hsm : ∀ y ∈ closedBall (0 : E₀) ε, ‖i (Φ y)‖ ≤ ε / 4)
    (hD : ∀ y ∈ closedBall (0 : E₀) ε, ‖HDeriv i Φ y‖ ≤ (1 / 2 : ℝ))
    (z : E₀) (hz : z ∈ ball (0 : E₀) (ε / 2)) :
    ∃ h : H₀, ‖h‖ ≤ 2 * ‖Φ z‖ ∧
      z + i h ∈ closedBall (0 : E₀) ε ∧
      (z + i h) + i (Φ (z + i h)) = z := by
  -- Lipschitz bound along a Cameron-Martin direction inside the closed ball.
  have hlip : ∀ x ∈ closedBall (0 : E₀) ε, ∀ x' ∈ closedBall (0 : E₀) ε, ∀ k : H₀,
      x - x' = i k → ‖Φ x - Φ x'‖ ≤ (1 / 2 : ℝ) * ‖k‖ := by
    intro x hx x' hx' k hxk
    have hx_eq : x = i k + x' := sub_eq_iff_eq_add.mp hxk
    have hx'_eq : x' + i k = x := by rw [hx_eq, add_comm]
    have hγ : ∀ t ∈ Icc (0 : ℝ) 1, x' + t • i k ∈ closedBall (0 : E₀) ε := by
      intro t ht
      have e : x' + t • i k = (1 - t) • x' + t • x := by
        rw [hx_eq]
        module
      rw [e]
      exact (convex_closedBall (0 : E₀) ε) hx' hx (by linarith [ht.2]) ht.1 (by ring)
    have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun t : ℝ => Φ (x' + t • i k)) (fderiv ℝ Φ (x' + t • i k) (i k))
          (Icc (0 : ℝ) 1) t := by
      intro t ht
      have hΦ : HasFDerivAt Φ (fderiv ℝ Φ (x' + t • i k)) (x' + t • i k) :=
        (hdiff _ (hγ t ht)).hasFDerivAt
      have h0 : HasDerivAt (fun t : ℝ => t • i k) (i k) t := by
        have h1 := (hasDerivAt_id' t).smul_const (i k)
        rwa [one_smul] at h1
      have hg : HasDerivAt (fun t : ℝ => x' + t • i k) (i k) t := h0.const_add x'
      exact (hΦ.comp_hasDerivAt t hg).hasDerivWithinAt
    have hbound : ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ Φ (x' + t • i k) (i k)‖ ≤ (1 / 2 : ℝ) * ‖k‖ := by
      intro t ht
      have h1 : fderiv ℝ Φ (x' + t • i k) (i k) = HDeriv i Φ (x' + t • i k) k := rfl
      rw [h1]
      calc ‖HDeriv i Φ (x' + t • i k) k‖ ≤ ‖HDeriv i Φ (x' + t • i k)‖ * ‖k‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (1 / 2 : ℝ) * ‖k‖ :=
            mul_le_mul_of_nonneg_right (hD _ (hγ t ht)) (norm_nonneg _)
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc (0 : ℝ) 1)
      (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one)
    simp only [one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one, hx'_eq] at hmv
    exact hmv
  have hz' : ‖z‖ < ε / 2 := mem_ball_zero_iff.mp hz
  have hzC : z ∈ closedBall (0 : E₀) ε := mem_closedBall_zero_iff.mpr (by linarith)
  -- the closed, hence complete, set of admissible fibre parameters
  have hKc : IsClosed {h : H₀ | z + i h ∈ closedBall (0 : E₀) ε ∧ ‖h‖ ≤ 2 * ‖Φ z‖} :=
    (isClosed_closedBall.preimage (continuous_const.add i.continuous)).inter
      (isClosed_le continuous_norm continuous_const)
  have hKcomp := hKc.isComplete
  have hmaps : MapsTo (fun h : H₀ => -Φ (z + i h))
      {h : H₀ | z + i h ∈ closedBall (0 : E₀) ε ∧ ‖h‖ ≤ 2 * ‖Φ z‖}
      {h : H₀ | z + i h ∈ closedBall (0 : E₀) ε ∧ ‖h‖ ≤ 2 * ‖Φ z‖} := by
    intro h hh
    obtain ⟨hy, hn⟩ := hh
    have h1 : ‖Φ (z + i h) - Φ z‖ ≤ (1 / 2 : ℝ) * ‖h‖ :=
      hlip (z + i h) hy z hzC h (add_sub_cancel_left _ _)
    have hnorm : ‖Φ (z + i h)‖ ≤ ‖Φ z‖ + ‖Φ (z + i h) - Φ z‖ := by
      have := norm_add_le (Φ z) (Φ (z + i h) - Φ z)
      have e : Φ z + (Φ (z + i h) - Φ z) = Φ (z + i h) := by abel
      rw [e] at this
      exact this
    have h2 : ‖i (Φ (z + i h))‖ ≤ ε / 4 := hsm _ hy
    have h3 := norm_sub_le z (i (Φ (z + i h)))
    refine ⟨?_, ?_⟩
    · show z + i (-Φ (z + i h)) ∈ closedBall (0 : E₀) ε
      rw [mem_closedBall_zero_iff, map_neg, ← sub_eq_add_neg]
      linarith
    · show ‖-Φ (z + i h)‖ ≤ 2 * ‖Φ z‖
      rw [norm_neg]
      linarith
  have hlipK : LipschitzWith (1 / 2 : NNReal)
      (hmaps.restrict (fun h : H₀ => -Φ (z + i h)) _ _) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    have hc : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
    show dist (-Φ (z + i (a : H₀))) (-Φ (z + i (b : H₀))) ≤
      ((1 / 2 : NNReal) : ℝ) * dist (a : H₀) (b : H₀)
    rw [hc, dist_eq_norm, dist_eq_norm, neg_sub_neg, norm_sub_rev (a : H₀) (b : H₀)]
    have hxk : (z + i (b : H₀)) - (z + i (a : H₀)) = i ((b : H₀) - (a : H₀)) := by
      rw [map_sub]
      abel
    exact hlip (z + i (b : H₀)) b.2.1 (z + i (a : H₀)) a.2.1 ((b : H₀) - (a : H₀)) hxk
  have hcontr : ContractingWith (1 / 2 : NNReal)
      (hmaps.restrict (fun h : H₀ => -Φ (z + i h)) _ _) := ⟨by norm_num, hlipK⟩
  have hK0 : (0 : H₀) ∈ {h : H₀ | z + i h ∈ closedBall (0 : E₀) ε ∧ ‖h‖ ≤ 2 * ‖Φ z‖} := by
    refine ⟨?_, ?_⟩
    · simpa using hzC
    · rw [norm_zero]
      positivity
  obtain ⟨y, hyK, hyfix, -, -⟩ :=
    ContractingWith.exists_fixedPoint' hKcomp hmaps hcontr hK0 (edist_ne_top _ _)
  have hy' : -Φ (z + i y) = y := hyfix
  have hΦy : Φ (z + i y) = -y := neg_eq_iff_eq_neg.mp hy'
  refine ⟨y, hyK.2, hyK.1, ?_⟩
  rw [hΦy, map_neg, add_neg_cancel_right]

end R034Aux

section SmallMapBall
variable {lower upper : ℝ}
variable (c : NlsGge.Pilot.BoundedCoefficients lower upper)
variable (s : ℝ) (hs : (1 : ℝ) / 2 < s)

local notation "E" => RamerE c s
local notation "H" => RamerH c
local notation "i" => cmEmbedding c s hs

/-- R-034: small-map surjectivity and the H-fibre bound. -/
theorem exists_add_image_eq
    (Φ : E → H) (ε : ℝ)
    (hSmall : SmallFibreField c s hs Φ ε) :
    ∀ z ∈ ball (0 : E) (ε / 2),
      ∃ h : H, ‖h‖ ≤ 2 * ‖Φ z‖ ∧
        z + i h ∈ closedBall (0 : E) ε ∧
        (z + i h) + i (Φ (z + i h)) = z := by
  obtain ⟨hε, hdiff, hsm, hD⟩ := hSmall
  intro z hz
  exact R034Aux.core (cmEmbedding c s hs) Φ ε hε hdiff hsm hD z hz

end SmallMapBall

end
end NlsGge.ThirdConsultation.R
