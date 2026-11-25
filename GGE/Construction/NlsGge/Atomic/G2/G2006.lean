                                                                                                                                                                                                                                                                   
import Mathlib
import NlsGge.Atomic.G2.G2005

section

                                                                       
                                                                                              
                                                                                                       
                                                                                                
                                               

                                                      
                                                                                           
                                                 

set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis.BanachHolomorphy

open Metric Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- P1: Cauchy estimate for the Fréchet derivative of an analytic map. -/
theorem norm_fderiv_le_of_analytic {G : E → F} {U : Set E} (hG : AnalyticOnNhd ℂ G U) {y : E}
    {δ C : ℝ} (hδ : 0 < δ) (hU : closedBall y δ ⊆ U) (hC : ∀ z ∈ closedBall y δ, ‖G z‖ ≤ C) :
    ‖fderiv ℂ G y‖ ≤ C / δ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC y (mem_closedBall_self hδ.le))
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg hC0 hδ.le) (fun h => ?_)
  by_cases hh : h = 0
  · simp [hh]
  have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
  set R : ℝ := δ / ‖h‖ with hR
  have hRpos : 0 < R := by positivity
  have hmem : ∀ ζ : ℂ, ζ ∈ closedBall (0 : ℂ) R → y + ζ • h ∈ closedBall y δ := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right] at hζ
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    calc ‖ζ‖ * ‖h‖ ≤ R * ‖h‖ := mul_le_mul_of_nonneg_right hζ hnh.le
      _ = δ := by rw [hR]; field_simp
  have hline : ∀ ζ : ℂ, HasDerivAt (fun ζ : ℂ => y + ζ • h) h ζ := by
    intro ζ
    simpa using ((hasDerivAt_id ζ).smul_const h).const_add y
  have hd : ∀ ζ : ℂ, ζ ∈ closedBall (0 : ℂ) R →
      HasDerivAt (fun ζ : ℂ => G (y + ζ • h)) (fderiv ℂ G (y + ζ • h) h) ζ := by
    intro ζ hζ
    exact HasFDerivAt.comp_hasDerivAt ζ
      ((hG _ (hU (hmem ζ hζ))).differentiableAt.hasFDerivAt) (hline ζ)
  have hdc : DiffContOnCl ℂ (fun ζ : ℂ => G (y + ζ • h)) (ball (0 : ℂ) R) := by
    refine ⟨fun ζ hζ => (hd ζ (ball_subset_closedBall hζ)).differentiableAt.differentiableWithinAt,
      ?_⟩
    rw [closure_ball (0 : ℂ) hRpos.ne']
    exact fun ζ hζ => (hd ζ hζ).continuousAt.continuousWithinAt
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) R, ‖G (y + ζ • h)‖ ≤ C := fun ζ hζ =>
    hC _ (hmem ζ (sphere_subset_closedBall hζ))
  have key := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc hsph
  have h0 : deriv (fun ζ : ℂ => G (y + ζ • h)) 0 = fderiv ℂ G y h := by
    have := hd 0 (mem_closedBall_self hRpos.le)
    simpa using this.deriv
  rw [h0] at key
  calc ‖fderiv ℂ G y h‖ ≤ C / R := key
    _ = C / δ * ‖h‖ := by rw [hR]; field_simp

variable [CompleteSpace F]

/-- P2: iterated Cauchy estimate with shrinking balls. -/
theorem norm_iteratedFDeriv_le {G : E → F} {U : Set E} (hG : AnalyticOnNhd ℂ G U) {x : E}
    {ρ M : ℝ} (hρ : 0 < ρ) (hxU : closedBall x ρ ⊆ U) (hM : ∀ z ∈ closedBall x ρ, ‖G z‖ ≤ M)
    (n : ℕ) (hn : 1 ≤ n) : ‖iteratedFDeriv ℂ n G x‖ ≤ ((n : ℝ) / ρ) ^ n * M := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set δ : ℝ := ρ / n with hδ
  have hδpos : 0 < δ := by positivity
  have hnδ : (n : ℝ) * δ = ρ := by rw [hδ]; field_simp
  have claim : ∀ k : ℕ, k ≤ n → ∀ y : E, dist y x ≤ ((n : ℝ) - k) * δ →
      ‖iteratedFDeriv ℂ k G y‖ ≤ ((n : ℝ) / ρ) ^ k * M := by
    intro k
    induction k with
    | zero =>
      intro _ y hy
      rw [norm_iteratedFDeriv_zero, pow_zero, one_mul]
      apply hM
      rw [mem_closedBall]
      simpa [hnδ] using hy
    | succ k ih =>
      intro hk y hy
      have hkn : k ≤ n := Nat.le_of_succ_le hk
      have hkn' : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
      push_cast at hy hkn'
      have hball : closedBall y δ ⊆ closedBall x ρ := by
        intro z hz
        rw [mem_closedBall] at hz ⊢
        have : dist z x ≤ ((n : ℝ) - k) * δ := by
          calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
            _ ≤ δ + ((n : ℝ) - (k + 1)) * δ := add_le_add hz hy
            _ = ((n : ℝ) - k) * δ := by ring
        calc dist z x ≤ ((n : ℝ) - k) * δ := this
          _ ≤ (n : ℝ) * δ := by
              apply mul_le_mul_of_nonneg_right _ hδpos.le
              have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
              linarith
          _ = ρ := hnδ
      have hH : AnalyticOnNhd ℂ (iteratedFDeriv ℂ k G) U := hG.iteratedFDeriv k
      have hbound : ∀ z ∈ closedBall y δ, ‖iteratedFDeriv ℂ k G z‖ ≤ ((n : ℝ) / ρ) ^ k * M := by
        intro z hz
        apply ih hkn
        rw [← mem_closedBall]
        have hz' : z ∈ closedBall x ρ := hball hz
        rw [mem_closedBall] at hz hz' ⊢
        calc dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
          _ ≤ δ + ((n : ℝ) - (k + 1)) * δ := add_le_add hz hy
          _ = ((n : ℝ) - k) * δ := by ring
      have hP1 := norm_fderiv_le_of_analytic hH hδpos (hball.trans hxU) hbound
      rw [← norm_fderiv_iteratedFDeriv]
      refine hP1.trans (le_of_eq ?_)
      rw [hδ, pow_succ]
      field_simp
  have := claim n le_rfl x (by simp)
  exact this

/-- P3 at the origin: Taylor expansion along a line. -/
theorem hasSum_iteratedFDeriv_origin {G : E → F} {ρ : ℝ} (hG : ∀ z ∈ ball (0 : E) ρ, AnalyticAt ℂ G z)
    {y : E} (hy : ‖y‖ < ρ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n G 0 (fun _ => y)) (G y) := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hy
  have hyb : y ∈ ball (0 : E) ρ := by simpa using hy
  -- the line map
  set u : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight y with hu
  have hu_apply : ∀ ζ : ℂ, u ζ = ζ • y := fun ζ => by simp [hu]
  have hu_norm : ∀ ζ : ℂ, ‖u ζ‖ = ‖ζ‖ * ‖y‖ := fun ζ => by rw [hu_apply, norm_smul]
  -- choose a radius R > 1 with R ‖y‖ < ρ
  set R : ℝ := 1 + (ρ - ‖y‖) / (2 * (‖y‖ + 1)) with hR
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hRgt : 1 < R := by
    have : 0 < (ρ - ‖y‖) / (2 * (‖y‖ + 1)) := by
      apply div_pos (by linarith) (by positivity)
    linarith
  have hRy : R * ‖y‖ < ρ := by
    have h1 : (ρ - ‖y‖) / (2 * (‖y‖ + 1)) * ‖y‖ ≤ (ρ - ‖y‖) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ ρ - ‖y‖) hy0]
    calc R * ‖y‖ = ‖y‖ + (ρ - ‖y‖) / (2 * (‖y‖ + 1)) * ‖y‖ := by rw [hR]; ring
      _ ≤ ‖y‖ + (ρ - ‖y‖) / 2 := by linarith
      _ < ρ := by linarith
  set Rn : NNReal := ⟨R, by linarith⟩ with hRn
  have hRnR : (Rn : ℝ) = R := rfl
  have hRnpos : (0 : NNReal) < Rn := by
    have h : (0 : ℝ) < (Rn : ℝ) := by rw [hRnR]; linarith
    exact_mod_cast h
  -- differentiability of the line function on the closed disc
  have hmem : ∀ ζ : ℂ, ζ ∈ closedBall (0 : ℂ) (Rn : ℝ) → u ζ ∈ ball (0 : E) ρ := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right] at hζ
    rw [mem_ball, dist_zero_right, hu_norm]
    calc ‖ζ‖ * ‖y‖ ≤ R * ‖y‖ := mul_le_mul_of_nonneg_right (by rw [← hRnR]; exact hζ) hy0
      _ < ρ := hRy
  have hdiff : DifferentiableOn ℂ (G ∘ u) (closedBall (0 : ℂ) (Rn : ℝ)) := by
    intro ζ hζ
    exact ((hG _ (hmem ζ hζ)).differentiableAt.comp ζ u.differentiableAt).differentiableWithinAt
  have hCauchy := hdiff.hasFPowerSeriesOnBall hRnpos
  -- local power series of G at 0 and of the line function
  obtain ⟨p, r, hp⟩ := hG 0 (mem_ball_self hρ)
  have hp' : HasFPowerSeriesOnBall G p (u 0) r := by simpa using hp
  have hline := hp'.compContinuousLinearMap (u := u) (x := (0 : ℂ))
  have heq : cauchyPowerSeries (G ∘ u) 0 (Rn : ℝ) = p.compContinuousLinearMap u :=
    hCauchy.hasFPowerSeriesAt.eq_formalMultilinearSeries hline.hasFPowerSeriesAt
  have h1 : (1 : ℂ) ∈ Metric.eball (0 : ℂ) (Rn : ENNReal) := by
    rw [Metric.mem_eball, edist_zero_right, enorm_one]
    have h : (1 : NNReal) < Rn := by
      have : (1 : ℝ) < (Rn : ℝ) := by rw [hRnR]; exact hRgt
      exact_mod_cast this
    exact_mod_cast h
  have hsum := hCauchy.hasSum h1
  rw [heq] at hsum
  simp only [zero_add] at hsum
  have hu1 : u 1 = y := by simp [hu_apply]
  have key : ∀ n : ℕ, ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n G 0 (fun _ => y) =
      (p.compContinuousLinearMap u) n (fun _ => (1 : ℂ)) := by
    intro n
    rw [← hp.factorial_smul y n, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), one_smul]
    simp [FormalMultilinearSeries.compContinuousLinearMap, hu1]
  have hfun : (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n G 0 (fun _ => y)) =
      fun n => (p.compContinuousLinearMap u) n (fun _ => (1 : ℂ)) := funext key
  rw [hfun]
  simpa [Function.comp, hu1] using hsum

/-- P2 for all `n` (the case `n = 0` is the sup bound). -/
theorem norm_iteratedFDeriv_le' {G : E → F} {U : Set E} (hG : AnalyticOnNhd ℂ G U) {x : E}
    {ρ M : ℝ} (hρ : 0 < ρ) (hxU : closedBall x ρ ⊆ U) (hM : ∀ z ∈ closedBall x ρ, ‖G z‖ ≤ M)
    (n : ℕ) : ‖iteratedFDeriv ℂ n G x‖ ≤ ((n : ℝ) / ρ) ^ n * M := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    simpa using hM x (mem_closedBall_self hρ.le)
  · exact norm_iteratedFDeriv_le hG hρ hxU hM n hpos

/-- P3 at a base point `x`. -/
theorem hasSum_iteratedFDeriv {G : E → F} {x : E} {ρ : ℝ}
    (hG : ∀ z ∈ ball x ρ, AnalyticAt ℂ G z) {y : E} (hy : ‖y‖ < ρ) :
    HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n G x (fun _ => y)) (G (x + y)) := by
  have hψ : ∀ z ∈ ball (0 : E) ρ, AnalyticAt ℂ (fun w => G (x + w)) z := by
    intro z hz
    have hz' : x + z ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm] at hz ⊢
      simpa using hz
    exact (hG (x + z) hz').comp (f := fun w : E => x + w) (analyticAt_const.add analyticAt_id)
  have := hasSum_iteratedFDeriv_origin hψ hy
  simpa [iteratedFDeriv_comp_add_left] using this

/-- `n^n / n! ≤ e^n`, in the form used for the Cauchy estimates. -/
private lemma pow_div_factorial_le (n : ℕ) :
    ((n : ℝ) ^ n) / (n.factorial : ℝ) ≤ Real.exp 1 ^ n := by
  have := Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have h2 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [← Real.exp_nat_mul]; simp
  rwa [h2] at this

/-- Main theorem (ii): a uniform-on-neighbourhoods limit of analytic maps on an open subset of
a complex normed space, with complete target, is analytic. -/
theorem analyticOnNhd_of_tendstoUniformlyOn_nhds {U : Set E} (hU : IsOpen U)
    {Fk : ℕ → E → F} {P : E → F} (hF : ∀ k, AnalyticOnNhd ℂ (Fk k) U)
    (hlim : ∀ x ∈ U, ∃ t ∈ nhds x, TendstoUniformlyOn Fk P Filter.atTop t) :
    AnalyticOnNhd ℂ P U := by
  intro x0 hx0
  obtain ⟨t, ht, hunif⟩ := hlim x0 hx0
  -- radius ε with ball ⊆ t ∩ U
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht (hU.mem_nhds hx0))
  -- eventually all F_k are within 1 of P on t
  have h1 : ∀ᶠ k in Filter.atTop, ∀ y ∈ t, dist (P y) (Fk k y) < 1 :=
    (Metric.tendstoUniformlyOn_iff.1 hunif) 1 one_pos
  obtain ⟨k0, hk0⟩ := h1.exists_forall_of_atTop
  -- local boundedness of F_{k0}
  have hcont : ContinuousAt (Fk k0) x0 := (hF k0 x0 hx0).continuousAt
  obtain ⟨ρ1, hρ1, hρ1b⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
  set ρ : ℝ := min (ε / 2) (ρ1 / 2) with hρdef
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρε : ρ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρρ1 : ρ < ρ1 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hballt : closedBall x0 ρ ⊆ t := fun z hz =>
    (hεt (Metric.closedBall_subset_ball hρε hz)).1
  have hballU : closedBall x0 ρ ⊆ U := fun z hz =>
    (hεt (Metric.closedBall_subset_ball hρε hz)).2
  set M : ℝ := ‖Fk k0 x0‖ + 3 with hMdef
  have hM : ∀ k, k0 ≤ k → ∀ z ∈ closedBall x0 ρ, ‖Fk k z‖ ≤ M := by
    intro k hk z hz
    have hz1 : dist z x0 < ρ1 := lt_of_le_of_lt (mem_closedBall.1 hz) hρρ1
    have a1 : dist (P z) (Fk k z) < 1 := hk0 k hk z (hballt hz)
    have a2 : dist (P z) (Fk k0 z) < 1 := hk0 k0 le_rfl z (hballt hz)
    have a3 : dist (Fk k0 z) (Fk k0 x0) < 1 := hρ1b hz1
    have e1 : ‖Fk k z‖ ≤ ‖Fk k z - P z‖ + ‖P z - Fk k0 z‖ + ‖Fk k0 z - Fk k0 x0‖ + ‖Fk k0 x0‖ := by
      calc ‖Fk k z‖ = ‖(Fk k z - P z) + (P z - Fk k0 z) + (Fk k0 z - Fk k0 x0) + Fk k0 x0‖ := by
            congr 1; abel
        _ ≤ _ := by
            refine (norm_add_le _ _).trans ?_
            gcongr
            exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    rw [dist_eq_norm] at a1 a2 a3
    have : ‖Fk k z - P z‖ = ‖P z - Fk k z‖ := norm_sub_rev _ _
    rw [hMdef]; linarith
  -- Cauchy sequences of Taylor coefficients
  have hCauchy : ∀ n : ℕ, CauchySeq (fun k => ((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0) := by
    intro n
    rw [Metric.cauchySeq_iff]
    intro η hη
    set Cn : ℝ := ((n.factorial : ℝ))⁻¹ * (((n : ℝ)) / ρ) ^ n with hCn
    have hCn0 : 0 ≤ Cn := by positivity
    set ε' : ℝ := η / (Cn + 1) with hε'
    have hε'pos : 0 < ε' := by positivity
    have h2 : ∀ᶠ k in Filter.atTop, ∀ y ∈ t, dist (P y) (Fk k y) < ε' / 2 :=
      (Metric.tendstoUniformlyOn_iff.1 hunif) (ε' / 2) (by positivity)
    obtain ⟨N, hN⟩ := h2.exists_forall_of_atTop
    refine ⟨N, fun k hk l hl => ?_⟩
    have hdiffU : AnalyticOnNhd ℂ (Fk k - Fk l) U := (hF k).sub (hF l)
    have hb : ∀ z ∈ closedBall x0 ρ, ‖(Fk k - Fk l) z‖ ≤ ε' := by
      intro z hz
      have a1 := hN k hk z (hballt hz)
      have a2 := hN l hl z (hballt hz)
      rw [dist_eq_norm] at a1 a2
      calc ‖(Fk k - Fk l) z‖ = ‖(P z - Fk l z) - (P z - Fk k z)‖ := by
            simp only [Pi.sub_apply]; congr 1; abel
        _ ≤ ‖P z - Fk l z‖ + ‖P z - Fk k z‖ := norm_sub_le _ _
        _ ≤ ε' := by linarith
    have hP2 := norm_iteratedFDeriv_le' hdiffU hρ hballU hb n
    have hsub : iteratedFDeriv ℂ n (Fk k - Fk l) x0 =
        iteratedFDeriv ℂ n (Fk k) x0 - iteratedFDeriv ℂ n (Fk l) x0 :=
      iteratedFDeriv_sub_apply (((hF k x0 hx0).contDiffAt)) (((hF l x0 hx0).contDiffAt))
    rw [hsub] at hP2
    rw [dist_eq_norm, ← smul_sub, norm_smul, norm_inv, Complex.norm_natCast]
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n (Fk k) x0 - iteratedFDeriv ℂ n (Fk l) x0‖
        ≤ (n.factorial : ℝ)⁻¹ * (((n : ℝ) / ρ) ^ n * ε') :=
          mul_le_mul_of_nonneg_left hP2 (by positivity)
      _ = Cn * ε' := by rw [hCn]; ring
      _ ≤ Cn * ε' := le_rfl
      _ < η := by
          rw [hε']
          have : Cn * (η / (Cn + 1)) < η := by
            rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
            nlinarith
          exact this
  -- the limit coefficients
  choose Q hQ using fun n => cauchySeq_tendsto_of_complete (hCauchy n)
  set e1 : ℝ := Real.exp 1 with he1
  have he1pos : 0 < e1 := Real.exp_pos 1
  have hAbound : ∀ k, k0 ≤ k → ∀ n : ℕ,
      ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0‖ ≤ M * (e1 / ρ) ^ n := by
    intro k hk n
    have hP2 := norm_iteratedFDeriv_le' (hF k) hρ hballU (hM k hk) n
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hpd := pow_div_factorial_le n
    calc (n.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℂ n (Fk k) x0‖
        ≤ (n.factorial : ℝ)⁻¹ * (((n : ℝ) / ρ) ^ n * M) :=
          mul_le_mul_of_nonneg_left hP2 (by positivity)
      _ = M * (((n : ℝ) ^ n / n.factorial) / ρ ^ n) := by rw [div_pow]; field_simp
      _ ≤ M * (e1 ^ n / ρ ^ n) := by
          have hM0 : 0 ≤ M := by rw [hMdef]; positivity
          gcongr
      _ = M * (e1 / ρ) ^ n := by rw [div_pow]
  have hQbound : ∀ n : ℕ, ‖Q n‖ ≤ M * (e1 / ρ) ^ n := by
    intro n
    refine le_of_tendsto (tendsto_norm.comp (hQ n)) ?_
    filter_upwards [Filter.eventually_ge_atTop k0] with k hk using hAbound k hk n
  -- radius
  set r0 : NNReal := ⟨ρ / (2 * e1), by positivity⟩ with hr0
  have hr0val : (r0 : ℝ) = ρ / (2 * e1) := rfl
  have hr0pos : (0 : NNReal) < r0 := by
    rw [← NNReal.coe_lt_coe, hr0val]; simp; positivity
  let Qs : FormalMultilinearSeries ℂ E F := Q
  have hradius : (r0 : ENNReal) ≤ Qs.radius := by
    refine FormalMultilinearSeries.le_radius_of_bound _ M (fun n => ?_)
    have hM0 : 0 ≤ M := by rw [hMdef]; positivity
    calc ‖Qs n‖ * (r0 : ℝ) ^ n
        ≤ M * (e1 / ρ) ^ n * (r0 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (hQbound n) (by positivity)
      _ = M * (1 / 2) ^ n := by
          rw [hr0val, mul_assoc, ← mul_pow]
          congr 2; field_simp
      _ ≤ M * 1 := by
          gcongr
          exact pow_le_one₀ (by norm_num) (by norm_num)
      _ = M := mul_one M
  refine ⟨Qs, r0, ?_⟩
  refine ⟨hradius, ENNReal.coe_pos.2 hr0pos, ?_⟩
  intro y hy
  have hyr : ‖y‖ < r0 := by
    rw [Metric.mem_eball, edist_zero_right] at hy
    have : (‖y‖₊ : ENNReal) < r0 := by simpa [enorm] using hy
    exact_mod_cast ENNReal.coe_lt_coe.1 this
  have hyρ : ‖y‖ < ρ := by
    have : (r0 : ℝ) < ρ := by
      rw [hr0val, div_lt_iff₀ (by positivity)]; nlinarith [he1pos, Real.add_one_le_exp (1 : ℝ)]
    linarith
  set q : ℝ := ‖y‖ * (e1 / ρ) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    have : (‖y‖ : ℝ) < ρ / (2 * e1) := hyr
    rw [hq]
    calc ‖y‖ * (e1 / ρ) < ρ / (2 * e1) * (e1 / ρ) := by gcongr
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have hbsum : Summable (fun n : ℕ => M * q ^ n) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left M
  -- termwise convergence and domination
  have hab : ∀ n : ℕ, Filter.Tendsto
      (fun k => (((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0) (fun _ => y)) Filter.atTop
      (nhds (Q n (fun _ => y))) := by
    intro n
    exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin n => E) F (fun _ => y)).continuous.tendsto
      (Q n)).comp (hQ n)
  have hdom : ∀ᶠ k in Filter.atTop, ∀ n : ℕ,
      ‖(((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0) (fun _ => y)‖ ≤ M * q ^ n := by
    filter_upwards [Filter.eventually_ge_atTop k0] with k hk n
    calc ‖(((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0) (fun _ => y)‖
        ≤ ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0‖ * ∏ _i : Fin n, ‖y‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0‖ * ‖y‖ ^ n := by simp
      _ ≤ M * (e1 / ρ) ^ n * ‖y‖ ^ n :=
          mul_le_mul_of_nonneg_right (hAbound k hk n) (by positivity)
      _ = M * q ^ n := by rw [hq, mul_pow]; ring
  have htend := tendsto_tsum_of_dominated_convergence hbsum hab hdom
  -- identify the sums with F_k (x0 + y)
  have hFk : ∀ k, HasSum (fun n : ℕ =>
      (((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0) (fun _ => y)) (Fk k (x0 + y)) := by
    intro k
    have hAn : ∀ z ∈ ball x0 ρ, AnalyticAt ℂ (Fk k) z := fun z hz =>
      hF k z (hballU (Metric.ball_subset_closedBall hz))
    simpa using hasSum_iteratedFDeriv hAn hyρ
  have htend2 : Filter.Tendsto (fun k => ∑' n : ℕ,
      (((n.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ n (Fk k) x0) (fun _ => y)) Filter.atTop
      (nhds (P (x0 + y))) := by
    have hmem : x0 + y ∈ t := by
      refine hballt ?_
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hyρ.le
    have := hunif.tendsto_at hmem
    refine this.congr (fun k => ?_)
    exact (hFk k).tsum_eq.symm
  have hlimeq : ∑' n : ℕ, Q n (fun _ => y) = P (x0 + y) := tendsto_nhds_unique htend htend2
  have hgbound : ∀ n : ℕ, ‖Q n (fun _ => y)‖ ≤ M * q ^ n := by
    intro n
    refine le_of_tendsto (tendsto_norm.comp (hab n)) ?_
    filter_upwards [hdom] with k hk using hk n
  have hgsum : Summable (fun n : ℕ => Q n (fun _ => y)) :=
    Summable.of_norm_bounded hbsum hgbound
  rw [← hlimeq]
  exact hgsum.hasSum

end NlsGge.Analysis.BanachHolomorphy

-- ===== part (1) =====
set_option autoImplicit false
noncomputable section
open Filter Topology Finset
open NlsGge.GK38.Lib

                                                                  
                                                                                   
                                                                  
                                                                          
                                                                                         
                                                                                 

set_option autoImplicit false
noncomputable section

open Filter Topology Finset
open NlsGge.GK38.Lib

namespace NlsGge.Atomic.G2

/-- The symmetric factor `(σ_m − λ)/π_m`, with `σ_m = mπ + s m` and `π_m = if m = 0 then 1 else mπ`. -/
def gFac (s : L2Z) (lam : ℂ) (m : ℤ) : ℂ :=
  (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) / (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))

/-- The prefactor of the `m = 0` factor when `n ≠ 0`, and `1` when `n = 0`. -/
def pref (s : L2Z) (lam : ℂ) (n : ℤ) : ℂ :=
  if n = 0 then (1 : ℂ) else gFac s lam 0

/-- The factor used at the index `k + 1` of the ℕ-indexed family, where the excluded index
`±|n|` has been replaced by its unpaired partner `gFac (−n)`. -/
def qf (s : L2Z) (lam : ℂ) (n : ℤ) (k : ℕ) : ℂ :=
  if k + 1 = n.natAbs then gFac s lam (-n)
  else gFac s lam ((k : ℤ) + 1) * gFac s lam (-((k : ℤ) + 1))

/-- The finite-N version of `qf`, valid only after the excluded index is reached. -/
def qN (s : L2Z) (lam : ℂ) (n : ℤ) (N k : ℕ) : ℂ :=
  if n.natAbs ≤ N ∧ k + 1 = n.natAbs then gFac s lam (-n)
  else gFac s lam ((k : ℤ) + 1) * gFac s lam (-((k : ℤ) + 1))

lemma gFac_eq_one_add {s : L2Z} {lam : ℂ} {j : ℤ} (hj : j ≠ 0) :
    gFac s lam j = 1 + perturbedFactor s lam j := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hj' : (j : ℂ) ≠ 0 := by exact_mod_cast hj
  unfold gFac perturbedFactor
  rw [if_neg hj]
  field_simp
  ring

lemma gFac_mul_gFac_neg {s : L2Z} {lam : ℂ} {j : ℤ} (hj : j ≠ 0) :
    gFac s lam j * gFac s lam (-j) =
      1 + (perturbedFactor s lam j + perturbedFactor s lam (-j) +
        perturbedFactor s lam j * perturbedFactor s lam (-j)) := by
  have hneg : -j ≠ 0 := neg_ne_zero.mpr hj
  rw [gFac_eq_one_add hj, gFac_eq_one_add hneg]
  ring

/-- The paired errors, indexed by `k + 1 ∈ ℕ`, are summable. -/
lemma summable_pair_nat (s : L2Z) (lam : ℂ) :
    Summable (fun k : ℕ => perturbedFactor s lam ((k : ℤ) + 1) +
      perturbedFactor s lam (-((k : ℤ) + 1)) +
      perturbedFactor s lam ((k : ℤ) + 1) * perturbedFactor s lam (-((k : ℤ) + 1))) := by
  have h : Summable (fun k : ℕ => ‖pairedFactorError s lam (Nat.succPNat k)‖) :=
    (paired_product_summable s lam).comp_injective Nat.succPNat_injective
  refine Summable.of_norm ?_
  refine h.congr (fun k => ?_)
  simp [pairedFactorError]

/-- The modified paired family minus one: the paired error plus a finitely supported term. -/
lemma qf_sub_one_eq (s : L2Z) (lam : ℂ) (n : ℤ) (k : ℕ) :
    qf s lam n k - 1 =
      (perturbedFactor s lam ((k : ℤ) + 1) +
        perturbedFactor s lam (-((k : ℤ) + 1)) +
        perturbedFactor s lam ((k : ℤ) + 1) * perturbedFactor s lam (-((k : ℤ) + 1))) +
      (if k + 1 = n.natAbs then
        gFac s lam (-n) - gFac s lam ((k : ℤ) + 1) * gFac s lam (-((k : ℤ) + 1)) else 0) := by
  have hp := gFac_mul_gFac_neg (s := s) (lam := lam) (j := (k : ℤ) + 1) (by omega)
  unfold qf
  split_ifs with h
  · linear_combination hp
  · linear_combination hp

lemma summable_qf_sub_one (s : L2Z) (lam : ℂ) (n : ℤ) :
    Summable (fun k : ℕ => qf s lam n k - 1) := by
  have hpair := summable_pair_nat s lam
  have hfin : Summable (fun k : ℕ =>
      if k + 1 = n.natAbs then
        gFac s lam (-n) - gFac s lam ((k : ℤ) + 1) * gFac s lam (-((k : ℤ) + 1))
      else 0) := by
    apply summable_of_ne_finset_zero (s := {n.natAbs - 1})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    rw [if_neg (by omega)]
  refine (hpair.add hfin).congr (fun k => ?_)
  rw [qf_sub_one_eq]

/-- The ℕ-indexed modified product converges. -/
lemma hasProd_qf (s : L2Z) (lam : ℂ) (n : ℤ) :
    HasProd (fun k : ℕ => qf s lam n k) (∏' k : ℕ, qf s lam n k) := by
  have hf : (fun k : ℕ => qf s lam n k) = (fun k : ℕ => 1 + (qf s lam n k - 1)) :=
    funext fun k => by ring
  rw [hf]
  exact (Complex.multipliable_one_add_of_summable (summable_qf_sub_one s lam n)).hasProd

/-- Recursion for the symmetric finite product: `T N = pref · ∏_{k<N} qN N k`. -/
lemma symmetric_finite_formula (s : L2Z) (lam : ℂ) (n : ℤ) (N : ℕ) :
    ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, gFac s lam m =
      pref s lam n * ∏ k ∈ range N, qN s lam n N k := by
  induction N with
  | zero =>
    by_cases hn : n = 0
    · subst hn
      simp [pref]
    · have hmem : n ∉ ({0} : Finset ℤ) := by simp [hn]
      simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.range_zero,
        Finset.prod_empty, mul_one]
      rw [Finset.erase_eq_of_notMem hmem, Finset.prod_singleton]
      simp [pref, hn]
  | succ N ih =>
    have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
    rw [hcast, Finset.prod_range_succ]
    have hR : ∏ k ∈ range N, qN s lam n (N + 1) k = ∏ k ∈ range N, qN s lam n N k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      unfold qN
      have hiff : (n.natAbs ≤ N + 1 ∧ k + 1 = n.natAbs) ↔ (n.natAbs ≤ N ∧ k + 1 = n.natAbs) := by
        constructor
        · rintro ⟨_, h2⟩
          exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      simp only [hiff]
    rw [hR]
    have hpos : ((N : ℤ) + 1).natAbs = N + 1 := by
      rw [← Nat.cast_succ]
      exact Int.natAbs_natCast _
    by_cases h1 : n = (N : ℤ) + 1
    · have hnat : n.natAbs = N + 1 := by rw [h1, hpos]
      have hc : qN s lam n (N + 1) N = gFac s lam (-((N : ℤ) + 1)) := by
        unfold qN
        rw [if_pos ⟨hnat.le, hnat.symm⟩, h1]
      have hA : (Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)).erase n =
          insert (-((N : ℤ) + 1)) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
        ext m
        simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_Icc]
        omega
      have hB : (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        apply Finset.erase_eq_of_notMem
        simp only [Finset.mem_Icc]
        omega
      have hnot : -((N : ℤ) + 1) ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hB] at ih
      rw [hA, Finset.prod_insert hnot, hc, ih]
      ring
    · by_cases h2 : n = -((N : ℤ) + 1)
      · have hnat : n.natAbs = N + 1 := by rw [h2, Int.natAbs_neg, hpos]
        have hc : qN s lam n (N + 1) N = gFac s lam ((N : ℤ) + 1) := by
          unfold qN
          rw [if_pos ⟨hnat.le, hnat.symm⟩, h2, neg_neg]
        have hA : (Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)).erase n =
            insert ((N : ℤ) + 1) (Finset.Icc (-(N : ℤ)) (N : ℤ)) := by
          ext m
          simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_Icc]
          omega
        have hB : (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n = Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          apply Finset.erase_eq_of_notMem
          simp only [Finset.mem_Icc]
          omega
        have hnot : (N : ℤ) + 1 ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simp only [Finset.mem_Icc]
          omega
        rw [hB] at ih
        rw [hA, Finset.prod_insert hnot, hc, ih]
        ring
      · have hnat_ne : ¬ (n.natAbs ≤ N + 1 ∧ N + 1 = n.natAbs) := by
          rintro ⟨_, h⟩
          rcases Int.natAbs_eq_iff.1 h.symm with h' | h'
          · exact h1 (by omega)
          · exact h2 (by omega)
        have hc : qN s lam n (N + 1) N =
            gFac s lam ((N : ℤ) + 1) * gFac s lam (-((N : ℤ) + 1)) := by
          unfold qN
          rw [if_neg hnat_ne]
        have hA : (Finset.Icc (-((N : ℤ) + 1)) ((N : ℤ) + 1)).erase n =
            insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1))
              ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n)) := by
          ext m
          simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_Icc]
          omega
        have hn1 : (N : ℤ) + 1 ∉ insert (-((N : ℤ) + 1))
            ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n) := by
          simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_Icc]
          omega
        have hn2 : -((N : ℤ) + 1) ∉ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n := by
          simp only [Finset.mem_erase, Finset.mem_Icc]
          omega
        rw [hA, Finset.prod_insert hn1, Finset.prod_insert hn2, hc, ih]
        ring

/-- The symmetric partial products converge for every `s`, `λ` and `n`. -/
theorem symmetric_partial_products_tendsto (s : L2Z) (lam : ℂ) (n : ℤ) :
    ∃ P : ℂ, Tendsto (fun N : ℕ =>
      (1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) *
        ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
            (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)))
      atTop (𝓝 P) := by
  refine ⟨(1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) *
    (pref s lam n * ∏' k : ℕ, qf s lam n k), ?_⟩
  have hlim := (hasProd_qf s lam n).tendsto_prod_nat
  refine Tendsto.congr' (Filter.eventually_atTop.2 ⟨n.natAbs, fun N hN => ?_⟩)
    (tendsto_const_nhds.mul (tendsto_const_nhds.mul hlim))
  dsimp only
  have hprod : ∏ k ∈ range N, qN s lam n N k = ∏ k ∈ range N, qf s lam n k := by
    apply Finset.prod_congr rfl
    intro k hk
    unfold qN qf
    have hiff : (n.natAbs ≤ N ∧ k + 1 = n.natAbs) ↔ (k + 1 = n.natAbs) :=
      ⟨fun h => h.2, fun h => ⟨hN, h⟩⟩
    simp only [hiff]
  have hsym : ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)) =
      pref s lam n * ∏ k ∈ range N, qN s lam n N k :=
    symmetric_finite_formula s lam n N
  rw [hsym, hprod]

-- ===== part (2) =====
open Metric Set

                                                                  

                                                                                                  
                                                                                            
                                                                                        
                                                                                               
                                                  

/-- The finite partial products of the symmetric product, as functions of `(λ, s)`. -/
def Fp (n : ℤ) (N : ℕ) (p : ℂ × L2Z) : ℂ :=
  (1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) *
    ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      (((m : ℂ) * (Real.pi : ℂ) + p.2 m) - p.1) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))

lemma Fp_eq_gFac (n : ℤ) (N : ℕ) (p : ℂ × L2Z) :
    Fp n N p = (1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) *
      ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, gFac p.2 p.1 m := rfl

lemma norm_apply_le_L2Z (s : L2Z) (m : ℤ) : ‖s m‖ ≤ ‖s‖ :=
  lp.norm_apply_le_norm (by norm_num) s m

lemma analyticAt_coord (m : ℤ) (q : ℂ × L2Z) :
    AnalyticAt ℂ (fun p : ℂ × L2Z => p.2 m) q := by
  have h := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).analyticAt q.2
  exact h.comp analyticAt_snd

lemma analyticAt_gFac_fun (m : ℤ) (q : ℂ × L2Z) :
    AnalyticAt ℂ (fun p : ℂ × L2Z =>
      (((m : ℂ) * (Real.pi : ℂ) + p.2 m) - p.1) /
        (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ))) q := by
  refine AnalyticAt.div ?_ analyticAt_const ?_
  · exact (analyticAt_const.add (analyticAt_coord m q)).sub analyticAt_fst
  · split_ifs with h
    · exact one_ne_zero
    · exact mul_ne_zero (by exact_mod_cast h) (by exact_mod_cast Real.pi_ne_zero)

lemma analyticAt_Fp (n : ℤ) (N : ℕ) (q : ℂ × L2Z) : AnalyticAt ℂ (Fp n N) q := by
  have hfun : Fp n N = fun p : ℂ × L2Z => (1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) *
      ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        (((m : ℂ) * (Real.pi : ℂ) + p.2 m) - p.1) /
          (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)) := rfl
  rw [hfun]
  refine analyticAt_const.mul ?_
  exact Finset.analyticAt_fun_prod _ (fun m _ => analyticAt_gFac_fun m q)

lemma norm_gFac_le {s : L2Z} {lam : ℂ} {R : ℝ} (hR : 0 ≤ R) (hs : ‖s‖ ≤ R) (hl : ‖lam‖ ≤ R)
    (j : ℤ) : ‖gFac s lam j‖ ≤ 1 + 4 * R := by
  have hsj : ‖s j‖ ≤ R := (norm_apply_le_L2Z s j).trans hs
  unfold gFac
  split_ifs with hj
  · subst hj
    simp only [Int.cast_zero, zero_mul, zero_add, div_one]
    have := norm_sub_le (s 0) lam
    linarith
  · have hd1 : (1 : ℝ) ≤ ‖(j : ℂ) * (Real.pi : ℂ)‖ := by
      have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
        exact_mod_cast this
      rw [norm_mul, Complex.norm_intCast, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      nlinarith [Real.pi_gt_three]
    have hnum : ‖((j : ℂ) * (Real.pi : ℂ) + s j) - lam‖ ≤
        ‖(j : ℂ) * (Real.pi : ℂ)‖ + 2 * R := by
      have h1 := norm_sub_le ((j : ℂ) * (Real.pi : ℂ) + s j) lam
      have h2 := norm_add_le ((j : ℂ) * (Real.pi : ℂ)) (s j)
      linarith
    rw [norm_div]
    have hpos : 0 < ‖(j : ℂ) * (Real.pi : ℂ)‖ := by linarith
    rw [div_le_iff₀ hpos]
    nlinarith

/-- Telescoping bound on a finite product of `1 + a`. -/
lemma norm_prod_one_add_le' (F : Finset ℕ) (a : ℕ → ℂ) :
    ‖∏ k ∈ F, (1 + a k)‖ ≤ ∏ k ∈ F, (1 + ‖a k‖) := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert j F hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, norm_mul]
    have h1 : ‖1 + a j‖ ≤ 1 + ‖a j‖ := by
      have := norm_add_le (1 : ℂ) (a j)
      simpa using this
    exact (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ih (by positivity))

lemma norm_prod_one_add_sub_one_le' (F : Finset ℕ) (a : ℕ → ℂ) :
    ‖∏ k ∈ F, (1 + a k) - 1‖ ≤ ∏ k ∈ F, (1 + ‖a k‖) - 1 := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert j F hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    have hP := norm_prod_one_add_le' F a
    have e : (1 + a j) * (∏ k ∈ F, (1 + a k)) - 1 =
        (∏ k ∈ F, (1 + a k) - 1) + a j * ∏ k ∈ F, (1 + a k) := by ring
    rw [e]
    calc ‖(∏ k ∈ F, (1 + a k) - 1) + a j * ∏ k ∈ F, (1 + a k)‖
        ≤ ‖∏ k ∈ F, (1 + a k) - 1‖ + ‖a j * ∏ k ∈ F, (1 + a k)‖ := norm_add_le _ _
      _ = ‖∏ k ∈ F, (1 + a k) - 1‖ + ‖a j‖ * ‖∏ k ∈ F, (1 + a k)‖ := by rw [norm_mul]
      _ ≤ (∏ k ∈ F, (1 + ‖a k‖) - 1) + ‖a j‖ * ∏ k ∈ F, (1 + ‖a k‖) := by
          apply add_le_add ih
          exact mul_le_mul_of_nonneg_left hP (norm_nonneg _)
      _ = (1 + ‖a j‖) * (∏ k ∈ F, (1 + ‖a k‖)) - 1 := by ring

lemma prod_one_add_norm_le_exp' (F : Finset ℕ) (a : ℕ → ℂ) :
    ∏ k ∈ F, (1 + ‖a k‖) ≤ Real.exp (∑ k ∈ F, ‖a k‖) := by
  rw [Real.exp_sum]
  gcongr with k hk
  have := Real.add_one_le_exp (‖a k‖)
  linarith

lemma norm_prod_sub_one_le_of_sum (F : Finset ℕ) (a : ℕ → ℂ) (δ : ℝ)
    (hδ : ∑ k ∈ F, ‖a k‖ ≤ δ) :
    ‖∏ k ∈ F, (1 + a k) - 1‖ ≤ Real.exp δ - 1 := by
  have h1 := norm_prod_one_add_sub_one_le' F a
  have h2 := prod_one_add_norm_le_exp' F a
  have h3 : Real.exp (∑ k ∈ F, ‖a k‖) ≤ Real.exp δ := Real.exp_le_exp.2 hδ
  linarith

/-- A finite tail of the ℕ-indexed paired errors is bounded by the ℕ+-indexed tail (G2-005). -/
lemma sum_Ico_pair_le_tsum (s : L2Z) (lam : ℂ) (N n' m' : ℕ) (hN : N ≤ n') :
    ∑ k ∈ Finset.Ico n' m', ‖pairedFactorError s lam (Nat.succPNat k)‖ ≤
      ∑' m : ℕ+, if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0 := by
  have hsum : Summable (fun m : ℕ+ => ‖pairedFactorError s lam m‖) := paired_product_summable s lam
  have hf : Summable (fun m : ℕ+ => if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0) :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> positivity)
      (fun m => by split_ifs <;> simp [norm_nonneg]) hsum
  have hinj : Function.Injective (Nat.succPNat) := Nat.succPNat_injective
  have hpt : ∀ k ∈ Finset.Ico n' m',
      ‖pairedFactorError s lam (Nat.succPNat k)‖ =
        (fun m : ℕ+ => if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0)
          (Nat.succPNat k) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hlt : N < ((Nat.succPNat k : ℕ+) : ℕ) := by
      rw [Nat.succPNat_coe]
      omega
    simp only [if_pos hlt]
  rw [Finset.sum_congr rfl hpt]
  rw [← Finset.sum_image (f := fun m : ℕ+ => if N < (m : ℕ) then ‖pairedFactorError s lam m‖ else 0)
    (fun x _ y _ h => hinj h)]
  exact Summable.sum_le_tsum _ (fun m _ => by split_ifs <;> positivity) hf

/-- The abstract uniform limit on a set `B` of partial products with uniformly small tails. -/
lemma tendstoUniformlyOn_of_prod_tails {α : Type*} (B : Set α) (F : ℕ → α → ℂ) (P : α → ℂ)
    (N1 : ℕ) (c : α → ℂ) (a : ℕ → α → ℂ)
    (hF : ∀ N, N1 ≤ N → ∀ p ∈ B, F N p = c p * ∏ k ∈ Finset.range N, (1 + a k p))
    (hc : ∃ C : ℝ, ∀ p ∈ B, ‖c p‖ ≤ C)
    (hfin : ∀ M : ℕ, ∃ D0 : ℝ, ∀ p ∈ B, ∑ k ∈ Finset.range M, ‖a k p‖ ≤ D0)
    (htail : ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, N1 ≤ M ∧ ∀ n m : ℕ, M ≤ n → n ≤ m → ∀ p ∈ B,
        ∑ k ∈ Finset.Ico n m, ‖a k p‖ ≤ δ)
    (hlim : ∀ p ∈ B, Tendsto (fun N => F N p) atTop (𝓝 (P p))) :
    TendstoUniformlyOn F P atTop B := by
  obtain ⟨C0, hC0⟩ := hc
  set C : ℝ := max C0 0 with hCdef
  have hC : ∀ p ∈ B, ‖c p‖ ≤ C := fun p hp => (hC0 p hp).trans (le_max_left _ _)
  have hC_nn : 0 ≤ C := le_max_right _ _
  obtain ⟨M1, hM1N, hM1⟩ := htail 1 one_pos
  obtain ⟨D0, hD0⟩ := hfin M1
  set D : ℝ := D0 + 1 with hD
  have hhead : ∀ n, M1 ≤ n → ∀ p ∈ B, ∑ k ∈ Finset.range n, ‖a k p‖ ≤ D := by
    intro n hn p hp
    have hs : ∑ k ∈ Finset.range n, ‖a k p‖ =
        ∑ k ∈ Finset.range M1, ‖a k p‖ + ∑ k ∈ Finset.Ico M1 n, ‖a k p‖ :=
      (Finset.sum_range_add_sum_Ico _ hn).symm
    have h1 := hD0 p hp
    have h2 := hM1 M1 n le_rfl hn p hp
    rw [hs, hD]
    linarith
  -- the Cauchy estimate for `F m − F n` with `N ≤ n ≤ m`
  have hbound : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ∈ B, ∀ n' m' : ℕ, N ≤ n' → n' ≤ m' →
      ‖F m' p - F n' p‖ < ε := by
    intro ε hε
    set K0 : ℝ := C * Real.exp D with hK0
    have hK0_nn : 0 ≤ K0 := mul_nonneg hC_nn (Real.exp_pos _).le
    set δ : ℝ := min 1 (ε / (2 * (K0 + 1))) with hδdef
    have hδpos : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ ε / (2 * (K0 + 1)) := min_le_right _ _
    obtain ⟨Mδ, hMδN, hMδ⟩ := htail δ hδpos
    refine ⟨max M1 Mδ, fun p hp n' m' hn' hnm' => ?_⟩
    have hn'1 : M1 ≤ n' := le_trans (le_max_left _ _) hn'
    have hn'2 : Mδ ≤ n' := le_trans (le_max_right _ _) hn'
    have hN1n' : N1 ≤ n' := le_trans hM1N hn'1
    have hN1m' : N1 ≤ m' := le_trans hN1n' hnm'
    have hpr := Finset.prod_range_mul_prod_Ico (fun k => 1 + a k p) hnm'
    have hdiff : F m' p - F n' p =
        (c p * ∏ k ∈ Finset.range n', (1 + a k p)) *
          (∏ k ∈ Finset.Ico n' m', (1 + a k p) - 1) := by
      rw [hF m' hN1m' p hp, hF n' hN1n' p hp, ← hpr]
      ring
    have hhn : ‖∏ k ∈ Finset.range n', (1 + a k p)‖ ≤ Real.exp D :=
      (norm_prod_one_add_le' (Finset.range n') (fun k => a k p)).trans
        ((prod_one_add_norm_le_exp' (Finset.range n') (fun k => a k p)).trans
          (Real.exp_le_exp.2 (hhead n' hn'1 p hp)))
    have hIco : ‖∏ k ∈ Finset.Ico n' m', (1 + a k p) - 1‖ ≤ Real.exp δ - 1 :=
      norm_prod_sub_one_le_of_sum (Finset.Ico n' m') (fun k => a k p) δ (hMδ n' m' hn'2 hnm' p hp)
    have hexp : Real.exp δ - 1 ≤ 2 * δ := by
      have h := Real.abs_exp_sub_one_le (x := δ) (by rw [abs_of_pos hδpos]; exact hδ1)
      rw [abs_of_pos hδpos] at h
      linarith [le_abs_self (Real.exp δ - 1)]
    have hA : ‖c p‖ * ‖∏ k ∈ Finset.range n', (1 + a k p)‖ ≤ C * Real.exp D :=
      (mul_le_mul_of_nonneg_right (hC p hp) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hhn hC_nn)
    have hB : ‖c p * ∏ k ∈ Finset.range n', (1 + a k p)‖ *
        ‖∏ k ∈ Finset.Ico n' m', (1 + a k p) - 1‖ ≤ (C * Real.exp D) * (Real.exp δ - 1) := by
      have hX : ‖c p * ∏ k ∈ Finset.range n', (1 + a k p)‖ ≤ C * Real.exp D := by
        rw [norm_mul]
        exact hA
      exact (mul_le_mul_of_nonneg_right hX (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hIco (mul_nonneg hC_nn (Real.exp_pos _).le))
    have hC2 : (C * Real.exp D) * (Real.exp δ - 1) ≤ K0 * (2 * δ) :=
      mul_le_mul_of_nonneg_left hexp hK0_nn
    have hd : 2 * δ * (K0 + 1) ≤ ε := by
      rw [le_div_iff₀ (by positivity)] at hδ2
      nlinarith
    rw [hdiff, norm_mul]
    have hfinal : K0 * (2 * δ) < ε := by nlinarith [hδpos]
    linarith
  -- uniform Cauchy from the bound, then uniform convergence from pointwise convergence
  refine UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto ?_ (fun p hp => hlim p hp)
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := hbound ε hε
  refine ⟨N, fun m hm n hn p hp => ?_⟩
  rcases le_total n m with h | h
  · rw [dist_eq_norm]
    exact hN p hp n m (le_trans (le_refl _) hn) h
  · rw [dist_comm, dist_eq_norm]
    exact hN p hp m n (le_trans (le_refl _) hm) h

/-- The head bound for the `k`-th factor, uniformly on the closed ball of radius `R`. -/
lemma norm_qf_sub_one_le (n : ℤ) (R : ℝ) (hR : 0 ≤ R) {s : L2Z} {lam : ℂ}
    (hs : ‖s‖ ≤ R) (hl : ‖lam‖ ≤ R) (k : ℕ) :
    ‖qf s lam n k - 1‖ ≤ (1 + 4 * R) * (1 + 4 * R) + (1 + 4 * R) + 1 := by
  have h1 : ‖qf s lam n k‖ ≤ (1 + 4 * R) * (1 + 4 * R) + (1 + 4 * R) := by
    unfold qf
    split_ifs with hk
    · have := norm_gFac_le hR hs hl (-n)
      nlinarith
    · have ha := norm_gFac_le hR hs hl ((k : ℤ) + 1)
      have hb := norm_gFac_le hR hs hl (-((k : ℤ) + 1))
      rw [norm_mul]
      have h0 : (0 : ℝ) ≤ 1 + 4 * R := by linarith
      nlinarith [norm_nonneg (gFac s lam ((k : ℤ) + 1)), norm_nonneg (gFac s lam (-((k : ℤ) + 1)))]
  have h2 := norm_sub_le (qf s lam n k) 1
  rw [norm_one] at h2
  linarith

/-- The factors of the symmetric product, shifted by one, on the closed ball of radius `R`. -/
lemma g2006_unif_on_closedBall (n : ℤ) (R : ℝ) (hR : 0 ≤ R) (P : ℂ × L2Z → ℂ)
    (hP : ∀ p : ℂ × L2Z, Tendsto (fun N => Fp n N p) atTop (𝓝 (P p))) :
    TendstoUniformlyOn (fun N p => Fp n N p) P atTop (closedBall (0 : ℂ × L2Z) R) := by
  have hpB : ∀ p ∈ closedBall (0 : ℂ × L2Z) R, ‖p.2‖ ≤ R ∧ ‖p.1‖ ≤ R := by
    intro p hp
    rw [mem_closedBall_zero_iff] at hp
    exact ⟨(norm_snd_le p).trans hp, (norm_fst_le p).trans hp⟩
  apply tendstoUniformlyOn_of_prod_tails (closedBall (0 : ℂ × L2Z) R) (fun N p => Fp n N p) P
    n.natAbs
    (fun p => (1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) * pref p.2 p.1 n)
    (fun k p => qf p.2 p.1 n k - 1)
  · -- the finite-product identity for `N ≥ |n|`
    intro N hN p hp
    have hk : ∀ k ∈ Finset.range N, (1 + (qf p.2 p.1 n k - 1)) = qf p.2 p.1 n k := fun k _ => by ring
    rw [Fp_eq_gFac, symmetric_finite_formula p.2 p.1 n N]
    have hprod : ∏ k ∈ Finset.range N, qN p.2 p.1 n N k = ∏ k ∈ Finset.range N, qf p.2 p.1 n k := by
      apply Finset.prod_congr rfl
      intro k hk'
      unfold qN qf
      have hiff : (n.natAbs ≤ N ∧ k + 1 = n.natAbs) ↔ (k + 1 = n.natAbs) :=
        ⟨fun h => h.2, fun h => ⟨hN, h⟩⟩
      simp only [hiff]
    rw [hprod, Finset.prod_congr rfl hk]
    unfold pref
    ring
  · -- the prefactor is bounded on bounded sets
    refine ⟨‖(1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ)))‖ * (1 + 4 * R), fun p hp => ?_⟩
    obtain ⟨hs, hl⟩ := hpB p hp
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold pref
    split_ifs with h0
    · simp only [norm_one]
      linarith
    · exact norm_gFac_le hR hs hl 0
  · -- uniform bound on the first `M` factors
    intro M
    refine ⟨(M : ℝ) * ((1 + 4 * R) * (1 + 4 * R) + (1 + 4 * R) + 1), fun p hp => ?_⟩
    obtain ⟨hs, hl⟩ := hpB p hp
    calc ∑ k ∈ Finset.range M, ‖qf p.2 p.1 n k - 1‖
        ≤ ∑ k ∈ Finset.range M, ((1 + 4 * R) * (1 + 4 * R) + (1 + 4 * R) + 1) :=
          Finset.sum_le_sum (fun k _ => norm_qf_sub_one_le n R hR hs hl k)
      _ = (M : ℝ) * ((1 + 4 * R) * (1 + 4 * R) + (1 + 4 * R) + 1) := by
          simp [Finset.sum_const, Finset.card_range]
          ring
  · -- uniform tails, from G2-005
    intro δ hδ
    obtain ⟨N, hN⟩ := paired_product_locally_uniform R hR δ hδ
    refine ⟨max n.natAbs N, le_max_left _ _, fun n' m' hn' hnm' p hp => ?_⟩
    obtain ⟨hs, hl⟩ := hpB p hp
    have hn'1 : n.natAbs ≤ n' := le_trans (le_max_left _ _) hn'
    have hn'2 : N ≤ n' := le_trans (le_max_right _ _) hn'
    have hpt : ∀ k ∈ Finset.Ico n' m',
        ‖qf p.2 p.1 n k - 1‖ = ‖pairedFactorError p.2 p.1 (Nat.succPNat k)‖ := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [qf_sub_one_eq, if_neg (by omega), add_zero]
      congr 1
    rw [Finset.sum_congr rfl hpt]
    exact (sum_Ico_pair_le_tsum p.2 p.1 N n' m' hn'2).trans (hN p.2 p.1 hs hl).le
  · intro p _
    exact hP p

/-- G2-006 part (2): the limit of the symmetric partial products is analytic on `ℂ × L2Z`. -/
theorem g2006_part2 (n : ℤ) : ∃ P : ℂ × L2Z → ℂ,
    (∀ p : ℂ × L2Z, Tendsto (fun N => Fp n N p) atTop (𝓝 (P p))) ∧
      AnalyticOnNhd ℂ P Set.univ := by
  choose P hP using fun p : ℂ × L2Z => symmetric_partial_products_tendsto p.2 p.1 n
  have hPp : ∀ p : ℂ × L2Z, Tendsto (fun N => Fp n N p) atTop (𝓝 (P p)) := fun p => hP p
  refine ⟨P, hPp, ?_⟩
  apply NlsGge.Analysis.BanachHolomorphy.analyticOnNhd_of_tendstoUniformlyOn_nhds isOpen_univ
    (Fk := fun N => Fp n N) (fun k x _ => analyticAt_Fp n k x)
  intro x _
  refine ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩
  have hsub : ball x 1 ⊆ closedBall (0 : ℂ × L2Z) (‖x‖ + 1) := by
    intro p hp
    rw [mem_closedBall_zero_iff]
    have h1 := norm_sub_norm_le p x
    rw [mem_ball, dist_eq_norm] at hp
    linarith
  exact (g2006_unif_on_closedBall n (‖x‖ + 1) (by positivity) P hPp).mono hsub


end NlsGge.Atomic.G2


end

section

                                                                                                  
-- Claim: for a finite product of linear factors (a i - λ)/c i with c i ≠ 0, the analytic order at λ0
-- equals the number of factors vanishing at λ0. This is the finite case of part (3); the infinite
-- symmetric product needs the paired summability (G2-005) and the nonvanishing of the reduced limit
-- (Mathlib tprod_one_add_ne_zero_of_summable), which are NOT in this file.

set_option autoImplicit false

open Filter Topology Set

namespace NlsGge.Atomic.G2006Part3

lemma analyticOrderAt_factor (a c lam0 : ℂ) (hc : c ≠ 0) :
    analyticOrderAt (fun lam : ℂ => (a - lam) / c) lam0 =
      (if a = lam0 then (1 : ℕ∞) else 0) := by
  have hfa : AnalyticAt ℂ (fun lam : ℂ => (a - lam) / c) lam0 := by fun_prop
  split_ifs with h
  · subst h
    refine (hfa.analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun _ => -c⁻¹, analyticAt_const,
      by simp [hc], Eventually.of_forall fun z => ?_⟩
    simp only [pow_one, smul_eq_mul]
    field_simp
    ring
  · refine (hfa.analyticOrderAt_eq_zero).2 ?_
    simp only [div_ne_zero_iff, sub_ne_zero]
    exact ⟨h, hc⟩

lemma analyticOrderAt_finset_prod {ι : Type*} [DecidableEq ι] (a c : ι → ℂ)
    (hc : ∀ i, c i ≠ 0) (lam0 : ℂ) (S : Finset ι) :
    analyticOrderAt (fun lam : ℂ => ∏ i ∈ S, (a i - lam) / c i) lam0 =
      ((S.filter (fun i => a i = lam0)).card : ℕ∞) := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.filter_empty, Finset.card_empty, Nat.cast_zero]
    exact (analyticAt_const.analyticOrderAt_eq_zero).2 one_ne_zero
  | insert i S hi ih =>
    have hfun : (fun lam : ℂ => ∏ j ∈ insert i S, (a j - lam) / c j) =
        (fun lam : ℂ => (a i - lam) / c i) * (fun lam : ℂ => ∏ j ∈ S, (a j - lam) / c j) := by
      funext lam
      simp [Finset.prod_insert hi]
    have hA : AnalyticAt ℂ (fun lam : ℂ => (a i - lam) / c i) lam0 := by fun_prop
    have hB : AnalyticAt ℂ (fun lam : ℂ => ∏ j ∈ S, (a j - lam) / c j) lam0 := by fun_prop
    rw [hfun, analyticOrderAt_mul hA hB, analyticOrderAt_factor _ _ _ (hc i), ih]
    rw [Finset.filter_insert]
    by_cases h1 : a i = lam0
    · rw [if_pos h1, if_pos h1, Finset.card_insert_of_notMem (by simp [hi])]
      push_cast
      ring
    · rw [if_neg h1, if_neg h1]
      simp

end NlsGge.Atomic.G2006Part3


end

section
                                                                                                   
                                                                                                
                                                

set_option autoImplicit false

open Filter Topology Finset Metric Set NlsGge.GK38.Lib

namespace NlsGge.Atomic.G2

noncomputable section

/-- The paired error at the label `j + 1`, as a function of `(λ, s)`. -/
def eN (s : L2Z) (lam : ℂ) (j : ℕ) : ℂ :=
  perturbedFactor s lam ((j : ℤ) + 1) + perturbedFactor s lam (-((j : ℤ) + 1)) +
    perturbedFactor s lam ((j : ℤ) + 1) * perturbedFactor s lam (-((j : ℤ) + 1))

lemma gFac_mul_eq (s : L2Z) (lam : ℂ) (j : ℕ) :
    gFac s lam ((j : ℤ) + 1) * gFac s lam (-((j : ℤ) + 1)) = 1 + eN s lam j := by
  have h := gFac_mul_gFac_neg (s := s) (lam := lam) (j := (j : ℤ) + 1) (by omega)
  rw [h]
  rfl

lemma summable_norm_eN (s : L2Z) (lam : ℂ) : Summable (fun k : ℕ => ‖eN s lam k‖) := by
  have h : Summable (fun k : ℕ => ‖pairedFactorError s lam (Nat.succPNat k)‖) :=
    (paired_product_summable s lam).comp_injective Nat.succPNat_injective
  refine h.congr (fun k => ?_)
  simp [pairedFactorError, eN]

/-- The `λ`-dependence of the paired error is explicit and quadratic. -/
lemma eN_sub_eN_zero (s : L2Z) (lam : ℂ) (j : ℕ) :
    eN s lam j - eN s 0 j =
      (lam * (s ((j : ℤ) + 1) + s (-((j : ℤ) + 1))) - lam ^ 2) /
        ((((j : ℂ) + 1) * (Real.pi : ℂ)) ^ 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero j)
  unfold eN perturbedFactor
  push_cast
  field_simp
  ring

lemma norm_eN_le (s : L2Z) {lam : ℂ} {R : ℝ} (hl : ‖lam‖ ≤ R) (j : ℕ) :
    ‖eN s lam j‖ ≤ ‖eN s 0 j‖ +
      (2 * R * ‖s‖ + R ^ 2) / (((j : ℝ) + 1) ^ 2 * Real.pi ^ 2) := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hl
  have hd : eN s lam j = eN s 0 j + (eN s lam j - eN s 0 j) := by ring
  rw [hd]
  refine (norm_add_le _ _).trans ?_
  rw [← sub_add_cancel (eN s lam j) (eN s 0 j)] at hd
  refine add_le_add (by simp) ?_
  rw [eN_sub_eN_zero, norm_div, norm_pow, norm_mul]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : (0 : ℝ) < ((j : ℝ) + 1) := by positivity
  have hden : ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 := by
    rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hpos.le]
  rw [hden, Complex.norm_real, Real.norm_of_nonneg hπ.le, mul_pow]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have h1 : ‖s ((j : ℤ) + 1)‖ ≤ ‖s‖ := norm_apply_le_L2Z s _
  have h2 : ‖s (-((j : ℤ) + 1))‖ ≤ ‖s‖ := norm_apply_le_L2Z s _
  calc ‖lam * (s ((j : ℤ) + 1) + s (-((j : ℤ) + 1))) - lam ^ 2‖
      ≤ ‖lam * (s ((j : ℤ) + 1) + s (-((j : ℤ) + 1)))‖ + ‖lam ^ 2‖ := norm_sub_le _ _
    _ ≤ R * (‖s‖ + ‖s‖) + R ^ 2 := by
        rw [norm_mul, norm_pow]
        refine add_le_add (mul_le_mul hl ?_ (norm_nonneg _) hR) (pow_le_pow_left₀ (norm_nonneg _) hl 2)
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = 2 * R * ‖s‖ + R ^ 2 := by ring


lemma continuous_eN (s : L2Z) (j : ℕ) : Continuous (fun lam : ℂ => eN s lam j) := by
  unfold eN perturbedFactor
  fun_prop

lemma differentiable_eN (s : L2Z) (j : ℕ) : Differentiable ℂ (fun lam : ℂ => eN s lam j) := by
  unfold eN perturbedFactor
  fun_prop

/-- The tail product of the paired factors from label `K + 1` on. -/
def tailProd (s : L2Z) (K : ℕ) (lam : ℂ) : ℂ := ∏' k : ℕ, (1 + eN s lam (K + k))

lemma summable_tail_bound (s : L2Z) (K : ℕ) (R : ℝ) :
    Summable (fun k : ℕ => ‖eN s 0 (K + k)‖ +
      (2 * R * ‖s‖ + R ^ 2) / ((((K + k : ℕ) : ℝ) + 1) ^ 2 * Real.pi ^ 2)) := by
  have hA : Summable (fun k : ℕ => ‖eN s 0 (K + k)‖) :=
    ((summable_nat_add_iff K).2 (summable_norm_eN s 0)).congr (fun k => by rw [add_comm])
  have h0 : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow.2 (by norm_num : 1 < 2)
  have h1 : Summable (fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 2)) :=
    ((summable_nat_add_iff 1).2 h0).congr (fun j => by push_cast; ring)
  have h2 : Summable (fun k : ℕ => ((2 * R * ‖s‖ + R ^ 2) / Real.pi ^ 2) *
      (1 / ((((K + k : ℕ) : ℝ) + 1) ^ 2))) :=
    (((summable_nat_add_iff K).2 h1).congr (fun k => by rw [Nat.add_comm k K])).mul_left _
  refine hA.add (h2.congr (fun k => ?_))
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  field_simp

lemma hasProdLocallyUniformlyOn_tail (s : L2Z) (K : ℕ) (lam0 : ℂ) :
    HasProdLocallyUniformlyOn (fun (k : ℕ) (lam : ℂ) => 1 + eN s lam (K + k)) (tailProd s K)
      (ball lam0 1) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact isOpen_ball ?_
  intro C hCs hCc
  set R : ℝ := ‖lam0‖ + 1 with hR
  refine (summable_tail_bound s K R).hasProdUniformlyOn_nat_one_add hCc
    (Eventually.of_forall fun k lam hlam => ?_) (fun k => (continuous_eN s _).continuousOn)
  have hl : ‖lam‖ ≤ R := by
    have := hCs hlam
    rw [mem_ball, dist_eq_norm] at this
    have h2 := norm_sub_norm_le lam lam0
    rw [hR]; linarith
  exact norm_eN_le s hl (K + k)

lemma analyticAt_tailProd (s : L2Z) (K : ℕ) (lam0 : ℂ) : AnalyticAt ℂ (tailProd s K) lam0 := by
  have hd : DifferentiableOn ℂ (tailProd s K) (ball lam0 1) :=
    (hasProdLocallyUniformlyOn_tail s K lam0).differentiableOn
      (Eventually.of_forall fun _ => by
        simpa [Finset.prod_fn] using
          DifferentiableOn.finsetProd (fun k _ => (differentiable_eN s (K + k)).const_add 1
            |>.differentiableOn)) isOpen_ball
  exact hd.analyticAt (ball_mem_nhds lam0 one_pos)


/-- Splitting of the symmetric finite product at a level `K ≥ |n|`. -/
lemma split_symmetric (s : L2Z) (lam : ℂ) (n : ℤ) (K : ℕ) (hK : n.natAbs ≤ K) (d : ℕ) :
    ∏ m ∈ (Finset.Icc (-((K + d : ℕ) : ℤ)) ((K + d : ℕ) : ℤ)).erase n, gFac s lam m =
      (∏ m ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase n, gFac s lam m) *
        ∏ k ∈ range d, (1 + eN s lam (K + k)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hcast : (((K + (d + 1) : ℕ)) : ℤ) = ((K + d : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hcast, Finset.prod_range_succ, ← mul_assoc, ← ih, ← gFac_mul_eq]
    have hnat : n.natAbs ≤ K + d := by omega
    have hA : (Finset.Icc (-(((K + d : ℕ) : ℤ) + 1)) (((K + d : ℕ) : ℤ) + 1)).erase n =
        insert (((K + d : ℕ) : ℤ) + 1) (insert (-(((K + d : ℕ) : ℤ) + 1))
          ((Finset.Icc (-((K + d : ℕ) : ℤ)) ((K + d : ℕ) : ℤ)).erase n)) := by
      ext m
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hn1 : ((K + d : ℕ) : ℤ) + 1 ∉ insert (-(((K + d : ℕ) : ℤ) + 1))
        ((Finset.Icc (-((K + d : ℕ) : ℤ)) ((K + d : ℕ) : ℤ)).erase n) := by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_Icc]
      omega
    have hn2 : -(((K + d : ℕ) : ℤ) + 1) ∉
        (Finset.Icc (-((K + d : ℕ) : ℤ)) ((K + d : ℕ) : ℤ)).erase n := by
      simp only [Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [hA, Finset.prod_insert hn1, Finset.prod_insert hn2]
    simp only [Nat.cast_add]
    ring


lemma exists_K (s : L2Z) (lam0 : ℂ) (n : ℤ) :
    ∃ K : ℕ, n.natAbs ≤ K ∧ ∀ m : ℤ, K < m.natAbs → (m : ℂ) * (Real.pi : ℂ) + s m ≠ lam0 := by
  refine ⟨max n.natAbs ⌈(‖s‖ + ‖lam0‖) / Real.pi⌉₊, le_max_left _ _, fun m hm heq => ?_⟩
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hK : (‖s‖ + ‖lam0‖) / Real.pi ≤ (max n.natAbs ⌈(‖s‖ + ‖lam0‖) / Real.pi⌉₊ : ℕ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have hm' : ((max n.natAbs ⌈(‖s‖ + ‖lam0‖) / Real.pi⌉₊ : ℕ) : ℝ) < (m.natAbs : ℝ) := by
    exact_mod_cast hm
  have hlt : ‖s‖ + ‖lam0‖ < (m.natAbs : ℝ) * Real.pi := by
    have := (div_le_iff₀ hπ).1 (hK.trans hm'.le)
    nlinarith [(div_le_iff₀ hπ).1 hK, mul_lt_mul_of_pos_right hm' hπ]
  have habs : ‖(m : ℂ) * (Real.pi : ℂ)‖ = (m.natAbs : ℝ) * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hπ.le]
    congr 1
    simp
  have h2 : (m : ℂ) * (Real.pi : ℂ) = lam0 - s m := by rw [← heq]; ring
  have h3 : ‖(m : ℂ) * (Real.pi : ℂ)‖ ≤ ‖lam0‖ + ‖s‖ := by
    rw [h2]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_apply_le_L2Z s m))
  rw [habs] at h3
  linarith

lemma gFac_ne_zero (s : L2Z) (lam0 : ℂ) {j : ℤ} (hj : j ≠ 0)
    (h : (j : ℂ) * (Real.pi : ℂ) + s j ≠ lam0) : gFac s lam0 j ≠ 0 := by
  unfold gFac
  rw [if_neg hj]
  refine div_ne_zero (sub_ne_zero.2 h) (mul_ne_zero ?_ ?_)
  · exact_mod_cast hj
  · exact_mod_cast Real.pi_ne_zero

/-- Part (3): the analytic order of the symmetric product at `lam0` is the zero count. -/
theorem order_symmetric_product (n : ℤ) (P : ℂ × L2Z → ℂ)
    (hP : ∀ p : ℂ × L2Z, Tendsto (fun N => Fp n N p) atTop (𝓝 (P p))) (s : L2Z) (lam0 : ℂ) :
    analyticOrderAt (fun lam : ℂ => P (lam, s)) lam0 =
      Set.encard {m : ℤ | m ≠ n ∧ (m : ℂ) * (Real.pi : ℂ) + s m = lam0} := by
  obtain ⟨K, hnK, hKz⟩ := exists_K s lam0 n
  set c : ℂ := 1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine one_div_ne_zero ?_
    split_ifs with h
    · exact one_ne_zero
    · exact mul_ne_zero (by exact_mod_cast h) (by exact_mod_cast Real.pi_ne_zero)
  set S : Finset ℤ := (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase n with hS
  set Zf : ℂ → ℂ := fun lam => ∏ m ∈ S, gFac s lam m with hZf
  -- identification of the limit
  have hid : ∀ lam : ℂ, P (lam, s) = c * Zf lam * tailProd s K lam := by
    intro lam
    have hmult : Multipliable (fun k : ℕ => 1 + eN s lam (K + k)) :=
      Complex.multipliable_one_add_of_summable (Summable.of_norm
        (((summable_nat_add_iff K).2 (summable_norm_eN s lam)).congr (fun k => by rw [add_comm])))
    have hT : Tendsto (fun d : ℕ => ∏ k ∈ range d, (1 + eN s lam (K + k))) atTop
        (𝓝 (tailProd s K lam)) := hmult.hasProd.tendsto_prod_nat
    have hlim : Tendsto (fun d : ℕ => Fp n (K + d) (lam, s)) atTop (𝓝 (P (lam, s))) :=
      (hP (lam, s)).comp (tendsto_atTop_mono (fun d : ℕ => Nat.le_add_left d K) tendsto_id)
    have hlim2 : Tendsto (fun d : ℕ => Fp n (K + d) (lam, s)) atTop
        (𝓝 (c * (Zf lam * tailProd s K lam))) := by
      have := (tendsto_const_nhds (x := c)).mul ((tendsto_const_nhds (x := Zf lam)).mul hT)
      refine this.congr (fun d => ?_)
      rw [Fp_eq_gFac, split_symmetric s lam n K hnK d]
    rw [tendsto_nhds_unique hlim hlim2]
    ring
  have hfun : (fun lam : ℂ => P (lam, s)) = fun lam => c * Zf lam * tailProd s K lam :=
    funext hid
  -- order of the tail product is zero
  have hT0 : tailProd s K lam0 ≠ 0 := by
    refine tprod_one_add_ne_zero_of_summable (f := fun k : ℕ => eN s lam0 (K + k)) ?_ ?_
    · intro k
      rw [← gFac_mul_eq]
      refine mul_ne_zero ?_ ?_
      · refine gFac_ne_zero s lam0 (by omega) (hKz _ ?_)
        omega
      · refine gFac_ne_zero s lam0 (by omega) (hKz _ ?_)
        omega
    · exact ((summable_nat_add_iff K).2 (summable_norm_eN s lam0)).congr
        (fun k => by rw [add_comm])
  have hordT : analyticOrderAt (tailProd s K) lam0 = 0 :=
    ((analyticAt_tailProd s K lam0).analyticOrderAt_eq_zero).2 hT0
  have hZ : AnalyticAt ℂ Zf lam0 := by
    refine Finset.analyticAt_fun_prod _ (fun m _ => ?_)
    unfold gFac
    refine AnalyticAt.div (by fun_prop) analyticAt_const ?_
    split_ifs with h
    · exact one_ne_zero
    · exact mul_ne_zero (by exact_mod_cast h) (by exact_mod_cast Real.pi_ne_zero)
  have hcZ : AnalyticAt ℂ (fun lam => c * Zf lam) lam0 := analyticAt_const.mul hZ
  have hordc : analyticOrderAt (fun lam : ℂ => c * Zf lam) lam0 = analyticOrderAt Zf lam0 := by
    have h1 : (fun lam : ℂ => c * Zf lam) = (fun _ : ℂ => c) * Zf := rfl
    rw [h1, analyticOrderAt_mul analyticAt_const hZ,
      (analyticAt_const.analyticOrderAt_eq_zero).2 hc0, zero_add]
  have hordZ : analyticOrderAt Zf lam0 = ((S.filter (fun m : ℤ => (m : ℂ) * (Real.pi : ℂ) + s m = lam0)).card : ℕ∞) := by
    have := NlsGge.Atomic.G2006Part3.analyticOrderAt_finset_prod (fun m : ℤ => (m : ℂ) * (Real.pi : ℂ) + s m)
      (fun m : ℤ => if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)) (by
        intro m
        split_ifs with h
        · exact one_ne_zero
        · exact mul_ne_zero (by exact_mod_cast h) (by exact_mod_cast Real.pi_ne_zero)) lam0 S
    exact this
  rw [hfun]
  have hmul : (fun lam : ℂ => c * Zf lam * tailProd s K lam) =
      (fun lam : ℂ => c * Zf lam) * tailProd s K := rfl
  rw [hmul, analyticOrderAt_mul hcZ (analyticAt_tailProd s K lam0), hordc, hordT, add_zero, hordZ]
  have hset : {m : ℤ | m ≠ n ∧ (m : ℂ) * (Real.pi : ℂ) + s m = lam0} =
      ↑(S.filter (fun m : ℤ => (m : ℂ) * (Real.pi : ℂ) + s m = lam0)) := by
    ext m
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hS, Finset.mem_erase, Finset.mem_Icc]
    constructor
    · rintro ⟨hmn, hm⟩
      refine ⟨⟨hmn, ?_, ?_⟩, hm⟩
      · by_contra hlt
        exact hKz m (by omega) hm
      · by_contra hlt
        exact hKz m (by omega) hm
    · rintro ⟨⟨hmn, _, _⟩, hm⟩
      exact ⟨hmn, hm⟩
  rw [hset, Set.encard_coe_eq_coe_finsetCard]

end

end NlsGge.Atomic.G2

end

namespace NlsGge.Atomic.G2006

set_option autoImplicit false

open Filter Topology NlsGge.GK38.Lib NlsGge.Atomic.G2

/-- G2-006, whole COMMAND02 proposition (symmetric limit product, joint analyticity, zero multiplicities). -/
theorem G2006_full :
    (∀ n : ℤ,
      ∃ P : ℂ × L2Z → ℂ,
        (∀ (s : L2Z) (lam : ℂ),
            Filter.Tendsto
              (fun N : ℕ =>
                (1 / (if n = 0 then (1 : ℂ) else (n : ℂ) * (Real.pi : ℂ))) *
                  ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
                    (((m : ℂ) * (Real.pi : ℂ) + s m) - lam) /
                      (if m = 0 then (1 : ℂ) else (m : ℂ) * (Real.pi : ℂ)))
              Filter.atTop (nhds (P (lam, s)))) ∧
        AnalyticOnNhd ℂ P Set.univ ∧
        (∀ (s : L2Z) (lam0 : ℂ),
            analyticOrderAt (fun lam : ℂ => P (lam, s)) lam0 =
              (Set.encard {m : ℤ | m ≠ n ∧ (m : ℂ) * (Real.pi : ℂ) + s m = lam0}))
      : Prop) := by
  intro n
  obtain ⟨P, hP, hA⟩ := g2006_part2 n
  exact ⟨P, fun s lam => hP (lam, s), hA, fun s lam0 => order_symmetric_product n P hP s lam0⟩

end NlsGge.Atomic.G2006
