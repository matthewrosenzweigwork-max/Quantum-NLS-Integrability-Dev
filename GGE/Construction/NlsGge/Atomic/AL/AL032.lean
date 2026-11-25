import Mathlib
import NlsGge.ThirdConsultation.AL.Basic
import NlsGge.Hierarchy.ALEnergyAnalytic38
import NlsGge.Hierarchy.ALComplexExteriorLog38
import NlsGge.Hierarchy.ALComplexMonodromy38
import NlsGge.Hierarchy.ALPoissonLiouville38
import NlsGge.Hierarchy.ALLaurent38
import NlsGge.Hierarchy.ALQuadraticPart38
import NlsGge.Hierarchy.ALPositiveDecompositions38
import NlsGge.Hierarchy.ALMomentsBridge38

                                                                                                                      
                                                                                                                                                                
                                                                                                                                                            
                                                                                                                                                           
                                                                                                                                                     
                                                                                                                                                                 
                                                                                                                                                     
                                                                                                                                                 
                                                                                                                                            
set_option autoImplicit false
open scoped BigOperators Matrix ENNReal
open Set Filter Topology MeasureTheory Metric
open NlsGge.AblowitzLadik NlsGge.HierarchyRiccati.Core NlsGge.Pilot
namespace NlsGge.ThirdConsultation.AL
noncomputable section

theorem al032_iteratedDeriv_conj (f : ℂ → ℂ) (n : ℕ) :
    iteratedDeriv n ((starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ)) =
      (starRingEnd ℂ) ∘ iteratedDeriv n f ∘ (starRingEnd ℂ) := by
  induction n generalizing f with
  | zero => ext z; simp
  | succ n ih => rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_conj_conj, ih]

theorem al032_scalar_conj {a : ℂ} (ha : ‖a‖ < 1) :
    alScalar38 (star a) a = (starRingEnd ℂ) (alScalar38 a (star a)) := by
  have hn : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hx : 1 - a * star a = (((1 - Complex.normSq a : ℝ)) : ℂ) := by
    have : a * star a = ((Complex.normSq a : ℝ) : ℂ) := Complex.mul_conj a
    rw [this]; push_cast; ring
  have hx' : 1 - star a * a = (((1 - Complex.normSq a : ℝ)) : ℂ) := by rw [mul_comm]; exact hx
  have hpos : 0 ≤ 1 - Complex.normSq a := by linarith
  have harg : (((1 - Complex.normSq a : ℝ)) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hpos]; exact Real.pi_ne_zero.symm
  unfold alScalar38
  rw [hx, hx']
  have h := Complex.conj_cpow (((1 - Complex.normSq a : ℝ)) : ℂ) (-(1 / 2 : ℂ)) harg
  have e1 : (starRingEnd ℂ) (((1 - Complex.normSq a : ℝ)) : ℂ) = (((1 - Complex.normSq a : ℝ)) : ℂ) :=
    Complex.conj_ofReal _
  have e2 : (starRingEnd ℂ) (-(1 / 2 : ℂ)) = -(1 / 2 : ℂ) := by
    rw [map_neg, map_div₀, map_one, map_ofNat]
  rw [e1, e2] at h
  exact h

theorem al032_partial_conj {L : ℕ} [NeZero L] {a : ZMod L → ℂ} (ha : IsALField38 a) (ζ : ℂ) (k : ℕ) :
    alComplexPartial38 (fun j => star (a j)) a ζ k =
      (alComplexPartial38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ) k).map (starRingEnd ℂ) := by
  induction k with
  | zero => simp [alComplexPartial38]
  | succ k ih =>
    simp only [alComplexPartial38]
    rw [Matrix.map_mul, ih]
    congr 1
    have hs : alScalar38 ((starRingEnd ℂ) (a (k : ZMod L))) (a (k : ZMod L)) =
        (starRingEnd ℂ) (alScalar38 (a (k : ZMod L)) ((starRingEnd ℂ) (a (k : ZMod L)))) :=
      al032_scalar_conj (ha (k : ZMod L))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [alTransferTilde38, hs, Matrix.smul_apply, map_mul, Complex.star_def]

theorem al032_T_conj {L : ℕ} [NeZero L] {a : ZMod L → ℂ} (ha : IsALField38 a) (ζ : ℂ) :
    alComplexT38 (fun j => star (a j)) a ζ =
      (starRingEnd ℂ) (alComplexT38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ)) := by
  unfold alComplexT38 alComplexMonodromy38
  rw [al032_partial_conj ha ζ L]
  simp [Matrix.trace_fin_two]

theorem al032_log_conj {L : ℕ} [NeZero L] {a : ZMod L → ℂ} (ha : IsALField38 a) (ζ : ℂ)
    (hD : alComplexD38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ) ∈ Complex.slitPlane)
    (hG : alComplexG38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ) ∈ Complex.slitPlane) :
    alComplexLog38 (fun j => star (a j)) a ζ =
      (starRingEnd ℂ) (alComplexLog38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ)) := by
  set D2 := alComplexD38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ) with hD2
  have hT := al032_T_conj ha ζ
  have hDc : alComplexD38 (fun j => star (a j)) a ζ = (starRingEnd ℂ) D2 := by
    unfold alComplexD38 at hD2 ⊢
    rw [hT, hD2]
    simp [map_ofNat]
  have hSc : alComplexS38 (fun j => star (a j)) a ζ =
      (starRingEnd ℂ) (alComplexS38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ)) := by
    unfold alComplexS38
    rw [hDc]
    have h := Complex.conj_cpow D2 (2⁻¹ : ℂ) (Complex.mem_slitPlane_iff_arg.1 hD).1
    have e2 : (starRingEnd ℂ) (2⁻¹ : ℂ) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
    rw [e2] at h
    exact h
  have hGc : alComplexG38 (fun j => star (a j)) a ζ =
      (starRingEnd ℂ) (alComplexG38 a (fun j => star (a j)) ((starRingEnd ℂ) ζ)) := by
    unfold alComplexG38
    rw [hT, hSc, map_div₀, map_add, map_ofNat]
  unfold alComplexLog38
  rw [hGc, Complex.log_conj _ (Complex.mem_slitPlane_iff_arg.1 hG).1]

theorem al032_Kc_bound {L : ℕ} [NeZero L] {C q : ℝ} (hC0 : 0 ≤ C) (hq : 0 ≤ q)
    {p : (ZMod L → ℂ) × (ZMod L → ℂ)} (hCk : ∀ k : ℕ, ‖alCc38 p k‖ ≤ C * q ^ k) (j : ℕ) :
    ‖alKc38 j p‖ ≤ 2 * C * (4 * max 1 q) ^ j := by
  set R' : ℝ := max 1 q with hR'
  have hR1 : 1 ≤ R' := le_max_left _ _
  have hk : ∀ k ≤ j, ‖alCc38 p k‖ ≤ C * R' ^ j := fun k hkj =>
    (hCk k).trans (mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ hq (le_max_right 1 q) k).trans (pow_le_pow_right₀ hR1 hkj)) hC0)
  have hB : (Nat.choose (2 * j) j : ℝ) + ∑ k ∈ Finset.Icc 1 j, (Nat.choose (2 * j) (j - k) : ℝ) ≤ 4 ^ j := by
    have hinj : Set.InjOn (fun k => j - k) (Finset.Icc 1 j : Set ℕ) := by
      intro x hx y hy hxy
      simp only [Finset.coe_Icc, Set.mem_Icc] at hx hy
      simp only at hxy
      omega
    have e : ∑ k ∈ Finset.Icc 1 j, (Nat.choose (2 * j) (j - k) : ℝ) =
        ∑ m ∈ (Finset.Icc 1 j).image (fun k => j - k), (Nat.choose (2 * j) m : ℝ) :=
      (Finset.sum_image (f := fun m : ℕ => (Nat.choose (2 * j) m : ℝ)) (g := fun k => j - k) hinj).symm
    have hnot : j ∉ (Finset.Icc 1 j).image (fun k => j - k) := by
      simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and]
      intro x hx1 hx2
      omega
    have e2 : (Nat.choose (2 * j) j : ℝ) + ∑ m ∈ (Finset.Icc 1 j).image (fun k => j - k), (Nat.choose (2 * j) m : ℝ) =
        ∑ m ∈ insert j ((Finset.Icc 1 j).image (fun k => j - k)), (Nat.choose (2 * j) m : ℝ) :=
      (Finset.sum_insert (f := fun m : ℕ => (Nat.choose (2 * j) m : ℝ)) hnot).symm
    rw [e, e2]
    have hsub : insert j ((Finset.Icc 1 j).image (fun k => j - k)) ⊆ Finset.range (2 * j + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_Icc, Finset.mem_range] at hx ⊢
      rcases hx with rfl | ⟨k, hk1, rfl⟩ <;> omega
    calc ∑ m ∈ insert j ((Finset.Icc 1 j).image (fun k => j - k)), (Nat.choose (2 * j) m : ℝ)
        ≤ ∑ m ∈ Finset.range (2 * j + 1), (Nat.choose (2 * j) m : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = 4 ^ j := by
          have := Nat.sum_range_choose (2 * j)
          have h2 : ((∑ m ∈ Finset.range (2 * j + 1), Nat.choose (2 * j) m : ℕ) : ℝ) = ((2 ^ (2 * j) : ℕ) : ℝ) := by
            rw [this]
          push_cast at h2
          rw [h2, pow_mul]; norm_num
  have hterm : ∀ k ∈ Finset.Icc 1 j,
      ‖(-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖ ≤
        (Nat.choose (2 * j) (j - k) : ℝ) * (C * R' ^ j) := by
    intro k hkk
    rw [Finset.mem_Icc] at hkk
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hk k hkk.2) (by positivity)
  have hsum : ‖∑ k ∈ Finset.Icc 1 j, (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖ ≤
      (∑ k ∈ Finset.Icc 1 j, (Nat.choose (2 * j) (j - k) : ℝ)) * (C * R' ^ j) := by
    rw [Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  have h0 : ‖2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0‖ ≤ 2 * ((Nat.choose (2 * j) j : ℝ) * (C * R' ^ j)) := by
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hk 0 (Nat.zero_le _)) (by positivity))
      (by norm_num)
  have hCR : 0 ≤ C * R' ^ j := by positivity
  unfold alKc38
  calc ‖2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0 +
        2 * ∑ k ∈ Finset.Icc 1 j, (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖
      ≤ ‖2 * (Nat.choose (2 * j) j : ℂ) * alCc38 p 0‖ + ‖2 * ∑ k ∈ Finset.Icc 1 j,
          (-1 : ℂ) ^ k * (Nat.choose (2 * j) (j - k) : ℂ) * alCc38 p k‖ := norm_add_le _ _
    _ ≤ 2 * ((Nat.choose (2 * j) j : ℝ) * (C * R' ^ j)) +
          2 * ((∑ k ∈ Finset.Icc 1 j, (Nat.choose (2 * j) (j - k) : ℝ)) * (C * R' ^ j)) := by
        gcongr
        rw [norm_mul]
        have h2 : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 2 * (C * R' ^ j) * ((Nat.choose (2 * j) j : ℝ) + ∑ k ∈ Finset.Icc 1 j, (Nat.choose (2 * j) (j - k) : ℝ)) := by
        ring
    _ ≤ 2 * (C * R' ^ j) * 4 ^ j := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = 2 * C * (4 * R') ^ j := by rw [mul_pow]; ring

theorem al032 {L : ℕ} [NeZero L]
    (U : Set ((ZMod L → ℂ) × (ZMod L → ℂ)))
    (hU : IsOpen U) (hswap : ∀ p ∈ U, p.swap ∈ U)
    (R C : ℝ) (hR : 1 < R) (hC : 0 ≤ C)
    (hlog : AnalyticOnNhd ℂ
      (fun q : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) =>
        alComplexLog38 q.2.1 q.2.2 q.1)
      (Metric.closedBall (0 : ℂ) R⁻¹ ×ˢ U))
    (hbound : ∀ p ∈ U, ∀ ζ ∈ Metric.closedBall (0 : ℂ) R⁻¹,
      ‖alComplexLog38 p.1 p.2 ζ‖ ≤ C) :
  (∀ p ∈ U, ∀ k : ℕ, ‖alCc38 p k‖ ≤ C*R^(2*k)) ∧
  (∀ j : ℕ, AnalyticOnNhd ℂ (fun p => complexMoment p j) U) ∧
  (∀ p ∈ U, ∀ j : ℕ,
    ‖complexMoment p j‖ ≤ 2*C*(4*max 1 (R^2))^j) ∧
  (∀ a : ZMod L → ℂ, IsALField38 a → ∀ k : ℕ,
    alCc38 (alIota38 a) k = alC38 a k ∧
    alCc38 (alIota38 a).swap k = star (alC38 a k)) ∧
  ∀ a : ZMod L → ℂ, IsALField38 a → ∀ j : ℕ,
    complexMoment (alIota38 a) j = (alK38 a j : ℂ) := by
  classical
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < R⁻¹ := inv_pos.2 hR0
  have hlogball : ∀ ζ ∈ ball (0 : ℂ) R⁻¹, ∀ p ∈ U,
      AnalyticAt ℂ (fun r : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) => alComplexLog38 r.2.1 r.2.2 r.1) (ζ, p) :=
    fun ζ hζ p hp => hlog (ζ, p) ⟨ball_subset_closedBall hζ, hp⟩
  -- Cauchy bound
  have h1 : ∀ p ∈ U, ∀ k : ℕ, ‖alCc38 p k‖ ≤ C * R ^ (2 * k) := by
    intro p hp k
    have hdiff : DiffContOnCl ℂ (alComplexLog38 p.1 p.2) (ball (0 : ℂ) R⁻¹) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ hr0.ne']
      intro t ht
      have : AnalyticAt ℂ (fun q : ℂ × ((ZMod L → ℂ) × (ZMod L → ℂ)) =>
          alComplexLog38 q.2.1 q.2.2 q.1) (t, p) := hlog (t, p) ⟨ht, hp⟩
      exact (hasDerivAt_slice38 this).differentiableAt.differentiableWithinAt
    have hsph : ∀ t ∈ sphere (0 : ℂ) R⁻¹, ‖alComplexLog38 p.1 p.2 t‖ ≤ C :=
      fun t ht => hbound p hp t (sphere_subset_closedBall ht)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (2 * k) hr0 hdiff hsph
    have hfac : (0 : ℝ) < ((Nat.factorial (2 * k) : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
    unfold alCc38
    rw [norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
    calc ‖iteratedDeriv (2 * k) (alComplexLog38 p.1 p.2) 0‖
        ≤ ((Nat.factorial (2 * k) : ℕ) : ℝ) * C / R⁻¹ ^ (2 * k) := h
      _ = C * R ^ (2 * k) * ((Nat.factorial (2 * k) : ℕ) : ℝ) := by
          rw [inv_pow]; field_simp
  have hCq : ∀ p ∈ U, ∀ k : ℕ, ‖alCc38 p k‖ ≤ C * (R ^ 2) ^ k := by
    intro p hp k
    have := h1 p hp k
    rwa [pow_mul] at this
  have h3 : ∀ p ∈ U, ∀ j : ℕ, ‖complexMoment p j‖ ≤ 2 * C * (4 * max 1 (R ^ 2)) ^ j := by
    intro p hp j
    have a1 := al032_Kc_bound hC (by positivity) (hCq p hp) j
    have a2 := al032_Kc_bound hC (by positivity) (hCq p.swap (hswap p hp)) j
    unfold complexMoment
    calc ‖(alKc38 j p + alKc38 j p.swap) / 2‖ = ‖alKc38 j p + alKc38 j p.swap‖ / 2 := by
          rw [norm_div]; simp
      _ ≤ (‖alKc38 j p‖ + ‖alKc38 j p.swap‖) / 2 := by
          gcongr; exact norm_add_le _ _
      _ ≤ 2 * C * (4 * max 1 (R ^ 2)) ^ j := by linarith
  have h2 : ∀ j : ℕ, AnalyticOnNhd ℂ (fun p => complexMoment p j) U := by
    intro j p hp
    have hK1 : AnalyticAt ℂ (alKc38 j) p := analyticAt_alKc38 hr0 hU hlogball j hp
    have hK2 : AnalyticAt ℂ (alKc38 j) p.swap := analyticAt_alKc38 hr0 hU hlogball j (hswap p hp)
    have hsw : AnalyticAt ℂ (Prod.swap : ((ZMod L → ℂ) × (ZMod L → ℂ)) → _) p :=
      analyticAt_snd.prod analyticAt_fst
    have := (hK1.add (hK2.comp hsw)).div (analyticAt_const (v := (2 : ℂ))) (by norm_num)
    exact this
  -- real-slice identities
  have hreal : ∀ a : ZMod L → ℂ, IsALField38 a →
      (∀ k : ℕ, alCc38 (alIota38 a) k = alC38 a k) ∧
      (∀ k : ℕ, alCc38 (alIota38 a).swap k = (starRingEnd ℂ) (alC38 a k)) ∧
      ((∀ k : ℕ, alCc38 (alIota38 a) k = alC38 a k) → ∀ j : ℕ,
        (alKc38 j (alIota38 a)).re = alK38 a j) := by
    intro a ha
    obtain ⟨U', ρ, hUo, hpU, hUd, hρ, hρ1, hslit, hana, hexp, hr⟩ := exists_alComplexLogNhd38 ha
    have hag := hr a ha hpU
    have hc1 : ∀ k : ℕ, alCc38 (alIota38 a) k = alC38 a k := fun k => alCc38_real hρ hag k
    refine ⟨hc1, ?_, fun _ j => ?_⟩
    · intro k
      have hev : alComplexLog38 (fun j => star (a j)) a =ᶠ[𝓝 (0 : ℂ)]
          ((starRingEnd ℂ) ∘ alComplexLog38 a (fun j => star (a j)) ∘ (starRingEnd ℂ)) := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with ζ hζ
        have hζ' : (starRingEnd ℂ) ζ ∈ ball (0 : ℂ) ρ := by
          rw [mem_ball, dist_zero_right, Complex.norm_conj]; rwa [mem_ball, dist_zero_right] at hζ
        obtain ⟨hD, hG⟩ := hslit _ hζ' _ hpU
        exact al032_log_conj ha ζ hD hG
      have hd := hev.iteratedDeriv_eq (n := 2 * k)
      have hc : iteratedDeriv (2 * k) (alComplexLog38 (fun j => star (a j)) a) 0 =
          (starRingEnd ℂ) (iteratedDeriv (2 * k) (alComplexLog38 a (fun j => star (a j))) 0) := by
        rw [hd, al032_iteratedDeriv_conj]; simp
      have e1 : alCc38 (alIota38 a).swap k =
          iteratedDeriv (2 * k) (alComplexLog38 (fun j => star (a j)) a) 0 / ((Nat.factorial (2 * k) : ℕ) : ℂ) := rfl
      have e2 : alCc38 (alIota38 a) k =
          iteratedDeriv (2 * k) (alComplexLog38 a (fun j => star (a j))) 0 / ((Nat.factorial (2 * k) : ℕ) : ℂ) := rfl
      rw [e1, hc, ← hc1 k, e2, map_div₀, map_natCast]
    · exact alKc38_re ha hρ hag j |>.trans (alMomentK38_eq_alK38 a j)
  refine ⟨h1, h2, h3, fun a ha k => ⟨(hreal a ha).1 k, ?_⟩, fun a ha j => ?_⟩
  · rw [(hreal a ha).2.1 k]; rfl
  · have hc1 := (hreal a ha).1
    have hc2 := (hreal a ha).2.1
    have hre := (hreal a ha).2.2 hc1 j
    have hconj : alKc38 j (alIota38 a).swap = (starRingEnd ℂ) (alKc38 j (alIota38 a)) := by
      unfold alKc38
      simp only [hc2, hc1, map_add, map_mul, map_sum, map_pow, map_neg, map_one, map_natCast, map_ofNat]
    unfold complexMoment
    rw [hconj]
    have := Complex.add_conj (alKc38 j (alIota38 a))
    rw [this]
    rw [← hre]
    push_cast
    ring

end
end NlsGge.ThirdConsultation.AL
