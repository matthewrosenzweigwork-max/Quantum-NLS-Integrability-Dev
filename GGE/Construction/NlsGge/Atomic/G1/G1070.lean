import NlsGge.Atomic.G1.G1044
import NlsGge.GK38.PoissonMixedTargets
import NlsGge.GK38.DirichletLabels

/-!
G1-070 (entire interpolation factor at a simple Dirichlet root), Pro third-consultation form.
Differences from the earlier packet statement, recorded per the coordinator's instruction:
* the root sequence is the house `muSeq` (NlsGge.GK38.DirichletLabels); `mu φ = muSeq φ` is
  proved below from cutoff invariance (`mu_eq_muSeq`), so the G1044 results transfer;
* the interpolation factor is the house `dirInterpolation38` (`PoissonMixedTargets`), i.e. the
  `dslope` form, so its value at the root is the derivative quotient;
* the predicate is Pro's `simpleDirichlet`;
* the symmetric product is stated as Pro's finite partial-product limit over `Icc (-N) N`, not as
  a `tprod`; the `tprod` is used only internally.
-/



namespace NlsGge.Atomic.G1070

open NlsGge.GK38 NlsGge.Pilot NlsGge.Atomic.G1044S3M NlsGge.GK38.PoissonMixed38 Filter Topology SummationFilter
open scoped Topology

def simpleDirichlet (φ : PotPair) (z : ℂ) : Prop :=
  dirichletChar φ z = 0 ∧ deriv (dirichletChar φ) z ≠ 0



open NlsGge.GK38 NlsGge.Pilot NlsGge.Atomic.G1044S3M

/-- The interpolation factor `p_n(λ) = χ_d(λ) / ((λ − μ_n) χ_d′(μ_n))`, with the removable
value `1` at `λ = μ_n` (packet definition). -/
noncomputable def interpolationFactor (φ : PotPair) (n : ℤ) (lam : ℂ) : ℂ :=
  if lam = mu φ n then 1 else
    dirichletChar φ lam / ((lam - mu φ n) * deriv (dirichletChar φ) (mu φ n))

theorem dirichlet_interpolation_values (φ : PotPair) (n : ℤ) (h : simpleDirichlet φ (mu φ n)) :
    ∀ m : ℤ, interpolationFactor φ n (mu φ m) = if m = n then 1 else 0 := by
  intro m
  by_cases hmn : m = n
  · subst hmn
    simp [interpolationFactor]
  · have hne : mu φ m ≠ mu φ n := by
      intro heq
      have hfa : AnalyticAt ℂ (dirichletChar φ) (mu φ n) :=
        analyticOnNhd_dirichletChar_z φ (mu φ n) (Set.mem_univ _)
      have hord0 := hfa.analyticOrderAt_sub_eq_one_of_deriv_ne_zero h.2
      simp only [h.1, sub_zero] at hord0
      have hcard : Set.encard {k : ℤ | mu φ k = mu φ n} = 1 := by
        rw [((mu_enum φ).2.2 (mu φ n)).2, hord0]
      obtain ⟨x, hx⟩ := Set.encard_eq_one.1 hcard
      have hm : m ∈ {k : ℤ | mu φ k = mu φ n} := heq
      have hn : n ∈ {k : ℤ | mu φ k = mu φ n} := rfl
      rw [hx] at hm hn
      exact hmn (hm.trans hn.symm)
    have hz : dirichletChar φ (mu φ m) = 0 := (mu_enum φ).1 m
    simp only [interpolationFactor, if_neg hne, hz, zero_div, if_neg hmn]


theorem interpolationFactor_eq_dslope (φ : PotPair) (n : ℤ) (h : simpleDirichlet φ (mu φ n)) :
    interpolationFactor φ n = fun lam =>
      dslope (dirichletChar φ) (mu φ n) lam / deriv (dirichletChar φ) (mu φ n) := by
  funext lam
  by_cases hl : lam = mu φ n
  · subst hl
    simp [interpolationFactor, dslope_same, div_self h.2]
  · have hlt : lam ≠ mu φ n := hl
    simp only [interpolationFactor, if_neg hl, dslope_of_ne _ hlt, slope_def_field, h.1,
      sub_zero]
    have hd : (lam - mu φ n) ≠ 0 := sub_ne_zero.mpr hl
    have hc : deriv (dirichletChar φ) (mu φ n) ≠ 0 := h.2
    field_simp

theorem interpolationFactor_differentiable (φ : PotPair) (n : ℤ) (h : simpleDirichlet φ (mu φ n)) :
    Differentiable ℂ (interpolationFactor φ n) := by
  have hdiff : DifferentiableOn ℂ (dirichletChar φ) Set.univ :=
    fun z _ => (analyticOnNhd_dirichletChar_z φ z (Set.mem_univ _)).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ (dslope (dirichletChar φ) (mu φ n)) Set.univ :=
    (Complex.differentiableOn_dslope (Filter.univ_mem)).2 hdiff
  rw [interpolationFactor_eq_dslope φ n h]
  exact (differentiableOn_univ.mp hd).div_const _


theorem πn_ne_zero' (m : ℤ) : (πn m : ℂ) ≠ 0 := by
  have h : πn m ≠ 0 := by
    unfold πn NlsGge.GK38.Lib.piN
    split_ifs with h0
    · norm_num
    · exact mul_ne_zero (by exact_mod_cast h0) Real.pi_ne_zero
  exact_mod_cast h

theorem factor_mult_of_ne (L : SummationFilter ℤ) [L.LeAtTop] [L.NeBot] (F : ℤ → ℂ) (n : ℤ)
    (hF : Multipliable F L) (hne : F n ≠ 0) :
    Multipliable (fun m : ℤ => if m = n then (1 : ℂ) else F m) L := by
  have hK : HasProd (fun m : ℤ => if m = n then (F n)⁻¹ else 1) (F n)⁻¹ L :=
    hasProd_ite_eq n (F n)⁻¹ (L := L)
  have h := hF.hasProd.mul hK
  have h2 : Multipliable (fun m : ℤ => if m = n then (1 : ℂ) else F m) L := by
    convert h.multipliable using 1
    funext m
    by_cases hm : m = n
    · subst hm
      simp [mul_inv_cancel₀ hne]
    · simp [hm]
  exact h2

theorem factor_of_mult (L : SummationFilter ℤ) [L.LeAtTop] [L.NeBot] (F : ℤ → ℂ) (n : ℤ)
    (hF : Multipliable F L)
    (hG : Multipliable (fun m : ℤ => if m = n then (1 : ℂ) else F m) L) :
    ∏'[L] m : ℤ, F m = F n * ∏'[L] m : ℤ, (if m = n then (1 : ℂ) else F m) := by
  have hK : HasProd (fun m : ℤ => if m = n then F n else 1) (F n) L :=
    hasProd_ite_eq n (F n) (L := L)
  have h := hG.hasProd.mul hK
  have h' : HasProd F ((∏'[L] m : ℤ, (if m = n then (1 : ℂ) else F m)) * F n) L := by
    convert h using 1
    funext m
    by_cases hm : m = n
    · subst hm
      simp
    · simp [hm]
  rw [h'.tprod_eq, mul_comm]

/-- The reduced product `P_n(z) = ∏'_{m≠n} (μ_m − z)/π_m`, written with the `n`-th factor `1`. -/
noncomputable def reducedProd (φ : PotPair) (n : ℤ) (z : ℂ) : ℂ :=
  ∏'[symmetricIcc ℤ] m : ℤ, (if m = n then (1 : ℂ) else (mu φ m - z) / (πn m : ℂ))

theorem update_summable (φ : PotPair) (n : ℤ) (w : ℂ) :
    Summable (fun k : ℤ => ‖Function.update (mu φ) n w k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
  have e : (fun k : ℤ => ‖Function.update (mu φ) n w k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) =
      Function.update (fun k : ℤ => ‖mu φ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) n
        (‖w - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
    funext k
    by_cases hk : k = n
    · subst hk; simp
    · simp [Function.update_of_ne hk]
  rw [e]
  exact (mu_summable φ).update n _

theorem red_mult_all (φ : PotPair) (n : ℤ) (z : ℂ) :
    Multipliable (fun m : ℤ => if m = n then (1 : ℂ) else (mu φ m - z) / (πn m : ℂ))
      (symmetricIcc ℤ) := by
  obtain ⟨hmult, -, -⟩ := NlsGge.GK38.Lib.product_entire _ (update_summable φ n (z + 1))
  have hF := hmult z
  have hne : (Function.update (mu φ) n (z + 1) n - z) / (πn n : ℂ) ≠ 0 := by
    rw [Function.update_self]
    exact div_ne_zero (by simp) (πn_ne_zero' n)
  have hG := factor_mult_of_ne (symmetricIcc ℤ) _ n hF hne
  have e : (fun m : ℤ => if m = n then (1 : ℂ) else (mu φ m - z) / (πn m : ℂ)) =
      fun m : ℤ => if m = n then (1 : ℂ) else
        (Function.update (mu φ) n (z + 1) m - z) / (πn m : ℂ) := by
    funext m
    by_cases hm : m = n
    · simp [hm]
    · simp [hm, Function.update_of_ne hm]
  rw [e]
  exact hG

theorem ite_update_eq (φ : PotPair) (n : ℤ) (w z : ℂ) :
    (fun m : ℤ => if m = n then (1 : ℂ) else (Function.update (mu φ) n w m - z) / (πn m : ℂ)) =
      fun m : ℤ => if m = n then (1 : ℂ) else (mu φ m - z) / (πn m : ℂ) := by
  funext m
  by_cases hm : m = n
  · simp [hm]
  · simp [hm, Function.update_of_ne hm]

theorem factor_out_mu (φ : PotPair) (z : ℂ) (n : ℤ) :
    ∏'[symmetricIcc ℤ] m : ℤ, (mu φ m - z) / (πn m : ℂ) =
      ((mu φ n - z) / (πn n : ℂ)) * reducedProd φ n z :=
  factor_of_mult (symmetricIcc ℤ) (fun m : ℤ => (mu φ m - z) / (πn m : ℂ)) n
    (mu_multipliable φ z) (red_mult_all φ n z)

theorem reducedProd_update (φ : PotPair) (n : ℤ) (w z : ℂ) :
    ∏'[symmetricIcc ℤ] m : ℤ,
      (if m = n then (1 : ℂ) else (Function.update (mu φ) n w m - z) / (πn m : ℂ)) =
      reducedProd φ n z := by
  unfold reducedProd
  refine tprod_congr fun m => ?_
  by_cases h : m = n
  · simp [h]
  · simp [h, Function.update_of_ne h]

theorem chi_eq_factor (φ : PotPair) (n : ℤ) (z : ℂ) :
    dirichletChar φ z = ((z - mu φ n) / (πn n : ℂ)) * reducedProd φ n z := by
  rw [mu_product φ z, factor_out_mu φ z n]
  ring

theorem reducedProd_differentiableAt (φ : PotPair) (n : ℤ) :
    DifferentiableAt ℂ (reducedProd φ n) (mu φ n) := by
  set w : ℂ := mu φ n + 1 with hw
  have hsum : Summable (fun k : ℤ =>
      ‖Function.update (mu φ) n w k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
    have e : (fun k : ℤ => ‖Function.update (mu φ) n w k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) =
        Function.update (fun k : ℤ => ‖mu φ k - (k : ℂ) * (Real.pi : ℂ)‖ ^ 2) n
          (‖w - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) := by
      funext k
      by_cases hk : k = n
      · subst hk; simp
      · simp [Function.update_of_ne hk]
    rw [e]
    exact (mu_summable φ).update n _
  obtain ⟨hmult, hdiff, -⟩ := NlsGge.GK38.Lib.product_entire _ hsum
  have hfac : ∀ z : ℂ, (∏'[symmetricIcc ℤ] m : ℤ,
      (Function.update (mu φ) n w m - z) / (πn m : ℂ)) =
      ((w - z) / (πn n : ℂ)) * reducedProd φ n z := by
    intro z
    have hG : Multipliable (fun m : ℤ => if m = n then (1 : ℂ) else
        (Function.update (mu φ) n w m - z) / (πn m : ℂ)) (symmetricIcc ℤ) := by
      rw [ite_update_eq]
      exact red_mult_all φ n z
    rw [factor_of_mult (symmetricIcc ℤ) (fun m : ℤ => (Function.update (mu φ) n w m - z) / (πn m : ℂ))
      n (hmult z) hG]
    simp only [Function.update_self, reducedProd]
    rw [ite_update_eq]
  have hμw : mu φ n ≠ w := by
    intro h
    apply one_ne_zero (α := ℂ)
    rw [hw] at h
    linear_combination -h
  have hev : reducedProd φ n =ᶠ[𝓝 (mu φ n)]
      (fun z => (∏'[symmetricIcc ℤ] m : ℤ, (Function.update (mu φ) n w m - z) / (πn m : ℂ)) *
        (πn n : ℂ) / (w - z)) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.2 hμw)] with z hz
    have hz' : w - z ≠ 0 := sub_ne_zero.mpr (fun h : w = z => hz (Set.mem_singleton_iff.2 h.symm))
    have hπ := πn_ne_zero' n
    rw [hfac z]
    field_simp
  have hEd : DifferentiableAt ℂ (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ,
      (Function.update (mu φ) n w m - z) / (πn m : ℂ)) (mu φ n) :=
    hdiff.differentiableAt
  have hGd : DifferentiableAt ℂ (fun z : ℂ =>
      (∏'[symmetricIcc ℤ] m : ℤ, (Function.update (mu φ) n w m - z) / (πn m : ℂ)) *
        (πn n : ℂ) / (w - z)) (mu φ n) := by
    refine DifferentiableAt.div (hEd.mul_const _) ?_ ?_
    · exact (differentiableAt_const _).sub differentiableAt_id
    · rw [hw]
      intro h
      apply one_ne_zero (α := ℂ)
      linear_combination h
  exact hGd.congr_of_eventuallyEq hev

theorem deriv_dirichletChar_eq (φ : PotPair) (n : ℤ) :
    deriv (dirichletChar φ) (mu φ n) = reducedProd φ n (mu φ n) / (πn n : ℂ) := by
  have hfun : dirichletChar φ = fun z => ((z - mu φ n) / (πn n : ℂ)) * reducedProd φ n z :=
    funext (chi_eq_factor φ n)
  rw [hfun]
  have hA : HasDerivAt (fun z : ℂ => (z - mu φ n) / (πn n : ℂ)) (1 / (πn n : ℂ)) (mu φ n) :=
    ((hasDerivAt_id' (mu φ n)).sub_const _).div_const _
  have hP := (reducedProd_differentiableAt φ n).hasDerivAt
  have key : deriv (fun z : ℂ => (z - mu φ n) / (πn n : ℂ) * reducedProd φ n z) (mu φ n) =
      1 / (πn n : ℂ) * reducedProd φ n (mu φ n) + (mu φ n - mu φ n) / (πn n : ℂ) * deriv (reducedProd φ n) (mu φ n) := (hA.mul hP).deriv
  rw [key]
  simp only [sub_self, zero_div, zero_mul, add_zero]
  ring

theorem mu_eq_muSeq (φ : PotPair) : mu φ = muSeq φ := by
  have h := muSeq_eq_candidate38 φ (Ncut_spec φ)
  exact h.symm

theorem dirInterp_eq_interpolationFactor (φ : PotPair) (n : ℤ) (h : simpleDirichlet φ (mu φ n)) :
    dirInterpolation38 φ (mu φ n) = interpolationFactor φ n :=
  (interpolationFactor_eq_dslope φ n h).symm

theorem interp_eq_ratio (φ : PotPair) (n : ℤ) (h : simpleDirichlet φ (mu φ n)) (lam : ℂ) :
    dirInterpolation38 φ (mu φ n) lam = reducedProd φ n lam / reducedProd φ n (mu φ n) := by
  have hP : reducedProd φ n (mu φ n) ≠ 0 := by
    intro h0
    apply h.2
    rw [deriv_dirichletChar_eq, h0, zero_div]
  have hπ := πn_ne_zero' n
  unfold dirInterpolation38
  by_cases hl : lam = mu φ n
  · subst hl
    rw [dslope_same, deriv_dirichletChar_eq]
    field_simp
  · rw [dslope_of_ne _ hl, slope_def_field, h.1, sub_zero, deriv_dirichletChar_eq,
      chi_eq_factor φ n lam]
    have hlm : lam - mu φ n ≠ 0 := sub_ne_zero.mpr hl
    field_simp

theorem reducedProd_ne_zero_of (φ : PotPair) (n : ℤ) (h : simpleDirichlet φ (mu φ n)) :
    reducedProd φ n (mu φ n) ≠ 0 := by
  intro h0
  apply h.2
  rw [deriv_dirichletChar_eq, h0, zero_div]

theorem tendsto_symm_icc_nat :
    Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop (symmetricIcc ℤ).filter :=
  tendsto_map.comp tendsto_natCast_atTop_atTop

theorem reducedProd_tendsto (φ : PotPair) (n : ℤ) (lam : ℂ) :
    Tendsto (fun N : ℕ => ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      (if m = n then (1 : ℂ) else (mu φ m - lam) / (πn m : ℂ)))
      atTop (𝓝 (reducedProd φ n lam)) :=
  (show Tendsto (fun s : Finset ℤ => ∏ b ∈ s,
      (if b = n then (1 : ℂ) else (mu φ b - lam) / (πn b : ℂ))) (symmetricIcc ℤ).filter
      (𝓝 (reducedProd φ n lam)) from (red_mult_all φ n lam).hasProd).comp tendsto_symm_icc_nat

/-- Pro's G1-070 contract, in the house names. -/
theorem G1_070 (φ : PotPair) (n : ℤ) (hn : simpleDirichlet φ (muSeq φ n)) :
    AnalyticOnNhd ℂ (dirInterpolation38 φ (muSeq φ n)) Set.univ ∧
    (∀ m : ℤ, dirInterpolation38 φ (muSeq φ n) (muSeq φ m) =
      if m = n then 1 else 0) ∧
    (∀ lam : ℂ, lam ≠ muSeq φ n →
      dirInterpolation38 φ (muSeq φ n) lam =
        dirichletChar φ lam / ((lam - muSeq φ n) * deriv (dirichletChar φ) (muSeq φ n))) ∧
    (∀ lam : ℂ,
      Tendsto (fun N : ℕ => ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if m = n then (1 : ℂ) else
          (muSeq φ m - lam) / (muSeq φ m - muSeq φ n))
        atTop (𝓝 (dirInterpolation38 φ (muSeq φ n) lam))) := by
  have hmu : ∀ m : ℤ, muSeq φ m = mu φ m := fun m => (congrFun (mu_eq_muSeq φ) m).symm
  have hn' : simpleDirichlet φ (mu φ n) := by
    rw [← hmu n]
    exact hn
  simp only [hmu]
  have hd : Differentiable ℂ (dirInterpolation38 φ (mu φ n)) := by
    rw [dirInterp_eq_interpolationFactor φ n hn']
    exact interpolationFactor_differentiable φ n hn'
  refine ⟨fun z _ => hd.analyticAt z, ?_, ?_, ?_⟩
  · intro m
    rw [dirInterp_eq_interpolationFactor φ n hn']
    exact dirichlet_interpolation_values φ n hn' m
  · intro lam hl
    unfold dirInterpolation38
    rw [dslope_of_ne _ hl, slope_def_field, hn'.1, sub_zero, div_div]
  · intro lam
    have hP := reducedProd_ne_zero_of φ n hn'
    have hfun : (fun N : ℕ => ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        (if m = n then (1 : ℂ) else (mu φ m - lam) / (mu φ m - mu φ n))) =
        fun N : ℕ => (∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = n then (1 : ℂ) else (mu φ m - lam) / (πn m : ℂ))) /
          ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          (if m = n then (1 : ℂ) else (mu φ m - mu φ n) / (πn m : ℂ)) := by
      funext N
      rw [← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun m _ => ?_
      by_cases hm : m = n
      · simp [hm]
      · simp only [hm, if_false]
        rw [div_div_div_cancel_right₀ (πn_ne_zero' m)]
    rw [hfun, interp_eq_ratio φ n hn' lam]
    exact (reducedProd_tendsto φ n lam).div (reducedProd_tendsto φ n (mu φ n)) hP

end NlsGge.Atomic.G1070
