import QuantumNLS.Ext025A4BanachSeries
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal ENNReal
namespace QuantumNLS.Ext025A4FamilyCharts
open QuantumNLS.Ext025A4BanachComplexification QuantumNLS.Ext025A4BanachSeries
universe u v
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

theorem local_extension {f : F → W} {a : F} (hf : AnalyticAt ℝ f a) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∃ G : Cx F → Cx W,
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧
      (∀ z ∈ ball (Cx.ι a) R, ‖G z‖ ≤ M) ∧
      ∀ x ∈ ball a R, G (Cx.ι x) = Cx.ι (f x) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, hρ, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast (ENNReal.coe_pos.mp hρ)
  obtain ⟨C, _, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hρr.trans_le hp.r_le)
  have hpρ : HasFPowerSeriesOnBall f p a (ENNReal.ofReal (ρ : ℝ)) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hp.mono hρ hρr.le
  have H := series_sum_hasSeries p a hρR hC
  have hsub : ball (Cx.ι a) ((ρ : ℝ)/4) ⊆ Metric.eball (Cx.ι a) (ENNReal.ofReal ((ρ : ℝ)/2)) := by
    rw [Metric.eball_ofReal]
    exact ball_subset_ball (by linarith)
  refine ⟨(ρ : ℝ)/4, by positivity, 2*C, _, H.differentiableOn.mono hsub,
    fun z hz => series_sum_bound p a hC z hz, fun x hx => ?_⟩
  exact series_sum_real hpρ x (ball_subset_ball (by linarith) hx)

/-- Clipping is performed on the domain; the target may be a different
Banach space. This is only an extension of the field chart. -/
theorem clip_extension {f : Cx F → Cx W} {a : Cx F} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball a R)) :
    ∃ G : Cx F → Cx W, Continuous G ∧ EqOn G f (closedBall a r) ∧
      DifferentiableOn ℂ G (ball a r) := by
  open QuantumNLS.Ext025A4LocalExtension in
  have hc : Continuous (fun z => f (clip a r z)) :=
    (hf.continuousOn.mono (closedBall_subset_ball hrR)).comp_continuous
      (clip_continuous a hr) (fun z => clip_mem a hr z)
  have he : EqOn (fun z => f (QuantumNLS.Ext025A4LocalExtension.clip a r z)) f (closedBall a r) := by
    intro z hz
    change f (QuantumNLS.Ext025A4LocalExtension.clip a r z) = f z
    rw [QuantumNLS.Ext025A4LocalExtension.clip_eq hr hz]
  exact ⟨_,hc,he,(hf.mono (ball_subset_ball hrR.le)).congr (he.mono ball_subset_closedBall)⟩
theorem local_field_data {f : F → W} {a : F} (ha : AnalyticAt ℝ f a) :
    ∃ R > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∃ K : ℝ≥0, ∃ Λ ≥ (0 : ℝ),
      ∃ G : Cx F → Cx W, Continuous G ∧
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧
      (∀ x ∈ ball (Cx.ι a) R, ∀ y ∈ ball (Cx.ι a) R,
        ‖fderiv ℂ G x - fderiv ℂ G y‖ ≤ Λ * ‖x-y‖) ∧
      (∀ z ∈ closedBall (Cx.ι a) (R/2), ‖G z‖ ≤ M) ∧
      LipschitzOnWith K G (closedBall (Cx.ι a) (R/2)) ∧
      ∀ x ∈ closedBall a (R/2), G (Cx.ι x) = Cx.ι (f x) := by
  obtain ⟨R₀, hR₀, M, G, hd, hb, he⟩ :=
    local_extension ha
  obtain ⟨D, hD, Λ, hΛ, hLip⟩ :=
    QuantumNLS.HolomorphicCauchyC1.fderiv_lipschitz_near isOpen_ball hd (mem_ball_self hR₀)
  obtain ⟨d, hd0, hdsub, K, hK, hfd⟩ :=
    QuantumNLS.HolomorphicCauchyC1.exists_uniform_fderiv_bound isOpen_ball hd (mem_ball_self hR₀)
  let R := min (R₀/2) (min (D/4) (d/2))
  have hR : 0 < R := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hRR : R < R₀ := (min_le_left _ _).trans_lt (half_lt_self hR₀)
  have hRD : R ≤ D/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hRd : R < d := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hd0)
  obtain ⟨G', hc, he', hd'⟩ :=
    clip_extension hR hRR hd
  have hfe (z : Cx F) (hz : z ∈ ball (Cx.ι a) R) : fderiv ℂ G' z = fderiv ℂ G z :=
    Filter.EventuallyEq.fderiv_eq (𝕜 := ℂ) (Filter.mem_of_superset (isOpen_ball.mem_nhds hz)
      (fun w hw => he' (ball_subset_closedBall hw)))
  have hsub : closedBall (Cx.ι a) (R/2) ⊆ ball (Cx.ι a) R :=
    closedBall_subset_ball (half_lt_self hR)
  have hMG : 0 ≤ M := (norm_nonneg _).trans (hb _ (mem_ball_self hR₀))
  refine ⟨R, hR, M, hMG, ⟨K,hK⟩, Λ, hΛ, G', hc, hd', ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hfe x hx, hfe y hy]
    exact hLip x (ball_subset_ball hRD hx) y (ball_subset_ball hRD hy)
  · intro z hz
    rw [he' (closedBall_subset_closedBall (half_le_self hR.le) hz)]
    exact hb z (ball_subset_ball hRR.le (hsub hz))
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm]
    apply (convex_closedBall (Cx.ι a) (R/2)).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (((hd'.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
      (fun z hz => ?_) hy hx
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro v
    change ‖fderiv ℂ G' z v‖ ≤ K * ‖v‖
    rw [hfe z (hsub hz)]
    exact hfd z (ball_subset_ball hRd.le (hsub hz)) v
  · intro x hx
    have hh : Cx.ι x ∈ closedBall (Cx.ι a) (R/2) := by
      simpa only [mem_closedBall, dist_eq_norm, ← Cx.ι_sub, Cx.norm_ι] using hx
    rw [he' (closedBall_subset_closedBall (half_le_self hR.le) hh)]
    exact he x (ball_subset_ball hRR.le ((closedBall_subset_ball (half_lt_self hR)) hx))



/-- A finite cover of the compact real set supplies common field,
Lipschitz and differential Lipschitz bounds before any parameter operator
is applied. No compactness of the operator family is needed. -/
theorem compact_data {f : F → W} {S : Set F} (hS : IsCompact S)
    (hf : AnalyticOnNhd ℝ f S) :
    ∃ R > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∃ K : ℝ≥0, ∃ Λ ≥ (0 : ℝ),
      ∀ a ∈ S, ∃ G : Cx F → Cx W, Continuous G ∧
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧
      (∀ x ∈ ball (Cx.ι a) R, ∀ y ∈ ball (Cx.ι a) R,
        ‖fderiv ℂ G x - fderiv ℂ G y‖ ≤ Λ * ‖x-y‖) ∧
      (∀ z ∈ closedBall (Cx.ι a) (R/2), ‖G z‖ ≤ M) ∧
      LipschitzOnWith K G (closedBall (Cx.ι a) (R/2)) ∧
      ∀ x ∈ closedBall a (R/2), G (Cx.ι x) = Cx.ι (f x) := by
  classical
  by_cases hne : S.Nonempty
  · choose R hR M hM K Λ hΛ G hc hd hl hb hk he using fun a : S => local_field_data (hf a a.2)
    obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun a : S => ball (a : F) (R a / 8))
      (fun _ => isOpen_ball) (fun a ha => mem_iUnion.mpr ⟨⟨a,ha⟩, mem_ball_self (div_pos (hR ⟨a,ha⟩) (by norm_num))⟩)
    have hsn : s.Nonempty := by
      obtain ⟨a,ha⟩ := hne
      obtain ⟨i,hi,_⟩ := mem_iUnion₂.mp (hs ha)
      exact ⟨i,hi⟩
    let R₀ := s.inf' hsn (fun i => R i / 8)
    let M₀ := s.sup' hsn M
    let K₀ := s.sup' hsn K
    let Λ₀ := s.sup' hsn Λ
    have hR₀ : 0 < R₀ := by
      dsimp [R₀]
      rw [Finset.lt_inf'_iff]
      exact fun i _ => div_pos (hR i) (by norm_num)
    obtain ⟨j,hj⟩ := hsn
    refine ⟨R₀,hR₀,M₀,(hM j).trans (Finset.le_sup' M hj),K₀,Λ₀,
      (hΛ j).trans (Finset.le_sup' Λ hj),fun a ha => ?_⟩
    obtain ⟨i,hi,hai⟩ := mem_iUnion₂.mp (hs ha)
    have hRi : R₀ ≤ R i / 8 := Finset.inf'_le _ hi
    have hdist : dist (Cx.ι a) (Cx.ι (i : F)) = dist a (i : F) := by
      rw [dist_eq_norm, ← Cx.ι_sub, Cx.norm_ι, dist_eq_norm]
    have hsub : ball (Cx.ι a) R₀ ⊆ ball (Cx.ι (i : F)) (R i) := by
      intro z hz
      rw [mem_ball] at hz hai ⊢
      have hh := dist_triangle z (Cx.ι a) (Cx.ι (i : F))
      rw [hdist] at hh
      linarith [hR i]
    have hsubc : closedBall (Cx.ι a) (R₀/2) ⊆ closedBall (Cx.ι (i : F)) (R i/2) := by
      intro z hz
      rw [mem_closedBall] at hz ⊢
      have hh := dist_triangle z (Cx.ι a) (Cx.ι (i : F))
      rw [hdist] at hh
      have hh' : dist a (i : F) < R i/8 := hai
      linarith [hR i]
    refine ⟨G i,hc i,(hd i).mono hsub,fun x hx y hy => ?_,fun z hz => ?_,
      ((hk i).mono hsubc).weaken (Finset.le_sup' K hi),fun x hx => ?_⟩
    · exact (hl i x (hsub hx) y (hsub hy)).trans
        (mul_le_mul_of_nonneg_right (Finset.le_sup' Λ hi) (norm_nonneg _))
    · exact (hb i z (hsubc hz)).trans (Finset.le_sup' M hi)
    · apply he i
      rw [mem_closedBall] at hx ⊢
      have hh : dist a (i : F) < R i/8 := hai
      linarith [dist_triangle x a (i : F),hR i]
  · refine ⟨1,zero_lt_one,0,le_rfl,0,0,le_rfl,fun a ha => ?_⟩
    exact (hne ⟨a,ha⟩).elim

end QuantumNLS.Ext025A4FamilyCharts

namespace QuantumNLS.Ext025A4FamilyCharts
open QuantumNLS.Ext025A4BanachComplexification
universe u v
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Uniformity over the entire bounded operator family is obtained by
composition with the complexified operators, with no loss of norm. -/
theorem family_data {ι : Type*} {g : V → W} {S : Set V} (hS : IsCompact S)
    (hg : AnalyticOnNhd ℝ g S) (L : ι → W →L[ℝ] V) (B : ℝ) (hL : ∀ i, ‖L i‖ ≤ B) :
    ∃ R > (0 : ℝ), ∃ M ≥ (0 : ℝ), ∃ K : ℝ≥0, ∃ Λ ≥ (0 : ℝ),
      ∀ i a, a ∈ S → ∃ G : Cx V → Cx V, Continuous G ∧
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧
      (∀ x ∈ ball (Cx.ι a) R, ∀ y ∈ ball (Cx.ι a) R,
        ‖fderiv ℂ G x - fderiv ℂ G y‖ ≤ Λ * ‖x-y‖) ∧
      (∀ z ∈ closedBall (Cx.ι a) (R/2), ‖G z‖ ≤ M) ∧
      LipschitzOnWith K G (closedBall (Cx.ι a) (R/2)) ∧
      ∀ x ∈ closedBall a (R/2), G (Cx.ι x) = Cx.ι (L i (g x)) := by
  obtain ⟨R,hR,M,hM,K,Λ,hΛ,hG⟩ := compact_data hS hg
  let b : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  refine ⟨R,hR,(b : ℝ)*M,mul_nonneg b.coe_nonneg hM,b*K,(b : ℝ)*Λ,
    mul_nonneg b.coe_nonneg hΛ,fun i a ha => ?_⟩
  obtain ⟨G,hc,hd,hl,hb,hk,he⟩ := hG a ha
  let A := Cx.mapL (L i)
  have hA : ‖A‖ ≤ b := (Cx.norm_mapL_le _).trans ((hL i).trans (le_max_left _ _))
  let H := fun z => A (G z)
  have hfd (z : Cx V) (hz : z ∈ ball (Cx.ι a) R) :
      fderiv ℂ H z = A.comp (fderiv ℂ G z) :=
    (A.hasFDerivAt.comp z (hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasFDerivAt).fderiv
  refine ⟨H,A.continuous.comp hc,fun z hz =>
    (A.differentiableAt.comp z (hd.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt,
    fun x hx y hy => ?_,fun z hz => ?_,?_,fun x hx => ?_⟩
  · rw [hfd x hx,hfd y hy]
    have heq : A.comp (fderiv ℂ G x) - A.comp (fderiv ℂ G y) =
        A.comp (fderiv ℂ G x - fderiv ℂ G y) := by
      apply ContinuousLinearMap.ext
      intro v
      simp
    rw [heq]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hA (hl x hx y hy) (norm_nonneg _) b.coe_nonneg).trans_eq (by ring))
  · exact (A.le_opNorm _).trans (mul_le_mul hA (hb z hz) (norm_nonneg _) b.coe_nonneg)
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change dist (A (G x)) (A (G y)) ≤ _
    rw [dist_eq_norm,← map_sub]
    exact (A.le_opNorm _).trans
      ((mul_le_mul hA (show ‖G x-G y‖ ≤ (K : ℝ)*dist x y from by simpa only [dist_eq_norm] using hk.dist_le_mul x hx y hy)
        (norm_nonneg _) b.coe_nonneg).trans_eq (by simp only [NNReal.coe_mul]; ring))
  · change A (G (Cx.ι x)) = _
    rw [he x hx]
    exact Cx.mapL_ι _ _
end QuantumNLS.Ext025A4FamilyCharts

#print axioms QuantumNLS.Ext025A4FamilyCharts.local_extension
#print axioms QuantumNLS.Ext025A4FamilyCharts.clip_extension
#print axioms QuantumNLS.Ext025A4FamilyCharts.local_field_data
#print axioms QuantumNLS.Ext025A4FamilyCharts.compact_data
#print axioms QuantumNLS.Ext025A4FamilyCharts.family_data
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4FamilyCharts" then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Result aggregate audit PASS: {seen.size} transitive constants; every own and generated constant standard-only."
