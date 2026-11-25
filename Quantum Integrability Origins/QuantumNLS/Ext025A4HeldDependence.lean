import QuantumNLS.Ext025A4FamilyCharts
import QuantumNLS.Ext025A4LocalComparison
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open Set Metric Topology Filter
open scoped NNReal ENNReal
namespace QuantumNLS.Ext025A4HeldDependence
open QuantumNLS.Ext025A4BanachComplexification
open QuantumNLS.Ext025A4CompactAssembly
universe u v
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  {W : Type v} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- The exact Held GP-04 proposition, for arbitrary real Banach domain
and auxiliary target, with its radius and majorant constructed. -/
theorem held : QuantumNLS.ProductTorusAnalytic.HeldGP04AnalyticInitialDependence V W := by
  classical
  intro ι g L B φ S u hS hg hL hd h0 hm
  obtain ⟨R,hR,M,hM,K,Λ,hΛ,hG⟩ := QuantumNLS.Ext025A4FamilyCharts.family_data hS hg L B hL
  let τ := min (R/(16*(M+1))) (1/(2*((K : ℝ)+1)))
  have hτ : 0 < τ := lt_min (div_pos hR (by positivity)) (by positivity)
  obtain ⟨N,hN,d,hd0,hdτ,hNd⟩ := common_subdivision hτ
  let dn : ℝ≥0 := ⟨d,hd0.le⟩
  have hdM : d*M ≤ R/16 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 16*(M+1))).mp (hdτ.trans_le (min_le_left _ _))
    nlinarith
  have hdK : dn*K < 1 := by
    apply NNReal.coe_lt_coe.mp
    change d*(K : ℝ) < 1
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*((K : ℝ)+1))).mp (hdτ.trans_le (min_le_right _ _))
    nlinarith [K.coe_nonneg]
  let t : ℕ → ℝ := fun k => min ((k : ℝ)*d) 1
  have ht (k : ℕ) : t k ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min (mul_nonneg (Nat.cast_nonneg k) hd0.le) zero_le_one,min_le_right _ _⟩
  have htk (k : ℕ) (hk : k ≤ N) : t k = (k : ℝ)*d := by
    apply min_eq_left
    have hh : (k : ℝ) ≤ N := by exact_mod_cast hk
    nlinarith
  have ht0 : t 0 = 0 := by simp [t]
  have htN : t N = 1 := by rw [htk N le_rfl,hNd]
  have hts (k : ℕ) (hk : k < N) : t (k+1) = t k+d := by
    rw [htk (k+1) (by omega),htk k (by omega)]
    push_cast
    ring
  let a : ι → ℕ → V := fun i k => φ i (t k) u
  let c : ι → ℕ → Cx V := fun i k => Cx.ι (a i k)
  have ha (i : ι) (k : ℕ) : a i k ∈ S := hm i (t k) (ht k)
  choose G hc hdiff hLip hb hK he using fun i k => hG i (a i k) (ha i k)
  choose step hstep hstepL hstepEq using fun i k =>
    QuantumNLS.Ext025A4LocalComparison.local_step (hc i k) dn K hR hM
      (hdiff i k) hΛ (hLip i k) (hb i k) (hK i k) (he i k) hdM hdK
  have hγd (i : ι) (s : ℝ) (x : V) (z : ℝ) :
      HasDerivAt (fun z => φ i (s+d*z) x)
        (d • L i (g (φ i (s+d*z) x))) z := by
    have hh := (hd i x (s+d*z)).scomp z (((hasDerivAt_id z).const_mul d).const_add s)
    simpa only [mul_one,Function.comp_def,id_eq] using hh
  let A : ℝ := (1-d*(K : ℝ))⁻¹
  have hA : 1 ≤ A := by
    have hq : d*(K : ℝ) < 1 := by exact_mod_cast hdK
    apply (one_le_inv₀ (sub_pos.mpr hq)).mpr
    nlinarith [K.coe_nonneg]
  have hcent : ∀ i k, k < N → step i k (c i k) = c i (k+1) := by
    intro i k hk
    have hh := hstepEq i k (a i k) (mem_ball_self (by positivity))
      (fun z => φ i (t k+d*z) u) (hγd i (t k) u) (by simp [a])
    change step i k (Cx.ι (a i k)) = Cx.ι (φ i (t (k+1)) u)
    simpa only [mul_one,← hts k hk] using hh
  have hstart (i : ι) : c i 0 = Cx.ι u := by simp only [c,a,ht0,h0]
  have hfinal (i : ι) : c i N ∈ Cx.ι '' S := ⟨a i N,ha i N,rfl⟩
  have hSc : IsCompact (Cx.ι '' S) := hS.image (Cx.ιL : V →L[ℝ] Cx V).continuous
  have hδ : 0 < R/8 := by positivity
  obtain ⟨ρ,hρ,C,hp⟩ := compact_chain_uniformSeries step c N hSc hδ hA hcent
    (fun i k _ => hstepL i k) (fun i k _ => (hstep i k).differentiableOn) hfinal
  let ε := (R/8)/A^N
  have hε : 0 < ε := div_pos hδ (pow_pos (lt_of_lt_of_le zero_lt_one hA) N)
  have hagree (i : ι) (x : V) (hx : x ∈ ball u ε) :
      chain (step i) N (Cx.ι x) = Cx.ι (φ i 1 x) := by
    have hxi : Cx.ι x ∈ ball (c i 0) ε := by
      rw [hstart]
      simpa only [mem_ball,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hx
    have hcontrol := chain_control hδ hA (hcent i) (fun k _ => hstepL i k) hxi
    have heq (k : ℕ) (hk : k ≤ N) :
        chain (step i) k (Cx.ι x) = Cx.ι (φ i (t k) x) := by
      induction k with
      | zero => simp only [chain_zero,ht0,h0]
      | succ k ih =>
        have hkn : k < N := by omega
        have hi := ih (by omega)
        have hy : φ i (t k) x ∈ ball (a i k) (R/8) := by
          have hh := (hcontrol k (by omega)).2
          rw [hi] at hh
          simpa only [c,mem_ball,dist_eq_norm,← Cx.ι_sub,Cx.norm_ι] using hh
        rw [chain_succ,hi]
        have hh := hstepEq i k (φ i (t k) x) hy
          (fun z => φ i (t k+d*z) x) (hγd i (t k) x) (by simp)
        simpa only [mul_one,← hts k hkn] using hh
    simpa only [htN] using heq N le_rfl
  let r := min ρ ε
  have hr : 0 < r := lt_min hρ hε
  refine ⟨r,hr,C,fun i => ?_⟩
  obtain ⟨p,hp,hb⟩ := hp i
  let rn : ℝ≥0 := ⟨r,hr.le⟩
  have hco : (rn : ℝ≥0∞) = ENNReal.ofReal r := ENNReal.coe_nnreal_eq rn
  have hpr : HasFPowerSeriesOnBall (chain (step i) N) p (Cx.ι u) rn := by
    rw [← hstart]
    exact hp.mono (by exact_mod_cast hr) (by
      rw [hco]
      exact ENNReal.ofReal_le_ofReal (min_le_left _ _))
  have hbr (n : ℕ) : ‖p n‖*(rn : ℝ)^n ≤ C := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le (min_le_left ρ ε) n) (norm_nonneg _)).trans (hb n)
  obtain ⟨q,hq,hqb⟩ := QuantumNLS.Ext025A4RealRestriction.restrict_powerSeries
    Cx.ιL Cx.reL Cx.norm_ιL_le Cx.norm_reL_le (f := φ i 1) hpr hbr (fun x hx => by
      change Cx.re (chain (step i) N (Cx.ι x)) = φ i 1 x
      rw [hagree i x (ball_subset_ball (min_le_right _ _) hx)]
      rfl)
  exact ⟨q,by rw [← hco]; exact hq,hqb⟩
end QuantumNLS.Ext025A4HeldDependence

#print axioms QuantumNLS.Ext025A4HeldDependence.held
set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025A4HeldDependence" then
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
