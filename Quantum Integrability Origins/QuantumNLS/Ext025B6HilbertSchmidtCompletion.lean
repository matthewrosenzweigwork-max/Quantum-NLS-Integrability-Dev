import QuantumNLS.Ext025STrace

/-! GP-09: completeness of the rectangular Hilbert-Schmidt ideal in its
actual basis-sum norm. The limit is constructed; finiteness is proved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Topology InnerProductSpace
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.Ext025B6HilbertSchmidtCompletion
open TraceClass TraceIdeal
variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem opNorm_sq_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) :
    ENNReal.ofReal (‖T‖^2) ≤ hsSq b T := by
  have hp : (T.adjoint ∘L T).IsPositive := ContinuousLinearMap.isPositive_adjoint_comp_self T
  have h := norm_le_traceNorm (T.adjoint ∘L T)
  rw [ContinuousLinearMap.norm_adjoint_comp_self,← pow_two,traceNorm_of_isPositive hp,
    posTrace_eq b hp,traceIn_adjoint_comp_self] at h
  exact h

omit [CompleteSpace E] [CompleteSpace F] in
theorem hsSq_add_le (b : HilbertBasis ι ℂ E) (A B : E →L[ℂ] F) :
    hsSq b (A+B) ≤ 2 * hsSq b A + 2 * hsSq b B := by
  unfold hsSq
  calc
    ∑' i, ENNReal.ofReal (‖(A+B) (b i)‖^2) ≤
        ∑' i, (2 * ENNReal.ofReal (‖A (b i)‖^2) + 2 * ENNReal.ofReal (‖B (b i)‖^2)) := by
      apply ENNReal.tsum_le_tsum
      intro i
      have h : ‖(A+B) (b i)‖^2 ≤ 2*‖A (b i)‖^2 + 2*‖B (b i)‖^2 := by
        change ‖A (b i)+B (b i)‖^2 ≤ _
        have hn := (sq_le_sq₀ (norm_nonneg (A (b i)+B (b i)))
          (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le _ _)
        nlinarith [sq_nonneg (‖A (b i)‖-‖B (b i)‖)]
      have hh := ENNReal.ofReal_le_ofReal h
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hh
      exact hh
    _ = _ := by rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]

omit [CompleteSpace E] [CompleteSpace F] in
theorem hsSq_neg (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) : hsSq b (-T) = hsSq b T := by
  simp [hsSq]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Closed finite HS balls in the operator norm topology. -/
theorem hsSq_limit_bound {J : Type*} {l : Filter J} [l.NeBot]
    (b : HilbertBasis ι ℂ E) (A : J → E →L[ℂ] F) (T : E →L[ℂ] F)
    (hlim : Tendsto A l (𝓝 T)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ j in l, hsSq b (A j) ≤ ENNReal.ofReal C) :
    hsSq b T ≤ ENNReal.ofReal C := by
  rw [hsSq,ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg ‖T (b i)‖)]
  apply ENNReal.ofReal_le_ofReal
  have ht : Tendsto (fun j => ∑ i ∈ S, ‖A j (b i)‖^2) l
      (𝓝 (∑ i ∈ S, ‖T (b i)‖^2)) :=
    tendsto_finsetSum S fun i _ =>
      (((ContinuousLinearMap.apply ℂ F (b i)).continuous.tendsto T).comp hlim).norm.pow 2
  apply le_of_tendsto ht
  filter_upwards [hbound] with j hj
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hj
  have hs : ∑ i ∈ S, ‖A j (b i)‖^2 ≤ (hsSq b (A j)).toReal := by
    rw [← ENNReal.ofReal_le_iff_le_toReal hf, ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    exact ENNReal.sum_le_tsum S
  exact hs.trans (by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hj)

/-- Every HS-Cauchy sequence of rectangular HS operators converges in HS norm
to a rectangular HS operator, on arbitrary complete complex Hilbert spaces. -/
theorem hs_complete (b : HilbertBasis ι ℂ E) (A : ℕ → E →L[ℂ] F)
    (hfin : ∀ n, hsSq b (A n) ≠ ⊤)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ K, ∀ m ≥ K, ∀ n ≥ K,
      hsSq b (A m-A n) ≤ ENNReal.ofReal (ε^2)) :
    ∃ T : E →L[ℂ] F, hsSq b T ≠ ⊤ ∧ Tendsto A atTop (𝓝 T) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, hsSq b (A n-T) ≤ ENNReal.ofReal (ε^2) := by
  have hcs : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K,hK⟩ := hA (ε/2) (by positivity)
    refine ⟨K,fun m hm n hn => ?_⟩
    have h := (opNorm_sq_le b (A m-A n)).trans (hK m hm n hn)
    have hh : ‖A m-A n‖^2 ≤ (ε/2)^2 :=
      (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp h
    rw [dist_eq_norm]
    have hn0 := norm_nonneg (A m-A n)
    nlinarith
  obtain ⟨T,hT⟩ := cauchySeq_tendsto_of_complete hcs
  have hc (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n in atTop, hsSq b (A n-T) ≤ ENNReal.ofReal (ε^2) := by
    obtain ⟨K,hK⟩ := hA ε hε
    apply eventually_atTop.mpr
    refine ⟨K,fun n hn => ?_⟩
    apply hsSq_limit_bound b (fun m => A n-A m) (A n-T)
      (tendsto_const_nhds.sub hT) (ε^2) (sq_nonneg _)
    exact eventually_atTop.mpr ⟨K,fun m hm => hK n hn m hm⟩
  have hfT : hsSq b T ≠ ⊤ := by
    obtain ⟨n,hn⟩ := (hc 1 zero_lt_one).exists
    have hd : hsSq b (A n-T) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hn
    have he : T = -(A n-T)+A n := by abel
    rw [he]
    apply ne_top_of_le_ne_top _ (hsSq_add_le b _ _)
    rw [hsSq_neg]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hd,
      ENNReal.mul_ne_top (by norm_num) (hfin n)⟩
  exact ⟨T,hfT,hT,hc⟩

end QuantumNLS.Ext025B6HilbertSchmidtCompletion

#print axioms QuantumNLS.Ext025B6HilbertSchmidtCompletion.opNorm_sq_le
#print axioms QuantumNLS.Ext025B6HilbertSchmidtCompletion.hsSq_add_le
#print axioms QuantumNLS.Ext025B6HilbertSchmidtCompletion.hsSq_neg
#print axioms QuantumNLS.Ext025B6HilbertSchmidtCompletion.hsSq_limit_bound
#print axioms QuantumNLS.Ext025B6HilbertSchmidtCompletion.hs_complete

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext025B6HilbertSchmidtCompletion." then
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
  Lean.logInfo m!"Ext025B6HilbertSchmidtCompletion audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
