import QuantumNLS.ContractionTraceR13

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter Topology
open scoped InnerProductSpace BigOperators ENNReal
namespace QuantumNLS.ContinuousTraceLimitR13
open TraceClass TraceIdeal Ext025B7GentleCompression EnergyTracePassage EnergyTraceLimit
open ContractionTraceR13
variable {E ι T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem rankOne_total (g : E) : total (InnerProductSpace.rankOne ℂ g g) = ‖g‖^2 := by
  rw [total,Fidelity.posTrace_rankOne_self,ENNReal.toReal_ofReal (sq_nonneg _)]

theorem rankOne_compressed_total (C : E →L[ℂ] E) (hc : C.adjoint = C) (g : E) :
    total (C*InnerProductSpace.rankOne ℂ g g*C) = ‖C g‖^2 := by
  have he := rankOne_conjugate C g
  rw [hc] at he
  rw [he,rankOne_total]

theorem compact_defects (C : ℕ → E →L[ℂ] E)
    (hp : ∀ m, 0 ≤ C m) (hn : ∀ m, ‖C m‖ ≤ 1)
    (g : T → E) (hg : IsCompact (Set.range g))
    (hu : TendstoUniformly (fun m => fun x : Set.range g => C m x.val)
      (fun x => x.val) atTop) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ t,
      total (InnerProductSpace.rankOne ℂ (g t) (g t))-
        total (C m*InnerProductSpace.rankOne ℂ (g t) (g t)*C m) ≤ ε := by
  obtain ⟨R,hR,hRg⟩ := hg.isBounded.exists_pos_norm_le
  intro ε hε
  have heps : 0 < ε/(4*(R+1)) := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformly_iff.mp hu _ heps] with m hm
  intro t
  rw [rankOne_total,rankOne_compressed_total _ ((hp m).isSelfAdjoint)]
  have hc : ‖C m (g t)‖ ≤ ‖g t‖ := by
    exact ((C m).le_opNorm _).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hn m) (norm_nonneg (g t)))
  have hb := hRg (g t) (Set.mem_range_self t)
  have hh := hm ⟨g t,Set.mem_range_self t⟩
  change dist (g t) (C m (g t)) < ε/(4*(R+1)) at hh
  rw [dist_eq_norm] at hh
  have hd := norm_sub_norm_le (g t) (C m (g t))
  have hden : 0 < 4*(R+1) := by positivity
  have he := (lt_div_iff₀ hden).mp hh
  have hnn := norm_nonneg (g t-C m (g t))
  nlinarith [norm_nonneg (g t),norm_nonneg (C m (g t)),mul_nonneg hnn
    (show 0 ≤ 2*R-‖g t‖-‖C m (g t)‖ by linarith)]

theorem uniform_gentle_limit (b : HilbertBasis ι ℂ E) (F : ℕ → E →L[ℂ] E)
    (hp : ∀ m, 0 ≤ F m) (hnorm : ∀ m, ‖F m‖ ≤ 1)
    (B : ℕ → T → E →L[ℂ] E) (g : T → E)
    (hB : ∀ n t, (B n t).IsPositive ∧ IsTraceClass (B n t))
    (hg : IsCompact (Set.range g))
    (hu : TendstoUniformly (fun m => fun x : Set.range g => F m x.val)
      (fun x => x.val) atTop)
    (ht : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      |total (B n t)-‖g t‖^2| ≤ ε)
    (hc : ∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (F m*
        (B n t-InnerProductSpace.rankOne ℂ (g t) (g t))*F m) ≤
          ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      traceNorm (B n t-InnerProductSpace.rankOne ℂ (g t) (g t)) ≤ ENNReal.ofReal ε := by
  have hD (t : T) : (InnerProductSpace.rankOne ℂ (g t) (g t)).IsPositive ∧
      IsTraceClass (InnerProductSpace.rankOne ℂ (g t) (g t)) := by
    refine ⟨InnerProductSpace.isPositive_rankOne_self _,?_⟩
    rw [IsTraceClass,traceNorm_of_isPositive (InnerProductSpace.isPositive_rankOne_self _),
      Fidelity.posTrace_rankOne_self]
    exact ENNReal.ofReal_lt_top
  have htr (t : T) : total (InnerProductSpace.rankOne ℂ (g t) (g t)) = ‖g t‖^2 := by
    rw [total,Fidelity.posTrace_rankOne_self,ENNReal.toReal_ofReal (sq_nonneg _)]
  obtain ⟨R,hR,hRg⟩ := hg.isBounded.exists_pos_norm_le
  let C := R^2+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCg (t : T) : ‖g t‖^2 ≤ R^2 := by
    have hh := hRg (g t) (Set.mem_range_self t)
    exact (sq_le_sq₀ (norm_nonneg (g t)) hR.le).mpr hh
  intro ε hε
  let δ := (ε/(6*(C+1)))^2
  have hδ : 0 < δ := sq_pos_of_pos (div_pos hε (by positivity))
  obtain ⟨m,hm⟩ := (compact_defects F hp hnorm g hg hu (δ/3) (by positivity)).exists
  let Q := F m
  let D := fun t => InnerProductSpace.rankOne ℂ (g t) (g t)
  filter_upwards [ht 1 zero_lt_one,ht (δ/3) (by positivity),
    hc m (min (δ/3) (ε/3)) (lt_min (by positivity) (by positivity))] with n hn htN hcN
  intro t
  have hbt : total (B n t) ≤ C := by
    have hh := le_abs_self (total (B n t)-‖g t‖^2)
    have hx := hn t
    dsimp [C]
    linarith only [hx,hh,hCg t]
  have hdt : total (D t) ≤ C := by dsimp [D]; rw [htr]; dsimp [C]; linarith only [hCg t]
  have hcomp : traceNorm (Q*(B n t-D t)*Q) ≤ ENNReal.ofReal (min (δ/3) (ε/3)) := hcN t
  have hcompr : (traceNorm (Q*(B n t-D t)*Q)).toReal ≤ δ/3 :=
    (ENNReal.toReal_le_of_le_ofReal (le_min (by positivity) (by positivity)) hcomp).trans (min_le_left _ _)
  have hdefD : total (D t)-total (Q*D t*Q) ≤ δ/3 := hm t
  have htailD : tail Q (D t) ≤ δ/3 :=
    (tail_le_defect b Q (D t) (hp m) (hnorm m) (hD t).1 (hD t).2).trans hdefD
  have htailB : tail Q (B n t) ≤ δ := by
    have hh := tail_le_defect b Q (B n t) (hp m) (hnorm m) (hB n t).1 (hB n t).2
    have hs : Q.adjoint = Q := (hp m).isSelfAdjoint
    have hcp (X : E →L[ℂ] E) (hx : X.IsPositive) : (Q*X*Q).IsPositive := by
      simpa only [hs] using block_positive X Q hx
    have hct (X : E →L[ℂ] E) (hx : X.IsPositive) (htx : IsTraceClass X) :
        IsTraceClass (Q*X*Q) := by
      rw [IsTraceClass,traceNorm_of_isPositive (hcp X hx)]
      exact lt_top_iff_ne_top.mpr (by simpa only [hs] using block_finite X Q hx htx)
    have hdif := total_difference b (Q*B n t*Q) (Q*D t*Q)
      (hcp _ (hB n t).1) (hcp _ (hD t).1)
      (hct _ (hB n t).1 (hB n t).2) (hct _ (hD t).1 (hD t).2)
    rw [← sub_mul,← mul_sub] at hdif
    have hx := htN t
    rw [← htr t] at hx
    have hx' := le_abs_self (total (B n t)-total (D t))
    have hy := neg_le_abs (total (Q*B n t*Q)-total (Q*D t*Q))
    linarith only [hh,hx,hx',hy,hdif,hcompr,hdefD]
  have hgB := contraction_gentle b (B n t) Q (hB n t).1 (hB n t).2
    ((hp m).isSelfAdjoint) (hnorm m)
  have hgD := contraction_gentle b (D t) Q (hD t).1 (hD t).2
    ((hp m).isSelfAdjoint) (hnorm m)
  have heB : traceNorm (B n t-Q*B n t*Q) ≤ ENNReal.ofReal (ε/3) :=
    hgB.trans (ENNReal.ofReal_le_ofReal
      (gentle_small C ε hC hε _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hbt htailB))
  have heD : traceNorm (D t-Q*D t*Q) ≤ ENNReal.ofReal (ε/3) :=
    hgD.trans (ENNReal.ofReal_le_ofReal
      (gentle_small C ε hC hε _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hdt
        (htailD.trans (by linarith))))
  have hneg : traceNorm (Q*D t*Q-D t) = traceNorm (D t-Q*D t*Q) := by
    rw [show Q*D t*Q-D t = (-1 : ℂ) • (D t-Q*D t*Q) by
      rw [neg_one_smul]; abel,traceNorm_smul]
    simp
  have hid : B n t-D t = (B n t-Q*B n t*Q)+Q*(B n t-D t)*Q+(Q*D t*Q-D t) := by
    noncomm_ring
  rw [hid]
  calc
    _ ≤ traceNorm (B n t-Q*B n t*Q)+traceNorm (Q*(B n t-D t)*Q)+
        traceNorm (Q*D t*Q-D t) :=
      (traceNorm_add_le ((B n t-Q*B n t*Q)+Q*(B n t-D t)*Q) (Q*D t*Q-D t)).trans
        (add_le_add (traceNorm_add_le (B n t-Q*B n t*Q) (Q*(B n t-D t)*Q))
          (le_refl (traceNorm (Q*D t*Q-D t))))
    _ ≤ ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3) := by
      rw [hneg]
      exact add_le_add (add_le_add heB (hcomp.trans
        (ENNReal.ofReal_le_ofReal (min_le_right _ _)))) heD
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
end QuantumNLS.ContinuousTraceLimitR13
