import QuantumNLS.EnergyCompactCutoffsR20

/-! R-C17D95AA: uniform compact-form passage for every self-adjoint A >= 1.
The original A determines its bounded inverse, maximal positive square root,
and finite-energy sandwich through the frozen r13 construction. The source
pairing is complex and admits non-Hermitian compact forms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Filter Topology
open scoped InnerProductSpace ENNReal
namespace QuantumNLS.EnergyFormPassR20
open BoundedInverseR13 InverseSquareRootR13 CFCCutoffsR13 ArbitraryEnergyTraceR13
open TraceClass TraceIdeal EnergyForm Ext025B11TracePairing Ext025A12Trace Ext025A12Normal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) (h : LowerOne A)

/-- The source expectation is the pairing with the unique positive
trace-class realization. No eigenbasis for A is chosen. -/
def expectation (K : E →L[ℂ] E) (ρ : FiniteEnergy A hA h) : ℂ :=
  trace (refBasis E) (K*sandwich A hA h ρ)

/-- The source form on its exact square-root domain. -/
def form (K : E →L[ℂ] E) (f g : (half A hA h).domain) : ℂ :=
  ⟪half A hA h f,K (half A hA h g)⟫_ℂ

theorem form_sandwich (K : E →L[ℂ] E) (x y : E) :
    form A hA h K ⟨rootInv A hA h x,by rw [half_domain]; exact ⟨x,rfl⟩⟩
      ⟨rootInv A hA h y,by rw [half_domain]; exact ⟨y,rfl⟩⟩ = ⟪x,K y⟫_ℂ := by
  simp only [form,half_root]

/-- Any printed C with inverse-root sandwich K is this form on all Q(A). -/
theorem form_unique (K : E →L[ℂ] E)
    (C : (half A hA h).domain → (half A hA h).domain → ℂ)
    (hC : ∀ x y, C ⟨rootInv A hA h x,by rw [half_domain]; exact ⟨x,rfl⟩⟩
      ⟨rootInv A hA h y,by rw [half_domain]; exact ⟨y,rfl⟩⟩ = ⟪x,K y⟫_ℂ)
    (f g : (half A hA h).domain) : C f g = form A hA h K f g := by
  have hf : (⟨rootInv A hA h (half A hA h f),by rw [half_domain]; exact ⟨_,rfl⟩⟩ :
      (half A hA h).domain) = f := Subtype.ext (ArbitraryEnergyTraceR13.root_half A hA h f)
  have hg : (⟨rootInv A hA h (half A hA h g),by rw [half_domain]; exact ⟨_,rfl⟩⟩ :
      (half A hA h).domain) = g := Subtype.ext (ArbitraryEnergyTraceR13.root_half A hA h g)
  have he := hC (half A hA h f) (half A hA h g)
  rw [hf,hg] at he
  exact he

theorem expectation_basis {ι : Type*} (b : HilbertBasis ι ℂ E)
    (K : E →L[ℂ] E) (ρ : FiniteEnergy A hA h) :
    expectation A hA h K ρ = trace b (K*sandwich A hA h ρ) :=
  trace_basis_independent _ b _
    (lt_top_iff_ne_top.mpr (finite_left K _ (sandwich_finite A hA h ρ).ne))

theorem density_finite (ρ : FiniteEnergy A hA h) : IsTraceClass ρ.val := by
  rw [sandwich_spec A hA h ρ]
  exact finite_right _ _ (lt_top_iff_ne_top.mpr
    (finite_left _ _ (sandwich_finite A hA h ρ).ne))

theorem compressed_identity (ρ : FiniteEnergy A hA h) (m : ℕ) :
    cutoff (inverse A hA h) m*sandwich A hA h ρ*cutoff (inverse A hA h) m =
      rootCutoff (inverse A hA h) m*ρ.val*rootCutoff (inverse A hA h) m := by
  have hR := ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h)
  rw [sandwich_spec A hA h ρ]
  have hs : rootCutoff (inverse A hA h) m*rootInv A hA h = cutoff (inverse A hA h) m :=
    root_factor _ hR m
  have hs' : rootInv A hA h*rootCutoff (inverse A hA h) m = cutoff (inverse A hA h) m :=
    root_factor' _ hR m
  simp only [← mul_assoc,hs]
  rw [mul_assoc _ _ (rootCutoff (inverse A hA h) m),hs']

/-- The truncated form is a bounded observable of the ordinary density. -/
theorem truncated_identity (K : E →L[ℂ] E) (ρ : FiniteEnergy A hA h) (m : ℕ) :
    expectation A hA h (cutoff (inverse A hA h) m*K*cutoff (inverse A hA h) m) ρ =
      trace (refBasis E)
        ((rootCutoff (inverse A hA h) m*K*rootCutoff (inverse A hA h) m)*ρ.val) := by
  let P := cutoff (inverse A hA h) m
  let D := rootCutoff (inverse A hA h) m
  let S := sandwich A hA h ρ
  have ht : IsTraceClass S := sandwich_finite A hA h ρ
  change trace (refBasis E) ((P*K*P)*S) = _
  calc
    _ = trace (refBasis E) ((K*P*S)*P) := by
      simpa only [mul_assoc] using trace_cycle (refBasis E) P (K*P*S)
        (lt_top_iff_ne_top.mpr (finite_left _ S ht.ne))
    _ = trace (refBasis E) (K*(D*ρ.val*D)) := by
      have he := congrArg (fun Z => trace (refBasis E) (K*Z)) (compressed_identity A hA h ρ m)
      simpa only [P,D,S,mul_assoc] using he
    _ = trace (refBasis E) ((D*K*D)*ρ.val) := by
      simpa only [mul_assoc] using (trace_cycle (refBasis E) D (K*D*ρ.val)
        (lt_top_iff_ne_top.mpr (finite_left _ _ (density_finite A hA h ρ).ne))).symm

theorem error_bound (K J : E →L[ℂ] E) (ρ : FiniteEnergy A hA h) :
    ‖expectation A hA h K ρ-expectation A hA h J ρ‖ ≤
      ‖K-J‖*(energyTraceNorm (rootInv A hA h) ρ.val).toReal := by
  have ht := (sandwich_finite A hA h ρ).ne
  have he : expectation A hA h K ρ-expectation A hA h J ρ =
      trace (refBasis E) ((K-J)*sandwich A hA h ρ) := by
    rw [sub_mul,Ext025B11TracePairing.trace_sub _ _ _ (finite_left K _ ht) (finite_left J _ ht)]
    rfl
  rw [he,sandwich_norm]
  exact pairing_bound (refBasis E) (K-J) _ ht

theorem truncated_bound (K : E →L[ℂ] E) (ρ σ : FiniteEnergy A hA h) (m : ℕ) :
    ‖expectation A hA h (cutoff (inverse A hA h) m*K*cutoff (inverse A hA h) m) ρ-
      expectation A hA h (cutoff (inverse A hA h) m*K*cutoff (inverse A hA h) m) σ‖ ≤
      ‖rootCutoff (inverse A hA h) m*K*rootCutoff (inverse A hA h) m‖*
        (traceNorm (ρ.val-σ.val)).toReal := by
  rw [truncated_identity,truncated_identity]
  have hr := (density_finite A hA h ρ).ne
  have hs := (density_finite A hA h σ).ne
  rw [← Ext025B11TracePairing.trace_sub _ _ _ (finite_left _ _ hr) (finite_left _ _ hs),← mul_sub]
  exact pairing_bound (refBasis E) _ _ (Ext025A12Trace.finite_sub
    (density_finite A hA h ρ) (density_finite A hA h σ)).ne

private theorem uniform_passage {T : Type*}
    (ρ : ℕ → T → FiniteEnergy A hA h) (σ : T → FiniteEnergy A hA h)
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ n t, energyTraceNorm (rootInv A hA h) (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, energyTraceNorm (rootInv A hA h) (σ t).val ≤ ENNReal.ofReal B)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-(σ t).val) ≤ ENNReal.ofReal δ)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t,
      ‖expectation A hA h K (ρ n t)-expectation A hA h K (σ t)‖ ≤ ε := by
  intro ε hε
  let η := ε/(4*(B+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hR : 0 ≤ inverse A hA h := ContinuousLinearMap.nonneg_iff_isPositive.mpr (inverse_positive A hA h)
  have hd : DenseRange (inverse A hA h) := by
    change Dense ((inverse A hA h).range : Set E)
    rw [Submodule.dense_iff_topologicalClosure_eq_top,Submodule.topologicalClosure_eq_top_iff]
    rw [ContinuousLinearMap.IsStarNormal.orthogonal_range (inverse_positive A hA h).isSelfAdjoint.isStarNormal]
    exact LinearMap.ker_eq_bot.mpr (inverse_injective A hA h)
  have hlim : Tendsto (fun m : ℕ => ‖K-cutoff (inverse A hA h) m*K*cutoff (inverse A hA h) m‖)
      atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds (x := K)).sub
      (EnergyCompactCutoffsR20.compact_compression (inverse A hA h) hR hd K hK)).norm
    simpa only [sub_self,norm_zero] using hh
  have ht : ∀ᶠ m : ℕ in atTop,
      ‖K-cutoff (inverse A hA h) m*K*cutoff (inverse A hA h) m‖ < η :=
    (tendsto_order.mp hlim).2 η hη
  obtain ⟨m,hm⟩ := ht.exists
  let J := cutoff (inverse A hA h) m*K*cutoff (inverse A hA h) m
  let D := ‖rootCutoff (inverse A hA h) m*K*rootCutoff (inverse A hA h) m‖
  have hD : 0 ≤ D := norm_nonneg _
  let δ := ε/(2*(D+1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [hconv δ hδ] with n hn
  intro t
  have heρ : (energyTraceNorm (rootInv A hA h) (ρ n t).val).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hρ n t)).trans_eq (ENNReal.toReal_ofReal hB)
  have heσ : (energyTraceNorm (rootInv A hA h) (σ t).val).toReal ≤ B :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hσ t)).trans_eq (ENNReal.toReal_ofReal hB)
  have hc : (traceNorm ((ρ n t).val-(σ t).val)).toReal ≤ δ :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hn t)).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have eρ : ‖expectation A hA h K (ρ n t)-expectation A hA h J (ρ n t)‖ ≤ η*B :=
    (error_bound A hA h K J (ρ n t)).trans
      (mul_le_mul hm.le heρ ENNReal.toReal_nonneg hη.le)
  have eσ : ‖expectation A hA h J (σ t)-expectation A hA h K (σ t)‖ ≤ η*B := by
    rw [norm_sub_rev]
    exact (error_bound A hA h K J (σ t)).trans
      (mul_le_mul hm.le heσ ENNReal.toReal_nonneg hη.le)
  have eJ : ‖expectation A hA h J (ρ n t)-expectation A hA h J (σ t)‖ ≤ D*δ :=
    (truncated_bound A hA h K (ρ n t) (σ t) m).trans
      (mul_le_mul_of_nonneg_left hc hD)
  have hηB : η*B ≤ ε/4 := by
    have he := div_mul_cancel₀ ε (ne_of_gt (show 0 < 4*(B+1) by positivity))
    change ε/(4*(B+1))*B ≤ ε/4
    nlinarith [div_pos hε (show 0 < 4*(B+1) by positivity)]
  have hδD : D*δ ≤ ε/2 := by
    have he := div_mul_cancel₀ ε (ne_of_gt (show 0 < 2*(D+1) by positivity))
    change D*(ε/(2*(D+1))) ≤ ε/2
    nlinarith [div_pos hε (show 0 < 2*(D+1) by positivity)]
  calc
    _ ≤ ‖expectation A hA h K (ρ n t)-expectation A hA h J (ρ n t)‖+
        (‖expectation A hA h J (ρ n t)-expectation A hA h J (σ t)‖+
          ‖expectation A hA h J (σ t)-expectation A hA h K (σ t)‖) :=
      (norm_sub_le_norm_sub_add_norm_sub _ (expectation A hA h J (ρ n t)) _).trans
        (add_le_add le_rfl (norm_sub_le_norm_sub_add_norm_sub
          (expectation A hA h J (ρ n t)) (expectation A hA h J (σ t)) (expectation A hA h K (σ t))))
    _ ≤ η*B+(D*δ+η*B) := add_le_add eρ (add_le_add eJ eσ)
    _ ≤ ε := by linarith

/-- R-C17D95AA in its printed arbitrary-A class. The conclusions give uniform convergence, convergence of the literal real
parameter supremum, and its ENNReal version (including empty parameter sets).
Only positivity, finite uniformly bounded energy, ordinary uniform trace-norm
convergence and compactness of K_C are hypotheses. -/
theorem R_C17D95AA {T : Type*}
    (ρ : ℕ → T → FiniteEnergy A hA h) (σ : T → FiniteEnergy A hA h)
    (B : ℝ) (hB : 0 ≤ B)
    (hρ : ∀ n t, energyTraceNorm (rootInv A hA h) (ρ n t).val ≤ ENNReal.ofReal B)
    (hσ : ∀ t, energyTraceNorm (rootInv A hA h) (σ t).val ≤ ENNReal.ofReal B)
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ t,
      traceNorm ((ρ n t).val-(σ t).val) ≤ ENNReal.ofReal δ)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) :
    TendstoUniformly (fun n t => expectation A hA h K (ρ n t))
      (fun t => expectation A hA h K (σ t)) atTop ∧
    Tendsto (fun n => ⨆ t,
      ‖expectation A hA h K (ρ n t)-expectation A hA h K (σ t)‖) atTop (𝓝 0) ∧
    Tendsto (fun n => ⨆ t, ENNReal.ofReal
      ‖expectation A hA h K (ρ n t)-expectation A hA h K (σ t)‖) atTop (𝓝 0) := by
  have hu := uniform_passage A hA h ρ σ B hB hρ hσ hconv K hK
  refine ⟨?_,?_,?_⟩
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hu (ε/2) (half_pos hε)] with n hn
    intro t
    rw [dist_eq_norm,norm_sub_rev]
    exact (hn t).trans_lt (half_lt_self hε)
  · apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => ha.trans_le (Real.iSup_nonneg fun t => norm_nonneg _)
    · intro ε hε
      filter_upwards [hu (ε/2) (half_pos hε)] with n hn
      exact (Real.iSup_le hn (half_pos hε).le).trans_lt (half_lt_self hε)
  · apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨r,_,hr0,hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    have hr : 0 < r := ENNReal.ofReal_pos.mp hr0
    filter_upwards [hu r hr] with n hn
    exact iSup_le fun t => (ENNReal.ofReal_le_ofReal (hn t)).trans hrε.le

end QuantumNLS.EnergyFormPassR20
