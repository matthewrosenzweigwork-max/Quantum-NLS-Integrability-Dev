import QuantumNLS.ReconstructionInputsR33m

/-! R-FAF88C8A, in pre-start form. Positivity, trace one, the uniform upgrade
and preparation stability use the frozen accepted implementations. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace QuantumNLS.ReconstructionR33m

open ActualModelTargetR53a (HigherFlows flowMap flow_unique hamFlows)
open BetheCoefficientTransform (HN)
open BetheOccupationGauge (Gauge)
open Def033HierarchyR24m (Smooth physical smoothStep jointSmooth)
open OccupationUnitary (OneParticle oneBasis)
open TraceClass

variable {L κ : ℝ} [Fact (0 < L)]

private theorem step_modulus (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (R : Finset ℕ) (r : ℕ) (t : ℝ) (u : Smooth L) (a : ℤ) :
    ‖(Def021ChartR41b.chart L κ hκ).Φ (physical (smoothStep (hamFlows F R) r t u)) a‖ =
      ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ := by
  let C := ActualModelBindingR53a.chart (L := L) hκ
  have hp : REF88PrintedChart.PrintedChart hκ C.Φ :=
    ActualModelBindingR53a.printed_chart hκ
  change ‖C.Φ (physical (smoothStep (hamFlows F R) r t u)) a‖ = ‖C.Φ (physical u) a‖
  by_cases hr : r ∈ R
  swap
  · simp [smoothStep, hr]
  rw [smoothStep, dite_eq_left hr]
  match r with
  | 0 =>
    have hphase := Def033LowR24m.smoothClass_phase u.property t
    have ht : -Complex.I * (t : ℂ) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [ht] at hphase
    refine (congrArg (fun v => ‖C.Φ v a‖) hphase).trans ?_
    have he := congrArg (fun z : ℂ => ‖z‖)
      ((Def033LowR24m.low_covariance hκ hp (physical u) a).1 (-t))
    simpa only [physical, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] using he
  | 1 =>
    refine (congrArg (fun v => ‖C.Φ v a‖)
      (Def033LowR24m.smoothClass_trans u.property t)).trans ?_
    have he := congrArg (fun z : ℂ => ‖z‖)
      ((Def033LowR24m.low_covariance hκ hp (physical u) a).2 (-t))
    have ht : Complex.I * (LocalSpectral.pm L a : ℂ) * ((-t : ℝ) : ℂ) =
        (((LocalSpectral.pm L a * -t : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [ht] at he
    simpa only [physical, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul] using he
  | r + 2 =>
    obtain ⟨Φ, hΦ, _, _, hrot, -⟩ :=
      ActualModelBindingR53a.hierarchy_intermediate hκ H
    have hr2 : 2 ≤ r + 2 := by omega
    have hv : (⟨flowMap F (r + 2) t u.val,
         (((hamFlows F R).ham (r + 2) hr u.val u.property).2.2 t).1⟩ : Smooth L) =
        ⟨Φ (r + 2) t u.val, ((hΦ (r + 2) hr2 u.val u.property).2.2 t).1⟩ :=
      Subtype.ext ((flow_unique F (r + 2)) (Φ (r + 2)) (hΦ (r + 2) hr2) u.val u.property t).symm
    obtain ⟨ω, hω⟩ := hrot (r + 2) hr2 u a
    change ‖C.Φ (physical (⟨flowMap F (r + 2) t u.val, _⟩ : Smooth L)) a‖ = _
    rw [hv, hω t, norm_mul, Def033CoreR24m.phase, Complex.norm_exp]
    simp <;> rfl

/-- The fixed-time coordinate magnitudes are those of the initial chart vector,
including every collapsed and exterior label. -/
theorem coordinate_modulus (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (u : Smooth L) (R : Finset ℕ) (t : ℕ → ℝ) (a : ℤ) :
    ‖w hκ F u R t a‖ = ‖(Def021ChartR41b.chart L κ hκ).Φ (physical u) a‖ := by
  let C := Def021ChartR41b.chart L κ hκ
  change ‖C.Φ (physical (jointSmooth (hamFlows F R)
    t u)) a‖ = _
  unfold jointSmooth
  induction R.sort (· ≤ ·) with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldr_cons, step_modulus hκ H F]
    exact ih

private theorem norm_eq_of_coordinate_moduli {z v : OneParticle}
    (hm : ∀ a : ℤ, ‖z a‖ = ‖v a‖) : ‖z‖ = ‖v‖ := by
  have htwo : 0 < (2 : ℝ≥0∞).toReal := by norm_num
  rw [lp.norm_eq_tsum_rpow htwo, lp.norm_eq_tsum_rpow htwo]
  simp only [hm]

private theorem target_unit (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (u : Smooth L) (hu : ‖physical u‖ = 1)
    (R : Finset ℕ) (t : ℕ → ℝ) : ‖w hκ F u R t‖ = 1 := by
  let C := Def021ChartR41b.chart L κ hκ
  have hs := C.norm (physical u)
  rw [hu] at hs
  exact (norm_eq_of_coordinate_moduli (coordinate_modulus hκ H F u R t)).trans
    (by nlinarith [norm_nonneg (C.Φ (physical u))])

private theorem finite_projection_apply (S : Finset ℤ) (z : OneParticle) (a : ℤ) :
    Fidelity.coordProj S z a = if a ∈ S then z a else 0 := by
  classical
  rw [← Fidelity.inner_ev_left]
  by_cases ha : a ∈ S
  · rw [ite_eq_left ha]
    exact Fidelity.inner_ev_coordProj S z ha
  · rw [ite_eq_right ha, Fidelity.coordProj, inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hia : a ≠ i := fun h => ha (h ▸ hi)
    rw [inner_smul_right, Fidelity.inner_ev_left, Fidelity.ev, lp.single_apply_ne 2 i 1 hia]
    simp

/-- The finite-coordinate tail has the same norm at all times as at the
initial datum, and its infimum over finite sets is zero. -/
private theorem tight_of_coordinate_moduli {T : Type*} [Nonempty T]
    (z : T → OneParticle) (z₀ : OneParticle)
    (hm : ∀ t a, ‖z t a‖ = ‖z₀ a‖) :
    (⨅ S : Finset ℤ, ⨆ t, ‖z t - Fidelity.coordProj S (z t)‖) = 0 := by
  classical
  have htail (S : Finset ℤ) (t : T) :
      ‖z t - Fidelity.coordProj S (z t)‖ = ‖z₀ - Fidelity.coordProj S z₀‖ := by
    apply norm_eq_of_coordinate_moduli
    intro a
    simp only [lp.coeFn_sub, Pi.sub_apply, finite_projection_apply]
    by_cases ha : a ∈ S <;> simp [ha, hm]
  simp_rw [htail, ciSup_const]
  have hb : BddBelow (Set.range fun S : Finset ℤ => ‖z₀ - Fidelity.coordProj S z₀‖) := by
    exact ⟨0, by rintro _ ⟨S, rfl⟩; exact norm_nonneg _⟩
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_)
    (le_ciInf fun S => norm_nonneg _)
  have hsum : HasSum (fun a : ℤ => z₀ a • Fidelity.ev a) z₀ := by
    have he (a : ℤ) : oneBasis.repr z₀ a = z₀ a := by
      rw [HilbertBasis.repr_apply_apply, OccupationUnitary.oneBasis_apply]
      exact Fidelity.inner_ev_left a z₀
    simpa only [he, Fidelity.ev, OccupationUnitary.oneBasis_apply] using oneBasis.hasSum_repr z₀
  have he := (Metric.tendsto_nhds.mp hsum ε hε).exists
  obtain ⟨S, hS⟩ := he
  rw [dist_eq_norm, norm_sub_rev] at hS
  simpa only [zero_add] using (ciInf_le hb S).trans hS.le

private theorem product_unit (u : Smooth L) (hu : ‖physical u‖ = 1) (n : ℕ) :
    ‖product u n‖ = 1 := by
  change ‖TensorCarrier.htpow (1 + n) (physical u)‖ = 1
  rw [TensorCarrier.norm_htpow, hu, one_pow]

/-- A compact set in the actual fixed finite time space is contained in one box. -/
private theorem compact_subset_box {R : Finset ℕ} {K : Set (ℕ → ℝ)} (hK : IsCompact K) :
    ∃ B : ↥R → ℝ, K ⊆ TimeBox R (-B) B := by
  classical
  have hb (r : ↥R) : ∃ B : ℝ, ∀ t ∈ K, |t r| ≤ B := by
    obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_abs.comp (continuous_apply (r : ℕ))).continuousOn
    exact ⟨B, fun t ht => hB (Set.mem_image_of_mem _ ht)⟩
  choose B hB using hb
  exact ⟨B, fun t ht r => abs_le.mp (hB r t ht)⟩

private theorem density_positive (hκ : 0 < κ) (g : Gauge) (n : ℕ) (ψ : HN L (1 + n)) :
    (density hκ g n ψ).IsPositive :=
  ExactDensity.gamma_isPositive _

private theorem density_trace_one (hκ : 0 < κ) (g : Gauge) (n : ℕ) (ψ : HN L (1 + n))
    (hψ : ‖ψ‖ = 1) : posTrace (density hκ g n ψ) = 1 := by
  unfold density PreparationStability.density
  rw [ExactDensity.posTrace_Gamma, LinearIsometryEquiv.norm_map, hψ]
  simp

private theorem entry_error_le (hκ : 0 < κ) (g : Gauge) (n : ℕ) (ψ : HN L (1 + n))
    (hψ : ‖ψ‖ = 1) (a b : ℤ) (c : ℂ) :
    ‖Fidelity.entry (density hκ g n ψ) a b - c‖ ≤ ‖E (L := L) hκ g n a b ψ - c • ψ‖ := by
  have he := PreparationStability.density_entry (basis hκ n) g ψ a b
  rw [AuxiliaryDensity.gammaEntry] at he
  have hs : ⟪ψ, c • ψ⟫_ℂ = c := by
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp
  calc
    ‖Fidelity.entry (density hκ g n ψ) a b - c‖ =
        ‖⟪ψ, E (L := L) hκ g n a b ψ - c • ψ⟫_ℂ‖ := by
      rw [Fidelity.entry, show Fidelity.ev a = oneBasis a by simp [Fidelity.ev],
        show Fidelity.ev b = oneBasis b by simp [Fidelity.ev], he, inner_sub_right, hs]
    _ ≤ ‖E (L := L) hκ g n a b ψ - c • ψ‖ := by
      simpa only [hψ, one_mul] using
        norm_inner_le_norm (𝕜 := ℂ) ψ (E (L := L) hκ g n a b ψ - c • ψ)

private theorem product_trace_limit (hκ : 0 < κ)
    (H : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (F : HigherFlows L κ) (g : Gauge) (D : RD8362E5EBInput hκ F g)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (K : Set (ℕ → ℝ))
    [Nonempty K] (hK : IsCompact K) :
    Tendsto (fun n => ⨆ t : K,
      traceNorm (density hκ g n (U hκ R t.val n (product u n)) -
        projector (w hκ F u R t.val))) atTop (𝓝 0) := by
  let z : K → OneParticle := fun t => w hκ F u R t.val
  let v : (n : ℕ) → K → HN L (1 + n) := fun n t => U hκ R t.val n (product u n)
  have hv (n : ℕ) (t : K) : ‖v n t‖ = 1 :=
    (LinearIsometryEquiv.norm_map _ _).trans (product_unit u hu n)
  let z₀ := (Def021ChartR41b.chart L κ hκ).Φ (physical u)
  have hm (t : K) (a : ℤ) : ‖z t a‖ = ‖z₀ a‖ :=
    coordinate_modulus hκ H F u R t.val a
  have hz (t : K) : ‖z t‖ = 1 := target_unit hκ H F u hu R t.val
  refine Fidelity.uniform_upgrade (fun n t => density hκ g n (v n t)) z
    (fun n t => density_positive _ _ _ _) (fun n t => density_trace_one _ _ _ _ (hv n t))
    hz (tight_of_coordinate_moduli z z₀ hm) ?_
  intro a b
  obtain ⟨B, hB⟩ := compact_subset_box (R := R) hK
  have hprep : Preparation u (product u) := by
    refine ⟨product_unit u hu, ?_⟩
    simpa only [sub_self, norm_zero] using (tendsto_const_nhds : Tendsto
      (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have hs := (D u hu R (-B) B (product u) hprep a b).1
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hs (ε / 2) (half_pos hε)] with n hn
  let f : K → ℝ := fun t => ‖Fidelity.entry (density hκ g n (v n t)) a b - z t a * conj (z t b)‖
  have hupper (t : K) : f t ≤ ε / 2 :=
    (entry_error_le hκ g n (v n t) (hv n t) a b _).trans (hn t.val (hB t.property)).1
  have hnonneg : 0 ≤ ⨆ t, f t :=
    (norm_nonneg _).trans (le_ciSup ⟨ε / 2, by rintro _ ⟨t, rfl⟩; exact hupper t⟩
      (Classical.choice (inferInstance : Nonempty K)))
  change dist (⨆ t, f t) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (ciSup_le hupper).trans_lt (half_lt_self hε)

/-- R-FAF88C8A intermediate with precisely the two named source inputs.
The conclusion is the printed reconstruction statement at the same gauge. -/
theorem reconstruction_ofInput (hκ : 0 < κ) (g : Gauge)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (RD8362E5EBInput : ReconstructionR33m.RD8362E5EBInput hκ (flows hκ HierarchyInput) g) :
    Reconstruction hκ (flows hκ HierarchyInput) g := by
  intro u hu R K hK ψ hunit hprep
  rcases isEmpty_or_nonempty K with h | h
  · simp only [iSup_of_empty, bot_eq_zero]
    exact tendsto_const_nhds
  let F := flows hκ HierarchyInput
  let A := fun n (t : K) => density hκ g n (U hκ R t.val n (ψ n))
  let B := fun n (t : K) => density hκ g n (U hκ R t.val n (product u n))
  let P := fun t : K => projector (w hκ F u R t.val)
  let η := fun n => ‖ψ n - product u n‖
  have hp := product_trace_limit hκ HierarchyInput F g RD8362E5EBInput u hu R K hK
  have hη : Tendsto (fun n => ENNReal.ofReal (2 * η n)) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hprep.const_mul (2 : ℝ))
  have hstab (n : ℕ) : (⨆ t, traceNorm (A n t - B n t)) ≤ ENNReal.ofReal (2 * η n) := by
    have hh := PreparationStability.uniform_stability (basis (L := L) hκ n) g
      (fun t => U hκ R t n) (ψ n) (product u n) (hunit n) (product_unit u hu n) K
    exact hh.1.trans hh.2
  have hsum : Tendsto (fun n => ENNReal.ofReal (2 * η n) + ⨆ t, traceNorm (B n t - P t))
      atTop (𝓝 0) := by
    simpa only [add_zero] using hη.add hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun n => ?_)
  refine iSup_le fun t => ?_
  rw [show A n t - P t = (A n t - B n t) + (B n t - P t) by abel]
  exact (traceNorm_add_le _ _).trans
    (add_le_add ((le_iSup (fun x => traceNorm (A n x - B n x)) t).trans (hstab n))
      (le_iSup (fun x => traceNorm (B n x - P x)) t))

private theorem residual_sup_le {X T : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (A : X →L[ℂ] X) (hA : ‖A‖ ≤ 1) (z : T → ℂ) (hz : ∀ t, ‖z t‖ ≤ 1)
    (V : T → X ≃ₗᵢ[ℂ] X) (x y : X) (hx : ‖x‖ = 1) :
    (⨆ t, ‖A (V t y) - z t • V t y‖) ≤
      (⨆ t, ‖A (V t x) - z t • V t x‖) + 2 * ‖y - x‖ := by
  rcases isEmpty_or_nonempty T with h | h
  · simp only [iSup_of_empty', Real.sSup_empty, zero_add]
    positivity
  let M (t : T) := A - z t • ContinuousLinearMap.id ℂ X
  have hres (t : T) (v : X) : ‖M t v‖ ≤ 2 * ‖v‖ := by
    refine (StrongSymbolDef.norm_sub_smul_id_apply_le A (z t) v).trans ?_
    exact mul_le_mul_of_nonneg_right (by linarith [hz t]) (norm_nonneg v)
  change (⨆ t, ‖M t (V t y)‖) ≤ (⨆ t, ‖M t (V t x)‖) + 2 * ‖y - x‖
  have hb : BddAbove (Set.range fun t => ‖M t (V t x)‖) :=
    ⟨2, by rintro _ ⟨t, rfl⟩; simpa only [LinearIsometryEquiv.norm_map, hx, mul_one]
      using hres t (V t x)⟩
  apply ciSup_le
  intro t
  calc
    ‖M t (V t y)‖ = ‖M t (V t x) + M t (V t (y - x))‖ := by
      rw [← map_add, ← map_add]
      congr 2
      abel_nf
    _ ≤ ‖M t (V t x)‖ + ‖M t (V t (y - x))‖ := norm_add_le _ _
    _ ≤ (⨆ t, ‖M t (V t x)‖) + 2 * ‖y - x‖ :=
      add_le_add (le_ciSup hb t) (by simpa only [LinearIsometryEquiv.norm_map] using hres t (V t (y - x)))

/-- The two uniform residual estimates at the end of the printed proof. They
hold for each fixed label pair and both adjoint orientations on the same time set. -/
theorem cartesian_preparation_bounds (hκ : 0 < κ) (g : Gauge)
    (HierarchyInput : HierarchyInputR25m.HierarchyR7B122087Input (L := L) hκ)
    (u : Smooth L) (hu : ‖physical u‖ = 1) (R : Finset ℕ) (K : Set (ℕ → ℝ))
    (n : ℕ) (a b : ℤ) (ψ : HN L (1 + n)) :
    let z (t : K) := w hκ (flows hκ HierarchyInput) u R t.val
    let c (t : K) := z t a * conj (z t b)
    let v (t : K) := U hκ R t.val n
    let A := E (L := L) hκ g n a b
    let x := product u n
    (⨆ t : K, ‖A (v t ψ) - c t • v t ψ‖) ≤
      (⨆ t : K, ‖A (v t x) - c t • v t x‖) + 2 * ‖ψ - x‖ ∧
    (⨆ t : K, ‖A.adjoint (v t ψ) - conj (c t) • v t ψ‖) ≤
      (⨆ t : K, ‖A.adjoint (v t x) - conj (c t) • v t x‖) + 2 * ‖ψ - x‖ := by
  intro z c v A x
  have hA : ‖A‖ ≤ 1 := CartesianOccupationTransfer.physical_norm_le _ _ _ _
  have hz (t : K) : ‖z t‖ = 1 := target_unit hκ HierarchyInput _ u hu R t.val
  have hm (t : K) (i : ℤ) : ‖z t i‖ ≤ 1 := by
    rw [← Fidelity.inner_ev_left]
    have he : ‖Fidelity.ev i‖ = 1 := by rw [Fidelity.ev, lp.norm_single, norm_one]; norm_num
    simpa only [he, hz t, one_mul] using norm_inner_le_norm (𝕜 := ℂ) (Fidelity.ev i) (z t)
  have hc (t : K) : ‖c t‖ ≤ 1 := by
    change ‖z t a * conj (z t b)‖ ≤ 1
    rw [norm_mul, Complex.norm_conj]
    simpa only [one_mul] using
      mul_le_mul (hm t a) (hm t b) (norm_nonneg (z t b)) zero_le_one
  exact ⟨residual_sup_le A hA c hc v x ψ (product_unit u hu n),
    residual_sup_le A.adjoint (by simpa only [LinearIsometryEquiv.norm_map] using hA)
      (fun t => conj (c t)) (fun t => by simpa only [Complex.norm_conj] using hc t)
      v x ψ (product_unit u hu n)⟩

end QuantumNLS.ReconstructionR33m

#print axioms QuantumNLS.ReconstructionR33m.reconstruction_ofInput
#print axioms QuantumNLS.ReconstructionR33m.cartesian_preparation_bounds
#check QuantumNLS.ReconstructionR33m.reconstruction_ofInput
