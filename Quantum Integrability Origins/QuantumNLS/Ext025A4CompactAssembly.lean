import QuantumNLS.Ext025A4AnalyticFlow
import QuantumNLS.ProductTorusHolomorphicExtension
import QuantumNLS.ProductTorusAnalytic
import QuantumNLS.TerraMultiRound18AnalyticFlow
import QuantumNLS.TerraMultiRound17D01Repair

/-! Round 92: quantitative finite composition along compact trajectories.
The local holomorphic charts are inputs to these assembly lemmas, not
additional hypotheses on either exact named consumer. Their construction
from the real analytic field remains a separate, explicitly open step.
All imported modules are frozen and consumed read-only. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open Set Metric Topology Filter
open scoped NNReal
namespace QuantumNLS.Ext025A4CompactAssembly

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Ordered short-step composition, with the actual intermediate values. -/
def chain (f : ℕ → E → E) : ℕ → E → E
  | 0 => id
  | n + 1 => fun x => f n (chain f n x)

@[simp] theorem chain_zero (f : ℕ → E → E) (x : E) : chain f 0 x = x := rfl
@[simp] theorem chain_succ (f : ℕ → E → E) (n : ℕ) (x : E) :
    chain f (n+1) x = f n (chain f n x) := rfl

/-- A fixed radius survives every step of a finite composition after the
explicit initial loss `A^n`. Centers may depend on every parameter. -/
theorem chain_control {f : ℕ → E → E} {c : ℕ → E} {n : ℕ} {R A : ℝ}
    (hR : 0 < R) (hA : 1 ≤ A)
    (hc : ∀ k < n, f k (c k) = c (k+1))
    (hL : ∀ k < n, ∀ x ∈ ball (c k) R, ∀ y ∈ ball (c k) R,
      dist (f k x) (f k y) ≤ A * dist x y)
    {x : E} (hx : x ∈ ball (c 0) (R / A^n)) :
    ∀ k ≤ n, dist (chain f k x) (c k) ≤ A^k * dist x (c 0) ∧
      chain f k x ∈ ball (c k) R := by
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hx' : dist x (c 0) < R / A^n := hx
  have hsmall (k : ℕ) (hk : k ≤ n) : A^k * dist x (c 0) < R := by
    calc A^k * dist x (c 0) ≤ A^n * dist x (c 0) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA hk) (dist_nonneg)
      _ < R := by
        have hh := (lt_div_iff₀ (pow_pos hA0 n)).mp hx'
        simpa only [mul_comm] using hh
  intro k hk
  induction k with
  | zero =>
      refine ⟨by simp, ?_⟩
      simpa only [chain_zero, mem_ball, pow_zero, one_mul] using hsmall 0 (Nat.zero_le n)
  | succ k ih =>
      obtain ⟨hb, hm⟩ := ih (Nat.le_of_succ_le hk)
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hh := hL k hkn _ hm _ (mem_ball_self hR)
      rw [hc k hkn] at hh
      have hbound : dist (chain f (k+1) x) (c (k+1)) ≤ A^(k+1) * dist x (c 0) := by
        calc dist (chain f (k+1) x) (c (k+1)) ≤ A * dist (chain f k x) (c k) := hh
          _ ≤ A * (A^k * dist x (c 0)) := mul_le_mul_of_nonneg_left hb hA0.le
          _ = A^(k+1) * dist x (c 0) := by ring
      exact ⟨hbound, hbound.trans_lt (hsmall (k+1) hk)⟩

/-- Holomorphy of the composed branch on the explicitly retained common
ball follows by differentiating the actual finite compositions. -/
theorem chain_differentiable {f : ℕ → E → E} {c : ℕ → E} {n : ℕ} {R A : ℝ}
    (hR : 0 < R) (hA : 1 ≤ A)
    (hc : ∀ k < n, f k (c k) = c (k+1))
    (hL : ∀ k < n, ∀ x ∈ ball (c k) R, ∀ y ∈ ball (c k) R,
      dist (f k x) (f k y) ≤ A * dist x y)
    (hf : ∀ k < n, DifferentiableOn ℂ (f k) (ball (c k) R)) :
    DifferentiableOn ℂ (chain f n) (ball (c 0) (R / A^n)) := by
  have hd (k : ℕ) (hk : k ≤ n) :
      DifferentiableOn ℂ (chain f k) (ball (c 0) (R / A^n)) := by
    induction k with
    | zero => exact differentiable_id.differentiableOn
    | succ k ih =>
      have hi := ih (Nat.le_of_succ_le hk)
      intro x hx
      exact ((hf k (Nat.lt_of_succ_le hk)).differentiableAt
        (isOpen_ball.mem_nhds (chain_control hR hA hc hL hx k (Nat.le_of_succ_le hk)).2)).comp_differentiableWithinAt
          x (hi x hx)
  exact hd n le_rfl

/-- Compactness supplies the common final value bound. Together with local
field-chart data, the finite assembly produces a uniform Taylor majorant;
no uniform-radius or uniform-coefficient conclusion is supplied. -/
theorem compact_chain_uniformSeries {ι : Type*} (f : ι → ℕ → E → E)
    (c : ι → ℕ → E) (n : ℕ) {S : Set E} (hS : IsCompact S)
    {R A : ℝ} (hR : 0 < R) (hA : 1 ≤ A)
    (hc : ∀ i k, k < n → f i k (c i k) = c i (k+1))
    (hL : ∀ i k, k < n → ∀ x ∈ ball (c i k) R, ∀ y ∈ ball (c i k) R,
      dist (f i k x) (f i k y) ≤ A * dist x y)
    (hf : ∀ i k, k < n → DifferentiableOn ℂ (f i k) (ball (c i k) R))
    (hfinal : ∀ i, c i n ∈ S) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ i, ∃ p : FormalMultilinearSeries ℂ E E,
      HasFPowerSeriesOnBall (chain (f i) n) p (c i 0) (ENNReal.ofReal r) ∧
      ∀ m, ‖p m‖ * r^m ≤ C := by
  obtain ⟨M, hM⟩ := hS.isBounded.subset_closedBall (0 : E)
  let M' := max M 0 + R
  let R' := R / A^n
  have hR' : 0 < R' := div_pos hR (pow_pos (lt_of_lt_of_le zero_lt_one hA) n)
  let r : NNReal := Real.toNNReal (R' / (4 * Real.exp 1))
  have hr : (0 : ℝ) < r := by
    change 0 < max (R' / (4 * Real.exp 1)) 0
    exact (div_pos hR' (by positivity)).trans_le (le_max_left _ _)
  refine ⟨r, hr, M' * Real.exp 1, fun i => ?_⟩
  have hd := chain_differentiable hR hA (hc i) (hL i) (hf i)
  have hb : ∀ z ∈ ball (c i 0) R', ‖chain (f i) n z‖ ≤ M' := by
    intro z hz
    have hn := (chain_control hR hA (hc i) (hL i) hz n le_rfl).2
    have hm : ‖c i n‖ ≤ M := by simpa only [mem_closedBall, dist_zero_right] using hM (hfinal i)
    calc ‖chain (f i) n z‖ ≤ ‖c i n‖ + R := norm_le_norm_add_const_of_dist_le hn.le
      _ ≤ max M 0 + R := add_le_add (hm.trans (le_max_left _ _)) le_rfl
  have hp := QuantumNLS.Ext025A4AnalyticMajorant.powerSeries_with_bound
    isOpen_ball hd (mem_ball_self hR') hR'
    (show 0 ≤ M' by dsimp [M']; positivity) (subset_refl _) hb
  refine ⟨fun m => ((m.factorial : ℂ))⁻¹ • iteratedFDeriv ℂ m (chain (f i) n) (c i 0), ?_, hp.2.2⟩
  simpa only [ENNReal.ofReal_coe_nnreal] using hp.2.1

/-- A compact cover gives a uniform chart radius at every reference
trajectory point, independently of the size of the parameter family. -/
theorem compact_chart_radius {S : Set E} (hS : IsCompact S) {J : Sort*}
    (U : J → Set E) (hU : ∀ j, IsOpen (U j)) (hcover : S ⊆ ⋃ j, U j) :
    ∃ R > (0 : ℝ), ∀ a ∈ S, ∃ j, ball a R ⊆ U j :=
  lebesgue_number_lemma_of_metric hS hU hcover

/-- A positive common short time determines a finite common subdivision.
The step length and the number of steps are constructed. -/
theorem common_subdivision {T : ℝ} (hT : 0 < T) :
    ∃ N : ℕ, 0 < N ∧ ∃ d > (0 : ℝ), d < T ∧ (N : ℝ) * d = 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / T)
  let N := n+1
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have hlarge : 1 / T < (N : ℝ) := by dsimp [N]; push_cast; linarith
  refine ⟨N, by dsimp [N]; omega, 1 / N, div_pos zero_lt_one hN, ?_, ?_⟩
  · rw [div_lt_iff₀ hN]
    have hh := (div_lt_iff₀ hT).mp hlarge
    nlinarith
  · field_simp

end QuantumNLS.Ext025A4CompactAssembly

namespace QuantumNLS.Ext025A4LocalExtension
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Radial clipping uses a strictly positive denominator and agrees with
identity on the closed ball. No compactness of a Banach ball is needed. -/
def clip (a : E) (r : ℝ) (z : E) : E :=
  a + ((r / max r ‖z-a‖ : ℝ) : ℂ) • (z-a)

theorem clip_continuous (a : E) {r : ℝ} (hr : 0 < r) : Continuous (clip a r) := by
  have hden (z : E) : max r ‖z-a‖ ≠ 0 := ne_of_gt (hr.trans_le (le_max_left _ _))
  unfold clip
  fun_prop

theorem clip_mem (a : E) {r : ℝ} (hr : 0 < r) (z : E) : clip a r z ∈ closedBall a r := by
  have hd : 0 < max r ‖z-a‖ := hr.trans_le (le_max_left _ _)
  rw [mem_closedBall, dist_eq_norm, clip, add_sub_cancel_left, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr.le hd.le)]
  have hm := le_max_right r ‖z-a‖
  exact (mul_le_mul_of_nonneg_left hm (div_nonneg hr.le hd.le)).trans_eq (div_mul_cancel₀ _ hd.ne')

theorem clip_eq {a z : E} {r : ℝ} (hr : 0 < r) (hz : z ∈ closedBall a r) : clip a r z = z := by
  have hn : ‖z-a‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  rw [clip, max_eq_left hn, div_self hr.ne', Complex.ofReal_one, one_smul]
  abel

/-- Every continuous field on a closed ball has a global continuous
extension agreeing there. This discharges the global-continuity requirement
of the literal Picard superposition operator from local field data. -/
theorem continuous_extension {f : E → E} {a : E} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall a r)) :
    ∃ F : E → E, Continuous F ∧ EqOn F f (closedBall a r) := by
  refine ⟨fun z => f (clip a r z), ?_, fun z hz => ?_⟩
  · exact hf.comp_continuous (clip_continuous a hr) (fun z => clip_mem a hr z)
  · change f (clip a r z) = f z
    rw [clip_eq hr hz]

/-- The clipped extension retains the actual complex differential on the
inner open ball. Its behavior outside that ball is irrelevant to Picard. -/
theorem holomorphic_continuous_extension {f : E → E} {a : E} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hf : DifferentiableOn ℂ f (ball a R)) :
    ∃ F : E → E, Continuous F ∧ EqOn F f (closedBall a r) ∧
      DifferentiableOn ℂ F (ball a r) := by
  have hsub : closedBall a r ⊆ ball a R := closedBall_subset_ball hrR
  obtain ⟨F, hF, he⟩ := continuous_extension hr (hf.continuousOn.mono hsub)
  refine ⟨F, hF, he, ?_⟩
  exact (hf.mono (ball_subset_ball hrR.le)).congr (he.mono ball_subset_closedBall)

end QuantumNLS.Ext025A4LocalExtension

namespace QuantumNLS.Ext025A4PicardStability
open QuantumNLS.Ext025A4AnalyticIntegral
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The actual Picard fixed point has an initial-value Lipschitz bound.
This derives the amplification factor needed by finite composition directly
from the time primitive and the local field Lipschitz constant. -/
theorem fixedPoint_initial_bound {f : E → E} (hc : Continuous f)
    {a : E} {r : ℝ} (T K : ℝ≥0)
    (hK : LipschitzOnWith K f (closedBall a r)) (hsmall : T*K < 1)
    {x y : E} {v w : Path E}
    (hv : v ∈ closedBall (ContinuousMap.const Time a) r)
    (hw : w ∈ closedBall (ContinuousMap.const Time a) r)
    (hfixv : picard f hc T (x,v) = v) (hfixw : picard f hc T (y,w) = w) :
    ‖v-w‖ ≤ (1 - (T : ℝ)*(K : ℝ))⁻¹ * ‖x-y‖ := by
  have hq : (T : ℝ)*(K : ℝ) < 1 := by exact_mod_cast hsmall
  have hdiff : picard f hc T (x,w) - picard f hc T (y,w) =
      ContinuousMap.const Time (x-y) := by
    ext t
    simp only [picard, ContinuousMap.sub_apply, ContinuousMap.add_apply,
      ContinuousMap.const_apply, ContinuousMap.smul_apply]
    abel
  have hsame := (picard_lipschitz hc T K hK x).dist_le_mul v hv w hw
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_mul] at hsame
  have hbound : ‖v-w‖ ≤ (T : ℝ)*(K : ℝ)*‖v-w‖ + ‖x-y‖ := by
    calc ‖v-w‖ = ‖picard f hc T (x,v) - picard f hc T (y,w)‖ := by rw [hfixv,hfixw]
      _ ≤ ‖picard f hc T (x,v) - picard f hc T (x,w)‖ +
          ‖picard f hc T (x,w) - picard f hc T (y,w)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (T : ℝ)*(K : ℝ)*‖v-w‖ + ‖x-y‖ := by
        rw [hdiff]
        exact add_le_add hsame ((ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun _ => le_rfl))
  rw [inv_mul_eq_div, le_div_iff₀ (sub_pos.mpr hq)]
  nlinarith

/-- Holomorphic local Picard solutions, including their common initial
amplification bound, are constructed from field data alone. -/
theorem local_holomorphic_lipschitz_solution {f : E → E} (hc : Continuous f)
    {a : E} {r R δ M Λ : ℝ} (T K : ℝ≥0) (hr : 0 ≤ r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball a R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ x ∈ ball a R, ∀ y ∈ ball a R,
      ‖fderiv ℂ f x - fderiv ℂ f y‖ ≤ Λ * ‖x-y‖)
    (hM : ∀ y ∈ closedBall a r, ‖f y‖ ≤ M)
    (hsize : δ + (T : ℝ)*M ≤ r) (hK : LipschitzOnWith K f (closedBall a r))
    (hsmall : T*K < 1) :
    ∃ g : E → Path E, AnalyticOnNhd ℂ g (ball a δ) ∧
      (∀ x ∈ ball a δ, g x ∈ closedBall (ContinuousMap.const Time a) r ∧
        ∀ t : Time, g x t = x + (T : ℂ) • ∫ s in (0 : ℝ)..(t : ℝ), extend
          (QuantumNLS.Ext025A4AnalyticPath.superposition f hc (g x)) s) ∧
      ∀ x ∈ ball a δ, ∀ y ∈ ball a δ,
        ‖g x-g y‖ ≤ (1 - (T : ℝ)*(K : ℝ))⁻¹ * ‖x-y‖ := by
  obtain ⟨g, hg, hsol⟩ := local_holomorphic_solution hc T K hr hrR hf hΛ hLip hM hsize hK hsmall
  refine ⟨g, hg, hsol, fun x hx y hy => ?_⟩
  apply fixedPoint_initial_bound hc T K hK hsmall (hsol x hx).1 (hsol y hy).1
  · ext t
    exact ((hsol x hx).2 t).symm
  · ext t
    exact ((hsol y hy).2 t).symm

/-- End-to-end complex assembly from local field bounds and reference
integral trajectories. The short holomorphic maps, their amplification
factor, the retained initial ball, and the Taylor majorant are constructed.
Reference paths carry no analyticity or nearby-initial-value conclusion. -/
theorem picard_compact_uniformSeries {ι : Type*} (f : ι → ℕ → E → E)
    (hc : ∀ i k, Continuous (f i k)) (c : ι → ℕ → E) (n : ℕ)
    {S : Set E} (hS : IsCompact S) (hfinal : ∀ i, c i n ∈ S)
    {r R δ M Λ : ℝ} (T K : ℝ≥0) (hr : 0 ≤ r) (hrR : r < R) (hδ : 0 < δ)
    (hf : ∀ i k, DifferentiableOn ℂ (f i k) (ball (c i k) R)) (hΛ : 0 ≤ Λ)
    (hLip : ∀ i k x, x ∈ ball (c i k) R → ∀ y ∈ ball (c i k) R,
      ‖fderiv ℂ (f i k) x - fderiv ℂ (f i k) y‖ ≤ Λ * ‖x-y‖)
    (hM : ∀ i k y, y ∈ closedBall (c i k) r → ‖f i k y‖ ≤ M)
    (hsize : δ + (T : ℝ)*M ≤ r)
    (hK : ∀ i k, LipschitzOnWith K (f i k) (closedBall (c i k) r))
    (hsmall : T*K < 1)
    (v : ι → ℕ → Path E)
    (hv : ∀ i k, k < n → v i k ∈ closedBall (ContinuousMap.const Time (c i k)) r)
    (hfix : ∀ i k, k < n → picard (f i k) (hc i k) T (c i k, v i k) = v i k)
    (hend : ∀ i k, k < n → v i k ⟨1, by constructor <;> norm_num⟩ = c i (k+1)) :
    ∃ step : ι → ℕ → E → E,
      (∀ i k, AnalyticOnNhd ℂ (step i k) (ball (c i k) δ)) ∧
      (∀ i k, k < n → step i k (c i k) = c i (k+1)) ∧
      ∃ ρ > (0 : ℝ), ∃ C : ℝ, ∀ i, ∃ p : FormalMultilinearSeries ℂ E E,
        HasFPowerSeriesOnBall (QuantumNLS.Ext025A4CompactAssembly.chain (step i) n)
          p (c i 0) (ENNReal.ofReal ρ) ∧ ∀ m, ‖p m‖ * ρ^m ≤ C := by
  classical
  choose g hg using fun i k => local_holomorphic_lipschitz_solution (hc i k)
    T K hr hrR (hf i k) hΛ (hLip i k) (hM i k) hsize (hK i k) hsmall
  let oneTime : Time := ⟨1, by constructor <;> norm_num⟩
  let step : ι → ℕ → E → E := fun i k x => g i k x oneTime
  have ha : ∀ i k, AnalyticOnNhd ℂ (step i k) (ball (c i k) δ) := by
    intro i k x hx
    exact ((ContinuousMap.evalCLM (R := ℂ) (M := E) oneTime).analyticAt _).comp ((hg i k).1 x hx)
  have he : ∀ i k, k < n → step i k (c i k) = c i (k+1) := by
    intro i k hk
    have hx := (hg i k).2.1 (c i k) (mem_ball_self hδ)
    have hfixg : picard (f i k) (hc i k) T (c i k, g i k (c i k)) = g i k (c i k) := by
      ext t
      exact (hx.2 t).symm
    have hb := fixedPoint_initial_bound (hc i k) T K (hK i k) hsmall hx.1 (hv i k hk) hfixg (hfix i k hk)
    have hh : g i k (c i k) = v i k := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa only [sub_self, norm_zero, mul_zero] using hb))
    change g i k (c i k) oneTime = _
    rw [hh]
    exact hend i k hk
  let A : ℝ := (1 - (T : ℝ)*(K : ℝ))⁻¹
  have hq : (T : ℝ)*(K : ℝ) < 1 := by exact_mod_cast hsmall
  have hA : 1 ≤ A := by
    dsimp only [A]
    apply (one_le_inv₀ (sub_pos.mpr hq)).mpr
    nlinarith [T.coe_nonneg, K.coe_nonneg]
  have hL : ∀ i k, k < n → ∀ x ∈ ball (c i k) δ, ∀ y ∈ ball (c i k) δ,
      dist (step i k x) (step i k y) ≤ A * dist x y := by
    intro i k _ x hx y hy
    change dist (g i k x oneTime) (g i k y oneTime) ≤ A * dist x y
    rw [dist_eq_norm, dist_eq_norm]
    exact ((g i k x - g i k y).norm_coe_le_norm oneTime).trans ((hg i k).2.2 x hx y hy)
  refine ⟨step, ha, he, ?_⟩
  exact QuantumNLS.Ext025A4CompactAssembly.compact_chain_uniformSeries step c n hS hδ hA he hL
    (fun i k _ => (ha i k).differentiableOn) hfinal

end QuantumNLS.Ext025A4PicardStability

namespace QuantumNLS.Ext025A4RealRestriction
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A complex uniform Taylor majorant restricts through contractive real
embedding and projection maps without losing either radius or bound.
This transports a constructed branch; its agreement with the real ODE
must be proved separately before applying it to an exact consumer. -/
theorem restrict_powerSeries (ι : V →L[ℝ] E) (π : E →L[ℝ] V)
    (hι : ‖ι‖ ≤ 1) (hπ : ‖π‖ ≤ 1) {f : V → V} {g : E → E} {u : V}
    {p : FormalMultilinearSeries ℂ E E} {r : NNReal} {C : ℝ}
    (hp : HasFPowerSeriesOnBall g p (ι u) r)
    (hbound : ∀ n, ‖p n‖ * (r : ℝ)^n ≤ C)
    (hag : ∀ x ∈ ball u (r : ℝ), π (g (ι x)) = f x) :
    ∃ q : FormalMultilinearSeries ℝ V V,
      HasFPowerSeriesOnBall f q u r ∧ ∀ n, ‖q n‖ * (r : ℝ)^n ≤ C := by
  let q := π.compFormalMultilinearSeries ((p.restrictScalars ℝ).compContinuousLinearMap ι)
  have hnorm (n : ℕ) : ‖q n‖ ≤ ‖p n‖ := by
    calc ‖q n‖ ≤ ‖π‖ * ‖(p.restrictScalars ℝ).compContinuousLinearMap ι n‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ 1 * (‖p n‖ * 1^n) := by
        apply mul_le_mul hπ
        · exact ((p.restrictScalars ℝ).norm_compContinuousLinearMap_le ι n).trans (by
            simp only [FormalMultilinearSeries.restrictScalars, ContinuousMultilinearMap.norm_restrictScalars]
            gcongr)
        · positivity
        · positivity
      _ = ‖p n‖ := by simp
  have hq : ∀ n, ‖q n‖ * (r : ℝ)^n ≤ C := fun n =>
    (mul_le_mul_of_nonneg_right (hnorm n) (by positivity)).trans (hbound n)
  refine ⟨q, ⟨FormalMultilinearSeries.le_radius_of_bound (p := q) C hq, hp.r_pos, ?_⟩, hq⟩
  intro y hy
  have hyr : ‖y‖ < (r : ℝ) := by simpa only [Metric.eball_coe, mem_ball, dist_zero_right] using hy
  have hιy : ‖ι y‖ < (r : ℝ) :=
    ((ι.le_opNorm y).trans (by simpa using mul_le_mul_of_nonneg_right hι (norm_nonneg y))).trans_lt hyr
  have hs := (hp.restrictScalars (𝕜 := ℝ)).hasSum (y := ι y) (by
    simpa only [Metric.eball_coe, mem_ball, dist_zero_right] using hιy)
  have hx : u+y ∈ ball u (r : ℝ) := by simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hyr
  have ht := π.hasSum hs
  rw [← map_add, hag _ hx] at ht
  convert ht using 1
  rfl

end QuantumNLS.Ext025A4RealRestriction

namespace QuantumNLS.Ext025A4HilbertCharts
open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear
universe u
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Actual local holomorphic field extension, obtained from real analyticity
using the frozen C2/C3 coefficient construction. No analytic flow is used. -/
theorem local_field_extension {f : F → F} {a : F} (hf : AnalyticAt ℝ f a) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∃ G : Cx F → Cx F,
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧ AnalyticOnNhd ℂ G (ball (Cx.ι a) R) ∧
      (∀ z ∈ ball (Cx.ι a) R, ‖G z‖ ≤ M) ∧
      ∀ x ∈ ball a R, G (Cx.ι x) = Cx.ι (f x) := by
  obtain ⟨p, r, hp⟩ := hf
  obtain ⟨ρ, hρ, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hρR : (0 : ℝ) < ρ := by exact_mod_cast (ENNReal.coe_pos.mp hρ)
  obtain ⟨C, _, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hρr.trans_le hp.r_le)
  have hpρ : HasFPowerSeriesOnBall f p a (ENNReal.ofReal (ρ : ℝ)) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using hp.mono hρ hρr.le
  obtain ⟨R, hR, M, hG⟩ := QuantumNLS.ProductTorusHolomorphicExtension.holomorphic_extension_of_majorant
    (fun _ : Unit => f) a hρR (fun _ => ⟨p, hpρ, hC⟩)
  exact ⟨R, hR, M, hG ()⟩

/-- A compact real analytic set supplies a uniform radius and value bound
for actual local complex field extensions centered at every reference
point. The finite cover and its common constants are constructed here. -/
theorem compact_field_charts {f : F → F} {S : Set F} (hS : IsCompact S)
    (hf : ∀ a ∈ S, AnalyticAt ℝ f a) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ S, ∃ G : Cx F → Cx F,
      DifferentiableOn ℂ G (ball (Cx.ι a) R) ∧ AnalyticOnNhd ℂ G (ball (Cx.ι a) R) ∧
      (∀ z ∈ ball (Cx.ι a) R, ‖G z‖ ≤ M) ∧
      ∀ x ∈ ball a R, G (Cx.ι x) = Cx.ι (f x) := by
  classical
  by_cases hne : S.Nonempty
  · choose R hR M G hG using fun a : S => local_field_extension (hf a a.2)
    obtain ⟨s, hs⟩ := hS.elim_finite_subcover (fun a : S => ball (a : F) (R a / 4))
      (fun _ => isOpen_ball) (fun a ha => mem_iUnion.mpr ⟨⟨a,ha⟩, mem_ball_self (div_pos (hR ⟨a,ha⟩) (by norm_num))⟩)
    have hsne : s.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      obtain ⟨i, hi, _⟩ := mem_iUnion₂.mp (hs ha)
      exact ⟨i,hi⟩
    let R₀ := s.inf' hsne (fun i => R i / 4)
    let M₀ := s.sup' hsne (fun i => max (M i) 0)
    have hR₀ : 0 < R₀ := by
      dsimp only [R₀]
      rw [Finset.lt_inf'_iff]
      exact fun i _ => div_pos (hR i) (by norm_num)
    have hM₀ : 0 ≤ M₀ := by
      obtain ⟨i, hi⟩ := hsne
      exact (le_max_right (M i) 0).trans (Finset.le_sup' (fun j => max (M j) 0) hi)
    refine ⟨R₀, hR₀, M₀, hM₀, fun a ha => ?_⟩
    obtain ⟨i, hi, hai⟩ := mem_iUnion₂.mp (hs ha)
    have hRi : R₀ ≤ R i / 4 := Finset.inf'_le _ hi
    have hdist : dist (Cx.ι a) (Cx.ι (i : F)) = dist a (i : F) := by
      rw [dist_eq_norm, ← ι_sub, Cx.norm_ι, dist_eq_norm]
    have hsub : ball (Cx.ι a) R₀ ⊆ ball (Cx.ι (i : F)) (R i) := by
      intro z hz
      rw [mem_ball] at hz hai ⊢
      have hh := dist_triangle z (Cx.ι a) (Cx.ι (i : F))
      rw [hdist] at hh
      linarith [hR i]
    refine ⟨G i, (hG i).1.mono hsub, (hG i).2.1.mono hsub, fun z hz => ?_, fun x hx => ?_⟩
    · exact ((hG i).2.2.1 z (hsub hz)).trans
        ((le_max_left (M i) 0).trans (Finset.le_sup' (fun j => max (M j) 0) hi))
    · apply (hG i).2.2.2
      rw [mem_ball] at hx hai ⊢
      linarith [dist_triangle x a (i : F), hR i]
  · refine ⟨1, zero_lt_one, 0, le_rfl, fun a ha => ?_⟩
    exact (hne ⟨a,ha⟩).elim

end QuantumNLS.Ext025A4HilbertCharts

namespace QuantumNLS.Ext025A4GP04Consumer
attribute [local instance] InnerProductSpace.complexToReal
open QuantumNLS.D01LocalPrimitive QuantumNLS.TerraMultiRound18Flow
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual compact complex field charts for the printed D01 hypotheses.
This is unconditional support for the exact compact-local consumer. -/
theorem d01_compact_field_charts (S : Hyp H) (K : Set H) (hK : IsCompact K) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, 0 ≤ M ∧ ∀ a ∈ K,
      ∃ G : QuantumNLS.ProductTorusComplexification.Cx H → QuantumNLS.ProductTorusComplexification.Cx H,
        DifferentiableOn ℂ G (ball (QuantumNLS.ProductTorusComplexification.Cx.ι a) R) ∧
        AnalyticOnNhd ℂ G (ball (QuantumNLS.ProductTorusComplexification.Cx.ι a) R) ∧
        (∀ z ∈ ball (QuantumNLS.ProductTorusComplexification.Cx.ι a) R, ‖G z‖ ≤ M) ∧
        ∀ x ∈ ball a R, G (QuantumNLS.ProductTorusComplexification.Cx.ι x) =
          QuantumNLS.ProductTorusComplexification.Cx.ι (S.Y x) :=
  QuantumNLS.Ext025A4HilbertCharts.compact_field_charts hK
    (fun a _ => (QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 a)

/-- Exact consumer bridge. The held proposition, specialized to the actual
analytic vector field and rescaled actual global flow, implies analyticity
at any finite real time. The reference compact set is constructed as the
continuous image of `[0,1]`; it is not a new source hypothesis. -/
theorem analytic_flow_of_held (S : Hyp H)
    (hGP : QuantumNLS.ProductTorusAnalytic.HeldGP04AnalyticInitialDependence H H)
    (t : ℝ) (x : H) : AnalyticAt ℝ (flow S t) x := by
  let γ : ℝ → H := fun s => flow S (t*s) x
  have hγ : Continuous γ :=
    (continuous_iff_continuousAt.mpr (fun s => ((flow_spec S x).2 s).continuousAt)).comp
      (continuous_const.mul continuous_id)
  let K : Set H := γ '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image hγ
  have hg : AnalyticOnNhd ℝ S.Y K := fun z _ =>
    (QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 z
  let L : Unit → H →L[ℝ] H := fun _ => t • ContinuousLinearMap.id ℝ H
  let φ : Unit → ℝ → H → H := fun _ s z => flow S (t*s) z
  have hL : ∀ i, ‖L i‖ ≤ ‖t‖ := by
    intro i
    exact (norm_smul_le t (ContinuousLinearMap.id ℝ H)).trans (by
      have hh := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := H)
      nlinarith [norm_nonneg t])
  have hφ : ∀ i z s, HasDerivAt (fun s => φ i s z) (L i (S.Y (φ i s z))) s := by
    intro i z s
    have hh := ((flow_spec S z).2 (t*s)).scomp s ((hasDerivAt_id s).const_mul t)
    simpa only [φ, L, _root_.smul_apply, ContinuousLinearMap.id_apply,
      mul_one, Function.comp_def, id_eq] using hh
  obtain ⟨r, _, C, hp⟩ := hGP Unit S.Y L ‖t‖ φ K x hK hg hL hφ
    (fun _ z => by simpa only [φ, mul_zero] using (flow_spec S z).1)
    (fun _ s hs => ⟨s, hs, rfl⟩)
  obtain ⟨p, hp, _⟩ := hp ()
  have ha := hp.analyticAt
  simpa only [φ, mul_one] using ha

/-- The exact named compact-local Prop follows from the exact held Prop.
Here the common time can be 1, since the previous theorem allows any t. -/
theorem compactLocalAnalyticity_of_held (S : Hyp H)
    (hGP : QuantumNLS.ProductTorusAnalytic.HeldGP04AnalyticInitialDependence H H) :
    QuantumNLS.TerraMultiRound18AnalyticFlow.GP04CompactLocalAnalyticity S := by
  intro K _
  exact ⟨1, zero_lt_one, fun x _ t _ => analytic_flow_of_held S hGP t x⟩

end QuantumNLS.Ext025A4GP04Consumer

#print axioms QuantumNLS.Ext025A4CompactAssembly.chain
#print axioms QuantumNLS.Ext025A4CompactAssembly.chain_zero
#print axioms QuantumNLS.Ext025A4CompactAssembly.chain_succ
#print axioms QuantumNLS.Ext025A4CompactAssembly.chain_control
#print axioms QuantumNLS.Ext025A4CompactAssembly.chain_differentiable
#print axioms QuantumNLS.Ext025A4CompactAssembly.compact_chain_uniformSeries
#print axioms QuantumNLS.Ext025A4CompactAssembly.compact_chart_radius
#print axioms QuantumNLS.Ext025A4CompactAssembly.common_subdivision
#print axioms QuantumNLS.Ext025A4GP04Consumer.analytic_flow_of_held
#print axioms QuantumNLS.Ext025A4GP04Consumer.compactLocalAnalyticity_of_held

#print axioms QuantumNLS.Ext025A4PicardStability.fixedPoint_initial_bound

#print axioms QuantumNLS.Ext025A4PicardStability.local_holomorphic_lipschitz_solution

#print axioms QuantumNLS.Ext025A4PicardStability.picard_compact_uniformSeries

#print axioms QuantumNLS.Ext025A4RealRestriction.restrict_powerSeries

#print axioms QuantumNLS.Ext025A4LocalExtension.clip

#print axioms QuantumNLS.Ext025A4LocalExtension.clip_continuous

#print axioms QuantumNLS.Ext025A4LocalExtension.clip_mem

#print axioms QuantumNLS.Ext025A4LocalExtension.clip_eq

#print axioms QuantumNLS.Ext025A4LocalExtension.continuous_extension

#print axioms QuantumNLS.Ext025A4LocalExtension.holomorphic_continuous_extension

#print axioms QuantumNLS.Ext025A4HilbertCharts.local_field_extension

#print axioms QuantumNLS.Ext025A4HilbertCharts.compact_field_charts

#print axioms QuantumNLS.Ext025A4GP04Consumer.d01_compact_field_charts

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if (n.toString.startsWith "QuantumNLS.Ext025A4CompactAssembly" || n.toString.startsWith "QuantumNLS.Ext025A4GP04Consumer" || n.toString.startsWith "QuantumNLS.Ext025A4PicardStability" || n.toString.startsWith "QuantumNLS.Ext025A4RealRestriction" || n.toString.startsWith "QuantumNLS.Ext025A4LocalExtension" || n.toString.startsWith "QuantumNLS.Ext025A4HilbertCharts") then
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
