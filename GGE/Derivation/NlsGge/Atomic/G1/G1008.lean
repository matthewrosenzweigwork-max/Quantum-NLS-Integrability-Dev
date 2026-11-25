import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential

/-! G1-008 induction step, part B01 (proof development): pure-analysis helpers.
Private candidate, supporting work; no acceptance claimed. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped Interval

namespace NlsGge.Atomic.G1008

theorem intervalIntegrable_of_sq {κ : ℝ → ℂ} {T : ℝ} (hm : AEStronglyMeasurable κ volume)
    (hsq : IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume 0 T) :
    IntervalIntegrable κ volume 0 T := by
  have hg : IntervalIntegrable (fun s : ℝ => 1 + ‖κ s‖ ^ 2) volume 0 T :=
    intervalIntegrable_const.add hsq
  refine hg.mono_fun' hm.restrict (Filter.Eventually.of_forall fun s => ?_)
  show ‖κ s‖ ≤ 1 + ‖κ s‖ ^ 2
  nlinarith [sq_nonneg (‖κ s‖ - 1), norm_nonneg (κ s)]

theorem integral_norm_le_sub {κ : ℝ → ℂ} {T Λ : ℝ} (hT : 0 ≤ T)
    (hm : AEStronglyMeasurable κ volume)
    (hsq : IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume 0 T)
    (hΛ : (∫ s in (0:ℝ)..T, ‖κ s‖ ^ 2) ≤ Λ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) :
    ∫ s in a..b, ‖κ s‖ ≤ Real.sqrt (b - a) * Real.sqrt Λ := by
  have hsq' : IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume a b := hsq.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hT]; exact Icc_subset_Icc ha hb)
  have h1 := NlsGge.GK38.integral_norm_le_sqrt_mul hab hm hsq'
  have h2 : (∫ s in a..b, ‖κ s‖ ^ 2) ≤ Λ := by
    refine le_trans ?_ hΛ
    exact intervalIntegral.integral_mono_interval ha hab hb
      (Filter.Eventually.of_forall fun s => (sq_nonneg ‖κ s‖ : (0:ℝ) ≤ ‖κ s‖ ^ 2)) hsq
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _))

theorem intervalIntegrable_mul_cont {κ g : ℝ → ℂ} {T w : ℝ} (hT : 0 ≤ T)
    (hκ : IntervalIntegrable κ volume 0 T) (hg : ContinuousOn g (Icc 0 T))
    (hw : w ∈ Icc (0:ℝ) T) : IntervalIntegrable (fun s => κ s * g s) volume 0 w := by
  have hsub : Set.uIcc (0:ℝ) w ⊆ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hw.1, Set.uIcc_of_le hT]; exact Icc_subset_Icc le_rfl hw.2
  exact (hκ.mono_set hsub).mul_continuousOn
    (hg.mono (by rw [Set.uIcc_of_le hw.1]; exact Icc_subset_Icc le_rfl hw.2))

theorem ql_time {κ : ℝ → ℂ} {T Λ Km : ℝ} (hT : 0 ≤ T) (hm : AEStronglyMeasurable κ volume)
    (hsq : IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume 0 T)
    (hΛ : (∫ s in (0:ℝ)..T, ‖κ s‖ ^ 2) ≤ Λ) {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 T))
    (hKb : ∀ s ∈ Icc (0:ℝ) T, ‖g s‖ ≤ Km) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hv : v ≤ T) :
    ‖(∫ s in (0:ℝ)..v, κ s * g s) - ∫ s in (0:ℝ)..u, κ s * g s‖ ≤
      Km * (Real.sqrt (v - u) * Real.sqrt Λ) := by
  have hκ : IntervalIntegrable κ volume 0 T := intervalIntegrable_of_sq hm hsq
  rw [intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_mul_cont hT hκ hg ⟨hu.trans huv, hv⟩)
    (intervalIntegrable_mul_cont hT hκ hg ⟨hu, huv.trans hv⟩)]
  have hκ' : IntervalIntegrable κ volume u v := hκ.mono_set (by
    rw [Set.uIcc_of_le huv, Set.uIcc_of_le hT]; exact Icc_subset_Icc hu hv)
  have hKm : 0 ≤ Km := le_trans (norm_nonneg _) (hKb 0 ⟨le_rfl, hT⟩)
  calc ‖∫ s in u..v, κ s * g s‖ ≤ ∫ s in u..v, Km * ‖κ s‖ := by
        refine intervalIntegral.norm_integral_le_of_norm_le huv ?_ (hκ'.norm.const_mul Km)
        refine Filter.Eventually.of_forall fun s hs => ?_
        have hs' : s ∈ Icc (0:ℝ) T := ⟨hu.trans hs.1.le, hs.2.trans hv⟩
        rw [norm_mul]
        calc ‖κ s‖ * ‖g s‖ ≤ ‖κ s‖ * Km := mul_le_mul_of_nonneg_left (hKb s hs') (norm_nonneg _)
          _ = Km * ‖κ s‖ := mul_comm _ _
    _ = Km * ∫ s in u..v, ‖κ s‖ := intervalIntegral.integral_const_mul _ _
    _ ≤ Km * (Real.sqrt (v - u) * Real.sqrt Λ) :=
        mul_le_mul_of_nonneg_left (integral_norm_le_sub hT hm hsq hΛ hu huv hv) hKm

theorem ql_space {κ : ℝ → ℂ} {T Λ Km ω : ℝ} (hT : 0 ≤ T)
    (hm : AEStronglyMeasurable κ volume)
    (hsq : IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume 0 T)
    (hΛ : (∫ s in (0:ℝ)..T, ‖κ s‖ ^ 2) ≤ Λ)
    {K : ℝ → ℂ → ℂ} {z z' : ℂ}
    (hKc : ContinuousOn (fun s => K s z) (Icc 0 T))
    (hKc' : ContinuousOn (fun s => K s z') (Icc 0 T))
    (hKb' : ∀ s ∈ Icc (0:ℝ) T, ‖K s z'‖ ≤ Km)
    (hω : ∀ s ∈ Icc (0:ℝ) T, ‖K s z - K s z'‖ ≤ ω)
    {t t' : ℝ} (ht : t ∈ Icc (0:ℝ) T) (ht' : t' ∈ Icc (0:ℝ) T) :
    ‖(∫ s in (0:ℝ)..t, κ s * K s z) - ∫ s in (0:ℝ)..t', κ s * K s z'‖ ≤
      ω * (Real.sqrt T * Real.sqrt Λ) + Km * (Real.sqrt |t - t'| * Real.sqrt Λ) := by
  have hκ : IntervalIntegrable κ volume 0 T := intervalIntegrable_of_sq hm hsq
  have hω0 : 0 ≤ ω := le_trans (norm_nonneg _) (hω 0 ⟨le_rfl, hT⟩)
  have hI1 := intervalIntegrable_mul_cont hT hκ hKc ht
  have hI2 := intervalIntegrable_mul_cont hT hκ hKc' ht
  have hsplit : (∫ s in (0:ℝ)..t, κ s * K s z) - ∫ s in (0:ℝ)..t', κ s * K s z' =
      (∫ s in (0:ℝ)..t, κ s * (K s z - K s z')) +
        ((∫ s in (0:ℝ)..t, κ s * K s z') - ∫ s in (0:ℝ)..t', κ s * K s z') := by
    have : (fun s => κ s * (K s z - K s z')) = fun s => κ s * K s z - κ s * K s z' :=
      funext fun s => mul_sub _ _ _
    rw [this, intervalIntegral.integral_sub hI1 hI2]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have hκt : IntervalIntegrable κ volume 0 t := hκ.mono_set (by
      rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2)
    calc ‖∫ s in (0:ℝ)..t, κ s * (K s z - K s z')‖ ≤ ∫ s in (0:ℝ)..t, ω * ‖κ s‖ := by
          refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ (hκt.norm.const_mul ω)
          refine Filter.Eventually.of_forall fun s hs => ?_
          have hs' : s ∈ Icc (0:ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
          rw [norm_mul]
          calc ‖κ s‖ * ‖K s z - K s z'‖ ≤ ‖κ s‖ * ω :=
                mul_le_mul_of_nonneg_left (hω s hs') (norm_nonneg _)
            _ = ω * ‖κ s‖ := mul_comm _ _
      _ = ω * ∫ s in (0:ℝ)..t, ‖κ s‖ := intervalIntegral.integral_const_mul _ _
      _ ≤ ω * (Real.sqrt T * Real.sqrt Λ) := by
          refine mul_le_mul_of_nonneg_left ?_ hω0
          have h := integral_norm_le_sub hT hm hsq hΛ le_rfl ht.1 ht.2
          rw [sub_zero] at h
          refine h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (Real.sqrt_nonneg _))
  · rcases le_total t' t with h | h
    · have := ql_time hT hm hsq hΛ hKc' hKb' ht'.1 h ht.2
      rw [abs_of_nonneg (sub_nonneg.2 h)]
      exact this
    · have := ql_time hT hm hsq hΛ hKc' hKb' ht.1 h ht'.2
      rw [norm_sub_rev] at this
      rw [abs_of_nonpos (sub_nonpos.2 h), neg_sub]
      exact this

theorem ql_uniform {K : ℝ → ℂ → ℂ} {T R : ℝ} (hT : 0 ≤ T)
    (hK : ContinuousOn (fun p : ℝ × ℂ => K p.1 p.2) (Icc 0 T ×ˢ closedBall (0:ℂ) R))
    {Λ : ℝ} (hΛ : 0 ≤ Λ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ κ : ℝ → ℂ, AEStronglyMeasurable κ volume →
      IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume 0 T →
      (∫ s in (0:ℝ)..T, ‖κ s‖ ^ 2) ≤ Λ →
      ∀ t ∈ Icc (0:ℝ) T, ∀ t' ∈ Icc (0:ℝ) T, ∀ z ∈ closedBall (0:ℂ) R,
        ∀ z' ∈ closedBall (0:ℂ) R, |t - t'| < δ → dist z z' < δ →
        ‖(∫ s in (0:ℝ)..t, κ s * K s z) - ∫ s in (0:ℝ)..t', κ s * K s z'‖ < ε := by
  have hSc : IsCompact (Icc (0:ℝ) T ×ˢ closedBall (0:ℂ) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨C, hC⟩ := hSc.exists_bound_of_continuousOn hK
  obtain ⟨Km, hKm0, hKmC⟩ : ∃ Km : ℝ, 0 ≤ Km ∧ C ≤ Km := ⟨max C 0, le_max_right _ _, le_max_left _ _⟩
  have hA0 : 0 ≤ Real.sqrt T * Real.sqrt Λ := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.sqrt T * Real.sqrt Λ := ⟨_, rfl⟩
  rw [← hA] at hA0
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Km * Real.sqrt Λ := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; exact mul_nonneg hKm0 (Real.sqrt_nonneg _)
  have hωpos : 0 < ε / (2 * (A + 1)) := div_pos hε (by linarith)
  have hEpos : 0 < ε / (2 * (D + 1)) := div_pos hε (by linarith)
  obtain ⟨δ1, hδ1, hδ1'⟩ := Metric.uniformContinuousOn_iff.1
    (hSc.uniformContinuousOn_of_continuous hK) (ε / (2 * (A + 1))) hωpos
  refine ⟨min δ1 ((ε / (2 * (D + 1))) ^ 2), lt_min hδ1 (by positivity), ?_⟩
  intro κ hm hsq hΛ' t ht t' ht' z hz z' hz' htt hzz
  have hzz1 : dist z z' < δ1 := lt_of_lt_of_le hzz (min_le_left _ _)
  have hω' : ∀ s ∈ Icc (0:ℝ) T, ‖K s z - K s z'‖ ≤ ε / (2 * (A + 1)) := by
    intro s hs
    have h := hδ1' (s, z) ⟨hs, hz⟩ (s, z') ⟨hs, hz'⟩
      (by rw [Prod.dist_eq]; exact max_lt (by simpa using hδ1) hzz1)
    rw [dist_eq_norm] at h
    exact h.le
  have hKc : ∀ w ∈ closedBall (0:ℂ) R, ContinuousOn (fun s => K s w) (Icc 0 T) := fun w hw =>
    hK.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hw⟩)
  have hKb : ∀ s ∈ Icc (0:ℝ) T, ‖K s z'‖ ≤ Km := fun s hs =>
    (hC (s, z') ⟨hs, hz'⟩).trans hKmC
  have hmain := ql_space hT hm hsq hΛ' (hKc z hz) (hKc z' hz') hKb hω' ht ht'
  have h1 : ε / (2 * (A + 1)) * (Real.sqrt T * Real.sqrt Λ) ≤ ε / 2 := by
    rw [← hA, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hsq1 : Real.sqrt |t - t'| < ε / (2 * (D + 1)) :=
    (Real.sqrt_lt' hEpos).2 (lt_of_lt_of_le htt (min_le_right _ _))
  have h2 : Km * (Real.sqrt |t - t'| * Real.sqrt Λ) < ε / 2 := by
    have e1 : Km * (Real.sqrt |t - t'| * Real.sqrt Λ) = D * Real.sqrt |t - t'| := by
      rw [hD]; ring
    rw [e1]
    have e2 : D * Real.sqrt |t - t'| ≤ D * (ε / (2 * (D + 1))) :=
      mul_le_mul_of_nonneg_left hsq1.le hD0
    have e3 : D * (ε / (2 * (D + 1))) < ε / 2 := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith)]
      nlinarith
    exact lt_of_le_of_lt e2 e3
  linarith

theorem uniform_of_equi {X : Type*} [PseudoMetricSpace X] {S : Set X} (hS : IsCompact S)
    {f : ℕ → X → ℂ} (hpt : ∀ x ∈ S, Tendsto (fun j => f j x) atTop (𝓝 0))
    (heq : ∀ ε > 0, ∃ δ > 0, ∀ j, ∀ x ∈ S, ∀ y ∈ S, dist x y < δ → ‖f j x - f j y‖ < ε) :
    TendstoUniformlyOn f (fun _ => (0:ℂ)) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := heq (ε / 2) (by linarith)
  obtain ⟨N, hNS, hNfin, hcover⟩ := hS.finite_cover_balls hδ
  have hev : ∀ᶠ j in atTop, ∀ y ∈ N, ‖f j y‖ < ε / 2 := by
    rw [Filter.eventually_all_finite hNfin]
    intro y hy
    have h := hpt y (hNS hy)
    have h2 := (Metric.tendsto_nhds.1 h) (ε / 2) (by linarith)
    filter_upwards [h2] with j hj
    simpa [dist_eq_norm] using hj
  filter_upwards [hev] with j hj x hx
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcover hx)
  have h1 := hδ' j x hx y (hNS hy) (Metric.mem_ball.1 hxy)
  have h2 := hj y hy
  rw [dist_eq_norm, zero_sub, norm_neg]
  calc ‖f j x‖ = ‖(f j x - f j y) + f j y‖ := by rw [sub_add_cancel]
    _ ≤ ‖f j x - f j y‖ + ‖f j y‖ := norm_add_le _ _
    _ < ε := by linarith

theorem tendstoUniformlyOn_pi_of {ι α : Type*} {δ : Type*} {β : δ → Type*}
    [∀ d, UniformSpace (β d)] {l : Filter ι} {s : Set α} {F : ι → α → ∀ d, β d}
    {f : α → ∀ d, β d}
    (h : ∀ d, TendstoUniformlyOn (fun i x => F i x d) (fun x => f x d) l s) :
    TendstoUniformlyOn F f l s := by
  rw [tendstoUniformlyOn_iff_tendsto, Pi.uniformity, tendsto_iInf]
  intro d
  rw [tendsto_comap_iff]
  exact tendstoUniformlyOn_iff_tendsto.1 (h d)

theorem tendstoUniformlyOn_matrix_of {ι α : Type*} {l : Filter ι} {s : Set α}
    {F : ι → α → Matrix (Fin 2) (Fin 2) ℂ} {f : α → Matrix (Fin 2) (Fin 2) ℂ}
    (h : ∀ i k, TendstoUniformlyOn (fun j x => F j x i k) (fun x => f x i k) l s) :
    TendstoUniformlyOn F f l s := by
  refine tendstoUniformlyOn_pi_of (β := fun _ : Fin 2 => Fin 2 → ℂ) (fun i => ?_)
  exact tendstoUniformlyOn_pi_of (β := fun _ : Fin 2 => ℂ) (fun k => h i k)


/-! ### Phases, kernels and the Volterra recursion -/

open NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations

def oth (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by fin_cases i <;> simp

def ph (z : ℂ) (u : ℝ) (i : Fin 2) : ℂ := freeE z u i i

def kap (a b : ℝ → ℂ) (i : Fin 2) (s : ℝ) : ℂ := rawPotCoeff38 a b s i (oth i)

theorem ph_zero (z : ℂ) (u : ℝ) : ph z u 0 = Complex.exp (-(Complex.I * z * u)) := by
  simp [ph, freeE]

theorem ph_one (z : ℂ) (u : ℝ) : ph z u 1 = Complex.exp (Complex.I * z * u) := by
  simp [ph, freeE]

theorem ph_sub (z : ℂ) (t s : ℝ) (i : Fin 2) : ph z (t - s) i = ph z t i * ph z (-s) i := by
  rcases fin2_cases i with rfl | rfl
  · rw [ph_zero, ph_zero, ph_zero, ← Complex.exp_add]; congr 1; push_cast; ring
  · rw [ph_one, ph_one, ph_one, ← Complex.exp_add]; congr 1; push_cast; ring

theorem continuous_ph (i : Fin 2) : Continuous (fun p : ℝ × ℂ => ph p.2 p.1 i) := by
  rcases fin2_cases i with rfl | rfl
  · simp only [ph_zero]; fun_prop
  · simp only [ph_one]; fun_prop

theorem continuous_ph_neg (i : Fin 2) : Continuous (fun p : ℝ × ℂ => ph p.2 (-p.1) i) :=
  (continuous_ph i).comp (by fun_prop : Continuous fun p : ℝ × ℂ => ((-p.1 : ℝ), p.2))

theorem continuous_freeE_entry (i k : Fin 2) :
    Continuous (fun p : ℝ × ℂ => freeE p.2 p.1 i k) := by
  rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases k with rfl | rfl
  · exact continuous_ph 0
  · have : (fun p : ℝ × ℂ => freeE p.2 p.1 0 1) = fun _ => 0 := by
      funext p; simp [freeE]
    rw [this]; exact continuous_const
  · have : (fun p : ℝ × ℂ => freeE p.2 p.1 1 0) = fun _ => 0 := by
      funext p; simp [freeE]
    rw [this]; exact continuous_const
  · exact continuous_ph 1

theorem ph_norm_le_ball {R T : ℝ} {z : ℂ} (hz : z ∈ closedBall (0:ℂ) R) {u : ℝ} (hu : |u| ≤ T)
    (i : Fin 2) : ‖ph z u i‖ ≤ Real.exp (R * T) := by
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have him : |z.im| ≤ R := (Complex.abs_im_le_norm z).trans hzR
  have hR0 : 0 ≤ R := (norm_nonneg z).trans hzR
  exact (norm_freeE_entry_le z u i i).trans
    (Real.exp_le_exp.2 (mul_le_mul him hu (abs_nonneg _) hR0))

theorem entry_integrand (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) (t s : ℝ) (i k : Fin 2) :
    (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
      freeKernelVolterraTerm38 a b z n s) i k =
      freeZsFundamentalComplex z (t - s) i i * rawPotCoeff38 a b s i (oth i) *
        freeKernelVolterraTerm38 a b z n s (oth i) k := by
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, oth, rawPotCoeff38,
      freeZsFundamentalComplex, freeDiagonalCandidate]

theorem Mn_succ (a b : ℝ → ℂ) (z : ℂ) (n : ℕ) (t : ℝ) (i k : Fin 2) :
    freeKernelVolterraTerm38 a b z (n + 1) t i k =
      ph z t i * ∫ s in (0:ℝ)..t,
        ph z (-s) i * kap a b i s * freeKernelVolterraTerm38 a b z n s (oth i) k := by
  change (∫ s in (0:ℝ)..t, (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
      freeKernelVolterraTerm38 a b z n s) i k) = _
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  show (freeZsFundamentalComplex z (t - s) * rawPotCoeff38 a b s *
      freeKernelVolterraTerm38 a b z n s) i k = _
  rw [entry_integrand]
  have h1 : freeZsFundamentalComplex z (t - s) i i = ph z (t - s) i := by
    rw [← freeE_eq]; rfl
  rw [h1, ph_sub]
  unfold kap
  ring

theorem kap_zero (a b : ℝ → ℂ) (s : ℝ) : kap a b 0 s = Complex.I * a s := by
  simp [kap, oth, rawPotCoeff38]

theorem kap_one (a b : ℝ → ℂ) (s : ℝ) : kap a b 1 s = -(Complex.I * b s) := by
  simp [kap, oth, rawPotCoeff38]

theorem kap_norm_sq_le (a b : ℝ → ℂ) (i : Fin 2) (s : ℝ) :
    ‖kap a b i s‖ ^ 2 ≤ ‖a s‖ ^ 2 + ‖b s‖ ^ 2 := by
  rcases fin2_cases i with rfl | rfl
  · rw [kap_zero, norm_mul, Complex.norm_I, one_mul]; nlinarith [sq_nonneg ‖b s‖]
  · rw [kap_one, norm_neg, norm_mul, Complex.norm_I, one_mul]; nlinarith [sq_nonneg ‖a s‖]

theorem kap_aesm {a b : ℝ → ℂ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) (i : Fin 2) : AEStronglyMeasurable (kap a b i) volume := by
  rcases fin2_cases i with rfl | rfl
  · have : kap a b 0 = fun s => Complex.I * a s := funext (kap_zero a b)
    rw [this]; exact aestronglyMeasurable_const.mul ha
  · have : kap a b 1 = fun s => -(Complex.I * b s) := funext (kap_one a b)
    rw [this]; exact (aestronglyMeasurable_const.mul hb).neg

theorem kap_sq_integrable {a b : ℝ → ℂ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) {T : ℝ}
    (hρ : IntervalIntegrable (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 T) (i : Fin 2) :
    IntervalIntegrable (fun s => ‖kap a b i s‖ ^ 2) volume 0 T := by
  refine hρ.mono_fun' ((kap_aesm ha hb i).norm.pow 2).restrict
    (Filter.Eventually.of_forall fun s => ?_)
  show ‖‖kap a b i s‖ ^ 2‖ ≤ ‖a s‖ ^ 2 + ‖b s‖ ^ 2
  rw [norm_pow, norm_norm]
  exact kap_norm_sq_le a b i s

theorem kap_sq_integral_le {a b : ℝ → ℂ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) {T : ℝ} (hT : 0 ≤ T)
    (hρ : IntervalIntegrable (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 T) (i : Fin 2) :
    (∫ s in (0:ℝ)..T, ‖kap a b i s‖ ^ 2) ≤ ∫ s in (0:ℝ)..T, (‖a s‖ ^ 2 + ‖b s‖ ^ 2) :=
  intervalIntegral.integral_mono_on hT (kap_sq_integrable ha hb hρ i) hρ
    (fun s _ => kap_norm_sq_le a b i s)

/-! ### Joint continuity of one fixed Volterra term -/

theorem Mn_continuousOn {a b : ℝ → ℂ} (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume)
    (hρ : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖a s‖ ^ 2 + ‖b s‖ ^ 2) volume 0 T)
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    ∀ i k : Fin 2, ContinuousOn
      (fun p : ℝ × ℂ => freeKernelVolterraTerm38 a b p.2 n p.1 i k)
      (Icc 0 T ×ˢ closedBall (0:ℂ) R) := by
  induction n with
  | zero =>
    intro i k
    have : (fun p : ℝ × ℂ => freeKernelVolterraTerm38 a b p.2 0 p.1 i k) =
        fun p => freeE p.2 p.1 i k := by
      funext p
      show freeZsFundamentalComplex p.2 p.1 i k = freeE p.2 p.1 i k
      rw [← freeE_eq]
    rw [this]; exact (continuous_freeE_entry i k).continuousOn
  | succ n ih =>
    intro i k
    let K : ℝ → ℂ → ℂ := fun s z =>
      ph z (-s) i * freeKernelVolterraTerm38 a b z n s (oth i) k
    have hK : ContinuousOn (fun p : ℝ × ℂ => K p.1 p.2) (Icc 0 T ×ˢ closedBall (0:ℂ) R) :=
      (continuous_ph_neg i).continuousOn.mul (ih (oth i) k)
    have hΛ0 : 0 ≤ ∫ s in (0:ℝ)..T, (‖a s‖ ^ 2 + ‖b s‖ ^ 2) :=
      intervalIntegral.integral_nonneg hT (fun s _ => by positivity)
    have hΨ : ContinuousOn
        (fun p : ℝ × ℂ => ∫ s in (0:ℝ)..p.1, kap a b i s * K s p.2)
        (Icc 0 T ×ˢ closedBall (0:ℂ) R) := by
      intro p hp
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hδ'⟩ := ql_uniform (K := K) hT hK hΛ0 hε
      refine ⟨δ, hδ, fun q hq hqp => ?_⟩
      rw [Prod.dist_eq] at hqp
      have hq1 := (max_lt_iff.1 hqp).1
      have hq2 := (max_lt_iff.1 hqp).2
      have h := hδ' (kap a b i) (kap_aesm ha hb i) (kap_sq_integrable ha hb (hρ T hT) i)
        (kap_sq_integral_le ha hb hT (hρ T hT) i) q.1 hq.1 p.1 hp.1 q.2 hq.2 p.2 hp.2
        (by rw [← Real.dist_eq]; exact hq1) hq2
      simpa [dist_eq_norm] using h
    have hMS : ∀ p : ℝ × ℂ, freeKernelVolterraTerm38 a b p.2 (n + 1) p.1 i k =
        ph p.2 p.1 i * ∫ s in (0:ℝ)..p.1, kap a b i s * K s p.2 := by
      intro p
      rw [Mn_succ]
      congr 1
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [K]
      ring
    exact ((continuous_ph i).continuousOn.mul hΨ).congr (fun p _ => hMS p)


/-! ### Abstract uniform convergence of the Volterra terms -/

theorem term1_bound {κ e m : ℝ → ℂ} {T Λ Eb η : ℝ} (hT : 0 ≤ T)
    (hmκ : AEStronglyMeasurable κ volume)
    (hsq : IntervalIntegrable (fun s => ‖κ s‖ ^ 2) volume 0 T)
    (hΛ : (∫ s in (0:ℝ)..T, ‖κ s‖ ^ 2) ≤ Λ)
    (he : ∀ s ∈ Icc (0:ℝ) T, ‖e s‖ ≤ Eb) (hm : ∀ s ∈ Icc (0:ℝ) T, ‖m s‖ ≤ η)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) T) :
    ‖∫ s in (0:ℝ)..t, e s * κ s * m s‖ ≤ Eb * η * (Real.sqrt T * Real.sqrt Λ) := by
  have hEb : 0 ≤ Eb := le_trans (norm_nonneg _) (he 0 ⟨le_rfl, hT⟩)
  have hη : 0 ≤ η := le_trans (norm_nonneg _) (hm 0 ⟨le_rfl, hT⟩)
  have hκ : IntervalIntegrable κ volume 0 T := intervalIntegrable_of_sq hmκ hsq
  have hκt : IntervalIntegrable κ volume 0 t := hκ.mono_set (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2)
  calc ‖∫ s in (0:ℝ)..t, e s * κ s * m s‖ ≤ ∫ s in (0:ℝ)..t, Eb * η * ‖κ s‖ := by
        refine intervalIntegral.norm_integral_le_of_norm_le ht.1 ?_ (hκt.norm.const_mul (Eb * η))
        refine Filter.Eventually.of_forall fun s hs => ?_
        have hs' : s ∈ Icc (0:ℝ) T := ⟨hs.1.le, hs.2.trans ht.2⟩
        rw [norm_mul, norm_mul]
        calc ‖e s‖ * ‖κ s‖ * ‖m s‖ ≤ Eb * ‖κ s‖ * η :=
              mul_le_mul (mul_le_mul_of_nonneg_right (he s hs') (norm_nonneg _)) (hm s hs')
                (norm_nonneg _) (mul_nonneg hEb (norm_nonneg _))
          _ = Eb * η * ‖κ s‖ := by ring
    _ = Eb * η * ∫ s in (0:ℝ)..t, ‖κ s‖ := intervalIntegral.integral_const_mul _ _
    _ ≤ Eb * η * (Real.sqrt T * Real.sqrt Λ) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hEb hη)
        have h := integral_norm_le_sub hT hmκ hsq hΛ le_rfl ht.1 ht.2
        rw [sub_zero] at h
        exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ht.2) (Real.sqrt_nonneg _))

theorem int_e_k_m {κ e m : ℝ → ℂ} {T t : ℝ} (hT : 0 ≤ T) (hκ : IntervalIntegrable κ volume 0 T)
    (he : ContinuousOn e (Icc 0 T)) (hm : ContinuousOn m (Icc 0 T)) (ht : t ∈ Icc (0:ℝ) T) :
    IntervalIntegrable (fun s => e s * κ s * m s) volume 0 t := by
  have h := intervalIntegrable_mul_cont hT hκ (he.mul hm) ht
  refine h.congr ?_
  intro s _
  simp only [Pi.mul_apply]
  ring

theorem Idecomp {κj κ0 e Mj M0 : ℝ → ℂ} {T t : ℝ} (hT : 0 ≤ T)
    (hκj : IntervalIntegrable κj volume 0 T) (hκ0 : IntervalIntegrable κ0 volume 0 T)
    (he : ContinuousOn e (Icc 0 T)) (hMj : ContinuousOn Mj (Icc 0 T))
    (hM0 : ContinuousOn M0 (Icc 0 T)) (ht : t ∈ Icc (0:ℝ) T) :
    ((∫ s in (0:ℝ)..t, e s * κj s * Mj s) - ∫ s in (0:ℝ)..t, e s * κ0 s * M0 s) =
      (∫ s in (0:ℝ)..t, e s * κj s * (Mj s - M0 s)) +
        ∫ s in (0:ℝ)..t, (κj s - κ0 s) * (e s * M0 s) := by
  have h1 := int_e_k_m hT hκj he hMj ht
  have h0 := int_e_k_m hT hκ0 he hM0 ht
  have hA : IntervalIntegrable (fun s => e s * κj s * (Mj s - M0 s)) volume 0 t :=
    int_e_k_m hT hκj he (hMj.sub hM0) ht
  have hB : IntervalIntegrable (fun s => (κj s - κ0 s) * (e s * M0 s)) volume 0 t :=
    intervalIntegrable_mul_cont hT (hκj.sub hκ0) (he.mul hM0) ht
  rw [← intervalIntegral.integral_sub h1 h0, ← intervalIntegral.integral_add hA hB]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  ring

theorem kap_pair {a b : ℕ → ℝ → ℂ} {a0 b0 : ℝ → ℂ}
    (hpa : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, a j s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, a0 s * g s)))
    (hpb : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, b j s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, b0 s * g s)))
    (i : Fin 2) {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 t)) :
    Tendsto (fun j => ∫ s in (0:ℝ)..t, kap (a j) (b j) i s * g s) atTop
      (𝓝 (∫ s in (0:ℝ)..t, kap a0 b0 i s * g s)) := by
  rcases fin2_cases i with rfl | rfl
  · simp only [kap_zero, mul_assoc, intervalIntegral.integral_const_mul]
    exact (hpa t ht g hg).const_mul Complex.I
  · simp only [kap_one, neg_mul, mul_assoc, intervalIntegral.integral_neg,
      intervalIntegral.integral_const_mul]
    exact ((hpb t ht g hg).const_mul Complex.I).neg

theorem norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x - y), norm_nonneg x, norm_nonneg y]


theorem small_of_tendsto_zero {S : Set (ℝ × ℂ)} {U : ℕ → ℝ × ℂ → ℂ}
    (h : TendstoUniformlyOn U (fun _ => (0:ℂ)) atTop S) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ p ∈ S, ‖U j p‖ < ε := by
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.1 h) ε hε] with j hj p hp
  have := hj p hp
  rwa [dist_eq_norm, zero_sub, norm_neg] at this

theorem step_generic {S : Set (ℝ × ℂ)} {Eb : ℝ} (hEb0 : 0 < Eb) {Fj : ℕ → ℝ × ℂ → ℂ}
    {F0 : ℝ × ℂ → ℂ} {ph' : ℝ × ℂ → ℂ} {U1 U2 : ℕ → ℝ × ℂ → ℂ}
    (hdec : ∀ j, ∀ p ∈ S, Fj j p - F0 p = ph' p * (U1 j p + U2 j p))
    (hph : ∀ p ∈ S, ‖ph' p‖ ≤ Eb)
    (hU1 : ∀ ε > 0, ∀ᶠ j in atTop, ∀ p ∈ S, ‖U1 j p‖ < ε)
    (hU2 : ∀ ε > 0, ∀ᶠ j in atTop, ∀ p ∈ S, ‖U2 j p‖ < ε) :
    TendstoUniformlyOn Fj F0 atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hε' : 0 < ε / (2 * (Eb + 1)) := div_pos hε (by linarith)
  filter_upwards [hU1 _ hε', hU2 _ hε'] with j h1 h2 p hp
  rw [dist_comm, dist_eq_norm, hdec j p hp, norm_mul]
  have hsum : ‖U1 j p + U2 j p‖ < 2 * (ε / (2 * (Eb + 1))) :=
    lt_of_le_of_lt (norm_add_le _ _) (by linarith [h1 p hp, h2 p hp])
  calc ‖ph' p‖ * ‖U1 j p + U2 j p‖ ≤ Eb * ‖U1 j p + U2 j p‖ :=
        mul_le_mul_of_nonneg_right (hph p hp) (norm_nonneg _)
    _ ≤ Eb * (2 * (ε / (2 * (Eb + 1)))) := mul_le_mul_of_nonneg_left hsum.le hEb0.le
    _ < ε := by
        have e1 : Eb * (2 * (ε / (2 * (Eb + 1)))) = ε * Eb / (Eb + 1) := by
          field_simp
        rw [e1, div_lt_iff₀ (by linarith)]
        nlinarith

theorem term1_small {κ : ℕ → ℝ → ℂ} {T R Λ Eb : ℝ} (hT : 0 ≤ T) (hEb0 : 0 < Eb)
    (hκm : ∀ j, AEStronglyMeasurable (κ j) volume)
    (hκsq : ∀ j, IntervalIntegrable (fun s => ‖κ j s‖ ^ 2) volume 0 T)
    (hκΛ : ∀ j, (∫ s in (0:ℝ)..T, ‖κ j s‖ ^ 2) ≤ Λ)
    {E : ℝ → ℂ → ℂ} (hE : ∀ s ∈ Icc (0:ℝ) T, ∀ z ∈ closedBall (0:ℂ) R, ‖E s z‖ ≤ Eb)
    {Mj : ℕ → ℝ × ℂ → ℂ} {M0 : ℝ × ℂ → ℂ}
    (hM : TendstoUniformlyOn Mj M0 atTop (Icc 0 T ×ˢ closedBall (0:ℂ) R)) :
    ∀ ε > 0, ∀ᶠ j in atTop, ∀ p ∈ Icc (0:ℝ) T ×ˢ closedBall (0:ℂ) R,
      ‖∫ s in (0:ℝ)..p.1, E s p.2 * κ j s * (Mj j (s, p.2) - M0 (s, p.2))‖ < ε := by
  intro ε hε
  have hA0 : 0 ≤ Real.sqrt T * Real.sqrt Λ :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = Real.sqrt T * Real.sqrt Λ := ⟨_, rfl⟩
  rw [← hA] at hA0
  have hEA : 0 ≤ Eb * A := mul_nonneg hEb0.le hA0
  have hη : 0 < ε / (Eb * A + 1) := div_pos hε (by linarith)
  have hIH := (Metric.tendstoUniformlyOn_iff.1 hM) (ε / (Eb * A + 1)) hη
  filter_upwards [hIH] with j hj p hp
  have hb := term1_bound (κ := κ j) (T := T) (Λ := Λ) (Eb := Eb) (η := ε / (Eb * A + 1))
    (e := fun s => E s p.2) (m := fun s => Mj j (s, p.2) - M0 (s, p.2)) hT (hκm j) (hκsq j)
    (hκΛ j) (fun s hs => hE s hs p.2 hp.2)
    (fun s hs => by
      have h := hj (s, p.2) ⟨hs, hp.2⟩
      rw [dist_comm, dist_eq_norm] at h
      exact h.le) hp.1
  rw [← hA] at hb
  have hlt : Eb * (ε / (Eb * A + 1)) * A < ε := by
    have e1 : Eb * (ε / (Eb * A + 1)) * A = ε * (Eb * A) / (Eb * A + 1) := by
      field_simp
    rw [e1, div_lt_iff₀ (by linarith)]
    nlinarith
  exact lt_of_le_of_lt hb hlt

theorem term2_uniform {κ : ℕ → ℝ → ℂ} {κ0 : ℝ → ℂ} {T R Λ : ℝ} (hT : 0 ≤ T) (hΛ : 0 ≤ Λ)
    (hκm : ∀ j, AEStronglyMeasurable (κ j) volume) (hκm0 : AEStronglyMeasurable κ0 volume)
    (hκsq : ∀ j, IntervalIntegrable (fun s => ‖κ j s‖ ^ 2) volume 0 T)
    (hκsq0 : IntervalIntegrable (fun s => ‖κ0 s‖ ^ 2) volume 0 T)
    (hκΛ : ∀ j, (∫ s in (0:ℝ)..T, ‖κ j s‖ ^ 2) ≤ Λ)
    (hκΛ0 : (∫ s in (0:ℝ)..T, ‖κ0 s‖ ^ 2) ≤ Λ)
    (hpair : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, κ j s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, κ0 s * g s)))
    {K : ℝ → ℂ → ℂ}
    (hK : ContinuousOn (fun p : ℝ × ℂ => K p.1 p.2) (Icc 0 T ×ˢ closedBall (0:ℂ) R)) :
    TendstoUniformlyOn (fun (j : ℕ) (p : ℝ × ℂ) => ∫ s in (0:ℝ)..p.1, (κ j s - κ0 s) * K s p.2)
      (fun _ => (0:ℂ)) atTop (Icc 0 T ×ˢ closedBall (0:ℂ) R) := by
  have hSc : IsCompact (Icc (0:ℝ) T ×ˢ closedBall (0:ℂ) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hgz : ∀ z ∈ closedBall (0:ℂ) R, ContinuousOn (fun s => K s z) (Icc 0 T) :=
    fun z hz => hK.comp (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hz⟩)
  have hκint : ∀ j, IntervalIntegrable (κ j) volume 0 T :=
    fun j => intervalIntegrable_of_sq (hκm j) (hκsq j)
  have hκint0 := intervalIntegrable_of_sq hκm0 hκsq0
  refine uniform_of_equi hSc ?_ ?_
  · intro p hp
    have hg : ContinuousOn (fun s => K s p.2) (Icc 0 p.1) :=
      (hgz p.2 hp.2).mono (Icc_subset_Icc_right hp.1.2)
    have htend := hpair p.1 hp.1.1 _ hg
    have h0 := htend.sub_const (∫ s in (0:ℝ)..p.1, κ0 s * K s p.2)
    rw [sub_self] at h0
    refine h0.congr (fun j => ?_)
    have hi1 := intervalIntegrable_mul_cont hT (hκint j) (hgz p.2 hp.2) hp.1
    have hi2 := intervalIntegrable_mul_cont hT hκint0 (hgz p.2 hp.2) hp.1
    show (∫ s in (0:ℝ)..p.1, κ j s * K s p.2) - (∫ s in (0:ℝ)..p.1, κ0 s * K s p.2) =
      ∫ s in (0:ℝ)..p.1, (κ j s - κ0 s) * K s p.2
    rw [← intervalIntegral.integral_sub hi1 hi2]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  · intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := ql_uniform (K := K) hT hK (Λ := 4 * Λ) (by linarith) hε
    refine ⟨δ, hδ, fun j p hp q hq hpq => ?_⟩
    rw [Prod.dist_eq] at hpq
    have hpq1 := (max_lt_iff.1 hpq).1
    have hpq2 := (max_lt_iff.1 hpq).2
    have hDm : AEStronglyMeasurable (fun s => κ j s - κ0 s) volume := (hκm j).sub hκm0
    have hg : IntervalIntegrable (fun s => 2 * ‖κ j s‖ ^ 2 + 2 * ‖κ0 s‖ ^ 2) volume 0 T :=
      ((hκsq j).const_mul 2).add (hκsq0.const_mul 2)
    have hDsq : IntervalIntegrable (fun s => ‖κ j s - κ0 s‖ ^ 2) volume 0 T := by
      refine hg.mono_fun' (hDm.norm.pow 2).restrict (Filter.Eventually.of_forall fun s => ?_)
      show ‖‖κ j s - κ0 s‖ ^ 2‖ ≤ _
      rw [norm_pow, norm_norm]
      exact norm_sub_sq_le _ _
    have hDΛ : (∫ s in (0:ℝ)..T, ‖κ j s - κ0 s‖ ^ 2) ≤ 4 * Λ := by
      have h1 : (∫ s in (0:ℝ)..T, ‖κ j s - κ0 s‖ ^ 2) ≤
          ∫ s in (0:ℝ)..T, (2 * ‖κ j s‖ ^ 2 + 2 * ‖κ0 s‖ ^ 2) :=
        intervalIntegral.integral_mono_on hT hDsq hg (fun s _ => norm_sub_sq_le _ _)
      have h2 : (∫ s in (0:ℝ)..T, (2 * ‖κ j s‖ ^ 2 + 2 * ‖κ0 s‖ ^ 2)) =
          2 * (∫ s in (0:ℝ)..T, ‖κ j s‖ ^ 2) + 2 * ∫ s in (0:ℝ)..T, ‖κ0 s‖ ^ 2 := by
        rw [intervalIntegral.integral_add ((hκsq j).const_mul 2) (hκsq0.const_mul 2),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      have h3 := hκΛ j
      linarith
    exact hδ' _ hDm hDsq hDΛ p.1 hp.1 q.1 hq.1 p.2 hp.2 q.2 hq.2
      (by rw [← Real.dist_eq]; exact hpq1) hpq2

theorem abstract_uc
    (a b : ℕ → ℝ → ℂ) (a0 b0 : ℝ → ℂ)
    (hma : ∀ j, AEStronglyMeasurable (a j) volume) (hmb : ∀ j, AEStronglyMeasurable (b j) volume)
    (hma0 : AEStronglyMeasurable a0 volume) (hmb0 : AEStronglyMeasurable b0 volume)
    (hρ : ∀ (j : ℕ) (T : ℝ), 0 ≤ T →
      IntervalIntegrable (fun s => ‖a j s‖ ^ 2 + ‖b j s‖ ^ 2) volume 0 T)
    (hρ0 : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable (fun s => ‖a0 s‖ ^ 2 + ‖b0 s‖ ^ 2) volume 0 T)
    (hΛ : ∀ T : ℝ, 0 ≤ T → ∃ Λ : ℝ,
      (∀ j, (∫ s in (0:ℝ)..T, (‖a j s‖ ^ 2 + ‖b j s‖ ^ 2)) ≤ Λ) ∧
        (∫ s in (0:ℝ)..T, (‖a0 s‖ ^ 2 + ‖b0 s‖ ^ 2)) ≤ Λ)
    (hpa : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, a j s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, a0 s * g s)))
    (hpb : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, b j s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, b0 s * g s)))
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    ∀ i k : Fin 2, TendstoUniformlyOn
      (fun (j : ℕ) (p : ℝ × ℂ) => freeKernelVolterraTerm38 (a j) (b j) p.2 n p.1 i k)
      (fun p : ℝ × ℂ => freeKernelVolterraTerm38 a0 b0 p.2 n p.1 i k) atTop
      (Icc 0 T ×ˢ closedBall (0:ℂ) R) := by
  induction n with
  | zero =>
    intro i k
    have h : (fun (j : ℕ) (p : ℝ × ℂ) => freeKernelVolterraTerm38 (a j) (b j) p.2 0 p.1 i k) =
        fun _ p => freeKernelVolterraTerm38 a0 b0 p.2 0 p.1 i k := by
      funext j p; rfl
    rw [h]
    exact fun u hu => Eventually.of_forall fun j x _ => refl_mem_uniformity hu
  | succ n ih =>
    intro i k
    obtain ⟨Λ, hΛj, hΛ0⟩ := hΛ T hT
    have hΛnn : 0 ≤ Λ :=
      le_trans (intervalIntegral.integral_nonneg hT (fun s _ => by positivity)) hΛ0
    obtain ⟨Eb, hEb⟩ : ∃ Eb : ℝ, Eb = Real.exp (R * T) := ⟨_, rfl⟩
    have hEb0 : 0 < Eb := by rw [hEb]; exact Real.exp_pos _
    have hκm : ∀ j, AEStronglyMeasurable (kap (a j) (b j) i) volume :=
      fun j => kap_aesm (hma j) (hmb j) i
    have hκm0 := kap_aesm hma0 hmb0 i
    have hκsq : ∀ j, IntervalIntegrable (fun s => ‖kap (a j) (b j) i s‖ ^ 2) volume 0 T :=
      fun j => kap_sq_integrable (hma j) (hmb j) (hρ j T hT) i
    have hκsq0 := kap_sq_integrable hma0 hmb0 (hρ0 T hT) i
    have hκΛ : ∀ j, (∫ s in (0:ℝ)..T, ‖kap (a j) (b j) i s‖ ^ 2) ≤ Λ := fun j =>
      (kap_sq_integral_le (hma j) (hmb j) hT (hρ j T hT) i).trans (hΛj j)
    have hκΛ0 : (∫ s in (0:ℝ)..T, ‖kap a0 b0 i s‖ ^ 2) ≤ Λ :=
      (kap_sq_integral_le hma0 hmb0 hT (hρ0 T hT) i).trans hΛ0
    have hκint : ∀ j, IntervalIntegrable (kap (a j) (b j) i) volume 0 T :=
      fun j => intervalIntegrable_of_sq (hκm j) (hκsq j)
    have hκint0 := intervalIntegrable_of_sq hκm0 hκsq0
    have hcont : ∀ j, ∀ z ∈ closedBall (0:ℂ) R,
        ContinuousOn (fun s => freeKernelVolterraTerm38 (a j) (b j) z n s (oth i) k)
          (Icc 0 T) := fun j z hz =>
      (Mn_continuousOn (hma j) (hmb j) (hρ j) n hT R (oth i) k).comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hz⟩)
    have hcont0 : ∀ z ∈ closedBall (0:ℂ) R,
        ContinuousOn (fun s => freeKernelVolterraTerm38 a0 b0 z n s (oth i) k) (Icc 0 T) :=
      fun z hz =>
      (Mn_continuousOn hma0 hmb0 hρ0 n hT R (oth i) k).comp
        (continuousOn_id.prodMk continuousOn_const) (fun s hs => ⟨hs, hz⟩)
    have hephase : ∀ z : ℂ, ContinuousOn (fun s : ℝ => ph z (-s) i) (Icc 0 T) := fun z =>
      ((continuous_ph_neg i).comp (continuous_id.prodMk continuous_const)).continuousOn
    have hU2 := term2_uniform (κ := fun j => kap (a j) (b j) i) (κ0 := kap a0 b0 i)
      (T := T) (R := R) (Λ := Λ) hT hΛnn hκm hκm0 hκsq hκsq0 hκΛ hκΛ0
      (fun t ht g hg => kap_pair hpa hpb i ht hg)
      (K := fun s z => ph z (-s) i * freeKernelVolterraTerm38 a0 b0 z n s (oth i) k)
      ((continuous_ph_neg i).continuousOn.mul
        (Mn_continuousOn hma0 hmb0 hρ0 n hT R (oth i) k))
    have hU1 := term1_small (κ := fun j => kap (a j) (b j) i) (T := T) (R := R) (Λ := Λ)
      (Eb := Eb) hT hEb0 hκm hκsq hκΛ (E := fun s z => ph z (-s) i)
      (fun s hs z hz => by
        rw [hEb]
        exact ph_norm_le_ball hz (by rw [abs_neg, abs_of_nonneg hs.1]; exact hs.2) i)
      (ih (oth i) k)
    refine step_generic (Eb := Eb) hEb0 (ph' := fun p => ph p.2 p.1 i) ?_ ?_ hU1
      (small_of_tendsto_zero hU2)
    · intro j p hp
      rw [Mn_succ, Mn_succ, ← mul_sub]
      congr 1
      exact Idecomp (κj := kap (a j) (b j) i) (κ0 := kap a0 b0 i) (e := fun s => ph p.2 (-s) i)
        (Mj := fun s => freeKernelVolterraTerm38 (a j) (b j) p.2 n s (oth i) k)
        (M0 := fun s => freeKernelVolterraTerm38 a0 b0 p.2 n s (oth i) k)
        hT (hκint j) hκint0 (hephase p.2) (hcont j p.2 hp.2) (hcont0 p.2 hp.2) hp.1
    · intro p hp
      rw [hEb]
      exact ph_norm_le_ball hp.2 (by rw [abs_of_nonneg hp.1.1]; exact hp.1.2) i


/-! ### The pairing functional on the circle potential and the final statement -/

open NlsGge.Pilot

theorem weak_tendsto_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {φs : ℕ → E} {φ : E}
    (h : Tendsto (fun j => toWeakSpace ℂ E (φs j)) atTop (𝓝 (toWeakSpace ℂ E φ)))
    (ℓ : E →L[ℂ] ℂ) : Tendsto (fun j => ℓ (φs j)) atTop (𝓝 (ℓ φ)) := by
  have hc : Continuous (fun x : WeakSpace ℂ E => (topDualPairing ℂ E).flip x ℓ) :=
    WeakBilin.eval_continuous (topDualPairing ℂ E).flip ℓ
  have h2 := (hc.tendsto (toWeakSpace ℂ E φ)).comp h
  exact h2

theorem coverRep_periodic_two (f : PhysicalL2) : Function.Periodic (coverRep38 f) 2 := by
  intro t
  simp only [coverRep38, AddCircle.coe_add, AddCircle.coe_period, add_zero]

theorem coverRep_sq_periodic_two (f : PhysicalL2) :
    Function.Periodic (fun t => ‖coverRep38 f t‖ ^ 2) 2 := by
  intro t
  change ‖coverRep38 f (t + 2)‖ ^ 2 = ‖coverRep38 f t‖ ^ 2
  rw [coverRep_periodic_two f t]

theorem intervalIntegrable_cr_any (f : PhysicalL2) (a b : ℝ) :
    IntervalIntegrable (coverRep38 f) volume a b :=
  (coverRep_periodic_two f).intervalIntegrable₀ (by norm_num)
    (intervalIntegrable_coverRep38_two f) a b

theorem intervalIntegrable_cr_sq_any (f : PhysicalL2) (a b : ℝ) :
    IntervalIntegrable (fun t => ‖coverRep38 f t‖ ^ 2) volume a b :=
  (coverRep_sq_periodic_two f).intervalIntegrable₀ (by norm_num)
    (intervalIntegrable_coverRep38_sq_two f) a b

theorem integral_sq_cover_nat (f : PhysicalL2) (N : ℕ) :
    ∫ s in (0:ℝ)..(2 * (N:ℝ)), ‖coverRep38 f s‖ ^ 2 = N * (2 * ‖f‖ ^ 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_cr_sq_any f 0 (2 * (N:ℝ)))
      (intervalIntegrable_cr_sq_any f (2 * (N:ℝ)) (2 * ((N + 1 : ℕ) : ℝ)))
    have h2 : ∫ s in (2 * (N:ℝ))..(2 * ((N + 1 : ℕ) : ℝ)), ‖coverRep38 f s‖ ^ 2 =
        2 * ‖f‖ ^ 2 := by
      have := (coverRep_sq_periodic_two f).intervalIntegral_add_eq (2 * (N:ℝ)) 0
      rw [show (2 * ((N + 1 : ℕ) : ℝ)) = 2 * (N:ℝ) + 2 by push_cast; ring]
      rw [this, zero_add, integral_sq_coverRep38_two]
    rw [← h1, ih, h2]
    push_cast
    ring

theorem integral_sq_cover_le (f : PhysicalL2) {t : ℝ} (ht : 0 ≤ t) {N : ℕ}
    (hN : t ≤ 2 * (N:ℝ)) :
    ∫ s in (0:ℝ)..t, ‖coverRep38 f s‖ ^ 2 ≤ N * (2 * ‖f‖ ^ 2) := by
  rw [← integral_sq_cover_nat f N]
  exact intervalIntegral.integral_mono_interval le_rfl ht hN
    (Filter.Eventually.of_forall fun s => (sq_nonneg ‖coverRep38 f s‖ : (0:ℝ) ≤ ‖coverRep38 f s‖ ^ 2))
    (intervalIntegrable_cr_sq_any f 0 (2 * (N:ℝ)))

theorem integral_norm_cover_le (f : PhysicalL2) {t : ℝ} (ht : 0 ≤ t) {N : ℕ}
    (hN : t ≤ 2 * (N:ℝ)) :
    ∫ s in (0:ℝ)..t, ‖coverRep38 f s‖ ≤ Real.sqrt t * (Real.sqrt (2 * N) * ‖f‖) := by
  have h := NlsGge.GK38.integral_norm_le_sqrt_mul ht
    (stronglyMeasurable_coverRep38 f).aestronglyMeasurable (intervalIntegrable_cr_sq_any f 0 t)
  rw [sub_zero] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
  calc Real.sqrt (∫ s in (0:ℝ)..t, ‖coverRep38 f s‖ ^ 2)
      ≤ Real.sqrt ((N:ℝ) * (2 * ‖f‖ ^ 2)) := Real.sqrt_le_sqrt (integral_sq_cover_le f ht hN)
    _ = Real.sqrt (2 * N) * ‖f‖ := by
        rw [show (N:ℝ) * (2 * ‖f‖ ^ 2) = (2 * N) * ‖f‖ ^ 2 by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

/-- The continuous linear functional `f ↦ ∫₀ᵗ f(s) g(s) ds` on the circle `L²`, `f` read through its
period-one representative `coverRep38`. -/
def pairL (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : t ≤ 2 * (N:ℝ)) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc 0 t)) (G : ℝ) (hG : ∀ s ∈ Icc (0:ℝ) t, ‖g s‖ ≤ G) :
    PhysicalL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ s in (0:ℝ)..t, coverRep38 f s * g s
      map_add' := fun f f' => by
        have h1 : IntervalIntegrable (fun s => coverRep38 f s * g s) volume 0 t :=
          (intervalIntegrable_cr_any f 0 t).mul_continuousOn
            (by rw [Set.uIcc_of_le ht]; exact hg)
        have h2 : IntervalIntegrable (fun s => coverRep38 f' s * g s) volume 0 t :=
          (intervalIntegrable_cr_any f' 0 t).mul_continuousOn
            (by rw [Set.uIcc_of_le ht]; exact hg)
        show (∫ s in (0:ℝ)..t, coverRep38 (f + f') s * g s) =
          (∫ s in (0:ℝ)..t, coverRep38 f s * g s) + ∫ s in (0:ℝ)..t, coverRep38 f' s * g s
        rw [← intervalIntegral.integral_add h1 h2]
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [coverRep38_add_ae f f'] with s hs _
        rw [hs]; ring
      map_smul' := fun c f => by
        show (∫ s in (0:ℝ)..t, coverRep38 (c • f) s * g s) =
          (RingHom.id ℂ) c • ∫ s in (0:ℝ)..t, coverRep38 f s * g s
        rw [RingHom.id_apply, smul_eq_mul, ← intervalIntegral.integral_const_mul]
        refine intervalIntegral.integral_congr_ae ?_
        filter_upwards [coverRep38_smul_ae c f] with s hs _
        rw [hs]; ring }
    (G * (Real.sqrt t * Real.sqrt (2 * N))) (fun f => by
      have hG0 : 0 ≤ G := le_trans (norm_nonneg _) (hG 0 ⟨le_rfl, ht⟩)
      show ‖∫ s in (0:ℝ)..t, coverRep38 f s * g s‖ ≤ _
      calc ‖∫ s in (0:ℝ)..t, coverRep38 f s * g s‖
          ≤ ∫ s in (0:ℝ)..t, G * ‖coverRep38 f s‖ := by
            refine intervalIntegral.norm_integral_le_of_norm_le ht ?_
              (((intervalIntegrable_cr_any f 0 t).norm).const_mul G)
            refine Filter.Eventually.of_forall fun s hs => ?_
            rw [norm_mul]
            calc ‖coverRep38 f s‖ * ‖g s‖ ≤ ‖coverRep38 f s‖ * G :=
                  mul_le_mul_of_nonneg_left (hG s ⟨hs.1.le, hs.2⟩) (norm_nonneg _)
              _ = G * ‖coverRep38 f s‖ := mul_comm _ _
        _ = G * ∫ s in (0:ℝ)..t, ‖coverRep38 f s‖ := intervalIntegral.integral_const_mul _ _
        _ ≤ G * (Real.sqrt t * (Real.sqrt (2 * N) * ‖f‖)) :=
            mul_le_mul_of_nonneg_left (integral_norm_cover_le f ht hN) hG0
        _ = G * (Real.sqrt t * Real.sqrt (2 * N)) * ‖f‖ := by ring)

theorem pairL_apply (t : ℝ) (ht : 0 ≤ t) (N : ℕ) (hN : t ≤ 2 * (N:ℝ)) (g : ℝ → ℂ)
    (hg : ContinuousOn g (Icc 0 t)) (G : ℝ) (hG : ∀ s ∈ Icc (0:ℝ) t, ‖g s‖ ≤ G)
    (f : PhysicalL2) :
    pairL t ht N hN g hg G hG f = ∫ s in (0:ℝ)..t, coverRep38 f s * g s := rfl

theorem pot_pair_fst (φs : ℕ → PotPair) (φ : PotPair)
    (hw : Tendsto (fun j : ℕ => toWeakSpace ℂ PotPair (φs j)) atTop
      (𝓝 (toWeakSpace ℂ PotPair φ)))
    {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 t)) :
    Tendsto (fun j => ∫ s in (0:ℝ)..t, coverRep38 (φs j).1 s * g s) atTop
      (𝓝 (∫ s in (0:ℝ)..t, coverRep38 φ.1 s * g s)) := by
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn hg
  have hN : t ≤ 2 * ((⌈t / 2⌉₊ : ℕ) : ℝ) := by
    have := Nat.le_ceil (t / 2)
    linarith
  let ℓ : PotPair →L[ℂ] ℂ :=
    (pairL t ht ⌈t / 2⌉₊ hN g hg G hG).comp (ContinuousLinearMap.fst ℂ PhysicalL2 PhysicalL2)
  exact weak_tendsto_apply hw ℓ

theorem pot_pair_snd (φs : ℕ → PotPair) (φ : PotPair)
    (hw : Tendsto (fun j : ℕ => toWeakSpace ℂ PotPair (φs j)) atTop
      (𝓝 (toWeakSpace ℂ PotPair φ)))
    {t : ℝ} (ht : 0 ≤ t) {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 t)) :
    Tendsto (fun j => ∫ s in (0:ℝ)..t, coverRep38 (φs j).2 s * g s) atTop
      (𝓝 (∫ s in (0:ℝ)..t, coverRep38 φ.2 s * g s)) := by
  obtain ⟨G, hG⟩ := (isCompact_Icc (a := (0:ℝ)) (b := t)).exists_bound_of_continuousOn hg
  have hN : t ≤ 2 * ((⌈t / 2⌉₊ : ℕ) : ℝ) := by
    have := Nat.le_ceil (t / 2)
    linarith
  let ℓ : PotPair →L[ℂ] ℂ :=
    (pairL t ht ⌈t / 2⌉₊ hN g hg G hG).comp (ContinuousLinearMap.snd ℂ PhysicalL2 PhysicalL2)
  exact weak_tendsto_apply hw ℓ

theorem g1008_full :
    ∀ (n : ℕ) (φs : ℕ → NlsGge.GK38.PotPair) (φ : NlsGge.GK38.PotPair),
      (∃ C : ℝ, ∀ j : ℕ, Real.sqrt (‖(φs j).1‖ ^ 2 + ‖(φs j).2‖ ^ 2) ≤ C) →
      Filter.Tendsto (fun j : ℕ => toWeakSpace ℂ NlsGge.GK38.PotPair (φs j)) Filter.atTop
        (nhds (toWeakSpace ℂ NlsGge.GK38.PotPair φ)) →
      ∀ B : Set (ℝ × ℂ), B ⊆ {p : ℝ × ℂ | 0 ≤ p.1} → Bornology.IsBounded B →
        TendstoUniformlyOn
          (fun (j : ℕ) (p : ℝ × ℂ) =>
            NlsGge.Atomic.Volterra.potentialVolterraTerm38 (φs j) p.2 n p.1)
          (fun p : ℝ × ℂ => NlsGge.Atomic.Volterra.potentialVolterraTerm38 φ p.2 n p.1)
          Filter.atTop B := by
  intro n φs φ hbd hw B hB0 hBb
  obtain ⟨C, hC⟩ := hbd
  obtain ⟨r, hr⟩ := hBb.subset_closedBall (0 : ℝ × ℂ)
  obtain ⟨T, hT, hTr⟩ : ∃ T : ℝ, 0 ≤ T ∧ r ≤ T := ⟨max r 0, le_max_right _ _, le_max_left _ _⟩
  have hBsub : B ⊆ Icc 0 T ×ˢ closedBall (0:ℂ) T := by
    intro p hp
    have h1 : ‖p‖ ≤ r := by simpa using hr hp
    have h2 : ‖p.1‖ ≤ r := (le_max_left _ _).trans (by rw [← Prod.norm_def]; exact h1)
    have h3 : ‖p.2‖ ≤ r := (le_max_right _ _).trans (by rw [← Prod.norm_def]; exact h1)
    refine ⟨⟨hB0 hp, ?_⟩, ?_⟩
    · have := (le_abs_self p.1).trans (by simpa using h2)
      linarith
    · simpa using h3.trans hTr
  have hC0 : 0 ≤ C := le_trans (Real.sqrt_nonneg _) (hC 0)
  have hsumC : ∀ j, ‖(φs j).1‖ ^ 2 + ‖(φs j).2‖ ^ 2 ≤ C ^ 2 := fun j =>
    ((Real.sqrt_le_iff).1 (hC j)).2
  have hma : ∀ j, AEStronglyMeasurable (fun s => potRepFst38 (φs j) s) volume := fun j =>
    (stronglyMeasurable_coverRep38 (φs j).1).aestronglyMeasurable
  have hmb : ∀ j, AEStronglyMeasurable (fun s => potRepSnd38 (φs j) s) volume := fun j =>
    (stronglyMeasurable_coverRep38 (φs j).2).aestronglyMeasurable
  have hma0 : AEStronglyMeasurable (fun s => potRepFst38 φ s) volume :=
    (stronglyMeasurable_coverRep38 φ.1).aestronglyMeasurable
  have hmb0 : AEStronglyMeasurable (fun s => potRepSnd38 φ s) volume :=
    (stronglyMeasurable_coverRep38 φ.2).aestronglyMeasurable
  have hρ : ∀ (j : ℕ) (T : ℝ), 0 ≤ T → IntervalIntegrable
      (fun s => ‖potRepFst38 (φs j) s‖ ^ 2 + ‖potRepSnd38 (φs j) s‖ ^ 2) volume 0 T :=
    fun j T _ => (intervalIntegrable_cr_sq_any (φs j).1 0 T).add
      (intervalIntegrable_cr_sq_any (φs j).2 0 T)
  have hρ0 : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable
      (fun s => ‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2) volume 0 T :=
    fun T _ => (intervalIntegrable_cr_sq_any φ.1 0 T).add (intervalIntegrable_cr_sq_any φ.2 0 T)
  have hΛ : ∀ T : ℝ, 0 ≤ T → ∃ Λ : ℝ,
      (∀ j, (∫ s in (0:ℝ)..T,
        (‖potRepFst38 (φs j) s‖ ^ 2 + ‖potRepSnd38 (φs j) s‖ ^ 2)) ≤ Λ) ∧
      (∫ s in (0:ℝ)..T, (‖potRepFst38 φ s‖ ^ 2 + ‖potRepSnd38 φ s‖ ^ 2)) ≤ Λ := by
    intro T hT
    have hN : T ≤ 2 * ((⌈T / 2⌉₊ : ℕ) : ℝ) := by
      have := Nat.le_ceil (T / 2)
      linarith
    have hN0 : (0:ℝ) ≤ ((⌈T / 2⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
    have key : ∀ ψ : PotPair, (∫ s in (0:ℝ)..T,
        (‖potRepFst38 ψ s‖ ^ 2 + ‖potRepSnd38 ψ s‖ ^ 2)) ≤
        2 * ((⌈T / 2⌉₊ : ℕ) : ℝ) * (‖ψ.1‖ ^ 2 + ‖ψ.2‖ ^ 2) := by
      intro ψ
      have hsplit : (∫ s in (0:ℝ)..T, (‖potRepFst38 ψ s‖ ^ 2 + ‖potRepSnd38 ψ s‖ ^ 2)) =
          (∫ s in (0:ℝ)..T, ‖coverRep38 ψ.1 s‖ ^ 2) +
            ∫ s in (0:ℝ)..T, ‖coverRep38 ψ.2 s‖ ^ 2 :=
        intervalIntegral.integral_add (intervalIntegrable_cr_sq_any ψ.1 0 T)
          (intervalIntegrable_cr_sq_any ψ.2 0 T)
      have h1 := integral_sq_cover_le ψ.1 hT hN
      have h2 := integral_sq_cover_le ψ.2 hT hN
      rw [hsplit]
      nlinarith
    refine ⟨2 * ((⌈T / 2⌉₊ : ℕ) : ℝ) * (C ^ 2 + ‖φ.1‖ ^ 2 + ‖φ.2‖ ^ 2), fun j => ?_, ?_⟩
    · refine (key (φs j)).trans ?_
      have := hsumC j
      have h3 : 0 ≤ 2 * ((⌈T / 2⌉₊ : ℕ) : ℝ) := by positivity
      nlinarith [sq_nonneg ‖φ.1‖, sq_nonneg ‖φ.2‖]
    · refine (key φ).trans ?_
      have h3 : 0 ≤ 2 * ((⌈T / 2⌉₊ : ℕ) : ℝ) := by positivity
      nlinarith [sq_nonneg C, sq_nonneg ‖φ.1‖, sq_nonneg ‖φ.2‖]
  have hpa : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, potRepFst38 (φs j) s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, potRepFst38 φ s * g s)) :=
    fun t ht g hg => pot_pair_fst φs φ hw ht hg
  have hpb : ∀ t : ℝ, 0 ≤ t → ∀ g : ℝ → ℂ, ContinuousOn g (Icc 0 t) →
      Tendsto (fun j => ∫ s in (0:ℝ)..t, potRepSnd38 (φs j) s * g s) atTop
        (𝓝 (∫ s in (0:ℝ)..t, potRepSnd38 φ s * g s)) :=
    fun t ht g hg => pot_pair_snd φs φ hw ht hg
  have hmain := fun i k => abstract_uc (fun j => potRepFst38 (φs j)) (fun j => potRepSnd38 (φs j))
    (potRepFst38 φ) (potRepSnd38 φ) hma hmb hma0 hmb0 hρ hρ0 hΛ hpa hpb n hT T i k
  exact (tendstoUniformlyOn_matrix_of (fun i k => hmain i k)).mono hBsub

end NlsGge.Atomic.G1008
