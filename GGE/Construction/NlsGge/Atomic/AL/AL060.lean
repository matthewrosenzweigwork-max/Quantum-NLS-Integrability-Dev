import NlsGge.Hierarchy.ALSampling38

namespace NlsGge.Atomic.AL060

open NlsGge.AblowitzLadik NlsGge.Pilot MeasureTheory Filter Topology Set

noncomputable def alCellLeft38 (N : ℕ) (x : ℝ) : ℝ :=
  (Int.floor (x / alh38 N) : ℝ) * alh38 N

noncomputable def alForwardStep38 (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (f (alCellLeft38 N x + alh38 N) - f (alCellLeft38 N x)) /
    (alh38 N : ℂ)

noncomputable def alBackwardStep38 (N : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (f (alCellLeft38 N x) - f (alCellLeft38 N x - alh38 N)) /
    (alh38 N : ℂ)

theorem alCellLeft_bounds38 (N : ℕ) (x : ℝ) :
    alCellLeft38 N x ≤ x ∧ x - alCellLeft38 N x < alh38 N := by
  have hpos := alh38_pos N
  have h1 := Int.floor_le (x / alh38 N)
  have h2 := Int.lt_floor_add_one (x / alh38 N)
  unfold alCellLeft38
  constructor
  · have : (Int.floor (x / alh38 N) : ℝ) ≤ x / alh38 N := h1
    rw [le_div_iff₀ hpos] at this
    linarith
  · have : x / alh38 N < (Int.floor (x / alh38 N) : ℝ) + 1 := h2
    rw [div_lt_iff₀ hpos] at this
    nlinarith

theorem alDifferenceStep_sample38 (N : ℕ)
    (x : SobolevHilbert 1) (j : ZMod (2 * N + 1))
    (s : ℝ) (hs : s ∈ Ico (alt38 N j) (alt38 N j + alh38 N)) :
    alForwardStep38 N (alCanon38 x) s = alFd38 N x j ∧
    alBackwardStep38 N (alCanon38 x) s = alBd38 N x j := by
  have hpos := alh38_pos N
  obtain ⟨hs1, hs2⟩ := hs
  have hfloor : Int.floor (s / alh38 N) = ((j.val : ℕ) : ℤ) := by
    rw [Int.floor_eq_iff]
    constructor
    · unfold alt38 at hs1
      rw [le_div_iff₀ hpos]
      push_cast
      linarith
    · unfold alt38 at hs2
      rw [div_lt_iff₀ hpos]
      push_cast
      have e : ((j.val : ℝ) + 1) * alh38 N = (j.val : ℝ) * alh38 N + alh38 N := by ring
      linarith
  have hcell : alCellLeft38 N s = alt38 N j := by
    unfold alCellLeft38 alt38
    rw [hfloor]
    push_cast
    ring
  constructor
  · unfold alForwardStep38 alFd38
    rw [hcell]
  · unfold alBackwardStep38 alBd38
    rw [hcell]

theorem fixedModes_eventually_small38 (M : ℕ) :
    ∀ᶠ N : ℕ in atTop, M ≤ N ∧
      ∀ i : Fin (2 * M + 1),
        |2 * Real.pi * (modeIndex M i : ℝ) * alh38 N| ≤ 1 := by
  have hlim : ∀ i : Fin (2 * M + 1), ∀ᶠ N : ℕ in atTop,
      |2 * Real.pi * (modeIndex M i : ℝ) * alh38 N| ≤ 1 := by
    intro i
    have ht : Tendsto (fun N : ℕ => 2 * Real.pi * (modeIndex M i : ℝ) * alh38 N) atTop (𝓝 0) := by
      simpa using alh_tendsto38.const_mul (2 * Real.pi * (modeIndex M i : ℝ))
    have habs : Tendsto (fun N : ℕ => |2 * Real.pi * (modeIndex M i : ℝ) * alh38 N|) atTop (𝓝 0) := by
      simpa using ht.abs
    exact (habs.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))).mono fun N hN => le_of_lt hN
  have hall : ∀ᶠ N : ℕ in atTop, ∀ i : Fin (2 * M + 1),
      |2 * Real.pi * (modeIndex M i : ℝ) * alh38 N| ≤ 1 :=
    Filter.eventually_all.2 hlim
  exact ((eventually_ge_atTop M).and hall).mono fun N hN => ⟨hN.1, hN.2⟩

theorem eLpNorm_two_le_uniform_unitInterval
    (f : ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)), ‖f x‖ ≤ C) :
    eLpNorm f 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ≤ ENNReal.ofReal C := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  refine (eLpNorm_le_of_ae_bound hf hb).trans ?_
  simp [Real.volume_Ioc]


theorem derivativePlane_term_lipschitz38 (M : ℕ) (z : FourierPlane M) (i : Fin (2 * M + 1))
    (s t : ℝ) :
    ‖derivativePlane M z i * Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (s : ℂ)) -
      derivativePlane M z i * Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ))‖ ≤
      |s - t| * (‖z i‖ * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|) ^ 2) := by
  set k : ℤ := modeIndex M i with hk
  have hcoef : derivativePlane M z i = z i * (2 * Real.pi * Complex.I * (k : ℂ)) := rfl
  rw [hcoef]
  have hE : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) *
        (Complex.exp (Complex.I * ((2 * Real.pi * k * (s - t) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : z i * (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)) -
      z i * (2 * Real.pi * Complex.I * (k : ℂ)) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) =
      (z i * (2 * Real.pi * Complex.I * (k : ℂ))) *
        (Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)) *
          (Complex.exp (Complex.I * ((2 * Real.pi * k * (s - t) : ℝ) : ℂ)) - 1)) := by
    rw [← hE]; ring
  have hEt : ‖Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))‖ = 1 := by
    have e : 2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ) =
        Complex.I * ((2 * Real.pi * k * t : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_exp_I_mul_ofReal]
  have hc : ‖2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)‖ = 2 * Real.pi * |(k : ℝ)| := by
    have e : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = Complex.I * ((2 * Real.pi * k : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hx : ‖Complex.exp (Complex.I * ((2 * Real.pi * k * (s - t) : ℝ) : ℂ)) - 1‖ ≤
      2 * Real.pi * |(k : ℝ)| * |s - t| := by
    have h1 : ‖Complex.exp (Complex.I * ((2 * Real.pi * k * (s - t) : ℝ) : ℂ)) - 1‖ ≤
        ‖(2 * Real.pi * k * (s - t) : ℝ)‖ := by
      first
        | exact Real.norm_exp_I_mul_ofReal_sub_one_le
        | exact Complex.norm_exp_I_mul_ofReal_sub_one_le
    have h2 : ‖(2 * Real.pi * k * (s - t) : ℝ)‖ = 2 * Real.pi * |(k : ℝ)| * |s - t| := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    linarith
  have hcoefn : ‖z i * (2 * Real.pi * Complex.I * (k : ℂ))‖ = ‖z i‖ * (2 * Real.pi * |(k : ℝ)|) := by
    rw [norm_mul, hc]
  rw [e2, norm_mul, hcoefn, norm_mul, hEt, one_mul]
  calc ‖z i‖ * (2 * Real.pi * |(k : ℝ)|) * ‖Complex.exp (Complex.I * ((2 * Real.pi * k * (s - t) : ℝ) : ℂ)) - 1‖
      ≤ ‖z i‖ * (2 * Real.pi * |(k : ℝ)|) * (2 * Real.pi * |(k : ℝ)| * |s - t|) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = |s - t| * (‖z i‖ * (2 * Real.pi * |(k : ℝ)|) ^ 2) := by ring

theorem derivativePlaneReal_lipschitz38 (M : ℕ) (z : FourierPlane M) (s t : ℝ) :
    ‖planeReal M (derivativePlane M z) s - planeReal M (derivativePlane M z) t‖ ≤
      |s - t| * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |((modeIndex M i : ℤ) : ℝ)|) ^ 2 := by
  rw [planeReal_eq38, planeReal_eq38, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  exact derivativePlane_term_lipschitz38 M z i s t

theorem fixedTrigPolynomial_step_error38
    (M : ℕ) (z : FourierPlane M) (N : ℕ)
    (hMN : ∀ i : Fin (2 * M + 1), |2 * Real.pi * (modeIndex M i : ℝ) * alh38 N| ≤ 1)
    (x : ℝ) :
    ‖alForwardStep38 N (planeReal M z) x - planeReal M (derivativePlane M z) x‖ ≤
      2 * alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 ∧
    ‖alBackwardStep38 N (planeReal M z) x - planeReal M (derivativePlane M z) x‖ ≤
      2 * alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 := by
  have hpos : 0 < alh38 N := alh38_pos N
  have hS0 : 0 ≤ ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨hcx, hxc⟩ := alCellLeft_bounds38 N x
  have hdist : |alCellLeft38 N x - x| ≤ alh38 N := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have hlip : ‖planeReal M (derivativePlane M z) (alCellLeft38 N x) -
      planeReal M (derivativePlane M z) x‖ ≤
      alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 :=
    (derivativePlaneReal_lipschitz38 M z _ x).trans
      (mul_le_mul_of_nonneg_right hdist hS0)
  constructor
  · have hc1 := alPlaneFwdErr38 M z (alh38 N) hpos hMN (alCellLeft38 N x)
    have e : alForwardStep38 N (planeReal M z) x - planeReal M (derivativePlane M z) x =
        ((planeReal M z (alCellLeft38 N x + alh38 N) - planeReal M z (alCellLeft38 N x)) /
            (alh38 N : ℂ) - planeReal M (derivativePlane M z) (alCellLeft38 N x)) +
        (planeReal M (derivativePlane M z) (alCellLeft38 N x) - planeReal M (derivativePlane M z) x) := by
      unfold alForwardStep38; ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 +
          alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 :=
          add_le_add hc1 hlip
      _ = 2 * alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 := by
          ring
  · have hc2 := alPlaneBwdErr38 M z (alh38 N) hpos hMN (alCellLeft38 N x)
    have e : alBackwardStep38 N (planeReal M z) x - planeReal M (derivativePlane M z) x =
        ((planeReal M z (alCellLeft38 N x) - planeReal M z (alCellLeft38 N x - alh38 N)) /
            (alh38 N : ℂ) - planeReal M (derivativePlane M z) (alCellLeft38 N x)) +
        (planeReal M (derivativePlane M z) (alCellLeft38 N x) - planeReal M (derivativePlane M z) x) := by
      unfold alBackwardStep38; ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 +
          alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 :=
          add_le_add hc2 hlip
      _ = 2 * alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 := by
          ring

theorem planeReal_continuous38 (M : ℕ) (z : FourierPlane M) : Continuous (planeReal M z) := by
  have hf : planeReal M z = fun t : ℝ => ∑ i : Fin (2 * M + 1),
      z i * Complex.exp (2 * Real.pi * Complex.I * ((modeIndex M i : ℤ) : ℂ) * (t : ℂ)) :=
    funext (planeReal_eq38 M z)
  rw [hf]
  fun_prop

theorem alCellLeft_measurable38 (N : ℕ) : Measurable (alCellLeft38 N) := by
  unfold alCellLeft38
  exact ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (Int.measurable_floor.comp (measurable_id.div_const _))).mul_const _

theorem alForwardStep_measurable38 (M : ℕ) (z : FourierPlane M) (N : ℕ) :
    Measurable (alForwardStep38 N (planeReal M z)) := by
  unfold alForwardStep38
  have hc := alCellLeft_measurable38 N
  have hp := (planeReal_continuous38 M z).measurable
  exact ((hp.comp (hc.add_const _)).sub (hp.comp hc)).div_const _

theorem alBackwardStep_measurable38 (M : ℕ) (z : FourierPlane M) (N : ℕ) :
    Measurable (alBackwardStep38 N (planeReal M z)) := by
  unfold alBackwardStep38
  have hc := alCellLeft_measurable38 N
  have hp := (planeReal_continuous38 M z).measurable
  exact ((hp.comp hc).sub (hp.comp (hc.sub_const _))).div_const _

theorem alStep_bound38 (M : ℕ) (z : FourierPlane M) (N : ℕ) (x : ℝ) :
    ‖alForwardStep38 N (planeReal M z) x‖ ≤ 2 * (∑ i, ‖z i‖) / alh38 N ∧
    ‖alBackwardStep38 N (planeReal M z) x‖ ≤ 2 * (∑ i, ‖z i‖) / alh38 N := by
  have hpos : 0 < alh38 N := alh38_pos N
  have hb : ∀ t, ‖planeReal M z t‖ ≤ ∑ i, ‖z i‖ := fun t => alPlaneNorm_le38 M z t
  constructor
  · unfold alForwardStep38
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    gcongr
    exact (norm_sub_le _ _).trans (by linarith [hb (alCellLeft38 N x + alh38 N), hb (alCellLeft38 N x)])
  · unfold alBackwardStep38
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    gcongr
    exact (norm_sub_le _ _).trans (by linarith [hb (alCellLeft38 N x), hb (alCellLeft38 N x - alh38 N)])

theorem alStep_memLp38 (M : ℕ) (z : FourierPlane M) (N : ℕ) :
    MemLp (alForwardStep38 N (planeReal M z)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) ∧
    MemLp (alBackwardStep38 N (planeReal M z)) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    constructor
    simp
  constructor
  · exact MemLp.of_bound (alForwardStep_measurable38 M z N).aestronglyMeasurable
      (2 * (∑ i, ‖z i‖) / alh38 N)
      (ae_of_all _ fun x => (alStep_bound38 M z N x).1)
  · exact MemLp.of_bound (alBackwardStep_measurable38 M z N).aestronglyMeasurable
      (2 * (∑ i, ‖z i‖) / alh38 N)
      (ae_of_all _ fun x => (alStep_bound38 M z N x).2)

theorem fixedTrigPolynomial_difference_uniform38 (M : ℕ) (z : FourierPlane M) :
    TendstoUniformly (fun N => alForwardStep38 N (planeReal M z))
      (planeReal M (derivativePlane M z)) atTop ∧
    TendstoUniformly (fun N => alBackwardStep38 N (planeReal M z))
      (planeReal M (derivativePlane M z)) atTop := by
  have hS0 : 0 ≤ ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  have hlim : Tendsto (fun N : ℕ => 2 * alh38 N *
      ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2) atTop (𝓝 0) := by
    have := ((alh_tendsto38.const_mul 2).mul_const
      (∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2))
    simpa using this
  refine ⟨Metric.tendstoUniformly_iff.2 fun ε hε => ?_,
    Metric.tendstoUniformly_iff.2 fun ε hε => ?_⟩
  · filter_upwards [hlim.eventually (gt_mem_nhds hε), fixedModes_eventually_small38 M] with N hN hM x
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (fixedTrigPolynomial_step_error38 M z N hM.2 x).1 hN
  · filter_upwards [hlim.eventually (gt_mem_nhds hε), fixedModes_eventually_small38 M] with N hN hM x
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (fixedTrigPolynomial_step_error38 M z N hM.2 x).2 hN

theorem fixedTrigPolynomial_difference_L2_38 (M : ℕ) (z : FourierPlane M) :
    (∀ N : ℕ,
      MemLp (alForwardStep38 N (planeReal M z)) 2
        (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (alBackwardStep38 N (planeReal M z)) 2
        (volume.restrict (Ioc (0 : ℝ) 1))) ∧
    Tendsto
      (fun N => eLpNorm
        (fun x => alForwardStep38 N (planeReal M z) x -
          planeReal M (derivativePlane M z) x)
        2 (volume.restrict (Ioc (0 : ℝ) 1)))
      atTop (𝓝 0) ∧
    Tendsto
      (fun N => eLpNorm
        (fun x => alBackwardStep38 N (planeReal M z) x -
          planeReal M (derivativePlane M z) x)
        2 (volume.restrict (Ioc (0 : ℝ) 1)))
      atTop (𝓝 0) := by
  have hS0 : 0 ≤ ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  have hlim : Tendsto (fun N : ℕ => 2 * alh38 N *
      ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2) atTop (𝓝 0) := by
    have := ((alh_tendsto38.const_mul 2).mul_const
      (∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2))
    simpa using this
  have hEN : Tendsto (fun N : ℕ => ENNReal.ofReal (2 * alh38 N *
      ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hlim
    simpa using this
  have hmeasF : ∀ N : ℕ, AEStronglyMeasurable (fun x => alForwardStep38 N (planeReal M z) x -
      planeReal M (derivativePlane M z) x) (volume.restrict (Ioc (0 : ℝ) 1)) := fun N =>
    ((alForwardStep_measurable38 M z N).sub (planeReal_continuous38 M (derivativePlane M z)).measurable).aestronglyMeasurable
  have hmeasB : ∀ N : ℕ, AEStronglyMeasurable (fun x => alBackwardStep38 N (planeReal M z) x -
      planeReal M (derivativePlane M z) x) (volume.restrict (Ioc (0 : ℝ) 1)) := fun N =>
    ((alBackwardStep_measurable38 M z N).sub (planeReal_continuous38 M (derivativePlane M z)).measurable).aestronglyMeasurable
  refine ⟨fun N => alStep_memLp38 M z N, ?_, ?_⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEN
      (Eventually.of_forall fun N => zero_le) ?_
    filter_upwards [fixedModes_eventually_small38 M] with N hM
    exact eLpNorm_two_le_uniform_unitInterval _ (hmeasF N)
      (2 * alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2)
      (by have := alh38_pos N; positivity)
      (ae_of_all _ fun x => fixedTrigPolynomial_step_error38 M z N hM.2 x |>.1)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEN
      (Eventually.of_forall fun N => zero_le) ?_
    filter_upwards [fixedModes_eventually_small38 M] with N hM
    exact eLpNorm_two_le_uniform_unitInterval _ (hmeasB N)
      (2 * alh38 N * ∑ i : Fin (2 * M + 1), ‖z i‖ * (2 * Real.pi * |(modeIndex M i : ℝ)|) ^ 2)
      (by have := alh38_pos N; positivity)
      (ae_of_all _ fun x => fixedTrigPolynomial_step_error38 M z N hM.2 x |>.2)

end NlsGge.Atomic.AL060
