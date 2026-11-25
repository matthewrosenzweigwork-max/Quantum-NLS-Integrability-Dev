import QuantumNLS.Ext025A6LocalImage

/-! LOCAL-018, source `symplectic_correction.tex:298`. The global argument
is adapted from the accepted application Ext025A8Modulus, while only the
accepted GP-03 local inverse and open-image interfaces are imported here.
The norm identity is the source hypothesis; no mass identity is assumed.
The source uses neither the LOCAL-022 chart-uniqueness nor LOCAL-011 placement
interfaces in this lemma. -/

/-! LOCAL-018 on the full Banach ball. The source norm identity and
derivative margin imply global bijectivity; the inverse regularity is
derived by identifying the global selection with each proved local inverse. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Local018ModulusImage
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem modulus_lower {f : E → E} {R ε : ℝ}
    (hf : ∀ x ∈ ball (0 : E) R, AnalyticAt ℝ f x)
    (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ f x - 1‖ ≤ ε)
    {x y : E} (hx : x ∈ ball (0 : E) R) (hy : y ∈ ball (0 : E) R) :
    (1 - ε) * ‖y - x‖ ≤ ‖f y - f x‖ := by
  have hb : ‖(f y - y) - (f x - x)‖ ≤ ε * ‖y - x‖ :=
    (convex_ball (0 : E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => ((hf z hz).differentiableAt.hasFDerivAt.sub
        (hasFDerivAt_id z)).hasFDerivWithinAt) hD hx hy
  have ht := norm_sub_le (f y - f x) ((f y - y) - (f x - x))
  rw [show f y - f x - ((f y - y) - (f x - x)) = y - x by abel] at ht
  nlinarith

theorem modulus_surjective {f : E → E} {R ε : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ ball (0 : E) R, AnalyticAt ℝ f x)
    (hn : ∀ x ∈ ball (0 : E) R, ‖f x‖ = ‖x‖)
    (hε : ε < 1) (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ f x - 1‖ ≤ ε) :
    f '' ball (0 : E) R = ball (0 : E) R := by
  classical
  let B := ball (0 : E) R
  have hm : MapsTo f B B := by
    intro x hx
    change f x ∈ ball (0 : E) R
    rw [mem_ball_zero_iff, hn x hx]
    exact mem_ball_zero_iff.mp hx
  let F : B → B := fun x => ⟨f x, hm x.property⟩
  have hclosed : IsClosed (range F) := by
    apply IsSeqClosed.isClosed
    intro u z hu hz
    choose v hv using hu
    have hvlim : Tendsto (fun n => f (v n : E)) atTop (𝓝 (z : E)) := by
      have hh := continuous_subtype_val.tendsto z |>.comp hz
      apply hh.congr'
      exact Filter.Eventually.of_forall (fun n => (congrArg Subtype.val (hv n)).symm)
    have hc : CauchySeq (fun n => (v n : E)) := by
      rw [Metric.cauchySeq_iff]
      intro δ hδ
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hvlim.cauchySeq
        (δ * (1 - ε)) (mul_pos hδ (sub_pos.mpr hε))
      refine ⟨N, fun m hm n hn => ?_⟩
      have hb := modulus_lower hf hD (v n).property (v m).property
      have hd := hN m hm n hn
      rw [dist_eq_norm] at hd ⊢
      nlinarith [sub_pos.mpr hε]
    obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hc
    have hnorm : ‖x‖ = ‖(z : E)‖ := by
      apply tendsto_nhds_unique (continuous_norm.tendsto x |>.comp hx)
      have hh := continuous_norm.tendsto (z : E) |>.comp hvlim
      have hn_eq : (fun n => ‖f (v n : E)‖) = (fun n => ‖(v n : E)‖) :=
        funext (fun n => hn _ (v n).property)
      change Tendsto (fun n => ‖f (v n : E)‖) atTop (𝓝 ‖(z : E)‖) at hh
      rw [hn_eq] at hh
      exact hh
    have hxB : x ∈ B := by
      rw [mem_ball_zero_iff, hnorm]
      exact mem_ball_zero_iff.mp z.property
    have hfx : f x = z := tendsto_nhds_unique
      ((hf x hxB).continuousAt.tendsto.comp hx) hvlim
    exact ⟨⟨x, hxB⟩, Subtype.ext hfx⟩
  have hopen : IsOpen (range F) := by
    have heq : range F = Subtype.val ⁻¹' (f '' B) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
      · rintro ⟨x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    rw [heq]
    exact (QuantumNLS.Ext025A6.local018_open_image hf hε hD).preimage
      continuous_subtype_val
  let : PreconnectedSpace B := Subtype.preconnectedSpace (convex_ball (0 : E) R).isPreconnected
  have hall : range F = univ := (show IsClopen (range F) from ⟨hclosed, hopen⟩).eq_univ
    ⟨F ⟨0, mem_ball_self hR⟩, mem_range_self _⟩
  apply Subset.antisymm (image_subset_iff.mpr hm)
  intro y hy
  obtain ⟨x, hx⟩ := hall.symm ▸ (mem_univ (⟨y, hy⟩ : B))
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- Literal LOCAL-018 application. No inverse, onto property, lower
Lipschitz estimate or inverse differential is supplied as a premise. -/
theorem reset_modulus_image {f : E → E} {R ε : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ ball (0 : E) R, AnalyticAt ℝ f x)
    (hn : ∀ x ∈ ball (0 : E) R, ‖f x‖ = ‖x‖)
    (hε : ε < 1) (hD : ∀ x ∈ ball (0 : E) R, ‖fderiv ℝ f x - 1‖ ≤ ε) :
    f 0 = 0 ∧
    (∀ x ∈ ball (0 : E) R, ‖f x‖ = ‖x‖) ∧
    (∀ x ∈ ball (0 : E) R, ∀ y ∈ ball (0 : E) R,
      ‖f y - f x - (y - x)‖ ≤ ε * ‖y - x‖) ∧
    InjOn f (ball (0 : E) R) ∧
    IsClosed ((Subtype.val : ball (0 : E) R → E) ⁻¹' (f '' ball (0 : E) R)) ∧
    ∃ g : E → E, f '' ball (0 : E) R = ball (0 : E) R ∧
      (∀ x ∈ ball (0 : E) R, g (f x) = x) ∧
      (∀ y ∈ ball (0 : E) R, g y ∈ ball (0 : E) R ∧ f (g y) = y ∧
        AnalyticAt ℝ g y ∧ HasFDerivAt g (fderiv ℝ f (g y)).inverse y ∧
        ‖(fderiv ℝ f (g y)).inverse‖ ≤ (1 - ε)⁻¹) := by
  classical
  have honto := modulus_surjective hR hf hn hε hD
  have hinj : InjOn f (ball (0 : E) R) := by
    intro x hx y hy heq
    have hb := modulus_lower hf hD hx hy
    rw [heq, sub_self, norm_zero] at hb
    have : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x), sub_pos.mpr hε]
    exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm
  have hex (y : E) (hy : y ∈ ball (0 : E) R) :
      ∃ x ∈ ball (0 : E) R, f x = y := by
    have hmem : y ∈ f '' ball (0 : E) R := by rw [honto]; exact hy
    exact hmem
  let g : E → E := fun y => if hy : y ∈ ball (0 : E) R then
    (hex y hy).choose else 0
  have hg (y : E) (hy : y ∈ ball (0 : E) R) :
      g y ∈ ball (0 : E) R ∧ f (g y) = y := by
    simpa only [g, dite_eq_left hy] using (hex y hy).choose_spec
  have hl (x : E) (hx : x ∈ ball (0 : E) R) : g (f x) = x := by
    have hm : f x ∈ ball (0 : E) R := by
      simpa only [mem_ball_zero_iff, hn x hx] using hx
    exact hinj (hg _ hm).1 hx (hg _ hm).2
  have hzero : f 0 = 0 := by
    apply norm_eq_zero.mp
    simpa using hn 0 (mem_ball_self hR)
  have hsegment : ∀ x ∈ ball (0 : E) R, ∀ y ∈ ball (0 : E) R,
      ‖f y - f x - (y - x)‖ ≤ ε * ‖y - x‖ := by
    intro x hx y hy
    have hb : ‖(f y - y) - (f x - x)‖ ≤ ε * ‖y - x‖ :=
      (convex_ball (0 : E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((hf z hz).differentiableAt.hasFDerivAt.sub
          (hasFDerivAt_id z)).hasFDerivWithinAt) hD hx hy
    convert hb using 1; congr 1; abel
  have hclosed : IsClosed ((Subtype.val : ball (0 : E) R → E) ⁻¹'
      (f '' ball (0 : E) R)) := by
    rw [honto]
    have : ((Subtype.val : ball (0 : E) R → E) ⁻¹' ball (0 : E) R) = univ := by
      ext x
      simp
    rw [this]
    exact isClosed_univ
  refine ⟨hzero, hn, hsegment, hinj, hclosed, g, honto, hl, fun y hy => ?_⟩
  obtain ⟨k, hk, hky, hdk, hbk, _, hkr⟩ :=
    QuantumNLS.Ext025A6.local018_analytic_inverse (hg y hy).1 hf hε hD
  rw [(hg y hy).2] at hk hky hdk hkr
  have heq : g =ᶠ[𝓝 y] k := by
    filter_upwards [hkr, (hk.continuousAt.tendsto.eventually
      (isOpen_ball.mem_nhds ((hky.symm ▸ (hg y hy).1) : k y ∈ ball (0 : E) R)))]
      with z hz hzk
    calc
      g z = g (f (k z)) := congrArg g hz.symm
      _ = k z := hl _ hzk
  exact ⟨(hg y hy).1, (hg y hy).2, hk.congr heq.symm,
    hdk.congr_of_eventuallyEq heq, hbk⟩
end QuantumNLS.Local018ModulusImage

#print axioms QuantumNLS.Local018ModulusImage.modulus_lower
#print axioms QuantumNLS.Local018ModulusImage.modulus_surjective
#print axioms QuantumNLS.Local018ModulusImage.reset_modulus_image

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Local018ModulusImage." then
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
  Lean.logInfo m!"Local018ModulusImage audit PASS: {roots} namespace constants; {seen.size} transitive constants; standard only."
