import Mathlib
import NlsGge.Atomic.M.M009Host
import NlsGge.GK38.IsolatingTopology

                                                                                              
                                                                                                                               
                                                                                                  
                                                                                              
                                                                                                    
                                                                                                    
                                                                                                    
                                                                                            
                                      
set_option autoImplicit false
open Set Filter Metric Relation
open scoped Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.MPrimitive
noncomputable section
namespace Support3Aux

theorem balls_disjoint {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R)
    {k m : ℤ} (hkm : k ≠ m) {z : ℂ} (hk : z ∈ ball (C k) (R k)) (hm : z ∈ ball (C m) (R m)) :
    False := by
  obtain ⟨c, N, ⟨_, _, hc1, hdist, _⟩, _⟩ := hf
  have h1 := (hdist k m hkm).1
  have hpos : 0 < c⁻¹ * |((k - m : ℤ) : ℝ)| := by
    have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
    have : (1 : ℝ) ≤ |((k - m : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |k - m| := Int.one_le_abs (sub_ne_zero.2 hkm)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|k - m| : ℤ) : ℝ) := by exact_mod_cast this
      simpa [Int.cast_abs] using h2
    positivity
  have h2 : ballDistance38 (C k) (C m) (R k) (R m) ≤ 0 := by
    unfold ballDistance38
    apply csInf_le
    · exact ⟨0, by rintro v ⟨a, _, b, _, rfl⟩; exact dist_nonneg⟩
    · exact ⟨z, hk, z, hm, by simp⟩
  linarith

theorem cut_sub_ball {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ}
    (hf : IsolatingFamily38 φ C R) (n : ℤ) :
    segment ℝ (lamMinus φ n) (lamPlus φ n) ⊆ ball (C n) (R n) := by
  obtain ⟨_, _, _, hS⟩ := hf
  exact (hS.1 n).1

theorem dist_real_center {c z : ℂ} (hc : c.im = 0) :
    dist z c = Real.sqrt ((z.re - c.re) ^ 2 + z.im ^ 2) := by
  rw [Complex.dist_eq_re_im, hc]; simp

theorem mem_ball_mono {c z w : ℂ} {r : ℝ} (hc : c.im = 0) (hre : z.re = w.re)
    (him : |z.im| ≤ |w.im|) (hw : w ∈ ball c r) : z ∈ ball c r := by
  rw [mem_ball, dist_real_center hc] at hw ⊢
  refine lt_of_le_of_lt (Real.sqrt_le_sqrt ?_) hw
  rw [hre]
  have : z.im ^ 2 ≤ w.im ^ 2 := by simpa using sq_le_sq.2 him
  linarith

theorem ball_cut {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R)
    {z : ℂ} (hz : z ∈ gapSegments38 φ) : ∃ n, z ∈ ball (C n) (R n) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hz
  exact ⟨n, cut_sub_ball hf n hn⟩

theorem locallyFinite_cuts {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R) :
    LocallyFinite (fun n : ℤ => segment ℝ (lamMinus φ n) (lamPlus φ n)) := by
  intro z0
  have hf0 := hf
  obtain ⟨c, N, ⟨hR, _, hc1, hdist, _⟩, _⟩ := hf
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  refine ⟨ball z0 1, ball_mem_nhds z0 one_pos, ?_⟩
  set D : ℝ := c * (dist (C 0) z0 + 1) with hD
  refine ((Set.finite_Icc (-⌈D⌉) ⌈D⌉).insert 0).subset ?_
  intro n hn
  by_cases h0 : n = 0
  · exact Or.inl h0
  right
  obtain ⟨w, hwseg, hwb⟩ := hn
  have hwball : w ∈ ball (C n) (R n) := cut_sub_ball hf0 n hwseg
  have h1 := (hdist 0 n (Ne.symm h0)).1
  have h2 : ballDistance38 (C 0) (C n) (R 0) (R n) ≤ dist (C 0) w := by
    unfold ballDistance38
    apply csInf_le
    · exact ⟨0, by rintro v ⟨a, _, b, _, rfl⟩; exact dist_nonneg⟩
    · exact ⟨C 0, mem_ball_self (hR 0).1, w, hwball, rfl⟩
  have h3 : dist (C 0) w ≤ dist (C 0) z0 + 1 := by
    have := mem_ball.1 hwb
    have := dist_comm z0 w
    linarith [dist_triangle (C 0) z0 w]
  have h4 : |((n : ℤ) : ℝ)| ≤ D := by
    have : c⁻¹ * |(((0 : ℤ) - n : ℤ) : ℝ)| ≤ dist (C 0) z0 + 1 := h1.trans (h2.trans h3)
    have h5 : |(((0 : ℤ) - n : ℤ) : ℝ)| = |(n : ℝ)| := by simp
    rw [h5] at this
    rw [hD]
    have := (inv_mul_le_iff₀ hc0).1 this
    linarith
  have hn1 : (n : ℝ) ≤ D := (le_abs_self _).trans h4
  have hn2 : -D ≤ (n : ℝ) := by linarith [neg_abs_le (n : ℝ)]
  have hD1 : D ≤ (⌈D⌉ : ℝ) := Int.le_ceil D
  constructor
  · have : (-(⌈D⌉ : ℝ)) ≤ (n : ℝ) := by linarith
    exact_mod_cast this
  · have : (n : ℝ) ≤ (⌈D⌉ : ℝ) := hn1.trans hD1
    exact_mod_cast this

theorem isClosed_cuts {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R) :
    IsClosed (gapSegments38 φ) := by
  refine (locallyFinite_cuts hf).isClosed_iUnion (fun n => ?_)
  rw [segment_eq_image]
  exact (isCompact_Icc.image (by fun_prop)).isClosed

theorem exists_radius_bound {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R) :
    ∃ M : ℝ, ∀ n, R n ≤ M := by
  obtain ⟨c, N, ⟨hR, _, _, _, hN⟩, _⟩ := hf
  obtain ⟨M1, hM1⟩ := ((Set.finite_Icc (-(N : ℤ)) N).image R).bddAbove
  refine ⟨max M1 (Real.pi / 4), fun n => ?_⟩
  by_cases hn : |n| ≤ N
  · exact (hM1 ⟨n, abs_le.1 hn |> fun h => ⟨h.1, h.2⟩, rfl⟩).trans (le_max_left _ _)
  · exact ((hN n (not_le.1 hn)).2.1).le.trans (le_max_right _ _)

theorem cut_im_lt {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R)
    {M : ℝ} (hM : ∀ n, R n ≤ M) {z : ℂ} (hz : z ∈ gapSegments38 φ) : |z.im| < M := by
  obtain ⟨n, hn⟩ := ball_cut hf hz
  have hc : (C n).im = 0 := by obtain ⟨_, _, ⟨hR, _⟩, _⟩ := hf; exact (hR n).2
  have := hn
  rw [mem_ball, dist_real_center hc] at this
  have h1 : |z.im| ≤ Real.sqrt ((z.re - (C n).re) ^ 2 + z.im ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (z.re - (C n).re)])
  linarith [hM n]

theorem real_mem_of_mem {c z : ℂ} {r : ℝ} (hc : c.im = 0) (hz : z ∈ ball c r) :
    ((z.re : ℝ) : ℂ) ∈ ball c r :=
  mem_ball_mono hc (by simp) (by simp) hz

theorem exists_free_real {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R) :
    ∃ x0 : ℝ, ∀ n, ((x0 : ℝ) : ℂ) ∉ ball (C n) (R n) := by
  have hC : ∀ n, (C n).im = 0 := by obtain ⟨_, _, ⟨hR, _⟩, _⟩ := hf; exact fun n => (hR n).2
  have hR0 : ∀ n, 0 < R n := by obtain ⟨_, _, ⟨hR, _⟩, _⟩ := hf; exact fun n => (hR n).1
  let I : ℤ → Set ℝ := fun n => {x | ((x : ℝ) : ℂ) ∈ ball (C n) (R n)}
  have hIo : ∀ n, IsOpen (I n) := fun n =>
    isOpen_ball.preimage Complex.continuous_ofReal
  have hdis : ∀ m n, m ≠ n → Disjoint (I m) (I n) := by
    intro m n hmn
    rw [Set.disjoint_left]
    intro x hm hn
    exact balls_disjoint hf hmn hm hn
  have hself : ∀ n, (C n).re ∈ I n := by
    intro n
    show (((C n).re : ℝ) : ℂ) ∈ ball (C n) (R n)
    have : (((C n).re : ℝ) : ℂ) = C n := Complex.ext (by simp) (by simp [hC n])
    rw [this]; exact mem_ball_self (hR0 n)
  by_contra hcon
  push Not at hcon
  have hcov : (univ : Set ℝ) ⊆ I 0 ∪ ⋃ n ∈ ({0}ᶜ : Set ℤ), I n := by
    intro x _
    obtain ⟨n, hn⟩ := hcon x
    by_cases h : n = 0
    · subst h; exact Or.inl hn
    · exact Or.inr (Set.mem_biUnion h hn)
  have hdis' : Disjoint (I 0) (⋃ n ∈ ({0}ᶜ : Set ℤ), I n) := by
    rw [Set.disjoint_iUnion₂_right]
    intro n hn
    exact hdis 0 n (Ne.symm hn)
  have hsub := isPreconnected_univ.subset_left_of_subset_union (hIo 0)
    (isOpen_biUnion fun n _ => hIo n) hdis' hcov ⟨(C 0).re, mem_univ _, hself 0⟩
  exact (Set.disjoint_left.1 (hdis 0 1 (by norm_num)) (hsub (mem_univ _)) (hself 1))


theorem exists_ray {φ : PotPair} {C : ℤ → ℂ} {R : ℤ → ℝ} (hf : IsolatingFamily38 φ C R)
    {z : ℂ} (hz : z ∉ gapSegments38 φ) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ∀ t : ℝ, 0 ≤ t → z + ((t * s : ℝ) : ℂ) * Complex.I ∉ gapSegments38 φ := by
  have hC : ∀ n, (C n).im = 0 := by obtain ⟨_, _, ⟨hR, _⟩, _⟩ := hf; exact fun n => (hR n).2
  have hre : ∀ (t s : ℝ), (z + ((t * s : ℝ) : ℂ) * Complex.I).re = z.re := by intro t s; simp
  have him : ∀ (t s : ℝ), (z + ((t * s : ℝ) : ℂ) * Complex.I).im = z.im + t * s := by intro t s; simp
  by_cases hb : ∃ n, z ∈ ball (C n) (R n)
  · obtain ⟨n, hn⟩ := hb
    by_contra h
    push Not at h
    obtain ⟨t1, ht1, hp1⟩ := h 1 (Or.inl rfl)
    obtain ⟨t2, ht2, hp2⟩ := h (-1) (Or.inr rfl)
    have hin : ∀ {p : ℂ}, p.re = z.re → p ∈ gapSegments38 φ → p ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      intro p hpre hp
      obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hp
      have hpb : p ∈ ball (C m) (R m) := cut_sub_ball hf m hm
      by_cases hmn : m = n
      · subst hmn; exact hm
      · exfalso
        have h1 : ((z.re : ℝ) : ℂ) ∈ ball (C n) (R n) := real_mem_of_mem (hC n) hn
        have h2 : ((p.re : ℝ) : ℂ) ∈ ball (C m) (R m) := real_mem_of_mem (hC m) hpb
        rw [hpre] at h2
        exact balls_disjoint hf hmn h2 h1
    have hs1 := hin (hre t1 1) hp1
    have hs2 := hin (hre t2 (-1)) hp2
    have ht1pos : 0 < t1 := by
      rcases ht1.eq_or_lt with h0 | h0
      · exfalso; subst h0; apply hz; simpa using hp1
      · exact h0
    have hzs : z ∈ segment ℝ (lamMinus φ n) (lamPlus φ n) := by
      refine (convex_segment _ _).segment_subset hs1 hs2 ?_
      refine ⟨t2 / (t1 + t2), t1 / (t1 + t2), by positivity, by positivity, by rw [← add_div, add_comm t2 t1]; exact div_self (by positivity), ?_⟩
      have hne : (t1 + t2 : ℝ) ≠ 0 := by positivity
      have hne2 : ((t2 : ℂ) + t1) ≠ 0 := by exact_mod_cast (by linarith : (t2 + t1 : ℝ) ≠ 0)
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      field_simp
      refine (by ring : _ = z * (((t2 : ℂ) + t1) * ((t2 : ℂ) + t1)⁻¹)).trans ?_
      rw [mul_inv_cancel₀ hne2, mul_one]
    exact hz (Set.mem_iUnion.2 ⟨n, hzs⟩)
  · refine ⟨if 0 ≤ z.im then 1 else -1, ?_, fun t ht hK => ?_⟩
    · by_cases h : 0 ≤ z.im <;> simp [h]
    · obtain ⟨m, hm⟩ := ball_cut hf hK
      apply hb
      refine ⟨m, mem_ball_mono (hC m) (hre t _).symm ?_ hm⟩
      rw [him]
      by_cases h : 0 ≤ z.im
      · simp only [h, ite_true, mul_one]
        rw [abs_of_nonneg h, abs_of_nonneg (by linarith)]; linarith
      · simp only [h, ite_false]
        push Not at h
        rw [abs_of_neg h, abs_of_neg (by nlinarith)]; nlinarith

end Support3Aux

theorem cutFreeFiber_isOpen (φ : PotPair) (hφ : φ ∈ gkW) : IsOpen (cutFreeFiber φ) := by
  obtain ⟨C, R, hf⟩ := exists_isolating_family38 φ hφ
  exact (Support3Aux.isClosed_cuts hf).isOpen_compl


theorem cutFreeFiber_polygonal (φ : PotPair) (hφ : φ ∈ gkW) :
    ∀ z ∈ cutFreeFiber φ, ∀ w ∈ cutFreeFiber φ,
      ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z w := by
  obtain ⟨C, R, hf⟩ := exists_isolating_family38 φ hφ
  obtain ⟨M, hM⟩ := Support3Aux.exists_radius_bound hf
  obtain ⟨x0, hx0⟩ := Support3Aux.exists_free_real hf
  have hC : ∀ n, (C n).im = 0 := by obtain ⟨_, _, ⟨hR, _⟩, _⟩ := hf; exact fun n => (hR n).2
  have hR0 : ∀ n, 0 < R n := by obtain ⟨_, _, ⟨hR, _⟩, _⟩ := hf; exact fun n => (hR n).1
  have hM0 : 0 ≤ M := (hR0 0).le.trans (hM 0)
  have hsymm : ∀ a b : ℂ, segment ℝ a b ⊆ cutFreeFiber φ → segment ℝ b a ⊆ cutFreeFiber φ := by
    intro a b h; simpa only [segment_symm] using h
  have hsymm2 : ∀ a b : ℂ,
      ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) a b →
      ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) b a := by
    intro a b h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hbc ih => exact ReflTransGen.head (hsymm _ _ hbc) ih
  have hseg : ∀ {a b p : ℂ}, p ∈ segment ℝ a b →
      ∃ u : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ p = a + (u : ℂ) * (b - a) := by
    intro a b p hp
    rw [segment_eq_image'] at hp
    obtain ⟨u, ⟨hu0, hu1⟩, rfl⟩ := hp
    exact ⟨u, hu0, hu1, by simp [Complex.real_smul]⟩
  have hvert : ∀ y : ℝ, ((x0 : ℂ) + (y : ℂ) * Complex.I) ∈ cutFreeFiber φ := by
    intro y hK
    obtain ⟨n, hn⟩ := Support3Aux.ball_cut hf hK
    have := Support3Aux.real_mem_of_mem (hC n) hn
    exact hx0 n (by simpa using this)
  have toX : ∀ z ∈ cutFreeFiber φ,
      ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z (x0 : ℂ) := by
    intro z hz
    obtain ⟨s, hs, hray⟩ := Support3Aux.exists_ray hf hz
    set T : ℝ := |z.im| + M + 1 with hT
    have hT0 : 0 ≤ T := by positivity
    set z1 : ℂ := z + ((T * s : ℝ) : ℂ) * Complex.I with hz1
    set z2 : ℂ := (x0 : ℂ) + (z1.im : ℂ) * Complex.I with hz2
    have hz1im : z1.im = z.im + T * s := by simp [hz1]
    have him1 : M < |z1.im| := by
      rw [hz1im]
      rcases hs with rfl | rfl
      · have h1 := neg_abs_le z.im
        have h2 := le_abs_self (z.im + T * 1)
        linarith
      · have h1 := le_abs_self z.im
        have h2 := neg_le_abs (z.im + T * -1)
        linarith
    have hfar : ∀ p : ℂ, |p.im| = |z1.im| → p ∈ cutFreeFiber φ := by
      intro p hp hK
      have := Support3Aux.cut_im_lt hf hM hK
      linarith
    have s1 : (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z z1 := by
      intro p hp
      obtain ⟨u, hu0, hu1, rfl⟩ := hseg hp
      have : z + (u : ℂ) * (z1 - z) = z + ((u * T * s : ℝ) : ℂ) * Complex.I := by
        rw [hz1]; push_cast; ring
      rw [this]
      exact hray (u * T) (mul_nonneg hu0 hT0)
    have s2 : (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z1 z2 := by
      intro p hp
      obtain ⟨u, hu0, hu1, rfl⟩ := hseg hp
      apply hfar
      have : (z1 + (u : ℂ) * (z2 - z1)).im = z1.im := by simp [hz2]
      rw [this]
    have s3 : (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z2 (x0 : ℂ) := by
      intro p hp
      obtain ⟨u, hu0, hu1, rfl⟩ := hseg hp
      have : z2 + (u : ℂ) * ((x0 : ℂ) - z2) = (x0 : ℂ) + (((1 - u) * z1.im : ℝ) : ℂ) * Complex.I := by
        rw [hz2]; push_cast; ring
      rw [this]
      exact hvert _
    have c1 : ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z z1 :=
      ReflTransGen.single s1
    have c2 : ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ cutFreeFiber φ) z z2 :=
      c1.tail s2
    exact c2.tail s3
  intro z hz w hw
  exact (toX z hz).trans (hsymm2 _ _ (toX w hw))

end
end NlsGge.ThirdConsultation.MPrimitive
