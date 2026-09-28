import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Tactic

/-!
# Local sectors in Morse model coordinates

This file proves `lem:local-sectors` on the Euclidean plane. Transfer to a surface
requires `lem:morse-coords`. Rays exclude the critical point, and all disks are open.
-/

namespace LiquidDrop

open Set Metric
open scoped Convex

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- The coordinate disk in `lem:local-sectors`. -/
def morseDisk (ρ : ℝ) : Set E2 := ball 0 ρ

/-- First ray in the cyclic order of `lem:local-sectors`. -/
def morseRay1 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | x 1 = x 0 ∧ 0 < x 0}
/-- Second ray in the cyclic order of `lem:local-sectors`. -/
def morseRay2 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | x 1 = -x 0 ∧ x 0 < 0}
/-- Third ray in the cyclic order of `lem:local-sectors`. -/
def morseRay3 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | x 1 = x 0 ∧ x 0 < 0}
/-- Fourth ray in the cyclic order of `lem:local-sectors`. -/
def morseRay4 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | x 1 = -x 0 ∧ 0 < x 0}
/-- Upper negative sector in `lem:local-sectors`. -/
def morseSm12 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | |x 0| < x 1}
/-- Left positive sector in `lem:local-sectors`. -/
def morseSp23 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | |x 1| < -x 0}
/-- Lower negative sector in `lem:local-sectors`. -/
def morseSm34 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | |x 0| < -x 1}
/-- Right positive sector in `lem:local-sectors`. -/
def morseSp41 (ρ : ℝ) : Set E2 := {x ∈ morseDisk ρ | |x 1| < x 0}

private lemma coord_zero_iff (x : E2) : x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  constructor
  · rintro rfl; simp
  · intro h
    ext i
    fin_cases i <;> simp_all

private lemma sum_sq_zero_iff (x : E2) : x 0 ^ 2 + x 1 ^ 2 = 0 ↔ x = 0 := by
  rw [coord_zero_iff]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  · rintro ⟨h0, h1⟩; simp [h0, h1]

/-- `lem:local-sectors`, index zero, in model coordinates. -/
theorem morse_index_zero_sets {ρ : ℝ} (hρ : 0 < ρ) :
    {x ∈ morseDisk ρ | x 0 ^ 2 + x 1 ^ 2 < 0} = ∅ ∧
    {x ∈ morseDisk ρ | 0 < x 0 ^ 2 + x 1 ^ 2} = morseDisk ρ \ {0} ∧
    {x ∈ morseDisk ρ | x 0 ^ 2 + x 1 ^ 2 = 0} = {0} := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro _; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  · ext x
    simp only [mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
    have hn : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [lt_iff_le_and_ne, and_iff_right hn, ne_comm, ne_eq, (sum_sq_zero_iff x)]
  · ext x
    simp only [mem_ofPred_eq, sum_sq_zero_iff, mem_singleton_iff]
    exact and_iff_right_of_imp (fun h => by subst x; simpa [morseDisk] using hρ)

/-- `lem:local-sectors`, index two, in model coordinates. -/
theorem morse_index_two_sets {ρ : ℝ} (hρ : 0 < ρ) :
    {x ∈ morseDisk ρ | 0 < -(x 0 ^ 2 + x 1 ^ 2)} = ∅ ∧
    {x ∈ morseDisk ρ | -(x 0 ^ 2 + x 1 ^ 2) < 0} = morseDisk ρ \ {0} ∧
    {x ∈ morseDisk ρ | -(x 0 ^ 2 + x 1 ^ 2) = 0} = {0} := by
  simpa only [neg_pos, neg_neg_iff_pos, neg_eq_zero] using morse_index_zero_sets hρ

/-- `lem:local-sectors`: the saddle level consists of the origin and four rays. -/
theorem morse_saddle_zero_set {ρ : ℝ} (hρ : 0 < ρ) :
    {x ∈ morseDisk ρ | x 0 ^ 2 - x 1 ^ 2 = 0} =
      {0} ∪ morseRay1 ρ ∪ morseRay2 ρ ∪ morseRay3 ρ ∪ morseRay4 ρ := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_singleton_iff, morseRay1, morseRay2, morseRay3, morseRay4]
  constructor
  · rintro ⟨hx, he⟩
    have he' : x 1 = x 0 ∨ x 1 = -x 0 := by
      have : (x 1 - x 0) * (x 1 + x 0) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · left; linarith
      · right; linarith
    rcases lt_trichotomy (x 0) 0 with hn | hz | hp
    · rcases he' with h | h <;> tauto
    · have : x = 0 := (coord_zero_iff x).mpr ⟨hz, by rcases he' with h | h <;> linarith⟩
      tauto
    · rcases he' with h | h <;> tauto
  · intro h
    rcases h with (((h | h) | h) | h) | h
    · subst x; simp [morseDisk, hρ]
    all_goals rcases h with ⟨hx, he, _⟩; exact ⟨hx, by nlinarith⟩

/-- `lem:local-sectors`: the four rays exclude the critical point. -/
theorem morse_rays_zero_notMem (ρ : ℝ) :
    (0 : E2) ∉ morseRay1 ρ ∧ (0 : E2) ∉ morseRay2 ρ ∧ (0 : E2) ∉ morseRay3 ρ ∧ (0 : E2) ∉ morseRay4 ρ := by
  simp [morseRay1, morseRay2, morseRay3, morseRay4]

/-- `lem:local-sectors`: pairwise disjointness of the four rays. -/
theorem morse_rays_disjoint (ρ : ℝ) :
    Disjoint (morseRay1 ρ) (morseRay2 ρ) ∧ Disjoint (morseRay1 ρ) (morseRay3 ρ) ∧
    Disjoint (morseRay1 ρ) (morseRay4 ρ) ∧ Disjoint (morseRay2 ρ) (morseRay3 ρ) ∧
    Disjoint (morseRay2 ρ) (morseRay4 ρ) ∧ Disjoint (morseRay3 ρ) (morseRay4 ρ) := by
  simp only [Set.disjoint_left, morseRay1, morseRay2, morseRay3, morseRay4, mem_ofPred_eq]
  repeat' constructor
  all_goals rintro x ⟨_, h1, h2⟩ ⟨_, h3, h4⟩; linarith

private lemma sq_lt_sq_iff_sectors (a b : ℝ) :
    a ^ 2 < b ^ 2 ↔ |a| < b ∨ |a| < -b := by
  rw [sq_lt_sq, lt_abs]

/-- `lem:local-sectors`: the negative saddle set is the two vertical sectors. -/
theorem morse_saddle_negative_set (ρ : ℝ) :
    {x ∈ morseDisk ρ | x 0 ^ 2 - x 1 ^ 2 < 0} = morseSm12 ρ ∪ morseSm34 ρ := by
  ext x
  simp only [mem_ofPred_eq, sub_neg, sq_lt_sq_iff_sectors, morseSm12, morseSm34, mem_union]
  tauto

/-- `lem:local-sectors`: the positive saddle set is the two horizontal sectors. -/
theorem morse_saddle_positive_set (ρ : ℝ) :
    {x ∈ morseDisk ρ | 0 < x 0 ^ 2 - x 1 ^ 2} = morseSp23 ρ ∪ morseSp41 ρ := by
  ext x
  simp only [mem_ofPred_eq, sub_pos, sq_lt_sq_iff_sectors, morseSp23, morseSp41, mem_union]
  tauto

/-- `lem:local-sectors`: sectors of each sign are disjoint. -/
theorem morse_sectors_disjoint (ρ : ℝ) :
    Disjoint (morseSm12 ρ) (morseSm34 ρ) ∧ Disjoint (morseSp23 ρ) (morseSp41 ρ) := by
  constructor
  · refine Set.disjoint_left.mpr ?_
    rintro x ⟨_, h⟩ ⟨_, h'⟩
    linarith [abs_nonneg (x 0)]
  · refine Set.disjoint_left.mpr ?_
    rintro x ⟨_, h⟩ ⟨_, h'⟩
    linarith [abs_nonneg (x 1)]

private lemma small_point_mem_disk {ρ : ℝ} (hρ : 0 < ρ) (a b : ℝ)
    (ha : |a| ≤ ρ / 4) (hb : |b| ≤ ρ / 4) :
    (WithLp.toLp 2 ![a, b] : E2) ∈ morseDisk ρ := by
  rw [morseDisk, EuclideanSpace.ball_zero_eq ρ hρ.le]
  simp only [mem_ofPred_eq, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have ha' := (sq_le_sq₀ (abs_nonneg a) (by linarith : 0 ≤ ρ / 4)).mpr ha
  have hb' := (sq_le_sq₀ (abs_nonneg b) (by linarith : 0 ≤ ρ / 4)).mpr hb
  rw [sq_abs] at ha' hb'
  nlinarith [sq_pos_of_pos hρ]

private lemma combo_lt {a b u v w z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hu : u < v) (hw : w < z) :
    a * u + b * w < a * v + b * z := by
  rcases ha.eq_or_lt with h | h
  · have ha0 : a = 0 := h.symm
    have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hw
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hu h)
      (mul_le_mul_of_nonneg_left hw.le hb)

/-- Convexity of all the rays and sectors of `lem:local-sectors`. -/
theorem morse_rays_sectors_convex (ρ : ℝ) :
    Convex ℝ (morseRay1 ρ) ∧ Convex ℝ (morseRay2 ρ) ∧ Convex ℝ (morseRay3 ρ) ∧ Convex ℝ (morseRay4 ρ) ∧
    Convex ℝ (morseSm12 ρ) ∧ Convex ℝ (morseSp23 ρ) ∧ Convex ℝ (morseSm34 ρ) ∧ Convex ℝ (morseSp41 ρ) := by
  have hc : Convex ℝ (morseDisk ρ) := convex_ball _ _
  repeat' constructor
  all_goals
    intro x hx y hy a b ha hb hab
    refine ⟨hc hx.1 hy.1 ha hb hab, ?_⟩
    have hx' := hx.2
    have hy' := hy.2
    simp only [abs_lt] at hx' hy'
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_lt]
    rcases hx' with ⟨hx1, hx2⟩
    rcases hy' with ⟨hy1, hy2⟩
    have h2 := combo_lt ha hb hab hx2 hy2
    first | have h1 := combo_lt ha hb hab hx1 hy1 | skip
    constructor <;> nlinarith

/-- Nonemptiness of all the rays and sectors of `lem:local-sectors`. -/
theorem morse_rays_sectors_nonempty {ρ : ℝ} (hρ : 0 < ρ) :
    (morseRay1 ρ).Nonempty ∧ (morseRay2 ρ).Nonempty ∧ (morseRay3 ρ).Nonempty ∧ (morseRay4 ρ).Nonempty ∧
    (morseSm12 ρ).Nonempty ∧ (morseSp23 ρ).Nonempty ∧ (morseSm34 ρ).Nonempty ∧ (morseSp41 ρ).Nonempty := by
  have hp : |ρ / 4| ≤ ρ / 4 := le_of_eq (abs_of_pos (by linarith))
  have hn : |-(ρ / 4)| ≤ ρ / 4 := by simpa using hp
  have hz : |(0 : ℝ)| ≤ ρ / 4 := by simp; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨WithLp.toLp 2 ![ρ / 4, ρ / 4], small_point_mem_disk hρ _ _ hp hp, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![-(ρ / 4), ρ / 4], small_point_mem_disk hρ _ _ hn hp, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![-(ρ / 4), -(ρ / 4)], small_point_mem_disk hρ _ _ hn hn, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![ρ / 4, -(ρ / 4)], small_point_mem_disk hρ _ _ hp hn, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![0, ρ / 4], small_point_mem_disk hρ _ _ hz hp, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![-(ρ / 4), 0], small_point_mem_disk hρ _ _ hn hz, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![0, -(ρ / 4)], small_point_mem_disk hρ _ _ hz hn, ?_⟩
    norm_num
    linarith
  · refine ⟨WithLp.toLp 2 ![ρ / 4, 0], small_point_mem_disk hρ _ _ hp hz, ?_⟩
    norm_num
    linarith

/-- `lem:local-sectors`: every ray and every sector is connected. -/
theorem morse_rays_sectors_connected {ρ : ℝ} (hρ : 0 < ρ) :
    IsConnected (morseRay1 ρ) ∧ IsConnected (morseRay2 ρ) ∧ IsConnected (morseRay3 ρ) ∧ IsConnected (morseRay4 ρ) ∧
    IsConnected (morseSm12 ρ) ∧ IsConnected (morseSp23 ρ) ∧ IsConnected (morseSm34 ρ) ∧
    IsConnected (morseSp41 ρ) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := morse_rays_sectors_convex ρ
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := morse_rays_sectors_nonempty hρ
  exact ⟨c1.isConnected n1, c2.isConnected n2, c3.isConnected n3, c4.isConnected n4,
    c5.isConnected n5, c6.isConnected n6, c7.isConnected n7, c8.isConnected n8⟩

/-- `lem:local-sectors`: all four saddle sectors are open. -/
theorem morse_sectors_open (ρ : ℝ) :
    IsOpen (morseSm12 ρ) ∧ IsOpen (morseSp23 ρ) ∧ IsOpen (morseSm34 ρ) ∧ IsOpen (morseSp41 ρ) := by
  have c0 : Continuous (fun x : E2 => x 0) := PiLp.continuous_apply _ _ _
  have c1 : Continuous (fun x : E2 => x 1) := PiLp.continuous_apply _ _ _
  exact ⟨isOpen_ball.inter (isOpen_lt c0.abs c1),
    isOpen_ball.inter (isOpen_lt c1.abs c0.neg),
    isOpen_ball.inter (isOpen_lt c0.abs c1.neg),
    isOpen_ball.inter (isOpen_lt c1.abs c0)⟩

private lemma component_union_eq {U V : Set E2} (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V) (hc : IsPreconnected U) {y : E2} (hy : y ∈ U) :
    connectedComponentIn (U ∪ V) y = U := by
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hd
      (connectedComponentIn_subset _ _) ⟨y, mem_connectedComponentIn (Or.inl hy), hy⟩
  · exact hc.subset_connectedComponentIn hy subset_union_left

/-- `lem:local-sectors`: the two sectors of each sign are exactly its connected components. -/
theorem morse_sectors_components {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ y ∈ morseSm12 ρ, connectedComponentIn
      {x ∈ morseDisk ρ | x 0 ^ 2 - x 1 ^ 2 < 0} y = morseSm12 ρ) ∧
    (∀ y ∈ morseSm34 ρ, connectedComponentIn
      {x ∈ morseDisk ρ | x 0 ^ 2 - x 1 ^ 2 < 0} y = morseSm34 ρ) ∧
    (∀ y ∈ morseSp23 ρ, connectedComponentIn
      {x ∈ morseDisk ρ | 0 < x 0 ^ 2 - x 1 ^ 2} y = morseSp23 ρ) ∧
    (∀ y ∈ morseSp41 ρ, connectedComponentIn
      {x ∈ morseDisk ρ | 0 < x 0 ^ 2 - x 1 ^ 2} y = morseSp41 ρ) := by
  rw [morse_saddle_negative_set, morse_saddle_positive_set]
  obtain ⟨o1, o2, o3, o4⟩ := morse_sectors_open ρ
  obtain ⟨d1, d2⟩ := morse_sectors_disjoint ρ
  obtain ⟨_, _, _, _, c1, c2, c3, c4⟩ := morse_rays_sectors_connected hρ
  refine ⟨fun _ h => component_union_eq o1 o3 d1 c1.2 h, ?_,
    fun _ h => component_union_eq o2 o4 d2 c2.2 h, ?_⟩
  · intro y hy; rw [union_comm]; exact component_union_eq o3 o1 d1.symm c3.2 hy
  · intro y hy; rw [union_comm]; exact component_union_eq o4 o2 d2.symm c4.2 hy

private lemma closure_of_openSegment {S : Set E2} {x y : E2}
    (h : openSegment ℝ x y ⊆ S) : x ∈ closure S :=
  closure_mono h (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

/-- `lem:local-sectors`: the origin is in the closure of every ray. -/
theorem morse_rays_zero_mem_closure {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : E2) ∈ closure (morseRay1 ρ) ∧ (0 : E2) ∈ closure (morseRay2 ρ) ∧
    (0 : E2) ∈ closure (morseRay3 ρ) ∧ (0 : E2) ∈ closure (morseRay4 ρ) := by
  obtain ⟨n1, n2, n3, n4, _⟩ := morse_rays_sectors_nonempty hρ
  have h0 : (0 : E2) ∈ morseDisk ρ := by simpa [morseDisk] using hρ
  have hc : Convex ℝ (morseDisk ρ) := convex_ball _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy⟩ := n1
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc h0 hy.1 ha.le hb.le hab, ?_⟩
    have hy' := hy.2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
      mul_zero, zero_add]
    constructor <;> nlinarith
  · obtain ⟨y, hy⟩ := n2
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc h0 hy.1 ha.le hb.le hab, ?_⟩
    have hy' := hy.2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
      mul_zero, zero_add]
    constructor <;> nlinarith
  · obtain ⟨y, hy⟩ := n3
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc h0 hy.1 ha.le hb.le hab, ?_⟩
    have hy' := hy.2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
      mul_zero, zero_add]
    constructor <;> nlinarith
  · obtain ⟨y, hy⟩ := n4
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc h0 hy.1 ha.le hb.le hab, ?_⟩
    have hy' := hy.2
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul,
      mul_zero, zero_add]
    constructor <;> nlinarith

/-- Weak sector inequalities inside the disk imply closure membership (`lem:local-sectors`). -/
theorem morse_sectors_mem_closure {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ x ∈ morseDisk ρ, |x 0| ≤ x 1 → x ∈ closure (morseSm12 ρ)) ∧
    (∀ x ∈ morseDisk ρ, |x 1| ≤ -x 0 → x ∈ closure (morseSp23 ρ)) ∧
    (∀ x ∈ morseDisk ρ, |x 0| ≤ -x 1 → x ∈ closure (morseSm34 ρ)) ∧
    (∀ x ∈ morseDisk ρ, |x 1| ≤ x 0 → x ∈ closure (morseSp41 ρ)) := by
  obtain ⟨_, _, _, _, n1, n2, n3, n4⟩ := morse_rays_sectors_nonempty hρ
  have hc : Convex ℝ (morseDisk ρ) := convex_ball _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hbound
    obtain ⟨y, hy⟩ := n1
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc hx hy.1 ha.le hb.le hab, ?_⟩
    obtain ⟨hx1, hx2⟩ := abs_le.mp hbound
    obtain ⟨hy1, hy2⟩ := abs_lt.mp hy.2
    have h1 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx1 ha.le)
      (mul_lt_mul_of_pos_left hy1 hb)
    have h2 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx2 ha.le)
      (mul_lt_mul_of_pos_left hy2 hb)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_lt]
    constructor <;> linarith
  · intro x hx hbound
    obtain ⟨y, hy⟩ := n2
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc hx hy.1 ha.le hb.le hab, ?_⟩
    obtain ⟨hx1, hx2⟩ := abs_le.mp hbound
    obtain ⟨hy1, hy2⟩ := abs_lt.mp hy.2
    have h1 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx1 ha.le)
      (mul_lt_mul_of_pos_left hy1 hb)
    have h2 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx2 ha.le)
      (mul_lt_mul_of_pos_left hy2 hb)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_lt]
    constructor <;> linarith
  · intro x hx hbound
    obtain ⟨y, hy⟩ := n3
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc hx hy.1 ha.le hb.le hab, ?_⟩
    obtain ⟨hx1, hx2⟩ := abs_le.mp hbound
    obtain ⟨hy1, hy2⟩ := abs_lt.mp hy.2
    have h1 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx1 ha.le)
      (mul_lt_mul_of_pos_left hy1 hb)
    have h2 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx2 ha.le)
      (mul_lt_mul_of_pos_left hy2 hb)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_lt]
    constructor <;> linarith
  · intro x hx hbound
    obtain ⟨y, hy⟩ := n4
    apply closure_of_openSegment (y := y)
    rintro z ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨hc hx hy.1 ha.le hb.le hab, ?_⟩
    obtain ⟨hx1, hx2⟩ := abs_le.mp hbound
    obtain ⟨hy1, hy2⟩ := abs_lt.mp hy.2
    have h1 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx1 ha.le)
      (mul_lt_mul_of_pos_left hy1 hb)
    have h2 := add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx2 ha.le)
      (mul_lt_mul_of_pos_left hy2 hb)
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, abs_lt]
    constructor <;> linarith

/-- Necessary weak inequalities on sector closures (`lem:local-sectors`). -/
theorem morse_sectors_closure_bounds (ρ : ℝ) :
    closure (morseSm12 ρ) ⊆ {x : E2 | |x 0| ≤ x 1} ∧
    closure (morseSp23 ρ) ⊆ {x : E2 | |x 1| ≤ -x 0} ∧
    closure (morseSm34 ρ) ⊆ {x : E2 | |x 0| ≤ -x 1} ∧
    closure (morseSp41 ρ) ⊆ {x : E2 | |x 1| ≤ x 0} := by
  have c0 : Continuous (fun x : E2 => x 0) := PiLp.continuous_apply _ _ _
  have c1 : Continuous (fun x : E2 => x 1) := PiLp.continuous_apply _ _ _
  exact ⟨closure_minimal (fun _ h => h.2.le) (isClosed_le c0.abs c1),
    closure_minimal (fun _ h => h.2.le) (isClosed_le c1.abs c0.neg),
    closure_minimal (fun _ h => h.2.le) (isClosed_le c0.abs c1.neg),
    closure_minimal (fun _ h => h.2.le) (isClosed_le c1.abs c0)⟩

/-- `lem:local-sectors`: each ray is in the closures of its two flanking sectors. -/
theorem morse_rays_flanking {ρ : ℝ} (hρ : 0 < ρ) :
    morseRay1 ρ ⊆ closure (morseSp41 ρ) ∩ closure (morseSm12 ρ) ∧
    morseRay2 ρ ⊆ closure (morseSm12 ρ) ∩ closure (morseSp23 ρ) ∧
    morseRay3 ρ ⊆ closure (morseSp23 ρ) ∩ closure (morseSm34 ρ) ∧
    morseRay4 ρ ⊆ closure (morseSm34 ρ) ∩ closure (morseSp41 ρ) := by
  obtain ⟨c1, c2, c3, c4⟩ := morse_sectors_mem_closure hρ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro x ⟨hx, he, hs⟩
    exact ⟨c4 x hx (by rw [abs_le]; constructor <;> linarith),
      c1 x hx (by rw [abs_le]; constructor <;> linarith)⟩
  · rintro x ⟨hx, he, hs⟩
    exact ⟨c1 x hx (by rw [abs_le]; constructor <;> linarith),
      c2 x hx (by rw [abs_le]; constructor <;> linarith)⟩
  · rintro x ⟨hx, he, hs⟩
    exact ⟨c2 x hx (by rw [abs_le]; constructor <;> linarith),
      c3 x hx (by rw [abs_le]; constructor <;> linarith)⟩
  · rintro x ⟨hx, he, hs⟩
    exact ⟨c3 x hx (by rw [abs_le]; constructor <;> linarith),
      c4 x hx (by rw [abs_le]; constructor <;> linarith)⟩

/-- `lem:local-sectors`: a ray misses the closures of both non-flanking sectors. -/
theorem morse_rays_nonflanking (ρ : ℝ) :
    Disjoint (morseRay1 ρ) (closure (morseSp23 ρ)) ∧ Disjoint (morseRay1 ρ) (closure (morseSm34 ρ)) ∧
    Disjoint (morseRay2 ρ) (closure (morseSm34 ρ)) ∧ Disjoint (morseRay2 ρ) (closure (morseSp41 ρ)) ∧
    Disjoint (morseRay3 ρ) (closure (morseSp41 ρ)) ∧ Disjoint (morseRay3 ρ) (closure (morseSm12 ρ)) ∧
    Disjoint (morseRay4 ρ) (closure (morseSm12 ρ)) ∧ Disjoint (morseRay4 ρ) (closure (morseSp23 ρ)) := by
  obtain ⟨c1, c2, c3, c4⟩ := morse_sectors_closure_bounds ρ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c2 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c3 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c3 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c4 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c4 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c1 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c1 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith
  · apply Set.disjoint_left.mpr
    rintro x ⟨_, he, hs⟩ hx
    have h := c2 hx
    simp only [mem_ofPred_eq, abs_le] at h
    linarith

/-- `lem:local-sectors`: all four sectors accumulate at the critical point. -/
theorem morse_sectors_zero_mem_closure {ρ : ℝ} (hρ : 0 < ρ) :
    (0 : E2) ∈ closure (morseSm12 ρ) ∧ (0 : E2) ∈ closure (morseSp23 ρ) ∧
    (0 : E2) ∈ closure (morseSm34 ρ) ∧ (0 : E2) ∈ closure (morseSp41 ρ) := by
  obtain ⟨c1, c2, c3, c4⟩ := morse_sectors_mem_closure hρ
  have h0 : (0 : E2) ∈ morseDisk ρ := by simpa [morseDisk] using hρ
  exact ⟨c1 0 h0 (by simp), c2 0 h0 (by simp), c3 0 h0 (by simp), c4 0 h0 (by simp)⟩

/-- `lem:local-sectors`: the punctured coordinate disk is connected in dimension two. -/
theorem morse_punctured_disk_connected {ρ : ℝ} (hρ : 0 < ρ) :
    IsConnected (morseDisk ρ \ {(0 : E2)}) := by
  have hrank : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast (by norm_num : 1 < (2 : ℕ))
  let e : OpenPartialHomeomorph E2 E2 := OpenPartialHomeomorph.univBall 0 ρ
  have he_source : e.source = univ := OpenPartialHomeomorph.univBall_source _ _
  have he_target : e.target = morseDisk ρ := OpenPartialHomeomorph.univBall_target _ hρ
  have he_zero : e 0 = 0 := OpenPartialHomeomorph.univBall_apply_zero _ _
  have himage : e '' ({(0 : E2)}ᶜ) = morseDisk ρ \ {0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨he_target ▸ e.map_source (by simp [he_source]), ?_⟩
      intro heq
      have hy0 : y = 0 := e.injOn (by simp [he_source]) (by simp [he_source])
        (heq.trans he_zero.symm)
      exact hy hy0
    · rintro ⟨hx, hn⟩
      have hxt : x ∈ e.target := he_target.symm ▸ hx
      refine ⟨e.symm x, ?_, e.right_inv hxt⟩
      intro heq
      have hx0 : x = 0 := by rw [← e.right_inv hxt, heq, he_zero]
      exact hn hx0
  rw [← himage]
  exact (isConnected_compl_singleton_of_one_lt_rank hrank (0 : E2)).image e
    (OpenPartialHomeomorph.continuous_univBall _ _).continuousOn

private lemma model_predicate_transport {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X E2) {ρ c : ℝ} (hD : morseDisk ρ ⊆ e.target)
    (h : X → ℝ) (g : E2 → ℝ) (hh : ∀ x ∈ e.source, h x = c + g (e x))
    (P : ℝ → Prop) :
    {x ∈ e.source ∩ e ⁻¹' morseDisk ρ | P (h x - c)} =
      e.symm '' {y ∈ morseDisk ρ | P (g y)} := by
  rw [e.symm_image_eq_source_inter_preimage (fun _ hy => hD hy.1)]
  ext x
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨⟨hx, hd⟩, hp⟩
    refine ⟨hx, hd, ?_⟩
    simpa [hh x hx] using hp
  · rintro ⟨hx, hd, hp⟩
    exact ⟨⟨hx, hd⟩, by simpa [hh x hx] using hp⟩

/-- Transport of the three model level sets in `lem:local-sectors` through a Morse chart.
Obtaining this chart for a surface requires `lem:morse-coords`. -/
theorem morse_model_sets_transport {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X E2) {ρ c : ℝ} (hD : morseDisk ρ ⊆ e.target)
    (h : X → ℝ) (g : E2 → ℝ) (hh : ∀ x ∈ e.source, h x = c + g (e x)) :
    {x ∈ e.source ∩ e ⁻¹' morseDisk ρ | h x < c} =
      e.symm '' {y ∈ morseDisk ρ | g y < 0} ∧
    {x ∈ e.source ∩ e ⁻¹' morseDisk ρ | h x = c} =
      e.symm '' {y ∈ morseDisk ρ | g y = 0} ∧
    {x ∈ e.source ∩ e ⁻¹' morseDisk ρ | c < h x} =
      e.symm '' {y ∈ morseDisk ρ | 0 < g y} := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [sub_neg] using model_predicate_transport e hD h g hh (· < 0)
  · simpa only [sub_eq_zero] using model_predicate_transport e hD h g hh (· = 0)
  · simpa only [sub_pos] using model_predicate_transport e hD h g hh (0 < ·)

/-- Connected model rays and sectors remain connected in the chart (`lem:local-sectors`;
the surface chart itself is supplied by `lem:morse-coords`). -/
theorem morse_model_connected_transport {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X E2) {ρ : ℝ} (hD : morseDisk ρ ⊆ e.target)
    {S : Set E2} (hS : S ⊆ morseDisk ρ) (hc : IsConnected S) :
    IsConnected (e.symm '' S) :=
  hc.image e.symm (e.symm.continuousOn.mono (hS.trans hD))

/-- Closure membership at points of the coordinate disk is preserved by the chart.
This transports the closure relations in `lem:local-sectors`; `lem:morse-coords`
is needed to supply a chart on the surface. Closures are ambient closures. -/
theorem morse_model_closure_transport {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X E2) {ρ : ℝ} (hD : morseDisk ρ ⊆ e.target)
    {S : Set E2} (hS : S ⊆ morseDisk ρ) {y : E2} (hy : y ∈ morseDisk ρ) :
    e.symm y ∈ closure (e.symm '' S) ↔ y ∈ closure S := by
  have hi : e '' (e.symm '' S) = S := by
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [e.right_inv (hD (hS hw))] using hw
    · intro hz
      exact ⟨e.symm z, mem_image_of_mem _ hz, e.right_inv (hD (hS hz))⟩
  constructor
  · intro hmem
    have hm := mem_closure_image (e.continuousAt (e.map_target (hD hy))) hmem
    simpa only [e.right_inv (hD hy), hi] using hm
  · exact mem_closure_image (e.continuousAt_symm (hD hy))

/-- Transport of flanking closure inclusions in `lem:local-sectors`. -/
theorem morse_model_closure_subset_transport {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X E2) {ρ : ℝ} (hD : morseDisk ρ ⊆ e.target)
    {R S : Set E2} (hR : R ⊆ morseDisk ρ) (hS : S ⊆ morseDisk ρ) :
    e.symm '' R ⊆ closure (e.symm '' S) ↔ R ⊆ closure S := by
  simp only [subset_def, forall_mem_image]
  exact forall_congr' fun y => imp_congr_right fun hy =>
    morse_model_closure_transport e hD hS (hR hy)

/-- Transport of non-flanking closure disjointness in `lem:local-sectors`. -/
theorem morse_model_closure_disjoint_transport {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X E2) {ρ : ℝ} (hD : morseDisk ρ ⊆ e.target)
    {R S : Set E2} (hR : R ⊆ morseDisk ρ) (hS : S ⊆ morseDisk ρ) :
    Disjoint (e.symm '' R) (closure (e.symm '' S)) ↔ Disjoint R (closure S) := by
  simp only [Set.disjoint_left, forall_mem_image]
  exact forall_congr' fun y => imp_congr_right fun hy =>
    not_congr (morse_model_closure_transport e hD hS (hR hy))

end LiquidDrop
