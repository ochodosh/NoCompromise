module

public import NoCompromise.Regularity.SlabPhases

@[expose] public section

/-! # Interior balls at flat cylindrical caps -/

noncomputable section
open Set Metric
namespace LiquidDrop

lemma norm_graphProjectionN_le {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) :
    ‖graphProjectionN k x‖ ≤ ‖x‖ := by
  have h := norm_sq_graphProjectionN x
  nlinarith [norm_nonneg x, norm_nonneg (graphProjectionN k x), sq_nonneg (x (Fin.last k))]

lemma abs_last_le_norm {k : ℕ} (x : EuclideanSpace ℝ (Fin (k + 1))) :
    |x (Fin.last k)| ≤ ‖x‖ := by
  have h := norm_sq_graphProjectionN x
  have ha := sq_abs (x (Fin.last k))
  nlinarith [norm_nonneg x, abs_nonneg (x (Fin.last k)), sq_nonneg ‖graphProjectionN k x‖]

@[simp] lemma graphAppendN_height_three (p : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    graphAppendN p s (2 : Fin 3) = s := graphAppendN_last p s

lemma dist_graphAppendN_same_base {k : ℕ} (p : EuclideanSpace ℝ (Fin k)) (a b : ℝ) :
    dist (graphAppendN p a) (graphAppendN p b) = |a - b| := by
  rw [dist_eq_norm]
  have he : graphAppendN p a - graphAppendN p b =
      (a - b) • EuclideanSpace.single (Fin.last k) (1 : ℝ) := by
    simp only [graphAppendN, sub_smul]
    abel
  rw [he, norm_smul]
  simp only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]

def cylindricalStrip (r a b : ℝ) : Set AmbientSpace :=
  (graphProjectionN 2) ⁻¹' ball 0 r ∩
    (EuclideanSpace.proj (2 : Fin 3) : AmbientSpace →L[ℝ] ℝ) ⁻¹' Ioo a b

lemma ball_graphAppendN_subset_strip {r a b t ε : ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hp : ‖p‖ + ε ≤ r) (ha : a + ε ≤ t) (hb : t + ε ≤ b) :
    ball (graphAppendN p t) ε ⊆ cylindricalStrip r a b := by
  intro y hy
  have hd : ‖y - graphAppendN p t‖ < ε := hy
  have hbase : ‖graphProjectionN 2 y - p‖ < ε := by
    have h := (norm_graphProjectionN_le (y - graphAppendN p t)).trans_lt hd
    simpa only [map_sub, graphProjectionN_append] using h
  have hheight : |y 2 - t| < ε := by
    have h := (abs_last_le_norm (y - graphAppendN p t)).trans_lt hd
    simpa only [PiLp.sub_apply, show (Fin.last 2 : Fin 3) = 2 from rfl,
      graphAppendN_height_three] using h
  have hn : ‖graphProjectionN 2 y‖ < r := by
    have hh := norm_add_le (graphProjectionN 2 y - p) p
    rw [sub_add_cancel] at hh
    linarith
  refine ⟨?_, ?_⟩
  · simpa only [mem_preimage, mem_ball, dist_zero_right] using hn
  · change a < y 2 ∧ y 2 < b
    have hh := abs_lt.mp hheight
    constructor <;> linarith

lemma interior_balls_cylindricalStrip_lower {r a b : ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hp : ‖p‖ < r) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∃ z : AmbientSpace, ball z (s / 4) ⊆
        cylindricalStrip r a b ∩ ball (graphAppendN p a) s := by
  refine ⟨min (r - ‖p‖) (b - a), lt_min (sub_pos.mpr hp) (sub_pos.mpr hab), ?_⟩
  intro s hs hsδ
  have hh := lt_min_iff.mp hsδ
  refine ⟨graphAppendN p (a + s / 2), ?_⟩
  have hsub := ball_graphAppendN_subset_strip (p := p) (t := a + s / 2) (ε := s / 4)
    (r := r) (a := a) (b := b) (by linarith [hh.1]) (by linarith) (by linarith [hh.2])
  intro y hy
  refine ⟨hsub hy, ?_⟩
  have hd := dist_triangle y (graphAppendN p (a + s / 2)) (graphAppendN p a)
  rw [dist_graphAppendN_same_base, add_sub_cancel_left,
    abs_of_pos (by positivity : 0 < s / 2)] at hd
  change dist y (graphAppendN p a) < s
  have hy' : dist y (graphAppendN p (a + s / 2)) < s / 4 := hy
  linarith

lemma interior_balls_cylindricalStrip_upper {r a b : ℝ} {p : EuclideanSpace ℝ (Fin 2)}
    (hp : ‖p‖ < r) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∃ z : AmbientSpace, ball z (s / 4) ⊆
        cylindricalStrip r a b ∩ ball (graphAppendN p b) s := by
  refine ⟨min (r - ‖p‖) (b - a), lt_min (sub_pos.mpr hp) (sub_pos.mpr hab), ?_⟩
  intro s hs hsδ
  have hh := lt_min_iff.mp hsδ
  refine ⟨graphAppendN p (b - s / 2), ?_⟩
  have hsub := ball_graphAppendN_subset_strip (p := p) (t := b - s / 2) (ε := s / 4)
    (r := r) (a := a) (b := b) (by linarith [hh.1]) (by linarith [hh.2]) (by linarith)
  intro y hy
  refine ⟨hsub hy, ?_⟩
  have hd := dist_triangle y (graphAppendN p (b - s / 2)) (graphAppendN p b)
  rw [dist_graphAppendN_same_base, sub_sub_cancel_left, abs_neg,
    abs_of_pos (by positivity : 0 < s / 2)] at hd
  change dist y (graphAppendN p b) < s
  have hy' : dist y (graphAppendN p (b - s / 2)) < s / 4 := hy
  linarith

end LiquidDrop
