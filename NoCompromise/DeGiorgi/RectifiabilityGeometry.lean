module

public import NoCompromise.DeGiorgi.LipschitzPieces

@[expose] public section

/-!
# Geometric separation of uniform density and cone pieces

A pair of points with large normal separation forces a small ball around one
point outside the other's thin cone. Quantitative lower mass bounds and small
exterior mass make that impossible. A nearby fixed normal then gives a single
Lipschitz graph containing the piece.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal
namespace LiquidDrop

/-- A ball around a point with large normal height lies outside a thinner cone. -/
lemma ball_subset_exterior_cone_of_height {n : ℕ}
    {x y ν : EuclideanSpace ℝ (Fin n)} (hν : ‖ν‖ = 1) (hd : 0 < ‖y - x‖)
    (hh : ‖y - x‖ / 4 ≤ |inner ℝ ν (y - x)|) :
    ball y (‖y - x‖ / 32) ⊆
      ball x (2 * ‖y - x‖) ∩
        {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ ν (z - x)|} := by
  intro z hz
  have hz' : ‖z - y‖ < ‖y - x‖ / 32 := by simpa only [mem_ball, dist_eq_norm] using hz
  have hnorm : ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z - y) (y - x)
  have hip : |inner ℝ ν (z - y)| ≤ ‖z - y‖ := by
    simpa only [hν, one_mul] using abs_real_inner_le_norm ν (z - y)
  have hi : |inner ℝ ν (y - x)| ≤ |inner ℝ ν (z - x)| + ‖z - y‖ := by
    have heq : y - x = (z - x) - (z - y) := by abel
    rw [heq, inner_sub_right]
    exact (abs_sub _ _).trans (add_le_add le_rfl hip)
  constructor
  · change dist z x < 2 * ‖y - x‖
    rw [dist_eq_norm]
    linarith
  · change (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ ν (z - x)|
    linarith

/-- Uniform positive lower density and sufficiently small exterior-cone mass
force every pair in a small piece to have small normal separation. -/
theorem uniform_mass_piece_height_bound {n : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    (S : Set (EuclideanSpace ℝ (Fin n))) (ν : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n)) {c R : ℝ} (hc : 0 < c)
    (hν : ∀ x ∈ S, ‖ν x‖ = 1)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, 2 * ‖y - x‖ < R)
    (hlower : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r < R → c * r ^ 2 ≤ μ.real (ball x r))
    (hcone : ∀ x ∈ S, ∀ r : ℝ, 0 < r → r < R →
      μ.real (ball x r ∩ {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ (ν x) (z - x)|}) ≤
        c / 8192 * r ^ 2) :
    ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (ν x) (y - x)| ≤ ‖y - x‖ / 4 := by
  intro x hx y hy
  by_cases hxy : y = x
  · simp only [hxy, sub_self, inner_zero_right, abs_zero, norm_zero, zero_div, le_refl]
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  by_contra hfail
  have hh := (lt_of_not_ge hfail).le
  have hsub := ball_subset_exterior_cone_of_height (hν x hx) hd hh
  have hrsmall : ‖y - x‖ / 32 < R := by linarith [hdiam x hx y hy]
  have hlo := hlower y hy (‖y - x‖ / 32) (by positivity) hrsmall
  have hhi := hcone x hx (2 * ‖y - x‖) (by positivity) (hdiam x hx y hy)
  have hfin : μ (ball x (2 * ‖y - x‖) ∩
      {z | (1 / 8 : ℝ) * ‖z - x‖ ≤ |inner ℝ (ν x) (z - x)|}) ≠ ∞ :=
    ((measure_mono (inter_subset_left.trans ball_subset_closedBall)).trans_lt
      (isCompact_closedBall x (2 * ‖y - x‖)).measure_lt_top).ne
  have hm := measureReal_mono (μ := μ) hsub hfin
  nlinarith [mul_pos hc (sq_pos_of_pos hd)]

/-- Nearby normals turn point-dependent height bounds into a single fixed cone. -/
lemma half_cone_of_nearby_normal_bound {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {ν₀ : EuclideanSpace ℝ (Fin (n + 1))}
    (hnear : ∀ x ∈ S, ‖ν x - ν₀‖ ≤ (1 / 16 : ℝ))
    (hheight : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (ν x) (y - x)| ≤ ‖y - x‖ / 4) :
    ∀ x ∈ S, ∀ y ∈ S, |inner ℝ ν₀ (x - y)| ≤ (1 / 2 : ℝ) * ‖x - y‖ := by
  intro x hx y hy
  have hh := hheight x hx y hy
  rw [show y - x = -(x - y) by abel, inner_neg_right, abs_neg, norm_neg] at hh
  have hc : ‖ν₀ - ν x‖ ≤ (1 / 16 : ℝ) := by
    simpa only [norm_sub_rev] using hnear x hx
  have hb : |inner ℝ (ν₀ - ν x) (x - y)| ≤ (1 / 16 : ℝ) * ‖x - y‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
  have hi : inner ℝ ν₀ (x - y) =
      inner ℝ (ν₀ - ν x) (x - y) + inner ℝ (ν x) (x - y) := by
    rw [inner_sub_left]
    ring
  rw [hi]
  have ha := abs_add_le (inner ℝ (ν₀ - ν x) (x - y)) (inner ℝ (ν x) (x - y))
  nlinarith [norm_nonneg (x - y)]

/-- A uniform piece with nearby normal directions is contained in one rotated graph. -/
theorem exists_rotated_graph_of_nearby_normal_bound {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {ν₀ : EuclideanSpace ℝ (Fin (n + 1))} (hν₀ : ‖ν₀‖ = 1)
    (hnear : ∀ x ∈ S, ‖ν x - ν₀‖ ≤ (1 / 16 : ℝ))
    (hheight : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (ν x) (y - x)| ≤ ‖y - x‖ / 4) :
    ∃ (e : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n + 1)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ),
      e (EuclideanSpace.single (Fin.last n) 1) = ν₀ ∧ LipschitzWith 1 f ∧
      S ⊆ range (fun p => e (graphMapN f p)) :=
  exists_rotated_lipschitz_graph_of_half_cone S hν₀
    (half_cone_of_nearby_normal_bound S ν hnear hheight)

/-- Uniform pieces also admit global parametrizations with one fixed Lipschitz bound. -/
theorem exists_lipschitz_param_of_nearby_normal_bound {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    {ν₀ : EuclideanSpace ℝ (Fin (n + 1))} (hν₀ : ‖ν₀‖ = 1)
    (hnear : ∀ x ∈ S, ‖ν x - ν₀‖ ≤ (1 / 16 : ℝ))
    (hheight : ∀ x ∈ S, ∀ y ∈ S, |inner ℝ (ν x) (y - x)| ≤ ‖y - x‖ / 4) :
    ∃ f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + 1)),
      LipschitzWith 2 f ∧ S ⊆ range f :=
  exists_lipschitz_param_of_half_cone S hν₀
    (half_cone_of_nearby_normal_bound S ν hnear hheight)

end LiquidDrop
