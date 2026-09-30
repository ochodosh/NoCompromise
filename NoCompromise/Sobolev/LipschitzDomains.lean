module

public import NoCompromise.Sobolev.Extension
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-!
# Lipschitz boundary charts for Euclidean balls

The hemisphere height is extended from a small tangential ball using the proved
scalar Lipschitz extension. Affine isometries place genuine one-sided graph charts
at the boundary points.
-/

noncomputable section
open MeasureTheory Metric Filter Set
open scoped ENNReal Topology
namespace LiquidDrop

/-- The inward height of a sphere of radius `r` above its tangent plane. -/
def ballGraphHeight {n : ℕ} (r : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  r - Real.sqrt (r ^ 2 - ‖x‖ ^ 2)

lemma sqrt_radius_sq_sub_norm_sq_ge_half {n : ℕ} {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ ≤ r / 2) :
    r / 2 ≤ Real.sqrt (r ^ 2 - ‖x‖ ^ 2) := by
  have hx0 := norm_nonneg x
  have hsq : 0 ≤ r ^ 2 - ‖x‖ ^ 2 := by nlinarith
  have hroot := Real.sq_sqrt hsq
  have hroot0 := Real.sqrt_nonneg (r ^ 2 - ‖x‖ ^ 2)
  nlinarith

lemma ballGraphHeight_lipschitzOn_half_ball {n : ℕ} {r : ℝ} (hr : 0 < r) :
    LipschitzOnWith 1 (ballGraphHeight (n := n) r) (closedBall 0 (r / 2)) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hx' : ‖x‖ ≤ r / 2 := by simpa using hx
  have hy' : ‖y‖ ≤ r / 2 := by simpa using hy
  have hx0 := norm_nonneg x
  have hy0 := norm_nonneg y
  have hxsq : 0 ≤ r ^ 2 - ‖x‖ ^ 2 := by nlinarith
  have hysq : 0 ≤ r ^ 2 - ‖y‖ ^ 2 := by nlinarith
  have hrootx := Real.sq_sqrt hxsq
  have hrooty := Real.sq_sqrt hysq
  have hxroot := sqrt_radius_sq_sub_norm_sq_ge_half hr hx'
  have hyroot := sqrt_radius_sq_sub_norm_sq_ge_half hr hy'
  have hnorm : |‖y‖ - ‖x‖| ≤ dist x y := by
    simpa only [dist_eq_norm, norm_sub_rev] using abs_norm_sub_norm_le y x
  have hfactor : |Real.sqrt (r ^ 2 - ‖x‖ ^ 2) - Real.sqrt (r ^ 2 - ‖y‖ ^ 2)| *
      (Real.sqrt (r ^ 2 - ‖x‖ ^ 2) + Real.sqrt (r ^ 2 - ‖y‖ ^ 2)) =
      |‖y‖ - ‖x‖| * (‖y‖ + ‖x‖) := by
    rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (r ^ 2 - ‖x‖ ^ 2) +
      Real.sqrt (r ^ 2 - ‖y‖ ^ 2)), ← abs_mul,
      ← abs_of_nonneg (by positivity : 0 ≤ ‖y‖ + ‖x‖), ← abs_mul]
    congr 1
    nlinarith
  have hrootabs := abs_nonneg
    (Real.sqrt (r ^ 2 - ‖x‖ ^ 2) - Real.sqrt (r ^ 2 - ‖y‖ ^ 2))
  have hnormabs := abs_nonneg (‖y‖ - ‖x‖)
  have hd := dist_nonneg (x := x) (y := y)
  have hmul := mul_le_mul_of_nonneg_right hnorm (by positivity : 0 ≤ ‖y‖ + ‖x‖)
  have hfinal : |Real.sqrt (r ^ 2 - ‖x‖ ^ 2) - Real.sqrt (r ^ 2 - ‖y‖ ^ 2)| ≤
      dist x y := by
    nlinarith
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq, ballGraphHeight, sub_sub_sub_cancel_left,
    abs_sub_comm] using hfinal

lemma coordinateErase_add_normal {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    coordinateErase i x + x i • EuclideanSpace.single i 1 = x := by
  ext j
  by_cases hj : j = i <;> simp [coordinateErase_apply, hj]

lemma norm_sq_coordinateErase_add_normal {n : ℕ} (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    ‖coordinateErase i x + s • EuclideanSpace.single i 1‖ ^ 2 =
      ‖coordinateErase i x‖ ^ 2 + s ^ 2 := by
  rw [norm_add_sq_real]
  simp [real_inner_smul_right, EuclideanSpace.inner_single_right, coordinateErase_apply,
    norm_smul, PiLp.norm_single, Real.norm_eq_abs, sq_abs]

/-- Inside the small tangential ball, the sphere fills exactly the upper side of its graph. -/
lemma ballGraphHeight_graph_membership {n : ℕ} (i : Fin n) {r : ℝ} (hr : 0 < r)
    {x : EuclideanSpace ℝ (Fin n)} (ht : ‖coordinateErase i x‖ ≤ r / 2)
    (hs : |x i| < r / 2) :
    graphShear i (ballGraphHeight r) x ∈ ball (r • EuclideanSpace.single i 1) r ↔
      0 < x i := by
  have heq : graphShear i (ballGraphHeight r) x - r • EuclideanSpace.single i 1 =
      coordinateErase i x +
        (x i - Real.sqrt (r ^ 2 - ‖coordinateErase i x‖ ^ 2)) •
          EuclideanSpace.single i 1 := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [graphShear, ballGraphHeight, coordinateErase_apply]
      ring
    · simp [graphShear, ballGraphHeight, coordinateErase_apply, hj]
  have hnormsq := norm_sq_coordinateErase_add_normal i x
    (x i - Real.sqrt (r ^ 2 - ‖coordinateErase i x‖ ^ 2))
  have ht0 := norm_nonneg (coordinateErase i x)
  have hsq : 0 ≤ r ^ 2 - ‖coordinateErase i x‖ ^ 2 := by nlinarith
  have hroot := Real.sq_sqrt hsq
  have hrootlower := sqrt_radius_sq_sub_norm_sq_ge_half hr ht
  have hxi : x i < r / 2 := (le_abs_self _).trans_lt hs
  rw [mem_ball, dist_eq_norm, heq]
  constructor
  · intro hx
    have hnorm0 := norm_nonneg
      (coordinateErase i x +
        (x i - Real.sqrt (r ^ 2 - ‖coordinateErase i x‖ ^ 2)) •
          EuclideanSpace.single i 1)
    have hprod : x i *
        (x i - 2 * Real.sqrt (r ^ 2 - ‖coordinateErase i x‖ ^ 2)) < 0 := by
      nlinarith
    rcases mul_neg_iff.mp hprod with h | h
    · exact h.1
    · linarith [h.2]
  · intro hx
    have hprod : x i *
        (x i - 2 * Real.sqrt (r ^ 2 - ‖coordinateErase i x‖ ^ 2)) < 0 :=
      mul_neg_of_pos_of_neg hx (by linarith)
    nlinarith

/-- A dimension-dependent elementary bound places small coordinate cubes inside norm balls. -/
lemma norm_le_succ_card_mul_of_mem_coordinateCube {n : ℕ} {R : ℝ} (hR : 0 ≤ R)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ coordinateCube n R) :
    ‖x‖ ≤ (n + 1 : ℝ) * R := by
  have hsq : ‖x‖ ^ 2 ≤ (n : ℝ) * R ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin n, R ^ 2 := Finset.sum_le_sum fun i _ => by
        have hi := (hx i).le
        nlinarith [le_abs_self (x i), neg_le_abs (x i), sq_abs (x i)]
      _ = _ := by simp
  have hn : (n : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
  have hsq' := mul_le_mul_of_nonneg_right hn (sq_nonneg R)
  have hR' : 0 ≤ (n + 1 : ℝ) * R := mul_nonneg (by positivity) hR
  nlinarith

lemma coordinateErase_mem_half_ball_of_mem_small_cube {n : ℕ} (i : Fin n)
    {r : ℝ} (hr : 0 < r) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ coordinateCube n (r / (4 * (n + 1 : ℝ)))) :
    coordinateErase i x ∈ closedBall 0 (r / 2) ∧ |x i| < r / 2 := by
  have hR : 0 < r / (4 * (n + 1 : ℝ)) := by positivity
  have hnorm := norm_le_succ_card_mul_of_mem_coordinateCube hR.le hx
  have hsmall : (n + 1 : ℝ) * (r / (4 * (n + 1 : ℝ))) = r / 4 := by
    field_simp
  rw [hsmall] at hnorm
  have herase : ‖coordinateErase i x‖ ≤ ‖x‖ := by
    have h := (lipschitzWith_coordinateErase i).dist_le_mul x 0
    have hzero : coordinateErase i (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      ext j
      simp [coordinateErase_apply]
    simpa only [hzero, dist_zero_right, NNReal.coe_one, one_mul] using h
  have hcoord : |x i| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  constructor
  · simpa only [mem_closedBall, dist_zero_right] using herase.trans (by linarith : ‖x‖ ≤ r / 2)
  · exact hcoord.trans_lt (by linarith)

/-- A rigid placement of the standard lower hemisphere gives a genuine chart for a ball. -/
theorem exists_lipschitzGraphChart_ball_of_placement {n : ℕ} (i : Fin n)
    {r : ℝ} (hr : 0 < r)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∃ c : LipschitzGraphChart n,
      c.IsChartFor (ball (a (r • EuclideanSpace.single i 1)) r) ∧ a 0 ∈ c.region := by
  obtain ⟨g, hg, heq⟩ := exists_lipschitz_extension_real
    (ballGraphHeight_lipschitzOn_half_ball (n := n) hr)
  let R : ℝ := r / (4 * (n + 1 : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  let c : LipschitzGraphChart n :=
    ⟨i, R, hR, g, 1, hg, a⟩
  have hmem (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ coordinateCube n R) :
      c.homeomorph y ∈ ball (a (r • EuclideanSpace.single i 1)) r ↔ 0 < y i := by
    have hsmall := coordinateErase_mem_half_ball_of_mem_small_cube i hr hy
    have hshear : graphShear i g y = graphShear i (ballGraphHeight r) y := by
      simp only [graphShear, ← heq hsmall.1]
    change dist (a (graphShear i g y)) (a (r • EuclideanSpace.single i 1)) < r ↔ _
    rw [a.isometry.dist_eq, hshear]
    exact ballGraphHeight_graph_membership i hr
      (by simpa only [mem_closedBall, dist_zero_right] using hsmall.1) hsmall.2
  refine ⟨c, ?_, ?_⟩
  · change c.homeomorph '' coordinateHalfCube i R =
      ball (a (r • EuclideanSpace.single i 1)) r ∩
        (c.homeomorph '' coordinateCube n R)
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(hmem y hy.1).mpr hy.2, ⟨y, hy.1, rfl⟩⟩
    · rintro ⟨hz, y, hy, rfl⟩
      exact ⟨y, ⟨hy, (hmem y hy).mp hz⟩, rfl⟩
  · have hzero : coordinateErase i (0 : EuclideanSpace ℝ (Fin n)) = 0 := by
      ext j
      simp [coordinateErase_apply]
    have hgzero : g 0 = 0 := by
      rw [← heq (by simpa only [mem_closedBall, dist_self] using (by linarith : 0 ≤ r / 2))]
      simp [ballGraphHeight, Real.sqrt_sq_eq_abs, abs_of_pos hr]
    refine ⟨0, ?_, ?_⟩
    · intro j
      simpa only [PiLp.zero_apply, abs_zero] using hR
    · change a (graphShear i g 0) = a 0
      simp only [graphShear, hzero, hgzero, zero_smul, zero_add]

/-- A reflection followed by a translation places the inward normal segment of a ball. -/
theorem exists_affineIsometry_ball_placement {n : ℕ} (i : Fin n) {r : ℝ}
    (hr : 0 < r) {z x : EuclideanSpace ℝ (Fin n)} (hx : ‖z - x‖ = r) :
    ∃ a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n),
      a 0 = x ∧ a (r • EuclideanSpace.single i 1) = z := by
  let e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Submodule.reflection (ℝ ∙ (r • EuclideanSpace.single i 1 - (z - x)))ᗮ
  have he : e (r • EuclideanSpace.single i 1) = z - x :=
    Submodule.reflection_sub (by
      rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
        abs_of_pos hr, hx])
  refine ⟨e.toAffineIsometryEquiv.trans (AffineIsometryEquiv.vaddConst ℝ x), ?_, ?_⟩
  · simp
  · simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply,
      AffineIsometryEquiv.coe_vaddConst, LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      vadd_eq_add, he, sub_add_cancel]

/-- Every point of the sphere has a globally specified Lipschitz graph chart for the ball. -/
theorem exists_lipschitzGraphChart_ball {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ sphere z r) :
    ∃ c : LipschitzGraphChart n, c.IsChartFor (ball z r) ∧ x ∈ c.region := by
  have hnorm : ‖z - x‖ = r := by simpa only [mem_sphere, dist_eq_norm, norm_sub_rev] using hx
  have hex : ∃ i : Fin n, (z - x) i ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : z - x = 0 := by
      ext i
      exact h i
    rw [hzero, norm_zero] at hnorm
    linarith
  obtain ⟨i, _⟩ := hex
  obtain ⟨a, ha0, har⟩ := exists_affineIsometry_ball_placement i hr hnorm
  simpa only [ha0, har] using exists_lipschitzGraphChart_ball_of_placement i hr a

/-- Euclidean balls of positive radius have Lipschitz boundary, with no dimension restriction. -/
theorem hasLipschitzBoundary_ball {n : ℕ} (z : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) : HasLipschitzBoundary (ball z r) := by
  intro x hx
  apply exists_lipschitzGraphChart_ball z hr
  simpa only [frontier_ball z hr.ne'] using hx

end LiquidDrop
