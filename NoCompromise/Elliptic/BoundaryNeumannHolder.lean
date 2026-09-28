import NoCompromise.Elliptic.BoundaryNeumannCoefficients
import NoCompromise.Elliptic.CampanatoHolderEmbedding

/-! Hölder gluing of the reflected coefficients across the flat face. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_mem_closure {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball 0 1) (hp : 0 ≤ x (Fin.last 2)) :
    x ∈ closure (boundaryHalfBall 1) := by
  by_cases hh : 0 < x (Fin.last 2)
  · exact subset_closure ⟨hx, hh⟩
  have hz : x (Fin.last 2) = 0 := le_antisymm (le_of_not_gt hh) hp
  have hnorm : ‖x‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := min (1 - ‖x‖) ε / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htball : t < 1 - ‖x‖ := by
    have := min_le_left (1 - ‖x‖) ε
    dsimp [t]
    linarith
  have htε : t < ε := by
    have := min_le_right (1 - ‖x‖) ε
    dsimp [t]
    linarith
  have hn : ‖EuclideanSpace.single (Fin.last 2) t‖ = t := by
    simp only [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨x + EuclideanSpace.single (Fin.last 2) t, ⟨?_, ?_⟩, ?_⟩
  · simp only [mem_ball, dist_zero_right]
    have := norm_add_le x (EuclideanSpace.single (Fin.last 2) t)
    rw [hn] at this
    linarith
  · change 0 < (x + EuclideanSpace.single (Fin.last 2) t) (Fin.last 2)
    simpa only [PiLp.add_apply, PiLp.single_apply, ite_true, hz, zero_add] using ht
  · simpa only [dist_self_add_right, hn] using htε

lemma boundary_neumann_reflection_mem_ball {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball 0 1) : coordinateReflection (Fin.last 2) x ∈ ball 0 1 := by
  simpa only [mem_ball, dist_zero_right, (coordinateReflection (Fin.last 2)).norm_map] using hx

lemma boundary_neumann_projection_dist {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : 0 ≤ x (Fin.last 2)) (hy : y (Fin.last 2) ≤ 0) :
    dist x (graphAppendN (graphProjectionN 2 x) 0) ≤ dist x y ∧
      dist (graphAppendN (graphProjectionN 2 x) 0) (coordinateReflection (Fin.last 2) y) ≤
        dist x y := by
  constructor
  · rw [boundary_dist_flat_projection, abs_of_nonneg hx]
    have hh := PiLp.norm_apply_le (x - y) (Fin.last 2)
    simp only [PiLp.sub_apply, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hy.trans hx))]
      at hh
    rw [dist_eq_norm]
    linarith
  · have hs : dist (graphAppendN (graphProjectionN 2 x) 0)
          (coordinateReflection (Fin.last 2) y) ^ 2 ≤ dist x y ^ 2 := by
      simp only [EuclideanSpace.dist_sq_eq]
      apply Finset.sum_le_sum
      intro i _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [graphAppendN_last, boundary_reflection_last, Real.dist_eq,
          zero_sub, neg_neg, sq_abs]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hx hy]
      · simp only [graphAppendN_castSucc, graphProjectionN_apply, coordinateReflection_apply,
          Fin.castSucc_ne_last, ite_false, le_refl]
    nlinarith [dist_nonneg (x := graphAppendN (graphProjectionN 2 x) 0)
      (y := coordinateReflection (Fin.last 2) y), dist_nonneg (x := x) (y := y)]

def boundaryNeumannReflect {E : Type*} (f : EuclideanSpace ℝ (Fin 3) → E)
    (T : E → E) (x : EuclideanSpace ℝ (Fin 3)) : E :=
  if 0 ≤ x (Fin.last 2) then f x else T (f (coordinateReflection (Fin.last 2) x))

lemma boundaryNeumannReflect_holder {E : Type*} [NormedAddCommGroup E]
    {a K : ℝ} (ha : 0 ≤ a) (hK : 0 ≤ K)
    (f : EuclideanSpace ℝ (Fin 3) → E) (T : E → E) (hT : Isometry T)
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ K * dist x y ^ a)
    (hfix : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → T (f x) = f x) :
    ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖boundaryNeumannReflect f T x - boundaryNeumannReflect f T y‖ ≤
        (2 * K) * dist x y ^ a := by
  have hnorm (u v : E) : ‖T u - T v‖ = ‖u - v‖ := by
    simpa only [dist_eq_norm] using hT.dist_eq u v
  have hcross (x y : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ ball 0 1)
      (hy : y ∈ ball 0 1) (hp : 0 ≤ x (Fin.last 2)) (hn : y (Fin.last 2) < 0) :
      ‖f x - T (f (coordinateReflection (Fin.last 2) y))‖ ≤ (2 * K) * dist x y ^ a := by
    let z := graphAppendN (graphProjectionN 2 x) 0
    have hzball : z ∈ ball 0 1 := by
      simp only [mem_ball, dist_zero_right] at hx ⊢
      exact (boundary_flat_projection_norm_le x).trans_lt hx
    have hzflat : z (Fin.last 2) = 0 := graphAppendN_last _ _
    have hz := boundary_neumann_mem_closure hzball hzflat.ge
    have hyR := boundary_neumann_mem_closure (boundary_neumann_reflection_mem_ball hy)
      (by rw [boundary_reflection_last]; linarith :
        0 ≤ coordinateReflection (Fin.last 2) y (Fin.last 2))
    have hd := boundary_neumann_projection_dist hp hn.le
    calc
      _ ≤ ‖f x - f z‖ + ‖f z - T (f (coordinateReflection (Fin.last 2) y))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖f x - f z‖ + ‖f z - f (coordinateReflection (Fin.last 2) y)‖ := by
        conv_lhs => rhs; arg 1; lhs; rw [← hfix z hz hzflat]
        rw [hnorm]
      _ ≤ K * dist x z ^ a + K * dist z (coordinateReflection (Fin.last 2) y) ^ a :=
        add_le_add (hh x (boundary_neumann_mem_closure hx hp) z hz)
          (hh z hz _ hyR)
      _ ≤ K * dist x y ^ a + K * dist x y ^ a := by
        exact add_le_add (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd.1 ha) hK)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hd.2 ha) hK)
      _ = _ := by ring
  intro x hx y hy
  by_cases hp : 0 ≤ x (Fin.last 2) <;> by_cases hq : 0 ≤ y (Fin.last 2)
  · simp only [boundaryNeumannReflect, ite_eq_left hp, ite_eq_left hq]
    exact (hh x (boundary_neumann_mem_closure hx hp) y
      (boundary_neumann_mem_closure hy hq)).trans
        (mul_le_mul_of_nonneg_right (by linarith : K ≤ 2 * K) (Real.rpow_nonneg dist_nonneg a))
  · simp only [boundaryNeumannReflect, ite_eq_left hp, ite_eq_right hq]
    exact hcross x y hx hy hp (lt_of_not_ge hq)
  · simp only [boundaryNeumannReflect, ite_eq_right hp, ite_eq_left hq]
    rw [norm_sub_rev, dist_comm x y]
    exact hcross y x hy hx hq (lt_of_not_ge hp)
  · simp only [boundaryNeumannReflect, ite_eq_right hp, ite_eq_right hq, hnorm]
    have hxR := boundary_neumann_mem_closure (boundary_neumann_reflection_mem_ball hx)
      (by rw [boundary_reflection_last]; linarith [lt_of_not_ge hp] :
        0 ≤ coordinateReflection (Fin.last 2) x (Fin.last 2))
    have hyR := boundary_neumann_mem_closure (boundary_neumann_reflection_mem_ball hy)
      (by rw [boundary_reflection_last]; linarith [lt_of_not_ge hq] :
        0 ≤ coordinateReflection (Fin.last 2) y (Fin.last 2))
    have hb := hh _ hxR _ hyR
    rw [(coordinateReflection (Fin.last 2)).dist_map] at hb
    exact hb.trans
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ 2 * K) (Real.rpow_nonneg dist_nonneg a))

lemma boundaryNeumannCoefficient_holder {a HA : ℝ} (ha : 0 ≤ a) (hHA : 0 ≤ HA)
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖A x - A y‖ ≤ HA * dist x y ^ a)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
          A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) :
    ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖boundaryNeumannCoefficient A x - boundaryNeumannCoefficient A y‖ ≤
        (2 * HA) * dist x y ^ a := by
  apply boundaryNeumannReflect_holder ha hHA A boundaryNeumannConjugate
  · apply Isometry.of_dist_eq
    intro B C
    simp only [dist_eq_norm, ← boundaryNeumannConjugate_sub, boundaryNeumannConjugate_norm]
  · exact hh
  · intro x hx hz
    exact boundaryNeumannConjugate_eq_of_cross_zero (hcross x hx hz)

lemma boundaryNeumannDatum_holder {a HH : ℝ} (ha : 0 ≤ a) (hHH : 0 ≤ HH)
    (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖H x - H y‖ ≤ HH * dist x y ^ a)
    (hzero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0) :
    ∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1,
      ‖boundaryNeumannDatum H x - boundaryNeumannDatum H y‖ ≤ (2 * HH) * dist x y ^ a := by
  apply boundaryNeumannReflect_holder ha hHH H (coordinateReflection (Fin.last 2))
    (coordinateReflection (Fin.last 2)).isometry hh
  intro x hx hz
  exact boundary_neumann_reflection_fixed (hzero x hx hz)

lemma boundaryNeumannCoefficient_continuousOn {a HA : ℝ} (ha : 0 < a) (hHA : 0 ≤ HA)
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖A x - A y‖ ≤ HA * dist x y ^ a)
    (hcross : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
      ∀ i : Fin 3, i ≠ Fin.last 2 →
        A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
          A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) :
    ContinuousOn (boundaryNeumannCoefficient A) (ball 0 1) :=
  campanato_continuousOn_of_holder_bound (by positivity) ha
    (boundaryNeumannCoefficient_holder ha.le hHA A hh hcross)

lemma boundaryNeumannDatum_continuousOn {a HH : ℝ} (ha : 0 < a) (hHH : 0 ≤ HH)
    (H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖H x - H y‖ ≤ HH * dist x y ^ a)
    (hzero : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0) :
    ContinuousOn (boundaryNeumannDatum H) (ball 0 1) :=
  campanato_continuousOn_of_holder_bound (by positivity) ha
    (boundaryNeumannDatum_holder ha.le hHH H hh hzero)

lemma boundaryNeumannCoefficient_bound {cap : ℝ}
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) :
    ∀ x ∈ ball 0 1, ‖boundaryNeumannCoefficient A x‖ ≤ cap := by
  intro x hx
  by_cases hp : 0 ≤ x (Fin.last 2)
  · rw [boundaryNeumannCoefficient_eq_upper A hp]
    exact hb x (boundary_neumann_mem_closure hx hp)
  · rw [boundaryNeumannCoefficient, ite_eq_right hp, boundaryNeumannConjugate_norm]
    apply hb
    apply boundary_neumann_mem_closure (boundary_neumann_reflection_mem_ball hx)
    rw [boundary_reflection_last]
    linarith [lt_of_not_ge hp]

lemma boundaryNeumannCoefficient_elliptic {lam : ℝ}
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3))
    (hell : ∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) :
    ∀ x ∈ ball 0 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (boundaryNeumannCoefficient A x ξ) ξ := by
  intro x hx ξ
  by_cases hp : 0 ≤ x (Fin.last 2)
  · rw [boundaryNeumannCoefficient_eq_upper A hp]
    exact hell x (boundary_neumann_mem_closure hx hp) ξ
  · rw [boundaryNeumannCoefficient, ite_eq_right hp]
    apply boundaryNeumannConjugate_elliptic
    apply hell
    apply boundary_neumann_mem_closure (boundary_neumann_reflection_mem_ball hx)
    rw [boundary_reflection_last]
    linarith [lt_of_not_ge hp]

end LiquidDrop
