import NoCompromise.Elliptic.BoundaryNeumannInhomLift

/-! Quantitative estimates for the vertical primitive of the interior source. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Contraction of the normal coordinate, leaving the tangential coordinates fixed. -/
def boundaryNeumannVerticalContraction (t : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) :=
  graphAppendN (graphProjectionN 2 x) (t * x (Fin.last 2))

lemma boundaryNeumannVerticalContraction_continuous (t : ℝ) :
    Continuous (boundaryNeumannVerticalContraction t) := by
  unfold boundaryNeumannVerticalContraction graphAppendN
  fun_prop

lemma boundaryNeumannVerticalContraction_norm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (x : EuclideanSpace ℝ (Fin 3)) : ‖boundaryNeumannVerticalContraction t x‖ ≤ ‖x‖ := by
  have h1 := norm_sq_graphProjectionN x
  have h2 := norm_sq_graphProjectionN (boundaryNeumannVerticalContraction t x)
  simp only [boundaryNeumannVerticalContraction, graphProjectionN_append, graphAppendN_last] at h2
  change ‖boundaryNeumannVerticalContraction t x‖ ^ 2 =
    ‖graphProjectionN 2 x‖ ^ 2 + (t * x (Fin.last 2)) ^ 2 at h2
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hm := mul_le_mul_of_nonneg_right ht2 (sq_nonneg (x (Fin.last 2)))
  nlinarith [norm_nonneg x, norm_nonneg (boundaryNeumannVerticalContraction t x)]

lemma boundaryNeumannVerticalContraction_dist {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (x y : EuclideanSpace ℝ (Fin 3)) :
    dist (boundaryNeumannVerticalContraction t x) (boundaryNeumannVerticalContraction t y) ≤
      dist x y := by
  have he : boundaryNeumannVerticalContraction t x - boundaryNeumannVerticalContraction t y =
      boundaryNeumannVerticalContraction t (x - y) := by
    simp only [boundaryNeumannVerticalContraction, graphAppendN, map_sub,
      PiLp.sub_apply, mul_sub, sub_smul]
    abel
  simpa only [dist_eq_norm, he] using boundaryNeumannVerticalContraction_norm ht (x - y)

lemma boundaryNeumannVerticalContraction_mem_closure {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1)) :
    boundaryNeumannVerticalContraction t x ∈ closure (boundaryHalfBall 1) := by
  have hm : MapsTo (boundaryNeumannVerticalContraction t) (boundaryHalfBall 1)
      (closure (boundaryHalfBall 1)) := by
    intro y hy
    apply boundary_neumann_mem_closure
    · simp only [mem_ball, dist_zero_right]
      exact (boundaryNeumannVerticalContraction_norm ht y).trans_lt
        (by simpa only [mem_ball, dist_zero_right] using hy.1)
    · simpa only [boundaryNeumannVerticalContraction, graphAppendN_last] using
        mul_nonneg ht.1 (le_of_lt hy.2)
  exact hm.closure_left (boundaryNeumannVerticalContraction_continuous t) isClosed_closure hx

lemma boundary_neumann_closed_norm_le {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closure (boundaryHalfBall 1)) : ‖x‖ ≤ 1 := by
  have hs : closure (boundaryHalfBall 1) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closure_minimal (inter_subset_left.trans ball_subset_closedBall) isClosed_closedBall
  simpa only [mem_closedBall, dist_zero_right] using hs hx

lemma boundary_neumann_closed_height {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ closure (boundaryHalfBall 1)) : x (Fin.last 2) ∈ Icc (0 : ℝ) 1 := by
  have hs : closure (boundaryHalfBall 1) ⊆
      {x : EuclideanSpace ℝ (Fin 3) | 0 ≤ x (Fin.last 2)} :=
    closure_minimal (fun y hy => show 0 ≤ y (Fin.last 2) from le_of_lt hy.2)
      (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
  refine ⟨hs hx, ?_⟩
  have h := (PiLp.norm_apply_le x (Fin.last 2)).trans (boundary_neumann_closed_norm_le hx)
  exact (le_abs_self _).trans h

lemma boundaryNeumannPrimitive_normalized (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryNeumannPrimitive f x =
      (x (Fin.last 2) * ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)) •
        EuclideanSpace.single (Fin.last 2) 1 := by
  have he := intervalIntegral.smul_integral_comp_mul_right
    (fun s => f (graphAppendN (graphProjectionN 2 x) s)) (x (Fin.last 2))
      (a := 0) (b := 1)
  simp only [smul_eq_mul, zero_mul, one_mul] at he
  exact congrArg (fun r : ℝ => r • EuclideanSpace.single (Fin.last 2) 1) he.symm

lemma boundaryNeumannPrimitive_normalized_integrable
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1)) :
    IntervalIntegrable (fun t => f (boundaryNeumannVerticalContraction t x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply hf.comp
  · unfold boundaryNeumannVerticalContraction graphAppendN
    fun_prop
  · intro t ht
    exact boundaryNeumannVerticalContraction_mem_closure
      (by simpa only [uIcc_of_le zero_le_one] using ht) hx

lemma boundaryNeumannPrimitive_normalized_bound {Bf : ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1)) :
    ‖∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)‖ ≤ Bf := by
  have he := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => f (boundaryNeumannVerticalContraction t x))
    (a := (0 : ℝ)) (b := 1) (C := Bf) (fun t ht =>
      hb _ (boundaryNeumannVerticalContraction_mem_closure
        (by simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one]
          using Ioc_subset_Icc_self ht) hx))
  simpa using he

lemma boundaryNeumannPrimitive_bound {Bf : ℝ} (hBf : 0 ≤ Bf)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1)) :
    ‖boundaryNeumannPrimitive f x‖ ≤ Bf := by
  rw [boundaryNeumannPrimitive_normalized, norm_smul, PiLp.norm_single, norm_one, mul_one,
    norm_mul, Real.norm_of_nonneg (boundary_neumann_closed_height hx).1]
  exact (mul_le_mul_of_nonneg_left (boundaryNeumannPrimitive_normalized_bound hb hx)
    (boundary_neumann_closed_height hx).1).trans
      (by simpa using mul_le_mul_of_nonneg_right (boundary_neumann_closed_height hx).2 hBf)

/-- Before converting the Lipschitz term to an α-Hölder term, the primitive
obeys the stronger mixed estimate `Hf * dist^a + Bf * dist`. -/
lemma boundaryNeumannPrimitive_mixed_bound {a Bf Hf : ℝ} (ha : 0 ≤ a)
    (hHf : 0 ≤ Hf) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1))
    (hy : y ∈ closure (boundaryHalfBall 1)) :
    ‖boundaryNeumannPrimitive f x - boundaryNeumannPrimitive f y‖ ≤
      Hf * dist x y ^ a + Bf * dist x y := by
  let I := fun x => ∫ t in (0 : ℝ)..1, f (boundaryNeumannVerticalContraction t x)
  have hi : ‖I x - I y‖ ≤ Hf * dist x y ^ a := by
    dsimp only [I]
    rw [← intervalIntegral.integral_sub
      (boundaryNeumannPrimitive_normalized_integrable hf hx)
      (boundaryNeumannPrimitive_normalized_integrable hf hy)]
    have he := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := Hf * dist x y ^ a) (fun t ht => by
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa only [min_eq_left zero_le_one, max_eq_right zero_le_one]
            using Ioc_subset_Icc_self ht
        exact (hh _ (boundaryNeumannVerticalContraction_mem_closure ht' hx)
          _ (boundaryNeumannVerticalContraction_mem_closure ht' hy)).trans
            (mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (dist_nonneg)
                (boundaryNeumannVerticalContraction_dist ht' x y) ha) hHf))
    simpa using he
  have hn : ‖x (Fin.last 2) - y (Fin.last 2)‖ ≤ dist x y := by
    simpa only [dist_eq_norm, PiLp.sub_apply] using PiLp.norm_apply_le (x - y) (Fin.last 2)
  have he : x (Fin.last 2) * I x - y (Fin.last 2) * I y =
      x (Fin.last 2) * (I x - I y) + (x (Fin.last 2) - y (Fin.last 2)) * I y := by ring
  rw [boundaryNeumannPrimitive_normalized, boundaryNeumannPrimitive_normalized, ← sub_smul,
    norm_smul, PiLp.norm_single, norm_one, mul_one]
  change ‖x (Fin.last 2) * I x - y (Fin.last 2) * I y‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖x (Fin.last 2) * (I x - I y)‖ +
        ‖(x (Fin.last 2) - y (Fin.last 2)) * I y‖ := norm_add_le _ _
    _ ≤ 1 * (Hf * dist x y ^ a) + dist x y * Bf := by
      simp only [norm_mul]
      exact add_le_add
        (mul_le_mul (by simpa only [Real.norm_of_nonneg (boundary_neumann_closed_height hx).1]
          using (boundary_neumann_closed_height hx).2) hi (norm_nonneg _) zero_le_one)
        (mul_le_mul hn (boundaryNeumannPrimitive_normalized_bound hb hy)
          (norm_nonneg _) (dist_nonneg))
    _ = _ := by ring

lemma boundaryNeumannPrimitive_holder {a Bf Hf : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hBf : 0 ≤ Bf) (hHf : 0 ≤ Hf) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a)
    {x y : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ closure (boundaryHalfBall 1))
    (hy : y ∈ closure (boundaryHalfBall 1)) :
    ‖boundaryNeumannPrimitive f x - boundaryNeumannPrimitive f y‖ ≤
      (Hf + 2 * Bf) * dist x y ^ a := by
  have hd : dist x y ≤ 2 := by
    have he := (norm_sub_le x y).trans (add_le_add
      (boundary_neumann_closed_norm_le hx) (boundary_neumann_closed_norm_le hy))
    rw [dist_eq_norm]
    linarith
  have hp : dist x y ≤ 2 * dist x y ^ a := by
    by_cases hd1 : dist x y ≤ 1
    · have he := Real.self_le_rpow_of_le_one (dist_nonneg (x := x) (y := y)) hd1 ha1
      linarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) a]
    · have he := Real.one_le_rpow (le_of_not_ge hd1) ha
      linarith
  have he := boundaryNeumannPrimitive_mixed_bound ha hHf hf hb hh hx hy
  have hm := mul_le_mul_of_nonneg_left hp hBf
  nlinarith

lemma boundaryNeumannPrimitive_continuousOn {a Bf Hf : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hBf : 0 ≤ Bf) (hHf : 0 ≤ Hf) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hb : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a) :
    ContinuousOn (boundaryNeumannPrimitive f) (closure (boundaryHalfBall 1)) := by
  apply campanato_continuousOn_of_holder_bound (show 0 ≤ Hf + 2 * Bf by positivity) ha
  intro x hx y hy
  exact boundaryNeumannPrimitive_holder ha.le ha1 hBf hHf hf hb hh hx hy

end LiquidDrop
