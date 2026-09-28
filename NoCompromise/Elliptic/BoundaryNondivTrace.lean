import NoCompromise.Elliptic.BoundaryNondivQuotient
import NoCompromise.Elliptic.BoundaryHolderTranslate
import NoCompromise.Elliptic.BoundaryHolderTraceAlgebra
import NoCompromise.Elliptic.BoundaryNeumannWeak
import NoCompromise.Elliptic.BoundaryNeumannHolder
import NoCompromise.Sobolev.H1TraceContinuous

/-!
# Zero flat trace for tangential nondivergence quotients

Classical zero boundary values of a continuous half-ball H¹ function imply the
actual localized trace condition. Tangential translation, subtraction and scalar
multiplication then preserve that condition, with the genuine quotient gradient.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_nondiv_fold_mem_closure {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball 0 1) : coordinateFold (Fin.last 2) x ∈ closure (boundaryHalfBall 1) := by
  apply boundary_neumann_mem_closure
  · by_cases hp : 0 ≤ x (Fin.last 2)
    · simpa only [coordinateFold_eq_self hp] using hx
    · rw [coordinateFold_eq_reflection (le_of_not_ge hp)]
      exact boundary_neumann_reflection_mem_ball hx
  · simp only [coordinateFold_apply, ite_true]
    exact abs_nonneg _

lemma boundary_nondiv_even_eq_fold
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hz : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → u x = 0)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 1) :
    boundaryEvenFunction u x = u (coordinateFold (Fin.last 2) x) := by
  rcases lt_trichotomy (x (Fin.last 2)) 0 with hn | he | hp
  · rw [coordinateFold_eq_reflection hn.le, ← boundaryEvenFunction_reflect u x]
    apply boundaryEvenFunction_eq_upper
    refine ⟨boundary_neumann_reflection_mem_ball hx, ?_⟩
    change 0 < coordinateReflection (Fin.last 2) x (Fin.last 2)
    rw [boundary_reflection_last]
    exact neg_pos.mpr hn
  · have hxU : x ∉ boundaryHalfBall 1 := fun hh => by
      have hh' : 0 < x (Fin.last 2) := hh.2
      linarith
    have hxR : coordinateReflection (Fin.last 2) x ∉ boundaryHalfBall 1 := by
      intro hh
      have hh' : 0 < coordinateReflection (Fin.last 2) x (Fin.last 2) := hh.2
      rw [boundary_reflection_last, he] at hh'
      simp at hh'
    rw [coordinateFold_eq_self he.ge, hz x (boundary_neumann_mem_closure hx he.ge) he]
    simp only [boundaryEvenFunction, indicator_of_notMem hxU, indicator_of_notMem hxR, add_zero]
  · rw [coordinateFold_eq_self hp.le]
    exact boundaryEvenFunction_eq_upper u ⟨hx, hp⟩

/-- The classical hypotheses in the boundary nondivergence theorem give the
actual localized zero trace; no regularity outside the closed half ball is used. -/
theorem HasH1GradientOn.boundary_nondiv_zero_trace
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hu : HasH1GradientOn u D (boundaryHalfBall 1))
    (hc : ContinuousOn u (closure (boundaryHalfBall 1)))
    (hz : ∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → u x = 0) :
    HasZeroFlatTraceOn u D (ball 0 1) := by
  have hcE : ContinuousOn (boundaryEvenFunction u) (ball 0 1) :=
    (hc.comp (lipschitzWith_coordinateFold (Fin.last 2)).continuous.continuousOn
      (fun _ hx => boundary_nondiv_fold_mem_closure hx)).congr
        (fun _ hx => boundary_nondiv_even_eq_fold hz hx)
  intro ζ hζ hcζ hsζ
  have hζ1 : ContDiff ℝ 1 ζ := hζ.of_le (by simp)
  have hH := hu.boundary_even_h1.locallyH1.mul_compact_cutoff hζ1 hcζ hsζ
  have hcont : Continuous (fun x => ζ x * boundaryEvenFunction u x) :=
    (hζ.continuous.continuousOn.mul hcE).continuous_of_tsupport_subset isOpen_ball
      (tsupport_mul_subset_left.trans hsζ)
  have hT := flatTraceFunction_eq_restrict_ae_of_continuous hH hcont
  have hzero (x : EuclideanSpace ℝ (Fin 2)) : boundaryEvenFunction u (graphAppendN x 0) = 0 := by
    have hn : graphAppendN x 0 ∉ boundaryHalfBall 1 := by
      intro hh
      have hh' : 0 < (graphAppendN x 0) (Fin.last 2) := hh.2
      simp only [graphAppendN_last, lt_self_iff_false] at hh'
    have hnR : coordinateReflection (Fin.last 2) (graphAppendN x 0) ∉ boundaryHalfBall 1 := by
      simpa only [boundary_reflection_flat] using hn
    simp only [boundaryEvenFunction, indicator_of_notMem hn, indicator_of_notMem hnR, add_zero]
  have hcongr := boundaryLocalizedFlatTrace_congr_ae measurableSet_ball hsζ
    (f := u) (g := boundaryEvenFunction u) (G := D) (H := boundaryEvenField D)
    (by
      filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
      exact (boundaryEvenFunction_eq_upper u hx).symm)
    (by
      filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
      exact (boundaryEvenField_eq_upper D hx).symm)
  filter_upwards [hcongr, hT] with x hx hy
  change boundaryLocalizedFlatTrace u D ζ x = 0
  rw [hx]
  change flatTraceFunction _ _ x = 0
  rw [hy, hzero, mul_zero]


/-- Scalar multiplication preserves the actual localized flat trace. -/
lemma HasZeroFlatTraceOn.boundary_nondiv_const_mul {k : ℕ}
    {u : EuclideanSpace ℝ (Fin (k + 1)) → ℝ}
    {D : EuclideanSpace ℝ (Fin (k + 1)) → EuclideanSpace ℝ (Fin (k + 1))}
    {W : Set (EuclideanSpace ℝ (Fin (k + 1)))}
    (hu : HasZeroFlatTraceOn u D W) (c : ℝ) :
    HasZeroFlatTraceOn (fun x => c * u x) (fun x => c • D x) W := by
  intro ζ hζ hcζ hsζ
  have he : boundaryLocalizedFlatTrace (fun x => c * u x) (fun x => c • D x) ζ =
      c • boundaryLocalizedFlatTrace u D ζ := by
    unfold boundaryLocalizedFlatTrace
    have hfun : (fun x => ζ x * (c * u x)) = c • (fun x => ζ x * u x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    have hgrad : (fun x => ζ x • (c • D x) + (c * u x) • gradient ζ x) =
        c • (fun x => ζ x • D x + u x • gradient ζ x) := by
      funext x
      simp only [Pi.smul_apply, smul_add, smul_smul]
      rw [mul_comm (ζ x) c]
    rw [hfun, hgrad, flatTraceFunction_smul]
  rw [he]
  filter_upwards [hu ζ hζ hcζ hsζ] with x hx
  simp only [Pi.smul_apply, hx, Pi.zero_apply, smul_zero]

/-- Tangential quotients retain the actual zero trace, including the specified
weak gradient. The assertion also holds at the conventional zero step. -/
theorem HasZeroFlatTraceOn.boundary_nondiv_quotient
    {u : EuclideanSpace ℝ (Fin 3) → ℝ}
    {D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {r R h : ℝ} (hrR : r ≤ R)
    (hu : HasH1GradientOn u D (boundaryHalfBall R))
    (hT : HasZeroFlatTraceOn u D (ball 0 R))
    {i : Fin 3} (hi : i ≠ Fin.last 2) (hh : |h| ≤ R - r) :
    HasZeroFlatTraceOn (coordinateDifferenceQuotient i h u)
      (coordinateDifferenceQuotient i h D) (ball 0 r) := by
  let c := h • EuclideanSpace.single i (1 : ℝ)
  have hclast : c (Fin.last 2) = 0 := by
    have hne : (2 : Fin 3) ≠ i := Ne.symm hi
    simp [c, PiLp.smul_apply, hne]
  have hc : graphAppendN (graphProjectionN 2 c) 0 = c := by
    simpa only [hclast] using graphAppendN_projection c
  have hmap (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ ball 0 r) : x + c ∈ ball 0 R := by
    rw [mem_ball_zero_iff] at hx ⊢
    have hnorm : ‖c‖ = |h| := by
      simp only [c, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    calc
      ‖x + c‖ ≤ ‖x‖ + ‖c‖ := norm_add_le _ _
      _ < R := by rw [hnorm]; linarith
  have ht := hT.translate (graphProjectionN 2 c) (V := ball 0 r)
    (fun x hx => by rw [hc]; exact hmap x hx)
  rw [hc] at ht
  have huT := hu.translate (isOpen_boundaryHalfBall R) (isOpen_boundaryHalfBall r) c
    (fun _ hx => boundaryHalfBall_add_tangential hi hh hx)
  have huR := hu.mono (boundaryHalfBall_mono hrR)
  have hs := HasZeroFlatTraceOn.sub measurableSet_ball huT huR ht
    (hT.mono (ball_subset_ball hrR))
  exact hs.boundary_nondiv_const_mul h⁻¹

end LiquidDrop
