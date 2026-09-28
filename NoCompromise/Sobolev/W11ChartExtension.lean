import NoCompromise.Sobolev.W11Bounds
import NoCompromise.Sobolev.H1ChartExtension

/-!
# W¹,¹ extension pieces in Lipschitz charts

Pullback, reflection, inverse pullback and a compact cutoff give the actual
linear extension piece with an input-independent bound.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Pointwise
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A compact local chart extension is globally W¹,¹, with a fixed bound depending
only on the chart and cutoff. The construction is the existing raw linear map. -/
theorem w11_local_chart_extension {n : ℕ} (i : Fin n) (R : ℝ)
    (e : EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)) {C K : ℝ≥0}
    (he : LipschitzWith C e) (heinverse : LipschitzWith K e.symm)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (hchart : e '' coordinateHalfCube i R = D ∩ e '' coordinateCube n R)
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G D)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ e '' coordinateCube n R)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbζ : ∀ x, ‖ζ x‖ ≤ A) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasW11GradientOn (cutoffChartReflectionLinearMap i e ζ f) H univ ∧
      EqOn (cutoffChartReflectionLinearMap i e ζ f) (fun x => ζ x * f x) D ∧
      tsupport (cutoffChartReflectionLinearMap i e ζ f) ⊆ tsupport ζ ∧
      lpNorm (cutoffChartReflectionLinearMap i e ζ f) 1 volume + lpNorm H 1 volume ≤
        ((A + B) * (2 * (max 1 (C : ℝ) * (K : ℝ) ^ n) *
          (max 1 (K : ℝ) * (C : ℝ) ^ n))) *
            (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D)) := by
  obtain ⟨r, hrR, hsr⟩ := exists_smaller_chart_cube_of_compact_support i e hcζ hsζ
  have hpull := hf.comp_homeomorph_on_lpNorm (isOpen_coordinateHalfCube i R) hD e he
    heinverse (fun x hx => by
      have : e x ∈ e '' coordinateHalfCube i R := mem_image_of_mem e hx
      rw [hchart] at this
      exact this.1)
  obtain ⟨Hflat, hflat, hbflat⟩ := hpull.1.coordinateFold_halfCube_lpNorm i hrR
  have hpush := hflat.comp_homeomorph_on_lpNorm
    (e.isOpenMap _ (isOpen_coordinateCube n r)) (isOpen_coordinateCube n r)
    e.symm heinverse he (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := hx
      simpa only [e.symm_apply_apply] using hy)
  have hcut := hpush.1.mul_compact_cutoff_lpNorm
    (e.isOpenMap _ (isOpen_coordinateCube n r)).measurableSet hζ hcζ hsr hA hB hbζ hbgrad
  refine ⟨_, hcut.1, cutoffChartReflection_eq_on_domain i R e hchart hsζ f,
    tsupport_mul_subset_left, ?_⟩
  apply hcut.2.trans
  calc
    _ ≤ (A + B) * ((max 1 (K : ℝ) * (C : ℝ) ^ n) *
        (2 * ((max 1 (C : ℝ) * (K : ℝ) ^ n) *
          (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D))))) := by
      apply mul_le_mul_of_nonneg_left _ (add_nonneg hA hB)
      apply hpush.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact hbflat.trans (mul_le_mul_of_nonneg_left hpull.2 (by norm_num))
    _ = _ := by ring

/-- A finite, input-independent W¹,¹ bound for one interior or boundary partition piece. -/
noncomputable def w11BoundaryExtensionPieceBound {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D}) (B : ℝ) : ℝ :=
  match i with
  | none => 1 + B
  | some c => (1 + B) * (2 *
      (max 1 ((1 + c.val.lip : ℝ≥0) : ℝ) *
        ((1 + c.val.lip : ℝ≥0) : ℝ) ^ n) *
      (max 1 ((1 + c.val.lip : ℝ≥0) : ℝ) *
        ((1 + c.val.lip : ℝ≥0) : ℝ) ^ n))

lemma w11BoundaryExtensionPieceBound_nonneg {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))}
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D}) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ w11BoundaryExtensionPieceBound i B := by
  cases i <;> simp only [w11BoundaryExtensionPieceBound] <;> positivity

/-- Each fixed smooth partition piece gives a compact global W¹,¹ extension of its
cutoff times the original function, with a bound uniform over all W¹,¹ inputs. -/
theorem w11_boundaryExtensionPiece {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D)
    (i : Option {c : LipschitzGraphChart n // c.IsChartFor D})
    {f ζ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hf : HasW11GradientOn f G D)
    (hζ : ContDiff ℝ 1 ζ) (hcζ : HasCompactSupport ζ)
    (hsζ : tsupport ζ ⊆ boundaryExtensionRegion D i)
    (hbζ : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hbgrad : ∀ x, ‖gradient ζ x‖ ≤ B) :
    ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasW11GradientOn (boundaryExtensionPiece D i ζ f) H univ ∧
      EqOn (boundaryExtensionPiece D i ζ f) (fun x => ζ x * f x) D ∧
      tsupport (boundaryExtensionPiece D i ζ f) ⊆ tsupport ζ ∧
      lpNorm (boundaryExtensionPiece D i ζ f) 1 volume + lpNorm H 1 volume ≤
        w11BoundaryExtensionPieceBound i B *
          (lpNorm f 1 (volume.restrict D) + lpNorm G 1 (volume.restrict D)) := by
  have hnorm : ∀ x, ‖ζ x‖ ≤ (1 : ℝ) := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hbζ x).1]
    exact (hbζ x).2
  cases i with
  | none =>
    have hb := hf.mul_compact_cutoff_lpNorm hD.measurableSet hζ hcζ hsζ
      (by norm_num : (0 : ℝ) ≤ 1) hB hnorm hbgrad
    exact ⟨_, hb.1, fun _ _ => rfl, tsupport_mul_subset_left, hb.2⟩
  | some c =>
    exact w11_local_chart_extension c.val.normal c.val.radius c.val.homeomorph
      c.val.lipschitz c.val.lipschitz_symm hD c.property hf hζ hcζ hsζ
      (by norm_num) hB hnorm hbgrad

end LiquidDrop
