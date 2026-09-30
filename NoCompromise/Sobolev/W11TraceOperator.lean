module

public import NoCompromise.Sobolev.W11TraceBoundary
public import NoCompromise.Sobolev.W11Density
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-!
# The constructed W¹,¹ trace on bounded Lipschitz domains

Actual boundary restriction on continuous weak-gradient pairs is bounded by the
W¹,¹ norm and has a dense domain. Its extension into the complete boundary L¹ space
is the trace operator. Smooth approximation realizes every trace as an L¹ limit.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Actual boundary restriction on continuous weak-gradient pairs is linear. -/
def continuousW11Data_restriction {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hMem : ∀ p : continuousW11Data D, MemLp p.val.1 1 μ) :
    continuousW11Data D →ₗ[ℝ] Lp ℝ 1 μ where
  toFun p := (hMem p).toLp p.val.1
  map_add' p q := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hMem (p + q)), MemLp.coeFn_toLp (hMem p),
      MemLp.coeFn_toLp (hMem q), Lp.coeFn_add ((hMem p).toLp p.val.1)
        ((hMem q).toLp q.val.1)] with x w11 h2 h3 h4
    simp only [Pi.add_apply, h2, h3] at h4
    exact w11.trans ((show (p + q).val.1 x = p.val.1 x + q.val.1 x from rfl).trans h4.symm)
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hMem (c • p)), MemLp.coeFn_toLp (hMem p),
      Lp.coeFn_smul c ((hMem p).toLp p.val.1)] with x w11 h2 h3
    simp only [Pi.smul_apply, smul_eq_mul, h2] at h3
    exact w11.trans ((show (c • p).val.1 x = c * p.val.1 x from rfl).trans h3.symm)

lemma norm_continuousW11Data_restriction {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    (hMem : ∀ p : continuousW11Data D, MemLp p.val.1 1 μ) (p : continuousW11Data D) :
    ‖continuousW11Data_restriction μ hMem p‖ = lpNorm p.val.1 1 μ := by
  change ‖(hMem p).toLp p.val.1‖ = _
  rw [Lp.norm_toLp, toReal_eLpNorm]

/-- A bounded linear trace on every bounded open Lipschitz domain, agreeing with
actual boundary restriction for all continuous W¹,¹ representatives. -/
theorem exists_w11_trace_operator {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : W11Space D →L[ℝ]
      Lp ℝ 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧
      ∀ f G (hf : HasW11GradientOn f G D), Continuous f →
        ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[
          (Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f := by
  obtain ⟨C, hC, hbound⟩ := exists_w11_boundary_restriction_bound hD hbD hL
  let μ := (Measure.euclideanHausdorffMeasure k).restrict (frontier D)
  let hMem (p : continuousW11Data D) : MemLp p.val.1 1 μ :=
    (hbound p.val.1 p.val.2 p.property.2 p.property.1).1
  let R := continuousW11Data_restriction μ hMem
  let e := continuousW11Data_toW11Space hD
  have hd : DenseRange e := denseRange_continuousW11Data_toW11Space hD hbD hL
  have hnorm (p : continuousW11Data D) : ‖R p‖ ≤ (2 * C) * ‖e p‖ := by
    rw [norm_continuousW11Data_restriction]
    calc
      _ ≤ C * (lpNorm p.val.1 1 (volume.restrict D) +
          lpNorm p.val.2 1 (volume.restrict D)) :=
        (hbound p.val.1 p.val.2 p.property.2 p.property.1).2
      _ ≤ C * (2 * ‖e p‖) :=
        mul_le_mul_of_nonneg_left (continuousW11Data_sum_lpNorm_le hD p) hC
      _ = _ := by ring
  let T := R.extendOfNorm e
  refine ⟨T, 2 * C, by positivity, LinearMap.opNorm_extendOfNorm_le hd (by positivity) hnorm,
    fun f G hf hc => ?_⟩
  let p : continuousW11Data D := ⟨(f, G), hc, hf⟩
  have heq : T (e p) = R p := LinearMap.extendOfNorm_eq hd ⟨2 * C, hnorm⟩ p
  change ⇑(T (e p)) =ᵐ[μ] f
  rw [heq]
  exact MemLp.coeFn_toLp (hMem p)

/-- The bounded trace is unique once its values on continuous representatives are fixed. -/
theorem w11_trace_operator_unique {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D)
    (T S : W11Space D →L[ℝ]
      Lp ℝ 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)))
    (hT : ∀ f G (hf : HasW11GradientOn f G D), Continuous f →
      ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D),
        T (W11Space.ofFunction f G hf) x = f x)
    (hS : ∀ f G (hf : HasW11GradientOn f G D), Continuous f →
      ∀ᵐ x ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D),
        S (W11Space.ofFunction f G hf) x = f x) : T = S := by
  have heq : (T : W11Space D → _) ∘ continuousW11Data_toW11Space hD =
      (S : W11Space D → _) ∘ continuousW11Data_toW11Space hD := by
    funext p
    apply Lp.ext
    filter_upwards [hT p.val.1 p.val.2 p.property.2 p.property.1,
      hS p.val.1 p.val.2 p.property.2 p.property.1] with x hx hy
    exact hx.trans hy.symm
  exact DFunLike.coe_injective ((denseRange_continuousW11Data_toW11Space hD hbD hL).equalizer
    T.continuous S.continuous heq)

/-- Scalar W¹,¹ trace theorem: a bounded trace on genuine W¹,¹,
with normalized Hausdorff boundary measure and realization by actual smooth L¹ limits. -/
theorem exists_w11_trace {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : W11Space D →L[ℝ]
      Lp ℝ 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧
      (∀ u : W11Space D, ‖T u‖ ≤ C *
        (lpNorm u 1 (volume.restrict D) + lpNorm u.gradientLp 1 (volume.restrict D))) ∧
      (∀ f G (hf : HasW11GradientOn f G D), Continuous f →
        ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[
          (Measure.euclideanHausdorffMeasure k).restrict (frontier D)] f) ∧
      ∀ u : W11Space D, ∃ v : ℕ → EuclideanSpace ℝ (Fin (k + 1)) → ℝ,
        ∃ hv : ∀ j, HasW11GradientOn (v j) (gradient (v j)) D,
        ∃ hb : ∀ j, MemLp (v j) 1
          ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)),
          (∀ j, ContDiff ℝ (⊤ : ℕ∞) (v j)) ∧
          Tendsto (fun j => W11Space.ofFunction (v j) (gradient (v j)) (hv j)) atTop (𝓝 u) ∧
          Tendsto (fun j => (hb j).toLp (v j)) atTop (𝓝 (T u)) := by
  obtain ⟨T, C, hC, hTC, hT⟩ := exists_w11_trace_operator hD hbD hL
  refine ⟨T, C, hC, hTC, fun u => ?_, hT, fun u => ?_⟩
  · calc
      _ ≤ ‖T‖ * ‖u‖ := T.le_opNorm u
      _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right hTC (norm_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [W11Space.norm_toLp_eq_lpNorm, W11Space.norm_gradientLp_eq_lpNorm] using
          u.norm_le_sum) hC
  · obtain ⟨v, hv, hc, hconv⟩ := W11Space.exists_smooth_approx_on_domain hD hbD hL u
    let hb (j : ℕ) : MemLp (v j) 1
        ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) :=
      (Lp.memLp (T (W11Space.ofFunction (v j) (gradient (v j)) (hv j)))).ae_eq
        (hT (v j) (gradient (v j)) (hv j) (hc j).continuous)
    refine ⟨v, hv, hb, hc, hconv, ?_⟩
    have heq (j : ℕ) : T (W11Space.ofFunction (v j) (gradient (v j)) (hv j)) =
        (hb j).toLp (v j) := by
      apply Lp.ext
      exact (hT (v j) (gradient (v j)) (hv j) (hc j).continuous).trans
        (MemLp.coeFn_toLp (hb j)).symm
    have h := (T.continuous.tendsto u).comp hconv
    simpa only [Function.comp_def, heq] using h

end LiquidDrop
