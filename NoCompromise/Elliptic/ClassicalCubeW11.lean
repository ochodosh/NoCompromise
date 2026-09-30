module

public import NoCompromise.Elliptic.ClassicalCubeCalculus
public import NoCompromise.Elliptic.ClassicalGaussGreenW11

@[expose] public section

/-!
# Genuine W¹,¹ Gauss–Green on coordinate cubes

The trace is the bounded extension of classical boundary restriction. Both
sides of the smooth cube identity are continuous W¹,¹ functionals, so the
proved smooth approximation on Lipschitz cubes yields the full formula.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem w11_directional_gauss_green_cube {R : ℝ} (hR : 0 < R)
    (T : W11Space (coordinateCube 3 R) →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))))
    (hT : ∀ f G (hf : HasW11GradientOn f G (coordinateCube 3 R)), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf))
        =ᵐ[(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))] f)
    (u : W11Space (coordinateCube 3 R)) (v : AmbientSpace) :
    (∫ x in coordinateCube 3 R, inner ℝ (u.gradientLp x) v) =
      ∫ x, T u x * inner ℝ v (cubeOutwardNormal R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
  have hνm := (measurable_cubeOutwardNormal R).aestronglyMeasurable
    (μ := (hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)))
  have hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)),
      ‖cubeOutwardNormal R x‖ ≤ 1 :=
    Eventually.of_forall (norm_cubeOutwardNormal_le_one hR)
  let L : W11Space (coordinateCube 3 R) →L[ℝ] ℝ :=
    (lpOneInnerPairing (V := fun _ : AmbientSpace => v) aestronglyMeasurable_const
      (Eventually.of_forall fun _ => le_refl ‖v‖)).comp W11Space.gradientCLM
  have hnv : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)),
      ‖inner ℝ v (cubeOutwardNormal R x)‖ ≤ ‖v‖ := by
    filter_upwards [hn] with x hx
    exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg v])
  let B : W11Space (coordinateCube 3 R) →L[ℝ] ℝ :=
    (lpOneInnerPairing (hνm.const_inner (c := v)) hnv).comp T
  have hL (w : W11Space (coordinateCube 3 R)) :
      L w = ∫ x in coordinateCube 3 R, inner ℝ (w.gradientLp x) v := rfl
  have hB (w : W11Space (coordinateCube 3 R)) : B w =
      ∫ x, T w x * inner ℝ v (cubeOutwardNormal R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
    simp only [B, ContinuousLinearMap.comp_apply, lpOneInnerPairing_apply,
      RCLike.inner_apply, conj_trivial, mul_comm]
  obtain ⟨φ, hφ, hcφ, hconv⟩ := W11Space.exists_smooth_approx_on_domain
    (isOpen_coordinateCube 3 R) (isBounded_coordinateCube 3 R)
    (hasLipschitzBoundary_coordinateCube 3 hR) u
  let a (j : ℕ) := W11Space.ofFunction (φ j) (gradient (φ j)) (hφ j)
  have heq (j : ℕ) : L (a j) = B (a j) := by
    rw [hL, hB]
    calc
      _ = ∫ x in coordinateCube 3 R, fderiv ℝ (φ j) x v := by
        apply integral_congr_ae
        filter_upwards [W11Space.gradientLp_ofFunction (φ j) (gradient (φ j)) (hφ j)]
          with x hx
        rw [hx, inner_gradient_left]
      _ = ∫ x, φ j x * inner ℝ v (cubeOutwardNormal R x)
          ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) :=
        classical_directional_gauss_green_cube hR
          ((hcφ j).of_le (by simp)) v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hT (φ j) (gradient (φ j)) (hφ j) (hcφ j).continuous] with x hx
        rw [hx]
  have htL : Tendsto (fun j => L (a j)) atTop (𝓝 (L u)) :=
    (L.continuous.tendsto u).comp hconv
  have htR : Tendsto (fun j => L (a j)) atTop (𝓝 (B u)) := by
    simpa only [heq, a, Function.comp_def] using (B.continuous.tendsto u).comp hconv
  simpa only [hL, hB] using tendsto_nhds_unique htL htR

theorem w11_gauss_green_cube {R : ℝ} (hR : 0 < R)
    (T : W11Space (coordinateCube 3 R) →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))))
    (hT : ∀ f G (hf : HasW11GradientOn f G (coordinateCube 3 R)), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf))
        =ᵐ[(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))] f)
    {Z : AmbientSpace → AmbientSpace} {J : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace}
    (hZ : HasW11VectorGradientOn Z J (coordinateCube 3 R)) :
    (∫ x in coordinateCube 3 R, w11Divergence J x) =
      ∫ x, inner ℝ (w11VectorTrace T hZ x) (cubeOutwardNormal R x)
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
  have hνm := (measurable_cubeOutwardNormal R).aestronglyMeasurable
    (μ := (hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)))
  have hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)),
      ‖cubeOutwardNormal R x‖ ≤ 1 :=
    Eventually.of_forall (norm_cubeOutwardNormal_le_one hR)
  classical
  let e (i : Fin 3) : AmbientSpace := EuclideanSpace.single i 1
  let u (i : Fin 3) := W11Space.ofFunction _ _ (hZ.component i)
  have hj (i : Fin 3) : IntegrableOn (fun x => J x (e i) i) (coordinateCube 3 R) := by
    have h := ((hZ.component i).integrable_gradient.inner_const (𝕜 := ℝ) (e i))
    simpa only [IntegrableOn, e, ContinuousLinearMap.adjoint_inner_left,
      EuclideanSpace.inner_single_left, map_one, one_mul] using h
  have ht (i : Fin 3) : Integrable (fun x => T (u i) x * cubeOutwardNormal R x i)
      ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))) := by
    have hi := memLp_one_iff_integrable.mp (Lp.memLp (T (u i)))
    have hb : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)),
        ‖cubeOutwardNormal R x i‖ ≤ 1 :=
      hn.mono fun x hx => (PiLp.norm_apply_le (cubeOutwardNormal R x) i).trans hx
    have hm : AEStronglyMeasurable (fun x => cubeOutwardNormal R x i)
        ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))) := by
      exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hνm
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      integrable_inner_of_ae_bound hi hm hb
  have heq (i : Fin 3) : (∫ x in coordinateCube 3 R, J x (e i) i) =
      ∫ x, T (u i) x * cubeOutwardNormal R x i
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
    have h := w11_directional_gauss_green_cube hR T hT (u i) (e i)
    have he : (∫ x in coordinateCube 3 R, inner ℝ ((u i).gradientLp x) (e i)) =
        ∫ x in coordinateCube 3 R, J x (e i) i := by
      apply integral_congr_ae
      filter_upwards [W11Space.gradientLp_ofFunction _ _ (hZ.component i)] with x hx
      rw [hx, ContinuousLinearMap.adjoint_inner_left]
      simp only [e, EuclideanSpace.inner_single_left, map_one, one_mul]
    simpa only [he, e, EuclideanSpace.inner_single_left, map_one, one_mul] using h
  calc
    _ = ∑ i : Fin 3, ∫ x in coordinateCube 3 R, J x (e i) i :=
      integral_finsetSum _ fun i _ => hj i
    _ = ∑ i : Fin 3, ∫ x, T (u i) x * cubeOutwardNormal R x i
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) :=
      Finset.sum_congr rfl fun i _ => heq i
    _ = ∫ x, ∑ i : Fin 3, T (u i) x * cubeOutwardNormal R x i
        ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) :=
      (integral_finsetSum _ fun i _ => ht i).symm
    _ = _ := by
      congr 1
      funext x
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
        w11VectorTrace, u, mul_comm]

/-- The trace operator is constructed once, before the vector field is specified. -/
theorem exists_w11_gauss_green_cube {R : ℝ} (hR : 0 < R) :
    ∃ T : W11Space (coordinateCube 3 R) →L[ℝ]
      Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))),
    ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧
      (∀ f G (hf : HasW11GradientOn f G (coordinateCube 3 R)), Continuous f →
        ⇑(T (W11Space.ofFunction f G hf))
          =ᵐ[(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R))] f) ∧
      ∀ Z J (hZ : HasW11VectorGradientOn Z J (coordinateCube 3 R)),
        (∫ x in coordinateCube 3 R, w11Divergence J x) =
          ∫ x, inner ℝ (w11VectorTrace T hZ x) (cubeOutwardNormal R x)
            ∂(hausdorffMeasure2 3).restrict (frontier (coordinateCube 3 R)) := by
  obtain ⟨T, C, hC, hTC, hT⟩ := exists_w11_trace_operator
    (isOpen_coordinateCube 3 R) (isBounded_coordinateCube 3 R)
    (hasLipschitzBoundary_coordinateCube 3 hR)
  exact ⟨T, C, hC, hTC, hT, fun _ _ hZ => w11_gauss_green_cube hR T hT hZ⟩

end LiquidDrop
