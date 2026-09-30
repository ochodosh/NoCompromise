module

public import NoCompromise.Elliptic.ClassicalGaussGreen
public import NoCompromise.Sobolev.W11Pairing
public import NoCompromise.Sobolev.W11TraceVector

@[expose] public section

/-!
# Passage from classical graph calculus to W¹,¹ Gauss–Green

Both sides of the directional identity are continuous functionals on genuine
W¹,¹. Smooth density therefore passes the classical identity to every class.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem w11_directional_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {ν : AmbientSpace → AmbientSpace}
    (hνm : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier D)))
    (hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D), ‖ν x‖ ≤ 1)
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor D →
      ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
        x ∈ c.region → ν x = c.outwardNormal x)
    (T : W11Space D →L[ℝ] Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)))
    (hT : ∀ f G (hf : HasW11GradientOn f G D), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[
        (hausdorffMeasure2 3).restrict (frontier D)] f)
    (u : W11Space D) (v : AmbientSpace) :
    (∫ x in D, inner ℝ (u.gradientLp x) v) =
      ∫ x, T u x * inner ℝ v (ν x) ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  let L : W11Space D →L[ℝ] ℝ :=
    (lpOneInnerPairing (V := fun _ : AmbientSpace => v) aestronglyMeasurable_const
      (Eventually.of_forall fun _ => le_refl ‖v‖)).comp W11Space.gradientCLM
  have hnv : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
      ‖inner ℝ v (ν x)‖ ≤ ‖v‖ := by
    filter_upwards [hn] with x hx
    exact (norm_inner_le_norm _ _).trans (by nlinarith [norm_nonneg v])
  let R : W11Space D →L[ℝ] ℝ := (lpOneInnerPairing (hνm.const_inner (c := v)) hnv).comp T
  have hL (w : W11Space D) : L w = ∫ x in D, inner ℝ (w.gradientLp x) v := rfl
  have hR (w : W11Space D) : R w =
      ∫ x, T w x * inner ℝ v (ν x) ∂(hausdorffMeasure2 3).restrict (frontier D) := by
    simp only [R, ContinuousLinearMap.comp_apply, lpOneInnerPairing_apply,
      RCLike.inner_apply, conj_trivial, mul_comm]
  obtain ⟨φ, hφ, hcφ, hconv⟩ := W11Space.exists_smooth_approx_on_domain
    hD hbD hC1.hasLipschitzBoundary u
  let a (j : ℕ) := W11Space.ofFunction (φ j) (gradient (φ j)) (hφ j)
  have heq (j : ℕ) : L (a j) = R (a j) := by
    rw [hL, hR]
    calc
      _ = ∫ x in D, fderiv ℝ (φ j) x v := by
        apply integral_congr_ae
        filter_upwards [W11Space.gradientLp_ofFunction (φ j) (gradient (φ j)) (hφ j)]
          with x hx
        rw [hx, inner_gradient_left]
      _ = ∫ x, φ j x * inner ℝ v (ν x)
          ∂(hausdorffMeasure2 3).restrict (frontier D) :=
        classical_directional_gauss_green hD hbD hC1 hνm hn hν
          ((hcφ j).of_le (by simp)) v
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hT (φ j) (gradient (φ j)) (hφ j) (hcφ j).continuous] with x hx
        rw [hx]
  have htL : Tendsto (fun j => L (a j)) atTop (𝓝 (L u)) :=
    (L.continuous.tendsto u).comp hconv
  have htR : Tendsto (fun j => L (a j)) atTop (𝓝 (R u)) := by
    simpa only [heq, a, Function.comp_def] using (R.continuous.tendsto u).comp hconv
  simpa only [hL, hR] using tendsto_nhds_unique htL htR

/-- The divergence of the actual weak derivative matrix, in the Euclidean basis. -/
def w11Divergence {n : ℕ}
    (J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, J x (EuclideanSpace.single i 1) i

theorem w11_vector_gauss_green {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (hC1 : HasC1Boundary D)
    {ν : AmbientSpace → AmbientSpace}
    (hνm : AEStronglyMeasurable ν ((hausdorffMeasure2 3).restrict (frontier D)))
    (hn : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D), ‖ν x‖ ≤ 1)
    (hν : ∀ c : C1BoundaryChart, c.IsChartFor D →
      ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D),
        x ∈ c.region → ν x = c.outwardNormal x)
    (T : W11Space D →L[ℝ] Lp ℝ 1 ((hausdorffMeasure2 3).restrict (frontier D)))
    (hT : ∀ f G (hf : HasW11GradientOn f G D), Continuous f →
      ⇑(T (W11Space.ofFunction f G hf)) =ᵐ[
        (hausdorffMeasure2 3).restrict (frontier D)] f)
    {Z : AmbientSpace → AmbientSpace} {J : AmbientSpace → AmbientSpace →L[ℝ] AmbientSpace}
    (hZ : HasW11VectorGradientOn Z J D) :
    (∫ x in D, w11Divergence J x) =
      ∫ x, inner ℝ (w11VectorTrace T hZ x) (ν x)
        ∂(hausdorffMeasure2 3).restrict (frontier D) := by
  classical
  let e (i : Fin 3) : AmbientSpace := EuclideanSpace.single i 1
  let u (i : Fin 3) := W11Space.ofFunction _ _ (hZ.component i)
  have hj (i : Fin 3) : IntegrableOn (fun x => J x (e i) i) D := by
    have h := ((hZ.component i).integrable_gradient.inner_const (𝕜 := ℝ) (e i))
    simpa only [IntegrableOn, e, ContinuousLinearMap.adjoint_inner_left,
      EuclideanSpace.inner_single_left, map_one, one_mul] using h
  have ht (i : Fin 3) : Integrable (fun x => T (u i) x * ν x i)
      ((hausdorffMeasure2 3).restrict (frontier D)) := by
    have hi := memLp_one_iff_integrable.mp (Lp.memLp (T (u i)))
    have hb : ∀ᵐ x ∂(hausdorffMeasure2 3).restrict (frontier D), ‖ν x i‖ ≤ 1 :=
      hn.mono fun x hx => (PiLp.norm_apply_le (ν x) i).trans hx
    have hm : AEStronglyMeasurable (fun x => ν x i)
        ((hausdorffMeasure2 3).restrict (frontier D)) := by
      exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable hνm
    simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using
      integrable_inner_of_ae_bound hi hm hb
  have heq (i : Fin 3) : (∫ x in D, J x (e i) i) =
      ∫ x, T (u i) x * ν x i ∂(hausdorffMeasure2 3).restrict (frontier D) := by
    have h := w11_directional_gauss_green hD hbD hC1 hνm hn hν T hT (u i) (e i)
    have he : (∫ x in D, inner ℝ ((u i).gradientLp x) (e i)) =
        ∫ x in D, J x (e i) i := by
      apply integral_congr_ae
      filter_upwards [W11Space.gradientLp_ofFunction _ _ (hZ.component i)] with x hx
      rw [hx, ContinuousLinearMap.adjoint_inner_left]
      simp only [e, EuclideanSpace.inner_single_left, map_one, one_mul]
    simpa only [he, e, EuclideanSpace.inner_single_left, map_one, one_mul] using h
  calc
    _ = ∑ i : Fin 3, ∫ x in D, J x (e i) i :=
      integral_finsetSum _ fun i _ => hj i
    _ = ∑ i : Fin 3, ∫ x, T (u i) x * ν x i
        ∂(hausdorffMeasure2 3).restrict (frontier D) := Finset.sum_congr rfl fun i _ => heq i
    _ = ∫ x, ∑ i : Fin 3, T (u i) x * ν x i
        ∂(hausdorffMeasure2 3).restrict (frontier D) :=
      (integral_finsetSum _ fun i _ => ht i).symm
    _ = _ := by
      congr 1
      funext x
      simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
        w11VectorTrace, u, mul_comm]

end LiquidDrop
