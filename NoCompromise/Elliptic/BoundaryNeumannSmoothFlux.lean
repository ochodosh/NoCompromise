module

public import NoCompromise.Elliptic.BoundaryNeumannC2

@[expose] public section

/-!
# Tangential differentiation of the weak conormal flux

The flux is C¹ on an open neighborhood of the closed larger half ball.
Tangential translation preserves the flat face. Dominated convergence therefore
passes the existing flux quotient identity to the classical derivative, while
retaining the original C¹ class of ambient test functions.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Vector- and operator-valued coordinate quotients converge to the actual
Fréchet derivative. The step may approach zero from either side. -/
lemma boundary_neumann_smooth_quotient_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : EuclideanSpace ℝ (Fin 3) → E} {x : EuclideanSpace ℝ (Fin 3)}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    Tendsto (fun s : ℝ => coordinateDifferenceQuotient i s f x) (𝓝[≠] 0)
      (𝓝 (fderiv ℝ f x (EuclideanSpace.single i 1))) := by
  have hp : HasDerivAt (fun t : ℝ => x + t • EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i 1) 0 := by
    simpa only [one_smul, id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (EuclideanSpace.single i (1 : ℝ))).const_add x
  have hfd : HasFDerivAt f (fderiv ℝ f x)
      (x + (0 : ℝ) • EuclideanSpace.single i 1) := by simpa using hf.hasFDerivAt
  simpa only [Function.comp_def, slope_def_module, sub_zero, zero_smul, add_zero, zero_add,
    coordinateDifferenceQuotient] using (hfd.comp_hasDerivAt 0 hp).tendsto_slope_zero

/-- Differentiation of a C¹ conormal flux in a tangential direction. No
ellipticity or additional smoothness of the test function is required. -/
theorem boundary_neumann_smooth_flux_derivative {R r : ℝ} (hrR : r < R)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    (hRU : closure (boundaryHalfBall R) ⊆ U)
    {V : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hV : ContDiffOn ℝ 1 V U)
    (he : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ →
      HasCompactSupport φ → tsupport φ ⊆ ball 0 R →
      (∫ x in boundaryHalfBall R, inner ℝ (V x) (gradient φ x)) = 0)
    {i : Fin 3} (hi : i ≠ Fin.last 2) :
    ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 r →
      (∫ x in boundaryHalfBall r,
        inner ℝ (fderiv ℝ V x (EuclideanSpace.single i 1)) (gradient φ x)) = 0 := by
  intro φ hφ hcφ hsφ
  have hK : IsCompact (closure (boundaryHalfBall R)) :=
    (isBounded_ball.subset (inter_subset_left : boundaryHalfBall R ⊆ ball 0 R)).isCompact_closure
  have hDV : ContinuousOn (fderiv ℝ V) U :=
    (hV.fderiv_of_isOpen hU (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hDV.mono hRU)
  have hsub : closure (boundaryHalfBall r) ⊆ closure (boundaryHalfBall R) :=
    closure_mono (boundaryHalfBall_mono hrR.le)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[≠] 0, |s| ≤ R - r := by
    have ht : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ∈ ball 0 (R - r) :=
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (sub_pos.mpr hrR))
    exact ht.mono fun s hs => (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs]
      using hs : |s| < R - r).le
  have hmap {s : ℝ} (hs : |s| ≤ R - r) :
      MapsTo (fun x => x + s • EuclideanSpace.single i (1 : ℝ))
        (closure (boundaryHalfBall r)) (closure (boundaryHalfBall R)) :=
    (show MapsTo (fun x => x + s • EuclideanSpace.single i (1 : ℝ))
      (boundaryHalfBall r) (boundaryHalfBall R) from
      fun _ hx => boundaryHalfBall_add_tangential hi hs hx).closure
        (continuous_id.add continuous_const)
  have hbound {s : ℝ} (hs : |s| ≤ R - r) (hs0 : s ≠ 0)
      {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ boundaryHalfBall r) :
      ‖coordinateDifferenceQuotient i s V x‖ ≤ B := by
    have hb := (convex_boundaryHalfBall R).closure.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hV.contDiffAt (hU.mem_nhds (hRU hy))).differentiableAt one_ne_zero)
      hB (hsub (subset_closure hx)) (hmap hs (subset_closure hx))
    rw [coordinateDifferenceQuotient, norm_smul]
    apply (mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans_eq
    simp only [add_sub_cancel_left, norm_smul, PiLp.norm_single, norm_one, mul_one, norm_inv]
    rw [mul_left_comm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hs0), mul_one]
  let μ := volume.restrict (boundaryHalfBall r)
  let : IsFiniteMeasure μ :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (isBounded_ball.subset
          (inter_subset_left : boundaryHalfBall r ⊆ ball 0 r)).measure_lt_top⟩
  have hmeas := (isOpen_boundaryHalfBall r).measurableSet
  have hlimit : Tendsto
      (fun s : ℝ => ∫ x in boundaryHalfBall r,
        inner ℝ (coordinateDifferenceQuotient i s V x) (gradient φ x))
      (𝓝[≠] 0)
      (𝓝 (∫ x in boundaryHalfBall r,
        inner ℝ (fderiv ℝ V x (EuclideanSpace.single i 1)) (gradient φ x))) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun x => B * ‖gradient φ x‖)
    · filter_upwards [hsmall] with s hs
      have hc : ContinuousOn (coordinateDifferenceQuotient i s V)
          (closure (boundaryHalfBall r)) :=
        (((hV.continuousOn.mono hRU).comp
          (continuous_id.add continuous_const).continuousOn (hmap hs)).sub
            (hV.continuousOn.mono (hsub.trans hRU))).const_smul s⁻¹
      exact ((hc.mono subset_closure).inner (𝕜 := ℝ)
        (continuous_gradient_of_contDiff hφ).continuousOn).aestronglyMeasurable hmeas
    · filter_upwards [hsmall, self_mem_nhdsWithin] with s hs hs0
      filter_upwards [ae_restrict_mem hmeas] with x hx
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hbound hs hs0 hx) (norm_nonneg _))
    · have hc : IsCompact (closure (boundaryHalfBall r)) :=
        (isBounded_ball.subset
          (inter_subset_left : boundaryHalfBall r ⊆ ball 0 r)).isCompact_closure
      have hg : ContinuousOn (fun x => B * ‖gradient φ x‖)
          (closure (boundaryHalfBall r)) :=
        ((continuous_gradient_of_contDiff hφ).norm.const_mul B).continuousOn
      exact (hg.integrableOn_compact hc).mono_set subset_closure
    · filter_upwards [ae_restrict_mem hmeas] with x hx
      exact (boundary_neumann_smooth_quotient_tendsto
        ((hV.contDiffAt (hU.mem_nhds (hRU (hsub (subset_closure hx))))).differentiableAt
          one_ne_zero) i).inner tendsto_const_nhds
  have hzero : ∀ᶠ s : ℝ in 𝓝[≠] 0,
      (∫ x in boundaryHalfBall r,
        inner ℝ (coordinateDifferenceQuotient i s V x) (gradient φ x)) = 0 := by
    filter_upwards [hsmall] with s hs
    exact boundary_neumann_flux_quotient hi hs (hV.continuousOn.mono hRU) he φ hφ hcφ hsφ
  exact tendsto_nhds_unique (hlimit.congr' hzero) tendsto_const_nhds

end LiquidDrop
