import NoCompromise.Stationary.EulerLagrange

/-!
# The scaling identity

Blueprint `prop:scaling-identity`. Testing the weak Euler--Lagrange equation with a
smooth compactly supported field equal to the identity near the closure of the
minimizer identifies the multiplier: its normal flux is `3V`, so the multiplier is
unique and equals `(2P + 5D) / (3V)`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- A smooth compactly supported field equal to the identity on an open
neighbourhood of the closure of a bounded set. -/
lemma exists_identity_field {Ω : Set AmbientSpace} (hb : Bornology.IsBounded Ω) :
    ∃ Y : AmbientSpace → AmbientSpace, ContDiff ℝ (⊤ : ℕ∞) Y ∧ HasCompactSupport Y ∧
      ∃ U : Set AmbientSpace, IsOpen U ∧ closure Ω ⊆ U ∧ ∀ x ∈ U, Y x = x := by
  obtain ⟨R, hR⟩ := hb.closure.subset_ball (0 : AmbientSpace)
  let f : ContDiffBump (0 : AmbientSpace) :=
    ⟨max R 1, max R 1 + 1, lt_max_of_lt_right one_pos, by linarith⟩
  refine ⟨fun x => f x • x, f.contDiff.smul contDiff_id,
    f.hasCompactSupport.smul_right (f' := id), ball 0 (max R 1), isOpen_ball,
    hR.trans (ball_subset_ball (le_max_left _ _)), fun x hx => ?_⟩
  change f x • x = x
  rw [f.one_of_mem_closedBall (ball_subset_closedBall hx), one_smul]

/-- The divergence of a field equal to the identity near a point is three. -/
lemma divergenceN_eq_three_of_eventuallyEq_id {Y : AmbientSpace → AmbientSpace}
    {x : AmbientSpace} (h : Y =ᶠ[𝓝 x] id) : divergenceN Y x = 3 := by
  simp only [divergenceN, h.fderiv_eq (𝕜 := ℝ), fderiv_id, ContinuousLinearMap.id_apply]
  simp

/-- The volume-flux of a field equal to the identity near the minimizer is `3V`. -/
lemma integral_normal_flux_identity_field {V : ℝ} {Ω : Set AmbientSpace} (hV : 0 < V)
    (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hP : HasLocallyFinitePerimeter Ω)
    {Y : AmbientSpace → AmbientSpace} (hY : ContDiff ℝ 1 Y) (hcY : HasCompactSupport Y)
    {U : Set AmbientSpace} (hU : IsOpen U) (hΩU : Ω ⊆ U) (hYU : ∀ x ∈ U, Y x = x) :
    (∫ x in reducedBoundary Ω hP hmin.1,
      inner ℝ (Y x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3) = 3 * V := by
  have hvolfin : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  rw [← (first_variation_volume_eq Ω hP hmin.1 hvolfin hY hcY).2]
  have hdiv : ∀ x ∈ U, divergenceN Y x = 3 := fun x hx =>
    divergenceN_eq_three_of_eventuallyEq_id
      (Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy => hYU y hy)
  rw [setIntegral_congr_fun₀ hmin.1 (fun x hx => hdiv x (hΩU hx)), setIntegral_const,
    measureReal_def, hmin.2.1, ENNReal.toReal_ofReal hV.le, smul_eq_mul, mul_comm]

/-- Blueprint `prop:scaling-identity`, uniqueness: any multiplier satisfying the weak
Euler--Lagrange equation against smooth compactly supported fields is the explicit one. -/
theorem eq_minimizerMultiplier_of_weak_euler_lagrange {V : ℝ} {Ω : Set AmbientSpace}
    (hV : 0 < V) (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω) {lam : ℝ}
    (hlam : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ (⊤ : ℕ∞) X → HasCompactSupport X →
      (∫ x in reducedBoundary Ω hP hmin.1,
          tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
        ∫ x in reducedBoundary Ω hP hmin.1,
          (lam - (coulombPotential Ω x).toReal) *
            inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3) :
    lam = minimizerMultiplier V Ω := by
  obtain ⟨Y, hY, hcY, U, hU, hΩU, hYU⟩ := exists_identity_field hb
  have hY1 : ContDiff ℝ 1 Y := hY.of_le (by simp)
  have h1 := hlam Y hY hcY
  rw [constrained_first_variation_eq hV hmin hb hP hY1 hcY] at h1
  have hB := integral_normal_flux_identity_field hV hmin hP hY1 hcY hU
    (subset_closure.trans hΩU) hYU
  have hiB := integrableOn_normal_flux hP hmin.1 hY1.continuous hcY
  have hiD := integrableOn_coulomb_boundary_flux hP hmin.1 hb hY1.continuous hcY
  simp_rw [sub_mul] at h1
  rw [integral_sub (Integrable.const_mul hiB _) hiD, integral_sub (Integrable.const_mul hiB _) hiD,
    integral_const_mul, integral_const_mul, hB] at h1
  have h3 : lam * (3 * V) = minimizerMultiplier V Ω * (3 * V) := by linarith
  exact mul_right_cancel₀ (mul_pos (by norm_num) hV).ne' h3

/-- Blueprint `prop:scaling-identity`: `3Vλ = 2P + 5D = 5𝓔 - 3P`. -/
theorem scaling_identity {V : ℝ} {Ω : Set AmbientSpace}
    (hV : 0 < V) (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω) {lam : ℝ}
    (hlam : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ (⊤ : ℕ∞) X → HasCompactSupport X →
      (∫ x in reducedBoundary Ω hP hmin.1,
          tangentialDivergence X (reducedNormal Ω hP hmin.1) x ∂hausdorffMeasure2 3) =
        ∫ x in reducedBoundary Ω hP hmin.1,
          (lam - (coulombPotential Ω x).toReal) *
            inner ℝ (X x) (reducedNormal Ω hP hmin.1 x) ∂hausdorffMeasure2 3) :
    3 * V * lam = 2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * lam = 5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal := by
  have hvolfin : volume Ω < ∞ := by rw [hmin.2.1]; exact ENNReal.ofReal_lt_top
  have h := eq_minimizerMultiplier_of_weak_euler_lagrange hV hmin hb hP hlam
  have h1 : 3 * V * lam = 2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal := by
    rw [h, minimizerMultiplier, mul_div_cancel₀ _ (mul_pos (by norm_num) hV).ne']
  refine ⟨h1, ?_⟩
  rw [h1, energy, ENNReal.toReal_add hmin.2.2.1.ne (coulombEnergy_lt_top Ω hvolfin).ne]
  ring

/-- The explicit multiplier satisfies the scaling identity. -/
theorem scaling_identity_minimizerMultiplier {V : ℝ} {Ω : Set AmbientSpace}
    (hV : 0 < V) (hmin : IsLebesgueFixedVolumeMinimizer V Ω) (hb : Bornology.IsBounded Ω)
    (hP : HasLocallyFinitePerimeter Ω) :
    3 * V * minimizerMultiplier V Ω =
        2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * minimizerMultiplier V Ω =
        5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal :=
  scaling_identity hV hmin hb hP fun _ hX hcX =>
    constrained_first_variation_eq hV hmin hb hP (hX.of_le (by simp)) hcX

/-- Uniqueness of the multiplier for the fixed representative, frontier form. -/
theorem MinimizerRep.eq_minimizerMultiplier {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {lam : ℝ}
    (hlam : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ (⊤ : ℕ∞) X → HasCompactSupport X →
      (∫ x in frontier Ω, tangentialDivergence X
          (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet) x
          ∂hausdorffMeasure2 3) =
        ∫ x in frontier Ω, (lam - (coulombPotential Ω x).toReal) *
          inner ℝ (X x) (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet x)
          ∂hausdorffMeasure2 3) :
    lam = minimizerMultiplier V Ω := by
  apply eq_minimizerMultiplier_of_weak_euler_lagrange h.volume_pos h.minimizer h.bounded
    h.hasLocallyFinitePerimeter
  intro X hX hcX
  have hX' := hlam X hX hcX
  rwa [Measure.restrict_congr_set
    (h.c1Boundary.boundary_ae_eq_reducedBoundary h.isOpen h.hasLocallyFinitePerimeter)] at hX'

/-- The scaling identity for the fixed representative, frontier form. -/
theorem MinimizerRep.scaling_identity {V : ℝ} {Ω : Set AmbientSpace}
    (h : MinimizerRep V Ω) {lam : ℝ}
    (hlam : ∀ X : AmbientSpace → AmbientSpace, ContDiff ℝ (⊤ : ℕ∞) X → HasCompactSupport X →
      (∫ x in frontier Ω, tangentialDivergence X
          (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet) x
          ∂hausdorffMeasure2 3) =
        ∫ x in frontier Ω, (lam - (coulombPotential Ω x).toReal) *
          inner ℝ (X x) (reducedNormal Ω h.hasLocallyFinitePerimeter h.nullMeasurableSet x)
          ∂hausdorffMeasure2 3) :
    3 * V * lam = 2 * (perimeter Ω).toReal + 5 * (coulombEnergy Ω).toReal ∧
      3 * V * lam = 5 * (energy Ω).toReal - 3 * (perimeter Ω).toReal := by
  rw [h.eq_minimizerMultiplier hlam]
  exact scaling_identity_minimizerMultiplier h.volume_pos h.minimizer h.bounded
    h.hasLocallyFinitePerimeter

end LiquidDrop
