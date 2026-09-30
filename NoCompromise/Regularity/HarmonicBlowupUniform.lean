module

public import NoCompromise.Regularity.HarmonicBlowup
public import NoCompromise.Regularity.HarmonicBlowupUniformNormalized

@[expose] public section

/-!
# Uniform harmonic approximation of every actual graph approximation

For fixed graph-loss and Dirichlet constants, one harmonic energy bound is
chosen before the tolerance and before any graph-height threshold. The final
smallness threshold can be required to lie below any supplied positive graph
threshold. The statement is universal over all graphs satisfying the genuine
approximation estimates and therefore includes their clamped extensions.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- Blueprint `lem:harmonic-approx-uniform`. For a fixed graph parameter, use
its proved base-loss constant `B` and Dirichlet constant `C`. The energy bound
is independent of the tolerance, graph threshold, and chosen clamp height. -/
theorem harmonic_approximation_uniform {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∃ Cb > 0, ∀ εg : ℝ, 0 < εg → ∀ τ : ℝ, 0 < τ →
      ∃ εb > 0, εb ≤ εg ∧
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω),
      (0 : AmbientSpace) ∈ frontier (densityOne E) →
      0 < cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω ≤ εb →
      ∀ (G : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ),
      MeasurableSet G → G ⊆ ball 0 (1 / 2) → LipschitzWith 1 f →
      (reducedBoundary E hE.locallyFinite hE.nullMeasurable ∩ standardCylinder (1 / 2)) ∩
        graphProjectionN 2 ⁻¹' G = graphMap f '' G →
      volume.real (ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) \ G) ≤
        B * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
          (EuclideanSpace.single 2 1) →
      (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
        C * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
          (EuclideanSpace.single 2 1) →
      let a := Real.sqrt (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
        (EuclideanSpace.single 2 1) + ω)
      ∃ h : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiffOn ℝ (⊤ : ℕ∞) h (ball 0 (1 / 4)) ∧
        HasH1GradientOn h (gradient h) (ball 0 (1 / 4)) ∧
        HasDistributionalLaplacianOn h (fun _ => 0) (ball 0 (1 / 4)) ∧
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4), laplacianN h x = 0) ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          |harmonicBlowupFunction f a x - h x| ^ 2) ≤ τ ∧
        (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4),
          |h x| ^ 2 + ‖gradient h x‖ ^ 2) ≤ Cb := by
  have hD : 0 ≤ C + 2 * B + 2 + Real.pi := by positivity
  obtain ⟨Cb, hCb, hu⟩ := harmonicBlowup_uniform_normalized hC hD
  refine ⟨Cb, hCb, fun εg hεg τ hτ => ?_⟩
  obtain ⟨εa, hεa, _, ha⟩ := hu τ hτ
  obtain ⟨εgeom, hεgeom, _, hgeom⟩ := harmonicBlowup_geometry
  let εb := min εg (min εgeom εa)
  have hεb : 0 < εb := lt_min hεg (lt_min hεgeom hεa)
  refine ⟨εb, hεb, min_le_left _ _,
    fun E ω hE h0 hpos hsmall G f hG hGB hf hgraph hbase henergy => ?_⟩
  let a := Real.sqrt (cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
    (EuclideanSpace.single 2 1) + ω)
  have ha0 : 0 < a := Real.sqrt_pos.mpr hpos
  have hasq : a ^ 2 = cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 1
      (EuclideanSpace.single 2 1) + ω := Real.sq_sqrt hpos.le
  have hsmalla : a ^ 2 ≤ εa := by
    rw [hasq]
    exact hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hphase, hheight, hexcess⟩ := hgeom E ω hE h0
    (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2), ‖gradient f x‖ ^ 2) ≤
      C * a ^ 2 := by
    rw [hasq]
    exact henergy.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE.nonneg) hC)
  have hres (φ : EuclideanSpace ℝ (Fin 2) → ℝ) (hφ : ContDiff ℝ 1 φ)
      (hcφ : HasCompactSupport φ) (hsφ : tsupport φ ⊆ ball 0 (1 / 2))
      (M : ℝ) (hM : 0 ≤ M) (hMb : ∀ x, ‖gradient φ x‖ ≤ M) :
      |∫ x in ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2),
        inner ℝ (gradient f x) (gradient φ x)| ≤ (C + 2 * B + 2 + Real.pi) * a ^ 2 * M := by
    rw [hasq]
    exact approxHarmonic_residual_of_bounds hE hphase hheight hf (by norm_num)
      hG hGB hgraph hB hC hbase henergy hexcess hφ hcφ hsφ hM hMb
  have hf1 := harmonicBlowup_hasH1_lipschitz hf
  obtain ⟨h, hc, hh1, hd, hz, henergyh, herr⟩ := ha f (gradient f) hf1 a ha0 hsmalla he hres
  have hs : ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 4) ⊆ ball 0 (1 / 2) :=
    ball_subset_ball (by norm_num)
  refine ⟨h, hc.mono hs, hh1.mono hs, hd.mono hs, fun x hx => hz x (hs hx), ?_, ?_⟩
  · have hi := ((harmonicBlowup_hasH1GradientOn hf1 a).memLp_function.sub
      hh1.memLp_function).integrable_norm_pow (by norm_num : 2 ≠ 0)
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hi
    exact (setIntegral_mono_set hi (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hs)).trans herr
  · have hi := (hh1.memLp_function.integrable_norm_pow (by norm_num : 2 ≠ 0)).add
      (hh1.memLp_gradient.integrable_norm_pow (by norm_num : 2 ≠ 0))
    have hb := (setIntegral_mono_set hi
      (Eventually.of_forall fun _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      (Eventually.of_forall hs)).trans henergyh
    simpa only [Real.norm_eq_abs, Pi.add_apply] using! hb

end LiquidDrop
