import NoCompromise.Elliptic.NewtonianKernel
import NoCompromise.Sobolev.W11Closed
import NoCompromise.Sobolev.W11Classical

/-!
# The reciprocal-distance kernel has a genuine W¹,¹ gradient

Smooth regularized kernels converge in L¹ together with their actual gradients.
The weak-gradient graph is closed, including at the singular point.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped ENNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def classicalNewtonGradient (z : AmbientSpace) : AmbientSpace :=
  -(‖z‖ ^ 3)⁻¹ • z

lemma toDual_classicalNewtonGradient (z : AmbientSpace) :
    (toDual ℝ AmbientSpace) (classicalNewtonGradient z) = newtonDerivativeKernel z := by
  simp only [classicalNewtonGradient, map_smul, newtonDerivativeKernel]
  rfl

lemma integrableOn_classicalNewtonGradient {D : Set AmbientSpace}
    (hD : volume D < ∞) (y : AmbientSpace) :
    IntegrableOn (fun x => classicalNewtonGradient (x - y)) D := by
  have hi : IntegrableOn (fun x => (‖x - y‖ ^ 2)⁻¹) D := by
    simpa only [norm_sub_rev] using integrableOn_inv_norm_sub_sq D hD y
  have hm : Measurable (fun x => classicalNewtonGradient (x - y)) := by
    unfold classicalNewtonGradient
    fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    rw [← (toDual ℝ AmbientSpace).norm_map, toDual_classicalNewtonGradient,
      norm_newtonDerivativeKernel]

lemma gradient_regularizedNewtonKernel_sub {ε : ℝ} (hε : 0 < ε)
    (x y : AmbientSpace) :
    gradient (fun z => regularizedNewtonKernel ε (z - y)) x =
      (toDual ℝ AmbientSpace).symm (regularizedNewtonDerivative ε (x - y)) := by
  apply (toDual ℝ AmbientSpace).injective
  rw [toDual_gradient, LinearIsometryEquiv.apply_symm_apply]
  have h := (hasFDerivAt_regularizedNewtonKernel hε (x - y)).comp x
    ((hasFDerivAt_id x).sub_const y)
  simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using h.fderiv

theorem hasW11GradientOn_reciprocal_distance {D : Set AmbientSpace}
    (hD : IsOpen D) (hbD : Bornology.IsBounded D) (y : AmbientSpace) :
    HasW11GradientOn (fun x => ‖x - y‖⁻¹)
      (fun x => classicalNewtonGradient (x - y)) D := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : ∀ j, 0 < ε j := fun j => by dsimp [ε]; positivity
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f (j : ℕ) (x : AmbientSpace) := regularizedNewtonKernel (ε j) (x - y)
  have hc (j) : ContDiff ℝ 1 (f j) :=
    ((contDiff_regularizedNewtonKernel (hε j)).of_le (by simp)).comp
      (contDiff_id.sub contDiff_const)
  have hf (j) : HasW11GradientOn (f j) (gradient (f j)) D :=
    ⟨hasWeakGradientOn_of_contDiffOn hD (hc j).contDiffOn,
      (hc j).continuous.continuousOn.integrableOn_compact hbD.isCompact_closure |>.mono_set
        subset_closure,
      (continuous_gradient_of_contDiff (hc j)).continuousOn.integrableOn_compact
        hbD.isCompact_closure |>.mono_set subset_closure⟩
  have hg : IntegrableOn (fun x => ‖x - y‖⁻¹) D := by
    simpa only [norm_sub_rev] using integrableOn_coulombKernel D hbD.measure_lt_top y
  have hG := integrableOn_classicalNewtonGradient hbD.measure_lt_top y
  have hGnorm : IntegrableOn (fun x => (‖x - y‖ ^ 2)⁻¹) D := by
    simpa only [norm_sub_rev] using integrableOn_inv_norm_sub_sq D hbD.measure_lt_top y
  have hne : ∀ᵐ x ∂volume.restrict D, x - y ≠ 0 := by
    have ha : ∀ᵐ x : AmbientSpace ∂volume, x ≠ y := by
      simp [ae_iff]
    filter_upwards [ae_restrict_of_ae ha] with x hx
    exact sub_ne_zero.mpr hx
  apply hasW11GradientOn_of_tendsto_L1 hD hf hg hG
  · have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict D)
      (fun x => 2 * ‖x - y‖⁻¹)
      (F := fun j x => ‖f j x - ‖x - y‖⁻¹‖) (f := fun _ => (0 : ℝ))
    apply (by simpa only [integral_zero] using h)
    · exact fun j => ((hf j).integrable_function.sub hg).norm.1
    · exact hg.const_mul 2
    · intro j
      filter_upwards [hne] with x hx
      have hs := regularizedNewton_sqrt_bounds (hε j) (x - y)
      have hb : ‖regularizedNewtonKernel (ε j) (x - y)‖ ≤ ‖x - y‖⁻¹ := by
        rw [regularizedNewtonKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
        exact inv_anti₀ (norm_pos_iff.mpr hx) hs.2.1
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by
        dsimp [f]
        simp only [Real.norm_eq_abs] at hb ⊢
        rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        linarith)
    · filter_upwards [hne] with x hx
      simpa only [f, sub_self, norm_zero] using
        ((tendsto_regularizedNewtonKernel htε hx).sub
          (tendsto_const_nhds (x := ‖x - y‖⁻¹))).norm
  · have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict D)
      (fun x => 2 * (‖x - y‖ ^ 2)⁻¹)
      (F := fun j x => ‖gradient (f j) x - classicalNewtonGradient (x - y)‖)
      (f := fun _ => (0 : ℝ))
    apply (by simpa only [integral_zero] using h)
    · exact fun j => ((hf j).integrable_gradient.sub hG).norm.1
    · exact hGnorm.const_mul 2
    · intro j
      apply Eventually.of_forall
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        ← (toDual ℝ AmbientSpace).norm_map, map_sub,
        gradient_regularizedNewtonKernel_sub (hε j), LinearIsometryEquiv.apply_symm_apply,
        toDual_classicalNewtonGradient]
      exact (norm_sub_le _ _).trans (by
        rw [norm_newtonDerivativeKernel]
        linarith [(norm_regularizedNewtonDerivative_le (hε j) (x - y)).2])
    · apply Eventually.of_forall
      intro x
      have h := ((toDual ℝ AmbientSpace).symm.continuous.tendsto
        (newtonDerivativeKernel (x - y))).comp (tendsto_regularizedNewtonDerivative htε (x - y))
      have he : (toDual ℝ AmbientSpace).symm (newtonDerivativeKernel (x - y)) =
          classicalNewtonGradient (x - y) := by
        rw [← toDual_classicalNewtonGradient, LinearIsometryEquiv.symm_apply_apply]
      simpa only [f, gradient_regularizedNewtonKernel_sub (hε _), he, sub_self, norm_zero,
        Function.comp_def] using
        (h.sub (tendsto_const_nhds (x := classicalNewtonGradient (x - y)))).norm

end LiquidDrop
