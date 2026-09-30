module

public import NoCompromise.Elliptic.InteriorH2Hessian
public import NoCompromise.Elliptic.InteriorH2H1

@[expose] public section

/-!
# Actual second weak derivatives for compact global Poisson solutions

The second derivatives are constructed as weak limits of derivatives of smooth
convolutions. Their identification uses strong L² convergence of the first derivatives.
-/

noncomputable section

open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient Convolution

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- An H² representative, including its first gradient and every weak Hessian row. -/
structure HasH2DerivativesOn {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  hasH1GradientOn : HasH1GradientOn u G U
  coordinate_hasH1GradientOn : ∀ i, HasH1GradientOn (fun x => G x i) (H i) U

/-- Compact global H¹ solutions with L² distributional Laplacian have actual H²
weak derivatives, with the sharp Laplacian bound for every Hessian row. -/
theorem HasDistributionalLaplacianOn.hasH2DerivativesOn_of_compact {n : ℕ}
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h : HasDistributionalLaplacianOn u f univ) (hu : HasH1GradientOn u G univ)
    (hcu : HasCompactSupport u) (hf : MemLp f 2 volume) :
    ∃ H : Fin n → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      HasH2DerivativesOn u G H univ ∧
        ∀ i, lpNorm (H i) 2 volume ≤ lpNorm f 2 volume := by
  classical
  let φ (j : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨(1 / ((j : ℝ) + 1)) / 2, 1 / ((j : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hφ : Tendsto (fun j => (φ j).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  let v (j : ℕ) := (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] u
  have hmG : MemLp G 2 volume := by simpa only [Measure.restrict_univ] using hu.memLp_gradient
  have hv (j) := hu.bump_convolution (φ j)
  have hcv (j) : HasCompactSupport (v j) :=
    (φ j).hasCompactSupport_normed.convolution _ hcu
  have hbs (j) : eLpNorm (gradient (v j)) 2 volume ≤ eLpNorm G 2 volume := by
    rw [show gradient (v j) = _ from funext (hv j).2.1]
    exact (hv j).2.2.2.2
  have hmq (j) := memLp_two_convolution_probability_kernel (φ j).continuous_normed
    (φ j).hasCompactSupport_normed (φ j).nonneg_normed (φ j).integral_normed hf
  have hlap (j) : laplacianN (v j) =
      (φ j).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ] f := by
    funext x
    simpa only [Set.indicator_univ] using h.laplacianN_convolution_indicator
      isOpen_univ hu.memLp_function (by simpa only [Measure.restrict_univ] using hf)
      (φ j).contDiff_normed (φ j).hasCompactSupport_normed x (subset_univ _)
  have hblap (j) : lpNorm (laplacianN (v j)) 2 volume ≤ lpNorm f 2 volume := by
    rw [hlap j, ← toReal_eLpNorm, ← toReal_eLpNorm]
    exact ENNReal.toReal_mono hf.eLpNorm_ne_top (hmq j).2.1
  have hcoord (i : Fin n) :
      ∃ H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        HasH1GradientOn (fun x => G x i) H univ ∧ lpNorm H 2 volume ≤ lpNorm f 2 volume := by
    let w (j : ℕ) := poissonCoordinateDerivative i (v j)
    have hws (j) : ContDiff ℝ (⊤ : ℕ∞) (w j) :=
      poissonCoordinateDerivative_smooth (hv j).1 i
    have hcw (j) : HasCompactSupport (w j) :=
      HasCompactSupport.poissonCoordinateDerivative (hcv j) i
    have hmw (j) : MemLp (w j) 2 volume :=
      (hws j).continuous.memLp_of_hasCompactSupport (hcw j)
    have hmDw (j) : MemLp (gradient (w j)) 2 volume :=
      (continuous_gradient_of_contDiff ((hws j).of_le (by simp))).memLp_of_hasCompactSupport
        ((hcw j).of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset (w j)))
    have hwH1 (j) : HasH1GradientOn (w j) (gradient (w j)) univ :=
      ⟨hasWeakGradientOn_of_contDiffOn isOpen_univ ((hws j).of_le (by simp)).contDiffOn,
        by simpa only [Measure.restrict_univ] using hmw j,
        by simpa only [Measure.restrict_univ] using hmDw j⟩
    have htarget : MemLp (fun x => G x i) 2 volume :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hmG
    have hstrong := (hu.tendsto_bump_convolution hφ).2
    have ht : Tendsto (fun j => eLpNorm (w j - fun x => G x i) 2 volume) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hstrong
        (fun _ => bot_le) (fun j => ?_)
      apply eLpNorm_mono_ae ((hmw j).aestronglyMeasurable.sub htarget.aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        simpa only [w, v, Pi.sub_apply, poissonCoordinateDerivative_eq_gradient, PiLp.sub_apply]
          using PiLp.norm_apply_le (gradient (v j) x - G x) i
    have hwA (j) : eLpNorm (w j) 2 volume ≤ eLpNorm G 2 volume := by
      apply le_trans _ (hbs j)
      apply eLpNorm_mono_ae (hmw j).aestronglyMeasurable
      exact Eventually.of_forall fun x => by
        simpa only [w, poissonCoordinateDerivative_eq_gradient] using
          PiLp.norm_apply_le (gradient (v j) x) i
    have hwB (j) : eLpNorm (gradient (w j)) 2 volume ≤ eLpNorm f 2 volume := by
      rw [← ofReal_lpNorm (hmDw j), ← ofReal_lpNorm hf]
      exact ENNReal.ofReal_le_ofReal
        ((lpNorm_gradient_poissonCoordinateDerivative_le (hv j).1 (hcv j) i).trans (hblap j))
    obtain ⟨H, hH, _, hbH⟩ := exists_hasH1GradientOn_of_l2_limit_of_uniform_bounds
      hwH1 (by simpa only [Measure.restrict_univ] using htarget)
      (by simpa only [Measure.restrict_univ] using ht) hmG.eLpNorm_lt_top hf.eLpNorm_lt_top
      (by simpa only [Measure.restrict_univ] using hwA)
      (by simpa only [Measure.restrict_univ] using hwB)
    refine ⟨H, hH, ?_⟩
    have hmH : MemLp H 2 volume := by
      simpa only [Measure.restrict_univ] using hH.memLp_gradient
    rw [← toReal_eLpNorm, ← toReal_eLpNorm]
    apply ENNReal.toReal_mono hf.eLpNorm_ne_top
    simpa only [Measure.restrict_univ] using hbH
  choose H hH hbH using hcoord
  exact ⟨H, ⟨hu, hH⟩, hbH⟩

end LiquidDrop
