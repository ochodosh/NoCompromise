module

public import NoCompromise.Regularity.HarmonicBlowupTests
public import NoCompromise.Elliptic.HarmonicMeanValue

@[expose] public section

/-!
# Harmonic compactness of bounded planar H¹ sequences

Rellich provides simultaneous weak H¹ and strong L² convergence. Vanishing
actual test residuals identify the limit as distributionally harmonic; the
proved interior regularity theorem supplies a smooth representative. Its
classical gradient and energy are identified with the original Hilbert class.
-/

noncomputable section
open MeasureTheory Set Filter Metric InnerProductSpace
open scoped Topology ENNReal NNReal Gradient
namespace LiquidDrop

/-- The smooth harmonic representative retains the genuine H¹ gradient and
exact square-sum energy of its Hilbert-space class. -/
theorem harmonicBlowup_smooth_representative {n : ℕ} (hn : n < 4)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (v : H1Space U)
    (hv : HasDistributionalLaplacianOn v (fun _ => 0) U) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) h U ∧ h =ᵐ[volume.restrict U] v ∧
      gradient h =ᵐ[volume.restrict U] v.gradientLp ∧
      HasH1GradientOn h (gradient h) U ∧
      HasDistributionalLaplacianOn h (fun _ => 0) U ∧
      (∀ x ∈ U, laplacianN h x = 0) ∧
      (∫ x in U, ‖h x‖ ^ 2 + ‖gradient h x‖ ^ 2) = ‖v‖ ^ 2 := by
  have hloc : ∀ x ∈ U, ∃ R > 0, ball x R ⊆ U ∧
      MemLp v 2 (volume.restrict (ball x R)) := by
    intro x hx
    obtain ⟨R, hR, hs⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    exact ⟨R, hR, hs, v.hasH1GradientOn.memLp_function.mono_measure
      (Measure.restrict_mono_set _ hs)⟩
  obtain ⟨h, hc, he, hz, _⟩ := hv.exists_smooth_mean_value hn hU hloc
  have hw : HasWeakGradientOn h v.gradientLp U :=
    v.hasH1GradientOn.toHasWeakGradientOn.congr_ae he.symm EventuallyEq.rfl
  have hg : gradient h =ᵐ[volume.restrict U] v.gradientLp :=
    (hasWeakGradientOn_of_contDiffOn hU (hc.of_le (by simp))).unique hU hw
  have hh1 : HasH1GradientOn h (gradient h) U :=
    v.hasH1GradientOn.congr_ae he.symm hg.symm
  have hef := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 2) he)
  have heg := congrArg ENNReal.toReal (eLpNorm_congr_ae (p := 2) hg)
  rw [toReal_eLpNorm,
    toReal_eLpNorm] at hef
  rw [toReal_eLpNorm,
    toReal_eLpNorm] at heg
  refine ⟨h, hc, he, hg, hh1, hv.congr_ae he.symm EventuallyEq.rfl, hz, ?_⟩
  rw [integral_add (hh1.memLp_function.integrable_norm_pow (by norm_num : 2 ≠ 0))
    (hh1.memLp_gradient.integrable_norm_pow (by norm_num : 2 ≠ 0)),
    ← lpNorm_two_sq_eq_integral_norm_sq hh1.memLp_function,
    ← lpNorm_two_sq_eq_integral_norm_sq hh1.memLp_gradient,
    hef, heg,
    ← v.norm_toLp_eq_lpNorm, ← v.norm_gradientLp_eq_lpNorm, v.norm_sq]

/-- Strong convergence of scalar L² classes is convergence of the actual
squared integral error against any representative of the limit. -/
lemma harmonicBlowup_tendsto_integral_error {n : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {u : ℕ → H1Space U} {v : H1Space U}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (he : h =ᵐ[volume.restrict U] v)
    (ht : Tendsto (fun j => (u j).toLp) atTop (𝓝 v.toLp)) :
    Tendsto (fun j => ∫ x in U, |u j x - h x| ^ 2) atTop (𝓝 0) := by
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero.mp ht).pow 2
  simp only [zero_pow (by norm_num : 2 ≠ 0)] at hnorm
  have heq (j : ℕ) : ‖(u j).toLp - v.toLp‖ ^ 2 =
      ∫ x in U, |u j x - h x| ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change (∫ x in U, inner ℝ (((u j).toLp - v.toLp) x)
      (((u j).toLp - v.toLp) x)) = _
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u j).toLp v.toLp, he] with x hx he
    rw [hx, he]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, Pi.sub_apply]
  simpa only [heq] using hnorm

/-- The analytic compactness theorem used in blueprint `lem:blowup-compactness`.
The bound and test residuals concern the actual H¹ sequence. -/
theorem harmonicBlowup_compactness (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ}
    (hr : 0 < r) (u : ℕ → H1Space (ball z r)) {C : ℝ}
    (hu : ∀ j, ‖u j‖ ≤ C)
    (hres : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ ball z r →
      Tendsto (fun j => ∫ x in ball z r,
        inner ℝ ((u j).gradientLp x) (gradient φ x)) atTop (𝓝 0)) :
    ∃ (v : H1Space (ball z r)) (σ : ℕ → ℕ) (h : EuclideanSpace ℝ (Fin 2) → ℝ),
      StrictMono σ ∧ ‖v‖ ≤ C ∧
      (∀ ℓ : H1Space (ball z r) →L[ℝ] ℝ,
        Tendsto (fun j => ℓ (u (σ j))) atTop (𝓝 (ℓ v))) ∧
      Tendsto (fun j => (u (σ j)).toLp) atTop (𝓝 v.toLp) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) h (ball z r) ∧ h =ᵐ[volume.restrict (ball z r)] v ∧
      gradient h =ᵐ[volume.restrict (ball z r)] v.gradientLp ∧
      HasH1GradientOn h (gradient h) (ball z r) ∧
      HasDistributionalLaplacianOn h (fun _ => 0) (ball z r) ∧
      (∀ x ∈ ball z r, laplacianN h x = 0) ∧
      (∫ x in ball z r, ‖h x‖ ^ 2 + ‖gradient h x‖ ^ 2) ≤ C ^ 2 ∧
      Tendsto (fun j => ∫ x in ball z r, |u (σ j) x - h x| ^ 2) atTop (𝓝 0) := by
  obtain ⟨v, σ, hσ, hv, hw, ht⟩ := rellich_disk z hr u hu
  have hd := harmonicBlowup_distributional_limit hw
    (fun φ hφ hcφ hsφ => (hres φ hφ hcφ hsφ).comp hσ.tendsto_atTop)
  obtain ⟨h, hc, he, hg, hh1, hdist, hz, henergy⟩ :=
    harmonicBlowup_smooth_representative (by norm_num : 2 < 4) isOpen_ball v hd
  refine ⟨v, σ, h, hσ, hv, hw, ht, hc, he, hg, hh1, hdist, hz, ?_,
    harmonicBlowup_tendsto_integral_error he ht⟩
  rw [henergy]
  exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg v).trans hv)).mpr hv

end LiquidDrop
