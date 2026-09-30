module

public import NoCompromise.Elliptic.CampanatoHolderOscillation
public import NoCompromise.Elliptic.CampanatoHolderIteration

@[expose] public section

/-! The actual weak elliptic equation upgrades a local energy power bound to
an oscillation power bound, with constants uniform over all centers and solutions. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- This is the analytic step used twice in the Campanato bootstrap. Its energy
premise is an explicit bound on the original weak gradient, not on a replacement. -/
theorem campanato_oscillation_growth_on_small_balls {n : ℕ} (hn0 : 0 < n) (hn : n < 4)
    {a β R lam cap HA HG M E : ℝ} (ha : 0 < a)
    (hσ : 0 ≤ β + 2 * a) (hβn : β ≤ n) (hgap : β + 2 * a < n + 2)
    (hR : 0 < R) (hRsmall : R ≤ 1 / 8)
    (hlam : 0 < lam) (hcap : 0 ≤ cap) (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (A : EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (G F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
        (u : EuclideanSpace ℝ (Fin n) → ℝ),
        ContinuousOn A (ball 0 1) → ContinuousOn G (ball 0 1) →
        (∀ x ∈ ball 0 1, ‖A x‖ ≤ cap) →
        (∀ x ∈ ball 0 1, ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ ball 0 1, ∀ y ∈ ball 0 1, ‖G x - G y‖ ≤ HG * dist x y ^ a) →
        HasH1GradientOn u F (ball 0 1) → IsWeakDivergenceEquationOn A F G (ball 0 1) →
        (∫ x in ball 0 1, ‖F x‖ ^ 2) ≤ M →
        ∀ c ∈ ball 0 (3 / 4 : ℝ),
          (∀ r ∈ Ioc 0 R, (∫ x in ball c r, ‖F x‖ ^ 2) ≤ E * r ^ β) →
          ∀ r ∈ Ioc 0 R,
            (∫ x in ball c r, ‖F x - ⨍ y in ball c r, F y‖ ^ 2) ≤ K * r ^ (β + 2 * a) := by
  obtain ⟨C, hC, D, hD, hstep⟩ :=
    campanato_oscillation_recurrence_constants hn0 hn hlam hcap hHA hHG
  obtain ⟨K, hK, hscalar⟩ := campanato_oscillation_growth_from_energy
    hσ hβn hgap hR (by linarith : R ≤ 1) hC.le hD hM (E := E)
  refine ⟨K, hK, ?_⟩
  intro A G F u hA hG hbA hell hHA' hHG' hu hw henergy c hc he
  have hc1 : c ∈ ball 0 1 := ball_subset_ball (by norm_num) hc
  have hGr := campanato_memLp_of_holder_on_unit ha.le hHG hG hHG'
  have hFr := hu.memLp_gradient
  have hi := (memLp_two_iff_integrable_sq_norm hFr.aestronglyMeasurable).mp hFr
  let Φ (s : ℝ) := ∫ x in ball c s, ‖F x - ⨍ y in ball c s, F y‖ ^ 2
  let Ψ (s : ℝ) := ∫ x in ball c s, ‖F x‖ ^ 2
  have hsub (s) (hs : s ≤ R) : ball c s ⊆ ball 0 1 :=
    campanato_small_ball_subset_unit hc (hs.trans hRsmall)
  have hnonneg : ∀ s ∈ Ioc 0 R, 0 ≤ Φ s :=
    fun _ _ => integral_nonneg (fun _ => sq_nonneg _)
  have hbound : ∀ s ∈ Ioc 0 R, Φ s ≤ M := by
    intro s hs
    let : IsFiniteMeasure (volume.restrict (ball c s)) :=
      ⟨by simpa using (isBounded_ball (x := c) (r := s)).measure_lt_top⟩
    have hmin := frozen_integral_norm_sub_average_le
      (hFr.mono_measure (Measure.restrict_mono (hsub s hs.2) le_rfl)) 0
    simp only [sub_zero] at hmin
    exact hmin.trans ((setIntegral_mono_set hi
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
      (Filter.Eventually.of_forall (hsub s hs.2))).trans henergy)
  have hmono : MonotoneOn Φ (Ioc 0 R) := by
    intro s hs t ht hst
    exact campanato_oscillation_mono_radius
      (hFr.mono_measure (Measure.restrict_mono (hsub t ht.2) le_rfl)) hst
  apply hscalar Φ Ψ hnonneg hmono hbound he
  intro s hs θ hθ hθ1
  have hμ := Measure.restrict_mono (hsub s hs.2) (le_rfl (a := volume))
  have hBA : ∀ᵐ x ∂volume.restrict (ball c s), ‖A x‖ ≤ cap := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hbA x (hsub s hs.2 hx)
  have hoscA : ∀ᵐ x ∂volume.restrict (ball c s), ‖A x - A c‖ ≤ HA * s ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hHA' x (hsub s hs.2 hx) c hc1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (le_of_lt hx) ha.le) hHA)
  have hoscG : ∀ᵐ x ∂volume.restrict (ball c s), ‖G x - G c‖ ≤ HG * s ^ a := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (hHG' x (hsub s hs.2 hx) c hc1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow dist_nonneg (le_of_lt hx) ha.le) hHG)
  exact hstep a c s hs.1 u F G A (hu.mono (hsub s hs.2)) (hw.mono (hsub s hs.2))
    ((hA.mono (hsub s hs.2)).aestronglyMeasurable measurableSet_ball) hBA
    (hGr.mono_measure hμ) (hell c hc1) (hbA c hc1) hoscA hoscG θ hθ hθ1

end LiquidDrop
