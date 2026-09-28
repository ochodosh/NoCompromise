import NoCompromise.Elliptic.BoundaryHolderRadiusLocalization
import NoCompromise.Elliptic.BoundaryHolderHalfScaling
import NoCompromise.Elliptic.BoundaryHolderExcess

/-! Frozen boundary decay at every positive radius, obtained from the actual
localized zero extension and exact similarity identities. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- The original weak representative and gradient admit a genuine normalized
half-ball pullback on a fixed smaller radius; actual zero trace is proved. -/
theorem HasH1GradientOn.boundary_local_rescaled {r : ℝ} (hr : 0 < r)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hf : HasH1GradientOn f G (boundaryHalfBall r))
    (hT : HasZeroFlatTraceOn f G (ball 0 r)) :
    HasH1GradientOn (f ∘ frozenBallScaling 0 (show 0 < r / 64 by positivity))
      (fun x => (r / 64) • G (frozenBallScaling 0 (show 0 < r / 64 by positivity) x))
      (boundaryHalfBall 1) ∧
      HasZeroFlatTraceOn (f ∘ frozenBallScaling 0 (show 0 < r / 64 by positivity))
        (fun x => (r / 64) • G (frozenBallScaling 0 (show 0 < r / 64 by positivity) x))
        (ball 0 1) := by
  have hδ : 0 < r / 64 := by positivity
  let e := frozenBallScaling (0 : EuclideanSpace ℝ (Fin 3)) hδ
  obtain ⟨u, H, hu, hcu, hs, heu, heH⟩ := hf.exists_boundary_radius_zero_extension hr hT
  obtain ⟨hv, hTv⟩ := hu.boundary_comp_similarity_global hcu hs 0 (by simp) hδ
  have hmap : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall (r / 64)) := by
    intro x hx
    simpa only [mul_one] using (boundary_halfBall_scaling_mem hδ x 1).mpr hx
  have heu' : (u ∘ e) =ᵐ[volume.restrict (boundaryHalfBall 1)] (f ∘ e) := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
    exact heu (hmap hx)
  have heH' : (fun x => (r / 64) • H (e x)) =ᵐ[volume.restrict (boundaryHalfBall 1)]
      (fun x => (r / 64) • G (e x)) := by
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
    rw [heH (hmap hx)]
  exact ⟨(hv.mono (subset_univ _)).congr_ae heu' heH',
    (hTv.mono (subset_univ _)).congr_ae isOpen_ball.measurableSet heu' heH'⟩

/-- The same dimension/ellipticity constant works at every positive radius.
Normal-excess decay preserves the zero Dirichlet condition; no symmetry is added. -/
theorem boundary_frozen_decay_radius {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ D : ℝ, 0 < D ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (r : ℝ), 0 < r →
        HasH1GradientOn f G (boundaryHalfBall r) →
        HasZeroFlatTraceOn f G (ball 0 r) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0) (boundaryHalfBall r) →
        (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) → ‖A‖ ≤ cap →
        ∀ θ : ℝ, 0 < θ → θ < 1 →
          boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) G
            (volume.restrict (boundaryHalfBall (r * θ))) ≤
              D * θ ^ 5 * boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) G
                (volume.restrict (boundaryHalfBall r)) ∧
          (∫ x in boundaryHalfBall (r * θ), ‖G x‖ ^ 2) ≤
            D * θ ^ 3 * (∫ x in boundaryHalfBall r, ‖G x‖ ^ 2) := by
  obtain ⟨C, hC, hunit⟩ := boundary_frozen_decay_unit hlam hcap
  let D := max C 1 * 64 ^ 5
  have hD : 0 < D := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) (by norm_num)
  refine ⟨D, hD, ?_⟩
  intro A f G r hr hf hT hw hell hb θ hθ hθ1
  let n : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  have hn : ‖n‖ = 1 := by simp [n]
  have hiG := hf.memLp_gradient.norm.integrable_sq
  have hδ : 0 < r / 64 := by positivity
  have hδr : r / 64 ≤ r := by linarith
  have hrt : r * θ ≤ r := by nlinarith
  have hexmono {s : ℝ} (hs : s ≤ r) :
      boundaryNormalExcess n G (volume.restrict (boundaryHalfBall s)) ≤
        boundaryNormalExcess n G (volume.restrict (boundaryHalfBall r)) :=
    boundary_normal_excess_mono (boundaryHalfBall_mono hs)
      (boundaryHalfBall_volume_lt_top r) hf.memLp_gradient n hn
  have henmono {s : ℝ} (hs : s ≤ r) :
      (∫ x in boundaryHalfBall s, ‖G x‖ ^ 2) ≤ ∫ x in boundaryHalfBall r, ‖G x‖ ^ 2 :=
    setIntegral_mono_set hiG (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall fun _ hx => boundaryHalfBall_mono hs hx)
  have hN : 0 ≤ boundaryNormalExcess n G (volume.restrict (boundaryHalfBall r)) :=
    integral_nonneg fun _ => sq_nonneg _
  have hE : 0 ≤ ∫ x in boundaryHalfBall r, ‖G x‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  by_cases ht : θ < 1 / 64
  · obtain ⟨hf', hT'⟩ := hf.boundary_local_rescaled hr hT
    have hw' := (hw.mono (boundaryHalfBall_mono hδr)).boundary_comp_scaling hδ
    simp only [Function.comp_def, smul_zero] at hw'
    obtain ⟨hN', hE'⟩ := hunit A _ _ hf' hT' hw' hell hb (64 * θ)
      (by positivity) (by linarith)
    rw [boundary_normal_excess_scaling, boundary_normal_excess_scaling] at hN'
    rw [boundary_integral_energy_scaling, boundary_integral_energy_scaling] at hE'
    have he : r / 64 * (64 * θ) = r * θ := by ring
    rw [he, mul_one] at hN' hE'
    have hN'' : boundaryNormalExcess n G (volume.restrict (boundaryHalfBall (r * θ))) ≤
        C * (64 * θ) ^ 5 * boundaryNormalExcess n G
          (volume.restrict (boundaryHalfBall (r / 64))) := by
      apply (mul_le_mul_iff_right₀ (inv_pos.mpr hδ)).mp
      nlinarith only [hN']
    have hE'' : (∫ x in boundaryHalfBall (r * θ), ‖G x‖ ^ 2) ≤
        C * (64 * θ) ^ 3 * ∫ x in boundaryHalfBall (r / 64), ‖G x‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ (inv_pos.mpr hδ)).mp
      nlinarith only [hE']
    constructor
    · calc
        _ ≤ C * (64 * θ) ^ 5 * boundaryNormalExcess n G
            (volume.restrict (boundaryHalfBall r)) :=
          hN''.trans (mul_le_mul_of_nonneg_left (hexmono hδr) (by positivity))
        _ = (C * 64 ^ 5) * θ ^ 5 * boundaryNormalExcess n G
            (volume.restrict (boundaryHalfBall r)) := by ring
        _ ≤ D * θ ^ 5 * boundaryNormalExcess n G
            (volume.restrict (boundaryHalfBall r)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left C 1) (by norm_num))
            (by positivity)) hN
    · have hcoef : C * 64 ^ 3 ≤ D := by
        dsimp [D]
        have hm := le_max_left C 1
        have hp := le_max_right C 1
        nlinarith
      calc
        _ ≤ C * (64 * θ) ^ 3 * (∫ x in boundaryHalfBall r, ‖G x‖ ^ 2) :=
          hE''.trans (mul_le_mul_of_nonneg_left (henmono hδr) (by positivity))
        _ = (C * 64 ^ 3) * θ ^ 3 * (∫ x in boundaryHalfBall r, ‖G x‖ ^ 2) := by ring
        _ ≤ D * θ ^ 3 * (∫ x in boundaryHalfBall r, ‖G x‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity)) hE
  · have ht' : 1 / 64 ≤ θ := le_of_not_gt ht
    have hp5 := boundary_inverse_radius_power (by norm_num : 0 < (1 / 64 : ℝ)) ht' 5
    have hp3 := boundary_inverse_radius_power (by norm_num : 0 < (1 / 64 : ℝ)) ht' 3
    norm_num at hp5 hp3
    have hcoef5 : 1 ≤ D * θ ^ 5 := by
      have hd : (64 : ℝ) ^ 5 ≤ D :=
        le_mul_of_one_le_left (by norm_num) (le_max_right C 1)
      nlinarith [mul_le_mul_of_nonneg_right hd (pow_nonneg hθ.le 5)]
    have hcoef3 : 1 ≤ D * θ ^ 3 := by
      have hd : (64 : ℝ) ^ 3 ≤ D := by
        have hd' : (64 : ℝ) ^ 5 ≤ D :=
          le_mul_of_one_le_left (by norm_num) (le_max_right C 1)
        norm_num at hd' ⊢
        linarith
      nlinarith [mul_le_mul_of_nonneg_right hd (pow_nonneg hθ.le 3)]
    exact ⟨(hexmono hrt).trans (le_mul_of_one_le_left hN hcoef5),
      (henmono hrt).trans (le_mul_of_one_le_left hE hcoef3)⟩

end LiquidDrop
