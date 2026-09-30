module

public import NoCompromise.Elliptic.BoundaryHolderVariance
public import NoCompromise.Elliptic.FrozenDecayIntegrals

@[expose] public section

/-!
# Half-ball decay from genuine pointwise frozen estimates

The ordinary energy uses a supremum bound. The normal excess uses a derivative
bound and a normal value at the origin. Large radii are handled by monotonicity,
so the estimates apply throughout the unit half-ball.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- The three-dimensional upper half-ball, with normal coordinate last. -/
def boundaryHalfBall (r : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  ball 0 r ∩ {x | 0 < x (Fin.last 2)}

lemma isOpen_boundaryHalfBall (r : ℝ) : IsOpen (boundaryHalfBall r) :=
  isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)

lemma boundaryHalfBall_mono {r R : ℝ} (hrR : r ≤ R) : boundaryHalfBall r ⊆ boundaryHalfBall R :=
  inter_subset_inter_left _ (ball_subset_ball hrR)

lemma boundaryHalfBall_volume_lt_top (r : ℝ) : volume (boundaryHalfBall r) < ∞ :=
  (measure_mono inter_subset_left).trans_lt isBounded_ball.measure_lt_top

lemma boundary_integral_sq_le_of_ae_norm_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} [IsFiniteMeasure μ]
    {F : X → E} (hF : MemLp F 2 μ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂μ, ‖F x‖ ≤ B) :
    (∫ x, ‖F x‖ ^ 2 ∂μ) ≤ B ^ 2 * μ.real univ := by
  calc
    _ ≤ ∫ _x, B ^ 2 ∂μ := by
      apply integral_mono_ae hF.norm.integrable_sq (integrable_const _)
      filter_upwards [hb] with x hx
      exact (sq_le_sq₀ (norm_nonneg _) hB).mpr hx
    _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]

lemma boundary_inverse_radius_power {ρ θ : ℝ} (hρ : 0 < ρ) (hρθ : ρ ≤ θ) (p : ℕ) :
    1 ≤ (ρ⁻¹) ^ p * θ ^ p := by
  rw [← mul_pow]
  apply one_le_pow₀
  rw [inv_mul_eq_div]
  exact (one_le_div hρ).mpr hρθ

lemma boundary_energy_decay_of_bound
    {G F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hG : MemLp G 2 (volume.restrict (boundaryHalfBall 1)))
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B)
    (he : G =ᵐ[volume.restrict (boundaryHalfBall ρ)] F)
    (hb : ∀ x ∈ ball 0 ρ, ‖F x‖ ≤ B * lpNorm G 2 (volume.restrict (boundaryHalfBall 1)))
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∫ x in boundaryHalfBall θ, ‖G x‖ ^ 2) ≤
      max (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) (ρ⁻¹ ^ 3) *
        θ ^ 3 * (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall θ)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top θ⟩
  have hs := boundaryHalfBall_mono hθ1.le
  have hm := hG.mono_measure (Measure.restrict_mono hs le_rfl)
  have hE : 0 ≤ ∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases ht : θ ≤ ρ
  · have hbb : ∀ᵐ x ∂volume.restrict (boundaryHalfBall θ),
        ‖G x‖ ≤ B * lpNorm G 2 (volume.restrict (boundaryHalfBall 1)) := by
      filter_upwards [ae_mono (Measure.restrict_mono (boundaryHalfBall_mono ht) le_rfl) he,
        ae_restrict_mem (isOpen_boundaryHalfBall θ).measurableSet] with x hx hxx
      rw [hx]
      exact hb x (ball_subset_ball ht hxx.1)
    have hh := boundary_integral_sq_le_of_ae_norm_bound hm
      (mul_nonneg hB lpNorm_nonneg) hbb
    simp only [Measure.real, Measure.restrict_apply_univ] at hh
    have hvol : volume.real (boundaryHalfBall θ) ≤
        volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) θ) := measureReal_mono inter_subset_left
    calc
      _ ≤ (B * lpNorm G 2 (volume.restrict (boundaryHalfBall 1))) ^ 2 *
          volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) θ) :=
        hh.trans (mul_le_mul_of_nonneg_left hvol (sq_nonneg _))
      _ = (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) * θ ^ 3 *
          (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by
        rw [frozen_real_volume_ball (by norm_num : 0 < 3) _ hθ.le, mul_pow,
          lpNorm_two_sq_eq_integral_norm_sq hG]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le _)) hE
  · have hp := boundary_inverse_radius_power hρ (le_of_lt (lt_of_not_ge ht)) 3
    calc
      _ ≤ ∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2 := integral_mono_measure
        (Measure.restrict_mono hs le_rfl) (Eventually.of_forall fun _ => sq_nonneg _)
        hG.norm.integrable_sq
      _ ≤ ρ⁻¹ ^ 3 * θ ^ 3 * (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hθ.le _)) hE

lemma boundary_normal_decay_of_derivative_bound
    {G F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hG : MemLp G 2 (volume.restrict (boundaryHalfBall 1)))
    {ρ B b : ℝ} (hρ : 0 < ρ) (hB : 0 ≤ B)
    (he : G =ᵐ[volume.restrict (boundaryHalfBall ρ)] F)
    (hF : ∀ x ∈ ball 0 ρ, DifferentiableAt ℝ F x)
    (hb : ∀ x ∈ ball 0 ρ, ‖fderiv ℝ F x‖ ≤
      B * lpNorm G 2 (volume.restrict (boundaryHalfBall 1)))
    (hF0 : F 0 = b • EuclideanSpace.single (Fin.last 2) 1)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    boundaryNormalExcess (EuclideanSpace.single (Fin.last 2) 1) G
      (volume.restrict (boundaryHalfBall θ)) ≤
      max (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) (ρ⁻¹ ^ 5) *
        θ ^ 5 * (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall θ)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top θ⟩
  have hs := boundaryHalfBall_mono hθ1.le
  have hm := hG.mono_measure (Measure.restrict_mono hs le_rfl)
  have hn : ‖EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖ = 1 := by simp
  have hE : 0 ≤ ∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  by_cases ht : θ ≤ ρ
  · have hbb : ∀ᵐ x ∂volume.restrict (boundaryHalfBall θ),
        ‖G x - F 0‖ ≤ (B * lpNorm G 2 (volume.restrict (boundaryHalfBall 1))) * θ := by
      filter_upwards [ae_mono (Measure.restrict_mono (boundaryHalfBall_mono ht) le_rfl) he,
        ae_restrict_mem (isOpen_boundaryHalfBall θ).measurableSet] with x hx hxx
      rw [hx]
      have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hF hb (convex_ball _ _)
        (mem_ball_self hρ) (ball_subset_ball ht hxx.1)
      simp only [sub_zero] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hxx.1).le
        (mul_nonneg hB lpNorm_nonneg))
    have hshift : MemLp (fun x => G x - F 0) 2 (volume.restrict (boundaryHalfBall θ)) :=
      hm.sub (memLp_const _)
    have hh := boundary_integral_sq_le_of_ae_norm_bound hshift
      (mul_nonneg (mul_nonneg hB lpNorm_nonneg) hθ.le) hbb
    simp only [Measure.real, Measure.restrict_apply_univ] at hh
    have hvol : volume.real (boundaryHalfBall θ) ≤
        volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) θ) := measureReal_mono inter_subset_left
    calc
      _ ≤ ∫ x in boundaryHalfBall θ, ‖G x - F 0‖ ^ 2 := by
        rw [hF0]
        exact boundary_normal_excess_minimizes hm _ hn b
      _ ≤ ((B * lpNorm G 2 (volume.restrict (boundaryHalfBall 1))) * θ) ^ 2 *
          volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) θ) :=
        hh.trans (mul_le_mul_of_nonneg_left hvol (sq_nonneg _))
      _ = (B ^ 2 * volume.real (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) * θ ^ 5 *
          (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by
        rw [frozen_real_volume_ball (by norm_num : 0 < 3) _ hθ.le, mul_pow, mul_pow,
          lpNorm_two_sq_eq_integral_norm_sq hG]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hθ.le _)) hE
  · have hp := boundary_inverse_radius_power hρ (le_of_lt (lt_of_not_ge ht)) 5
    calc
      _ ≤ ∫ x in boundaryHalfBall θ, ‖G x‖ ^ 2 := boundary_normal_excess_le_energy hm _ hn
      _ ≤ ∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2 := integral_mono_measure
        (Measure.restrict_mono hs le_rfl) (Eventually.of_forall fun _ => sq_nonneg _)
        hG.norm.integrable_sq
      _ ≤ ρ⁻¹ ^ 5 * θ ^ 5 * (∫ x in boundaryHalfBall 1, ‖G x‖ ^ 2) := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hθ.le _)) hE

end LiquidDrop
