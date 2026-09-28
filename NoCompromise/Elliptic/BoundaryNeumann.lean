import NoCompromise.Elliptic.BoundaryNeumannHolder
import NoCompromise.Elliptic.BoundaryNeumannWeak
import NoCompromise.Elliptic.CampanatoHolder

/-!
# Homogeneous conormal boundary regularity

The first, homogeneous step of blueprint `thm:boundary-neumann`: even
reflection reduces the half-ball problem to the interior Campanato theorem.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_neumann_flux_memLp {a cap HH : ℝ} (ha : 0 ≤ a) (hHH : 0 ≤ HH)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {H F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hA : ContinuousOn A (closure (boundaryHalfBall 1)))
    (hH : ContinuousOn H (closure (boundaryHalfBall 1)))
    (hbA : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hh : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖H x - H y‖ ≤ HH * dist x y ^ a)
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1))) :
    MemLp (fun x => A x (F x) - H x) 2 (volume.restrict (boundaryHalfBall 1)) := by
  have hmA := (hA.mono subset_closure).aestronglyMeasurable (μ := volume)
    (isOpen_boundaryHalfBall 1).measurableSet
  have hmH := (hH.mono subset_closure).aestronglyMeasurable (μ := volume)
    (isOpen_boundaryHalfBall 1).measurableSet
  have hAF : MemLp (fun x => A x (F x)) 2 (volume.restrict (boundaryHalfBall 1)) := by
    apply hF.of_le_mul (c := cap)
    · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hmA.prodMk hF.aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
      exact (A x).le_opNorm (F x) |>.trans
        (mul_le_mul_of_nonneg_right (hbA x (subset_closure hx)) (norm_nonneg _))
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top 1⟩
  have h0 : (0 : EuclideanSpace ℝ (Fin 3)) ∈ closure (boundaryHalfBall 1) :=
    boundary_neumann_mem_closure (mem_ball_self zero_lt_one) (by simp)
  have hHLp : MemLp H 2 (volume.restrict (boundaryHalfBall 1)) := by
    apply MemLp.of_bound hmH (HH + ‖H 0‖)
    filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
    have hhx := hh x (subset_closure hx) 0 h0
    have hnorm : ‖x‖ ≤ 1 := by
      exact le_of_lt (by simpa only [mem_ball, dist_zero_right] using hx.1)
    have hp := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg x) hnorm ha) hHH
    simp only [dist_zero_right, Real.one_rpow] at hhx hp
    have hn := norm_le_insert' (H x) (H 0)
    linarith
  exact hAF.sub hHLp

theorem boundary_neumann_homogeneous_c1_holder {a lam cap HA HH M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHH : 0 ≤ HH) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (H F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (w : EuclideanSpace ℝ (Fin 3) → ℝ),
        ContinuousOn A (closure (boundaryHalfBall 1)) →
        ContinuousOn H (closure (boundaryHalfBall 1)) →
        (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖A x - A y‖ ≤ HA * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
          ‖H x - H y‖ ≤ HH * dist x y ^ a) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → ∀ i : Fin 3, i ≠ Fin.last 2 →
          A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
          A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → H x (Fin.last 2) = 0) →
        HasH1GradientOn w F (boundaryHalfBall 1) →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x) - H x) (gradient φ x)) = 0) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 1 v (ball 0 (1 / 2 : ℝ)) ∧
          w =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] v ∧
          F =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] gradient v ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ‖gradient v x‖ ≤ C) ∧
          (∀ x ∈ ball 0 (1 / 2 : ℝ), ∀ y ∈ ball 0 (1 / 2 : ℝ),
            ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) := by
  obtain ⟨C, hC, hregularity⟩ := campanato_c1_holder (n := 3) (by norm_num) (by norm_num)
    (HA := 2 * HA) (HG := 2 * HH) (M := 2 * M)
    ha ha1 hlam hcap (by positivity) (by positivity) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro A H F w hA hH hbA hell hholderA hholderH hcross hzero hw hweak henergy
  have hflux := boundary_neumann_flux_memLp ha.le hHH hA hH hbA hholderH hw.memLp_gradient
  have henergy' : (∫ x in ball 0 1, ‖boundaryEvenField F x‖ ^ 2) ≤ 2 * M := by
    rw [boundaryEvenField_energy hw.memLp_gradient]
    linarith
  obtain ⟨v, hv, hwv, hFv, hbound, hholder, _⟩ := hregularity
    (boundaryNeumannCoefficient A) (boundaryNeumannDatum H) (boundaryEvenField F)
    (boundaryEvenFunction w)
    (boundaryNeumannCoefficient_continuousOn ha hHA A hholderA hcross)
    (boundaryNeumannDatum_continuousOn ha hHH H hholderH hzero)
    (boundaryNeumannCoefficient_bound A hbA) (boundaryNeumannCoefficient_elliptic A hell)
    (boundaryNeumannCoefficient_holder ha.le hHA A hholderA hcross)
    (boundaryNeumannDatum_holder ha.le hHH H hholderH hzero)
    hw.boundary_even_h1 (boundary_neumann_even_weak_equation A F H hflux hweak) henergy'
  have hsub : boundaryHalfBall (1 / 2 : ℝ) ⊆ ball 0 (1 / 2 : ℝ) := inter_subset_left
  have hsub1 : boundaryHalfBall (1 / 2 : ℝ) ⊆ boundaryHalfBall 1 :=
    inter_subset_inter_left _ (ball_subset_ball (by norm_num))
  refine ⟨v, hv, ?_, ?_, hbound, hholder⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hwv,
      ae_restrict_mem (isOpen_boundaryHalfBall (1 / 2 : ℝ)).measurableSet] with x hx hxb
    rwa [boundaryEvenFunction_eq_upper w (hsub1 hxb)] at hx
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hFv,
      ae_restrict_mem (isOpen_boundaryHalfBall (1 / 2 : ℝ)).measurableSet] with x hx hxb
    rwa [boundaryEvenField_eq_upper F (hsub1 hxb)] at hx

end LiquidDrop
