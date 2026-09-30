module

public import NoCompromise.Elliptic.BoundaryHolderOddOscillation
public import NoCompromise.Elliptic.BoundaryHolderOddWeak
public import NoCompromise.Elliptic.CampanatoHolderPrimitive
public import NoCompromise.Elliptic.CampanatoHolderPowers

@[expose] public section

/-! A genuine C¹,α representative across the flat origin. The continuous weak
gradient comes from the proved Campanato estimate for the explicit odd field;
the scalar representative and its zero boundary values are then derived. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundary_reflection_ae_ball {E : Type*} {f g : EuclideanSpace ℝ (Fin 3) → E}
    {r : ℝ} (he : f =ᵐ[volume.restrict (ball 0 r)] g) :
    (fun x => f (coordinateReflection (Fin.last 2) x)) =ᵐ[volume.restrict (ball 0 r)]
      fun x => g (coordinateReflection (Fin.last 2) x) := by
  let R := coordinateReflection (Fin.last 2)
  have hh := R.measurePreserving.quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_ball).mp he)
  filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem measurableSet_ball] with x hx hxr
  exact hx (by simpa only [mem_ball, dist_zero_right, R.norm_map] using hxr)

lemma boundary_reflection_eq_self_of_flat {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x (Fin.last 2) = 0) : coordinateReflection (Fin.last 2) x = x := by
  rw [← graphAppendN_projection x, hx, boundary_reflection_flat]

/-- Uniform local boundary regularity at the origin, under only the original
weak hypotheses. The representative is C¹ on a full ball and vanishes pointwise
on its flat disk. Its gradient has the full Hölder exponent there. -/
theorem boundary_holder_c1_representative_origin {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 1 v (ball 0 (1 / 512 : ℝ)) ∧
          v =ᵐ[volume.restrict (ball 0 (1 / 512 : ℝ))] boundaryOddFunction u ∧
          v =ᵐ[volume.restrict (boundaryHalfBall (1 / 512 : ℝ))] u ∧
          gradient v =ᵐ[volume.restrict (boundaryHalfBall (1 / 512 : ℝ))] F ∧
          (∀ x ∈ ball 0 (1 / 512 : ℝ), ‖gradient v x‖ ≤ P) ∧
          (∀ x ∈ ball 0 (1 / 512 : ℝ), ∀ y ∈ ball 0 (1 / 512 : ℝ),
            ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          ∀ x ∈ ball 0 (1 / 512 : ℝ), x (Fin.last 2) = 0 → v x = 0 := by
  obtain ⟨J, hJ, hosc⟩ := boundary_holder_odd_oscillation ha ha1 hlam hcap hHA hHG hM
  obtain ⟨C, P, hC, hP, hrep⟩ := campanato_holder_representative_of_power
    (F := EuclideanSpace ℝ (Fin 3)) (by norm_num : 0 < 3) hJ ha
    (by norm_num : (0 : ℝ) < 1 / 512) (M := 4 * M)
  refine ⟨C, P, hC, hP, ?_⟩
  intro u F G A h
  have hfield := boundaryOddField_memLp h.h1.memLp_gradient
  have henergy : (∫ x in ball (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ‖boundaryOddField F x‖ ^ 2) ≤ 4 * M :=
    (boundaryOddField_energy_unit h.h1.memLp_gradient).trans
      (mul_le_mul_of_nonneg_left h.energy_bound (by norm_num))
  obtain ⟨H, heH, hH, hbH, hhH⟩ := hrep (boundaryOddField F)
    (ball 0 (1 / 256 : ℝ)) measurableSet_ball (hfield.restrict _) henergy (by
      intro x hx y hy
      have hh := dist_triangle y x 0
      have hx' : dist x 0 < 1 / 256 := hx
      have hy' : dist y x < 1 / 512 := hy
      change dist y 0 < 1
      linarith) (hosc u F G A h)
  have hw := ((h.h1.boundary_odd_weak_gradient h.trace_zero).mono
    (ball_subset_ball (by norm_num : (1 / 256 : ℝ) ≤ 1 / 64))).congr_ae EventuallyEq.rfl heH
  obtain ⟨v, hv, he, hg⟩ := campanato_c1_representative_of_continuous_weak_gradient
    (by norm_num : (0 : ℝ) < 1 / 512) (by norm_num : (1 / 512 : ℝ) < 1 / 256) hw hH
  have hsmall : ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 512 : ℝ) ⊆ ball 0 (1 / 256 : ℝ) :=
    ball_subset_ball (by norm_num)
  refine ⟨v, hv, he.symm, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left he,
      ae_restrict_mem (isOpen_boundaryHalfBall (1 / 512 : ℝ)).measurableSet] with x hx hxU
    exact hx.symm.trans (boundaryOddFunction_eq_upper u
      (boundaryHalfBall_mono (by norm_num : (1 / 512 : ℝ) ≤ 1 / 64) hxU))
  · filter_upwards [ae_restrict_of_ae_restrict_of_subset (inter_subset_left.trans hsmall) heH,
      ae_restrict_mem (isOpen_boundaryHalfBall (1 / 512 : ℝ)).measurableSet] with x hx hxU
    exact (hg x hxU.1).trans (hx.symm.trans (boundaryOddField_eq_upper F
      (boundaryHalfBall_mono (by norm_num : (1 / 512 : ℝ) ≤ 1) hxU)))
  · intro x hx
    rw [hg x hx]
    exact hbH x (hsmall hx)
  · intro x hx y hy
    rw [hg x hx, hg y hy]
    exact hhH x (hsmall hx) y (hsmall hy)
  · have her := boundary_reflection_ae_ball he
    have hodd : (fun x => v (coordinateReflection (Fin.last 2) x))
        =ᵐ[volume.restrict (ball 0 (1 / 512 : ℝ))] fun x => -v x := by
      filter_upwards [he, her] with x hx hxR
      rw [← hxR, boundaryOddFunction_reflect, hx]
    have hmap : MapsTo (coordinateReflection (Fin.last 2))
        (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 512 : ℝ)) (ball 0 (1 / 512 : ℝ)) := by
      intro x hx
      simpa only [mem_ball, dist_zero_right, (coordinateReflection (Fin.last 2)).norm_map] using hx
    have heq := Measure.eqOn_open_of_ae_eq hodd isOpen_ball
      (hv.continuousOn.comp (coordinateReflection (Fin.last 2)).continuous.continuousOn hmap)
      hv.continuousOn.neg
    intro x hx hflat
    have hh := heq hx
    dsimp only at hh
    rw [boundary_reflection_eq_self_of_flat hflat] at hh
    linarith

end LiquidDrop
