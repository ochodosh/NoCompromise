module

public import NoCompromise.Elliptic.BoundaryHolderExcess
public import NoCompromise.Elliptic.BoundaryHolderDecayIntegrals

@[expose] public section

/-! Transfer of frozen decay to a comparison solution, with the actual L² error. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

lemma boundary_transfer_energy_decay
    {F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r θ C : ℝ}
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall r)))
    (hH : MemLp H 2 (volume.restrict (boundaryHalfBall r)))
    (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hdec : (∫ x in boundaryHalfBall (r * θ), ‖H x‖ ^ 2) ≤
      C * θ ^ 3 * ∫ x in boundaryHalfBall r, ‖H x‖ ^ 2) :
    (∫ x in boundaryHalfBall (r * θ), ‖F x‖ ^ 2) ≤
      (2 + 4 * C) * (∫ x in boundaryHalfBall r, ‖F x - H x‖ ^ 2) +
        4 * C * θ ^ 3 * ∫ x in boundaryHalfBall r, ‖F x‖ ^ 2 := by
  have hs : boundaryHalfBall (r * θ) ⊆ boundaryHalfBall r :=
    boundaryHalfBall_mono (by nlinarith)
  have hμ := Measure.restrict_mono hs (le_rfl (a := volume))
  have hsmall := campanato_integral_norm_sq_le_twice
    (hF.mono_measure hμ) (hH.mono_measure hμ)
  have hlarge := campanato_integral_norm_sq_le_twice hH hF
  simp only [norm_sub_rev (H _) (F _)] at hlarge
  have hmono : (∫ x in boundaryHalfBall (r * θ), ‖F x - H x‖ ^ 2) ≤
      ∫ x in boundaryHalfBall r, ‖F x - H x‖ ^ 2 :=
    setIntegral_mono_set (hF.sub hH).norm.integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hs)
  have hscaled := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * C * θ ^ 3 by positivity)
  have hfirst : (∫ x in boundaryHalfBall (r * θ), ‖F x‖ ^ 2) ≤
      (2 + 4 * C * θ ^ 3) * (∫ x in boundaryHalfBall r, ‖F x - H x‖ ^ 2) +
        4 * C * θ ^ 3 * ∫ x in boundaryHalfBall r, ‖F x‖ ^ 2 := by
    nlinarith only [hsmall, hmono, hdec, hscaled]
  have hcoeff : 2 + 4 * C * θ ^ 3 ≤ 2 + 4 * C := by
    have ht := mul_le_mul_of_nonneg_left (pow_le_one₀ hθ.le hθ1.le (n := 3))
      (show 0 ≤ 4 * C by positivity)
    linarith only [ht]
  exact hfirst.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcoeff (integral_nonneg (fun _ => sq_nonneg _))) le_rfl)

lemma boundary_transfer_normal_decay
    {F H : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {r θ C : ℝ}
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall r)))
    (hH : MemLp H 2 (volume.restrict (boundaryHalfBall r)))
    (n : EuclideanSpace ℝ (Fin 3)) (hn : ‖n‖ = 1)
    (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hdec : boundaryNormalExcess n H (volume.restrict (boundaryHalfBall (r * θ))) ≤
      C * θ ^ 5 * boundaryNormalExcess n H (volume.restrict (boundaryHalfBall r))) :
    boundaryNormalExcess n F (volume.restrict (boundaryHalfBall (r * θ))) ≤
      (2 + 4 * C) * (∫ x in boundaryHalfBall r, ‖F x - H x‖ ^ 2) +
        4 * C * θ ^ 5 * boundaryNormalExcess n F (volume.restrict (boundaryHalfBall r)) := by
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall r)) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top r⟩
  let : IsFiniteMeasure (volume.restrict (boundaryHalfBall (r * θ))) :=
    ⟨by simpa using boundaryHalfBall_volume_lt_top (r * θ)⟩
  have hs : boundaryHalfBall (r * θ) ⊆ boundaryHalfBall r :=
    boundaryHalfBall_mono (by nlinarith)
  have hμ := Measure.restrict_mono hs (le_rfl (a := volume))
  have hsmall := boundary_normal_excess_le_twice (hF.mono_measure hμ) (hH.mono_measure hμ) n hn
  have hlarge := boundary_normal_excess_le_twice hH hF n hn
  simp only [norm_sub_rev (H _) (F _)] at hlarge
  have hmono : (∫ x in boundaryHalfBall (r * θ), ‖F x - H x‖ ^ 2) ≤
      ∫ x in boundaryHalfBall r, ‖F x - H x‖ ^ 2 :=
    setIntegral_mono_set (hF.sub hH).norm.integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _)) (Eventually.of_forall hs)
  have hscaled := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * C * θ ^ 5 by positivity)
  have hfirst : boundaryNormalExcess n F (volume.restrict (boundaryHalfBall (r * θ))) ≤
      (2 + 4 * C * θ ^ 5) * (∫ x in boundaryHalfBall r, ‖F x - H x‖ ^ 2) +
        4 * C * θ ^ 5 * boundaryNormalExcess n F (volume.restrict (boundaryHalfBall r)) := by
    nlinarith only [hsmall, hmono, hdec, hscaled]
  have hcoeff : 2 + 4 * C * θ ^ 5 ≤ 2 + 4 * C := by
    have ht := mul_le_mul_of_nonneg_left (pow_le_one₀ hθ.le hθ1.le (n := 5))
      (show 0 ≤ 4 * C by positivity)
    linarith only [ht]
  exact hfirst.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcoeff (integral_nonneg (fun _ => sq_nonneg _))) le_rfl)

end LiquidDrop
