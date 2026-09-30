module

public import NoCompromise.Ball.Perimeter
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Rigidity: a homothetic gradient map onto the unit ball forces a ball

Blueprint `thm:isoperimetric-rigidity`, Step 5. If a map `g` (the gradient of the
auxiliary function) has derivative `α • id` with `α > 0` on a preconnected open set `G`,
its image of `G` contains the unit ball, and `α ^ 3 |G| ≤ |B_1|`, then `G` is the ball of
radius `1 / α` centered at `-(α⁻¹ • b)`, where `g = α • · + b` on `G`.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Pointwise
namespace LiquidDrop

/-- A map with derivative `α • id` on a preconnected open set is `x ↦ α • x + b` there. -/
theorem exists_eq_smul_add_of_hasFDerivAt_smul_id {G : Set AmbientSpace} (hGo : IsOpen G)
    (hGc : IsPreconnected G) {g : AmbientSpace → AmbientSpace} {α : ℝ}
    (hg : ∀ x ∈ G, HasFDerivAt g (α • ContinuousLinearMap.id ℝ AmbientSpace) x) :
    ∃ b : AmbientSpace, ∀ x ∈ G, g x = α • x + b := by
  have hd : ∀ x ∈ G,
      HasFDerivAt (fun y => g y - α • y) (0 : AmbientSpace →L[ℝ] AmbientSpace) x := by
    intro x hx
    have h := (hg x hx).sub ((hasFDerivAt_id x).const_smul α)
    rw [sub_self] at h
    exact h
  obtain ⟨b, hb⟩ := hGo.exists_is_const_of_fderiv_eq_zero hGc
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => by simpa using (hd x hx).fderiv)
  refine ⟨b, fun x hx => ?_⟩
  have := hb x hx
  rw [← this]
  abel

/-- An open set containing the unit ball with volume at most that of the unit ball is the unit
ball. -/
theorem eq_ball_of_ball_subset_of_volume_le {U : Set AmbientSpace} (hU : IsOpen U)
    (hsub : ball (0 : AmbientSpace) 1 ⊆ U)
    (hvol : volume U ≤ ENNReal.ofReal (4 * Real.pi / 3)) : U = ball 0 1 := by
  have hball : volume (ball (0 : AmbientSpace) 1) = ENNReal.ofReal (4 * Real.pi / 3) := by
    rw [volume_ball_eq_ofReal 0 zero_le_one]
    norm_num
  have hsplit : volume (ball (0 : AmbientSpace) 1) + volume (U \ ball 0 1) = volume U := by
    rw [measure_add_sdiff measurableSet_ball.nullMeasurableSet, union_eq_right.mpr hsub]
  have hdiff0 : volume (U \ ball (0 : AmbientSpace) 1) = 0 := by
    have h := ENNReal.le_sub_of_add_le_left (by rw [hball]; exact ENNReal.ofReal_ne_top)
      (hsplit.le.trans hvol)
    rw [← hball, tsub_self] at h
    exact le_antisymm h bot_le
  have hclosed0 : volume (U \ closedBall (0 : AmbientSpace) 1) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_right ball_subset_closedBall) hdiff0
  have hempty : U \ closedBall (0 : AmbientSpace) 1 = ∅ :=
    ((hU.sdiff isClosed_closedBall).measure_eq_zero_iff volume).mp hclosed0
  have hUcb : U ⊆ closedBall (0 : AmbientSpace) 1 := sdiff_eq_empty.mp hempty
  have hUb : U ⊆ ball (0 : AmbientSpace) 1 := by
    rw [← interior_closedBall (0 : AmbientSpace) one_ne_zero]
    exact interior_maximal hUcb hU
  exact Subset.antisymm hUb hsub

/-- Blueprint thm:isoperimetric-rigidity, Step 5: if `∇z` has derivative `α I` (`α > 0`) on the
preconnected open set `G`, its image of `G` contains `B_1`, and `α^3 |G| ≤ |B_1|`, then `G` is a
ball of radius `1/α`. -/
theorem eq_ball_of_hasFDerivAt_smul_id {G : Set AmbientSpace} (hGo : IsOpen G)
    (hGc : IsPreconnected G) {g : AmbientSpace → AmbientSpace} {α : ℝ} (hα : 0 < α)
    (hg : ∀ x ∈ G, HasFDerivAt g (α • ContinuousLinearMap.id ℝ AmbientSpace) x)
    (hball : ball (0 : AmbientSpace) 1 ⊆ g '' G)
    (hvol : volume G * ENNReal.ofReal (α ^ 3) ≤ ENNReal.ofReal (4 * Real.pi / 3)) :
    ∃ c : AmbientSpace, G = ball c α⁻¹ := by
  obtain ⟨b, hb⟩ := exists_eq_smul_add_of_hasFDerivAt_smul_id hGo hGc hg
  set A : AmbientSpace → AmbientSpace := fun x => α • x + b with hA
  have himg : g '' G = A '' G := image_congr hb
  have hAopen : IsOpenMap A :=
    (isOpenMap_add_right b).comp (isOpenMap_smul₀ hα.ne')
  have hAvol : volume (A '' G) = ENNReal.ofReal (α ^ 3) * volume G := by
    have h1 : A '' G = (fun y => y + b) '' (α • G) := by
      rw [← image_smul, image_image]
    rw [h1, image_add_right, measure_preimage_add_right, Measure.addHaar_smul_of_nonneg _ hα.le,
      finrank_euclideanSpace_fin]
  have hAeq : A '' G = ball 0 1 := by
    refine eq_ball_of_ball_subset_of_volume_le (hAopen G hGo) (himg ▸ hball) ?_
    rw [hAvol, mul_comm]
    exact hvol
  have hAinj : Function.Injective A := by
    intro x y hxy
    simp only [hA, add_left_inj] at hxy
    exact smul_right_injective _ hα.ne' hxy
  refine ⟨-(α⁻¹ • b), ?_⟩
  ext x
  have hmem : x ∈ G ↔ A x ∈ ball (0 : AmbientSpace) 1 := by
    rw [← hAeq, hAinj.mem_set_image]
  rw [hmem, mem_ball, mem_ball, dist_zero_right, dist_eq_norm, sub_neg_eq_add]
  have hx : x + α⁻¹ • b = α⁻¹ • A x := by
    simp only [hA, smul_add, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
  rw [hx, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hα)]
  constructor
  · intro h
    calc α⁻¹ * ‖A x‖ < α⁻¹ * 1 := mul_lt_mul_of_pos_left h (inv_pos.mpr hα)
      _ = α⁻¹ := mul_one _
  · intro h
    have h' : α⁻¹ * ‖A x‖ < α⁻¹ * 1 := by rwa [mul_one]
    exact lt_of_mul_lt_mul_left h' (inv_pos.mpr hα).le

end LiquidDrop
