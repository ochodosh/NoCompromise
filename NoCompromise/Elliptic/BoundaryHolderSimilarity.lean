module

public import NoCompromise.Elliptic.BoundaryHolderOddWeak

@[expose] public section

/-! The common raw odd representative and exact similarity transport used to
glue local boundary representatives. All comparisons preserve almost-everywhere
representatives rather than assigning unjustified pointwise values to H¹ data. -/

noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology Gradient
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def boundaryRawOdd (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  {y | 0 < y (Fin.last 2)}.indicator u x -
    {y | 0 < y (Fin.last 2)}.indicator u (coordinateReflection (Fin.last 2) x)

lemma boundaryOddFunction_eq_raw (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ ball 0 (1 / 64 : ℝ)) :
    boundaryOddFunction u x = boundaryRawOdd u x := by
  have hRx : coordinateReflection (Fin.last 2) x ∈ ball (0 : EuclideanSpace ℝ (Fin 3))
      (1 / 64 : ℝ) := by
    simpa only [mem_ball, dist_zero_right, (coordinateReflection (Fin.last 2)).norm_map] using hx
  simp only [boundaryOddFunction, boundaryRawOdd, boundaryHolderZeroFunction, indicator_apply,
    boundaryHolderBump_eq_one hx, boundaryHolderBump_eq_one hRx, one_mul]

lemma boundaryRawOdd_eq_upper (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : 0 < x (Fin.last 2)) :
    boundaryRawOdd u x = u x := by
  have hn : ¬0 < coordinateReflection (Fin.last 2) x (Fin.last 2) := by
    rw [boundary_reflection_last]
    linarith
  simp only [boundaryRawOdd, indicator_apply, mem_ofPred_eq, hx, hn, ite_true, ite_false,
    sub_zero]

lemma boundary_ballScaling_reflection (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin 3)) :
    coordinateReflection (Fin.last 2) (frozenBallScaling (graphAppendN z 0) hr x) =
      frozenBallScaling (graphAppendN z 0) hr (coordinateReflection (Fin.last 2) x) := by
  simp only [frozenBallScaling_apply, map_add, map_smul, boundary_reflection_flat]

lemma boundaryRawOdd_comp_ballScaling (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ (Fin 3)) :
    boundaryRawOdd (u ∘ frozenBallScaling (graphAppendN z 0) hr) x =
      boundaryRawOdd u (frozenBallScaling (graphAppendN z 0) hr x) := by
  simp only [boundaryRawOdd, indicator_apply, mem_ofPred_eq, Function.comp_def]
  rw [boundary_ballScaling_reflection]
  simp only [frozenBallScaling_apply, PiLp.add_apply,
    graphAppendN_last, PiLp.smul_apply, smul_eq_mul, zero_add, mul_pos_iff_of_pos_left hr]

lemma boundary_ballScaling_quasiMeasurePreserving (c : EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (frozenBallScaling c hr) volume volume := by
  exact (measurePreserving_add_left volume c).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hr.ne')

lemma boundary_ballScaling_symm_quasiMeasurePreserving (c : EuclideanSpace ℝ (Fin 3))
    {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (frozenBallScaling c hr).symm volume volume := by
  have hh := (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).comp
    (measurePreserving_add_right volume (-c)).quasiMeasurePreserving
  simpa only [frozenBallScaling_symm_coe, sub_eq_add_neg, Function.comp_def] using hh

lemma boundary_ballScaling_pullback_ae {E : Type*} {f g : EuclideanSpace ℝ (Fin 3) → E}
    (c : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r) {s : ℝ}
    (he : f =ᵐ[volume.restrict (ball 0 s)] g) :
    (f ∘ (frozenBallScaling c hr).symm) =ᵐ[volume.restrict (ball c (r * s))]
      (g ∘ (frozenBallScaling c hr).symm) := by
  let e := frozenBallScaling c hr
  have hh := (boundary_ballScaling_symm_quasiMeasurePreserving c hr).ae
    ((ae_restrict_iff' measurableSet_ball).mp he)
  filter_upwards [ae_restrict_of_ae hh, ae_restrict_mem measurableSet_ball] with x hx hxB
  exact hx ((frozenBallScaling_mem_ball_iff c (e.symm x) hr s).mp
    (by
      change e (e.symm x) ∈ ball c (r * s)
      rw [e.apply_symm_apply]
      exact hxB))

end LiquidDrop
