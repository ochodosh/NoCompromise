module

public import NoCompromise.Elliptic.HarmonicAlgebra

@[expose] public section

/-!
# The explicit three-dimensional Hopf barrier

The barrier is R / ‖x-q‖ - 1. Its harmonicity comes from the proved singular
Newtonian distribution identity, and its inward quotient is computed exactly.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology
namespace LiquidDrop
set_option maxSynthPendingDepth 8

def hopfBarrier (q : AmbientSpace) (R : ℝ) (x : AmbientSpace) : ℝ :=
  R / ‖x - q‖ - 1

theorem hasDistributionalLaplacianOn_hopfBarrier (q : AmbientSpace) (R : ℝ)
    {U : Set AmbientSpace} (hq : q ∉ U) :
    HasDistributionalLaplacianOn (hopfBarrier q R) (fun _ => 0) U := by
  change HasDistributionalLaplacianOn (fun x => R / ‖x - q‖ - 1) (fun _ => 0) U
  simpa only [hopfBarrier, div_eq_mul_inv, mul_zero, sub_zero, Pi.smul_apply,
    smul_eq_mul] using
    ((hasDistributionalLaplacianOn_newtonKernel_away q hq).const_mul R).sub
      (hasDistributionalLaplacianOn_const U 1)

lemma continuousOn_hopfBarrier (q : AmbientSpace) (R : ℝ) :
    ContinuousOn (hopfBarrier q R) {q}ᶜ := by
  apply (continuousOn_const.div (continuous_id.sub continuous_const).norm.continuousOn ?_).sub
    continuousOn_const
  intro x hx
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (by simpa only [mem_compl_iff,
    mem_singleton_iff, id_eq] using hx))

lemma hopfBarrier_eq_zero_on_sphere (q : AmbientSpace) {R : ℝ} (hR : 0 < R)
    {x : AmbientSpace} (hx : x ∈ sphere q R) : hopfBarrier q R x = 0 := by
  have hn : ‖x - q‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hx
  simp only [hopfBarrier, hn, div_self hR.ne', sub_self]

lemma hopfBarrier_pos_inside (q : AmbientSpace) {R : ℝ} (_hR : 0 < R)
    {x : AmbientSpace} (hx : x ∈ ball q R) (hxq : x ≠ q) : 0 < hopfBarrier q R x := by
  have hn : 0 < ‖x - q‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxq)
  have hxR : ‖x - q‖ < R := by simpa only [mem_ball, dist_eq_norm] using hx
  exact sub_pos.mpr ((one_lt_div hn).mpr hxR)

lemma norm_hopf_inward_point (q p : AmbientSpace) {R s : ℝ} (hR : 0 < R)
    (hp : p ∈ sphere q R) (_hs : 0 ≤ s) (hsR : s ≤ R) :
    ‖p + (s / R) • (q - p) - q‖ = R - s := by
  have hpn : ‖p - q‖ = R := by simpa only [mem_sphere, dist_eq_norm] using hp
  have heq : p + (s / R) • (q - p) - q = (1 - s / R) • (p - q) := by module
  have hsign : 0 ≤ 1 - s / R := sub_nonneg.mpr ((div_le_one hR).mpr hsR)
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hsign, hpn]
  field_simp [hR.ne']

lemma hopfBarrier_inward_value (q p : AmbientSpace) {R s : ℝ} (hR : 0 < R)
    (hp : p ∈ sphere q R) (hs : 0 ≤ s) (hsR : s < R) :
    hopfBarrier q R (p + (s / R) • (q - p)) = s / (R - s) := by
  rw [hopfBarrier, norm_hopf_inward_point q p hR hp hs hsR.le]
  field_simp [(sub_pos.mpr hsR).ne']
  ring

lemma hopfBarrier_inward_quotient (q p : AmbientSpace) {R s : ℝ} (hR : 0 < R)
    (hp : p ∈ sphere q R) (hs : 0 < s) (hsR : s < R) :
    (hopfBarrier q R (p + (s / R) • (q - p)) - hopfBarrier q R p) / s =
      1 / (R - s) := by
  rw [hopfBarrier_inward_value q p hR hp hs.le hsR,
    hopfBarrier_eq_zero_on_sphere q hR hp, sub_zero]
  field_simp

lemma hopfBarrier_inward_quotient_lower (q p : AmbientSpace) {R s : ℝ} (hR : 0 < R)
    (hp : p ∈ sphere q R) (hs : 0 < s) (hsR : s < R) :
    1 / R ≤ (hopfBarrier q R (p + (s / R) • (q - p)) - hopfBarrier q R p) / s := by
  rw [hopfBarrier_inward_quotient q p hR hp hs hsR]
  exact one_div_le_one_div_of_le (sub_pos.mpr hsR) (sub_le_self R hs.le)

end LiquidDrop
