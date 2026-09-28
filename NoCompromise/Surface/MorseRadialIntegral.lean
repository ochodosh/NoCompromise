import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smoothness of weighted radial parametric integrals

For a continuous weight `φ` and a map `H` of class `C^n` on a ball `B(0,R)`, the weighted radial
integral `x ↦ ∫₀¹ φ(t) • H(t • x) dt` is again `C^n` on `B(0,R)`, and smooth when `H` is smooth.
This is the regularity statement used for the coefficient field of `eq:morse-B` in
`lem:morse-coords`.

The proof is by induction on `n`: differentiating under the integral sign replaces the weight
`φ(t)` by `t φ(t)` and `H` by `fderiv ℝ H`.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology Interval

namespace LiquidDrop

universe u

/-- Radial points `t • y`, `t ∈ [0,1]`, of a closed ball about the origin stay in it
(used for `eq:morse-B` in `lem:morse-coords`). -/
private lemma radial_smul_mem_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 ≤ r) {y : E} (hy : y ∈ closedBall (0 : E) r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : t • y ∈ closedBall (0 : E) r :=
  ((convex_closedBall (0 : E) r).starConvex (mem_closedBall_self hr)).smul_mem hy ht.1 ht.2

/-- Points of the interval `Ι 0 1` lie in `[0,1]` (used for `eq:morse-B` in
`lem:morse-coords`). -/
private lemma mem_Icc_of_mem_uIoc_zero_one {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) :
    t ∈ Icc (0 : ℝ) 1 := by
  have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
  exact Ioc_subset_Icc_self ht'

/-- A uniform bound for the weighted radial integrand of `eq:morse-B` in `lem:morse-coords`
on a closed ball about the origin containing `x` and contained in `B(0,R)`. -/
private lemma exists_radial_integrand_bound {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {R : ℝ} {ψ : ℝ → ℝ} (hψ : Continuous ψ) {K : E → G} (hK : ContinuousOn K (ball (0 : E) R))
    {x : E} (hx : x ∈ ball (0 : E) R) :
    ∃ r : ℝ, x ∈ ball (0 : E) r ∧ closedBall (0 : E) r ⊆ ball (0 : E) R ∧
      ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall (0 : E) r, ‖ψ t • K (t • y)‖ ≤ M := by
  have hxR : ‖x‖ < R := mem_ball_zero_iff.mp hx
  set r : ℝ := (‖x‖ + R) / 2 with hr_def
  have hxr : ‖x‖ < r := by rw [hr_def]; linarith
  have hrR : r < R := by rw [hr_def]; linarith
  have hr : 0 ≤ r := (norm_nonneg x).trans hxr.le
  have hsub : closedBall (0 : E) r ⊆ ball (0 : E) R := closedBall_subset_ball hrR
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) r).exists_bound_of_continuousOn
    (hK.mono hsub)
  obtain ⟨Cψ, hCψ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hψ.continuousOn
  refine ⟨r, mem_ball_zero_iff.mpr hxr, hsub, Cψ * C, fun t ht y hy => ?_⟩
  rw [norm_smul]
  exact mul_le_mul (hCψ t ht) (hC _ (radial_smul_mem_closedBall hr hy ht)) (norm_nonneg _)
    ((norm_nonneg _).trans (hCψ t ht))

/-- Continuity in `t` of the weighted radial integrand of `eq:morse-B` in `lem:morse-coords`. -/
private lemma continuousOn_radial_integrand {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {R : ℝ} {ψ : ℝ → ℝ} (hψ : Continuous ψ) {K : E → G} (hK : ContinuousOn K (ball (0 : E) R))
    {r : ℝ} (hr : 0 ≤ r) (hrR : closedBall (0 : E) r ⊆ ball (0 : E) R)
    {y : E} (hy : y ∈ closedBall (0 : E) r) :
    ContinuousOn (fun t : ℝ => ψ t • K (t • y)) (Icc 0 1) := by
  intro t ht
  have h : ContinuousAt K (t • y) :=
    hK.continuousAt (isOpen_ball.mem_nhds (hrR (radial_smul_mem_closedBall hr hy ht)))
  exact (hψ.continuousAt.smul (h.comp (f := fun s : ℝ => s • y)
    (continuousAt_id.smul continuousAt_const))).continuousWithinAt

/-- For a continuous weight `ψ` and `K` continuous on `B(0,R)`, the weighted radial integral
`x ↦ ∫₀¹ ψ(t) • K(t • x) dt` is continuous on `B(0,R)` (`eq:morse-B` in `lem:morse-coords`). -/
theorem continuousOn_radial_integral {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {R : ℝ} {ψ : ℝ → ℝ} (hψ : Continuous ψ) {K : E → G}
    (hK : ContinuousOn K (ball (0 : E) R)) :
    ContinuousOn (fun x : E => ∫ t in (0 : ℝ)..1, ψ t • K (t • x)) (ball (0 : E) R) := by
  intro x hx
  obtain ⟨r, hxr, hrR, M, hM⟩ := exists_radial_integrand_bound hψ hK hx
  have hr : 0 ≤ r := (pos_of_mem_ball hxr).le
  apply ContinuousAt.continuousWithinAt
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => M)
  · filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
    exact ((continuousOn_radial_integrand hψ hK hr hrR (ball_subset_closedBall hy)
      ).intervalIntegrable_of_Icc (by norm_num)).aestronglyMeasurable_restrict_uIoc
  · filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
    exact Eventually.of_forall fun t ht =>
      hM t (mem_Icc_of_mem_uIoc_zero_one ht) y (ball_subset_closedBall hy)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht => ?_
    have h : ContinuousAt K (t • x) :=
      hK.continuousAt (isOpen_ball.mem_nhds (hrR (radial_smul_mem_closedBall hr
        (ball_subset_closedBall hxr) (mem_Icc_of_mem_uIoc_zero_one ht))))
    exact (h.comp (f := fun y : E => t • y) (continuousAt_const.smul continuousAt_id)).const_smul
      (ψ t)

/-- Differentiation under the integral sign for the weighted radial integral of `eq:morse-B` in
`lem:morse-coords`: for `H` of class `C¹` on `B(0,R)` and `x ∈ B(0,R)`, the derivative of
`y ↦ ∫₀¹ φ(t) • H(t • y) dt` at `x` is `∫₀¹ (t φ(t)) • DH(t • x) dt`. -/
theorem hasFDerivAt_radial_integral {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) {H : E → F}
    (hH : ContDiffOn ℝ 1 H (ball (0 : E) R)) {x : E} (hx : x ∈ ball (0 : E) R) :
    HasFDerivAt (fun y : E => ∫ t in (0 : ℝ)..1, φ t • H (t • y))
      (∫ t in (0 : ℝ)..1, (t * φ t) • fderiv ℝ H (t • x)) x := by
  have hdH : ContinuousOn (fderiv ℝ H) (ball (0 : E) R) :=
    hH.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hdiff : DifferentiableOn ℝ H (ball (0 : E) R) := hH.differentiableOn one_ne_zero
  have hψ : Continuous fun t : ℝ => t * φ t := continuous_id.mul hφ
  obtain ⟨r, hxr, hrR, M, hM⟩ := exists_radial_integrand_bound hψ hdH hx
  have hr : 0 ≤ r := (pos_of_mem_ball hxr).le
  have hHc : ContinuousOn H (ball (0 : E) R) := hH.continuousOn
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun y t => (t * φ t) • fderiv ℝ H (t • y))
    (s := ball (0 : E) r) (bound := fun _ => M) (isOpen_ball.mem_nhds hxr)
  · filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
    exact ((continuousOn_radial_integrand hφ hHc hr hrR (ball_subset_closedBall hy)
      ).intervalIntegrable_of_Icc (by norm_num)).aestronglyMeasurable_restrict_uIoc
  · exact (continuousOn_radial_integrand hφ hHc hr hrR (ball_subset_closedBall hxr)
      ).intervalIntegrable_of_Icc (by norm_num)
  · exact ((continuousOn_radial_integrand hψ hdH hr hrR (ball_subset_closedBall hxr)
      ).intervalIntegrable_of_Icc (by norm_num)).aestronglyMeasurable_restrict_uIoc
  · exact Eventually.of_forall fun t ht y hy =>
      hM t (mem_Icc_of_mem_uIoc_zero_one ht) y (ball_subset_closedBall hy)
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t ht y hy => ?_
    have hmem : t • y ∈ ball (0 : E) R :=
      hrR (radial_smul_mem_closedBall hr (ball_subset_closedBall hy)
        (mem_Icc_of_mem_uIoc_zero_one ht))
    have hd : HasFDerivAt H (fderiv ℝ H (t • y)) (t • y) :=
      (hdiff.differentiableAt (isOpen_ball.mem_nhds hmem)).hasFDerivAt
    have h2 := (hd.comp y ((hasFDerivAt_id y).const_smul t)).const_smul (φ t)
    have heq : φ t • (fderiv ℝ H (t • y)).comp (t • ContinuousLinearMap.id ℝ E) =
        (t * φ t) • fderiv ℝ H (t • y) := by
      ext v
      simp [smul_smul, mul_comm]
    rw [heq] at h2
    exact h2

/-- For a continuous weight `φ` and `H` of class `C^n` on the ball `B(0,R)`, the weighted radial
integral `x ↦ ∫₀¹ φ(t) • H(t • x) dt` is `C^n` on `B(0,R)` (`eq:morse-B` in `lem:morse-coords`). -/
theorem contDiffOn_radial_integral_nat {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) {R : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) {H : E → F}
    (hH : ContDiffOn ℝ n H (ball (0 : E) R)) :
    ContDiffOn ℝ n (fun x : E => ∫ t in (0 : ℝ)..1, φ t • H (t • x)) (ball (0 : E) R) := by
  induction n generalizing F φ H with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero] at hH ⊢
    exact continuousOn_radial_integral hφ hH
  | succ n ih =>
    have hH1 : ContDiffOn ℝ 1 H (ball (0 : E) R) :=
      hH.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball] at hH ⊢
    have hI := ih (F := E →L[ℝ] F) (φ := fun t => t * φ t) (continuous_id.mul hφ) hH.2.2
    refine ⟨fun x hx =>
        (hasFDerivAt_radial_integral hφ hH1 hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hI.congr fun x hx => (hasFDerivAt_radial_integral hφ hH1 hx).fderiv

/-- The smooth case of `contDiffOn_radial_integral_nat`: for a continuous weight `φ` and `H`
smooth on `B(0,R)`, the weighted radial integral `x ↦ ∫₀¹ φ(t) • H(t • x) dt` is smooth on
`B(0,R)` (`eq:morse-B` in `lem:morse-coords`). -/
theorem contDiffOn_radial_integral {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {R : ℝ} {φ : ℝ → ℝ} (hφ : Continuous φ) {H : E → F}
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (ball (0 : E) R)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : E => ∫ t in (0 : ℝ)..1, φ t • H (t • x))
      (ball (0 : E) R) :=
  contDiffOn_infty.mpr fun n => contDiffOn_radial_integral_nat n hφ (contDiffOn_infty.mp hH n)

end LiquidDrop
