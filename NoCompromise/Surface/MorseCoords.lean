module

public import NoCompromise.Surface.MorseIndex
public import NoCompromise.Surface.MorseModel
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Ingredients for local Morse coordinates in the plane

This file proves the Taylor integral representation, the C¹ symmetric coefficient
field of `eq:morse-B`, and a local C¹ diffeomorphism for the explicit
completion-of-squares map when its two pivots at zero are nonzero.
The intended chart regularity is C¹ pending the user's wording decision.

The full `lem:morse-coords` is not yet assembled: selecting the initial linear
coordinates and identifying the signs with `formIndex` remain to be formalized.
-/

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology Interval

namespace LiquidDrop

local notation "E2" => EuclideanSpace ℝ (Fin 2)

set_option maxHeartbeats 800000 in
-- The nested Hessian chain rule exceeds the default elaboration budget.
/-- `eq:morse-B` in `lem:morse-coords`: Taylor's integral identity along a radial
segment. C² near every point of the segment suffices for this identity. -/
theorem morse_taylor_integral {g : E2 → ℝ} {x : E2}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 g (t • x))
    (h0 : g 0 = 0) (hd : fderiv ℝ g 0 = 0) :
    g x = ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ g) (t • x) x x := by
  have hr (t : ℝ) : HasDerivAt (fun t : ℝ => t • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have hg' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => g (t • x)) (fderiv ℝ g (t • x) x) t :=
    ((hg t ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hr t)
  have hdC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 1 (fderiv ℝ g) (t • x) :=
    (hg t ht).fderiv_right (by norm_num)
  have hg'' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => fderiv ℝ g (t • x) x)
        (fderiv ℝ (fderiv ℝ g) (t • x) x x) t := by
    simpa using (((hdC t ht).differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt
      t (hr t)).clm_apply (hasDerivAt_const t x)
  have hc' : ContinuousOn (fun t : ℝ => fderiv ℝ g (t • x) x) (Icc 0 1) :=
    fun t ht => (hg'' t ht).continuousAt.continuousWithinAt
  have hc'' : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x) x x)
      (Icc 0 1) := by
    intro t ht
    have h : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (t • x) :=
      ((hdC t ht).fderiv_right (m := 0) (by norm_num)).continuousAt
    exact (((h.comp (f := fun s : ℝ => s • x) (hr t).continuousAt).clm_apply
      continuousAt_const).clm_apply continuousAt_const).continuousWithinAt
  have hi' : IntervalIntegrable (fun t : ℝ => fderiv ℝ g (t • x) x) volume 0 1 :=
    hc'.intervalIntegrable_of_Icc (by norm_num)
  have hi'' : IntervalIntegrable (fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x) x x)
      volume 0 1 := hc''.intervalIntegrable_of_Icc (by norm_num)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hg' t (by simpa using ht)) hi'
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => 1 - t) (u' := fun _ : ℝ => -1)
    (v := fun t : ℝ => fderiv ℝ g (t • x) x)
    (v' := fun t : ℝ => fderiv ℝ (fderiv ℝ g) (t • x) x x)
    (fun t _ => by simpa using (hasDerivAt_id t).const_sub 1)
    (fun t ht => hg'' t (by simpa using ht)) (intervalIntegrable_const) hi''
  simp only [one_smul, zero_smul, h0, sub_zero] at hftc
  simpa [hd, intervalIntegral.integral_neg, hftc] using hip.symm

/-- `eq:morse-B` in `lem:morse-coords` holds on a ball about a C² critical
point whose critical value is zero. -/
theorem exists_morse_taylor_integral {g : E2 → ℝ} (hg : ContDiffAt ℝ 2 g 0)
    (h0 : g 0 = 0) (hd : fderiv ℝ g 0 = 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ x ∈ ball (0 : E2) R,
      g x = ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ g) (t • x) x x := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hg.eventually (by norm_num))
  refine ⟨R, hR, fun x hx => morse_taylor_integral (fun t ht => hsub ?_) h0 hd⟩
  exact ((convex_ball (0 : E2) R).starConvex (mem_ball_self hR)).smul_mem hx ht.1 ht.2

/-- The completion-of-squares identity used in `lem:morse-coords`. -/
theorem morse_complete_square (a b d u v : ℝ) (ha : a ≠ 0) :
    a * u ^ 2 + 2 * b * u * v + d * v ^ 2 =
      a * (u + b / a * v) ^ 2 + (d - b ^ 2 / a) * v ^ 2 := by
  field_simp
  ring

/-- The Schur complement in `lem:morse-coords` is nonzero if the symmetric
coefficient matrix has nonzero determinant and its first pivot is nonzero. -/
theorem morse_schur_ne_zero {a b d : ℝ} (ha : a ≠ 0) (hdet : a * d - b ^ 2 ≠ 0) :
    d - b ^ 2 / a ≠ 0 := by
  intro h
  apply hdet
  field_simp at h
  nlinarith

/-- The square-root coordinate map in the completion-of-squares step of
`lem:morse-coords`, before a possible interchange of its two coordinates. -/
def morseSquareChart (a b d : E2 → ℝ) (x : E2) : E2 :=
  WithLp.toLp 2 ![Real.sqrt |a x| * (x 0 + b x / a x * x 1),
    Real.sqrt |d x - b x ^ 2 / a x| * x 1]

/-- The raw square-root chart for `lem:morse-coords` fixes the origin. -/
theorem morseSquareChart_zero (a b d : E2 → ℝ) : morseSquareChart a b d 0 = 0 := by
  ext i
  fin_cases i <;> simp [morseSquareChart]

private lemma sign_mul_sqrt_sq (a u : ℝ) :
    Real.sign a * (Real.sqrt |a| * u) ^ 2 = a * u ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (abs_nonneg a)]
  rcases lt_trichotomy a 0 with h | rfl | h
  · simp [Real.sign_of_neg h, abs_of_neg h]
  · simp
  · simp [Real.sign_of_pos h, abs_of_pos h]

/-- Exact signed normal form for the explicit square-root chart in
`lem:morse-coords`. The signs can subsequently be matched with the Morse index. -/
theorem morseSquareChart_identity (a b d : E2 → ℝ) (x : E2) (ha : a x ≠ 0) :
    a x * x 0 ^ 2 + 2 * b x * x 0 * x 1 + d x * x 1 ^ 2 =
      Real.sign (a x) * (morseSquareChart a b d x 0) ^ 2 +
      Real.sign (d x - b x ^ 2 / a x) * (morseSquareChart a b d x 1) ^ 2 := by
  simp only [morseSquareChart, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [sign_mul_sqrt_sq, sign_mul_sqrt_sq]
  exact morse_complete_square _ _ _ _ _ ha

/-- The explicit square-root chart in `lem:morse-coords` is C¹ near the origin
when its coefficients are C¹ and both pivots there are nonzero. This is the
finite-regularity step: C¹ pending the user's wording decision. -/
theorem contDiffAt_morseSquareChart {a b d : E2 → ℝ}
    (ha : ContDiffAt ℝ 1 a 0) (hb : ContDiffAt ℝ 1 b 0) (hd : ContDiffAt ℝ 1 d 0)
    (ha0 : a 0 ≠ 0) (hs0 : d 0 - b 0 ^ 2 / a 0 ≠ 0) :
    ContDiffAt ℝ 1 (morseSquareChart a b d) 0 := by
  have haS := (ha.abs ha0).sqrt (abs_ne_zero.mpr ha0)
  have hs := hd.sub ((hb.pow 2).div ha ha0)
  have hsS := (hs.abs hs0).sqrt (abs_ne_zero.mpr hs0)
  apply (contDiffAt_piLp 2).mpr
  intro i
  fin_cases i
  · exact haS.mul ((contDiffAt_piLp_apply 2).add
      ((hb.div ha ha0).mul (contDiffAt_piLp_apply 2)))
  · exact hsS.mul (contDiffAt_piLp_apply 2)

set_option maxHeartbeats 800000 in
-- Allow room for elaborating the operator-valued parameter integral and its derivative.
private theorem contDiffAt_weighted_radial_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {H : E → F} (hH : ContDiffAt ℝ 1 H 0) :
    ContDiffAt ℝ 1 (fun x : E => ∫ t in (0 : ℝ)..1, (1 - t) • H (t • x)) 0 := by
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp (hH.eventually (by norm_num))
  have hr : 0 < R / 2 := half_pos hR
  have hreg (x : E) (hx : x ∈ closedBall (0 : E) (R / 2)) :
      ContDiffAt ℝ 1 H x :=
    hsub ((closedBall_subset_ball (half_lt_self hR)) hx)
  have hregD (x : E) (hx : x ∈ closedBall (0 : E) (R / 2)) :
      ContinuousAt (fderiv ℝ H) x :=
    ((hreg x hx).fderiv_right (m := 0) (by norm_num)).continuousAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) (R / 2)).exists_bound_of_continuousOn
    (fun x hx => (hregD x hx).continuousWithinAt)
  have hrad {x : E} (hx : x ∈ closedBall (0 : E) (R / 2))
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • x ∈ closedBall (0 : E) (R / 2) :=
    ((convex_closedBall (0 : E) (R / 2)).starConvex
      (mem_closedBall_self hr.le)).smul_mem hx ht.1 ht.2
  let D : E → ℝ → E →L[ℝ] F := fun x t => (t * (1 - t)) • fderiv ℝ H (t • x)
  have hFc {x : E} (hx : x ∈ closedBall (0 : E) (R / 2)) :
      ContinuousOn (fun t : ℝ => (1 - t) • H (t • x)) (Icc 0 1) := by
    intro t ht
    exact ((continuousAt_const.sub continuousAt_id).smul
      ((hreg _ (hrad hx ht)).continuousAt.comp
        (f := fun s : ℝ => s • x) (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hDc {x : E} (hx : x ∈ closedBall (0 : E) (R / 2)) :
      ContinuousOn (D x) (Icc 0 1) := by
    intro t ht
    exact ((continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).smul
      ((hregD _ (hrad hx ht)).comp
        (f := fun s : ℝ => s • x) (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hDb {x : E} (hx : x ∈ closedBall (0 : E) (R / 2))
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖D x t‖ ≤ C := by
    have ht0 : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
    have ht1 : t * (1 - t) ≤ 1 := by nlinarith [sq_nonneg t]
    calc
      ‖D x t‖ = (t * (1 - t)) * ‖fderiv ℝ H (t • x)‖ := by
        change ‖(t * (1 - t)) • fderiv ℝ H (t • x)‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
      _ ≤ ‖fderiv ℝ H (t • x)‖ := mul_le_of_le_one_left (norm_nonneg _) ht1
      _ ≤ C := hC _ (hrad hx ht)
  have hDF {x : E} (hx : x ∈ closedBall (0 : E) (R / 2))
      {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      HasFDerivAt (fun y : E => (1 - t) • H (t • y)) (D x t) x := by
    convert! (((hreg _ (hrad hx ht)).differentiableAt one_ne_zero).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul t)).const_smul (1 - t) using 1
    simp [D, smul_smul, mul_comm]
  have hIoc {t : ℝ} (ht : t ∈ Ι (0 : ℝ) 1) : t ∈ Icc (0 : ℝ) 1 := by
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa using ht
    exact Ioc_subset_Icc_self ht'
  have hFD {x : E} (hx : x ∈ ball (0 : E) (R / 2)) :
      HasFDerivAt (fun y : E => ∫ t in (0 : ℝ)..1, (1 - t) • H (t • y))
        (∫ t in (0 : ℝ)..1, D x t) x := by
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := ball (0 : E) (R / 2)) (bound := fun _ => C) (isOpen_ball.mem_nhds hx)
    · filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact ((hFc (ball_subset_closedBall hy)).intervalIntegrable_of_Icc
        (by norm_num)).aestronglyMeasurable_restrict_uIoc
    · exact (hFc (ball_subset_closedBall hx)).intervalIntegrable_of_Icc (by norm_num)
    · exact ((hDc (ball_subset_closedBall hx)).intervalIntegrable_of_Icc
        (by norm_num)).aestronglyMeasurable_restrict_uIoc
    · exact Filter.Eventually.of_forall fun t ht x hx => hDb (ball_subset_closedBall hx) (hIoc ht)
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun t ht x hx => hDF (ball_subset_closedBall hx) (hIoc ht)
  have hDC {x : E} (hx : x ∈ ball (0 : E) (R / 2)) :
      ContinuousAt (fun x : E => ∫ t in (0 : ℝ)..1, D x t) x := by
    apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C)
    · filter_upwards [isOpen_ball.mem_nhds hx] with x hx
      exact ((hDc (ball_subset_closedBall hx)).intervalIntegrable_of_Icc
        (by norm_num)).aestronglyMeasurable_restrict_uIoc
    · filter_upwards [isOpen_ball.mem_nhds hx] with x hx
      exact Filter.Eventually.of_forall fun t ht => hDb (ball_subset_closedBall hx) (hIoc ht)
    · exact intervalIntegrable_const
    · apply Filter.Eventually.of_forall
      intro t ht
      have h : ContinuousAt (fderiv ℝ H) (t • x) :=
        hregD _ (hrad (ball_subset_closedBall hx) (hIoc ht))
      have hs : ContinuousAt (fun y : E => t • y) x := by fun_prop
      change ContinuousAt (fun y : E => (t * (1 - t)) • fderiv ℝ H (t • y)) x
      exact (h.comp (f := fun y : E => t • y) hs).const_smul (t * (1 - t))
  exact contDiffAt_succ_iff_hasFDerivAt.mpr
    ⟨fun x => ∫ t in (0 : ℝ)..1, D x t,
      ⟨ball 0 (R / 2), ball_mem_nhds _ hr, fun _ hx => hFD hx⟩,
      contDiffAt_zero.mpr ⟨ball 0 (R / 2), ball_mem_nhds _ hr,
        fun _ hx => (hDC hx).continuousWithinAt⟩⟩

/-- The bilinear coefficient field `B` of `eq:morse-B`. The factor two makes
its value at the origin exactly the Hessian. -/
def morseB (g : E2 → ℝ) (x : E2) : E2 →L[ℝ] E2 →L[ℝ] ℝ :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)

/-- `eq:morse-B` in `lem:morse-coords`: C³ regularity of `g` gives C¹ regularity
of the integral coefficient field. C¹ pending the user's wording decision. -/
theorem contDiffAt_morseB {g : E2 → ℝ} (hg : ContDiffAt ℝ 3 g 0) :
    ContDiffAt ℝ 1 (morseB g) 0 := by
  have hD : ContDiffAt ℝ 2 (fderiv ℝ g) 0 := hg.fderiv_right (by norm_num)
  have hDD : ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ g)) 0 :=
    hD.fderiv_right (by norm_num)
  exact (contDiffAt_weighted_radial_integral hDD).const_smul 2

/-- At the origin the coefficient field in `eq:morse-B` is the Hessian, with
no regularity assumption needed for this evaluation. -/
theorem morseB_zero (g : E2 → ℝ) : morseB g 0 = fderiv ℝ (fderiv ℝ g) 0 := by
  have hi : ∫ t in (0 : ℝ)..1, (1 - t) = (1 / 2 : ℝ) := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => 1) (g := fun t : ℝ => t)
      intervalIntegrable_const (continuous_id.intervalIntegrable 0 1),
      intervalIntegral.integral_const, integral_id]
    norm_num
  have hiB : (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ g) 0) =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ g) 0 := by
    simpa only [hi] using! (intervalIntegral.integral_smul_const
      (a := 0) (b := 1) (μ := volume) (fun t : ℝ => 1 - t) (fderiv ℝ (fderiv ℝ g) 0))
  simp only [morseB, smul_zero, hiB, smul_smul]
  norm_num

/-- Evaluation of the coefficient field in `eq:morse-B` as a scalar integral. -/
theorem morseB_apply {g : E2 → ℝ} {x : E2}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 g (t • x)) (v w : E2) :
    morseB g x v w =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ g) (t • x) v w := by
  have hc : ContinuousOn
      (fun t : ℝ => (1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) (Icc 0 1) := by
    intro t ht
    have hD : ContDiffAt ℝ 1 (fderiv ℝ g) (t • x) :=
      (hg t ht).fderiv_right (by norm_num)
    have hDD : ContinuousAt (fderiv ℝ (fderiv ℝ g)) (t • x) :=
      (hD.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact ((continuousAt_const.sub continuousAt_id).smul
      (hDD.comp (f := fun s : ℝ => s • x)
        (continuousAt_id.smul continuousAt_const))).continuousWithinAt
  have hi := ContinuousOn.intervalIntegrable_of_Icc
    (E := E2 →L[ℝ] E2 →L[ℝ] ℝ) (μ := volume)
    (a := 0) (b := 1) (by norm_num) (by exact hc)
  have hiv := ContinuousOn.intervalIntegrable_of_Icc
    (E := E2 →L[ℝ] ℝ) (μ := volume)
    (a := 0) (b := 1) (by norm_num)
    (show ContinuousOn (fun t : ℝ => ((1 - t) • fderiv ℝ (fderiv ℝ g) (t • x)) v)
      (Icc 0 1) from hc.clm_apply continuousOn_const)
  simp only [morseB, smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.intervalIntegral_apply hi,
    ContinuousLinearMap.intervalIntegral_apply hiv]
  rfl

/-- The symmetric coefficient field required by `eq:morse-B`. -/
theorem morseB_symmetric {g : E2 → ℝ} {x : E2}
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 g (t • x)) (v w : E2) :
    morseB g x v w = morseB g x w v := by
  rw [morseB_apply hg, morseB_apply hg]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  change (1 - t) * fderiv ℝ (fderiv ℝ g) (t • x) v w =
    (1 - t) * fderiv ℝ (fderiv ℝ g) (t • x) w v
  congr 1
  exact ((hg t ht').isSymmSndFDerivAt (by norm_num)).eq v w

/-- `eq:morse-B` on a ball, including the normalization at zero, symmetry,
and the C¹ coefficient field. C¹ pending the user's wording decision. -/
theorem exists_morseB {g : E2 → ℝ} (hg : ContDiffAt ℝ 3 g 0)
    (h0 : g 0 = 0) (hd : fderiv ℝ g 0 = 0) :
    ∃ R : ℝ, 0 < R ∧ ContDiffOn ℝ 1 (morseB g) (ball 0 R) ∧
      morseB g 0 = fderiv ℝ (fderiv ℝ g) 0 ∧
      ∀ x ∈ ball (0 : E2) R,
        g x = (1 / 2 : ℝ) * morseB g x x x ∧
        ∀ v w : E2, morseB g x v w = morseB g x w v := by
  have he := ((hg.of_le (by norm_num) : ContDiffAt ℝ 2 g 0).eventually (by norm_num)).and
    ((contDiffAt_morseB hg).eventually (by norm_num))
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨R, hR, fun x hx => (hsub hx).2.contDiffWithinAt, morseB_zero g, ?_⟩
  intro x hx
  have hrad (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 2 g (t • x) :=
    (hsub (((convex_ball (0 : E2) R).starConvex (mem_ball_self hR)).smul_mem hx ht.1 ht.2)).1
  refine ⟨?_, morseB_symmetric hrad⟩
  rw [morseB_apply hrad, ← morse_taylor_integral hrad h0 hd]
  ring

private def morseSquareLinear (a b d : ℝ) : E2 →L[ℝ] E2 :=
  LinearMap.toContinuousLinearMap
    { toFun := morseSquareChart (fun _ => a) (fun _ => b) (fun _ => d)
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp [morseSquareChart] <;> ring
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp [morseSquareChart] <;> ring }

set_option maxHeartbeats 800000 in
-- Allow room for the Euclidean operator types in the coordinate derivative calculation.
private theorem morseSquareChart_hasFDerivAt {a b d : E2 → ℝ}
    (ha : ContDiffAt ℝ 1 a 0) (hb : ContDiffAt ℝ 1 b 0) (hd : ContDiffAt ℝ 1 d 0)
    (ha0 : a 0 ≠ 0) (hs0 : d 0 - b 0 ^ 2 / a 0 ≠ 0) :
    HasFDerivAt (morseSquareChart a b d) (morseSquareLinear (a 0) (b 0) (d 0)) 0 := by
  have haS := ((ha.abs ha0).sqrt (abs_ne_zero.mpr ha0)).differentiableAt one_ne_zero
  have hs := hd.sub ((hb.pow 2).div ha ha0)
  have hsS := ((hs.abs hs0).sqrt (abs_ne_zero.mpr hs0)).differentiableAt one_ne_zero
  have hbA := (hb.div ha ha0).differentiableAt one_ne_zero
  have h0 := PiLp.hasFDerivAt_apply 2 (𝕜 := ℝ) (0 : E2) (0 : Fin 2)
  have h1 := PiLp.hasFDerivAt_apply 2 (𝕜 := ℝ) (0 : E2) (1 : Fin 2)
  rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_piLp]
  intro i
  fin_cases i
  · convert! (haS.hasFDerivAt.mul (h0.add (hbA.hasFDerivAt.mul h1))).hasFDerivWithinAt using 1
    ext v
    simp [morseSquareLinear, morseSquareChart]
    ring
  · convert! (hsS.hasFDerivAt.mul h1).hasFDerivWithinAt using 1
    ext v
    simp [morseSquareLinear, morseSquareChart]

private theorem morseSquareLinear_injective {a b d : ℝ}
    (ha : a ≠ 0) (hs : d - b ^ 2 / a ≠ 0) :
    Function.Injective (morseSquareLinear a b d) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have h0 := congrArg (fun y : E2 => y 0) hx
  have h1 := congrArg (fun y : E2 => y 1) hx
  have haS : Real.sqrt |a| ≠ 0 := Real.sqrt_ne_zero'.mpr (abs_pos.mpr ha)
  have hsS : Real.sqrt |d - b ^ 2 / a| ≠ 0 := Real.sqrt_ne_zero'.mpr (abs_pos.mpr hs)
  change Real.sqrt |a| * (x 0 + b / a * x 1) = 0 at h0
  change Real.sqrt |d - b ^ 2 / a| * x 1 = 0 at h1
  have hx1 : x 1 = 0 := (mul_eq_zero.mp h1).resolve_left hsS
  have hx0 : x 0 = 0 := by simpa [hx1] using (mul_eq_zero.mp h0).resolve_left haS
  ext i
  fin_cases i <;> assumption

/-- The completion-of-squares map in `lem:morse-coords` supplies a local
C¹ diffeomorphism whenever its coefficient functions are C¹ and its two pivots
at the origin are nonzero. C¹ pending the user's wording decision. -/
theorem exists_morseSquareChart {a b d : E2 → ℝ}
    (ha : ContDiffAt ℝ 1 a 0) (hb : ContDiffAt ℝ 1 b 0) (hd : ContDiffAt ℝ 1 d 0)
    (ha0 : a 0 ≠ 0) (hs0 : d 0 - b 0 ^ 2 / a 0 ≠ 0) :
    ∃ e : OpenPartialHomeomorph E2 E2, (0 : E2) ∈ e.source ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (e : E2 → E2) = morseSquareChart a b d := by
  let L := morseSquareLinear (a 0) (b 0) (d 0)
  have hL : Function.Bijective L :=
    ⟨morseSquareLinear_injective ha0 hs0,
      LinearMap.surjective_of_injective (morseSquareLinear_injective ha0 hs0)⟩
  let A : E2 ≃L[ℝ] E2 := (LinearEquiv.ofBijective L.toLinearMap hL).toContinuousLinearEquiv
  have hC := contDiffAt_morseSquareChart ha hb hd ha0 hs0
  have hD : HasFDerivAt (morseSquareChart a b d) (A : E2 →L[ℝ] E2) 0 :=
    morseSquareChart_hasFDerivAt ha hb hd ha0 hs0
  let e := hC.toOpenPartialHomeomorph (morseSquareChart a b d) hD one_ne_zero
  have hsource : (0 : E2) ∈ e.source := hC.mem_toOpenPartialHomeomorph_source hD one_ne_zero
  have he0 : e 0 = 0 := morseSquareChart_zero a b d
  have hiC : ContDiffAt ℝ 1 e.symm (e 0) := by
    apply e.contDiffAt_symm (e.map_source hsource)
    · simpa only [e.left_inv hsource] using! hD
    · simpa only [e.left_inv hsource] using! hC
  refine ⟨e.restrContDiff ℝ 1 (by norm_num), ?_, he0,
    e.contDiffOn_restrContDiff_source ℝ (by norm_num),
    e.contDiffOn_restrContDiff_target ℝ (by norm_num), rfl⟩
  exact ⟨hsource, hC, hiC⟩

/-- A symmetric bilinear form in the plane has the coefficient expansion used
in the completion-of-squares step of `lem:morse-coords`. -/
theorem morse_bilinear_expansion (B : E2 →L[ℝ] E2 →L[ℝ] ℝ)
    (hB : ∀ v w : E2, B v w = B w v) (x : E2) :
    B x x = B (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) * x 0 ^ 2 +
      2 * B (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) * x 0 * x 1 +
      B (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) * x 1 ^ 2 := by
  have hx : x = x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1 := by
    ext i
    fin_cases i <;> simp
  calc
    B x x = B (x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1)
        (x 0 • EuclideanSpace.single 0 1 + x 1 • EuclideanSpace.single 1 1) := by
      exact congrArg₂ (fun v w : E2 => B v w) hx hx
    _ = _ := by
      simp only [map_add, map_smul, add_apply,
        smul_apply, smul_eq_mul]
      rw [hB (EuclideanSpace.single 1 1) (EuclideanSpace.single 0 1)]
      ring

end LiquidDrop
