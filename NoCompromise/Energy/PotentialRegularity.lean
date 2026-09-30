module

public import NoCompromise.Variation.CoulombSingle
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
# Differentiability of the Newtonian potential

Smooth regularizations of the Newtonian kernel justify its gradient formula at
points inside as well as outside the source set.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace

namespace LiquidDrop

set_option maxSynthPendingDepth 8

local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ

/-- A smooth regularization of the three-dimensional Newtonian kernel. -/
def regularizedNewtonKernel (ε : ℝ) (z : E₃) : ℝ :=
  (Real.sqrt (‖z‖ ^ 2 + ε ^ 2))⁻¹

/-- The genuine derivative of the regularized kernel. -/
def regularizedNewtonDerivative (ε : ℝ) (z : E₃) : D₃ :=
  -((Real.sqrt (‖z‖ ^ 2 + ε ^ 2)) ^ 3)⁻¹ • innerSL ℝ z

/-- The limiting derivative kernel, with the total convention zero at the origin. -/
def newtonDerivativeKernel (z : E₃) : D₃ :=
  -(‖z‖ ^ 3)⁻¹ • innerSL ℝ z

lemma regularizedNewton_sqrt_bounds {ε : ℝ} (hε : 0 < ε) (z : E₃) :
    0 < Real.sqrt (‖z‖ ^ 2 + ε ^ 2) ∧
      ‖z‖ ≤ Real.sqrt (‖z‖ ^ 2 + ε ^ 2) ∧
      ε ≤ Real.sqrt (‖z‖ ^ 2 + ε ^ 2) := by
  have hpos : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hs := Real.sq_sqrt hpos.le
  have hn := Real.sqrt_nonneg (‖z‖ ^ 2 + ε ^ 2)
  refine ⟨Real.sqrt_pos.mpr hpos, ?_, ?_⟩ <;> nlinarith [norm_nonneg z, sq_nonneg ε]

lemma hasFDerivAt_regularizedNewtonKernel {ε : ℝ} (hε : 0 < ε) (z : E₃) :
    HasFDerivAt (regularizedNewtonKernel ε) (regularizedNewtonDerivative ε z) z := by
  have hpos : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have hs := (hasDerivAt_inv (Real.sqrt_pos.mpr hpos).ne').comp_hasFDerivAt z
    (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const (ε ^ 2)).sqrt hpos.ne')
  convert! hs using 1
  ext v
  simp only [regularizedNewtonDerivative, smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp
  ring

lemma continuous_regularizedNewtonKernel {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedNewtonKernel ε) :=
  continuous_iff_continuousAt.mpr fun z => (hasFDerivAt_regularizedNewtonKernel hε z).continuousAt

lemma continuous_regularizedNewtonDerivative {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedNewtonDerivative ε) := by
  have hpos (z : E₃) : Real.sqrt (‖z‖ ^ 2 + ε ^ 2) ≠ 0 :=
    (regularizedNewton_sqrt_bounds hε z).1.ne'
  exact (((continuous_norm.pow 2).add continuous_const).sqrt.pow 3).inv₀
    (fun z => pow_ne_zero 3 (hpos z)) |>.neg |>.smul (innerSL ℝ).continuous

lemma measurable_newtonDerivativeKernel : Measurable newtonDerivativeKernel := by
  exact (((continuous_norm.pow 3).measurable.inv).neg).smul (innerSL ℝ).continuous.measurable

lemma norm_regularizedNewtonKernel_le {ε : ℝ} (hε : 0 < ε) (z : E₃) :
    ‖regularizedNewtonKernel ε z‖ ≤ ε⁻¹ := by
  have hs := regularizedNewton_sqrt_bounds hε z
  rw [regularizedNewtonKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
  exact inv_anti₀ hε hs.2.2

lemma norm_newtonDerivativeKernel (z : E₃) :
    ‖newtonDerivativeKernel z‖ = (‖z‖ ^ 2)⁻¹ := by
  by_cases hz : z = 0
  · simp [newtonDerivativeKernel, hz]
  have hn := norm_ne_zero_iff.mpr hz
  rw [newtonDerivativeKernel, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (norm_nonneg _) _)), innerSL_apply_norm]
  field_simp

lemma norm_regularizedNewtonDerivative_le {ε : ℝ} (hε : 0 < ε) (z : E₃) :
    ‖regularizedNewtonDerivative ε z‖ ≤ ε⁻¹ ^ 2 ∧
      ‖regularizedNewtonDerivative ε z‖ ≤ (‖z‖ ^ 2)⁻¹ := by
  have hs := regularizedNewton_sqrt_bounds hε z
  let s := Real.sqrt (‖z‖ ^ 2 + ε ^ 2)
  have hs0 : 0 < s := hs.1
  have hnorm : ‖regularizedNewtonDerivative ε z‖ = ‖z‖ / s ^ 3 := by
    rw [regularizedNewtonDerivative, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.mpr (pow_pos hs0 3)), innerSL_apply_norm]
    rw [div_eq_mul_inv, mul_comm]
  rw [hnorm]
  have hsmall : ‖z‖ / s ^ 3 ≤ (s ^ 2)⁻¹ := by
    calc
      _ ≤ s / s ^ 3 := div_le_div_of_nonneg_right hs.2.1 (by positivity)
      _ = _ := by field_simp
  constructor
  · calc
      _ ≤ (s ^ 2)⁻¹ := hsmall
      _ ≤ (ε ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos hε) (by nlinarith [hs.2.2])
      _ = _ := (inv_pow ε 2).symm
  · by_cases hz : z = 0
    · simp [hz]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    calc
      _ ≤ (s ^ 2)⁻¹ := hsmall
      _ ≤ (‖z‖ ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos hn) (by nlinarith [hs.2.1])

/-- The potential of the smooth regularized kernel. -/
def regularizedNewtonPotential (ε : ℝ) (E : Set E₃) (x : E₃) : ℝ :=
  ∫ y in E, regularizedNewtonKernel ε (x - y)

/-- The derivative integral of the regularized potential. -/
def regularizedNewtonPotentialDerivative (ε : ℝ) (E : Set E₃) (x : E₃) : D₃ :=
  ∫ y in E, regularizedNewtonDerivative ε (x - y)

/-- The absolutely convergent derivative integral of the Newtonian potential. -/
def newtonPotentialDerivative (E : Set E₃) (x : E₃) : D₃ :=
  ∫ y in E, newtonDerivativeKernel (x - y)

lemma integrableOn_newtonDerivativeKernel (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    IntegrableOn (fun y => newtonDerivativeKernel (x - y)) E := by
  apply (integrableOn_inv_norm_sub_sq E hE x).mono'
    (measurable_newtonDerivativeKernel.comp
      (continuous_const.sub continuous_id).measurable).aestronglyMeasurable
  exact Eventually.of_forall fun y => (norm_newtonDerivativeKernel (x - y)).le

lemma integrableOn_regularizedNewtonDerivative {ε : ℝ} (hε : 0 < ε)
    (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    IntegrableOn (fun y => regularizedNewtonDerivative ε (x - y)) E := by
  have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hE⟩
  exact (integrable_const (ε⁻¹ ^ 2)).mono'
    ((continuous_regularizedNewtonDerivative hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => (norm_regularizedNewtonDerivative_le hε (x - y)).1)

lemma hasFDerivAt_regularizedNewtonPotential {ε : ℝ} (hε : 0 < ε)
    (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    HasFDerivAt (regularizedNewtonPotential ε E)
      (regularizedNewtonPotentialDerivative ε E x) x := by
  have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hE⟩
  unfold regularizedNewtonPotential regularizedNewtonPotentialDerivative
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun a y => regularizedNewtonDerivative ε (a - y)) (bound := fun _ => ε⁻¹ ^ 2)
    (Filter.univ_mem)
  · exact Eventually.of_forall fun a => ((continuous_regularizedNewtonKernel hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact (integrable_const ε⁻¹).mono'
      ((continuous_regularizedNewtonKernel hε).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun y => norm_regularizedNewtonKernel_le hε (x - y))
  · exact ((continuous_regularizedNewtonDerivative hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun y a _ => (norm_regularizedNewtonDerivative_le hε (a - y)).1
  · exact integrable_const _
  · exact Eventually.of_forall fun y a _ => by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
        (hasFDerivAt_regularizedNewtonKernel hε (a - y)).comp a ((hasFDerivAt_id a).sub_const y)

lemma continuous_regularizedNewtonPotentialDerivative {ε : ℝ} (hε : 0 < ε)
    (E : Set E₃) (hE : volume E < ∞) :
    Continuous (regularizedNewtonPotentialDerivative ε E) := by
  have : IsFiniteMeasure (volume.restrict E) := ⟨by simpa using hE⟩
  apply continuous_of_dominated (bound := fun _ => ε⁻¹ ^ 2)
  · exact fun x => ((continuous_regularizedNewtonDerivative hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact fun x => Eventually.of_forall fun y =>
      (norm_regularizedNewtonDerivative_le hε (x - y)).1
  · exact integrable_const _
  · exact Eventually.of_forall fun y => (continuous_regularizedNewtonDerivative hε).comp
      (continuous_id.sub continuous_const)

lemma tendsto_regularizedNewtonKernel {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    {z : E₃} (hz : z ≠ 0) :
    Tendsto (fun j => regularizedNewtonKernel (ε j) z) atTop (𝓝 ‖z‖⁻¹) := by
  have hs : Tendsto (fun j => Real.sqrt (‖z‖ ^ 2 + ε j ^ 2)) atTop (𝓝 ‖z‖) := by
    convert! ((tendsto_const_nhds (x := ‖z‖ ^ 2)).add (hε.pow 2)).sqrt using 1
    simp [Real.sqrt_sq (norm_nonneg z)]
  exact hs.inv₀ (norm_ne_zero_iff.mpr hz)

lemma tendsto_regularizedNewtonDerivative {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (z : E₃) :
    Tendsto (fun j => regularizedNewtonDerivative (ε j) z) atTop
      (𝓝 (newtonDerivativeKernel z)) := by
  by_cases hz : z = 0
  · simp [regularizedNewtonDerivative, newtonDerivativeKernel, hz]
  have h := ((tendsto_regularizedNewtonKernel hε hz).pow 3).neg.smul
    (tendsto_const_nhds (x := innerSL ℝ z))
  simpa only [regularizedNewtonDerivative, regularizedNewtonKernel, newtonDerivativeKernel,
    inv_pow] using h

/-- The derivative kernels converge in L¹ on each fixed ball. -/
lemma tendsto_integral_regularizedNewtonDerivative_error {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j) (R : ℝ) :
    Tendsto (fun j => ∫ z in ball (0 : E₃) R,
      ‖regularizedNewtonDerivative (ε j) z - newtonDerivativeKernel z‖) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (ball (0 : E₃) R)) (fun z : E₃ => 2 * (‖z‖ ^ 2)⁻¹)
    (F := fun j z => ‖regularizedNewtonDerivative (ε j) z - newtonDerivativeKernel z‖)
    (f := fun _ => (0 : ℝ))
  apply (by simpa only [integral_zero] using h)
  · exact fun j => (((continuous_regularizedNewtonDerivative (hεpos j)).measurable.sub
      measurable_newtonDerivativeKernel).norm).aestronglyMeasurable
  · exact (integrableOn_inv_norm_sq_ball R).const_mul 2
  · intro j
    apply Eventually.of_forall
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ ‖regularizedNewtonDerivative (ε j) z‖ + ‖newtonDerivativeKernel z‖ :=
        norm_sub_le _ _
      _ ≤ (‖z‖ ^ 2)⁻¹ + (‖z‖ ^ 2)⁻¹ := add_le_add
        (norm_regularizedNewtonDerivative_le (hεpos j) z).2 (norm_newtonDerivativeKernel z).le
      _ = _ := by ring
  · exact Eventually.of_forall fun z => by
      simpa only [sub_self, norm_zero] using
        ((tendsto_regularizedNewtonDerivative hε z).sub
          (tendsto_const_nhds (x := newtonDerivativeKernel z))).norm

/-- Translation bounds a convolution integral by the L¹ norm on a containing ball. -/
lemma norm_setIntegral_sub_le_integral_ball {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {H : E₃ → F} {R : ℝ} (hH : IntegrableOn H (ball 0 R))
    {E : Set E₃} (x : E₃) (hE : ∀ y ∈ E, x - y ∈ ball 0 R) :
    ‖∫ y in E, H (x - y)‖ ≤ ∫ z in ball (0 : E₃) R, ‖H z‖ := by
  let T := (fun y : E₃ => x - y) ⁻¹' ball 0 R
  have hi : IntegrableOn (fun y => H (x - y)) T :=
    ((volume.measurePreserving_sub_left x).integrableOn_comp_preimage
      (MeasurableEquiv.subLeft x).measurableEmbedding).mpr hH
  calc
    _ ≤ ∫ y in E, ‖H (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in T, ‖H (x - y)‖ := setIntegral_mono_set hi.norm
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hE)
    _ = _ := ((volume.measurePreserving_sub_left x).restrict_preimage
      measurableSet_ball).integral_comp
        (MeasurableEquiv.subLeft x).measurableEmbedding (fun z => ‖H z‖)

lemma integrableOn_regularizedNewtonDerivative_error {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    IntegrableOn (fun z => regularizedNewtonDerivative ε z - newtonDerivativeKernel z)
      (ball 0 R) := by
  apply ((integrableOn_inv_norm_sq_ball R).const_mul 2).mono'
    (((continuous_regularizedNewtonDerivative hε).measurable.sub
      measurable_newtonDerivativeKernel).aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  calc
    _ ≤ ‖regularizedNewtonDerivative ε z‖ + ‖newtonDerivativeKernel z‖ := norm_sub_le _ _
    _ ≤ (‖z‖ ^ 2)⁻¹ + (‖z‖ ^ 2)⁻¹ := add_le_add
      (norm_regularizedNewtonDerivative_le hε z).2 (norm_newtonDerivativeKernel z).le
    _ = _ := by ring

/-- For a bounded source, the potential derivatives converge uniformly on every bounded ball. -/
lemma tendstoUniformlyOn_regularizedNewtonPotentialDerivative {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {E : Set E₃} (hEb : Bornology.IsBounded E) (S : ℝ) :
    TendstoUniformlyOn (fun j => regularizedNewtonPotentialDerivative (ε j) E)
      (newtonPotentialDerivative E) atTop (ball 0 S) := by
  obtain ⟨M, hM⟩ := hEb.exists_norm_le
  let R := S + M + 1
  have hfin : volume E < ∞ := hEb.measure_lt_top
  have hbound (j : ℕ) (x : E₃) (hx : x ∈ ball 0 S) :
      ‖regularizedNewtonPotentialDerivative (ε j) E x - newtonPotentialDerivative E x‖ ≤
        ∫ z in ball (0 : E₃) R,
          ‖regularizedNewtonDerivative (ε j) z - newtonDerivativeKernel z‖ := by
    rw [regularizedNewtonPotentialDerivative, newtonPotentialDerivative,
      ← integral_sub (integrableOn_regularizedNewtonDerivative (hεpos j) E hfin x)
        (integrableOn_newtonDerivativeKernel E hfin x)]
    apply norm_setIntegral_sub_le_integral_ball
      (integrableOn_regularizedNewtonDerivative_error (hεpos j) R) x
    intro y hy
    have hxn : ‖x‖ < S := by simpa only [mem_ball, dist_zero_right] using hx
    have hyn := hM y hy
    have hxy := norm_sub_le x y
    rw [mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hlim := tendsto_integral_regularizedNewtonDerivative_error hε hεpos R
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with j hj x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound j x hx).trans_lt hj

/-- The potentials converge pointwise to the actual extended-real potential's real value. -/
lemma tendsto_regularizedNewtonPotential {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    Tendsto (fun j => regularizedNewtonPotential (ε j) E x) atTop
      (𝓝 (coulombPotential E x).toReal) := by
  rw [coulombPotential_toReal E hE x]
  have hne : ∀ᵐ y : E₃ ∂volume.restrict E, x - y ≠ 0 := by
    have h : ∀ᵐ y : E₃ ∂volume, y ≠ x := by simp [ae_iff]
    filter_upwards [ae_restrict_of_ae (s := E) h] with y hy
    exact sub_ne_zero.mpr hy.symm
  apply tendsto_integral_of_dominated_convergence (fun y : E₃ => ‖x - y‖⁻¹)
  · exact fun j => ((continuous_regularizedNewtonKernel (hεpos j)).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact integrableOn_coulombKernel E hE x
  · intro j
    filter_upwards [hne] with y hy
    have hs := regularizedNewton_sqrt_bounds (hεpos j) (x - y)
    rw [regularizedNewtonKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
    exact inv_anti₀ (norm_pos_iff.mpr hy) hs.2.1
  · exact hne.mono fun y hy => tendsto_regularizedNewtonKernel hε hy

/-- Differentiability of the Newtonian potential, including points inside a bounded source. -/
theorem hasFDerivAt_coulombPotential_of_isBounded {E : Set E₃}
    (hEb : Bornology.IsBounded E) (x : E₃) :
    HasFDerivAt (fun a => (coulombPotential E a).toReal) (newtonPotentialDerivative E x) x := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  apply hasFDerivAt_of_tendstoUniformlyOn (s := ball 0 (‖x‖ + 1)) isOpen_ball
    (tendstoUniformlyOn_regularizedNewtonPotentialDerivative hε hεpos hEb (‖x‖ + 1))
  · exact fun j a _ => hasFDerivAt_regularizedNewtonPotential (hεpos j) E hEb.measure_lt_top a
  · exact fun a _ => tendsto_regularizedNewtonPotential hε hεpos E hEb.measure_lt_top a
  · simp only [mem_ball, dist_zero_right]
    linarith

/-- The genuine derivative of the bounded-source Newtonian potential is continuous. -/
lemma continuous_newtonPotentialDerivative_of_isBounded {E : Set E₃}
    (hEb : Bornology.IsBounded E) : Continuous (newtonPotentialDerivative E) := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := (tendstoUniformlyOn_regularizedNewtonPotentialDerivative hε hεpos hEb
    (‖x‖ + 1)).continuousOn
    (Eventually.of_forall fun j =>
      (continuous_regularizedNewtonPotentialDerivative
        (hεpos j) E hEb.measure_lt_top).continuousOn).frequently
  apply hc.continuousAt (isOpen_ball.mem_nhds ?_)
  simp only [mem_ball, dist_zero_right]
  linarith

/-- The Newtonian potential of a bounded source is genuinely C¹ on all of space. -/
theorem contDiff_one_coulombPotential_of_isBounded {E : Set E₃}
    (hEb : Bornology.IsBounded E) : ContDiff ℝ 1 (fun x => (coulombPotential E x).toReal) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨newtonPotentialDerivative E, continuous_newtonPotentialDerivative_of_isBounded hEb,
    hasFDerivAt_coulombPotential_of_isBounded hEb⟩

/-- Absolute convergence of the vector-valued Newtonian force kernel. -/
lemma integrableOn_newtonGradientKernel (E : Set E₃) (hE : volume E < ∞) (x : E₃) :
    IntegrableOn (fun y => -(‖x - y‖ ^ 3)⁻¹ • (x - y)) E := by
  have hm : Measurable (fun y : E₃ => -(‖x - y‖ ^ 3)⁻¹ • (x - y)) := by fun_prop
  apply (integrableOn_newtonDerivativeKernel E hE x).norm.mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    simp only [newtonDerivativeKernel, norm_smul, innerSL_apply_norm, le_refl]

/-- The classical Newtonian gradient formula, proved at every point. -/
theorem gradient_coulombPotential_of_isBounded {E : Set E₃}
    (hEb : Bornology.IsBounded E) (x : E₃) :
    gradient (fun a => (coulombPotential E a).toReal) x =
      ∫ y in E, -(‖x - y‖ ^ 3)⁻¹ • (x - y) := by
  apply (InnerProductSpace.toDual ℝ E₃).injective
  rw [toDual_gradient, (hasFDerivAt_coulombPotential_of_isBounded hEb x).fderiv]
  change newtonPotentialDerivative E x = (innerSL ℝ) (∫ y in E,
    -(‖x - y‖ ^ 3)⁻¹ • (x - y))
  rw [← (innerSL ℝ).integral_comp_comm
    (integrableOn_newtonGradientKernel E hEb.measure_lt_top x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by simp [newtonDerivativeKernel]

/-- The explicit vector integral is the actual gradient at every point. -/
theorem hasGradientAt_coulombPotential_of_isBounded {E : Set E₃}
    (hEb : Bornology.IsBounded E) (x : E₃) :
    HasGradientAt (fun a => (coulombPotential E a).toReal)
      (∫ y in E, -(‖x - y‖ ^ 3)⁻¹ • (x - y)) x := by
  rw [← gradient_coulombPotential_of_isBounded hEb x]
  exact (hasFDerivAt_coulombPotential_of_isBounded hEb x).differentiableAt.hasGradientAt

lemma continuous_gradient_coulombPotential_of_isBounded {E : Set E₃}
    (hEb : Bornology.IsBounded E) :
    Continuous (gradient (fun x => (coulombPotential E x).toReal)) := by
  have heq : gradient (fun x => (coulombPotential E x).toReal) =
      (InnerProductSpace.toDual ℝ E₃).symm ∘ newtonPotentialDerivative E := by
    funext x
    exact (hasFDerivAt_coulombPotential_of_isBounded hEb x).hasGradientAt.gradient
  rw [heq]
  exact (InnerProductSpace.toDual ℝ E₃).symm.continuous.comp
    (continuous_newtonPotentialDerivative_of_isBounded hEb)

end LiquidDrop
