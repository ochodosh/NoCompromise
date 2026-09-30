module

public import NoCompromise.Energy.PotentialRegularity
public import NoCompromise.Elliptic.Newtonian

@[expose] public section

/-!
# C¹ regularity of Newtonian potentials of bounded signed densities

The density is only Lebesgue measurable. Compact support and a pointwise bound
justify every integral; differentiability follows by uniform convergence of
regularized derivative kernels in local L¹, with the density bound carried
through the convolution estimates.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "D₃" => E₃ →L[ℝ] ℝ

/-- The absolutely convergent candidate derivative of a signed potential. -/
def scalarNewtonianPotentialDerivative (f : E₃ → ℝ) (x : E₃) : D₃ :=
  ∫ y, f y • newtonDerivativeKernel (x - y)

/-- Smooth-kernel approximation of a signed potential. -/
def regularizedScalarNewtonPotential (ε : ℝ) (f : E₃ → ℝ) (x : E₃) : ℝ :=
  ∫ y, f y * regularizedNewtonKernel ε (x - y)

/-- Derivative integral of the smooth-kernel approximation. -/
def regularizedScalarNewtonPotentialDerivative (ε : ℝ) (f : E₃ → ℝ) (x : E₃) : D₃ :=
  ∫ y, f y • regularizedNewtonDerivative ε (x - y)

lemma integrable_scalarNewtonianPotentialDerivative_integrand {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ x, ‖f x‖ ≤ B) (x : E₃) :
    Integrable (fun y => f y • newtonDerivativeKernel (x - y)) := by
  have hs : Function.support (fun y => f y • newtonDerivativeKernel (x - y)) ⊆
      tsupport f := by
    intro y hy
    by_contra hn
    exact hy (by simp [image_eq_zero_of_notMem_tsupport hn])
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  apply ((integrableOn_inv_norm_sub_sq (tsupport f) hcf.measure_lt_top x).const_mul B).mono'
    (hf.smul ((measurable_newtonDerivativeKernel.comp
      (continuous_const.sub continuous_id).measurable).aestronglyMeasurable)).restrict
  exact Eventually.of_forall fun y => by
    change ‖f y • newtonDerivativeKernel (x - y)‖ ≤ B * (‖x - y‖ ^ 2)⁻¹
    rw [norm_smul, norm_newtonDerivativeKernel]
    exact mul_le_mul_of_nonneg_right (hB y) (by positivity)

lemma integrable_regularizedScalarNewtonPotential_integrand {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun y => f y * regularizedNewtonKernel ε (x - y)) := by
  apply (hf.norm.mul_const ε⁻¹).mono'
    (hf.aestronglyMeasurable.mul ((continuous_regularizedNewtonKernel hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun y => by
    change ‖f y * regularizedNewtonKernel ε (x - y)‖ ≤ ‖f y‖ * ε⁻¹
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_regularizedNewtonKernel_le hε _) (norm_nonneg _)

lemma integrable_regularizedScalarNewtonPotentialDerivative_integrand {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    Integrable (fun y => f y • regularizedNewtonDerivative ε (x - y)) := by
  apply (hf.norm.mul_const (ε⁻¹ ^ 2)).mono'
    (hf.aestronglyMeasurable.smul ((continuous_regularizedNewtonDerivative hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall fun y => by
    change ‖f y • regularizedNewtonDerivative ε (x - y)‖ ≤ ‖f y‖ * ε⁻¹ ^ 2
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_regularizedNewtonDerivative_le hε _).1 (norm_nonneg _)

lemma hasFDerivAt_regularizedScalarNewtonPotential {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) (x : E₃) :
    HasFDerivAt (regularizedScalarNewtonPotential ε f)
      (regularizedScalarNewtonPotentialDerivative ε f x) x := by
  unfold regularizedScalarNewtonPotential regularizedScalarNewtonPotentialDerivative
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (F' := fun a y => f y • regularizedNewtonDerivative ε (a - y))
    (bound := fun y => ‖f y‖ * ε⁻¹ ^ 2) (Filter.univ_mem)
  · exact Eventually.of_forall fun a => hf.aestronglyMeasurable.mul
      (((continuous_regularizedNewtonKernel hε).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact integrable_regularizedScalarNewtonPotential_integrand hε hf x
  · exact hf.aestronglyMeasurable.smul (((continuous_regularizedNewtonDerivative hε).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact Eventually.of_forall fun y a _ => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_regularizedNewtonDerivative_le hε _).1 (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact Eventually.of_forall fun y a _ => by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq,
        Pi.smul_apply, smul_eq_mul] using!
        ((hasFDerivAt_regularizedNewtonKernel hε (a - y)).comp a
          ((hasFDerivAt_id a).sub_const y)).const_smul (f y)

lemma continuous_regularizedScalarNewtonPotentialDerivative {ε : ℝ} (hε : 0 < ε)
    {f : E₃ → ℝ} (hf : Integrable f) :
    Continuous (regularizedScalarNewtonPotentialDerivative ε f) := by
  apply continuous_of_dominated (bound := fun y => ‖f y‖ * ε⁻¹ ^ 2)
  · exact fun x => hf.aestronglyMeasurable.smul
      (((continuous_regularizedNewtonDerivative hε).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact fun x => Eventually.of_forall fun y => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_regularizedNewtonDerivative_le hε _).1 (norm_nonneg _)
  · exact hf.norm.mul_const _
  · exact Eventually.of_forall fun y =>
      ((continuous_regularizedNewtonDerivative hε).comp
        (continuous_id.sub continuous_const)).const_smul (f y)

/-- A bounded scalar weight multiplies the translated L¹-kernel bound by its bound. -/
lemma norm_integral_bounded_weight_sub_le_integral_ball
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₃ → ℝ} {B R : ℝ} (hf : AEStronglyMeasurable f volume)
    (hB : ∀ y, ‖f y‖ ≤ B) {H : E₃ → F}
    (hH : IntegrableOn H (ball 0 R)) (x : E₃)
    (hs : ∀ y ∈ tsupport f, x - y ∈ ball 0 R) :
    ‖∫ y, f y • H (x - y)‖ ≤ B * ∫ z in ball (0 : E₃) R, ‖H z‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  let T := (fun y : E₃ => x - y) ⁻¹' ball 0 R
  have hiT : IntegrableOn (fun y => H (x - y)) T :=
    ((volume.measurePreserving_sub_left x).integrableOn_comp_preimage
      (MeasurableEquiv.subLeft x).measurableEmbedding).mpr hH
  have hi : IntegrableOn (fun y => H (x - y)) (tsupport f) := hiT.mono_set hs
  have hw : IntegrableOn (fun y => f y • H (x - y)) (tsupport f) :=
    (hi.norm.const_mul B).mono' (hf.restrict.smul hi.aestronglyMeasurable)
      (Eventually.of_forall fun y => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := tsupport f) (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])]
  calc
    _ ≤ ∫ y in tsupport f, ‖f y • H (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in tsupport f, B * ‖H (x - y)‖ := integral_mono hw.norm (hi.norm.const_mul B)
      (fun y => by rw [norm_smul]; exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _))
    _ = B * ∫ y in tsupport f, ‖H (x - y)‖ := integral_const_mul _ _
    _ ≤ B * ∫ z in ball (0 : E₃) R, ‖H z‖ := by
      apply mul_le_mul_of_nonneg_left _ hB0
      calc
        _ ≤ ∫ y in T, ‖H (x - y)‖ := setIntegral_mono_set hiT.norm
          (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall hs)
        _ = _ := ((volume.measurePreserving_sub_left x).restrict_preimage
          measurableSet_ball).integral_comp
            (MeasurableEquiv.subLeft x).measurableEmbedding (fun z => ‖H z‖)

/-- The regularized signed-potential derivatives converge uniformly on bounded balls. -/
lemma tendstoUniformlyOn_regularizedScalarNewtonPotentialDerivative {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {f : E₃ → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f volume)
    (hcf : HasCompactSupport f) (hB : ∀ y, ‖f y‖ ≤ B) (S : ℝ) :
    TendstoUniformlyOn (fun j => regularizedScalarNewtonPotentialDerivative (ε j) f)
      (scalarNewtonianPotentialDerivative f) atTop (ball 0 S) := by
  obtain ⟨M, hM⟩ := hcf.isBounded.exists_norm_le
  let R := S + M + 1
  have hfi := integrable_scalarDensity_of_bounded_compact hf hcf hB
  have hbound (j : ℕ) (x : E₃) (hx : x ∈ ball 0 S) :
      ‖regularizedScalarNewtonPotentialDerivative (ε j) f x -
        scalarNewtonianPotentialDerivative f x‖ ≤
      B * ∫ z in ball (0 : E₃) R,
        ‖regularizedNewtonDerivative (ε j) z - newtonDerivativeKernel z‖ := by
    rw [regularizedScalarNewtonPotentialDerivative, scalarNewtonianPotentialDerivative,
      ← integral_sub (integrable_regularizedScalarNewtonPotentialDerivative_integrand
        (hεpos j) hfi x) (integrable_scalarNewtonianPotentialDerivative_integrand hf hcf hB x)]
    simp_rw [← smul_sub]
    apply norm_integral_bounded_weight_sub_le_integral_ball hf hB
      (integrableOn_regularizedNewtonDerivative_error (hεpos j) R) x
    intro y hy
    have hxn : ‖x‖ < S := by simpa only [mem_ball, dist_zero_right] using hx
    have hyn := hM y hy
    have hxy := norm_sub_le x y
    rw [mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  have hlim : Tendsto (fun j => B * ∫ z in ball (0 : E₃) R,
      ‖regularizedNewtonDerivative (ε j) z - newtonDerivativeKernel z‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := B)).mul
      (tendsto_integral_regularizedNewtonDerivative_error hε hεpos R)
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with j hj x hx
  rw [dist_eq_norm, norm_sub_rev]
  exact (hbound j x hx).trans_lt hj

/-- The regularizations converge pointwise to the actual signed potential. -/
lemma tendsto_regularizedScalarNewtonPotential {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {f : E₃ → ℝ} {B : ℝ} (hf : AEStronglyMeasurable f volume)
    (hcf : HasCompactSupport f) (hB : ∀ y, ‖f y‖ ≤ B) (x : E₃) :
    Tendsto (fun j => regularizedScalarNewtonPotential (ε j) f x) atTop
      (𝓝 (scalarNewtonianPotential f x)) := by
  have hne : ∀ᵐ y : E₃ ∂volume, x - y ≠ 0 := by
    have h : ∀ᵐ y : E₃ ∂volume, y ≠ x := by simp [ae_iff]
    exact h.mono fun _ hy => sub_ne_zero.mpr hy.symm
  unfold regularizedScalarNewtonPotential scalarNewtonianPotential
  apply tendsto_integral_of_dominated_convergence (fun y : E₃ => ‖f y / ‖x - y‖‖)
  · exact fun j => hf.mul (((continuous_regularizedNewtonKernel (hεpos j)).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · exact (integrable_newtonianPotential_integrand hf hcf hB x).norm
  · intro j
    filter_upwards [hne] with y hy
    have hs := regularizedNewton_sqrt_bounds (hεpos j) (x - y)
    rw [norm_mul, norm_div, norm_norm, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [regularizedNewtonKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
    exact inv_anti₀ (norm_pos_iff.mpr hy) hs.2.1
  · exact hne.mono fun y hy => by
      simpa only [div_eq_mul_inv] using
        (tendsto_const_nhds (x := f y)).mul (tendsto_regularizedNewtonKernel hε hy)

/-- The actual Fréchet derivative, valid at every point for signed bounded sources. -/
theorem hasFDerivAt_scalarNewtonianPotential {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ y, ‖f y‖ ≤ B) (x : E₃) :
    HasFDerivAt (scalarNewtonianPotential f) (scalarNewtonianPotentialDerivative f x) x := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hfi := integrable_scalarDensity_of_bounded_compact hf hcf hB
  apply hasFDerivAt_of_tendstoUniformlyOn (s := ball 0 (‖x‖ + 1)) isOpen_ball
    (tendstoUniformlyOn_regularizedScalarNewtonPotentialDerivative hε hεpos hf hcf hB (‖x‖ + 1))
  · exact fun j a _ => hasFDerivAt_regularizedScalarNewtonPotential (hεpos j) hfi a
  · exact fun a _ => tendsto_regularizedScalarNewtonPotential hε hεpos hf hcf hB a
  · simp only [mem_ball, dist_zero_right]
    linarith

/-- Continuity of the genuine signed-potential derivative. -/
lemma continuous_scalarNewtonianPotentialDerivative {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ y, ‖f y‖ ≤ B) : Continuous (scalarNewtonianPotentialDerivative f) := by
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hfi := integrable_scalarDensity_of_bounded_compact hf hcf hB
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc := (tendstoUniformlyOn_regularizedScalarNewtonPotentialDerivative hε hεpos hf hcf hB
    (‖x‖ + 1)).continuousOn
    (Eventually.of_forall fun j =>
      (continuous_regularizedScalarNewtonPotentialDerivative (hεpos j) hfi).continuousOn).frequently
  apply hc.continuousAt (isOpen_ball.mem_nhds ?_)
  simp only [mem_ball, dist_zero_right]
  linarith

/-- Bounded Lebesgue-measurable compactly supported signed densities have C¹ potentials. -/
theorem contDiff_one_scalarNewtonianPotential {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ y, ‖f y‖ ≤ B) : ContDiff ℝ 1 (scalarNewtonianPotential f) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨scalarNewtonianPotentialDerivative f,
    continuous_scalarNewtonianPotentialDerivative hf hcf hB,
    hasFDerivAt_scalarNewtonianPotential hf hcf hB⟩

/-- A uniform bound on a signed Newtonian potential in terms of its support volume. -/
lemma norm_scalarNewtonianPotential_le {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ y, ‖f y‖ ≤ B) (x : E₃) :
    ‖scalarNewtonianPotential f x‖ ≤
      B * (coulombBoundConstant * volume.real (tsupport f) ^ ((2 : ℝ) / 3)) := by
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have hi := (integrable_newtonianPotential_integrand hf hcf hB x).integrableOn
    (s := tsupport f)
  have hk := integrableOn_coulombKernel (tsupport f) hcf.measure_lt_top x
  rw [scalarNewtonianPotential, ← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := tsupport f) (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])]
  calc
    _ ≤ ∫ y in tsupport f, ‖f y / ‖x - y‖‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in tsupport f, B * ‖x - y‖⁻¹ := integral_mono hi.norm (hk.const_mul B)
      (fun y => by
        rw [norm_div, norm_norm, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hB y) (by positivity))
    _ = B * ∫ y in tsupport f, ‖x - y‖⁻¹ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_coulombKernel_le (tsupport f) hcf.measure_lt_top x) hB0

/-- For sources in the unit ball, the potential has a fixed universal sup bound. -/
lemma norm_scalarNewtonianPotential_le_of_support_subset_unitBall {f : E₃ → ℝ} {B : ℝ}
    (hf : AEStronglyMeasurable f volume) (hcf : HasCompactSupport f)
    (hB : ∀ y, ‖f y‖ ≤ B) (hs : tsupport f ⊆ ball 0 1) (x : E₃) :
    ‖scalarNewtonianPotential f x‖ ≤
      (coulombBoundConstant * volume.real (ball (0 : E₃) 1) ^ ((2 : ℝ) / 3)) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg (f 0)).trans (hB 0)
  have hv : volume.real (tsupport f) ≤ volume.real (ball (0 : E₃) 1) :=
    ENNReal.toReal_mono (isBounded_ball.measure_lt_top.ne) (measure_mono hs)
  calc
    _ ≤ B * (coulombBoundConstant * volume.real (tsupport f) ^ ((2 : ℝ) / 3)) :=
      norm_scalarNewtonianPotential_le hf hcf hB x
    _ ≤ B * (coulombBoundConstant * volume.real (ball (0 : E₃) 1) ^ ((2 : ℝ) / 3)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow ENNReal.toReal_nonneg hv (by norm_num))
          (by unfold coulombBoundConstant; positivity)) hB0
    _ = _ := mul_comm _ _

end LiquidDrop
