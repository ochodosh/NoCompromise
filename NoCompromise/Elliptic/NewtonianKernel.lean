module

public import NoCompromise.Energy.PotentialRegularity
public import NoCompromise.Elliptic.InteriorH2Hessian
public import NoCompromise.Ball.Potential
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section

/-!
# The Newtonian fundamental kernel

An explicit smooth regularization has negative Laplacian equal to a nonnegative
approximation density. Radial integration proves its mass is `4π`, and scaling
proves convergence to a point mass. Two integrations by parts and dominated
convergence establish the distributional identity for the actual singular kernel.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped NNReal ENNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The nonnegative density obtained by taking minus the regularized Laplacian. -/
def newtonApproximationDensity (ε : ℝ) (x : E₃) : ℝ :=
  3 * ε ^ 2 / Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5

lemma contDiff_regularizedNewtonKernel {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (regularizedNewtonKernel ε) := by
  apply (((contDiff_norm_sq ℝ).add contDiff_const).sqrt ?_).inv
  · intro x
    exact (regularizedNewton_sqrt_bounds hε x).1.ne'
  · intro x
    have : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
    exact this.ne'

lemma poissonCoordinateDerivative_regularizedNewtonKernel {ε : ℝ} (hε : 0 < ε)
    (i : Fin 3) (x : E₃) :
    poissonCoordinateDerivative i (regularizedNewtonKernel ε) x =
      -(Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ * x i := by
  rw [poissonCoordinateDerivative, (hasFDerivAt_regularizedNewtonKernel hε x).fderiv]
  simp [regularizedNewtonDerivative, innerSL_apply_apply,
    EuclideanSpace.inner_single_right]

lemma poissonCoordinateDerivative_twice_regularizedNewtonKernel {ε : ℝ} (hε : 0 < ε)
    (i : Fin 3) (x : E₃) :
    poissonCoordinateDerivative i
      (poissonCoordinateDerivative i (regularizedNewtonKernel ε)) x =
      3 * (x i) ^ 2 / Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 5 -
        (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ := by
  have hp : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  have hs : Real.sqrt (‖x‖ ^ 2 + ε ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hd := (hasDerivAt_inv (pow_ne_zero 3 hs)).comp_hasFDerivAt x
    ((((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (ε ^ 2)).sqrt hp.ne').pow 3)
  have hm := hd.neg.mul ((EuclideanSpace.proj i).hasFDerivAt (x := x))
  change HasFDerivAt (fun y : E₃ =>
    -(Real.sqrt (‖y‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ * y i) _ x at hm
  have he : poissonCoordinateDerivative i (regularizedNewtonKernel ε) =
      fun y => -(Real.sqrt (‖y‖ ^ 2 + ε ^ 2) ^ 3)⁻¹ * y i :=
    funext (poissonCoordinateDerivative_regularizedNewtonKernel hε i)
  rw [he, poissonCoordinateDerivative, hm.fderiv]
  simp [Function.comp_def, Pi.neg_apply, EuclideanSpace.proj,
    EuclideanSpace.inner_single_right, innerSL_apply_apply, smul_eq_mul]
  field_simp
  ring

lemma laplacianN_regularizedNewtonKernel {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    laplacianN (regularizedNewtonKernel ε) x = -newtonApproximationDensity ε x := by
  have hs := (regularizedNewton_sqrt_bounds hε x).1.ne'
  have hsq := Real.sq_sqrt (show 0 ≤ ‖x‖ ^ 2 + ε ^ 2 by positivity)
  have hn := EuclideanSpace.real_norm_sq_eq x
  simp only [Fin.sum_univ_three] at hn
  simp only [laplacianN, poissonCoordinateDerivative_twice_regularizedNewtonKernel hε,
    Fin.sum_univ_three, newtonApproximationDensity]
  field_simp
  nlinarith

lemma integral_newtonian_laplacian_comm {n : ℕ}
    {u φ : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (hφ : ContDiff ℝ 2 φ) (hcφ : HasCompactSupport φ) :
    (∫ x, u x * laplacianN φ x) = ∫ x, φ x * laplacianN u x := by
  classical
  have hdu i := ContDiff.poissonCoordinateDerivative (r := 1) hu i
  have hdφ i := ContDiff.poissonCoordinateDerivative (r := 1) hφ i
  have hcDφ i := HasCompactSupport.poissonCoordinateDerivative hcφ i
  have hddu i := ContDiff.poissonCoordinateDerivative (r := 0) (hdu i) i
  have hddφ i := ContDiff.poissonCoordinateDerivative (r := 0) (hdφ i) i
  have hcDDφ i := HasCompactSupport.poissonCoordinateDerivative (hcDφ i) i
  have hiL i : Integrable (fun x => u x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i φ) x) :=
    (hu.continuous.mul (hddφ i).continuous).integrable_of_hasCompactSupport
      (hcDDφ i).mul_left
  have hiR i : Integrable (fun x => φ x *
      poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x) :=
    (hφ.continuous.mul (hddu i).continuous).integrable_of_hasCompactSupport hcφ.mul_right
  simp only [laplacianN, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hiL i),
    integral_finsetSum _ (fun i _ => hiR i)]
  apply Finset.sum_congr rfl
  intro i _
  have h1 := integral_mul_poissonCoordinateDerivative (hu.of_le (by norm_num))
    (hdφ i) (hcDφ i) i
  have h2 := integral_mul_poissonCoordinateDerivative (hdu i)
    (hφ.of_le (by norm_num)) hcφ i
  simp_rw [mul_comm (poissonCoordinateDerivative i u _)] at h2
  linarith only [h1, h2]

lemma hasDerivAt_newtonianRadialPrimitive (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 3 / Real.sqrt (s ^ 2 + 1) ^ 3)
      (3 * r ^ 2 / Real.sqrt (r ^ 2 + 1) ^ 5) r := by
  have hp : 0 < r ^ 2 + 1 := by positivity
  have hs : Real.sqrt (r ^ 2 + 1) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hd := ((hasDerivAt_id r).pow 3).div
    ((((hasDerivAt_id r).pow 2).add_const 1).sqrt hp.ne' |>.pow 3)
    (pow_ne_zero 3 hs)
  convert! hd using 1
  have hsq := Real.sq_sqrt hp.le
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    mul_one, pow_one]
  field_simp
  nlinarith [sq_nonneg (r ^ 2), sq_nonneg (Real.sqrt (r ^ 2 + 1)), hsq]

lemma tendsto_newtonianRadialPrimitive :
    Tendsto (fun r : ℝ => r ^ 3 / Real.sqrt (r ^ 2 + 1) ^ 3) atTop (𝓝 1) := by
  have hi : Tendsto (fun r : ℝ => (r ^ 2 + 1)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_add
      (tendsto_const_nhds (x := (1 : ℝ)))
  have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub hi).sqrt).pow 3
  have he : (fun r : ℝ => r ^ 3 / Real.sqrt (r ^ 2 + 1) ^ 3) =ᶠ[atTop]
      (fun r => Real.sqrt (1 - (r ^ 2 + 1)⁻¹) ^ 3) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    have hp : 0 < r ^ 2 + 1 := by positivity
    have hquot : 1 - (r ^ 2 + 1)⁻¹ = r ^ 2 / (r ^ 2 + 1) := by
      field_simp
      ring
    rw [hquot, Real.sqrt_div (sq_nonneg r), Real.sqrt_sq hr, div_pow]
  exact (by simpa using h :
    Tendsto (fun r : ℝ => Real.sqrt (1 - (r ^ 2 + 1)⁻¹) ^ 3) atTop (𝓝 1)).congr' he.symm

lemma integrable_newtonApproximationDensity_one : Integrable (newtonApproximationDensity 1) := by
  have hi := integrableOn_Ioi_deriv_of_nonneg'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => hasDerivAt_newtonianRadialPrimitive r)
    (fun r (_ : r ∈ Ioi (0 : ℝ)) => by positivity)
    tendsto_newtonianRadialPrimitive
  unfold newtonApproximationDensity
  simp only [one_pow, mul_one]
  apply (integrable_fun_norm_addHaar (volume : Measure E₃)
    (f := fun r => 3 / Real.sqrt (r ^ 2 + 1) ^ 5)).mpr
  convert! hi using 1
  funext r
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  ring


lemma integral_newtonApproximationDensity_one :
    (∫ x, newtonApproximationDensity 1 x) = 4 * Real.pi := by
  have he := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (_ : r ∈ Ici (0 : ℝ)) => hasDerivAt_newtonianRadialPrimitive r)
    (fun r (_ : r ∈ Ioi (0 : ℝ)) => by positivity)
    tendsto_newtonianRadialPrimitive
  simp only [zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_div, sub_zero] at he
  have hh := integral_fun_norm_addHaar (volume : Measure E₃)
    (fun r : ℝ => 3 / Real.sqrt (r ^ 2 + 1) ^ 5)
  simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    nsmul_eq_mul, smul_eq_mul] at hh
  have hball : volume.real (ball (0 : E₃) 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, volume_ball_eq_ofReal 0 (by norm_num), ENNReal.toReal_ofReal]
    · ring
    · positivity
  simp only [newtonApproximationDensity, one_pow, mul_one]
  rw [hh, hball]
  rw [show (fun r : ℝ => r ^ 2 * (3 / Real.sqrt (r ^ 2 + 1) ^ 5)) =
    (fun r : ℝ => 3 * r ^ 2 / Real.sqrt (r ^ 2 + 1) ^ 5) by funext r; ring, he]
  ring

lemma newtonApproximationDensity_nonneg (ε : ℝ) (x : E₃) :
    0 ≤ newtonApproximationDensity ε x := by
  unfold newtonApproximationDensity
  positivity

lemma continuous_newtonApproximationDensity {ε : ℝ} (hε : 0 < ε) :
    Continuous (newtonApproximationDensity ε) := by
  exact continuous_const.div (((continuous_norm.pow 2).add continuous_const).sqrt.pow 5)
    (fun x => pow_ne_zero 5 (regularizedNewton_sqrt_bounds hε x).1.ne')

lemma newtonApproximationDensity_smul {ε : ℝ} (hε : 0 < ε) (x : E₃) :
    newtonApproximationDensity ε (ε • x) =
      (ε ^ 3)⁻¹ * newtonApproximationDensity 1 x := by
  have hs : Real.sqrt (‖ε • x‖ ^ 2 + ε ^ 2) =
      ε * Real.sqrt (‖x‖ ^ 2 + 1) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε,
      show (ε * ‖x‖) ^ 2 + ε ^ 2 = ε ^ 2 * (‖x‖ ^ 2 + 1) by ring,
      Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]
  simp only [newtonApproximationDensity, hs, one_pow, mul_one]
  have hp : Real.sqrt (‖x‖ ^ 2 + 1) ≠ 0 := by positivity
  field_simp

lemma integral_newtonApproximationDensity_mul {ε : ℝ} (hε : 0 < ε) (φ : E₃ → ℝ) :
    (∫ x, newtonApproximationDensity ε x * φ x) =
      ∫ x, newtonApproximationDensity 1 x * φ (ε • x) := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E₃)
    (fun x => newtonApproximationDensity ε x * φ x) ε (hR := hε.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    newtonApproximationDensity_smul hε, mul_assoc, integral_const_mul] at h
  exact mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 3 hε.ne')) h.symm

lemma tendsto_integral_newtonApproximationDensity_mul {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {φ : E₃ → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun j => ∫ x, newtonApproximationDensity (ε j) x * φ x)
      atTop (𝓝 (4 * Real.pi * φ 0)) := by
  obtain ⟨B, hB⟩ := hcφ.exists_bound_of_continuous hφ
  have hlim : (∫ x, newtonApproximationDensity 1 x * φ 0) = 4 * Real.pi * φ 0 := by
    rw [integral_mul_const, integral_newtonApproximationDensity_one]
  rw [← hlim]
  simp_rw [integral_newtonApproximationDensity_mul (hεpos _)]
  apply tendsto_integral_of_dominated_convergence
    (fun x => newtonApproximationDensity 1 x * B)
  · intro j
    exact ((continuous_newtonApproximationDensity (ε := 1) (by norm_num)).mul
      (hφ.comp ((continuous_const : Continuous (fun _ : E₃ => ε j)).smul
        continuous_id))).aestronglyMeasurable
  · exact integrable_newtonApproximationDensity_one.mul_const B
  · intro j
    filter_upwards [] with x
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (newtonApproximationDensity_nonneg 1 x)]
    exact mul_le_mul_of_nonneg_left (hB _) (newtonApproximationDensity_nonneg 1 x)
  · filter_upwards [] with x
    have ht : Tendsto (fun j => ε j • x) atTop (𝓝 (0 : E₃)) := by
      simpa using hε.smul_const x
    exact tendsto_const_nhds.mul ((hφ.tendsto 0).comp ht)

lemma locallyIntegrable_newtonKernel : LocallyIntegrable (fun x : E₃ => ‖x‖⁻¹) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  simpa only [zero_sub, norm_neg] using
    integrableOn_coulombKernel K hK.measure_lt_top 0

lemma tendsto_integral_regularizedNewtonKernel_mul {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j, 0 < ε j)
    {φ : E₃ → ℝ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    Tendsto (fun j => ∫ x, regularizedNewtonKernel (ε j) x * φ x)
      atTop (𝓝 (∫ x, ‖x‖⁻¹ * φ x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖x‖⁻¹ * ‖φ x‖)
  · intro j
    exact ((continuous_regularizedNewtonKernel (hεpos j)).mul hφ).aestronglyMeasurable
  · exact locallyIntegrable_newtonKernel.integrable_smul_right_of_hasCompactSupport
      hφ.norm hcφ.norm
  · intro j
    filter_upwards [(volume : Measure E₃).ae_ne 0] with x hx
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hs := regularizedNewton_sqrt_bounds (hεpos j) x
    rw [regularizedNewtonKernel, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs.1)]
    exact inv_anti₀ (norm_pos_iff.mpr hx) hs.2.1
  · filter_upwards [(volume : Measure E₃).ae_ne 0] with x hx
    exact (tendsto_regularizedNewtonKernel hε hx).mul tendsto_const_nhds

/-- The inverse-distance kernel has distributional Laplacian `-4π δ₀`. -/
theorem integral_newtonKernel_mul_laplacianN {φ : E₃ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
    (∫ x, ‖x‖⁻¹ * laplacianN φ x) = -(4 * Real.pi * φ 0) := by
  let ε : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹
  have hε : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := (1 : ℝ))))
  have hεpos (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hΔφ := continuous_laplacianN (hφ.of_le (by simp) : ContDiff ℝ 2 φ)
  have hcΔφ : HasCompactSupport (laplacianN φ) :=
    hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_laplacianN_subset φ)
  have hleft := tendsto_integral_regularizedNewtonKernel_mul hε hεpos hΔφ hcΔφ
  have hright := (tendsto_integral_newtonApproximationDensity_mul hε hεpos
    hφ.continuous hcφ).neg
  apply tendsto_nhds_unique hleft
  convert! hright using 1
  ext j
  rw [integral_newtonian_laplacian_comm
    ((contDiff_regularizedNewtonKernel (hεpos j)).of_le (by simp))
    (hφ.of_le (by simp)) hcφ]
  simp only [laplacianN_regularizedNewtonKernel (hεpos j), mul_neg, integral_neg]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => mul_comm _ _)

/-- The same singular-kernel identity centered at an arbitrary source point. -/
theorem integral_newtonKernel_sub_mul_laplacianN {φ : E₃ → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) (y : E₃) :
    (∫ x, ‖x - y‖⁻¹ * laplacianN φ x) = -(4 * Real.pi * φ y) := by
  have h := integral_newtonKernel_mul_laplacianN
    (hφ.comp (contDiff_const.sub contDiff_id))
    (hcφ.comp_homeomorph (Homeomorph.subLeft y))
  change (∫ x, ‖x‖⁻¹ * laplacianN (fun z => φ (y - z)) x) =
    -(4 * Real.pi * φ (y - 0)) at h
  simp only [laplacianN_comp_const_sub (hφ.of_le (by simp)), sub_zero] at h
  rw [← integral_sub_left_eq_self (fun x : E₃ => ‖x - y‖⁻¹ * laplacianN φ x) volume y]
  simpa only [sub_sub_cancel_left, norm_neg] using h

end LiquidDrop
