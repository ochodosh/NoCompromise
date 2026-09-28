import NoCompromise.Capacity.Kelvin

/-!
# Second derivatives of the Kelvin transform

All differential identities involving inverse powers of the norm exclude the origin.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- The gradient of the reciprocal norm away from the origin. -/
lemma kelvin_gradient_inv_norm {x : E₃} (hx : x ≠ 0) :
    gradient (fun y : E₃ => ‖y‖⁻¹) x = -(‖x‖ ^ 3)⁻¹ • x := by
  have h := schauderNewton_hasFDerivAt_inv_norm_pow hx 0
  simp only [zero_add, pow_one, Nat.cast_one, neg_div, one_div] at h
  apply (toDual ℝ E₃).injective
  rw [toDual_gradient, h.fderiv]
  ext y
  simp [toDual_apply_apply]

/-- The exact Hessian of the reciprocal norm, as an operator on vectors. -/
lemma kelvin_hasFDerivAt_gradient_inv_norm {x : E₃} (hx : x ≠ 0) :
    HasFDerivAt (gradient (fun y : E₃ => ‖y‖⁻¹))
      ((3 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
        (1 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃) x := by
  have he : gradient (fun y : E₃ => ‖y‖⁻¹) =ᶠ[𝓝 x]
      (fun y => -(‖y‖ ^ 3)⁻¹ • y) :=
    Filter.eventually_of_mem (isOpen_ne.mem_nhds hx) fun _ hy =>
      kelvin_gradient_inv_norm hy
  have hd := (schauderNewton_hasFDerivAt_inv_norm_pow hx 2).neg.smul (hasFDerivAt_id x)
  apply (hd.congr_of_eventuallyEq he).congr_fderiv
  ext h : 1
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, Nat.reduceAdd, Nat.cast_ofNat,
    neg_apply, Pi.neg_apply, id_eq, smul_eq_mul]
  simp only [neg_div, one_div, neg_mul, neg_neg]
  module

/-- The Hessian identity in terms of the total Fréchet derivative. -/
lemma kelvin_fderiv_gradient_inv_norm {x : E₃} (hx : x ≠ 0) :
    fderiv ℝ (gradient (fun y : E₃ => ‖y‖⁻¹)) x =
      (3 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
        (1 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃ :=
  (kelvin_hasFDerivAt_gradient_inv_norm hx).fderiv

/-- Differentiating the Kelvin gradient, with the monopole Hessian separated
from the terms involving derivatives of the transformed function. -/
lemma kelvin_hessian_identity {v : E₃ → ℝ} {x : E₃} (hx : x ≠ 0)
    (hv : ContDiffAt ℝ 2 v (kelvinInversion x)) :
    let A := fderiv ℝ kelvinInversion x
    let L := fderiv ℝ v (kelvinInversion x)
    let H := fderiv ℝ (fderiv ℝ v) (kelvinInversion x)
    let G := fderiv ℝ (gradient v) (kelvinInversion x)
    fderiv ℝ (gradient (kelvinTransform v)) x =
      v (kelvinInversion x) •
        ((3 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
          (1 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃) -
      (‖x‖ ^ 3)⁻¹ • (L.comp A).smulRight x +
      ((-3 / ‖x‖ ^ 5) • innerSL ℝ x).smulRight (gradient v (kelvinInversion x)) +
      (‖x‖ ^ 3)⁻¹ • G.comp A -
      (2 * (‖x‖ ^ 5)⁻¹ * L x) • ContinuousLinearMap.id ℝ E₃ -
      (((-10 / ‖x‖ ^ 7 * L x) • innerSL ℝ x +
        (2 * (‖x‖ ^ 5)⁻¹) • ((H.comp A).flip x + L)).smulRight x) := by
  dsimp only
  have hI := (hasFDerivAt_kelvinInversion hx).differentiableAt.hasFDerivAt
  have hU := (hv.differentiableAt (by norm_num)).hasFDerivAt.comp x hI
  have hD := ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp x hI
  have hG : DifferentiableAt ℝ (gradient v) (kelvinInversion x) :=
    (toDual ℝ E₃).symm.differentiableAt.comp _
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hG' := hG.hasFDerivAt.comp x hI
  have h3 := schauderNewton_hasFDerivAt_inv_norm_pow hx 2
  have h5 := schauderNewton_hasFDerivAt_inv_norm_pow hx 4
  have hd := ((h3.neg.mul hU).smul (hasFDerivAt_id x)).add
    (h3.smul hG') |>.sub
      (((h5.const_mul 2).mul (hD.clm_apply (hasFDerivAt_id x))).smul (hasFDerivAt_id x))
  have he : gradient (kelvinTransform v) =ᶠ[𝓝 x]
      (fun y => (-(‖y‖ ^ 3)⁻¹ * v (kelvinInversion y)) • y +
        (‖y‖ ^ 3)⁻¹ • gradient v (kelvinInversion y) -
        (2 * (‖y‖ ^ 5)⁻¹ * fderiv ℝ v (kelvinInversion y) y) • y) := by
    filter_upwards [isOpen_ne.mem_nhds hx,
      hI.continuousAt (hv.eventually (by norm_num))] with y hy hyv
    change ContDiffAt ℝ 2 v (kelvinInversion y) at hyv
    exact gradient_kelvinTransform hy (hyv.differentiableAt (by norm_num))
  simp only [Pi.mul_apply, Pi.neg_apply,
    Function.comp_apply, id_eq, Nat.reduceAdd] at hd
  change HasFDerivAt (fun y : E₃ =>
    (-(‖y‖ ^ 3)⁻¹ * v (kelvinInversion y)) • y +
    (‖y‖ ^ 3)⁻¹ • gradient v (kelvinInversion y) -
    (2 * (‖y‖ ^ 5)⁻¹ * fderiv ℝ v (kelvinInversion y) y) • y) _ x at hd
  rw [he.fderiv_eq, hd.fderiv]
  ext h : 1
  simp only [add_apply, sub_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply,
    innerSL_apply_apply, Nat.cast_ofNat, smul_eq_mul, div_eq_mul_inv]
  module

/-- A bound for the derivative of inversion sufficient for remainder estimates. -/
lemma kelvin_norm_fderiv_inversion_le {x : E₃} (hx : x ≠ 0) :
    ‖fderiv ℝ kelvinInversion x‖ ≤ 3 / ‖x‖ ^ 2 := by
  rw [(hasFDerivAt_kelvinInversion hx).fderiv]
  have hn := (norm_pos_iff.mpr hx).le
  calc
    _ ≤ ‖(‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ E₃‖ +
        ‖((-2 / ‖x‖ ^ 4) • innerSL ℝ x).smulRight x‖ := norm_add_le _ _
    _ = (‖x‖ ^ 2)⁻¹ + (2 / ‖x‖ ^ 4 * ‖x‖) * ‖x‖ := by
      simp [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    _ = _ := by
      have hn0 := norm_ne_zero_iff.mpr hx
      field_simp
      ring

/-- Operator norm bound for the explicit monopole Hessian. -/
lemma kelvin_norm_monopole_hessian_le {x : E₃} (hx : x ≠ 0) :
    ‖(3 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
      (1 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃‖ ≤ 4 / ‖x‖ ^ 3 := by
  have hn := (norm_pos_iff.mpr hx).le
  calc
    _ ≤ ‖(3 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x‖ +
        ‖(1 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃‖ := norm_sub_le _ _
    _ = 3 / ‖x‖ ^ 5 * (‖x‖ * ‖x‖) + 1 / ‖x‖ ^ 3 := by
      simp [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
    _ = _ := by
      have hn0 := norm_ne_zero_iff.mpr hx
      field_simp
      ring

/-- Quantitative second-order Kelvin estimate from local bounds on the first
and second derivatives. The exterior radius is at least one. -/
lemma kelvin_hessian_estimate {v : E₃ → ℝ} {x : E₃} (hx : 1 ≤ ‖x‖)
    (hv : ContDiffAt ℝ 2 v (kelvinInversion x)) {a M : ℝ}
    (hval : |v (kelvinInversion x) - a| ≤ M / ‖x‖)
    (hD : ‖fderiv ℝ v (kelvinInversion x)‖ ≤ M)
    (hH : ‖fderiv ℝ (fderiv ℝ v) (kelvinInversion x)‖ ≤ M)
    (hG : ‖fderiv ℝ (gradient v) (kelvinInversion x)‖ ≤ M) :
    ‖fderiv ℝ (gradient (kelvinTransform v)) x -
      ((3 * a / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
        (a / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ 33 * M / ‖x‖ ^ 4 := by
  have hn : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hx
  have hx0 := norm_pos_iff.mp hn
  have hM : 0 ≤ M := (norm_nonneg _).trans hD
  let A := fderiv ℝ kelvinInversion x
  let L := fderiv ℝ v (kelvinInversion x)
  let H := fderiv ℝ (fderiv ℝ v) (kelvinInversion x)
  let G := fderiv ℝ (gradient v) (kelvinInversion x)
  let B := (3 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
    (1 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃
  have hA : ‖A‖ ≤ 3 / ‖x‖ ^ 2 := kelvin_norm_fderiv_inversion_le hx0
  have hB : ‖B‖ ≤ 4 / ‖x‖ ^ 3 := kelvin_norm_monopole_hessian_le hx0
  have hLA : ‖L.comp A‖ ≤ M * (3 / ‖x‖ ^ 2) :=
    (L.opNorm_comp_le A).trans (mul_le_mul hD hA (norm_nonneg _) hM)
  have hGA : ‖G.comp A‖ ≤ M * (3 / ‖x‖ ^ 2) :=
    (G.opNorm_comp_le A).trans (mul_le_mul hG hA (norm_nonneg _) hM)
  have hHA : ‖(H.comp A).flip x‖ ≤ M * (3 / ‖x‖ ^ 2) * ‖x‖ := by
    calc
      _ ≤ ‖(H.comp A).flip‖ * ‖x‖ := (H.comp A).flip.le_opNorm x
      _ = ‖H.comp A‖ * ‖x‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ (M * (3 / ‖x‖ ^ 2)) * ‖x‖ := by
        gcongr
        exact (H.opNorm_comp_le A).trans (mul_le_mul hH hA (norm_nonneg _) hM)
  have hLx : ‖L x‖ ≤ M * ‖x‖ :=
    (L.le_opNorm x).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hgrad : ‖gradient v (kelvinInversion x)‖ ≤ M := by
    change ‖(toDual ℝ E₃).symm (fderiv ℝ v (kelvinInversion x))‖ ≤ M
    simpa only [LinearIsometryEquiv.norm_map] using hD
  let T₀ := (v (kelvinInversion x) - a) • B
  let T₁ := (‖x‖ ^ 3)⁻¹ • (L.comp A).smulRight x
  let T₂ := ((-3 / ‖x‖ ^ 5) • innerSL ℝ x).smulRight (gradient v (kelvinInversion x))
  let T₃ := (‖x‖ ^ 3)⁻¹ • G.comp A
  let T₄ := (2 * (‖x‖ ^ 5)⁻¹ * L x) • ContinuousLinearMap.id ℝ E₃
  let T₅ := ((-10 / ‖x‖ ^ 7 * L x) • innerSL ℝ x +
    (2 * (‖x‖ ^ 5)⁻¹) • ((H.comp A).flip x + L)).smulRight x
  have heq : fderiv ℝ (gradient (kelvinTransform v)) x -
      ((3 * a / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
        (a / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃) =
      T₀ - T₁ + T₂ + T₃ - T₄ - T₅ := by
    rw [kelvin_hessian_identity hx0 hv]
    dsimp [T₀, T₁, T₂, T₃, T₄, T₅, B, A, L, H, G]
    simp only [div_eq_mul_inv]
    module
  have h₀ : ‖T₀‖ ≤ M / ‖x‖ * (4 / ‖x‖ ^ 3) := by
    dsimp [T₀]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hval hB (norm_nonneg _) (by positivity)
  have h₁ : ‖T₁‖ ≤ (‖x‖ ^ 3)⁻¹ * (M * (3 / ‖x‖ ^ 2) * ‖x‖) := by
    dsimp [T₁]
    simp only [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
    rw [Real.norm_of_nonneg (by positivity)]
    gcongr
  have h₂ : ‖T₂‖ ≤ 3 / ‖x‖ ^ 5 * ‖x‖ * M := by
    dsimp [T₂]
    simp only [ContinuousLinearMap.norm_smulRight_apply, norm_smul, innerSL_apply_norm]
    have hc : ‖(-3 : ℝ) / ‖x‖ ^ 5‖ = 3 / ‖x‖ ^ 5 := by simp
    rw [hc]
    gcongr
  have h₃ : ‖T₃‖ ≤ (‖x‖ ^ 3)⁻¹ * (M * (3 / ‖x‖ ^ 2)) := by
    dsimp [T₃]
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    gcongr
  have h₄ : ‖T₄‖ ≤ 2 * (‖x‖ ^ 5)⁻¹ * (M * ‖x‖) := by
    dsimp [T₄]
    rw [norm_smul, norm_mul, norm_mul, ContinuousLinearMap.norm_id, mul_one]
    simp only [Real.norm_ofNat, norm_inv, norm_pow, norm_norm]
    gcongr
  have h₅ : ‖T₅‖ ≤ (10 / ‖x‖ ^ 7 * (M * ‖x‖) * ‖x‖ +
      2 * (‖x‖ ^ 5)⁻¹ * (M * (3 / ‖x‖ ^ 2) * ‖x‖ + M)) * ‖x‖ := by
    dsimp [T₅]
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc
      _ ≤ (‖(-10 / ‖x‖ ^ 7 * L x) • innerSL ℝ x‖ +
          ‖(2 * (‖x‖ ^ 5)⁻¹) • ((H.comp A).flip x + L)‖) * ‖x‖ := by
        gcongr
        exact norm_add_le _ _
      _ = (10 / ‖x‖ ^ 7 * ‖L x‖ * ‖x‖ +
          2 * (‖x‖ ^ 5)⁻¹ * ‖(H.comp A).flip x + L‖) * ‖x‖ := by
        simp only [norm_smul, norm_mul, norm_div, innerSL_apply_norm, norm_neg,
          Real.norm_ofNat, norm_pow, norm_norm, norm_inv]
      _ ≤ _ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add hHA hD)
  rw [heq]
  calc
    _ ≤ ‖T₀‖ + ‖T₁‖ + ‖T₂‖ + ‖T₃‖ + ‖T₄‖ + ‖T₅‖ := by
      have h01 := norm_sub_le T₀ T₁
      have h02 := norm_add_le (T₀ - T₁) T₂
      have h03 := norm_add_le (T₀ - T₁ + T₂) T₃
      have h04 := norm_sub_le (T₀ - T₁ + T₂ + T₃) T₄
      have h05 := norm_sub_le (T₀ - T₁ + T₂ + T₃ - T₄) T₅
      linarith only [h01, h02, h03, h04, h05]
    _ ≤ M / ‖x‖ * (4 / ‖x‖ ^ 3) +
        (‖x‖ ^ 3)⁻¹ * (M * (3 / ‖x‖ ^ 2) * ‖x‖) +
        3 / ‖x‖ ^ 5 * ‖x‖ * M +
        (‖x‖ ^ 3)⁻¹ * (M * (3 / ‖x‖ ^ 2)) +
        2 * (‖x‖ ^ 5)⁻¹ * (M * ‖x‖) +
        (10 / ‖x‖ ^ 7 * (M * ‖x‖) * ‖x‖ +
          2 * (‖x‖ ^ 5)⁻¹ * (M * (3 / ‖x‖ ^ 2) * ‖x‖ + M)) * ‖x‖ := by
      linarith only [h₀, h₁, h₂, h₃, h₄, h₅]
    _ = 24 * M / ‖x‖ ^ 4 + 9 * M / ‖x‖ ^ 5 := by field_simp; ring
    _ ≤ 33 * M / ‖x‖ ^ 4 := by
      have hp : ‖x‖ ^ 4 ≤ ‖x‖ ^ 5 := by nlinarith [pow_pos hn 4]
      have hb := div_le_div_of_nonneg_left (by positivity : 0 ≤ 9 * M) (pow_pos hn 4) hp
      calc
        _ ≤ 24 * M / ‖x‖ ^ 4 + 9 * M / ‖x‖ ^ 4 := add_le_add_right hb _
        _ = _ := by ring

/-- Blueprint `lem:kelvin`, equation `eq:hess-u-expansion`: a smooth Kelvin
extension gives the Hessian expansion with coefficient equal to its value at zero. -/
theorem kelvin_hessian_expansion_of_smooth_extension {u v : E₃ → ℝ} {r : ℝ}
    (hr : 0 < r) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0})) :
    ∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      ‖fderiv ℝ (gradient u) x -
        ((3 * v 0 / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
          (v 0 / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ C' / ‖x‖ ^ 4 := by
  have hs : closedBall (0 : E₃) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  have hvD : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ v) (ball 0 r) :=
    hv.fderiv_of_isOpen isOpen_ball (by simp)
  have hvG : ContDiffOn ℝ (⊤ : ℕ∞) (gradient v) (ball 0 r) :=
    (toDual ℝ E₃).symm.contDiff.comp_contDiffOn hvD
  obtain ⟨M₁, hM₁⟩ := (isCompact_closedBall (0 : E₃) (r / 2)).exists_bound_of_continuousOn
    (hvD.continuousOn.mono hs)
  obtain ⟨M₂, hM₂⟩ := (isCompact_closedBall (0 : E₃) (r / 2)).exists_bound_of_continuousOn
    ((hvD.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hs)
  obtain ⟨M₃, hM₃⟩ := (isCompact_closedBall (0 : E₃) (r / 2)).exists_bound_of_continuousOn
    ((hvG.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hs)
  let M := max M₁ (max M₂ M₃)
  have hD : ∀ z ∈ closedBall (0 : E₃) (r / 2), ‖fderiv ℝ v z‖ ≤ M :=
    fun z hz => (hM₁ z hz).trans (le_max_left _ _)
  have hH : ∀ z ∈ closedBall (0 : E₃) (r / 2), ‖fderiv ℝ (fderiv ℝ v) z‖ ≤ M :=
    fun z hz => (hM₂ z hz).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hG : ∀ z ∈ closedBall (0 : E₃) (r / 2), ‖fderiv ℝ (gradient v) z‖ ≤ M :=
    fun z hz => (hM₃ z hz).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hdiff : ∀ z ∈ ball (0 : E₃) r, DifferentiableAt ℝ v z := fun z hz =>
    (hv.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hval : ∀ z ∈ closedBall (0 : E₃) (r / 2), |v z - v 0| ≤ M * ‖z‖ := by
    intro z hz
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy => hdiff y (hs hy)) hD
        (convex_closedBall (0 : E₃) (r / 2))
        (mem_closedBall_self (half_pos hr).le) hz
  refine ⟨max 1 (2 / r), 33 * M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx
  have hx1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hxR : 2 / r ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hn : 0 < ‖x‖ := zero_lt_one.trans_le hx1
  have hx0 : x ≠ 0 := norm_pos_iff.mp hn
  have hxI : kelvinInversion x ∈ closedBall (0 : E₃) (r / 2) := by
    rw [mem_closedBall, dist_zero_right, norm_kelvinInversion, inv_eq_one_div]
    apply (div_le_iff₀ hn).mpr
    have := (div_le_iff₀ hr).mp hxR
    nlinarith
  have hI0 : kelvinInversion x ≠ 0 := by
    intro h
    have := norm_kelvinInversion x
    rw [h, norm_zero] at this
    exact (inv_ne_zero hn.ne') this.symm
  have hnear : v =ᶠ[𝓝 (kelvinInversion x)] kelvinTransform u :=
    Filter.eventually_of_mem ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hs hxI, hI0⟩)
      (fun _ hy => he hy)
  have hback : kelvinTransform v =ᶠ[𝓝 x] u := by
    filter_upwards [hnear.comp_tendsto (hasFDerivAt_kelvinInversion hx0).continuousAt,
      isOpen_ne.mem_nhds hx0] with y hy hy0
    calc
      kelvinTransform v y = kelvinTransform (kelvinTransform u) y :=
        congrArg (fun a => ‖y‖⁻¹ * a) hy
      _ = u y := kelvinTransform_involutive u hy0
  have hvalue : |v (kelvinInversion x) - v 0| ≤ M / ‖x‖ := by
    simpa only [norm_kelvinInversion, div_eq_mul_inv] using hval _ hxI
  have hb := kelvin_hessian_estimate hx1
    ((hv.contDiffAt (isOpen_ball.mem_nhds (hs hxI))).of_le (by simp))
    hvalue (hD _ hxI) (hH _ hxI) (hG _ hxI)
  rw [hback.gradient.fderiv_eq] at hb
  exact hb

/-- Blueprint `lem:kelvin`: the value, gradient, and Hessian expansions of a
capacitary potential, all with the same coefficient at infinity. -/
theorem kelvin_hessian_expansion
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 ∧
      ‖fderiv ℝ (gradient u) x -
        ((3 * Cinf / ‖x‖ ^ 5) • (innerSL ℝ x).smulRight x -
          (Cinf / ‖x‖ ^ 3) • ContinuousLinearMap.id ℝ E₃)‖ ≤ C' / ‖x‖ ^ 4 := by
  obtain ⟨v, hv, he, _⟩ := kelvin_smooth_extension hK hR₀ hKR hzero hu hh hb hinf
  obtain ⟨R₁, C₁, hR₁, h₁⟩ := kelvin_expansion_of_smooth_extension (by positivity) hv he
  obtain ⟨R₂, C₂, _, h₂⟩ := kelvin_hessian_expansion_of_smooth_extension (by positivity) hv he
  refine ⟨v 0, max R₁ R₂, max C₁ C₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  obtain ⟨hval, hgrad⟩ := h₁ x ((le_max_left _ _).trans hx)
  have hhess := h₂ x ((le_max_right _ _).trans hx)
  exact ⟨hval.trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg hn 2)),
    hgrad.trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg hn 3)),
    hhess.trans (div_le_div_of_nonneg_right (le_max_right _ _) (pow_nonneg hn 4))⟩

end LiquidDrop
