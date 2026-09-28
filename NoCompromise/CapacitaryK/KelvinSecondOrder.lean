import NoCompromise.Capacity.Kelvin
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Second-order Kelvin expansion

Chapter 31, `lem:K-normalization`: the second-order expansion of the Kelvin
extension and its differentiated remainder. Translation removing the dipole
and the zero spherical mean of the quadrupole are not part of this module.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal Gradient RealInnerProductSpace
namespace LiquidDrop.CapacitaryK
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private lemma norm_sub_le_of_derivative_power
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₃ → F} {D : E₃ → E₃ →L[ℝ] F} {q M : ℝ} (hM : 0 ≤ M) (n : ℕ)
    (hd : ∀ z ∈ closedBall (0 : E₃) q, HasFDerivAt f (D z) z)
    (hb : ∀ z ∈ closedBall (0 : E₃) q, ‖D z‖ ≤ M * ‖z‖ ^ n)
    {y : E₃} (hy : y ∈ closedBall (0 : E₃) q) :
    ‖f y - f 0‖ ≤ M * ‖y‖ ^ (n + 1) := by
  have hs : closedBall (0 : E₃) ‖y‖ ⊆ closedBall 0 q :=
    closedBall_subset_closedBall (by simpa using hy)
  have hb' : ∀ z ∈ closedBall (0 : E₃) ‖y‖, ‖D z‖ ≤ M * ‖y‖ ^ n := by
    intro z hz
    apply (hb z (hs hz)).trans
    have hz' : ‖z‖ ≤ ‖y‖ := by simpa using hz
    gcongr
  simpa only [sub_zero, pow_succ, mul_assoc] using
    (convex_closedBall (0 : E₃) ‖y‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hd z (hs hz)).hasFDerivWithinAt) hb'
      (mem_closedBall_self (norm_nonneg y)) (by simp)

/-- Chapter 31, `lem:K-normalization`: simultaneous Taylor bounds on a smaller
closed ball, in operator norm for the derivative remainder. -/
lemma kelvin_second_order_taylor_bounds {v : E₃ → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ closedBall (0 : E₃) (r / 2),
      |v y - v 0 - fderiv ℝ v 0 y -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 y y| ≤ M * ‖y‖ ^ 3 ∧
      ‖fderiv ℝ v y - fderiv ℝ v 0 - fderiv ℝ (fderiv ℝ v) 0 y‖ ≤
        M * ‖y‖ ^ 2 := by
  let B := fderiv ℝ (fderiv ℝ v) 0
  have hs : closedBall (0 : E₃) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  have hv1 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ v) (ball 0 r) :=
    hv.fderiv_of_isOpen isOpen_ball (by simp)
  have hv2 : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ v)) (ball 0 r) :=
    hv1.fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E₃) (r / 2)).exists_bound_of_continuousOn
    ((hv2.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).mono hs)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans
    (hM 0 (mem_closedBall_self (half_pos hr).le))
  have hd0 : ∀ z ∈ closedBall (0 : E₃) (r / 2), DifferentiableAt ℝ v z :=
    fun z hz => (hv.contDiffAt (isOpen_ball.mem_nhds (hs hz))).differentiableAt (by simp)
  have hd1 : ∀ z ∈ closedBall (0 : E₃) (r / 2), DifferentiableAt ℝ (fderiv ℝ v) z :=
    fun z hz => (hv1.contDiffAt (isOpen_ball.mem_nhds (hs hz))).differentiableAt (by simp)
  have hd2 : ∀ z ∈ closedBall (0 : E₃) (r / 2), DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ v)) z :=
    fun z hz => (hv2.contDiffAt (isOpen_ball.mem_nhds (hs hz))).differentiableAt (by simp)
  have hB : ∀ z ∈ closedBall (0 : E₃) (r / 2),
      ‖fderiv ℝ (fderiv ℝ v) z - B‖ ≤ M * ‖z‖ := by
    intro z hz
    simpa only [sub_zero] using Convex.norm_image_sub_le_of_norm_fderiv_le
      hd2 hM (convex_closedBall (0 : E₃) (r / 2))
      (mem_closedBall_self (half_pos hr).le) hz
  have hD : ∀ y ∈ closedBall (0 : E₃) (r / 2),
      ‖fderiv ℝ v y - fderiv ℝ v 0 - B y‖ ≤ M * ‖y‖ ^ 2 := by
    intro y hy
    have hd : ∀ z ∈ closedBall (0 : E₃) (r / 2),
        HasFDerivAt (fun z => fderiv ℝ v z - fderiv ℝ v 0 - B z)
          (fderiv ℝ (fderiv ℝ v) z - B) z := by
      intro z hz
      convert! ((hd1 z hz).hasFDerivAt.sub_const (fderiv ℝ v 0)).sub B.hasFDerivAt using 1
    have hb : ∀ z ∈ closedBall (0 : E₃) (r / 2),
        ‖fderiv ℝ (fderiv ℝ v) z - B‖ ≤ M * ‖z‖ ^ 1 := by
      simpa only [pow_one] using hB
    simpa using norm_sub_le_of_derivative_power hM0 1 hd hb hy
  have hsym : ∀ z w, B z w = B w z :=
    (hv.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).isSymmSndFDerivAt (by simp)
  have hquad : ∀ z : E₃, HasFDerivAt (fun z => (1 / 2 : ℝ) * B z z) (B z) z := by
    intro z
    have h := (B.hasFDerivAt.clm_apply (hasFDerivAt_id z)).const_mul (1 / 2 : ℝ)
    convert! h using 1
    ext w
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, id_eq]
    rw [hsym w z]
    ring
  refine ⟨M, hM0, fun y hy => ⟨?_, hD y hy⟩⟩
  have hd : ∀ z ∈ closedBall (0 : E₃) (r / 2),
      HasFDerivAt (fun z => v z - v 0 - fderiv ℝ v 0 z - (1 / 2 : ℝ) * B z z)
        (fderiv ℝ v z - fderiv ℝ v 0 - B z) z := by
    intro z hz
    exact (((hd0 z hz).hasFDerivAt.sub_const (v 0)).sub
      (fderiv ℝ v 0).hasFDerivAt).sub (hquad z)
  simpa [Real.norm_eq_abs] using norm_sub_le_of_derivative_power hM0 2 hd hD hy

/-- Chapter 31, `eq:K-expansion`: monopole, dipole, and quadrupole before translation. -/
def kelvinSecondOrderModel (v : E₃ → ℝ) (x : E₃) : ℝ :=
  v 0 / ‖x‖ + fderiv ℝ v 0 x / ‖x‖ ^ 3 +
    (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 x x / ‖x‖ ^ 5

private lemma kelvin_second_order_exterior {u v : E₃ → ℝ} {r : ℝ} (hr : 0 < r)
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0}))
    {x : E₃} (hx : 2 / r ≤ ‖x‖) :
    x ≠ 0 ∧ kelvinInversion x ∈ closedBall (0 : E₃) (r / 2) ∧
      kelvinTransform v =ᶠ[𝓝 x] u := by
  have hn : 0 < ‖x‖ := (div_pos (by norm_num) hr).trans_le hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp hn
  have hxI : kelvinInversion x ∈ closedBall (0 : E₃) (r / 2) := by
    rw [mem_closedBall, dist_zero_right, norm_kelvinInversion, inv_eq_one_div]
    apply (div_le_iff₀ hn).mpr
    have := (div_le_iff₀ hr).mp hx
    nlinarith
  have hI0 : kelvinInversion x ≠ 0 := by
    intro h
    have := norm_kelvinInversion x
    rw [h, norm_zero] at this
    exact (inv_ne_zero hn.ne') this.symm
  have hs : closedBall (0 : E₃) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  have hnear : v =ᶠ[𝓝 (kelvinInversion x)] kelvinTransform u :=
    Filter.eventually_of_mem ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hs hxI, hI0⟩)
      (fun _ hy => he hy)
  refine ⟨hx0, hxI, ?_⟩
  filter_upwards [hnear.comp_tendsto (hasFDerivAt_kelvinInversion hx0).continuousAt,
    isOpen_ne.mem_nhds hx0] with y hy hy0
  calc
    kelvinTransform v y = kelvinTransform (kelvinTransform u) y :=
      congrArg (fun a => ‖y‖⁻¹ * a) hy
    _ = u y := kelvinTransform_involutive u hy0

/-- Chapter 31, `eq:K-expansion`: the second-order value expansion with a
remainder bounded by a constant times the inverse fourth power of the radius. -/
theorem kelvin_second_order_value {u v : E₃ → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0})) :
    ∃ R M : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      |u x - kelvinSecondOrderModel v x| ≤ M / ‖x‖ ^ 4 := by
  obtain ⟨M, _, hM⟩ := kelvin_second_order_taylor_bounds hr hv
  refine ⟨2 / r, M, by positivity, ?_⟩
  intro x hx
  obtain ⟨hx0, hxI, hback⟩ := kelvin_second_order_exterior hr he hx
  have hn := norm_pos_iff.mpr hx0
  have hmodel : kelvinSecondOrderModel v x = ‖x‖⁻¹ *
      (v 0 + fderiv ℝ v 0 (kelvinInversion x) +
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 (kelvinInversion x) (kelvinInversion x)) := by
    simp only [kelvinSecondOrderModel, kelvinInversion, map_smul, smul_apply, smul_eq_mul]
    field_simp
  have herr : u x - kelvinSecondOrderModel v x = ‖x‖⁻¹ *
      (v (kelvinInversion x) - v 0 - fderiv ℝ v 0 (kelvinInversion x) -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 (kelvinInversion x) (kelvinInversion x)) := by
    rw [← hback.self_of_nhds, hmodel, kelvinTransform]
    ring
  rw [herr, abs_mul, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  calc
    _ ≤ ‖x‖⁻¹ * (M * ‖kelvinInversion x‖ ^ 3) :=
      mul_le_mul_of_nonneg_left (hM _ hxI).1 (inv_nonneg.mpr hn.le)
    _ = M / ‖x‖ ^ 4 := by rw [norm_kelvinInversion]; ring

/-- Chapter 31, `eq:K-expansion`: the gradient model obtained by substituting
both Taylor polynomials into the Kelvin gradient formula. -/
def kelvinSecondOrderGradient (v : E₃ → ℝ) (x : E₃) : E₃ :=
  let y := kelvinInversion x
  let B := fderiv ℝ (fderiv ℝ v) 0
  (-(‖x‖ ^ 3)⁻¹ * (v 0 + fderiv ℝ v 0 y + (1 / 2 : ℝ) * B y y)) • x +
    (‖x‖ ^ 3)⁻¹ • (gradient v 0 + (toDual ℝ E₃).symm (B y)) -
    (2 * (‖x‖ ^ 5)⁻¹ * (fderiv ℝ v 0 x + B y x)) • x

/-- Chapter 31, `eq:K-expansion`: the differentiated second-order remainder
is bounded by a constant times the inverse fifth power of the radius. -/
theorem kelvin_second_order_gradient {u v : E₃ → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0})) :
    ∃ R M : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      ‖gradient u x - kelvinSecondOrderGradient v x‖ ≤ M / ‖x‖ ^ 5 := by
  obtain ⟨M, _, hM⟩ := kelvin_second_order_taylor_bounds hr hv
  refine ⟨2 / r, 4 * M, by positivity, ?_⟩
  intro x hx
  obtain ⟨hx0, hxI, hback⟩ := kelvin_second_order_exterior hr he hx
  have hn := norm_pos_iff.mpr hx0
  let y := kelvinInversion x
  let P := v 0 + fderiv ℝ v 0 y + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 y y
  let D := fderiv ℝ v y - fderiv ℝ v 0 - fderiv ℝ (fderiv ℝ v) 0 y
  have hval : |v y - P| ≤ M / ‖x‖ ^ 3 := by
    have h := (hM _ hxI).1
    have heq : v y - P = v y - v 0 - fderiv ℝ v 0 y -
        (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ v) 0 y y := by dsimp [P]; ring
    rw [heq]
    simpa only [y, norm_kelvinInversion, inv_pow, div_eq_mul_inv] using h
  have hder : ‖D‖ ≤ M / ‖x‖ ^ 2 := by
    simpa only [D, y, norm_kelvinInversion, inv_pow, div_eq_mul_inv] using (hM _ hxI).2
  have hgrad : ‖(toDual ℝ E₃).symm D‖ ≤ M / ‖x‖ ^ 2 := by
    simpa only [LinearIsometryEquiv.norm_map] using hder
  have hlin : |D x| ≤ (M / ‖x‖ ^ 2) * ‖x‖ :=
    (D.le_opNorm x).trans (mul_le_mul_of_nonneg_right hder (norm_nonneg x))
  have hs : closedBall (0 : E₃) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  have hdiff := (hv.contDiffAt (isOpen_ball.mem_nhds (hs hxI))).differentiableAt (by simp)
  have herr : gradient u x - kelvinSecondOrderGradient v x =
      (-(‖x‖ ^ 3)⁻¹ * (v y - P)) • x +
      (‖x‖ ^ 3)⁻¹ • (toDual ℝ E₃).symm D -
      (2 * (‖x‖ ^ 5)⁻¹ * D x) • x := by
    rw [← hback.gradient_eq, gradient_kelvinTransform hx0 hdiff]
    simp only [kelvinSecondOrderGradient, P, D, sub_apply, map_sub, gradient, y]
    module
  rw [herr]
  calc
    _ ≤ ‖(-(‖x‖ ^ 3)⁻¹ * (v y - P)) • x‖ +
        ‖(‖x‖ ^ 3)⁻¹ • (toDual ℝ E₃).symm D‖ +
        ‖(2 * (‖x‖ ^ 5)⁻¹ * D x) • x‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = (‖x‖ ^ 3)⁻¹ * |v y - P| * ‖x‖ +
        (‖x‖ ^ 3)⁻¹ * ‖(toDual ℝ E₃).symm D‖ +
        2 * (‖x‖ ^ 5)⁻¹ * |D x| * ‖x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn.le 3)),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn.le 5)),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ (‖x‖ ^ 3)⁻¹ * (M / ‖x‖ ^ 3) * ‖x‖ +
        (‖x‖ ^ 3)⁻¹ * (M / ‖x‖ ^ 2) +
        2 * (‖x‖ ^ 5)⁻¹ * ((M / ‖x‖ ^ 2) * ‖x‖) * ‖x‖ := by
      gcongr
    _ = _ := by field_simp; ring

/-- Chapter 31, `lem:K-normalization`: the Hessian of a C² harmonic function
has zero trace, using the standard orthonormal coordinate vectors. -/
theorem kelvin_quadrupole_trace_zero {v : E₃ → ℝ}
    (hv : ContDiffAt ℝ 2 v 0) (hh : laplacianN v 0 = 0) :
    ∑ i : Fin 3, fderiv ℝ (fderiv ℝ v) 0
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) = 0 := by
  have hD := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcoord : ∀ i : Fin 3,
      poissonCoordinateDerivative i (poissonCoordinateDerivative i v) 0 =
        fderiv ℝ (fderiv ℝ v) 0 (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    intro i
    have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) 0)
    change fderiv ℝ (fun y => fderiv ℝ v y (EuclideanSpace.single i 1)) 0 _ = _
    rw [h.fderiv]
    simp
  simpa only [laplacianN, hcoord] using hh

/-- Chapter 31, `lem:K-normalization`: a capacitary potential has a smooth
Kelvin extension with a trace-free quadrupole and simultaneous second-order
value and gradient expansions. The hypotheses are those of `kelvin_expansion`. -/
theorem capacitary_second_order_expansion
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ (v : E₃ → ℝ) (r : ℝ), 0 < r ∧
      ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r) ∧
      EqOn v (kelvinTransform u) (ball 0 r \ {0}) ∧
      laplacianN v 0 = 0 ∧
      (∑ i : Fin 3, fderiv ℝ (fderiv ℝ v) 0
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) = 0 ∧
      ∃ R M : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
        |u x - kelvinSecondOrderModel v x| ≤ M / ‖x‖ ^ 4 ∧
        ‖gradient u x - kelvinSecondOrderGradient v x‖ ≤ M / ‖x‖ ^ 5 := by
  obtain ⟨v, hv, he, hharm⟩ := kelvin_smooth_extension hK hR₀ hKR hzero hu hh hb hinf
  have hr : 0 < 1 / R₀ := by positivity
  have hh0 := hharm 0 (mem_ball_self hr)
  have ht := kelvin_quadrupole_trace_zero
    ((hv.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr))).of_le (by simp)) hh0
  refine ⟨v, 1 / R₀, hr, hv, he, hh0, ht, ?_⟩
  obtain ⟨Rv, Mv, hRv, hvbound⟩ := kelvin_second_order_value hr hv he
  obtain ⟨Rg, Mg, _, hgbound⟩ := kelvin_second_order_gradient hr hv he
  refine ⟨max Rv Rg, max Mv Mg, hRv.trans_le (le_max_left _ _), ?_⟩
  intro x hx
  constructor
  · exact (hvbound x ((le_max_left _ _).trans hx)).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact (hgbound x ((le_max_right _ _).trans hx)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) (by positivity))

end LiquidDrop.CapacitaryK
