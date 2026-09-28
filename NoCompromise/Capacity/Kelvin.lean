import NoCompromise.Capacity.Flux
import NoCompromise.Elliptic.KelvinRemovable
import NoCompromise.Elliptic.NewtonianSchauderKernel

/-!
# Kelvin transformation of capacitary potentials

The inversion and Kelvin transform use the total inverse convention at zero.
All differential identities below explicitly exclude that point.
-/

noncomputable section
open Set Filter Metric MeasureTheory InnerProductSpace
open scoped Topology ENNReal NNReal Gradient RealInnerProductSpace
namespace LiquidDrop
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Blueprint `lem:kelvin`: inversion in the unit sphere. -/
def kelvinInversion (x : E₃) : E₃ := (‖x‖ ^ 2)⁻¹ • x

/-- Blueprint `lem:kelvin`: the three-dimensional Kelvin transform. -/
def kelvinTransform (u : E₃ → ℝ) (x : E₃) : ℝ := ‖x‖⁻¹ * u (kelvinInversion x)

/-- Blueprint `lem:kelvin`: the derivative of inversion, in explicit linear form. -/
lemma hasFDerivAt_kelvinInversion {x : E₃} (hx : x ≠ 0) :
    HasFDerivAt kelvinInversion
      ((‖x‖ ^ 2)⁻¹ • ContinuousLinearMap.id ℝ E₃ +
        ((-2 / ‖x‖ ^ 4) • innerSL ℝ x).smulRight x) x := by
  convert! (schauderNewton_hasFDerivAt_inv_norm_pow hx 1).smul
    (hasFDerivAt_id x) using 1

/-- Blueprint `lem:kelvin`: inversion is smooth away from zero. -/
lemma contDiffAt_kelvinInversion {x : E₃} (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) kelvinInversion x :=
  (((contDiffAt_id.norm ℝ hx).pow 2).inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).smul
    contDiffAt_id

/-- Blueprint `lem:kelvin`: a first coordinate derivative of the transform. -/
lemma poissonCoordinateDerivative_kelvinTransform {u : E₃ → ℝ} {x : E₃}
    (hx : x ≠ 0) (hu : DifferentiableAt ℝ u (kelvinInversion x)) (i : Fin 3) :
    poissonCoordinateDerivative i (kelvinTransform u) x =
      -(‖x‖ ^ 3)⁻¹ * x i * u (kelvinInversion x) +
      (‖x‖ ^ 3)⁻¹ * fderiv ℝ u (kelvinInversion x) (EuclideanSpace.single i 1) -
      2 * (‖x‖ ^ 5)⁻¹ * x i * fderiv ℝ u (kelvinInversion x) x := by
  have hd := (schauderNewton_hasFDerivAt_inv_norm_pow hx 0).mul
    (hu.hasFDerivAt.comp x (hasFDerivAt_kelvinInversion hx))
  simp only [Nat.reduceAdd, pow_one] at hd
  change HasFDerivAt (kelvinTransform u) (_ : E₃ →L[ℝ] ℝ) x at hd
  rw [poissonCoordinateDerivative, hd.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    map_add, map_smul, smul_eq_mul, Nat.cast_one, starRingEnd_apply, star_trivial,
    Function.comp_apply]
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  ring

/-- Blueprint `lem:kelvin`: the diagonal second coordinate derivative before
summing the trace. Only local twice continuous differentiability is required. -/
lemma poissonCoordinateDerivative_twice_kelvinTransform {u : E₃ → ℝ} {x : E₃}
    (hx : x ≠ 0) (hu : ContDiffAt ℝ 2 u (kelvinInversion x)) (i : Fin 3) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative i (kelvinTransform u)) x =
      (3 * (‖x‖ ^ 5)⁻¹ * (x i) ^ 2 - (‖x‖ ^ 3)⁻¹) * u (kelvinInversion x) -
      6 * (‖x‖ ^ 5)⁻¹ * x i * fderiv ℝ u (kelvinInversion x) (EuclideanSpace.single i 1) +
      (12 * (‖x‖ ^ 7)⁻¹ * (x i) ^ 2 - 2 * (‖x‖ ^ 5)⁻¹) *
        fderiv ℝ u (kelvinInversion x) x +
      (‖x‖ ^ 5)⁻¹ * fderiv ℝ (fderiv ℝ u) (kelvinInversion x)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) -
      2 * (‖x‖ ^ 7)⁻¹ * x i * fderiv ℝ (fderiv ℝ u) (kelvinInversion x)
        x (EuclideanSpace.single i 1) -
      2 * (‖x‖ ^ 7)⁻¹ * x i * fderiv ℝ (fderiv ℝ u) (kelvinInversion x)
        (EuclideanSpace.single i 1) x +
      4 * (‖x‖ ^ 9)⁻¹ * (x i) ^ 2 * fderiv ℝ (fderiv ℝ u) (kelvinInversion x) x x := by
  have hI := hasFDerivAt_kelvinInversion hx
  have hU := (hu.differentiableAt (by norm_num)).hasFDerivAt.comp x hI
  have hD := ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp x hI
  have hDi := hD.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)
  have hDx := hD.clm_apply (hasFDerivAt_id x)
  have h3 := schauderNewton_hasFDerivAt_inv_norm_pow hx 2
  have h5 := schauderNewton_hasFDerivAt_inv_norm_pow hx 4
  have hi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  have hd := ((h3.neg.mul hi).mul hU).add (h3.mul hDi) |>.sub
    (((h5.const_mul 2).mul hi).mul hDx)
  have he : poissonCoordinateDerivative i (kelvinTransform u) =ᶠ[𝓝 x]
      (fun y => -(‖y‖ ^ 3)⁻¹ * y i * u (kelvinInversion y) +
        (‖y‖ ^ 3)⁻¹ * fderiv ℝ u (kelvinInversion y) (EuclideanSpace.single i 1) -
        2 * (‖y‖ ^ 5)⁻¹ * y i * fderiv ℝ u (kelvinInversion y) y) := by
    filter_upwards [isOpen_ne.mem_nhds hx,
      hI.continuousAt (hu.eventually (by norm_num))] with y hy hyu
    change ContDiffAt ℝ 2 u (kelvinInversion y) at hyu
    exact poissonCoordinateDerivative_kelvinTransform hy (hyu.differentiableAt (by norm_num)) i
  simp only [Pi.mul_apply, Pi.neg_apply,
    Function.comp_apply, EuclideanSpace.coe_proj, id_eq, Nat.reduceAdd] at hd
  change HasFDerivAt (fun y : E₃ =>
      -(‖y‖ ^ 3)⁻¹ * y i * u (kelvinInversion y) +
        (‖y‖ ^ 3)⁻¹ * fderiv ℝ u (kelvinInversion y) (EuclideanSpace.single i 1) -
        2 * (‖y‖ ^ 5)⁻¹ * y i * fderiv ℝ u (kelvinInversion y) y)
      (_ : E₃ →L[ℝ] ℝ) x at hd
  rw [poissonCoordinateDerivative, he.fderiv_eq, hd.fderiv]
  simp only [add_apply, sub_apply, neg_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, zero_apply,
    ContinuousLinearMap.flip_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right,
    map_add, map_smul, smul_eq_mul, Nat.cast_ofNat,
    EuclideanSpace.coe_proj, starRingEnd_apply, star_trivial]
  have hn := norm_ne_zero_iff.mpr hx
  simp only [PiLp.single_apply, ite_true, map_zero, mul_one, zero_add]
  field_simp
  ring

private lemma kelvin_sum_coordinates (L : E₃ →L[ℝ] ℝ) (x : E₃) :
    (∑ i, x i * L (EuclideanSpace.single i 1)) = L x := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x)
  simpa only [map_sum, map_smul, smul_eq_mul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply] using h

private lemma kelvin_second_coordinate_of_contDiffAt {u : E₃ → ℝ} {x : E₃}
    (hu : ContDiffAt ℝ 2 u x) (i : Fin 3) :
    poissonCoordinateDerivative i (poissonCoordinateDerivative i u) x =
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have hD := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (EuclideanSpace.single i (1 : ℝ)) x)
  change fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x _ = _
  rw [h.fderiv]
  simp

/-- Blueprint `lem:kelvin`: the classical Kelvin Laplacian identity in three
dimensions, for a function that is C² near the inverted point. -/
theorem laplacianN_kelvinTransform {u : E₃ → ℝ} {x : E₃}
    (hx : x ≠ 0) (hu : ContDiffAt ℝ 2 u (kelvinInversion x)) :
    laplacianN (kelvinTransform u) x =
      (‖x‖ ^ 5)⁻¹ * laplacianN u (kelvinInversion x) := by
  let L := fderiv ℝ u (kelvinInversion x)
  let H := fderiv ℝ (fderiv ℝ u) (kelvinInversion x)
  have hsum : laplacianN (kelvinTransform u) x =
      (3 * (‖x‖ ^ 5)⁻¹ * (∑ i, (x i) ^ 2) - 3 * (‖x‖ ^ 3)⁻¹) *
        u (kelvinInversion x) -
      6 * (‖x‖ ^ 5)⁻¹ * (∑ i, x i * L (EuclideanSpace.single i 1)) +
      (12 * (‖x‖ ^ 7)⁻¹ * (∑ i, (x i) ^ 2) - 6 * (‖x‖ ^ 5)⁻¹) * L x +
      (‖x‖ ^ 5)⁻¹ * laplacianN u (kelvinInversion x) -
      2 * (‖x‖ ^ 7)⁻¹ * (∑ i, x i * H x (EuclideanSpace.single i 1)) -
      2 * (‖x‖ ^ 7)⁻¹ * (∑ i, x i * H (EuclideanSpace.single i 1) x) +
      4 * (‖x‖ ^ 9)⁻¹ * (∑ i, (x i) ^ 2) * H x x := by
    simp only [laplacianN, poissonCoordinateDerivative_twice_kelvinTransform hx hu,
      kelvin_second_coordinate_of_contDiffAt hu, Fin.sum_univ_three, L, H]
    ring
  rw [hsum, ← EuclideanSpace.real_norm_sq_eq,
    kelvin_sum_coordinates L x, kelvin_sum_coordinates (H x) x]
  have hflip := kelvin_sum_coordinates (H.flip x) x
  simp only [ContinuousLinearMap.flip_apply] at hflip
  rw [hflip]
  have hn := norm_ne_zero_iff.mpr hx
  field_simp
  ring

/-- Blueprint `lem:kelvin`: the gradient transformation formula, with genuine
Fréchet gradients and only differentiability at the inverted point. -/
lemma gradient_kelvinTransform {u : E₃ → ℝ} {x : E₃} (hx : x ≠ 0)
    (hu : DifferentiableAt ℝ u (kelvinInversion x)) :
    gradient (kelvinTransform u) x =
      (-(‖x‖ ^ 3)⁻¹ * u (kelvinInversion x)) • x +
      (‖x‖ ^ 3)⁻¹ • gradient u (kelvinInversion x) -
      (2 * (‖x‖ ^ 5)⁻¹ * fderiv ℝ u (kelvinInversion x) x) • x := by
  apply PiLp.ext
  intro i
  rw [← poissonCoordinateDerivative_eq_gradient,
    poissonCoordinateDerivative_kelvinTransform hx hu i]
  simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
    gradient_apply_eq_fderiv_single]
  ring

/-- Blueprint `lem:kelvin`: continuity of the original potential gives its
actual smooth representative on the exterior. -/
theorem capacitary_potential_contDiffOn
    {K : Set E₃} (hK : IsCompact K) {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ :=
  hh.contDiffOn_of_continuous (by decide) hK.isClosed.isOpen_compl hu.continuousOn

/-- Blueprint `lem:kelvin`: smoothness on the region outside the enclosing
radius, in the requested `ℕ∞` convention. -/
theorem capacitary_potential_contDiffOn_exterior
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hKR : K ⊆ closedBall 0 R₀)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) u {x | R₀ < ‖x‖} := by
  apply (capacitary_potential_contDiffOn hK hu hh).mono
  intro x hx hxK
  have hxR : ‖x‖ ≤ R₀ := by simpa only [mem_closedBall, dist_zero_right] using hKR hxK
  exact (not_lt_of_ge hxR) hx

/-- Blueprint `lem:kelvin`: the norm of the inverted point. -/
lemma norm_kelvinInversion (x : E₃) : ‖kelvinInversion x‖ = ‖x‖⁻¹ := by
  by_cases hx : x = 0
  · simp [hx, kelvinInversion]
  · have hn := norm_ne_zero_iff.mpr hx
    rw [kelvinInversion, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp

/-- Blueprint `lem:kelvin`: inversion is involutive, including under the total
inverse convention at zero. -/
lemma kelvinInversion_involutive (x : E₃) : kelvinInversion (kelvinInversion x) = x := by
  by_cases hx : x = 0
  · simp [hx, kelvinInversion]
  · have hn := norm_ne_zero_iff.mpr hx
    rw [kelvinInversion, norm_kelvinInversion, kelvinInversion, smul_smul]
    have he : ((‖x‖⁻¹) ^ 2)⁻¹ * (‖x‖ ^ 2)⁻¹ = 1 := by field_simp
    rw [he, one_smul]

/-- Blueprint `lem:kelvin`: Kelvin transformation is involutive away from zero. -/
lemma kelvinTransform_involutive (u : E₃ → ℝ) {x : E₃} (hx : x ≠ 0) :
    kelvinTransform (kelvinTransform u) x = u x := by
  simp only [kelvinTransform, norm_kelvinInversion, kelvinInversion_involutive, inv_inv]
  rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx), one_mul]

/-- Blueprint `lem:kelvin`: the small punctured ball inverts into the exterior
of every set contained in the enclosing ball. -/
lemma kelvinInversion_mem_compl {K : Set E₃} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) {x : E₃} (hx : x ∈ ball 0 (1 / R₀) \ {0}) :
    kelvinInversion x ∈ Kᶜ := by
  have hx0 : x ≠ 0 := hx.2
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hlt : ‖x‖ < 1 / R₀ := by simpa only [mem_ball, dist_zero_right] using hx.1
  have hlarge : R₀ < ‖kelvinInversion x‖ := by
    rw [norm_kelvinInversion, inv_eq_one_div]
    apply (lt_div_iff₀ hn).mpr
    have := (lt_div_iff₀ hR₀).mp hlt
    nlinarith
  intro hmem
  have hsmall : ‖kelvinInversion x‖ ≤ R₀ := by
    simpa only [mem_closedBall, dist_zero_right] using hKR hmem
  exact (not_lt_of_ge hsmall) hlarge

/-- Blueprint `lem:kelvin`: smoothness of the Kelvin transform away from its
puncture. -/
lemma contDiffOn_kelvinTransform {K : Set E₃} {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hK : IsClosed K) {u : E₃ → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Kᶜ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kelvinTransform u) (ball 0 (1 / R₀) \ {0}) := by
  intro x hx
  have hx0 : x ≠ 0 := hx.2
  have hu' := hu.contDiffAt (hK.isOpen_compl.mem_nhds (kelvinInversion_mem_compl hR₀ hKR hx))
  exact (((contDiffAt_id.norm ℝ hx0).inv (norm_ne_zero_iff.mpr hx0)).mul
    (hu'.comp x (contDiffAt_kelvinInversion hx0))).contDiffWithinAt

/-- Blueprint `lem:kelvin`: reciprocal decay makes the Kelvin transform
uniformly bounded by the enclosing radius on the punctured ball. -/
theorem abs_kelvinTransform_le
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∀ x ∈ ball 0 (1 / R₀) \ {0}, |kelvinTransform u x| ≤ R₀ := by
  intro x hx
  have hbound := abs_le_div_norm_of_capacitary_potential hK hR₀ hKR hzero hu hh hb hinf
    (kelvinInversion x) (kelvinInversion_mem_compl hR₀ hKR hx)
  rw [kelvinTransform, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  apply (mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (norm_nonneg x))).trans_eq
  rw [norm_kelvinInversion]
  have hn := norm_ne_zero_iff.mpr (show x ≠ 0 from hx.2)
  field_simp

/-- Blueprint `lem:kelvin`: the classical equation of a smooth function on an
open set implies its distributional equation, without a global smoothness assumption. -/
lemma kelvin_hasDistributionalLaplacianOn_of_contDiffOn {U : Set E₃} (hU : IsOpen U)
    {u : E₃ → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U)
    (hh : ∀ x ∈ U, laplacianN u x = 0) :
    HasDistributionalLaplacianOn u (fun _ => 0) U := by
  refine ⟨hu.continuousOn.locallyIntegrableOn hU.measurableSet, locallyIntegrableOn_const 0, ?_⟩
  intro φ hφ hcφ hsφ
  obtain ⟨w, hw, he⟩ := exists_global_contDiff_eq_near_compact hU hcφ hsφ hu
  have heq : (∫ x in U, u x * laplacianN φ x) = ∫ x, w x * laplacianN φ x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := U) (f := fun x => w x * laplacianN φ x) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ
          (tsupport_laplacianN_subset φ ht))), mul_zero])]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ tsupport φ
    · rw [(he x hx).self_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport
        (fun ht => hx (tsupport_laplacianN_subset φ ht)), mul_zero, mul_zero]
  rw [heq, sobolevChain_integral_laplacianN_comm (hw.of_le (by simp)) hφ hcφ]
  simp only [zero_mul, integral_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  change φ x * laplacianN w x = 0
  by_cases hx : x ∈ tsupport φ
  · rw [laplacianN_congr_nhds (he x hx), hh x (hsφ hx), mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Blueprint `lem:kelvin`: continuous weakly harmonic functions satisfy the
classical equation pointwise on their open domain. -/
lemma kelvin_laplacianN_eq_zero_of_distributional {U : Set E₃} (hU : IsOpen U)
    {u : E₃ → ℝ} (hu : ContinuousOn u U)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) U) :
    ∀ x ∈ U, laplacianN u x = 0 := by
  obtain ⟨v, hv, he, hz, _⟩ := hh.exists_smooth_mean_value (by decide) hU
    (fun _ hx => exists_ball_memLp_two_of_continuousOn hU hu hx)
  have hp : EqOn v u U := Measure.eqOn_open_of_ae_eq he hU hv.continuousOn hu
  intro x hx
  have hn : v =ᶠ[𝓝 x] u := Filter.eventually_of_mem (hU.mem_nhds hx) (fun _ hy => hp hy)
  rw [← laplacianN_congr_nhds hn]
  exact hz x hx

/-- Blueprint `lem:kelvin`: the Kelvin transform of a capacitary potential
extends to a smooth harmonic function on the full ball around the origin. -/
theorem kelvin_smooth_extension
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ v : E₃ → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 (1 / R₀)) ∧
      EqOn v (kelvinTransform u) (ball 0 (1 / R₀) \ {0}) ∧
      (∀ x ∈ ball 0 (1 / R₀), laplacianN v x = 0) := by
  have hs := capacitary_potential_contDiffOn hK hu hh
  have hq := contDiffOn_kelvinTransform hR₀ hKR hK.isClosed hs
  have hz := kelvin_laplacianN_eq_zero_of_distributional hK.isClosed.isOpen_compl
    hu.continuousOn hh
  have hqh : HasDistributionalLaplacianOn (kelvinTransform u) (fun _ => 0)
      (ball 0 (1 / R₀) \ {0}) := by
    apply kelvin_hasDistributionalLaplacianOn_of_contDiffOn
      (isOpen_ball.sdiff isClosed_singleton) hq
    intro x hx
    have hxK := kelvinInversion_mem_compl hR₀ hKR hx
    rw [laplacianN_kelvinTransform hx.2
      ((hs.contDiffAt (hK.isClosed.isOpen_compl.mem_nhds hxK)).of_le (by simp)),
      hz _ hxK, mul_zero]
  apply kelvin_removable isOpen_ball isBounded_ball hqh hq.continuousOn
  exact ⟨R₀, abs_kelvinTransform_le hK hR₀ hKR hzero hu hh hb hinf⟩

/-- Blueprint `lem:kelvin`: quantitative first-order Kelvin estimates from a
local value estimate and a bound on the derivative at the inverted point. -/
lemma kelvin_expansion_estimates {v : E₃ → ℝ} {x : E₃} (hx : x ≠ 0)
    (hv : DifferentiableAt ℝ v (kelvinInversion x)) {a M : ℝ}
    (hval : |v (kelvinInversion x) - a| ≤ M / ‖x‖)
    (hder : ‖fderiv ℝ v (kelvinInversion x)‖ ≤ M) :
    |kelvinTransform v x - a / ‖x‖| ≤ M / ‖x‖ ^ 2 ∧
      ‖gradient (kelvinTransform v) x + (a / ‖x‖ ^ 3) • x‖ ≤ 4 * M / ‖x‖ ^ 3 := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hgrad : ‖gradient v (kelvinInversion x)‖ ≤ M := by
    change ‖(toDual ℝ E₃).symm (fderiv ℝ v (kelvinInversion x))‖ ≤ M
    simpa only [LinearIsometryEquiv.norm_map] using hder
  have hlin : |fderiv ℝ v (kelvinInversion x) x| ≤ M * ‖x‖ :=
    ((fderiv ℝ v (kelvinInversion x)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hder (norm_nonneg x))
  constructor
  · have he : kelvinTransform v x - a / ‖x‖ =
        ‖x‖⁻¹ * (v (kelvinInversion x) - a) := by
      dsimp [kelvinTransform]
      ring
    rw [he, abs_mul, abs_of_nonneg (inv_nonneg.mpr hn.le)]
    calc
      _ ≤ ‖x‖⁻¹ * (M / ‖x‖) := mul_le_mul_of_nonneg_left hval (inv_nonneg.mpr hn.le)
      _ = _ := by ring
  · have he : gradient (kelvinTransform v) x + (a / ‖x‖ ^ 3) • x =
        (-(‖x‖ ^ 3)⁻¹ * (v (kelvinInversion x) - a)) • x +
        (‖x‖ ^ 3)⁻¹ • gradient v (kelvinInversion x) -
        (2 * (‖x‖ ^ 5)⁻¹ * fderiv ℝ v (kelvinInversion x) x) • x := by
      rw [gradient_kelvinTransform hx hv]
      simp only [div_eq_mul_inv]
      module
    rw [he]
    calc
      _ ≤ ‖(-(‖x‖ ^ 3)⁻¹ * (v (kelvinInversion x) - a)) • x‖ +
          ‖(‖x‖ ^ 3)⁻¹ • gradient v (kelvinInversion x)‖ +
          ‖(2 * (‖x‖ ^ 5)⁻¹ * fderiv ℝ v (kelvinInversion x) x) • x‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = (‖x‖ ^ 3)⁻¹ * |v (kelvinInversion x) - a| * ‖x‖ +
          (‖x‖ ^ 3)⁻¹ * ‖gradient v (kelvinInversion x)‖ +
          2 * (‖x‖ ^ 5)⁻¹ * |fderiv ℝ v (kelvinInversion x) x| * ‖x‖ := by
        simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
          abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn.le 3)),
          abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hn.le 5)),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (‖x‖ ^ 3)⁻¹ * (M / ‖x‖) * ‖x‖ + (‖x‖ ^ 3)⁻¹ * M +
          2 * (‖x‖ ^ 5)⁻¹ * (M * ‖x‖) * ‖x‖ := by
        gcongr
      _ = _ := by field_simp; ring

/-- Blueprint `lem:kelvin`: a smooth Kelvin extension gives the value and
gradient expansions with a single constant and a positive exterior radius. -/
theorem kelvin_expansion_of_smooth_extension {u v : E₃ → ℝ} {r : ℝ} (hr : 0 < r)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 r))
    (he : EqOn v (kelvinTransform u) (ball 0 r \ {0})) :
    ∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      |u x - v 0 / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (v 0 / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 := by
  have hs : closedBall (0 : E₃) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (half_lt_self hr)
  have hvD := hv.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E₃) (r / 2)).exists_bound_of_continuousOn
    (hvD.mono hs)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self (half_pos hr).le))
  have hdiff : ∀ z ∈ ball (0 : E₃) r, DifferentiableAt ℝ v z := fun z hz =>
    (hv.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by simp)
  have hval : ∀ z ∈ closedBall (0 : E₃) (r / 2), |v z - v 0| ≤ M * ‖z‖ := by
    intro z hz
    simpa only [Real.norm_eq_abs, sub_zero] using
      Convex.norm_image_sub_le_of_norm_fderiv_le (fun y hy => hdiff y (hs hy)) hM
        (convex_closedBall (0 : E₃) (r / 2))
        (mem_closedBall_self (half_pos hr).le) hz
  refine ⟨2 / r, 4 * M, by positivity, ?_⟩
  intro x hx
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
  obtain ⟨hvbound, hgbound⟩ := kelvin_expansion_estimates hx0 (hdiff _ (hs hxI))
    hvalue (hM _ hxI)
  rw [hback.self_of_nhds] at hvbound
  rw [hback.gradient_eq] at hgbound
  exact ⟨hvbound.trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)), hgbound⟩

/-- Blueprint `lem:kelvin`: the monopole value expansion and differentiated
remainder for a capacitary potential, with the hypotheses of `potential_decay`. -/
theorem kelvin_expansion
    {K : Set E₃} (hK : IsCompact K) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hKR : K ⊆ closedBall 0 R₀) (hzero : (0 : E₃) ∈ interior K)
    {u : E₃ → ℝ} (hu : Continuous u)
    (hh : HasDistributionalLaplacianOn u (fun _ => 0) Kᶜ)
    (hb : ∀ x ∈ K, u x = 1) (hinf : Tendsto u (cocompact E₃) (𝓝 0)) :
    ∃ Cinf : ℝ, ∃ R C' : ℝ, 0 < R ∧ ∀ x : E₃, R ≤ ‖x‖ →
      |u x - Cinf / ‖x‖| ≤ C' / ‖x‖ ^ 2 ∧
      ‖gradient u x + (Cinf / ‖x‖ ^ 3) • x‖ ≤ C' / ‖x‖ ^ 3 := by
  obtain ⟨v, hv, he, _⟩ := kelvin_smooth_extension hK hR₀ hKR hzero hu hh hb hinf
  exact ⟨v 0, kelvin_expansion_of_smooth_extension (by positivity) hv he⟩

end LiquidDrop
