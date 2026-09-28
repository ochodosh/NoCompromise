import NoCompromise.Elliptic.BoundaryHolderSymmetrization
import NoCompromise.Elliptic.BoundaryHolderInterior
import NoCompromise.Elliptic.BoundaryHolderEnergy

/-!
# Quantitative derivatives of a frozen boundary solution

For every positive derivative order, genuine reflected regularity gives a
smooth representative through the flat face whose derivative is controlled
only by the original gradient L² norm. The radius and constant are chosen
before the coefficient and solution.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem boundary_frozen_derivative_representative {j : ℕ} {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 64 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
        HasH1GradientOn f G (ball 0 1 ∩ {x | 0 < x (Fin.last 2)}) →
        HasZeroFlatTraceOn f G (ball 0 1) →
        IsWeakDivergenceEquationOn (fun _ => A) G (fun _ => 0)
          (ball 0 1 ∩ {x | 0 < x (Fin.last 2)}) →
        (∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ) → ‖A‖ ≤ cap →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ (⊤ : ℕ∞) v (ball 0 ρ) ∧
          v =ᵐ[volume.restrict (ball 0 ρ ∩ {x | 0 < x (Fin.last 2)})] f ∧
          gradient v =ᵐ[volume.restrict (ball 0 ρ ∩ {x | 0 < x (Fin.last 2)})] G ∧
          (∀ x ∈ ball 0 ρ, x (Fin.last 2) = 0 → v x = 0) ∧
          ∀ x ∈ ball 0 ρ, ‖iteratedFDeriv ℝ (j + 1) v x‖ ≤
            C * lpNorm G 2 (volume.restrict (ball 0 1 ∩ {x | 0 < x (Fin.last 2)})) := by
  let M : ℝ := 1 + 2 * cap / lam
  have hM1 : 1 ≤ M := by
    have h : 0 ≤ 2 * cap / lam := by positivity
    dsimp [M]
    linarith
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  let r : ℝ := (128 * M)⁻¹
  let ρ : ℝ := r / (2 * M)
  have hr : 0 < r := by dsimp [r]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hMr : M * r = 1 / 128 := by dsimp [r]; field_simp
  have hrsmall : r < 1 / 64 := by nlinarith
  have hρr : ρ < r := by
    apply (div_lt_iff₀ (by positivity : 0 < 2 * M)).mpr
    nlinarith
  have hMρ : M * ρ = r / 2 := by dsimp [ρ]; field_simp
  have hρhalf : ρ ≤ r / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * M)).mpr
    nlinarith
  obtain ⟨B, hB, hder⟩ := boundary_frozen_derivative_ball_bound
    (k := j) (by norm_num : 3 < 4) hr hlam hcap
  let C := (1 / 2 : ℝ) * (1 + M ^ (j + 1)) * B * Real.sqrt (2 + 2 * M ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨ρ, hρ, (hρr.trans hrsmall).le, C, hC, ?_⟩
  intro A f G hf hT hw hell hb
  let n : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (Fin.last 2) 1
  have hnormn : ‖n‖ = 1 := by simp [n]
  have hβ : 0 < inner ℝ (frozenSymmetricPart A n) n := by
    rw [frozenSymmetricPart_inner]
    have h := hell n
    rw [hnormn] at h
    nlinarith
  let R := boundaryFrozenReflectionEquiv A n hβ.ne'
  have hbound : ‖boundaryFrozenReflection A n‖ ≤ M :=
    norm_boundaryFrozenReflection_le A n hnormn hlam hcap hell hb
  have hRx (x : EuclideanSpace ℝ (Fin 3)) : ‖R x‖ ≤ M * ‖x‖ :=
    ((boundaryFrozenReflection A n).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hbound (norm_nonneg x))
  have hmapr : MapsTo (boundaryFrozenReflection A n) (ball 0 r)
      (ball 0 (1 / 64 : ℝ)) := by
    intro x hx
    have hx' : ‖x‖ < r := by simpa only [mem_ball, dist_zero_right] using hx
    change dist (R x) 0 < 1 / 64
    rw [dist_zero_right]
    exact (hRx x).trans_lt ((mul_lt_mul_of_pos_left hx' hM).trans (by rw [hMr]; norm_num))
  have hmapρ : MapsTo (boundaryFrozenReflection A n) (ball 0 ρ) (ball 0 r) := by
    intro x hx
    have hx' : ‖x‖ < ρ := by simpa only [mem_ball, dist_zero_right] using hx
    change dist (R x) 0 < r
    rw [dist_zero_right]
    exact (hRx x).trans_lt ((mul_lt_mul_of_pos_left hx' hM).trans
      (by rw [hMρ]; exact half_lt_self hr))
  let f₀ := boundaryHolderZeroFunction f
  let G₀ := boundaryHolderZeroGradient f G
  let u := fun x => f₀ x - f₀ (R x)
  let H := fun x => G₀ x - R.toContinuousLinearMap.adjoint (G₀ (R x))
  have hzero : HasH1GradientOn f₀ G₀ univ := hf.boundary_zero_extension_ball hT
  have hu : HasH1GradientOn u H univ := hzero.boundary_odd_extension A n hβ.ne'
  have hp : IsWeakDivergenceEquationOn (fun _ => frozenSymmetricPart A) H
      (fun _ => 0) (ball 0 r) :=
    hzero.boundary_odd_weak_equation isOpen_ball
      (fun x hx => boundaryHolderZeroGradient_eq_zero f G hx) A hβ.ne'
      hw.boundary_localized (ball_subset_ball hrsmall.le) hmapr
  have henergy := boundary_odd_gradient_energy hf hT A n hβ.ne' hbound hrsmall.le hmapr
  change (∫ x in ball 0 r, ‖H x‖ ^ 2) ≤
    (2 + 2 * M ^ 2) * (∫ x in ball 0 1 ∩ {x | 0 < x (Fin.last 2)}, ‖G x‖ ^ 2) at henergy
  have hLp : lpNorm H 2 (volume.restrict (ball 0 r)) ≤
      Real.sqrt (2 + 2 * M ^ 2) *
        lpNorm G 2 (volume.restrict (ball 0 1 ∩ {x | 0 < x (Fin.last 2)})) := by
    rw [lpNorm_two_eq_sqrt_integral_norm_sq (hu.mono (subset_univ _)).memLp_gradient,
      lpNorm_two_eq_sqrt_integral_norm_sq hf.memLp_gradient]
    exact (Real.sqrt_le_sqrt henergy).trans_eq (Real.sqrt_mul (by positivity) _)
  obtain ⟨v, hv, he, _⟩ := exists_frozen_smooth_representative (by norm_num : 3 < 4)
    isOpen_ball (hu.mono (subset_univ _)) (frozenSymmetricPart A) hp hlam
      (fun ξ => by rw [frozenSymmetricPart_inner]; exact hell ξ)
  have hderv := hder (frozenSymmetricPart A) v H
    ((hu.mono (subset_univ _)).congr_ae he.symm EventuallyEq.rfl) hp
    (fun ξ => by rw [frozenSymmetricPart_inner]; exact hell ξ)
    ((norm_frozenSymmetricPart_le A).trans hb) hv
  have hmapρhalf : MapsTo R (ball 0 ρ) (ball 0 (r / 2)) := by
    intro x hx
    have hx' : ‖x‖ < ρ := by simpa only [mem_ball, dist_zero_right] using hx
    change dist (R x) 0 < r / 2
    rw [dist_zero_right]
    exact (hRx x).trans_lt ((mul_lt_mul_of_pos_left hx' hM).trans_eq hMρ)
  let w := fun x => (1 / 2 : ℝ) * (v x - v (R x))
  have hwc : ContDiffOn ℝ (⊤ : ℕ∞) w (ball 0 ρ) :=
    contDiffOn_const.mul ((hv.mono (ball_subset_ball hρr.le)).sub
      (hv.comp R.contDiff.contDiffOn hmapρ))
  have her := boundary_reflection_ae_comp isOpen_ball.measurableSet isOpen_ball.measurableSet
    A n hβ.ne' he hmapρ
  have heρ := ae_mono (Measure.restrict_mono (ball_subset_ball hρr.le) le_rfl) he
  have hwu : w =ᵐ[volume.restrict (ball 0 ρ)] u := by
    filter_upwards [heρ, her] with x hx hy
    change v x = u x at hx
    change v (R x) = u (R x) at hy
    dsimp only [w]
    rw [hx, hy]
    change (1 / 2 : ℝ) * ((f₀ x - f₀ (R x)) - (f₀ (R x) - f₀ (R (R x)))) = _
    have hRR : R (R x) = x := boundaryFrozenReflection_involutive A n hβ.ne' x
    rw [hRR]
    dsimp only [u]
    ring
  have hwgrad : gradient w =ᵐ[volume.restrict (ball 0 ρ)] H :=
    (hasWeakGradientOn_of_contDiffOn isOpen_ball (hwc.of_le (by simp))).unique isOpen_ball
      ((hu.mono (subset_univ _)).toHasWeakGradientOn.congr_ae hwu.symm EventuallyEq.rfl)
  have hsmall : ball (0 : EuclideanSpace ℝ (Fin 3)) ρ ⊆ ball 0 (1 / 64 : ℝ) :=
    ball_subset_ball (hρr.trans hrsmall).le
  have heuf (x) (hx : x ∈ ball 0 ρ) (hxu : 0 < x (Fin.last 2)) :
      u x = f x ∧ H x = G x := by
    have hRlower : R x (Fin.last 2) ≤ 0 := by
      change boundaryFrozenReflection A n x (Fin.last 2) ≤ 0
      rw [boundaryFrozenReflection_last A hβ.ne']
      linarith
    have hfR : f₀ (R x) = 0 := by
      simp only [f₀, boundaryHolderZeroFunction, indicator_apply, mem_ofPred_eq,
        not_lt_of_ge hRlower, ↓reduceIte]
    have hGR : G₀ (R x) = 0 := boundaryHolderZeroGradient_eq_zero f G hRlower
    change f₀ x - f₀ (R x) = f x ∧ G₀ x - R.toContinuousLinearMap.adjoint (G₀ (R x)) = G x
    rw [hfR, hGR, map_zero, sub_zero, sub_zero]
    exact ⟨boundaryHolderZeroFunction_eq f (hsmall hx) hxu,
      boundaryHolderZeroGradient_eq f G (hsmall hx) hxu⟩
  refine ⟨w, hwc, ?_, ?_, ?_, ?_⟩
  · filter_upwards [ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hwu,
      ae_restrict_mem (isOpen_ball.inter boundary_holder_open_upper).measurableSet] with x hx hxU
    exact hx.trans (heuf x hxU.1 hxU.2).1
  · filter_upwards [ae_mono (Measure.restrict_mono inter_subset_left le_rfl) hwgrad,
      ae_restrict_mem (isOpen_ball.inter boundary_holder_open_upper).measurableSet] with x hx hxU
    exact hx.trans (heuf x hxU.1 hxU.2).2
  · intro x _ hx
    have hi : inner ℝ n x = 0 := by
      simp only [n, EuclideanSpace.inner_single_left, hx, mul_zero]
    change (1 / 2 : ℝ) * (v x - v (boundaryFrozenReflection A n x)) = 0
    rw [boundaryFrozenReflection_eq_self A n x hi, sub_self, mul_zero]
  · intro x hx
    have hxhalf : x ∈ ball 0 (r / 2) := ball_subset_ball hρhalf hx
    have hxfull : x ∈ ball 0 r := ball_subset_ball (half_le_self hr.le) hxhalf
    have hRxhalf : R x ∈ ball 0 (r / 2) := hmapρhalf hx
    have hRxfull : R x ∈ ball 0 r := ball_subset_ball (half_le_self hr.le) hRxhalf
    have hdx : ContDiffAt ℝ (j + 1) v x :=
      (hv.of_le (by simp)).contDiffAt (isOpen_ball.mem_nhds hxfull)
    have hdRx : ContDiffAt ℝ (j + 1) v (R x) :=
      (hv.of_le (by simp)).contDiffAt (isOpen_ball.mem_nhds hRxfull)
    have hpow : ‖R.toContinuousLinearMap‖ ^ (j + 1) ≤ M ^ (j + 1) :=
      pow_le_pow_left₀ (norm_nonneg _) hbound _
    calc
      _ ≤ (1 / 2 : ℝ) * (‖iteratedFDeriv ℝ (j + 1) v x‖ +
          ‖iteratedFDeriv ℝ (j + 1) v (R x)‖ * ‖R.toContinuousLinearMap‖ ^ (j + 1)) :=
        boundary_half_odd_derivative_bound R hdx hdRx
      _ ≤ (1 / 2 : ℝ) * (B * lpNorm H 2 (volume.restrict (ball 0 r)) +
          B * lpNorm H 2 (volume.restrict (ball 0 r)) * M ^ (j + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact add_le_add (hderv x hxhalf) (mul_le_mul (hderv (R x) hRxhalf)
          hpow (by positivity) (mul_nonneg hB.le lpNorm_nonneg))
      _ = ((1 / 2 : ℝ) * (1 + M ^ (j + 1)) * B) *
          lpNorm H 2 (volume.restrict (ball 0 r)) := by ring
      _ ≤ ((1 / 2 : ℝ) * (1 + M ^ (j + 1)) * B) *
          (Real.sqrt (2 + 2 * M ^ 2) *
            lpNorm G 2 (volume.restrict (ball 0 1 ∩ {x | 0 < x (Fin.last 2)}))) :=
        mul_le_mul_of_nonneg_left hLp (by positivity)
      _ = _ := by dsimp [C]; ring

end LiquidDrop
