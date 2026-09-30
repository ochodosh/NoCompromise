module

public import NoCompromise.Elliptic.BoundaryHolderOdd
public import NoCompromise.Elliptic.BoundaryHolderLocalization
public import NoCompromise.Elliptic.FrozenDecayRegularity

@[expose] public section

/-!
# Genuine smooth frozen representatives across the flat boundary

The neighborhood depends only on ellipticity. The source is an arbitrary H¹
solution with its actual zero flat trace. Adapted reflection and interior
regularity produce a smooth representative which vanishes pointwise on the
flat face; neither smoothness nor reflected harmonicity is assumed.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

lemma boundaryFrozenReflection_last {k : ℕ}
    (A : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hn : inner ℝ (frozenSymmetricPart A (EuclideanSpace.single (Fin.last k) 1))
      (EuclideanSpace.single (Fin.last k) 1) ≠ 0)
    (x : EuclideanSpace ℝ (Fin (k + 1))) :
    boundaryFrozenReflection A (EuclideanSpace.single (Fin.last k) 1) x (Fin.last k) =
      -x (Fin.last k) := by
  have h := boundaryFrozenReflection_normal A (EuclideanSpace.single (Fin.last k) 1) x hn
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using h

lemma boundary_reflection_ae_comp {m : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin m))} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (n : EuclideanSpace ℝ (Fin m))
    (hn : inner ℝ (frozenSymmetricPart A n) n ≠ 0)
    {f g : EuclideanSpace ℝ (Fin m) → ℝ}
    (he : f =ᵐ[volume.restrict U] g)
    (hmap : MapsTo (boundaryFrozenReflection A n) V U) :
    (f ∘ boundaryFrozenReflection A n) =ᵐ[volume.restrict V]
      (g ∘ boundaryFrozenReflection A n) := by
  have h := (boundaryFrozenReflection_measurePreserving A n hn).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).mp he)
  filter_upwards [ae_restrict_of_ae h, ae_restrict_mem hV] with x hx hxV
  exact hx (hmap hxV)

/-- A frozen zero-Dirichlet solution has a genuine smooth representative through
the flat face, on an ellipticity-controlled neighborhood chosen before the data. -/
theorem boundary_frozen_smooth_representative {lam cap : ℝ}
    (hlam : 0 < lam) (hcap : 0 ≤ cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 64 ∧
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
          ∀ x ∈ ball 0 ρ, x (Fin.last 2) = 0 → v x = 0 := by
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
  refine ⟨ρ, hρ, (hρr.trans hrsmall).le, ?_⟩
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
  obtain ⟨v, hv, he, _⟩ := exists_frozen_smooth_representative (by norm_num : 3 < 4)
    isOpen_ball (hu.mono (subset_univ _)) (frozenSymmetricPart A) hp hlam
      (fun ξ => by rw [frozenSymmetricPart_inner]; exact hell ξ)
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
  refine ⟨w, hwc, ?_, ?_, ?_⟩
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

end LiquidDrop
