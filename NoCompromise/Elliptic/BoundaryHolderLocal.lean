import NoCompromise.Elliptic.BoundaryHolderRepresentative
import NoCompromise.Elliptic.BoundaryHolderNormalization
import NoCompromise.Elliptic.BoundaryHolderSimilarity

/-! Uniform local C¹,α representatives across every point of the smaller flat
disk. All representatives agree almost everywhere with one common raw odd
function, so their compatibility is genuine and requires no chosen trace values. -/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

theorem boundary_holder_local_representatives {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        ∀ z : EuclideanSpace ℝ (Fin 2), ‖graphAppendN z 0‖ < 3 / 4 →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 1 v (ball (graphAppendN z 0) (1 / 262144 : ℝ)) ∧
          v =ᵐ[volume.restrict (ball (graphAppendN z 0) (1 / 262144 : ℝ))] boundaryRawOdd u ∧
          (∀ x ∈ ball (graphAppendN z 0) (1 / 262144 : ℝ), ‖gradient v x‖ ≤ P) ∧
          (∀ x ∈ ball (graphAppendN z 0) (1 / 262144 : ℝ),
            ∀ y ∈ ball (graphAppendN z 0) (1 / 262144 : ℝ),
              ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          ∀ x ∈ ball (graphAppendN z 0) (1 / 262144 : ℝ),
            x (Fin.last 2) = 0 → v x = 0 := by
  obtain ⟨C₀, P₀, hC₀, hP₀, hb⟩ := boundary_holder_c1_representative_origin
    ha ha1 hlam hcap hHA hHG (show 0 ≤ 512 * M by positivity)
  refine ⟨512 * C₀ * (512 : ℝ) ^ a, 512 * P₀, by positivity, by positivity, ?_⟩
  intro u F G A h z hz
  let c := graphAppendN z 0
  have hδ : (0 : ℝ) < 1 / 512 := by norm_num
  let e := frozenBallScaling c hδ
  obtain ⟨v, hv, he, _, _, hgrad, hholder, hflat⟩ := hb _ _ _ _
    (h.normalize ha.le hHA hHG z hz)
  have hmap : MapsTo e.symm (ball c (1 / 262144 : ℝ)) (ball 0 (1 / 512 : ℝ)) := by
    intro x hx
    apply (frozenBallScaling_mem_ball_iff c (e.symm x) hδ (1 / 512)).mp
    change e (e.symm x) ∈ ball c ((1 / 512 : ℝ) * (1 / 512))
    simpa only [e.apply_symm_apply, show (1 / 512 : ℝ) * (1 / 512) = 1 / 262144 by norm_num]
      using hx
  have hec : ContDiff ℝ 1 e.symm := by
    rw [show e.symm = (frozenBallScaling c hδ).symm from rfl, frozenBallScaling_symm_coe]
    exact (contDiff_id.sub contDiff_const).const_smul (1 / 512 : ℝ)⁻¹
  have hder (x) (hx : x ∈ ball c (1 / 262144 : ℝ)) :
      gradient (v ∘ e.symm) x = (512 : ℝ) • gradient v (e.symm x) := by
    have hh := quasilinear_gradient_comp_ballScaling_symm_at c x hδ
      ((hv.contDiffAt (isOpen_ball.mem_nhds (hmap hx))).differentiableAt one_ne_zero)
    change gradient (v ∘ (frozenBallScaling c hδ).symm) x =
      (512 : ℝ) • gradient v ((frozenBallScaling c hδ).symm x)
    simpa only [one_div, inv_inv] using hh
  have heRaw : v =ᵐ[volume.restrict (ball 0 (1 / 512 : ℝ))]
      boundaryRawOdd (u ∘ e) := by
    filter_upwards [he, ae_restrict_mem measurableSet_ball] with x hx hxB
    exact hx.trans (boundaryOddFunction_eq_raw (u ∘ e)
      (ball_subset_ball (by norm_num : (1 / 512 : ℝ) ≤ 1 / 64) hxB))
  have heBack := boundary_ballScaling_pullback_ae c hδ heRaw
  have heBack' : (v ∘ e.symm) =ᵐ[volume.restrict (ball c (1 / 262144 : ℝ))]
      boundaryRawOdd u := by
    norm_num only [show (1 / 512 : ℝ) * (1 / 512) = 1 / 262144 by norm_num] at heBack
    filter_upwards [heBack] with x hx
    change v (e.symm x) = _
    exact hx.trans (by
      change boundaryRawOdd (u ∘ frozenBallScaling (graphAppendN z 0) hδ) (e.symm x) = _
      rw [boundaryRawOdd_comp_ballScaling]
      change boundaryRawOdd u (e (e.symm x)) = _
      rw [e.apply_symm_apply])
  refine ⟨v ∘ e.symm, hv.comp hec.contDiffOn hmap, heBack', ?_, ?_, ?_⟩
  · intro x hx
    rw [hder x hx, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 512)]
    exact mul_le_mul_of_nonneg_left (hgrad _ (hmap hx)) (by norm_num)
  · intro x hx y hy
    rw [hder x hx, hder y hy, ← smul_sub, norm_smul,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 512)]
    have hh := mul_le_mul_of_nonneg_left (hholder _ (hmap hx) _ (hmap hy))
      (by norm_num : (0 : ℝ) ≤ 512)
    rw [quasilinear_ballScaling_symm_dist c x y hδ, one_div, inv_inv,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 512) dist_nonneg] at hh
    simpa only [mul_assoc] using hh
  · intro x hx hxflat
    apply hflat _ (hmap hx)
    simp only [e, frozenBallScaling_symm_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.sub_apply, c, graphAppendN_last, hxflat, sub_zero, mul_zero]

end LiquidDrop
