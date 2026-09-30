module

public import NoCompromise.Elliptic.BoundaryC2aLocalAssembly
public import NoCompromise.Elliptic.InteriorC2aH1
public import NoCompromise.Elliptic.BoundaryHolderSimilarity
public import NoCompromise.Elliptic.BoundaryHolderGluing

@[expose] public section

/-!
# Boundary C²,α on the half ball `B⁺_{1/2}` (`thm:boundary-C2a`, covering)

The local boundary pieces of `boundary_c2a_local_of_h1` near the flat face and interior
pieces from `interior_c2a_holder_of_h1` (on balls of a fixed small radius) cover `B⁺_{1/2}`;
the continuous representatives agree on overlaps, and a short/long distance split turns the
local Hölder bounds of the second derivatives into a global one.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Local Hölder bounds at distances below `ρ` together with a sup bound give a global
Hölder bound. -/
lemma boundary_c2a_cover_holder_of_local {X : Type*} [PseudoMetricSpace X] {S : Set X}
    {f : X → ℝ} {α B ρ : ℝ} (hα : 0 ≤ α) (hB : 0 ≤ B) (hρ : 0 < ρ)
    (hb : ∀ x ∈ S, |f x| ≤ B)
    (hl : ∀ x ∈ S, ∀ y ∈ S, dist x y < ρ → |f x - f y| ≤ B * dist x y ^ α) :
    ∀ x ∈ S, ∀ y ∈ S, |f x - f y| ≤ (B + 2 * B / ρ ^ α) * dist x y ^ α := by
  intro x hx y hy
  have hd : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ _
  have hq : 0 ≤ 2 * B / ρ ^ α := by positivity
  by_cases hxy : dist x y < ρ
  · exact (hl x hx y hy hxy).trans (mul_le_mul_of_nonneg_right (by linarith) hd)
  · rw [not_lt] at hxy
    have h1 : |f x - f y| ≤ 2 * B := by
      have := abs_sub (f x) (f y)
      linarith [hb x hx, hb y hy]
    have h2 : ρ ^ α ≤ dist x y ^ α := Real.rpow_le_rpow hρ.le hxy hα
    have h3 : 2 * B = 2 * B / ρ ^ α * ρ ^ α := by field_simp
    calc |f x - f y| ≤ 2 * B / ρ ^ α * ρ ^ α := h3 ▸ h1
      _ ≤ 2 * B / ρ ^ α * dist x y ^ α := mul_le_mul_of_nonneg_left h2 hq
      _ ≤ (B + 2 * B / ρ ^ α) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) hd

/-- The coordinate second derivatives are controlled by the C²,α norm. -/
lemma boundary_c2a_cover_entry_of_c2Holder {α : ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hv : HasC2HolderOn α v U)
    (i j : Fin 3) :
    (∀ x ∈ U, |boundaryNeumannC2Entry v x i j| ≤ schauderC2HolderNorm α v U) ∧
      ∀ x ∈ U, ∀ y ∈ U, |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
        schauderC2HolderNorm α v U * dist x y ^ α := by
  have hent : ∀ x ∈ U, boundaryNeumannC2Entry v x i j =
      fderiv ℝ (fderiv ℝ v) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro x hx
    unfold boundaryNeumannC2Entry
    rw [nondiv_fderiv_coordinate_eq hU hv.contDiff j hx, ContinuousLinearMap.flip_apply]
  have hop : ∀ L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ,
      |L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ ‖L‖ := by
    intro L
    have h := L.le_opNorm₂ (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ))
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one] using h
  have hle : holderNorm α (fderiv ℝ (fderiv ℝ v)) U ≤ schauderC2HolderNorm α v U := by
    unfold schauderC2HolderNorm
    have := hv.function_holder.norm_nonneg
    have := hv.derivative_holder.norm_nonneg
    linarith
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [hent x hx]
    exact (hop _).trans ((hv.hessian_holder.nondiv_norm_le hx).trans hle)
  · rw [hent x hx, hent y hy, ← sub_apply, ← sub_apply]
    exact (hop _).trans (boundary_c2a_local_holder_pointwise hv.hessian_holder hle x hx y hy)

/-- Adding a constant does not change the coordinate second derivatives. -/
lemma boundary_c2a_cover_entry_add_const (v : EuclideanSpace ℝ (Fin 3) → ℝ) (c : ℝ) :
    boundaryNeumannC2Entry (fun z => v z + c) = boundaryNeumannC2Entry v := by
  funext x i j
  unfold boundaryNeumannC2Entry
  simp only [fderiv_add_const]

/-- The coordinate second derivatives only depend on the germ. -/
lemma boundary_c2a_cover_entry_congr {v w : EuclideanSpace ℝ (Fin 3) → ℝ}
    {y : EuclideanSpace ℝ (Fin 3)} (h : v =ᶠ[𝓝 y] w) (i j : Fin 3) :
    boundaryNeumannC2Entry v y i j = boundaryNeumannC2Entry w y i j := by
  unfold boundaryNeumannC2Entry
  have h2 : (fun z => fderiv ℝ v z (EuclideanSpace.single j 1)) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ w z (EuclideanSpace.single j 1)) :=
    (h.fderiv (𝕜 := ℝ)).mono fun z hz => by simp only [hz]
  rw [h2.fderiv_eq]

/-- Interior pieces: at points of `B⁺_{1/2}` at height at least `t`, `u` has a C² representative
on `ball x₀ (t/4)` whose coordinate second derivatives are bounded and α-Hölder there, with a
constant chosen before the data and the point. The constant is removed first (subtracting the
value of the C¹ representative at the centre), so the Schauder bound only sees the gradient. -/
theorem boundary_c2a_cover_interior {α lam cap M N P₁ E t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hE : 0 ≤ E) (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    ∃ C > 0, ∀ (u φ : EuclideanSpace ℝ (Fin 3) → ℝ)
      (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ 1 φ →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α G (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) ≤ N →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖gradient φ x‖ ≤ P₁) →
      HasH1GradientOn u F (boundaryHalfBall 1) →
      IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1) →
      (∫ x in boundaryHalfBall 1, ‖F x - gradient φ x‖ ^ 2) ≤ E →
      ∀ x₀ : EuclideanSpace ℝ (Fin 3), ‖x₀‖ < 1 / 2 → t ≤ x₀ (Fin.last 2) →
      ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContDiffOn ℝ 2 w (ball x₀ (t / 4)) ∧
        w =ᵐ[volume.restrict (ball x₀ (t / 4))] u ∧
        ∀ i j : Fin 3,
          (∀ y ∈ ball x₀ (t / 4), |boundaryNeumannC2Entry w y i j| ≤ C) ∧
          ∀ y ∈ ball x₀ (t / 4), ∀ z ∈ ball x₀ (t / 4),
            |boundaryNeumannC2Entry w y i j - boundaryNeumannC2Entry w z i j| ≤
              C * dist y z ^ α := by
  have hcap : 0 ≤ cap := hlam.le.trans hlamcap
  have ht1' : t ≤ 1 := ht1.trans (by norm_num)
  set V₀ : ℝ := volume.real (boundaryHalfBall 1)
  have hV₀ : 0 ≤ V₀ := measureReal_nonneg
  set E' : ℝ := (t ^ 2 * (t ^ 3)⁻¹) * (2 * E + 2 * P₁ ^ 2 * V₀)
  have hE' : 0 ≤ E' := by positivity
  set M' : ℝ := M + N
  have hM' : 0 ≤ M' := by positivity
  obtain ⟨C₁, hC₁, hc1⟩ := campanato_c1_holder (n := 3) (by norm_num) (by norm_num) hα hα1
    hlam hcap hM' hM' hE'
  obtain ⟨C₃, hC₃, hc3⟩ := interior_c2a_holder_of_h1 hα hα1 hlam hlamcap hM' hE'
  set K : ℝ := C₃ * (C₁ + 1)
  have hK : 0 < K := by positivity
  refine ⟨t⁻¹ ^ 2 * K * t⁻¹ ^ α, by positivity, ?_⟩
  intro u φ F G A hφ1 hA hG hAM hGN hcapb hell hφb hu hw hen x₀ hx₀ hx₀3
  set e := frozenBallScaling x₀ ht
  -- the ball `ball x₀ t` lies in the half ball
  have hball : ball x₀ t ⊆ boundaryHalfBall 1 := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have := norm_sub_norm_le y x₀
      linarith
    · change 0 < y (Fin.last 2)
      have h3 : |(y - x₀) (Fin.last 2)| ≤ ‖y - x₀‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (y - x₀) (Fin.last 2)
      rw [PiLp.sub_apply] at h3
      have := neg_abs_le (y (Fin.last 2) - x₀ (Fin.last 2))
      linarith
  have hmB : MapsTo e (ball 0 1) (ball x₀ t) := quasilinear_ballScaling_maps_unit x₀ ht
  have hmU : MapsTo e (ball 0 1) (closure (boundaryHalfBall 1)) :=
    fun z hz => subset_closure (hball (hmB hz))
  obtain ⟨hAe, hAeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le x₀ ht ht1' hA hmU
  obtain ⟨hGe0, hGe0N⟩ := boundary_c2a_c1Holder_comp_scaling hα.le x₀ ht ht1' hG hmU
  obtain ⟨hGe, hGeN⟩ := boundary_c2a_c1Holder_const_smul hGe0 ht.le ht1'
  have hAeM : nondivC1HolderNorm α (A ∘ e) (ball 0 1) ≤ M' := by linarith
  have hGeM : nondivC1HolderNorm α (fun y => t • (G ∘ e) y) (ball 0 1) ≤ M' := by linarith
  have hAh := boundary_c2a_local_holder_pointwise hAe.function_holder
    (hAe.function_norm_le.trans hAeM)
  have hGh := boundary_c2a_local_holder_pointwise hGe.function_holder
    (hGe.function_norm_le.trans hGeM)
  have hu1 : HasH1GradientOn (u ∘ e) (fun z => t • F (e z)) (ball 0 1) :=
    (hu.mono hball).comp_campanatoBallScaling x₀ ht
  have hw1 : IsWeakDivergenceEquationOn (A ∘ e) (fun z => t • F (e z))
      (fun z => t • G (e z)) (ball 0 1) :=
    (hw.mono hball).comp_campanatoBallScaling x₀ ht
  -- energy
  have hFi : Integrable (fun x => ‖F x‖ ^ 2) (volume.restrict (boundaryHalfBall 1)) :=
    hu.memLp_gradient.norm.integrable_sq
  have hFsq : (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ 2 * E + 2 * P₁ ^ 2 * V₀ := by
    have hφH := boundary_c2a_hasH1GradientOn_of_contDiff hφ1
    have hbU := boundaryHalfBall_volume_lt_top 1
    have : IsFiniteMeasure (volume.restrict (boundaryHalfBall 1)) :=
      isFiniteMeasure_restrict.mpr hbU.ne
    have hi2 : Integrable (fun x => ‖F x - gradient φ x‖ ^ 2)
        (volume.restrict (boundaryHalfBall 1)) :=
      (hu.memLp_gradient.sub hφH.memLp_gradient).norm.integrable_sq
    calc (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2)
        ≤ ∫ x in boundaryHalfBall 1, (2 * ‖F x - gradient φ x‖ ^ 2 + 2 * P₁ ^ 2) := by
          apply integral_mono_ae hFi ((hi2.const_mul 2).add (integrable_const _))
          filter_upwards [ae_restrict_mem (isOpen_boundaryHalfBall 1).measurableSet] with x hx
          have hxb : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
            ball_subset_closedBall hx.1
          have h1 := hφb x hxb
          have h2 := norm_sub_norm_le (F x) (gradient φ x)
          have h3 := norm_nonneg (F x - gradient φ x)
          have h4 := norm_nonneg (F x)
          have h5 : ‖F x‖ ≤ ‖F x - gradient φ x‖ + P₁ := by linarith
          have h6 : ‖F x‖ ^ 2 ≤ (‖F x - gradient φ x‖ + P₁) ^ 2 :=
            pow_le_pow_left₀ h4 h5 2
          change ‖F x‖ ^ 2 ≤ 2 * ‖F x - gradient φ x‖ ^ 2 + 2 * P₁ ^ 2
          nlinarith [sq_nonneg (‖F x - gradient φ x‖ - P₁)]
      _ = 2 * (∫ x in boundaryHalfBall 1, ‖F x - gradient φ x‖ ^ 2) + 2 * P₁ ^ 2 * V₀ := by
          rw [integral_add (hi2.const_mul 2) (integrable_const _), integral_const_mul,
            integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
          ring
      _ ≤ 2 * E + 2 * P₁ ^ 2 * V₀ := by linarith
  have hen1 : (∫ z in ball (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖t • F (e z)‖ ^ 2) ≤ E' := by
    rw [frozen_integral_gradient_sq_ballScaling F x₀ ht 1, mul_one]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans ?_ hFsq
    exact setIntegral_mono_set hFi (ae_of_all _ fun x => sq_nonneg _) hball.eventuallyLE
  -- the C¹ representative
  obtain ⟨v₁, hv₁, huv₁, -, hgv₁, -, -⟩ := hc1 (A ∘ e) (fun z => t • G (e z))
    (fun z => t • F (e z)) (u ∘ e) hAe.contDiff.continuousOn hGe.contDiff.continuousOn
    (fun z hz => hcapb _ (hmU hz)) (fun z hz => hell _ (hmU hz)) hAh hGh hu1 hw1 hen1
  set c := v₁ 0
  have hv₁b : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), |v₁ z - c| ≤ C₁ := by
    intro z hz
    have hdiff : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), DifferentiableAt ℝ v₁ x :=
      fun x hx => (hv₁.differentiableOn (by norm_num) x hx).differentiableAt
        (isOpen_ball.mem_nhds hx)
    have hfd : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2), ‖fderiv ℝ v₁ x‖ ≤ C₁ := by
      intro x hx
      have h := hgv₁ x hx
      rwa [gradient, LinearIsometryEquiv.norm_map] at h
    have h :=
      (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
        hdiff hfd (mem_ball_self (by norm_num)) hz
    rw [sub_zero, Real.norm_eq_abs] at h
    have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le.trans (by norm_num)
    nlinarith [norm_nonneg z]
  -- subtract the constant
  have hconst : HasH1GradientOn (fun _ : EuclideanSpace ℝ (Fin 3) => c) (fun _ => 0)
      (ball 0 1) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
      isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
    have h := hasWeakGradientOn_of_contDiffOn (U := ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      isOpen_ball (contDiffOn_const (c := c))
    have hg : gradient (fun _ : EuclideanSpace ℝ (Fin 3) => c) = fun _ => 0 := by
      funext x
      simp [gradient]
    rw [hg] at h
    exact ⟨h, memLp_const c, memLp_const 0⟩
  have hu2 : HasH1GradientOn (fun z => (u ∘ e) z - c) (fun z => t • F (e z)) (ball 0 1) := by
    have h := hu1.sub hconst
    simpa only [sub_zero] using h
  obtain ⟨v, huv, hC2, hnorm⟩ := hc3 (A ∘ e) (fun z => t • G (e z)) (fun z => t • F (e z))
    (fun z => (u ∘ e) z - c) hAe hGe hAeM hGeM (fun z hz => hcapb _ (hmU hz))
    (fun z hz => hell _ (hmU hz)) hu2 hw1 hen1
  -- sup bound
  have hlp : lpNorm v ∞ (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ))) ≤
      C₁ := by
    have hmeas : AEStronglyMeasurable v
        (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ))) :=
      ((hu2.memLp_function.mono_measure (Measure.restrict_mono
        (ball_subset_ball (by norm_num)) le_rfl)).aestronglyMeasurable).congr huv
    have hb : ∀ᵐ z ∂(volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2 : ℝ))),
        ‖v z‖ ≤ C₁ := by
      filter_upwards [huv, huv₁, ae_restrict_mem measurableSet_ball] with z h1 h2 hz
      rw [← h1, Real.norm_eq_abs, h2]
      exact hv₁b z hz
    rw [← toReal_eLpNorm, eLpNorm_exponent_top hmeas]
    exact ENNReal.toReal_le_of_le_ofReal hC₁.le (eLpNormEssSup_le_of_ae_bound hb)
  have hsch : schauderC2HolderNorm α v (ball 0 (1 / 4)) ≤ K :=
    hnorm.trans (mul_le_mul_of_nonneg_left (by linarith) hC₃.le)
  -- pull back
  set g : EuclideanSpace ℝ (Fin 3) → ℝ := fun z => v z + c
  have himg : ball x₀ (t / 4) ⊆ e '' ball 0 (1 / 4) := by
    intro y hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply (frozenBallScaling_mem_ball_iff x₀ (e.symm y) ht (1 / 4)).mp
    change e (e.symm y) ∈ ball x₀ (t * (1 / 4))
    rw [e.apply_symm_apply, mul_one_div]
    exact hy
  refine ⟨g ∘ e.symm, ?_, ?_, fun i j => ?_⟩
  · exact (boundary_c2a_contDiffOn_comp_scaling_symm x₀ ht
      (hC2.contDiff.add contDiffOn_const)).mono himg
  · have hae : g =ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4))] (u ∘ e) := by
      have h := ae_restrict_of_ae_restrict_of_subset
        (ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)) huv
      filter_upwards [h] with z hz
      change v z + c = u (e z)
      rw [← hz]
      simp
    have h := boundary_ballScaling_pullback_ae x₀ ht hae
    have hue : (u ∘ e) ∘ e.symm = u := by
      funext y
      simp only [Function.comp_apply, e.apply_symm_apply]
    rw [hue, mul_one_div] at h
    exact h
  · obtain ⟨hb, hh⟩ := boundary_c2a_cover_entry_of_c2Holder isOpen_ball hC2 i j
    have hent : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) (1 / 4),
        boundaryNeumannC2Entry (g ∘ e.symm) (e z) i j =
          t⁻¹ ^ 2 * boundaryNeumannC2Entry v z i j := by
      intro z _
      rw [boundary_c2a_entry_comp_scaling, boundary_c2a_cover_entry_add_const]
    have h1 : 1 ≤ t⁻¹ ^ α := Real.one_le_rpow ((one_le_inv₀ ht).mpr ht1') hα.le
    constructor
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := himg hy
      rw [hent z hz, abs_mul, abs_of_nonneg (by positivity)]
      calc t⁻¹ ^ 2 * |boundaryNeumannC2Entry v z i j| ≤ t⁻¹ ^ 2 * K :=
            mul_le_mul_of_nonneg_left ((hb z hz).trans hsch) (by positivity)
        _ ≤ t⁻¹ ^ 2 * K * t⁻¹ ^ α := le_mul_of_one_le_right (by positivity) h1
    · intro y hy y' hy'
      obtain ⟨z, hz, rfl⟩ := himg hy
      obtain ⟨z', hz', rfl⟩ := himg hy'
      rw [hent z hz, hent z' hz', ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
      have hd : dist z z' = t⁻¹ * dist (e z) (e z') := by
        rw [quasilinear_ballScaling_dist x₀ z z' ht, ← mul_assoc, inv_mul_cancel₀ ht.ne',
          one_mul]
      have hdp : dist z z' ^ α = t⁻¹ ^ α * dist (e z) (e z') ^ α := by
        rw [hd, Real.mul_rpow (by positivity) dist_nonneg]
      calc t⁻¹ ^ 2 * |boundaryNeumannC2Entry v z i j - boundaryNeumannC2Entry v z' i j|
          ≤ t⁻¹ ^ 2 * (K * dist z z' ^ α) :=
            mul_le_mul_of_nonneg_left ((hh z hz z' hz').trans
              (mul_le_mul_of_nonneg_right hsch (by positivity))) (by positivity)
        _ = t⁻¹ ^ 2 * K * t⁻¹ ^ α * dist (e z) (e z') ^ α := by rw [hdp]; ring

/-- Blueprint `thm:boundary-C2a` on `B⁺_{1/2}`: under the hypotheses of
`boundary_c2a_local_of_h1`, `u` has a representative `v` that is C² on the open half ball
`B⁺_{1/2}`, with all coordinate second derivatives bounded by `C` and α-Hölder with constant
`C` on `B⁺_{1/2}` (hence extending to C^{2,α} of its closure). `C` depends only on
`α, lam, cap, M, N, P₁, P₂, E`. -/
theorem boundary_c2a_half_ball_of_h1 {α lam cap M N P₁ P₂ E : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (hE : 0 ≤ E) :
    ∃ C > 0, ∀ (u φ : EuclideanSpace ℝ (Fin 3) → ℝ)
      (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ 2 φ →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α G (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α (gradient φ) (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α (gradient φ) (closure (boundaryHalfBall 1)) +
        nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) ≤ N →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ, lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1, ‖gradient φ x‖ ≤ P₁) →
      (∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1,
        ‖gradient φ x - gradient φ y‖ ≤ P₂ * dist x y ^ α) →
      HasH1GradientOn u F (boundaryHalfBall 1) →
      IsWeakDivergenceEquationOn A F G (boundaryHalfBall 1) →
      HasZeroFlatTraceOn (fun x => u x - φ x) (fun x => F x - gradient φ x) (ball 0 1) →
      (∫ x in boundaryHalfBall 1, ‖F x - gradient φ x‖ ^ 2) ≤ E →
      ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContDiffOn ℝ 2 v (boundaryHalfBall (1 / 2)) ∧
        v =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] u ∧
        ∀ i j : Fin 3,
          (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry v x i j| ≤ C) ∧
          ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
            |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
              C * dist x y ^ α := by
  obtain ⟨t, ht_def⟩ : ∃ t : ℝ, t = 1 / 35184372088832 := ⟨_, rfl⟩
  have ht : 0 < t := by norm_num [ht_def]
  have ht1 : t ≤ 1 / 2 := by norm_num [ht_def]
  obtain ⟨Cb, hCb, hbdry⟩ := boundary_c2a_local_of_h1 hα hα1 hlam hlamcap hM hN hP₁ hP₂ hE
  obtain ⟨Ci, hCi, hint⟩ :=
    boundary_c2a_cover_interior (P₁ := P₁) hα hα1 hlam hlamcap hM hN hE ht ht1
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = Cb + Ci := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hB_def]; positivity
  have hCbB : Cb ≤ B := by linarith
  have hCiB : Ci ≤ B := by linarith
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = t / 4 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  refine ⟨B + 2 * B / ρ ^ α, by positivity, ?_⟩
  intro u φ F G A hφ2 hA hG hφ hgφ hAM hNb hcapb hell hφb hφh hu hw htr hen
  obtain ⟨W, vb, hWo, hslab, -, hvbu, -, hloc⟩ :=
    hbdry u φ F G A hφ2 hA hG hφ hgφ hAM hNb hcapb hell hφb hφh hu hw htr hen
  have hGN : nondivC1HolderNorm α G (closure (boundaryHalfBall 1)) ≤ N := by
    have := hφ.norm_nonneg
    have := hgφ.norm_nonneg
    linarith
  have hi := hint u φ F G A (hφ2.of_le (by norm_num)) hA hG hAM hGN hcapb hell hφb hu hw hen
  have hupper : IsOpen {y : EuclideanSpace ℝ (Fin 3) | 0 < y (Fin.last 2)} :=
    isOpen_lt continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous
  -- local pieces around every point of the half ball
  have hlocal : ∀ x ∈ boundaryHalfBall (1 / 2), ∃ (V : Set (EuclideanSpace ℝ (Fin 3)))
      (w : EuclideanSpace ℝ (Fin 3) → ℝ), IsOpen V ∧
      ball x ρ ∩ boundaryHalfBall (1 / 2) ⊆ V ∧ ContDiffOn ℝ 2 w V ∧
      w =ᵐ[volume.restrict V] u ∧ ∀ i j : Fin 3,
        (∀ y ∈ V, |boundaryNeumannC2Entry w y i j| ≤ B) ∧
        ∀ y ∈ V, ∀ z ∈ V,
          |boundaryNeumannC2Entry w y i j - boundaryNeumannC2Entry w z i j| ≤
            B * dist y z ^ α := by
    intro x hx
    have hx1 : ‖x‖ < 1 / 2 := mem_ball_zero_iff.mp hx.1
    have hx3 : 0 < x (Fin.last 2) := hx.2
    by_cases hxt : t ≤ x (Fin.last 2)
    · obtain ⟨w, hwC, hwu, hwe⟩ := hi x hx1 hxt
      refine ⟨ball x (t / 4), w, isOpen_ball, by rw [hρ_def]; exact inter_subset_left, hwC, hwu,
        fun i j =>
        ⟨fun y hy => ((hwe i j).1 y hy).trans (by linarith), fun y hy z hz =>
          ((hwe i j).2 y hy z hz).trans (mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg dist_nonneg _))⟩⟩
    · rw [not_le] at hxt
      set p : EuclideanSpace ℝ (Fin 3) :=
        x - x (Fin.last 2) • EuclideanSpace.single (Fin.last 2) (1 : ℝ) with hp_def
      have hp3 : p (Fin.last 2) = 0 := by simp [p]
      have hgp : graphProjectionN 2 p = graphProjectionN 2 x := by
        ext i
        rw [graphProjectionN_apply, graphProjectionN_apply]
        simp only [p, PiLp.sub_apply, PiLp.smul_apply, PiLp.single_apply,
          (Fin.castSucc_lt_last i).ne, ↓reduceIte, smul_eq_mul, mul_zero, sub_zero]
      have hp : ‖p‖ ≤ 1 / 2 := by
        have h1 := norm_sq_graphProjectionN p
        have h2 := norm_sq_graphProjectionN x
        rw [hgp, hp3] at h1
        nlinarith [norm_nonneg p, norm_nonneg x, sq_nonneg (x (Fin.last 2))]
      have hxp : ‖x - p‖ = x (Fin.last 2) := by
        rw [hp_def, sub_sub_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one,
          Real.norm_eq_abs, abs_of_pos hx3]
      obtain ⟨hC2, hent⟩ := hloc p hp3 hp
      set S := (fun y => p + (1 / 2097152 : ℝ) • y) '' boundaryNondivC2Slab
      have hSo : IsOpen S :=
        (frozenBallScaling p boundary_c2a_local_radius_pos).isOpenMap _ isOpen_boundaryNondivC2Slab
      refine ⟨W ∩ S ∩ {y | 0 < y (Fin.last 2)}, vb, (hWo.inter hSo).inter hupper, ?_,
        hC2.mono (inter_subset_left.trans inter_subset_right), ?_, fun i j =>
        ⟨fun y hy => ((hent i j).1 y hy.1.2).trans (by linarith), fun y hy z hz =>
          ((hent i j).2 y hy.1.2 z hz.1.2).trans (mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg dist_nonneg _))⟩⟩
      · rintro y ⟨hyx, hy⟩
        have hy1 : ‖y‖ < 1 / 2 := mem_ball_zero_iff.mp hy.1
        have hy3 : 0 < y (Fin.last 2) := hy.2
        have hyx' : ‖y - x‖ < t / 4 := by
          rw [mem_ball, dist_eq_norm, hρ_def] at hyx
          exact hyx
        have hy3' : y (Fin.last 2) < 2 * t := by
          have h3 : |(y - x) (Fin.last 2)| ≤ ‖y - x‖ := by
            simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (y - x) (Fin.last 2)
          rw [PiLp.sub_apply] at h3
          have := le_abs_self (y (Fin.last 2) - x (Fin.last 2))
          linarith
        have hyp : ‖y - p‖ < 2 * t := by
          have := norm_sub_le_norm_sub_add_norm_sub y x p
          linarith
        refine ⟨⟨hslab ⟨?_, ?_⟩, ?_⟩, hy3⟩
        · rw [mem_preimage, mem_ball_zero_iff]
          have h := norm_sq_graphProjectionN y
          nlinarith [norm_nonneg y, norm_nonneg (graphProjectionN 2 y),
            sq_nonneg (y (Fin.last 2))]
        · change |y (Fin.last 2)| < 1 / 1048576
          rw [abs_of_pos hy3]
          linarith
        · refine ⟨(2097152 : ℝ) • (y - p), ?_, ?_⟩
          · change (4 / 3 : ℝ) • ((2097152 : ℝ) • (y - p)) ∈ boundaryC1UpperSlab
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rw [mem_preimage, mem_ball_zero_iff]
              set q := (4 / 3 : ℝ) • ((2097152 : ℝ) • (y - p))
              have hq : ‖q‖ = 4 / 3 * (2097152 * ‖y - p‖) := by
                simp only [q, norm_smul, Real.norm_eq_abs]
                norm_num
              have h := norm_sq_graphProjectionN q
              have hg : ‖graphProjectionN 2 q‖ ≤ ‖q‖ := by
                nlinarith [norm_nonneg q, norm_nonneg (graphProjectionN 2 q),
                  sq_nonneg (q (Fin.last 2))]
              linarith
            · change |((4 / 3 : ℝ) • ((2097152 : ℝ) • (y - p))) (Fin.last 2)| < 1 / 1048576
              simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hp3, sub_zero]
              rw [abs_of_pos (by positivity)]
              linarith
            · change 0 < ((4 / 3 : ℝ) • ((2097152 : ℝ) • (y - p))) (Fin.last 2)
              simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, hp3, sub_zero]
              positivity
          · simp only [smul_smul]
            norm_num
      · exact ae_restrict_of_ae_restrict_of_subset
          (show W ∩ S ∩ {y | 0 < y (Fin.last 2)} ⊆ W ∩ {y | 0 < y (Fin.last 2)} from
            fun y hy => ⟨hy.1.1, hy.2⟩) hvbu
  choose V w hVo hVsub hwC hwu hwe using hlocal
  have hU := isOpen_boundaryHalfBall (1 / 2 : ℝ)
  have hmem : ∀ x (hx : x ∈ boundaryHalfBall (1 / 2)), x ∈ V x hx :=
    fun x hx => hVsub x hx ⟨mem_ball_self hρ, hx⟩
  obtain ⟨v, hv1, hvu⟩ := boundary_exists_c1_representative_of_local hU (u := u)
    (fun x hx => ⟨V x hx ∩ boundaryHalfBall (1 / 2), (hVo x hx).inter hU, ⟨hmem x hx, hx⟩,
      inter_subset_right, w x hx, ((hwC x hx).mono inter_subset_left).of_le (by norm_num),
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hwu x hx)⟩)
  have heq : ∀ x (hx : x ∈ boundaryHalfBall (1 / 2)),
      EqOn v (w x hx) (V x hx ∩ boundaryHalfBall (1 / 2)) := by
    intro x hx
    have h₁ : v =ᵐ[volume.restrict (V x hx ∩ boundaryHalfBall (1 / 2))] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right hvu
    have h₂ : w x hx =ᵐ[volume.restrict (V x hx ∩ boundaryHalfBall (1 / 2))] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hwu x hx)
    exact Measure.eqOn_open_of_ae_eq (h₁.trans h₂.symm) ((hVo x hx).inter hU)
      (hv1.continuousOn.mono inter_subset_right) ((hwC x hx).continuousOn.mono inter_subset_left)
  have hnear : ∀ x (hx : x ∈ boundaryHalfBall (1 / 2)),
      ∀ y ∈ V x hx ∩ boundaryHalfBall (1 / 2), v =ᶠ[𝓝 y] w x hx :=
    fun x hx y hy => Filter.eventually_of_mem (((hVo x hx).inter hU).mem_nhds hy)
      (fun z hz => heq x hx hz)
  have hentv : ∀ x (hx : x ∈ boundaryHalfBall (1 / 2)),
      ∀ y ∈ V x hx ∩ boundaryHalfBall (1 / 2), ∀ i j : Fin 3,
        boundaryNeumannC2Entry v y i j = boundaryNeumannC2Entry (w x hx) y i j :=
    fun x hx y hy i j => boundary_c2a_cover_entry_congr (hnear x hx y hy) i j
  refine ⟨v, ?_, hvu, fun i j => ?_⟩
  · exact hU.contDiffOn_iff.mpr fun x hx =>
      ((hwC x hx).contDiffAt ((hVo x hx).mem_nhds (hmem x hx))).congr_of_eventuallyEq
        (hnear x hx x ⟨hmem x hx, hx⟩)
  · have hb : ∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry v x i j| ≤ B := by
      intro x hx
      rw [hentv x hx x ⟨hmem x hx, hx⟩ i j]
      exact (hwe x hx i j).1 x (hmem x hx)
    refine ⟨fun x hx => (hb x hx).trans (le_add_of_nonneg_right (by positivity)), ?_⟩
    apply boundary_c2a_cover_holder_of_local hα.le hB.le hρ hb
    intro x hx y hy hxy
    have hyV : y ∈ V x hx ∩ boundaryHalfBall (1 / 2) :=
      ⟨hVsub x hx ⟨by rw [mem_ball, dist_comm]; exact hxy, hy⟩, hy⟩
    rw [hentv x hx x ⟨hmem x hx, hx⟩ i j, hentv x hx y hyV i j]
    exact (hwe x hx i j).2 x (hmem x hx) y hyV.1

end LiquidDrop
