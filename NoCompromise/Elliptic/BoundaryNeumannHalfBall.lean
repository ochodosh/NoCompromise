import NoCompromise.Elliptic.BoundaryNeumannRecentre
import NoCompromise.Elliptic.BoundaryC2aCover
import NoCompromise.Elliptic.BoundaryNeumannC2HolderPrimitive
import NoCompromise.Elliptic.BoundaryNeumannInhom

/-!
# Boundary Neumann C²,α on the half ball `B⁺_{1/2}` (`thm:boundary-neumann`, second assertion)

The boundary layer of `boundary_neumann_c2_holder_layer` and interior pieces cover `B⁺_{1/2}`.
In the interior the conormal identity is the divergence equation `div(A∇z) = div P` for the
vertical primitive `P` of `f`, and interior C²,α regularity applies on balls of a fixed radius.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop

/-- Interior pieces from H¹ as in `boundary_c2a_cover_interior`, with the coefficient and datum
hypotheses only on the open half ball. -/
theorem boundary_neumann_cover_interior {α lam cap M N P₁ E t : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hE : 0 ≤ E) (ht : 0 < t) (ht1 : t ≤ 1 / 2) :
    ∃ C > 0, ∀ (u φ : EuclideanSpace ℝ (Fin 3) → ℝ)
      (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)),
      ContDiff ℝ 1 φ →
      HasC1HolderOn α A (boundaryHalfBall 1) →
      HasC1HolderOn α G (boundaryHalfBall 1) →
      nondivC1HolderNorm α A (boundaryHalfBall 1) ≤ M →
      nondivC1HolderNorm α G (boundaryHalfBall 1) ≤ N →
      (∀ x ∈ boundaryHalfBall 1, ‖A x‖ ≤ cap) →
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
  have hmU : MapsTo e (ball 0 1) (boundaryHalfBall 1) :=
    fun z hz => hball (hmB hz)
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
    (fun z hz => hcapb _ (hmU hz)) (fun z hz => hell _ (subset_closure (hmU hz))) hAh hGh hu1
    hw1 hen1
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
    (fun z hz => hell _ (subset_closure (hmU hz))) hu2 hw1 hen1
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

/-- In the interior of the half ball the weak conormal identity is the divergence equation
`div(A∇z) = div P` for the vertical primitive `P` of `f`. -/
theorem boundary_neumann_interior_equation {a cap Bf Hf : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hBf : 0 ≤ Bf) (hHf : 0 ≤ Hf)
    {A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3)}
    {F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {h : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hA : ContinuousOn A (closure (boundaryHalfBall 1)))
    (hbA : ∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap)
    (hF : MemLp F 2 (volume.restrict (boundaryHalfBall 1)))
    (hf : ContinuousOn f (closure (boundaryHalfBall 1)))
    (hbf : ∀ x ∈ closure (boundaryHalfBall 1), ‖f x‖ ≤ Bf)
    (hhf : ∀ x ∈ closure (boundaryHalfBall 1), ∀ y ∈ closure (boundaryHalfBall 1),
      ‖f x - f y‖ ≤ Hf * dist x y ^ a)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 1 →
      (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
        -(∫ x in boundaryHalfBall 1, f x * φ x) -
          ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1, h y * φ (graphBaseEmbedding y)) :
    IsWeakDivergenceEquationOn A F (boundaryNeumannPrimitive f) (boundaryHalfBall 1) := by
  intro φ hφ hcφ hsφ
  have hsφ' : tsupport φ ⊆ ball 0 1 := hsφ.trans inter_subset_left
  have hAF : MemLp (fun x => A x (F x)) 2 (volume.restrict (boundaryHalfBall 1)) := by
    have he := boundary_neumann_flux_memLp (a := a) (HH := 0) (H := fun _ => 0)
      ha.le le_rfl hA continuousOn_const hbA (by simp) hF
    simpa only [sub_zero] using he
  have hg : MemLp (gradient φ) 2 volume :=
    (continuous_gradient_of_contDiff hφ).memLp_of_hasCompactSupport
      (hcφ.of_isClosed_subset (isClosed_tsupport _) (tsupport_gradient_subset φ))
  have hiAF := integrable_inner_of_memLp_two hAF (hg.restrict (boundaryHalfBall 1))
  have hP := boundaryNeumannPrimitive_continuousOn ha ha1 hBf hHf hf hbf hhf
  have hiP := boundary_neumann_integrableOn_of_continuousOn
    (hP.inner (continuous_gradient_of_contDiff hφ).continuousOn)
  have hz : ∀ x, x ∉ boundaryHalfBall 1 →
      inner ℝ (A x (F x) - boundaryNeumannPrimitive f x) (gradient φ x) = 0 := by
    intro x hx
    rw [gradient_eq_zero_of_notMem_tsupport (fun ht => hx (hsφ ht)), inner_zero_right]
  have hbd : (∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      h y * φ (graphBaseEmbedding y)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y _
    have hy : graphBaseEmbedding y ∉ tsupport φ := by
      intro hy
      have h3 := (hsφ hy).2
      change 0 < graphBaseEmbedding y (Fin.last 2) at h3
      rw [boundary_neumann_recentre_emb_last] at h3
      exact lt_irrefl 0 h3
    rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  simp_rw [inner_sub_left]
  rw [integral_sub hiAF hiP, hweak φ hφ hcφ hsφ',
    boundary_neumann_interior_source_identity ha ha1 hBf hHf hf hbf hhf hφ hsφ', hbd]
  ring

/-- **Boundary Neumann C²,α on `B⁺_{1/2}` (second assertion of `thm:boundary-neumann`, flat
chart).** Under the TeX data classes `A ∈ C^{2,α}`, `f ∈ C^{1,α}`, `h ∈ C^{2,α}` (norms `≤ K`),
ellipticity `λ`, vanishing cross coefficients on the face, the normal-coefficient lower bound
and the energy bound `M`, one representative of the weak conormal solution `z` is C² on
`B⁺_{1/2}` with all second derivatives bounded and `α`-Hölder on `B⁺_{1/2}`, by a constant
depending only on `α`, `λ`, `K`, `M`. -/
theorem boundary_neumann_c2_holder_half_ball {α lam K M : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hK : 0 ≤ K) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (z f : EuclideanSpace ℝ (Fin 3) → ℝ)
        (h : EuclideanSpace ℝ (Fin 2) → ℝ)
        (O : Set (EuclideanSpace ℝ (Fin 3))) (U : Set (EuclideanSpace ℝ (Fin 2))),
        IsOpen O → closedBall 0 1 ⊆ O → ContDiffOn ℝ 2 A O →
        HasC1HolderOn α A (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ A) (closedBall 0 1) →
        nondivC1HolderNorm α A (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ A) (closedBall 0 1) ≤ K →
        (∀ x ∈ closure (boundaryHalfBall 1), ∀ ξ,
          lam * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) →
        (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 →
          ∀ i : Fin 3, i ≠ Fin.last 2 →
            A x (EuclideanSpace.single i 1) (Fin.last 2) = 0 ∧
            A x (EuclideanSpace.single (Fin.last 2) 1) i = 0) →
        IsOpen U → closedBall 0 1 ⊆ U →
        (∀ y ∈ U, lam ≤ boundaryNeumannNormalCoefficient A y) →
        ContDiffOn ℝ 2 h U →
        HasC1HolderOn α h (closedBall 0 1) → HasC1HolderOn α (fderiv ℝ h) (closedBall 0 1) →
        nondivC1HolderNorm α h (closedBall 0 1) ≤ K →
        nondivC1HolderNorm α (fderiv ℝ h) (closedBall 0 1) ≤ K →
        ContDiffOn ℝ 1 f O → HasC1HolderOn α f (closedBall 0 1) →
        nondivC1HolderNorm α f (closedBall 0 1) ≤ K →
        HasH1GradientOn z F (boundaryHalfBall 1) →
        (∫ x in boundaryHalfBall 1, ‖F x‖ ^ 2) ≤ M →
        (∀ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball 0 1 →
          (∫ x in boundaryHalfBall 1, inner ℝ (A x (F x)) (gradient φ x)) =
            -(∫ x in boundaryHalfBall 1, f x * φ x) -
              ∫ y in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
                h y * φ (graphBaseEmbedding y)) →
        ∃ v : EuclideanSpace ℝ (Fin 3) → ℝ,
          ContDiffOn ℝ 2 v (boundaryHalfBall (1 / 2)) ∧
          z =ᵐ[volume.restrict (boundaryHalfBall (1 / 2))] v ∧
          ∀ i j : Fin 3,
            (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry v x i j| ≤ C) ∧
            ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
              |boundaryNeumannC2Entry v x i j - boundaryNeumannC2Entry v y i j| ≤
                C * dist x y ^ α := by
  set t : ℝ := 3 / 256 with ht_def
  have ht : 0 < t := by norm_num [ht_def]
  have ht1 : t ≤ 1 / 2 := by norm_num [ht_def]
  obtain ⟨CL, hCL, hlayer⟩ := boundary_neumann_c2_holder_layer hα hα1 hlam hK hM
  obtain ⟨CI, hCI, hint⟩ := boundary_neumann_cover_interior (cap := K + lam) (M := K)
    (N := 36 * K) (P₁ := 0) (E := M) hα hα1 hlam (by linarith) hK (by positivity) hM ht ht1
  set Cb : ℝ := CL + CI
  have hCb : 0 < Cb := by positivity
  refine ⟨2 * Cb * (t / 4)⁻¹ ^ α + Cb, by positivity, ?_⟩
  intro A F z f h O U hO hOb hAO hA hdA hAK hdAK hell hcross hU hUb hnorm hhU hh hdh hhK hdhK
    hfO hf hfK hH1 hE hweak
  obtain ⟨vL, hvL2, hzvL, hvLent⟩ := hlayer A F z f h O U hO hOb hAO hA hdA hAK hdAK hell hcross
    hU hUb hnorm hhU hh hdh hhK hdhK hfO hf hfK hH1 hE hweak
  -- interior data
  have hclB : closure (boundaryHalfBall 1) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    closure_minimal (fun _ hx => ball_subset_closedBall hx.1) isClosed_closedBall
  have hHB : boundaryHalfBall 1 ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    subset_closure.trans hclB
  obtain ⟨hAH, hAHn⟩ := hA.mono hHB
  obtain ⟨hPc, hPH, hPn⟩ := boundaryNeumannPrimitive_hasC1HolderOn_of_subset hα.le hα1.le hO hOb
    hfO hf hfK (U := boundaryHalfBall 1) inter_subset_left
  obtain ⟨hAb, -⟩ := boundaryNeumannData_holder_bounds hA.function_holder
    (hA.function_norm_le.trans hAK)
  obtain ⟨hfb, hfh, -, -⟩ := boundaryNeumannData_c1_bounds hf hfK
  have heq : IsWeakDivergenceEquationOn A F (boundaryNeumannPrimitive f) (boundaryHalfBall 1) :=
    boundary_neumann_interior_equation hα hα1.le hK hK
      (hA.contDiff.continuousOn.mono hclB) (fun x hx => hAb x (hclB hx)) hH1.memLp_gradient
      (hf.contDiff.continuousOn.mono hclB) (fun x hx => hfb x (hclB hx))
      (fun x hx y hy => hfh x (hclB hx) y (hclB hy)) hweak
  have hφ0 : ContDiff ℝ 1 (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) := contDiff_const
  have hg0 : gradient (fun _ : EuclideanSpace ℝ (Fin 3) => (0 : ℝ)) = fun _ => 0 := by
    funext x
    simp [gradient]
  have hint' := hint z (fun _ => 0) F (boundaryNeumannPrimitive f) A hφ0 hAH hPH
    (hAHn.trans hAK) hPn (fun x hx => (hAb x (hHB hx)).trans (by linarith)) hell
    (fun x _ => by rw [hg0]; simp) hH1 heq (by simpa [hg0] using hE)
  -- the pieces
  set Lay := boundaryHalfBall (1 / 2) ∩ {x : EuclideanSpace ℝ (Fin 3) | x (Fin.last 2) < 3 / 128}
  have hLayo : IsOpen Lay := (isOpen_boundaryHalfBall _).inter
    (isOpen_lt (EuclideanSpace.proj (Fin.last 2)).continuous continuous_const)
  set P : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)) := fun x =>
    if x (Fin.last 2) < t then Lay else ball x (t / 4)
  set u : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ := fun x =>
    if hx : ‖x‖ < 1 / 2 ∧ t ≤ x (Fin.last 2) then Classical.choose (hint' x hx.1 hx.2) else vL
  have hspec : ∀ x ∈ boundaryHalfBall (1 / 2),
      ContDiffOn ℝ 2 (u x) (P x) ∧ z =ᵐ[volume.restrict (P x)] u x ∧
      ∀ i j : Fin 3, (∀ y ∈ P x, |boundaryNeumannC2Entry (u x) y i j| ≤ Cb) ∧
        ∀ y ∈ P x, ∀ y' ∈ P x,
          |boundaryNeumannC2Entry (u x) y i j - boundaryNeumannC2Entry (u x) y' i j| ≤
            Cb * dist y y' ^ α := by
    intro x hx
    have hxn : ‖x‖ < 1 / 2 := mem_ball_zero_iff.mp hx.1
    by_cases h3 : x (Fin.last 2) < t
    · have hPx : P x = Lay := ite_eq_left h3
      have hux : u x = vL := dite_eq_right (fun hc => absurd hc.2 (not_le.mpr h3))
      rw [hPx, hux]
      refine ⟨hvL2, hzvL, fun i j => ⟨fun y hy => ((hvLent i j).1 y hy).trans (by linarith),
        fun y hy y' hy' => ((hvLent i j).2 y hy y' hy').trans ?_⟩⟩
      have : 0 ≤ dist y y' ^ α := Real.rpow_nonneg dist_nonneg α
      have : CL ≤ Cb := by linarith
      nlinarith
    · push Not at h3
      have hPx : P x = ball x (t / 4) := ite_eq_right (not_lt.mpr h3)
      have hc := Classical.choose_spec (hint' x hxn h3)
      have hux : u x = Classical.choose (hint' x hxn h3) := dite_eq_left ⟨hxn, h3⟩
      rw [hPx, hux]
      refine ⟨hc.1, hc.2.1.symm, fun i j => ⟨fun y hy => ((hc.2.2 i j).1 y hy).trans
        (by linarith), fun y hy y' hy' => ((hc.2.2 i j).2 y hy y' hy').trans ?_⟩⟩
      have : 0 ≤ dist y y' ^ α := Real.rpow_nonneg dist_nonneg α
      have : CI ≤ Cb := by linarith
      nlinarith
  obtain ⟨v, hv2, hzv, hvent⟩ := boundary_neumann_layer_glue hα
    (by positivity : (0 : ℝ) < t / 4) hCb.le
    (isOpen_boundaryHalfBall _) P u
    (fun x _ => by
      by_cases h3 : x (Fin.last 2) < t
      · simp only [P, ite_eq_left h3]; exact hLayo
      · simp only [P, ite_eq_right h3]; exact isOpen_ball)
    (fun x hx y hy hxy => by
      by_cases h3 : x (Fin.last 2) < t
      · simp only [P, ite_eq_left h3]
        refine ⟨hy, ?_⟩
        change y (Fin.last 2) < 3 / 128
        have h4 : |(y - x) (Fin.last 2)| ≤ ‖y - x‖ := by
          simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (y - x) (Fin.last 2)
        rw [PiLp.sub_apply] at h4
        have h5 : ‖y - x‖ = dist x y := by rw [dist_comm, dist_eq_norm]
        have h6 := le_abs_self (y (Fin.last 2) - x (Fin.last 2))
        rw [ht_def] at h3 hxy
        linarith
      · simp only [P, ite_eq_right h3]
        exact mem_ball_comm.mp hxy)
    (fun x hx => (hspec x hx).1) (fun x hx => (hspec x hx).2.1)
    (fun x hx i j => ((hspec x hx).2.2 i j).1) (fun x hx i j => ((hspec x hx).2.2 i j).2)
  refine ⟨v, hv2, hzv, fun i j => ⟨fun x hx => ((hvent i j).1 x hx).trans ?_, (hvent i j).2⟩⟩
  have : 0 ≤ 2 * Cb * (t / 4)⁻¹ ^ α := by positivity
  linarith

end LiquidDrop
