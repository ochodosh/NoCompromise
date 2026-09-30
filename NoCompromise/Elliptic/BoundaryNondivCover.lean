module

public import NoCompromise.Elliptic.BoundaryNondivC2TraceData
public import NoCompromise.Elliptic.BoundaryC2aLocalAssembly
public import NoCompromise.Elliptic.NondivSchauderScalingBall
public import NoCompromise.Elliptic.NondivSchauderScalingEquation
public import NoCompromise.Elliptic.NondivSchauderLocalization

@[expose] public section

/-!
# Boundary nondivergence C²,α on the half ball `B⁺_{1/2}` (`thm:boundary-nondiv`, covering)

The slab estimate `boundary_nondiv_c2_holder_trace`, rescaled by `y ↦ p + 2⁻²¹ • y` at flat
points `p` with `‖p‖ ≤ 1/2`, and the interior estimate `nondiv_schauder_c1_ball` on balls of a
fixed radius cover `B⁺_{1/2}`; a Lebesgue-number argument turns the local Hölder bounds into a
global one.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- Local Hölder bounds at a fixed scale `ρ` and a uniform bound give a global Hölder bound. -/
lemma boundary_nondiv_cover_holder_of_local {E : Type*} [PseudoMetricSpace E]
    {α B ρ : ℝ} (hα : 0 ≤ α) (hB : 0 ≤ B) (hρ : 0 < ρ) {g : E → ℝ} {S : Set E}
    (hb : ∀ x ∈ S, |g x| ≤ B)
    (hh : ∀ x ∈ S, ∀ y ∈ S, dist x y < ρ → |g x - g y| ≤ B * dist x y ^ α) :
    ∀ x ∈ S, ∀ y ∈ S, |g x - g y| ≤ max B (2 * B * (ρ ^ α)⁻¹) * dist x y ^ α := by
  intro x hx y hy
  by_cases h : dist x y < ρ
  · exact (hh x hx y hy h).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg _))
  · have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
    have hle : ρ ^ α ≤ dist x y ^ α := Real.rpow_le_rpow hρ.le (not_lt.mp h) hα
    calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hb x hx, hb y hy]
      _ = 2 * B * (ρ ^ α)⁻¹ * ρ ^ α := by field_simp
      _ ≤ 2 * B * (ρ ^ α)⁻¹ * dist x y ^ α :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ ≤ max B (2 * B * (ρ ^ α)⁻¹) * dist x y ^ α :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg _)

/-- Scalar-source divergence identities pull back along a similarity mapping `U'` into `U`. -/
theorem boundary_nondiv_cover_scalar_rescale {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {D : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {U U' : Set (EuclideanSpace ℝ (Fin n))} (hm : MapsTo (frozenBallScaling c hr) U' U)
    (he : IsWeakScalarDivergenceEquationOn A D g U) :
    IsWeakScalarDivergenceEquationOn (A ∘ frozenBallScaling c hr)
      (fun x => r • D (frozenBallScaling c hr x))
      (fun x => r ^ 2 * g (frozenBallScaling c hr x)) U' := by
  let e := frozenBallScaling c hr
  intro ψ hψ hcψ hsψ
  let φ := ψ ∘ e.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    have he' : ContDiff ℝ (⊤ : ℕ∞) e.symm := by
      change ContDiff ℝ (⊤ : ℕ∞) (frozenBallScaling c hr).symm
      rw [frozenBallScaling_symm_coe]
      exact (contDiff_id.sub contDiff_const).const_smul r⁻¹
    exact hψ.comp he'
  have hcφ : HasCompactSupport φ := hcψ.comp_homeomorph e.symm
  have hsφ : tsupport φ ⊆ U := by
    rw [tsupport_comp_eq_preimage ψ e.symm]
    intro x hx
    have ht := hm (hsψ hx)
    change e (e.symm x) ∈ U at ht
    simpa only [e.apply_symm_apply] using ht
  have htest := he φ hφ hcφ hsφ
  have hgrad (x) : gradient ψ x = r • gradient φ (e x) := by
    have ht := frozen_gradient_comp_ballScaling_symm c hr (hψ.differentiable (by simp)) (e x)
    change gradient φ (e x) = r⁻¹ • gradient ψ (e.symm (e x)) at ht
    rw [ht, e.symm_apply_apply, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hL (x) : inner ℝ (A (e x) (r • D (e x))) (gradient ψ x) =
      r ^ 2 * inner ℝ (A (e x) (D (e x))) (gradient φ (e x)) := by
    rw [map_smul, hgrad, real_inner_smul_left, real_inner_smul_right]
    ring
  have hR (x) : ψ x * (r ^ 2 * g (e x)) = r ^ 2 * (φ (e x) * g (e x)) := by
    simp only [φ, Function.comp_apply, e.symm_apply_apply]
    ring
  change (∫ x, inner ℝ (A (e x) (r • D (e x))) (gradient ψ x)) =
    -(∫ x, ψ x * (r ^ 2 * g (e x)))
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_const_mul,
    frozen_integral_comp_ballScaling (fun x => inner ℝ (A x (D x)) (gradient φ x)) c hr,
    frozen_integral_comp_ballScaling (fun x => φ x * g x) c hr, htest]
  simp only [smul_eq_mul, mul_neg]

/-- Distributional nondivergence pullback along a similarity mapping an open `U'` into an
open `U`. -/
theorem boundary_nondiv_cover_weak_rescale {n : ℕ}
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {z f : EuclideanSpace ℝ (Fin n) → ℝ}
    (c : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    {U U' : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hU' : IsOpen U')
    (hm : MapsTo (frozenBallScaling c hr) U' U)
    (hA : ContDiffOn ℝ 1 A U) (hb : ContinuousOn b U)
    (hz : ContDiffOn ℝ 1 z U) (hf : ContinuousOn f U)
    (he : IsWeakNondivergenceEquationOn A b z f U) :
    IsWeakNondivergenceEquationOn (A ∘ frozenBallScaling c hr)
      (fun x => r • b (frozenBallScaling c hr x)) (z ∘ frozenBallScaling c hr)
      (fun x => r ^ 2 * f (frozenBallScaling c hr x)) U' := by
  let e := frozenBallScaling c hr
  have hec : ContDiff ℝ 1 e := contDiff_const.add (contDiff_id.const_smul r)
  have hAc := hA.comp hec.contDiffOn hm
  have hzc := hz.comp hec.contDiffOn hm
  have hbc : ContinuousOn (fun x => r • b (e x)) U' := by
    simpa only [Function.comp_apply, Pi.smul_apply] using!
      (hb.comp e.continuous.continuousOn hm).const_smul r
  have hfc : ContinuousOn (fun x => r ^ 2 * f (e x)) U' :=
    continuousOn_const.mul (hf.comp e.continuous.continuousOn hm)
  apply (isWeakNondivergenceEquationOn_iff_divergence hU' hAc hbc hzc hfc).mpr
  have hd := (isWeakNondivergenceEquationOn_iff_divergence hU hA hb hz hf).mp he
  apply (boundary_nondiv_cover_scalar_rescale c hr hm hd).congr_data
  · intro x hx
    exact (nondiv_gradient_comp_ballScaling c x hr
      ((hz.contDiffAt (hU.mem_nhds (hm hx))).differentiableAt one_ne_zero)).symm
  · intro x hx
    have hAx := (hA.contDiffAt (hU.mem_nhds (hm hx))).differentiableAt one_ne_zero
    have hzx := (hz.contDiffAt (hU.mem_nhds (hm hx))).differentiableAt one_ne_zero
    dsimp [nondivDivergenceSource]
    rw [nondivCoefficientDivergence_comp_ballScaling c x hr hAx,
      nondiv_gradient_comp_ballScaling c x hr hzx, ← smul_sub,
      real_inner_smul_left, real_inner_smul_right]
    ring

/-- Iterated coordinate derivatives scale by `r²` under `w ↦ w ∘ e`, with no hypothesis. -/
lemma boundary_nondiv_cover_entry_comp (c y : EuclideanSpace ℝ (Fin 3)) {r : ℝ}
    (hr : 0 < r) (w : EuclideanSpace ℝ (Fin 3) → ℝ) (i j : Fin 3) :
    boundaryNeumannC2Entry (w ∘ frozenBallScaling c hr) y i j =
      r ^ 2 * boundaryNeumannC2Entry w (frozenBallScaling c hr y) i j := by
  unfold boundaryNeumannC2Entry
  have h1 : (fun z => fderiv ℝ (w ∘ frozenBallScaling c hr) z (EuclideanSpace.single j 1)) =
      r • ((fun u => fderiv ℝ w u (EuclideanSpace.single j 1)) ∘ frozenBallScaling c hr) := by
    funext z
    rw [boundary_c2a_fderiv_comp_scaling]
    rfl
  rw [h1, fderiv_const_smul_field, Pi.smul_apply, boundary_c2a_fderiv_comp_scaling]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The classical operator of the rescaled data is `r²` times the rescaled classical operator. -/
lemma boundary_nondiv_cover_classical_comp (c : EuclideanSpace ℝ (Fin 3)) {r : ℝ} (hr : 0 < r)
    (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (y : EuclideanSpace ℝ (Fin 3)) :
    nondivClassicalOperator (A ∘ frozenBallScaling c hr)
        (fun x => r • b (frozenBallScaling c hr x)) (φ ∘ frozenBallScaling c hr) y =
      r ^ 2 * nondivClassicalOperator A b φ (frozenBallScaling c hr y) := by
  have h := boundary_nondiv_cover_entry_comp c y hr φ
  unfold boundaryNeumannC2Entry at h
  unfold nondivClassicalOperator
  simp only [Function.comp_apply, h, boundary_c2a_gradient_comp_scaling c y hr φ,
    real_inner_smul_left, real_inner_smul_right, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · ring

/-- The boundary pieces: rescaling by `y ↦ p + 2⁻²¹ • y` at a flat point `p` with `‖p‖ ≤ 1/2`,
the slab estimate gives C² regularity with bounded, α-Hölder second derivatives on the image of
`boundaryNondivC2Slab`, with a constant fixed before the data. -/
theorem boundary_nondiv_cover_boundary_piece {α lam cap M N P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) :
    ∃ K > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, x (Fin.last 2) = 0 →
        DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryHalfBall 1, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryHalfBall 1, ∀ y ∈ boundaryHalfBall 1,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ∀ p : EuclideanSpace ℝ (Fin 3), p (Fin.last 2) = 0 → ‖p‖ ≤ 1 / 2 →
        ContDiffOn ℝ 2 z (frozenBallScaling p boundary_c2a_local_radius_pos ''
          boundaryNondivC2Slab) ∧
        ∀ i j : Fin 3,
          (∀ x ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab,
            |boundaryNeumannC2Entry z x i j| ≤ K) ∧
          ∀ x ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab,
          ∀ y ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab,
            |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
              K * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_c2_holder_trace hα hα1 hlam hlamcap hM hN
  set r : ℝ := 1 / 2097152 with hr_def
  have hr0 : 0 < r := boundary_c2a_local_radius_pos
  have hr1 : r ≤ 1 := by norm_num [hr_def]
  have hri : 1 ≤ r⁻¹ := by norm_num [hr_def]
  refine ⟨r⁻¹ ^ 2 * (C + P) * r⁻¹ ^ α, by positivity, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace hNb hPφ
    p hp3 hp
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  set U := closure (boundaryHalfBall 1)
  have hmU : MapsTo e U U := fun y hy => (boundary_c2a_scaling_maps_slab hp3 hp hy).2
  have hmB : MapsTo e (boundaryHalfBall 1) (boundaryHalfBall 1) :=
    boundary_c2a_scaling_maps_halfBall hp3 hp
  have hd : ∀ x ∈ U, ∀ y ∈ U, ‖e x - e y‖ ≤ ‖x - y‖ := by
    intro x _ y _
    have heq : ‖e x - e y‖ = r * ‖x - y‖ := by
      simpa only [dist_eq_norm] using quasilinear_ballScaling_dist p x y hr0
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans_eq (one_mul _)
  have hec : ContDiff ℝ 2 e := contDiff_const.add (contDiff_id.const_smul r)
  have hr2 : r ^ 2 ≤ 1 := by norm_num [hr_def]
  -- rescaled data
  obtain ⟨hAe, hAeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p hr0 hr1 hA hmU
  obtain ⟨hze, hzeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p hr0 hr1 hz hmU
  obtain ⟨hφe, hφeN⟩ := boundary_c2a_c1Holder_comp_scaling hα.le p hr0 hr1 hφ hmU
  obtain ⟨hbc, hbcN⟩ := nondiv_holder_comp_contraction hα.le hb hmU hd
  obtain ⟨hbs, hbsN⟩ := nondiv_holder_const_smul hbc r
  obtain ⟨hfc, hfcN⟩ := nondiv_holder_comp_contraction hα.le hf hmU hd
  obtain ⟨hfs, hfsN⟩ := nondiv_holder_const_smul hfc (r ^ 2)
  obtain ⟨hLc, hLcN⟩ := nondiv_holder_comp_contraction hα.le hL hmU hd
  obtain ⟨hLs, hLsN⟩ := nondiv_holder_const_smul hLc (r ^ 2)
  rw [Real.norm_of_nonneg hr0.le] at hbsN
  rw [Real.norm_of_nonneg (sq_nonneg r)] at hfsN hLsN
  have hLeq : nondivClassicalOperator (A ∘ e) (fun x => r • b (e x)) (φ ∘ e) =
      fun x => r ^ 2 • (nondivClassicalOperator A b φ ∘ e) x := by
    funext y
    rw [boundary_nondiv_cover_classical_comp p hr0 A b φ y, smul_eq_mul]
    rfl
  have hfeq : (fun x => r ^ 2 * f (e x)) = fun x => r ^ 2 • (f ∘ e) x := rfl
  have hbeq : (fun x => r • b (e x)) = fun x => r • (b ∘ e) x := rfl
  have hweak := boundary_nondiv_cover_weak_rescale p hr0 (isOpen_boundaryHalfBall 1)
    (isOpen_boundaryHalfBall 1) hmB (hA.contDiff.mono subset_closure)
    ((hb.nondiv_continuousOn hα).mono subset_closure) (hz.contDiff.mono subset_closure)
    ((hf.nondiv_continuousOn hα).mono subset_closure) he
  have hzd' : ∀ x ∈ U, DifferentiableAt ℝ z (e x) := by
    intro x hx
    have hsub : U ⊆ closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∩
        {y | 0 ≤ y (Fin.last 2)} := by
      apply closure_minimal
      · exact fun y hy => ⟨ball_subset_closedBall hy.1,
          show 0 ≤ y (Fin.last 2) from le_of_lt (show 0 < y (Fin.last 2) from hy.2)⟩
      · exact isClosed_closedBall.inter
          (isClosed_le continuous_const (EuclideanSpace.proj (Fin.last 2)).continuous)
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hsub hx).1
    have hnorm : ‖e x‖ < 1 := by
      rw [frozenBallScaling_apply]
      calc ‖p + (1 / 2097152 : ℝ) • x‖ ≤ ‖p‖ + ‖(1 / 2097152 : ℝ) • x‖ := norm_add_le _ _
        _ = ‖p‖ + 1 / 2097152 * ‖x‖ := by rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
        _ < 1 := by nlinarith [norm_nonneg x]
    have h3 : 0 ≤ (e x) (Fin.last 2) := (hsub (hmU hx)).2
    rcases h3.eq_or_lt with h | h
    · exact hzd _ (mem_ball_zero_iff.mpr hnorm) h.symm
    · have hin : e x ∈ boundaryHalfBall 1 := ⟨mem_ball_zero_iff.mpr hnorm, h⟩
      exact (hz.contDiff.contDiffAt (mem_of_superset
        ((isOpen_boundaryHalfBall 1).mem_nhds hin) subset_closure)).differentiableAt one_ne_zero
  have hnφ := hφ.norm_nonneg
  have hnz := hz.norm_nonneg
  have hnf := hf.norm_nonneg
  have hnL := hL.norm_nonneg
  have hnb := hb.norm_nonneg
  have hnfc := hfc.norm_nonneg
  have hnLc := hLc.norm_nonneg
  have hnbc := hbc.norm_nonneg
  obtain ⟨hC2, hbd⟩ := hreg (A ∘ e) (fun x => r • b (e x)) (z ∘ e) (fun x => r ^ 2 * f (e x))
    (φ ∘ e) (e ⁻¹' V) P (hV.preimage e.continuous) (fun y hy => hKV (hmU hy)) hAe
    (by rw [hbeq]; exact hbs) hze (by rw [hfeq]; exact hfs) (hAeN.trans hAn)
    (by
      rw [hbeq]
      refine hbsN.trans ?_
      calc r * holderNorm α (b ∘ e) U ≤ 1 * holderNorm α b U := mul_le_mul hr1 hbcN hnbc zero_le_one
        _ = holderNorm α b U := one_mul _
        _ ≤ M := hbn)
    (fun x hx => hcap _ (hmU hx)) (fun x hx v => hell _ (hmU hx) v) hweak
    (fun x hx => (hzd' x hx).comp x ((hec.differentiable (by norm_num)) x))
    (hφ2.comp hec.contDiffOn (mapsTo_preimage _ _)) hφe (by rw [hLeq]; exact hLs)
    (by
      intro x hx hx3
      apply htrace _ (hmU hx)
      change (p + r • x) (Fin.last 2) = 0
      rw [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hp3, hx3, mul_zero, add_zero])
    (by
      rw [hfeq, hLeq]
      have h3 : holderNorm α (fun x => r ^ 2 • (f ∘ e) x) U ≤ holderNorm α f U :=
        hfsN.trans ((mul_le_mul hr2 hfcN hnfc zero_le_one).trans_eq (one_mul _))
      have h4 : holderNorm α (fun x => r ^ 2 • (nondivClassicalOperator A b φ ∘ e) x) U ≤
          holderNorm α (nondivClassicalOperator A b φ) U :=
        hLsN.trans ((mul_le_mul hr2 hLcN hnLc zero_le_one).trans_eq (one_mul _))
      linarith)
    (by
      intro i j
      refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
      · have hex := hmB (boundaryNondivC2Slab_subset hx)
        rw [boundary_nondiv_cover_entry_comp, abs_mul, abs_of_nonneg (sq_nonneg r)]
        exact (mul_le_mul hr2 ((hPφ i j).1 _ hex) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      · have hex := hmB (boundaryNondivC2Slab_subset hx)
        have hey := hmB (boundaryNondivC2Slab_subset hy)
        rw [boundary_nondiv_cover_entry_comp, boundary_nondiv_cover_entry_comp, ← mul_sub,
          abs_mul, abs_of_nonneg (sq_nonneg r)]
        have hdist : dist (e x) (e y) ^ α ≤ dist x y ^ α := by
          apply Real.rpow_le_rpow dist_nonneg _ hα.le
          rw [quasilinear_ballScaling_dist p x y hr0]
          exact (mul_le_mul_of_nonneg_right hr1 dist_nonneg).trans_eq (one_mul _)
        calc r ^ 2 * |boundaryNeumannC2Entry φ (e x) i j - boundaryNeumannC2Entry φ (e y) i j|
            ≤ 1 * (P * dist (e x) (e y) ^ α) :=
              mul_le_mul hr2 ((hPφ i j).2 _ hex _ hey) (abs_nonneg _) zero_le_one
          _ ≤ P * dist x y ^ α := by
              rw [one_mul]
              exact mul_le_mul_of_nonneg_left hdist hP)
  -- scale back
  have hzw : z = (z ∘ e) ∘ e.symm := by
    funext x
    simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  refine ⟨?_, fun i j => ⟨?_, ?_⟩⟩
  · rw [hzw]
    exact boundary_c2a_contDiffOn_comp_scaling_symm p boundary_c2a_local_radius_pos hC2
  · rintro _ ⟨x, hx, rfl⟩
    rw [hzw, boundary_c2a_entry_comp_scaling, abs_mul, abs_of_nonneg (by positivity)]
    have h1 : 1 ≤ r⁻¹ ^ α := Real.one_le_rpow hri hα.le
    calc r⁻¹ ^ 2 * |boundaryNeumannC2Entry (z ∘ e) x i j| ≤ r⁻¹ ^ 2 * (C + P) :=
          mul_le_mul_of_nonneg_left ((hbd i j).1 x hx) (by positivity)
      _ ≤ r⁻¹ ^ 2 * (C + P) * r⁻¹ ^ α := le_mul_of_one_le_right (by positivity) h1
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [hzw, boundary_c2a_entry_comp_scaling, boundary_c2a_entry_comp_scaling, ← mul_sub,
      abs_mul, abs_of_nonneg (by positivity)]
    have hd' : dist x y = r⁻¹ * dist (e x) (e y) := by
      rw [quasilinear_ballScaling_dist p x y hr0, ← mul_assoc, inv_mul_cancel₀ hr0.ne', one_mul]
    have hdp : dist x y ^ α = r⁻¹ ^ α * dist (e x) (e y) ^ α := by
      rw [hd', Real.mul_rpow (by positivity) dist_nonneg]
    calc r⁻¹ ^ 2 * |boundaryNeumannC2Entry (z ∘ e) x i j - boundaryNeumannC2Entry (z ∘ e) y i j|
        ≤ r⁻¹ ^ 2 * ((C + P) * dist x y ^ α) :=
          mul_le_mul_of_nonneg_left ((hbd i j).2 x hx y hy) (by positivity)
      _ = r⁻¹ ^ 2 * (C + P) * r⁻¹ ^ α * dist (e x) (e y) ^ α := by rw [hdp]; ring

/-- A coordinate entry of a bilinear map is bounded by its operator norm. -/
lemma boundary_nondiv_cover_bilinear_entry_le
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (i j : Fin 3) :
    |L (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ ‖L‖ := by
  have h1 := (L (EuclideanSpace.single i 1)).le_opNorm (EuclideanSpace.single j 1)
  have h2 := L.le_opNorm (EuclideanSpace.single i 1)
  simp only [PiLp.norm_single, norm_one, mul_one] at h1 h2
  rw [← Real.norm_eq_abs]
  exact h1.trans h2

/-- On an open set where `z` is C², the iterated coordinate derivative is a Hessian entry. -/
lemma boundary_nondiv_cover_entry_eq {z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hz : ContDiffOn ℝ 2 z U)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ U) (i j : Fin 3) :
    boundaryNeumannC2Entry z x i j =
      fderiv ℝ (fderiv ℝ z) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  unfold boundaryNeumannC2Entry
  rw [nondiv_fderiv_coordinate_eq hU hz j hx]
  rfl

/-- A C²,α bound on an open set bounds the iterated coordinate derivatives and their Hölder
quotients. -/
lemma boundary_nondiv_cover_entry_of_c2Holder {α B : ℝ} {z : EuclideanSpace ℝ (Fin 3) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hz : HasC2HolderOn α z U)
    (hB : schauderC2HolderNorm α z U ≤ B) (i j : Fin 3) :
    (∀ x ∈ U, |boundaryNeumannC2Entry z x i j| ≤ B) ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤ B * dist x y ^ α := by
  have hH : holderNorm α (fderiv ℝ (fderiv ℝ z)) U ≤ B := by
    have h0 := hz.function_holder.norm_nonneg
    have h1 := hz.derivative_holder.norm_nonneg
    unfold schauderC2HolderNorm at hB
    linarith
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · rw [boundary_nondiv_cover_entry_eq hU hz.contDiff hx]
    exact (boundary_nondiv_cover_bilinear_entry_le _ i j).trans
      ((hz.hessian_holder.nondiv_norm_le hx).trans hH)
  · rw [boundary_nondiv_cover_entry_eq hU hz.contDiff hx,
      boundary_nondiv_cover_entry_eq hU hz.contDiff hy]
    have h := boundary_nondiv_cover_bilinear_entry_le
      (fderiv ℝ (fderiv ℝ z) x - fderiv ℝ (fderiv ℝ z) y) i j
    simp only [sub_apply] at h
    exact h.trans (boundary_c2a_local_holder_pointwise hz.hessian_holder hH x hx y hy)

/-- The size of the half-ball region carried by one rescaled slab. -/
lemma boundary_nondiv_cover_slab_mem {p w : EuclideanSpace ℝ (Fin 3)}
    (hp3 : p (Fin.last 2) = 0) (hw : ‖w - p‖ < 3 / 8796093022208)
    (hw3 : 0 < w (Fin.last 2)) :
    w ∈ frozenBallScaling p boundary_c2a_local_radius_pos '' boundaryNondivC2Slab := by
  set e := frozenBallScaling p boundary_c2a_local_radius_pos
  refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
  set v : EuclideanSpace ℝ (Fin 3) := (4 / 3 : ℝ) • e.symm w with hv
  have hv' : v = (8388608 / 3 : ℝ) • (w - p) := by
    rw [hv, frozenBallScaling_symm_apply, smul_smul]
    norm_num
  have hvn : ‖v‖ < 1 / 1048576 := by
    rw [hv', norm_smul, Real.norm_of_nonneg (by norm_num)]
    have := norm_nonneg (w - p)
    nlinarith
  have hv3 : |v (Fin.last 2)| ≤ ‖v‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v (Fin.last 2)
  have hproj : ‖graphProjectionN 2 v‖ ≤ ‖v‖ := by
    have h := norm_sq_graphProjectionN v
    nlinarith [norm_nonneg v, norm_nonneg (graphProjectionN 2 v), sq_nonneg (v (Fin.last 2))]
  change v ∈ boundaryC1UpperSlab
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_preimage, mem_ball_zero_iff]
    linarith
  · change |v (Fin.last 2)| < 1 / 1048576
    linarith
  · change 0 < v (Fin.last 2)
    rw [hv', PiLp.smul_apply, PiLp.sub_apply, hp3, sub_zero, smul_eq_mul]
    positivity

/-- `thm:boundary-nondiv` on `B⁺_{1/2}`, with ambient differentiability of `z` required only on
the open flat face `Γ₁`: under the hypotheses of the slab estimate, with the Hessian bounds of
the boundary datum on the unit half ball, the solution is C² on the open half ball `B⁺_{1/2}`
with uniformly bounded, uniformly α-Hölder second derivatives. -/
theorem boundary_nondiv_half_ball_of_face {α lam cap M N P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1, x (Fin.last 2) = 0 →
        DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryHalfBall 1, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryHalfBall 1, ∀ y ∈ boundaryHalfBall 1,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ContDiffOn ℝ 2 z (boundaryHalfBall (1 / 2)) ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry z x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨Kb, hKb, hbd⟩ :=
    boundary_nondiv_cover_boundary_piece hα hα1 hlam hlamcap hM hN hP
  obtain ⟨Ci, hCi, hint⟩ :=
    nondiv_schauder_c1_ball (n := 3) (by norm_num) (by norm_num) hα hα1 hlam hlamcap hM
  set δ : ℝ := 3 / 8796093022208 with hδ_def
  set s : ℝ := δ / 2 with hs_def
  set ρ : ℝ := δ / 4 with hρ_def
  have hδ : 0 < δ := by norm_num [hδ_def]
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 := by norm_num [hs_def, hδ_def]
  have hρ : 0 < ρ := by positivity
  set K : ℝ := Kb + Ci * s⁻¹ ^ 3 * N with hK_def
  have hK : 0 < K := by positivity
  have hs2 : s < 1 / 2 := by norm_num [hs_def, hδ_def]
  have hρs : ρ = s / 2 := by rw [hρ_def, hs_def]; ring
  have hsδ : s = δ / 2 := hs_def
  have hρδ : ρ = δ / 4 := hρ_def
  have hKN : 0 ≤ Ci * s⁻¹ ^ 3 * N := by positivity
  clear_value K ρ s δ
  refine ⟨max K (2 * K * (ρ ^ α)⁻¹), lt_max_of_lt_left hK, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace hNb hPφ
  set U := closure (boundaryHalfBall 1)
  have hzf : nondivC1HolderNorm α z U + holderNorm α f U ≤ N := by
    have := hφ.norm_nonneg
    have := hL.norm_nonneg
    linarith
  have hbdz := hbd A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd hφ2 hφ hL htrace
    hNb hPφ
  have hloc : ∀ x ∈ boundaryHalfBall (1 / 2), ∃ O : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen O ∧ x ∈ O ∧ (∀ y ∈ boundaryHalfBall (1 / 2), dist x y < ρ → y ∈ O) ∧
      ContDiffOn ℝ 2 z O ∧ ∀ i j : Fin 3,
        (∀ w ∈ O, |boundaryNeumannC2Entry z w i j| ≤ K) ∧
        ∀ w ∈ O, ∀ w' ∈ O,
          |boundaryNeumannC2Entry z w i j - boundaryNeumannC2Entry z w' i j| ≤
            K * dist w w' ^ α := by
    intro x hx
    obtain ⟨hx1, hx3⟩ := hx
    rw [mem_ball_zero_iff] at hx1
    change 0 < x (Fin.last 2) at hx3
    by_cases hxs : x (Fin.last 2) < s
    · -- boundary piece at the foot point
      set p : EuclideanSpace ℝ (Fin 3) :=
        x - x (Fin.last 2) • EuclideanSpace.single (Fin.last 2) 1 with hp_def
      have hp3 : p (Fin.last 2) = 0 := by simp [hp_def]
      have hxp : ‖x - p‖ = x (Fin.last 2) := by
        rw [hp_def, sub_sub_cancel, norm_smul, PiLp.norm_single, norm_one, mul_one,
          Real.norm_of_nonneg hx3.le]
      have hpx : ‖p‖ ^ 2 + x (Fin.last 2) ^ 2 = ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
          Fin.sum_univ_three, Fin.sum_univ_three]
        simp [hp_def]
      have hp : ‖p‖ ≤ 1 / 2 := by
        nlinarith [norm_nonneg x, norm_nonneg p]
      obtain ⟨h2, hent⟩ := hbdz p hp3 hp
      refine ⟨_, (frozenBallScaling p boundary_c2a_local_radius_pos).isOpenMap _
        isOpen_boundaryNondivC2Slab, ?_, ?_, h2, fun i j => ⟨fun w hw => ?_,
          fun w hw w' hw' => ?_⟩⟩
      · exact boundary_nondiv_cover_slab_mem hp3 (by rw [hxp, ← hδ_def]; linarith) hx3
      · intro y hy hxy
        obtain ⟨-, hy3⟩ := hy
        apply boundary_nondiv_cover_slab_mem hp3 _ hy3
        rw [← hδ_def]
        calc ‖y - p‖ ≤ ‖y - x‖ + ‖x - p‖ := norm_sub_le_norm_sub_add_norm_sub y x p
          _ < ρ + s := by
              rw [hxp, ← dist_eq_norm, dist_comm]
              linarith
          _ < δ := by linarith
      · exact ((hent i j).1 w hw).trans (by linarith)
      · exact ((hent i j).2 w hw w' hw').trans (mul_le_mul_of_nonneg_right
          (by linarith) (Real.rpow_nonneg dist_nonneg _))
    · -- interior ball
      have hball : ball x s ⊆ boundaryHalfBall 1 := by
        intro w hw
        rw [mem_ball, dist_eq_norm] at hw
        refine ⟨?_, ?_⟩
        · rw [mem_ball_zero_iff]
          calc ‖w‖ ≤ ‖w - x‖ + ‖x‖ := norm_le_norm_sub_add w x
            _ < 1 := by linarith
        · change 0 < w (Fin.last 2)
          have h3 : |(w - x) (Fin.last 2)| ≤ ‖w - x‖ := by
            simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (w - x) (Fin.last 2)
          rw [PiLp.sub_apply] at h3
          have := (abs_le.mp h3).1
          linarith
      have hbU : ball x s ⊆ U := hball.trans subset_closure
      obtain ⟨hAs, hAsN⟩ := hA.mono hbU
      obtain ⟨hzs, hzsN⟩ := hz.mono hbU
      obtain ⟨hbs, hbsN⟩ := schauder_holder_mono hb hbU
      obtain ⟨hfs, hfsN⟩ := schauder_holder_mono hf hbU
      obtain ⟨hC2, hC2N⟩ := hint x s hs0 hs1 A b z f hAs hbs hzs hfs (hAsN.trans hAn)
        (hbsN.trans hbn) (fun w hw => hcap w (hbU hw)) (fun w hw v => hell w (hbU hw) v)
        (he.mono hball)
      have hB : schauderC2HolderNorm α z (ball x (s / 2)) ≤ K := by
        refine hC2N.trans ?_
        have : Ci * s⁻¹ ^ 3 * (nondivC1HolderNorm α z (ball x s) + holderNorm α f (ball x s)) ≤
            Ci * s⁻¹ ^ 3 * N :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      refine ⟨ball x (s / 2), isOpen_ball, mem_ball_self (by positivity), ?_, hC2.contDiff,
        fun i j => boundary_nondiv_cover_entry_of_c2Holder isOpen_ball hC2 hB i j⟩
      intro y _ hxy
      rw [mem_ball, dist_comm]
      linarith
  choose! O hOo hxO hOρ hO2 hOb using hloc
  refine ⟨fun x hx => ((hO2 x hx).contDiffAt ((hOo x hx).mem_nhds (hxO x hx))).contDiffWithinAt,
    fun i j => ⟨fun x hx => ((hOb x hx i j).1 x (hxO x hx)).trans (le_max_left _ _), ?_⟩⟩
  apply boundary_nondiv_cover_holder_of_local (g := fun x => boundaryNeumannC2Entry z x i j)
    hα.le hK.le hρ (fun x hx => (hOb x hx i j).1 x (hxO x hx))
  intro x hx y hy hxy
  exact (hOb x hx i j).2 x (hxO x hx) y (hOρ x hx y hy hxy)

/-- Points of the open flat face lie in the closure of the unit half ball. -/
lemma boundary_nondiv_cover_face_mem_closure {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin 3)) 1) (hx3 : x (Fin.last 2) = 0) :
    x ∈ closure (boundaryHalfBall 1) := by
  rw [mem_ball_zero_iff] at hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t := min ε (1 - ‖x‖) / 2 with ht_def
  have ht : 0 < t := by
    have : 0 < min ε (1 - ‖x‖) := lt_min hε (by linarith)
    positivity
  have htε : t < ε := by have := min_le_left ε (1 - ‖x‖); linarith
  have ht1 : t < 1 - ‖x‖ := by
    have := min_le_right ε (1 - ‖x‖)
    have : 0 < 1 - ‖x‖ := by linarith
    linarith
  refine ⟨x + t • EuclideanSpace.single (Fin.last 2) 1, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball_zero_iff]
    calc ‖x + t • EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖
        ≤ ‖x‖ + ‖t • EuclideanSpace.single (Fin.last 2) (1 : ℝ)‖ := norm_add_le _ _
      _ = ‖x‖ + t := by
          rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_of_nonneg ht.le]
      _ < 1 := by linarith
  · change 0 < (x + t • EuclideanSpace.single (Fin.last 2) (1 : ℝ)) (Fin.last 2)
    rw [PiLp.add_apply, PiLp.smul_apply, hx3, zero_add, smul_eq_mul]
    simpa only [PiLp.single_apply, ite_true, mul_one] using ht
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, PiLp.norm_single, norm_one,
      mul_one, Real.norm_of_nonneg ht.le]
    exact htε

/-- `thm:boundary-nondiv` on `B⁺_{1/2}`, exactly under the hypotheses of the slab estimate
`boundary_nondiv_c2_holder_trace`, except that the Hessian bounds of the boundary datum are
required on the unit half ball: the solution is C² on the open half ball `B⁺_{1/2}` with
uniformly bounded, uniformly α-Hölder second derivatives. -/
theorem boundary_nondiv_half_ball {α lam cap M N P : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hlam : 0 < lam) (hlamcap : lam ≤ cap)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hP : 0 ≤ P) :
    ∃ C > 0, ∀ (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3))
      (b : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (z f φ : EuclideanSpace ℝ (Fin 3) → ℝ) (V : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen V → closure (boundaryHalfBall 1) ⊆ V →
      HasC1HolderOn α A (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α b (closure (boundaryHalfBall 1)) →
      HasC1HolderOn α z (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α f (closure (boundaryHalfBall 1)) →
      nondivC1HolderNorm α A (closure (boundaryHalfBall 1)) ≤ M →
      holderNorm α b (closure (boundaryHalfBall 1)) ≤ M →
      (∀ x ∈ closure (boundaryHalfBall 1), ‖A x‖ ≤ cap) →
      (∀ x ∈ closure (boundaryHalfBall 1), ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (A x v)) →
      IsWeakNondivergenceEquationOn A b z f (boundaryHalfBall 1) →
      (∀ x ∈ closure (boundaryHalfBall 1), DifferentiableAt ℝ z x) →
      ContDiffOn ℝ 2 φ V →
      HasC1HolderOn α φ (closure (boundaryHalfBall 1)) →
      HasFiniteHolderNormOn α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) →
      (∀ x ∈ closure (boundaryHalfBall 1), x (Fin.last 2) = 0 → z x = φ x) →
      nondivC1HolderNorm α z (closure (boundaryHalfBall 1)) +
          nondivC1HolderNorm α φ (closure (boundaryHalfBall 1)) +
          holderNorm α f (closure (boundaryHalfBall 1)) +
          holderNorm α (nondivClassicalOperator A b φ) (closure (boundaryHalfBall 1)) ≤ N →
      (∀ i j : Fin 3, (∀ x ∈ boundaryHalfBall 1, |boundaryNeumannC2Entry φ x i j| ≤ P) ∧
        ∀ x ∈ boundaryHalfBall 1, ∀ y ∈ boundaryHalfBall 1,
          |boundaryNeumannC2Entry φ x i j - boundaryNeumannC2Entry φ y i j| ≤
            P * dist x y ^ α) →
      ContDiffOn ℝ 2 z (boundaryHalfBall (1 / 2)) ∧
      ∀ i j : Fin 3,
        (∀ x ∈ boundaryHalfBall (1 / 2), |boundaryNeumannC2Entry z x i j| ≤ C) ∧
        ∀ x ∈ boundaryHalfBall (1 / 2), ∀ y ∈ boundaryHalfBall (1 / 2),
          |boundaryNeumannC2Entry z x i j - boundaryNeumannC2Entry z y i j| ≤
            C * dist x y ^ α := by
  obtain ⟨C, hC, hreg⟩ := boundary_nondiv_half_ball_of_face hα hα1 hlam hlamcap hM hN hP
  refine ⟨C, hC, ?_⟩
  intro A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he hzd
  exact hreg A b z f φ V hV hKV hA hb hz hf hAn hbn hcap hell he
    (fun x hx hx3 => hzd x (boundary_nondiv_cover_face_mem_closure hx hx3))

end LiquidDrop
