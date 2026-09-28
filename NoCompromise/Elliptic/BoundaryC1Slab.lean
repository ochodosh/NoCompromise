import NoCompromise.Elliptic.BoundaryC1

/-!
# Boundary C¹,α regularity on a data-independent slab

`boundary_c1_holder` constructs its open set `W` as a union of balls of a fixed radius
around the flat half-disk, but only records that `W` contains the closed flat disk. For
passing to limits of tangential difference quotients (blueprint `thm:boundary-nondiv`,
`thm:boundary-C2a`) one needs a set on which all the estimates hold uniformly in the
data. `boundary_c1_holder_slab` has the same hypotheses and constants and additionally
asserts that `W` contains the fixed open convex slab `boundaryC1Slab`. The proof is that
of `boundary_c1_holder`, with the extra inclusion.
-/

noncomputable section
open MeasureTheory Filter Metric Set InnerProductSpace
open scoped ENNReal NNReal Topology Gradient RealInnerProductSpace
namespace LiquidDrop
set_option maxSynthPendingDepth 8

/-- A fixed open convex slab around the flat disk of radius `5/8`. -/
def boundaryC1Slab : Set (EuclideanSpace ℝ (Fin 3)) :=
  (graphProjectionN 2) ⁻¹' ball 0 (5 / 8) ∩ {x | |x (Fin.last 2)| < 1 / 1048576}

lemma isOpen_boundaryC1Slab : IsOpen boundaryC1Slab :=
  (isOpen_ball.preimage (graphProjectionN 2).continuous).inter
    (isOpen_lt ((continuous_abs.comp (EuclideanSpace.proj (Fin.last 2)).continuous))
      continuous_const)

lemma convex_boundaryC1Slab : Convex ℝ boundaryC1Slab := by
  refine ((convex_ball 0 (5 / 8)).linear_preimage (graphProjectionN 2).toLinearMap).inter ?_
  have h : {x : EuclideanSpace ℝ (Fin 3) | |x (Fin.last 2)| < 1 / 1048576} =
      (EuclideanSpace.proj (Fin.last 2) : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).toLinearMap ⁻¹'
        Ioo (-(1 / 1048576)) (1 / 1048576) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioo, abs_lt]
    rfl
  rw [h]
  exact (convex_Ioo _ _).linear_preimage _

lemma boundary_slab_dist_graphAppendN (p : EuclideanSpace ℝ (Fin 2)) (a b : ℝ) :
    dist (graphAppendN p a) (graphAppendN p b) = |a - b| := by
  rw [dist_eq_norm]
  have he : graphAppendN p a - graphAppendN p b =
      (a - b) • EuclideanSpace.single (Fin.last 2) (1 : ℝ) := by
    simp only [graphAppendN, sub_smul]
    abel
  rw [he, norm_smul]
  simp only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]

theorem boundary_c1_holder_slab {a lam cap HA HG M : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 0 < lam) (hcap : 0 ≤ cap)
    (hHA : 0 ≤ HA) (hHG : 0 ≤ HG) (hM : 0 ≤ M) :
    ∃ C P : ℝ, 0 < C ∧ 0 ≤ P ∧
      ∀ (u : EuclideanSpace ℝ (Fin 3) → ℝ)
        (F G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
        (A : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) →L[ℝ]
          EuclideanSpace ℝ (Fin 3)),
        BoundaryHolderUnitData a lam cap HA HG M u F G A →
        ∃ (W : Set (EuclideanSpace ℝ (Fin 3))) (v : EuclideanSpace ℝ (Fin 3) → ℝ),
          IsOpen W ∧ {x | ‖x‖ ≤ (1 / 2 : ℝ) ∧ x (Fin.last 2) = 0} ⊆ W ∧
          W ⊆ ball 0 (3 / 4 : ℝ) ∧ ContDiffOn ℝ 1 v W ∧
          v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] u ∧
          gradient v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] F ∧
          (∀ x ∈ W, ‖gradient v x‖ ≤ P) ∧
          (∀ x ∈ W, ∀ y ∈ W, ‖gradient v x - gradient v y‖ ≤ C * dist x y ^ a) ∧
          (∀ x ∈ W, x (Fin.last 2) = 0 → v x = 0) ∧ boundaryC1Slab ⊆ W := by
  classical
  obtain ⟨C₀, P, hC₀, hP, hlocal⟩ := boundary_holder_local_representatives
    ha ha1 hlam hcap hHA hHG hM
  let ρ : ℝ := 1 / 262144
  have hρ : 0 < ρ := by norm_num [ρ]
  let C := max C₀ (2 * P / (ρ / 4) ^ a) + 1
  have hC : 0 < C := by
    have hh := le_max_left C₀ (2 * P / (ρ / 4) ^ a)
    dsimp [C]
    linarith
  have hC₀C : C₀ ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one)
  have hfarC : 2 * P / (ρ / 4) ^ a ≤ C :=
    (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
  refine ⟨C, P, hC, hP, ?_⟩
  intro u F G A h
  let S := {z : EuclideanSpace ℝ (Fin 2) | ‖graphAppendN z 0‖ < (5 / 8 : ℝ)}
  let c (z : S) := graphAppendN z.val 0
  choose w hw he hwgrad hwholder hwflat using
    fun z : S => hlocal u F G A h z.val (z.property.trans (by norm_num))
  let W := ⋃ z : S, ball (c z) (ρ / 4)
  have hW : IsOpen W := isOpen_iUnion fun _ => isOpen_ball
  have hquarter : ρ / 4 ≤ ρ := by linarith
  obtain ⟨v, hv, hev⟩ := boundary_exists_c1_representative_of_local hW (u := boundaryRawOdd u) (by
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    refine ⟨ball (c z) ρ ∩ W, isOpen_ball.inter hW,
      ⟨ball_subset_ball hquarter hz, hx⟩, inter_subset_right, w z,
      (hw z).mono inter_subset_left, ?_⟩
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left (he z))
  have heq (z : S) : EqOn v (w z) (W ∩ ball (c z) ρ) := by
    have h₁ : v =ᵐ[volume.restrict (W ∩ ball (c z) ρ)] boundaryRawOdd u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left hev
    have h₂ : w z =ᵐ[volume.restrict (W ∩ ball (c z) ρ)] boundaryRawOdd u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (he z)
    exact Measure.eqOn_open_of_ae_eq (h₁.trans h₂.symm)
      (hW.inter isOpen_ball) (hv.continuousOn.mono inter_subset_left)
      ((hw z).continuousOn.mono inter_subset_right)
  have hgradEq (z : S) (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ W)
      (hxb : x ∈ ball (c z) ρ) : gradient v x = gradient (w z) x := by
    have hh : v =ᶠ[𝓝 x] w z :=
      Filter.eventually_of_mem ((hW.inter isOpen_ball).mem_nhds ⟨hx, hxb⟩)
        (fun _ hy => heq z hy)
    exact hh.gradient_eq
  have hWsmall : W ⊆ ball (0 : EuclideanSpace ℝ (Fin 3)) (3 / 4 : ℝ) := by
    intro x hx
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    have ht := dist_triangle x (c z) 0
    rw [dist_zero_right (c z)] at ht
    have hz' : dist x (c z) < ρ / 4 := hz
    have hc : ‖c z‖ < 5 / 8 := z.property
    change dist x 0 < 3 / 4
    norm_num [ρ] at hz'
    linarith
  have hupper : W ∩ {x | 0 < x (Fin.last 2)} ⊆ boundaryHalfBall 1 := by
    intro x hx
    exact ⟨ball_subset_ball (by norm_num) (hWsmall hx.1), hx.2⟩
  have hWU := hW.inter boundary_holder_open_upper
  have hevu : v =ᵐ[volume.restrict (W ∩ {x | 0 < x (Fin.last 2)})] u := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left hev,
      ae_restrict_mem hWU.measurableSet] with x hx hxU
    exact hx.trans (boundaryRawOdd_eq_upper u hxU.2)
  have hbound (x) (hx : x ∈ W) : ‖gradient v x‖ ≤ P := by
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    have hxb := ball_subset_ball hquarter hz
    rw [hgradEq z x hx hxb]
    exact hwgrad z x hxb
  refine ⟨W, v, hW, ?_, hWsmall, hv, hevu, ?_, hbound, ?_, ?_, ?_⟩
  · intro x hx
    let z : S := ⟨graphProjectionN 2 x, by
      have he : graphAppendN (graphProjectionN 2 x) 0 = x := by
        simpa only [hx.2] using graphAppendN_projection x
      change ‖graphAppendN (graphProjectionN 2 x) 0‖ < (5 / 8 : ℝ)
      rw [he]
      exact hx.1.trans_lt (by norm_num)⟩
    apply mem_iUnion.mpr
    refine ⟨z, ?_⟩
    have he : c z = x := by
      change graphAppendN (graphProjectionN 2 x) 0 = x
      simpa only [hx.2] using graphAppendN_projection x
    rw [he]
    exact mem_ball_self (by positivity)
  · exact (hasWeakGradientOn_of_contDiffOn hWU (hv.mono inter_subset_left)).unique hWU
      ((h.h1.mono hupper).toHasWeakGradientOn.congr_ae hevu.symm EventuallyEq.rfl)
  · intro x hx y hy
    by_cases hclose : dist x y < ρ / 4
    · obtain ⟨z, hz⟩ := mem_iUnion.mp hx
      have hxb := ball_subset_ball hquarter hz
      have hyb : y ∈ ball (c z) ρ := by
        have ht := dist_triangle y x (c z)
        rw [dist_comm y x] at ht
        have hxz : dist x (c z) < ρ / 4 := hz
        change dist y (c z) < ρ
        have hsum : dist x y + dist x (c z) < ρ / 4 + ρ / 4 := add_lt_add hclose hxz
        have hhalf : dist y (c z) < ρ / 4 + ρ / 4 := lt_of_le_of_lt ht hsum
        have heq : (ρ / 4 + ρ / 4 : ℝ) = ρ / 2 := by ring
        have hlt : dist y (c z) < ρ / 2 := heq ▸ hhalf
        have hρhalf : ρ / 2 < ρ := by linarith [hρ]
        exact lt_trans hlt hρhalf
      rw [hgradEq z x hx hxb, hgradEq z y hy hyb]
      exact (hwholder z x hxb y hyb).trans (mul_le_mul_of_nonneg_right hC₀C
        (Real.rpow_nonneg dist_nonneg a))
    · have hdist : ρ / 4 ≤ dist x y := le_of_not_gt hclose
      have hp : 0 < (ρ / 4) ^ a := Real.rpow_pos_of_pos (by positivity) a
      calc
        _ ≤ ‖gradient v x‖ + ‖gradient v y‖ := norm_sub_le _ _
        _ ≤ 2 * P := by linarith [hbound x hx, hbound y hy]
        _ = (2 * P / (ρ / 4) ^ a) * (ρ / 4) ^ a :=
          (div_mul_cancel₀ _ hp.ne').symm
        _ ≤ (2 * P / (ρ / 4) ^ a) * dist x y ^ a :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hdist ha.le)
            (by positivity)
        _ ≤ C * dist x y ^ a := mul_le_mul_of_nonneg_right hfarC
          (Real.rpow_nonneg dist_nonneg a)
  · intro x hx hflat
    obtain ⟨z, hz⟩ := mem_iUnion.mp hx
    have hxb := ball_subset_ball hquarter hz
    exact (heq z ⟨hx, hxb⟩).trans (hwflat z x hxb hflat)
  · intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx1' : ‖graphProjectionN 2 x‖ < 5 / 8 := by
      simpa only [mem_preimage, mem_ball, dist_zero_right] using hx1
    let z : S := ⟨graphProjectionN 2 x, by
      change ‖graphAppendN (graphProjectionN 2 x) 0‖ < (5 / 8 : ℝ)
      have h := norm_sq_graphProjectionN (graphAppendN (graphProjectionN 2 x) 0)
      simp only [graphProjectionN_append, graphAppendN_last] at h
      nlinarith [norm_nonneg (graphAppendN (graphProjectionN 2 x) 0),
        norm_nonneg (graphProjectionN 2 x)]⟩
    apply mem_iUnion.mpr
    refine ⟨z, ?_⟩
    change dist x (graphAppendN (graphProjectionN 2 x) 0) < ρ / 4
    have hdist : dist x (graphAppendN (graphProjectionN 2 x) 0) = |x (Fin.last 2)| := by
      nth_rw 1 [← graphAppendN_projection x]
      rw [boundary_slab_dist_graphAppendN, sub_zero]
    have hρ4 : ρ / 4 = 1 / 1048576 := by norm_num [ρ]
    rw [hdist, hρ4]
    exact hx2

end LiquidDrop
