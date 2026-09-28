import NoCompromise.Regularity.UniformCenters
import NoCompromise.Regularity.SlabCap

/-!
# Quarter-scale centres and the boundary cone estimate

Blueprint `thm:eps-regularity`, Step 3 (single-valuedness). The change of
centre at quarter scale, the normal iteration at every boundary centre of the
quarter cylinder, and the two-point cone estimate which follows from the
general height bound.
-/

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology ENNReal
namespace LiquidDrop

/-- Change of centre at quarter scale. -/
theorem excess_change_center_quarter (E : Set AmbientSpace)
    (hE : HasLocallyFinitePerimeter E) (hmE : NullMeasurableSet E volume)
    {x z ν : AmbientSpace} {r : ℝ} (hr : 0 < r) (hν : ‖ν‖ = 1)
    (hz : z ∈ cylinder x (r / 4) ν) :
    cylindricalExcess E hE hmE z (r / 4) ν ≤ 16 * cylindricalExcess E hE hmE x r ν := by
  have hsub : cylinder z (r / 4) ν ⊆ cylinder x r ν :=
    (cylinder_subset_add_radius hz).trans (cylinder_mono (by linarith))
  have hi := normalExcessIntegral_mono E hE hmE (isBounded_cylinder x r hν) hsub ν
  have hd := div_le_div_of_nonneg_right hi (sq_nonneg (r / 4))
  change normalExcessIntegral E hE hmE (cylinder z (r / 4) ν) ν / (r / 4) ^ 2 ≤
    16 * (normalExcessIntegral E hE hmE (cylinder x r ν) ν / r ^ 2)
  calc
    _ ≤ normalExcessIntegral E hE hmE (cylinder x r ν) ν / (r / 4) ^ 2 := hd
    _ = _ := by ring

/-- The normal iteration at every boundary centre of the quarter cylinder,
with a single threshold fixed in advance. -/
theorem normals_cauchy_quarter_centers :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 / 32 ∧ ∃ ε₀' > 0, ∃ C > 0,
      ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω)
        (x : AmbientSpace) (r : ℝ) (ν₀ : AmbientSpace),
      0 < r → r ≤ 1 → ‖ν₀‖ = 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable x r ν₀ + ω * r ≤ ε₀' →
      ∀ z ∈ frontier (densityOne E) ∩ cylinder x (r / 4) ν₀,
      ∃ (ν : ℕ → AmbientSpace) (νlim : AmbientSpace),
        ν 0 = ν₀ ∧ (∀ j, ‖ν j‖ = 1) ∧ ‖νlim‖ = 1 ∧ Tendsto ν atTop (𝓝 νlim) ∧
        let e := fun j => cylindricalExcess E hE.locallyFinite hE.nullMeasurable
          z (θ ^ j * (r / 4)) (ν j)
        ∀ j, e j + ω * (θ ^ j * (r / 4)) ≤ 16 * ε₀' ∧
          e j + ω * (θ ^ j * (r / 4)) ≤ C * θ ^ j * (e 0 + ω * (r / 4)) ∧
          ‖ν (j + 1) - ν j‖ ^ 2 ≤ C * (e j + ω * (θ ^ j * (r / 4))) ∧
          ‖ν j - νlim‖ ≤ C * θ ^ ((j : ℝ) / 2) * Real.sqrt (e 0 + ω * (r / 4)) := by
  obtain ⟨θ, hθ, hθ32, ε, hε, C, hC, hmain⟩ := normals_cauchy
  refine ⟨θ, hθ, hθ32, ε / 16, by positivity, C, hC, ?_⟩
  intro E ω hE x r ν₀ hr hr1 hν₀ hsmall z hz
  have hr4 : 0 < r / 4 := by linarith
  have hr41 : r / 4 ≤ 1 := by linarith
  have hcenter :=
    excess_change_center_quarter E hE.locallyFinite hE.nullMeasurable hr hν₀ hz.2
  have hωr : 0 ≤ ω * r := mul_nonneg hE.nonneg hr.le
  have hsmall' :
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable z (r / 4) ν₀ +
        ω * (r / 4) ≤ ε := by linarith
  obtain ⟨ν, νlim, hinit, hunit, hnlim, htend, hrest⟩ :=
    hmain E ω hE z (r / 4) ν₀ hr4 hr41 hν₀ hz.1 hsmall'
  refine ⟨ν, νlim, hinit, hunit, hnlim, htend, ?_⟩
  dsimp only
  intro j
  obtain ⟨hs, henergy, hincr, hrate⟩ := hrest j
  exact ⟨by linarith, henergy, hincr, hrate⟩

lemma inner_single_two_eq (v : AmbientSpace) :
    inner ℝ (EuclideanSpace.single 2 1 : AmbientSpace) v = v 2 := by
  simp [EuclideanSpace.inner_single_left]

lemma norm_sq_sub_eq_graphProjection (p q : AmbientSpace) :
    ‖q - p‖ ^ 2 = ‖graphProjectionN 2 q - graphProjectionN 2 p‖ ^ 2 + (q 2 - p 2) ^ 2 := by
  rw [← map_sub, norm_sq_graphProjectionN (q - p)]
  rfl

/-- The two-point cone estimate at boundary points of the quarter cylinder,
from the general height bound. -/
theorem boundary_cone_estimate
    (hH : ∀ η : ℝ, 0 < η → ∃ ε : ℝ, 0 < ε ∧ ∀ (E : Set AmbientSpace) (ω : ℝ)
      (hE : IsOmegaMinimal E ω) (p ν : AmbientSpace) (s : ℝ),
      p ∈ frontier (densityOne E) → ‖ν‖ = 1 → 0 < s → s ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable p s ν + ω * s ≤ ε →
      ∀ y ∈ frontier (densityOne E) ∩ cylinder p (3 * s / 4) ν,
        |inner ℝ ν (y - p)| < η * s) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (E : Set AmbientSpace) (ω : ℝ) (hE : IsOmegaMinimal E ω) (r : ℝ),
      (0 : AmbientSpace) ∈ frontier (densityOne E) → 0 < r → r ≤ 1 →
      cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
        (EuclideanSpace.single 2 1) + ω * r ≤ ε₀ →
      ∀ p ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
      ∀ q ∈ frontier (densityOne E) ∩ standardCylinder (r / 4),
        |q 2 - p 2| ≤ ‖graphProjectionN 2 q - graphProjectionN 2 p‖ := by
  obtain ⟨θ, hθ, hθ32, ε₀', hε₀', C, hC, hb⟩ := normals_cauchy_quarter_centers
  obtain ⟨εH, hεH, hHη⟩ := hH (θ / 8) (by positivity)
  have hpos : 0 < min ε₀' (min εH (min (εH / (16 * C)) (1 / (1024 * C ^ 2)))) :=
    lt_min hε₀' (lt_min hεH (lt_min (by positivity) (by positivity)))
  refine ⟨min ε₀' (min εH (min (εH / (16 * C)) (1 / (1024 * C ^ 2)))), hpos, ?_⟩
  intro E ω hE r h0 hr hr1 hsmall p hp q hq
  have h1 := hsmall.trans (min_le_left _ _)
  have h2 := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h4 := hsmall.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hθ1 : θ < 1 := by linarith
  have he₃ : ‖(EuclideanSpace.single 2 1 : AmbientSpace)‖ = 1 := by simp
  have hωr : 0 ≤ ω * r := mul_nonneg hE.nonneg hr.le
  have hExc0 : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
      (EuclideanSpace.single 2 1) :=
    div_nonneg (normalExcessIntegral_nonneg _ _ _ _ _) (sq_nonneg _)
  have hpc : p ∈ cylinder 0 (r / 4) (EuclideanSpace.single 2 1) := by
    rw [← standardCylinder_eq_cylinder]; exact hp.2
  have hqc : q ∈ cylinder 0 (r / 4) (EuclideanSpace.single 2 1) := by
    rw [← standardCylinder_eq_cylinder]; exact hq.2
  have hid := norm_sq_sub_eq_graphProjection p q
  have hPnn : 0 ≤ ‖graphProjectionN 2 q - graphProjectionN 2 p‖ := norm_nonneg _
  refine abs_le_of_sq_le_sq ?_ hPnn
  rcases lt_or_ge ‖q - p‖ (r / 8) with hnear | hfar
  · rcases (norm_nonneg (q - p)).eq_or_lt with hzero | hqp
    · have hv : q - p = 0 := norm_eq_zero.mp hzero.symm
      have hd : q 2 - p 2 = 0 := by
        have := congrArg (fun v : AmbientSpace => v 2) hv
        simpa using this
      rw [hd, zero_pow two_ne_zero]; positivity
    -- near case: run the iteration at the centre `p`
    obtain ⟨ν, νlim, hinit, hunit, hnlim, htend, hrest⟩ :=
      hb E ω hE 0 r (EuclideanSpace.single 2 1) hr hr1 he₃ h1 p ⟨hp.1, hpc⟩
    dsimp only at hrest
    have hex : ∃ n : ℕ, θ ^ n * (r / 4) / 2 ≤ ‖q - p‖ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
        (show 0 < ‖q - p‖ * 8 / r by positivity) hθ1
      refine ⟨n, ?_⟩
      have : θ ^ n * r < ‖q - p‖ * 8 := by rwa [lt_div_iff₀ hr] at hn
      linarith
    classical
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, θ ^ m * (r / 4) / 2 ≤ ‖q - p‖ ∧
        ∀ k < m, ¬ θ ^ k * (r / 4) / 2 ≤ ‖q - p‖ :=
      ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
    obtain _ | j := m
    · simp only [pow_zero, one_mul] at hm
      linarith
    have hjlt : ‖q - p‖ < θ ^ j * (r / 4) / 2 := lt_of_not_ge (hmin j (Nat.lt_succ_self j))
    rw [pow_succ] at hm
    have hθj : θ ^ j ≤ 1 := pow_le_one₀ hθ.le hθ1.le
    have hθj0 : 0 < θ ^ j := pow_pos hθ j
    have hs : 0 < θ ^ j * (r / 4) := by positivity
    have hs1 : θ ^ j * (r / 4) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hθj (by positivity : (0 : ℝ) ≤ r / 4)
      linarith
    obtain ⟨_, henergy, _, hrate⟩ := hrest j
    obtain ⟨_, _, _, hrate0⟩ := hrest 0
    have he0 : cylindricalExcess E hE.locallyFinite hE.nullMeasurable p (θ ^ 0 * (r / 4)) (ν 0)
        ≤ 16 * cylindricalExcess E hE.locallyFinite hE.nullMeasurable 0 r
          (EuclideanSpace.single 2 1) := by
      rw [pow_zero, one_mul, hinit]
      exact excess_change_center_quarter E hE.locallyFinite hE.nullMeasurable hr he₃ hpc
    have he0nn : 0 ≤ cylindricalExcess E hE.locallyFinite hE.nullMeasurable p
        (θ ^ 0 * (r / 4)) (ν 0) :=
      div_nonneg (normalExcessIntegral_nonneg _ _ _ _ _) (sq_nonneg _)
    set X := cylindricalExcess E hE.locallyFinite hE.nullMeasurable p
        (θ ^ 0 * (r / 4)) (ν 0) + ω * (r / 4) with hXdef
    have hX0 : 0 ≤ X := by linarith
    have hX : X ≤ 16 * min ε₀' (min εH (min (εH / (16 * C)) (1 / (1024 * C ^ 2)))) := by
      linarith
    -- the excess at step `j` is below the height-bound threshold
    have hej : cylindricalExcess E hE.locallyFinite hE.nullMeasurable p (θ ^ j * (r / 4)) (ν j)
        + ω * (θ ^ j * (r / 4)) ≤ εH := by
      have hX3 : X ≤ 16 * (εH / (16 * C)) := by linarith
      have hCθ : C * θ ^ j ≤ C := by
        have := mul_le_mul_of_nonneg_left hθj hC.le
        linarith
      have hCX : C * θ ^ j * X ≤ C * X := mul_le_mul_of_nonneg_right hCθ hX0
      have hfin : C * X ≤ εH := by
        calc C * X ≤ C * (16 * (εH / (16 * C))) := mul_le_mul_of_nonneg_left hX3 hC.le
          _ = εH := by first | field_simp | (field_simp; ring)
      linarith
    have hqcyl : q ∈ cylinder p (3 * (θ ^ j * (r / 4)) / 4) (ν j) := by
      apply ball_subset_cylinder p _ (hunit j)
      rw [mem_ball, dist_eq_norm]
      linarith
    have hinner := hHη E ω hE p (ν j) (θ ^ j * (r / 4)) hp.1 (hunit j) hs hs1 hej q
      ⟨hq.1, hqcyl⟩
    have hinner' : |inner ℝ (ν j) (q - p)| ≤ ‖q - p‖ / 4 := by
      have : θ / 8 * (θ ^ j * (r / 4)) = (θ ^ j * θ * (r / 4) / 2) / 4 := by ring
      linarith
    -- the normal at step `j` is close to the vertical axis
    have hsq : Real.sqrt X ≤ 1 / (8 * C) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have hX4 : X ≤ 16 * (1 / (1024 * C ^ 2)) := by linarith
      calc X ≤ 16 * (1 / (1024 * C ^ 2)) := hX4
        _ = (1 / (8 * C)) ^ 2 := by first | (field_simp; ring) | field_simp
    have hbound : ∀ k : ℕ, C * θ ^ ((k : ℝ) / 2) * Real.sqrt X ≤ 1 / 8 := by
      intro k
      have hk1 : θ ^ ((k : ℝ) / 2) ≤ 1 := Real.rpow_le_one hθ.le hθ1.le (by positivity)
      have hk0 : 0 ≤ θ ^ ((k : ℝ) / 2) := Real.rpow_nonneg hθ.le _
      calc C * θ ^ ((k : ℝ) / 2) * Real.sqrt X ≤ C * 1 * (1 / (8 * C)) := by
            gcongr
        _ = 1 / 8 := by first | (field_simp; ring) | field_simp
    have hνj : ‖ν j - EuclideanSpace.single 2 1‖ ≤ 1 / 4 := by
      have htri := norm_sub_le_norm_sub_add_norm_sub (ν j) νlim (ν 0)
      rw [hinit] at htri
      have hr0 := hbound 0
      have hrj := hbound j
      rw [hinit, norm_sub_rev (EuclideanSpace.single 2 1 : AmbientSpace) νlim] at hrate0
      linarith
    -- conclude
    have hsplit : q 2 - p 2 = inner ℝ (ν j) (q - p) +
        inner ℝ (EuclideanSpace.single 2 1 - ν j) (q - p) := by
      rw [inner_sub_left, inner_single_two_eq]
      simp only [PiLp.sub_apply]
      ring
    have hcs := abs_real_inner_le_norm (EuclideanSpace.single 2 1 - ν j) (q - p)
    rw [norm_sub_rev (EuclideanSpace.single 2 1 : AmbientSpace) (ν j)] at hcs
    have hcs' : ‖ν j - EuclideanSpace.single 2 1‖ * ‖q - p‖ ≤ 1 / 4 * ‖q - p‖ :=
      mul_le_mul_of_nonneg_right hνj (norm_nonneg _)
    have habs : |q 2 - p 2| ≤ ‖q - p‖ / 2 := by
      rw [hsplit]
      calc _ ≤ |inner ℝ (ν j) (q - p)| +
            |inner ℝ (EuclideanSpace.single 2 1 - ν j) (q - p)| := abs_add_le _ _
        _ ≤ _ := by linarith
    have hsq2 : (q 2 - p 2) ^ 2 ≤ (‖q - p‖ / 2) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rwa [sq_abs] at this
    linarith [sq_nonneg (q 2 - p 2)]
  · -- far case: the height bound at the centre `0` and scale `r`
    have hpy := hHη E ω hE 0 (EuclideanSpace.single 2 1) r h0 he₃ hr hr1 h2 p
      ⟨hp.1, cylinder_mono (by linarith) hpc⟩
    have hqy := hHη E ω hE 0 (EuclideanSpace.single 2 1) r h0 he₃ hr hr1 h2 q
      ⟨hq.1, cylinder_mono (by linarith) hqc⟩
    rw [sub_zero, inner_single_two_eq] at hpy hqy
    have hθr : θ / 8 * r ≤ r / 256 := by
      have := mul_le_mul_of_nonneg_right hθ32.le hr.le
      linarith
    have hd : |q 2 - p 2| < r / 128 := by
      calc |q 2 - p 2| ≤ |q 2| + |p 2| := abs_sub _ _
        _ < _ := by linarith
    have hd2 : (q 2 - p 2) ^ 2 < (r / 128) ^ 2 := by
      have := pow_lt_pow_left₀ hd (abs_nonneg _) two_ne_zero
      rwa [sq_abs] at this
    have hn2 : (r / 8) ^ 2 ≤ ‖q - p‖ ^ 2 := pow_le_pow_left₀ (by positivity) hfar 2
    linarith [sq_nonneg r]

end LiquidDrop

