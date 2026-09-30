module

public import NoCompromise.Ball.PotentialAngular
public import NoCompromise.Ball.Perimeter
public import NoCompromise.Energy.Scaling

@[expose] public section

/-!
# Exact Newtonian potential and energy of a ball

Spherical coordinates, the proved elementary angular integral, and a radial
polynomial integral compute the original Coulomb potential at every interior or
boundary point. Integrating this proved potential gives the exact Coulomb energy.
The volume and variational-perimeter identities then yield the prescribed-volume
ball's full liquid-drop energy. No radial PDE solution or Newton shell theorem
is assumed.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace LiquidDrop

/-- Orthogonal coordinate changes preserve the actual extended-real potential. -/
lemma coulombPotential_linearIsometryEquiv (E : Set AmbientSpace)
    (e : AmbientSpace ≃ₗᵢ[ℝ] AmbientSpace) (x : AmbientSpace) :
    coulombPotential (e '' E) (e x) = coulombPotential E x := by
  have h := e.measurePreserving.setLIntegral_comp_emb e.toHomeomorph.measurableEmbedding
    (coulombKernel (e x)) E
  simpa only [coulombPotential, coulombKernel, ← e.map_sub, e.norm_map] using h.symm

/-- Rotational invariance reduces every observation point to the third axis. -/
lemma coulombPotential_ball_eq_axis (R : ℝ) (x : AmbientSpace) :
    coulombPotential (ball (0 : AmbientSpace) R) x =
      coulombPotential (ball (0 : AmbientSpace) R) (EuclideanSpace.single 2 ‖x‖) := by
  let e := (ℝ ∙ (x - EuclideanSpace.single (2 : Fin 3) ‖x‖))ᗮ.reflection
  have he : e x = EuclideanSpace.single 2 ‖x‖ :=
    Submodule.reflection_sub (by simp only [PiLp.norm_single, Real.norm_eq_abs, abs_norm])
  have hball : e '' ball (0 : AmbientSpace) R = ball 0 R := by
    have hh := e.toIsometryEquiv.image_ball (0 : AmbientSpace) R
    change e '' ball (0 : AmbientSpace) R = ball (e 0) R at hh
    simpa only [map_zero] using hh
  have h := coulombPotential_linearIsometryEquiv (ball (0 : AmbientSpace) R) e x
  rw [hball, he] at h
  exact h.symm

lemma coulombPotential_ball_center_toReal {R : ℝ} (hR : 0 ≤ R) :
    (coulombPotential (ball (0 : AmbientSpace) R) 0).toReal = 2 * Real.pi * R ^ 2 := by
  rw [coulombPotential_toReal _ (isBounded_ball.measure_lt_top)]
  simp only [zero_sub, norm_neg]
  exact integral_inv_norm_ball hR

/-- Spherical coordinates restricted to a ball, with the integrability premise
coming from the actual function rather than from a radial formula. -/
lemma integral_ball_spherical_coordinates {R : ℝ} {g : AmbientSpace → ℝ}
    (hg : IntegrableOn g (ball 0 R)) :
    (∫ y in ball (0 : AmbientSpace) R, g y) =
      ∫ r in Ioo (0 : ℝ) R, ∫ p in sphereParamDomain,
        (r ^ 2 * Real.sin (p 1)) * g (r • sphereParam p) := by
  have h := integral_spherical_coordinates (hg.integrable_indicator measurableSet_ball)
  rw [integral_indicator measurableSet_ball] at h
  calc
    _ = ∫ r in Ioi (0 : ℝ), ∫ p in sphereParamDomain,
        (r ^ 2 * Real.sin (p 1)) • (ball (0 : AmbientSpace) R).indicator g
          (r • sphereParam p) := h
    _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator
        (fun r => ∫ p in sphereParamDomain,
          (r ^ 2 * Real.sin (p 1)) * g (r • sphereParam p)) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      have hmem (p : EuclideanSpace ℝ (Fin 2)) :
          r • sphereParam p ∈ ball (0 : AmbientSpace) R ↔ r < R := by
        simp only [mem_ball, dist_zero_right, norm_smul, norm_sphereParam,
          Real.norm_eq_abs, abs_of_pos (show 0 < r from hr), mul_one]
      by_cases hrR : r < R
      · simp only [indicator_of_mem (hmem _ |>.mpr hrR),
          indicator_of_mem (show r ∈ Iio R from hrR), smul_eq_mul]
      · simp only [indicator_of_notMem (fun hp => hrR ((hmem _).mp hp)),
          indicator_of_notMem (show r ∉ Iio R from hrR), smul_zero, integral_zero]
    _ = _ := by
      rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        inter_comm, Ioi_inter_Iio]

/-- The elementary remaining radial integral inside a ball. -/
lemma integral_ballPotential_radial_piecewise {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    (∫ r in Ioo (0 : ℝ) R, if r < a then r ^ 2 / a else r) =
      R ^ 2 / 2 - a ^ 2 / 6 := by
  classical
  let f (r : ℝ) := if r < a then r ^ 2 / a else r
  have hc : Continuous f := by
    have hh : ∀ r ∈ frontier (Iio a), r ^ 2 / a = r := by
      intro r hr
      rw [frontier_Iio, mem_singleton_iff] at hr
      subst r
      field_simp
    exact Continuous.piecewise hh ((continuous_id.pow 2).div_const a) continuous_id
  change (∫ r in Ioo (0 : ℝ) R, f r) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (ha.le.trans haR),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a R)]
  have hleft : (∫ r in (0 : ℝ)..a, f r) = ∫ r in (0 : ℝ)..a, r ^ 2 / a := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [(volume : Measure ℝ).ae_ne a] with r hra hr
    rw [uIoc_of_le ha.le] at hr
    simp [f, lt_of_le_of_ne hr.2 hra]
  have hright : (∫ r in a..R, f r) = ∫ r in a..R, r := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with r hr
    rw [uIoc_of_le haR] at hr
    simp [f, not_lt.mpr hr.1.le]
  rw [hleft, hright, intervalIntegral.integral_div, integral_pow, integral_id]
  norm_num
  field_simp
  ring


/-- The singular radius is removed as an actual null singleton in the radial
integral, leaving the explicitly evaluated elementary shell formula. -/
lemma coulombPotential_ball_axis_toReal {a R : ℝ} (ha : 0 < a) (haR : a ≤ R) :
    (coulombPotential (ball (0 : AmbientSpace) R) (EuclideanSpace.single 2 a)).toReal =
      2 * Real.pi * (R ^ 2 - a ^ 2 / 3) := by
  have hfin : volume (ball (0 : AmbientSpace) R) < ∞ := isBounded_ball.measure_lt_top
  rw [coulombPotential_toReal _ hfin, integral_ball_spherical_coordinates
    (integrableOn_coulombKernel _ hfin (EuclideanSpace.single 2 a))]
  calc
    _ = ∫ r in Ioo (0 : ℝ) R, 4 * Real.pi * (if r < a then r ^ 2 / a else r) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae ((volume : Measure ℝ).ae_ne a)] with r hr hra
      exact integral_ballPotential_shell_param_piecewise ha hr.1 hra.symm
    _ = _ := by
      rw [integral_const_mul, integral_ballPotential_radial_piecewise ha haR]
      ring

/-- The interior and boundary value of the actual Newtonian potential of a ball. -/
theorem coulombPotential_ball_zero_toReal {R : ℝ} (hR : 0 < R)
    {x : AmbientSpace} (hx : ‖x‖ ≤ R) :
    (coulombPotential (ball (0 : AmbientSpace) R) x).toReal =
      2 * Real.pi * (R ^ 2 - ‖x‖ ^ 2 / 3) := by
  by_cases hx0 : x = 0
  · subst x
    simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero] using
      coulombPotential_ball_center_toReal hR.le
  · rw [coulombPotential_ball_eq_axis R x]
    exact coulombPotential_ball_axis_toReal (norm_pos_iff.mpr hx0) hx

/-- The original extended-real potential, with no replacement by a real kernel
at the singularity in its definition. -/
theorem coulombPotential_ball_zero {R : ℝ} (hR : 0 < R)
    {x : AmbientSpace} (hx : ‖x‖ ≤ R) :
    coulombPotential (ball (0 : AmbientSpace) R) x =
      ENNReal.ofReal (2 * Real.pi * (R ^ 2 - ‖x‖ ^ 2 / 3)) := by
  rw [← ENNReal.ofReal_toReal (coulombPotential_lt_top _ isBounded_ball.measure_lt_top x).ne,
    coulombPotential_ball_zero_toReal hR hx]

/-- Radial integration in dimension three, including arbitrary real integrands. -/
lemma integral_ball_radial_three (R : ℝ) (f : ℝ → ℝ) :
    (∫ y : AmbientSpace in ball 0 R, f ‖y‖) =
      4 * Real.pi * ∫ r in Ioo (0 : ℝ) R, r ^ 2 * f r := by
  have h := integral_fun_norm_addHaar (volume : Measure AmbientSpace) ((Iio R).indicator f)
  have he : (fun y : AmbientSpace => (Iio R).indicator f ‖y‖) =
      (ball (0 : AmbientSpace) R).indicator (fun y => f ‖y‖) := by
    ext y
    simp [indicator]
  rw [he, integral_indicator measurableSet_ball] at h
  simp only [AmbientSpace, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul] at h
  have hr : (∫ r in Ioi (0 : ℝ), r ^ 2 * (Iio R).indicator f r) =
      ∫ r in Ioo (0 : ℝ) R, r ^ 2 * f r := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun r => r ^ 2 * f r) r := by
        apply integral_congr_ae
        filter_upwards [] with r
        by_cases hr : r < R <;> simp [indicator, hr]
      _ = _ := by
        rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
          inter_comm, Ioi_inter_Iio]
  rw [hr] at h
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one,
    one_pow, one_mul, ENNReal.toReal_ofReal (show 0 ≤ Real.pi * 4 / 3 by positivity),
    nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [h]
  ring


/-- Integrating the proved potential gives the exact real Coulomb energy. -/
theorem coulombEnergy_ball_zero_toReal {R : ℝ} (hR : 0 < R) :
    (coulombEnergy (ball (0 : AmbientSpace) R)).toReal =
      16 * Real.pi ^ 2 / 15 * R ^ 5 := by
  rw [coulombEnergy_toReal_eq_integral_potential _ isBounded_ball.measure_lt_top]
  have he : (∫ x in ball (0 : AmbientSpace) R,
      (coulombPotential (ball (0 : AmbientSpace) R) x).toReal) =
      ∫ x in ball (0 : AmbientSpace) R, 2 * Real.pi * (R ^ 2 - ‖x‖ ^ 2 / 3) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    apply coulombPotential_ball_zero_toReal hR
    exact (show ‖x‖ < R by simpa only [mem_ball, dist_zero_right] using hx).le
  rw [he, integral_ball_radial_three R (fun r => 2 * Real.pi * (R ^ 2 - r ^ 2 / 3))]
  have heq (r : ℝ) : r ^ 2 * (2 * Real.pi * (R ^ 2 - r ^ 2 / 3)) =
      (2 * Real.pi * R ^ 2) * r ^ 2 - (2 * Real.pi / 3) * r ^ 4 := by ring
  simp_rw [heq]
  have hi2 : IntervalIntegrable (fun r : ℝ => (2 * Real.pi * R ^ 2) * r ^ 2) volume 0 R :=
    (by fun_prop : Continuous (fun r : ℝ => (2 * Real.pi * R ^ 2) * r ^ 2)).intervalIntegrable _ _
  have hi4 : IntervalIntegrable (fun r : ℝ => (2 * Real.pi / 3) * r ^ 4) volume 0 R :=
    (by fun_prop : Continuous (fun r : ℝ => (2 * Real.pi / 3) * r ^ 4)).intervalIntegrable _ _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR.le,
    intervalIntegral.integral_sub hi2 hi4, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow]
  norm_num
  ring

/-- Exact original extended-real Coulomb energy of a centered positive-radius ball. -/
theorem coulombEnergy_ball_zero {R : ℝ} (hR : 0 < R) :
    coulombEnergy (ball (0 : AmbientSpace) R) =
      ENNReal.ofReal (16 * Real.pi ^ 2 / 15 * R ^ 5) := by
  rw [← ENNReal.ofReal_toReal (coulombEnergy_lt_top _ isBounded_ball.measure_lt_top).ne,
    coulombEnergy_ball_zero_toReal hR]

lemma image_add_ball_zero (c : AmbientSpace) (R : ℝ) :
    (fun y => c + y) '' ball (0 : AmbientSpace) R = ball c R := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hy
  · intro hz
    refine ⟨z - c, ?_, ?_⟩
    · simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
    · change c + (z - c) = z
      rw [← add_sub_assoc, add_sub_cancel_left]

/-- The potential formula at any center, including observation points on the sphere. -/
theorem coulombPotential_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R)
    {x : AmbientSpace} (hx : ‖x - c‖ ≤ R) :
    coulombPotential (ball c R) x =
      ENNReal.ofReal (2 * Real.pi * (R ^ 2 - ‖x - c‖ ^ 2 / 3)) := by
  have h := coulombPotential_translate (ball (0 : AmbientSpace) R) c (x - c)
  rw [image_add_ball_zero, show c + (x - c) = x by rw [← add_sub_assoc, add_sub_cancel_left]] at h
  rw [h, coulombPotential_ball_zero hR hx]

/-- The exact Coulomb energy is independent of the center. -/
theorem coulombEnergy_ball (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    coulombEnergy (ball c R) = ENNReal.ofReal (16 * Real.pi ^ 2 / 15 * R ^ 5) := by
  rw [← image_add_ball_zero c R, coulombEnergy_translate, coulombEnergy_ball_zero hR]

/-- For the prescribed-volume ball, D(B_V)=(V/5)P_B in ordinary real notation. -/
theorem coulombEnergy_ballByVolume_toReal {V : ℝ} (hV : 0 < V) :
    (coulombEnergy (ballByVolume V)).toReal = V / 5 * (ballPerimeter V).toReal := by
  rw [ballByVolume, coulombEnergy_ball_zero_toReal (ballRadius_pos hV),
    ballPerimeter_toReal_eq_radius hV]
  calc
    _ = (4 * Real.pi * ballRadius V ^ 3 / 3) / 5 * (4 * Real.pi * ballRadius V ^ 2) := by ring
    _ = _ := by rw [ballRadius_cube hV]; field_simp

/-- The prescribed-volume identity for the original extended-real energy. -/
theorem coulombEnergy_ballByVolume {V : ℝ} (hV : 0 < V) :
    coulombEnergy (ballByVolume V) = ENNReal.ofReal (V / 5) * ballPerimeter V := by
  apply (ENNReal.toReal_eq_toReal_iff' (coulombEnergy_lt_top _ (by
    rw [volume_ballByVolume hV]
    exact ENNReal.ofReal_lt_top)).ne
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballPerimeter_lt_top hV).ne)).mp
  rw [coulombEnergy_ballByVolume_toReal hV, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity)]

/-- The full liquid-drop energy of the prescribed-volume ball. -/
theorem energy_ballByVolume_toReal {V : ℝ} (hV : 0 < V) :
    (energy (ballByVolume V)).toReal = (V + 5) / 5 * (ballPerimeter V).toReal := by
  change (ballPerimeter V + coulombEnergy (ballByVolume V)).toReal = _
  rw [ENNReal.toReal_add (ballPerimeter_lt_top hV).ne
    (coulombEnergy_lt_top _ (by rw [volume_ballByVolume hV]; exact ENNReal.ofReal_lt_top)).ne,
    coulombEnergy_ballByVolume_toReal hV]
  ring

/-- Exact extended-real ball energy, preserving the original energy definition. -/
theorem energy_ballByVolume {V : ℝ} (hV : 0 < V) :
    energy (ballByVolume V) = ENNReal.ofReal ((V + 5) / 5) * ballPerimeter V := by
  rw [energy, coulombEnergy_ballByVolume hV]
  change ballPerimeter V + ENNReal.ofReal (V / 5) * ballPerimeter V = _
  rw [← one_add_mul, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  congr 2
  ring

/-- The closed volume-only expression in the blueprint's ball-energy corollary. -/
theorem energy_ballByVolume_eq_rpow {V : ℝ} (hV : 0 < V) :
    energy (ballByVolume V) = ENNReal.ofReal
      ((36 * Real.pi) ^ (1 / (3 : ℝ)) * ((V + 5) / 5) * V ^ (2 / (3 : ℝ))) := by
  rw [energy_ballByVolume hV, ballPerimeter_eq_rpow hV, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring


/-- The centered-potential polynomial in real notation at an arbitrary center. -/
theorem coulombPotential_ball_toReal (c : AmbientSpace) {R : ℝ} (hR : 0 < R)
    {x : AmbientSpace} (hx : ‖x - c‖ ≤ R) :
    (coulombPotential (ball c R) x).toReal =
      2 * Real.pi * (R ^ 2 - ‖x - c‖ ^ 2 / 3) := by
  have h := coulombPotential_translate (ball (0 : AmbientSpace) R) c (x - c)
  rw [image_add_ball_zero, show c + (x - c) = x by rw [← add_sub_assoc, add_sub_cancel_left]] at h
  rw [h, coulombPotential_ball_zero_toReal hR hx]

lemma coulombEnergy_ball_toReal (c : AmbientSpace) {R : ℝ} (hR : 0 < R) :
    (coulombEnergy (ball c R)).toReal = 16 * Real.pi ^ 2 / 15 * R ^ 5 := by
  rw [coulombEnergy_ball c hR, ENNReal.toReal_ofReal (by positivity)]

end LiquidDrop
