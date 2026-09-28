import NoCompromise.Sobolev.RelativeScaling
import NoCompromise.Sobolev.LipschitzCubes

/-!
# Relative isoperimetry for arbitrarily oriented cubes

A cube of side length `ℓ > 0` is an affine-isometric image of the open coordinate
cube of radius `ℓ / 2`. The final constant is independent of its side length,
position, and orientation. Relative perimeter is always taken in that same cube.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology Pointwise

namespace LiquidDrop

set_option maxSynthPendingDepth 8

/-- Every affine Euclidean isometry preserves the volume of arbitrary sets. -/
lemma volume_image_affineIsometry {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) : volume (a '' S) = volume S := by
  have h₁ := volume_image_le_of_lipschitzOn (a.isometry.lipschitzWith.lipschitzOnWith (s := S))
  have h₂ := volume_image_le_of_lipschitzOn
    (a.symm.isometry.lipschitzWith.lipschitzOnWith (s := a '' S))
  simp only [ENNReal.coe_one, one_pow, one_mul] at h₁ h₂
  have hset : a.symm '' (a '' S) = S := by
    rw [image_image]
    simp only [a.symm_apply_apply, image_id']
  exact le_antisymm h₁ (by simpa only [hset] using h₂)

/-- Affine Euclidean isometries preserve Lebesgue measure as maps. -/
lemma measurePreserving_affineIsometry {n : ℕ}
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving a volume volume := by
  refine ⟨a.continuous.measurable, ?_⟩
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply a.continuous.measurable hS]
  have h := volume_image_affineIsometry a (a ⁻¹' S)
  rw [image_preimage_eq S a.surjective] at h
  exact h.symm

/-- Pulling an indicator back through an affine isometry does not increase relative perimeter.
Finite volume of the open domain supplies integrability; infinite perimeter is automatic. -/
theorem perimeterIn_preimage_affineIsometry_le {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hvol : volume D ≠ ∞)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n))
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : NullMeasurableSet E volume) :
    perimeterIn (a ⁻¹' E) D ≤ perimeterIn E (a '' D) := by
  by_cases hper : perimeterIn E (a '' D) = ∞
  · rw [hper]; exact le_top
  have hV : IsOpen (a '' D) := a.toHomeomorph.isOpenMap D hD
  have hvolV : volume (a '' D) ≠ ∞ := by rwa [volume_image_affineIsometry]
  let g := E.indicator (fun _ => (1 : ℝ))
  have hg : IsBVOn g (a '' D) :=
    ⟨(integrableOn_const hvolV).indicator₀ (hE.mono Measure.restrict_le_self),
      lt_top_iff_ne_top.mpr hper⟩
  have hm : MapsTo a D (a '' D) := mapsTo_image _ _
  have hinv : LeftInvOn a.symm a D := fun x _ => a.symm_apply_apply x
  have h := variation_comp_le_of_lipschitz_leftInverse hD hV
    a.isometry.lipschitzWith.lipschitzOnWith
    a.symm.isometry.lipschitzWith.lipschitzOnWith hm hinv hg
  simp only [NNReal.coe_one, one_pow, one_mul, ENNReal.ofReal_toReal hg.2.ne] at h
  have heq : g ∘ a = (a ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : a x ∈ E <;> simp [g, hx]
  rw [heq] at h
  exact h

/-- A finite-volume open domain's relative isoperimetric constant is unchanged by any
rotation, reflection, or translation, represented uniformly as an affine isometry. -/
theorem HasRelativeIsoperimetricInequality.affineIsometry {n : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin n))} {q C : ℝ}
    (hI : HasRelativeIsoperimetricInequality D q C) (hD : IsOpen D)
    (hvol : volume D ≠ ∞)
    (a : EuclideanSpace ℝ (Fin n) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin n)) :
    HasRelativeIsoperimetricInequality (a '' D) q C := by
  intro E hE
  let F := a ⁻¹' E
  have hF : NullMeasurableSet F volume :=
    hE.preimage (measurePreserving_affineIsometry a).quasiMeasurePreserving
  have hEF : a '' F = E := image_preimage_eq E a.surjective
  have hint : volume (E ∩ a '' D) = volume (F ∩ D) := by
    rw [← hEF, ← image_inter a.injective, volume_image_affineIsometry]
  have hdiff : volume (a '' D \ E) = volume (D \ F) := by
    rw [← hEF, ← image_sdiff a.injective, volume_image_affineIsometry]
  rw [hint, hdiff]
  exact (hI F hF).trans (mul_le_mul_of_nonneg_left
    (perimeterIn_preimage_affineIsometry_le hD hvol a hE) (by positivity))

/-- Coordinate cubes are convex, including the empty-radius cases. -/
lemma convex_coordinateCube (n : ℕ) (R : ℝ) : Convex ℝ (coordinateCube n R) := by
  have heq : coordinateCube n R = ⋂ i : Fin n,
      (EuclideanSpace.proj (𝕜 := ℝ) i) ⁻¹' Ioo (-R) R := by
    ext x
    simp only [coordinateCube, mem_ofPred_eq, mem_iInter, mem_preimage, abs_lt]
    rfl
  rw [heq]
  exact convex_iInter fun i => (convex_Ioo (-R) R).linear_preimage
    ((EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap)

/-- Dilating the coordinate unit cube by `r > 0` gives the coordinate cube of radius `r`. -/
lemma image_coordinateUnitCube_pos_smul {n : ℕ} {r : ℝ} (hr : 0 < r) :
    (fun x : EuclideanSpace ℝ (Fin n) => r • x) '' coordinateCube n 1 =
      coordinateCube n r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    change |r * x i| < r
    rw [abs_mul, abs_of_pos hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left (hx i) hr
  · intro hy
    refine ⟨r⁻¹ • y, ?_, by simp [hr.ne']⟩
    intro i
    change |r⁻¹ * y i| < 1
    rw [abs_mul, abs_inv, abs_of_pos hr, inv_mul_eq_div, div_lt_one hr]
    exact hy i

/-- Blueprint `prop:rel-iso-cube`: one absolute constant works for all open cubes in ℝ³,
with arbitrary orientation and position. The coordinate radius is half the side length. -/
theorem relative_isoperimetric_cube_three :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : EuclideanSpace ℝ (Fin 3) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 3)) (ℓ : ℝ), 0 < ℓ →
        ∀ E : Set (EuclideanSpace ℝ (Fin 3)), NullMeasurableSet E volume →
          (min (volume (E ∩ a '' coordinateCube 3 (ℓ / 2)))
            (volume (a '' coordinateCube 3 (ℓ / 2) \ E))) ^ (2 / 3 : ℝ) ≤
              ENNReal.ofReal C * perimeterIn E (a '' coordinateCube 3 (ℓ / 2)) := by
  obtain ⟨C, hC, hI⟩ := relative_isoperimetric_three (isOpen_coordinateCube 3 1)
    (convex_coordinateCube 3 1).isPreconnected (isBounded_coordinateCube 3 1)
    (hasLipschitzBoundary_coordinateCube 3 zero_lt_one)
  have hunit : HasRelativeIsoperimetricInequality (coordinateCube 3 1) (2 / 3) C := hI
  refine ⟨C, hC, fun a ℓ hℓ E hE => ?_⟩
  have hrad : 0 < ℓ / 2 := half_pos hℓ
  have hscaled := hunit.smul (by norm_num) (by norm_num) (by norm_num) hrad
  rw [image_coordinateUnitCube_pos_smul hrad] at hscaled
  exact hscaled.affineIsometry (isOpen_coordinateCube 3 (ℓ / 2))
    (isBounded_coordinateCube 3 (ℓ / 2)).measure_lt_top.ne a E hE

end LiquidDrop
