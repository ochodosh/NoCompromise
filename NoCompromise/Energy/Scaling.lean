import NoCompromise.Energy.Coulomb
import NoCompromise.BV.Basic
import NoCompromise.Energy.Defs
import NoCompromise.Measure.NullChangeOfVariables

/-!
# Translation and dilation of Coulomb energy

The nonnegative extended-real definitions are used throughout, including the
infinite value of the kernel on the diagonal. The change-of-variables identities
therefore preserve infinite energies as well as finite ones.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal Pointwise
namespace LiquidDrop

lemma setLIntegral_image_smul {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (U : Set (EuclideanSpace ℝ (Fin n)))
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ x in (fun y => r • y) '' U, f x) =
      ENNReal.ofReal (r ^ n) * ∫⁻ x in U, f (r • x) := by
  let e := (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr.ne').unit :
    EuclideanSpace ℝ (Fin n) ≃ₜ EuclideanSpace ℝ (Fin n)).toMeasurableEquiv
  have hm : (∫⁻ x in e '' U, f x ∂Measure.map e volume) = ∫⁻ x in U, f (e x) := by
    rw [e.measurableEmbedding.restrict_map, e.measurableEmbedding.lintegral_map,
      e.injective.preimage_image]
  have he : (e : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      (fun x => r • x) := rfl
  rw [he, Measure.map_addHaar_smul volume hr.ne', Measure.restrict_smul,
    lintegral_smul_measure] at hm
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hr n)), ENNReal.ofReal_inv_of_pos (pow_pos hr n),
    smul_eq_mul] at hm
  calc
    _ = ENNReal.ofReal (r ^ n) * ((ENNReal.ofReal (r ^ n))⁻¹ *
        ∫⁻ x in (fun y => r • y) '' U, f x) := by
      rw [ENNReal.mul_inv_cancel_left (ENNReal.ofReal_pos.mpr (pow_pos hr n)).ne'
        ENNReal.ofReal_ne_top]
    _ = _ := by rw [hm]

lemma coulombKernel_translate (a x y : AmbientSpace) :
    coulombKernel (a + x) (a + y) = coulombKernel x y := by
  simp only [coulombKernel, add_sub_add_left_eq_sub]

lemma coulombKernel_smul {r : ℝ} (hr : 0 < r) (x y : AmbientSpace) :
    coulombKernel (r • x) (r • y) = (ENNReal.ofReal r)⁻¹ * coulombKernel x y := by
  simp only [coulombKernel, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    ENNReal.ofReal_mul hr.le]
  exact ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hr).ne') (Or.inl ENNReal.ofReal_ne_top)

/-- Coulomb potentials commute with simultaneous translation of source and observation point. -/
theorem coulombPotential_translate (E : Set AmbientSpace) (a x : AmbientSpace) :
    coulombPotential ((fun y => a + y) '' E) (a + x) = coulombPotential E x := by
  have h := (measurePreserving_add_left volume a).setLIntegral_comp_emb
    (Homeomorph.addLeft a).measurableEmbedding (coulombKernel (a + x)) E
  simpa only [coulombPotential, coulombKernel_translate] using h.symm

/-- The Coulomb potential scales quadratically under dilation. -/
theorem coulombPotential_smul (E : Set AmbientSpace) {r : ℝ} (hr : 0 < r)
    (x : AmbientSpace) :
    coulombPotential ((fun y => r • y) '' E) (r • x) =
      ENNReal.ofReal (r ^ 2) * coulombPotential E x := by
  rw [coulombPotential, setLIntegral_image_smul _ _ hr]
  simp_rw [coulombKernel_smul hr]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne')]
  rw [ENNReal.ofReal_pow hr.le, ENNReal.ofReal_pow hr.le]
  rw [← mul_assoc, pow_succ, ENNReal.mul_inv_cancel_right
    (ENNReal.ofReal_pos.mpr hr).ne' ENNReal.ofReal_ne_top]
  rfl

/-- Coulomb energy is invariant under translation, with no finite-energy premise. -/
theorem coulombEnergy_translate (E : Set AmbientSpace) (a : AmbientSpace) :
    coulombEnergy ((fun x => a + x) '' E) = coulombEnergy E := by
  rw [coulombEnergy_eq_lintegral_potential, coulombEnergy_eq_lintegral_potential]
  have h := (measurePreserving_add_left volume a).setLIntegral_comp_emb
    (Homeomorph.addLeft a).measurableEmbedding
    (coulombPotential ((fun x => a + x) '' E)) E
  rw [← h]
  simp_rw [coulombPotential_translate]

/-- Coulomb energy scales by the fifth power of a positive dilation. -/
theorem coulombEnergy_smul (E : Set AmbientSpace) {r : ℝ} (hr : 0 < r) :
    coulombEnergy ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ 5) * coulombEnergy E := by
  rw [coulombEnergy_eq_lintegral_potential, setLIntegral_image_smul _ _ hr]
  simp_rw [coulombPotential_smul E hr]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, coulombEnergy_eq_lintegral_potential]
  rw [show (5 : ℕ) = 3 + 2 from rfl, pow_add, ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ 3)]
  ac_rfl

lemma volume_image_translate (E : Set AmbientSpace) (a : AmbientSpace) :
    volume ((fun x => a + x) '' E) = volume E := by
  simp

lemma volume_image_smul (E : Set AmbientSpace) {r : ℝ} (hr : 0 < r) :
    volume ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ 3) * volume E := by
  simpa using setLIntegral_image_smul (fun _ : AmbientSpace => (1 : ℝ≥0∞)) E hr

lemma perimeter_image_translate {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (a : AmbientSpace) : perimeter ((fun x => a + x) '' E) = perimeter E := by
  have hΦ : Differentiable ℝ (fun x : AmbientSpace => a + x) := by fun_prop
  have hm := nullMeasurableSet_image_of_differentiable hΦ
    (fun _ _ hh => add_left_cancel hh) hE
  rw [← perimeterN_eq_perimeter _ hm, perimeterN_translate, perimeterN_eq_perimeter _ hE]

lemma perimeter_image_smul {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    {r : ℝ} (hr : 0 < r) :
    perimeter ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ 2) * perimeter E := by
  have hΦ : Differentiable ℝ (fun x : AmbientSpace => r • x) := by fun_prop
  have hm := nullMeasurableSet_image_of_differentiable hΦ (smul_right_injective _ hr.ne') hE
  rw [← perimeterN_eq_perimeter _ hm, perimeterN_smul (by decide : 0 < 3) _ hr,
    perimeterN_eq_perimeter _ hE]

/-- Translation invariance of the unchanged liquid-drop energy. -/
theorem energy_translate {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    (a : AmbientSpace) : energy ((fun x => a + x) '' E) = energy E := by
  rw [energy, perimeter_image_translate hE, coulombEnergy_translate, energy]

/-- The exact two scaling exponents in the unchanged liquid-drop energy. -/
theorem energy_smul {E : Set AmbientSpace} (hE : NullMeasurableSet E volume)
    {r : ℝ} (hr : 0 < r) : energy ((fun x => r • x) '' E) =
      ENNReal.ofReal (r ^ 2) * perimeter E + ENNReal.ofReal (r ^ 5) * coulombEnergy E := by
  rw [energy, perimeter_image_smul hE hr, coulombEnergy_smul E hr]

/-- All six blueprint translation/dilation identities, for the original set and
original perimeter and Coulomb definitions. Finite volume is unnecessary. -/
theorem translation_dilation_identities {E : Set AmbientSpace}
    (hE : NullMeasurableSet E volume) (a : AmbientSpace) {r : ℝ} (hr : 0 < r) :
    volume ((fun x => a + x) '' E) = volume E ∧
      perimeter ((fun x => a + x) '' E) = perimeter E ∧
      coulombEnergy ((fun x => a + x) '' E) = coulombEnergy E ∧
      volume ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ 3) * volume E ∧
      perimeter ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ 2) * perimeter E ∧
      coulombEnergy ((fun x => r • x) '' E) = ENNReal.ofReal (r ^ 5) * coulombEnergy E :=
  ⟨volume_image_translate E a, perimeter_image_translate hE a, coulombEnergy_translate E a,
    volume_image_smul E hr, perimeter_image_smul hE hr, coulombEnergy_smul E hr⟩

end LiquidDrop
