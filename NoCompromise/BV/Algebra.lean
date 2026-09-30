module

public import NoCompromise.BV.Basic

@[expose] public section

/-!
# Algebra and finite assembly of BV functions

The variation supremum is subadditive under addition and absolutely homogeneous.
These facts give BV closure under finite linear combinations and the constant-one
bound for assembling finitely many BV functions. No extension theorem is used.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace LiquidDrop

set_option maxSynthPendingDepth 8

@[simp]
theorem variation_zero {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    variation (fun _ => (0 : ℝ)) U = 0 := by
  simp [variation]

/-- Negating a function preserves its variation, even when the variation is infinite. -/
@[simp]
theorem variation_neg {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) :
    variation (fun x => -f x) U = variation f U := by
  have hneg (g : EuclideanSpace ℝ (Fin n) → ℝ) :
      variation (fun x => -g x) U ≤ variation g U := by
    apply iSup_le
    intro X
    apply iSup_le
    intro hX
    have heq : (∫ x in U, -g x * divergenceN X x) =
        ∫ x in U, g x * divergenceN (-X) x := by
      simp [divergenceN_neg]
    rw [heq]
    exact le_iSup_of_le (-X) (le_iSup_of_le hX.neg le_rfl)
  exact le_antisymm (hneg f) (by simpa using hneg (fun x => -f x))

/-- Nonnegative scalar multiplication scales the variation supremum. -/
theorem variation_const_mul_of_nonneg {n : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) :
    variation (fun x => c * f x) U = ENNReal.ofReal c * variation f U := by
  simp only [variation, mul_assoc, integral_const_mul, ENNReal.ofReal_mul hc,
    ENNReal.mul_iSup]

/-- Absolute homogeneity of variation, with no finiteness assumption. -/
theorem variation_const_mul {n : ℕ} (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) :
    variation (fun x => c * f x) U = ENNReal.ofReal |c| * variation f U := by
  rcases le_total 0 c with hc | hc
  · simpa only [abs_of_nonneg hc] using variation_const_mul_of_nonneg hc f U
  · have heq : (fun x => c * f x) = (fun x => -((-c) * f x)) := by
      funext x
      ring
    rw [heq, variation_neg, variation_const_mul_of_nonneg (neg_nonneg.mpr hc),
      abs_of_nonpos hc]

/-- Subadditivity follows by splitting each distributional pairing. -/
theorem variation_add_le {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : LocallyIntegrableOn f U) (hg : LocallyIntegrableOn g U) :
    variation (fun x => f x + g x) U ≤ variation f U + variation g U := by
  apply iSup_le
  intro X
  apply iSup_le
  intro hX
  have hif := (integrable_mul_divergenceN hf hX.1 hX.2.1 hX.2.2.1).integrableOn (s := U)
  have hig := (integrable_mul_divergenceN hg hX.1 hX.2.1 hX.2.2.1).integrableOn (s := U)
  simp only [add_mul, integral_add hif hig]
  exact ENNReal.ofReal_add_le.trans (add_le_add
    (le_iSup_of_le X (le_iSup_of_le hX le_rfl))
    (le_iSup_of_le X (le_iSup_of_le hX le_rfl)))

/-- Finite sums are locally integrable on the same region. -/
theorem locallyIntegrableOn_finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) U) :
    LocallyIntegrableOn (fun x => ∑ i ∈ s, f i x) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (locallyIntegrableOn_zero (s := U) (μ := volume))
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The variation of a finite sum is bounded by the sum of the individual variations. -/
theorem variation_finsetSum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) U) :
    variation (fun x => ∑ i ∈ s, f i x) U ≤ ∑ i ∈ s, variation (f i) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (variation_add_le (hf i (Finset.mem_insert_self i s))
        (locallyIntegrableOn_finsetSum s fun j hj => hf j (Finset.mem_insert_of_mem hj))).trans
        (add_le_add le_rfl (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The zero function is BV on every region. -/
theorem IsBVOn.zero {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n))) :
    IsBVOn (fun _ => (0 : ℝ)) U := by
  exact ⟨integrable_zero _ _ _, by simp⟩

/-- BV is preserved by addition. -/
theorem IsBVOn.add {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : IsBVOn f U) (hg : IsBVOn g U) :
    IsBVOn (fun x => f x + g x) U := by
  exact ⟨hf.1.add hg.1,
    (variation_add_le hf.1.locallyIntegrableOn hg.1.locallyIntegrableOn).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hf.2, hg.2⟩)⟩

/-- BV is preserved by negation. -/
theorem IsBVOn.neg {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : IsBVOn f U) :
    IsBVOn (fun x => -f x) U := by
  exact ⟨hf.1.neg, by simpa using hf.2⟩

/-- BV is preserved by subtraction. -/
theorem IsBVOn.sub {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : IsBVOn f U) (hg : IsBVOn g U) :
    IsBVOn (fun x => f x - g x) U := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

/-- BV is preserved by multiplication by any real scalar. -/
theorem IsBVOn.const_mul {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : IsBVOn f U) (c : ℝ) :
    IsBVOn (fun x => c * f x) U := by
  refine ⟨hf.1.const_mul c, ?_⟩
  rw [variation_const_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2

/-- BV is preserved by finite sums. -/
theorem IsBVOn.finsetSum {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ i ∈ s, IsBVOn (f i) U) :
    IsBVOn (fun x => ∑ i ∈ s, f i x) U := by
  refine ⟨integrable_finsetSum s (fun i hi => (hf i hi).1), ?_⟩
  exact (variation_finsetSum_le s fun i hi => (hf i hi).1.locallyIntegrableOn).trans_lt
    (ENNReal.sum_lt_top.mpr fun i hi => (hf i hi).2)

/-- Restricting a BV function to a subregion preserves BV. -/
theorem IsBVOn.mono {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hf : IsBVOn f V)
    (hV : MeasurableSet V) (hUV : U ⊆ V) : IsBVOn f U := by
  exact ⟨hf.1.mono_set hUV, (variation_mono hV hUV).trans_lt hf.2⟩

/-- BV depends only on the almost-everywhere class on the region. -/
theorem IsBVOn.congr_ae {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hf : IsBVOn f U)
    (hfg : f =ᵐ[volume.restrict U] g) : IsBVOn g U := by
  exact ⟨hf.1.congr hfg, by rw [← variation_congr_ae U hfg]; exact hf.2⟩

/-- The ordinary-real variation bound for a finite sum of BV functions. -/
theorem variation_finsetSum_toReal_le {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ i ∈ s, IsBVOn (f i) U) :
    (variation (fun x => ∑ i ∈ s, f i x) U).toReal ≤
      ∑ i ∈ s, (variation (f i) U).toReal := by
  rw [← ENNReal.toReal_sum (fun i hi => (hf i hi).2.ne)]
  exact ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr fun i hi => (hf i hi).2.ne)
    (variation_finsetSum_le s fun i hi => (hf i hi).1.locallyIntegrableOn)

/-- Constant-one BV norm control for finite assembly on a common region. -/
theorem bv_norm_finsetSum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    {f : ι → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hf : ∀ i ∈ s, IsBVOn (f i) U) :
    (∫ x in U, ‖∑ i ∈ s, f i x‖) +
        (variation (fun x => ∑ i ∈ s, f i x) U).toReal ≤
      ∑ i ∈ s, ((∫ x in U, ‖f i x‖) + (variation (f i) U).toReal) := by
  have hnorm : (∫ x in U, ‖∑ i ∈ s, f i x‖) ≤ ∑ i ∈ s, ∫ x in U, ‖f i x‖ := by
    rw [← integral_finsetSum s (fun i hi => (hf i hi).1.norm)]
    exact integral_mono ((IsBVOn.finsetSum s hf).1.norm)
      (integrable_finsetSum s fun i hi => (hf i hi).1.norm)
      (fun x => norm_sum_le s (fun i => f i x))
  simpa only [Finset.sum_add_distrib] using
    add_le_add hnorm (variation_finsetSum_toReal_le s hf)

/-- Absolute homogeneity also holds for the ordinary-real BV norm expression. -/
theorem bv_norm_const_mul {n : ℕ} (c : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) :
    (∫ x in U, ‖c * f x‖) + (variation (fun x => c * f x) U).toReal =
      |c| * ((∫ x in U, ‖f x‖) + (variation f U).toReal) := by
  simp only [norm_mul, Real.norm_eq_abs, integral_const_mul, variation_const_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg c), mul_add]

end LiquidDrop
