import NoCompromise.Sobolev.W11TraceOperator
import NoCompromise.Sobolev.W11VectorData

/-!
# The L¹ trace for vector-valued W¹,¹ fields

The scalar trace is applied to each coordinate of the actual weak derivative
matrix. The resulting vector trace is Hausdorff-integrable, obeys a bound in
terms of the L¹ norms of the vector field and its derivative matrix, and agrees
with actual restriction for continuous representatives.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace LiquidDrop

def w11VectorTrace {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (T : W11Space D →L[ℝ] Lp ℝ 1 μ)
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hZ : HasW11VectorGradientOn Z J D) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => T (W11Space.ofFunction _ _ (hZ.component i)) x)

theorem w11_vector_trace_bound {n : ℕ} {D : Set (EuclideanSpace ℝ (Fin n))}
    {μ : Measure (EuclideanSpace ℝ (Fin n))}
    (T : W11Space D →L[ℝ] Lp ℝ 1 μ) {C : ℝ} (hC : 0 ≤ C) (hTC : ‖T‖ ≤ C)
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {J : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hZ : HasW11VectorGradientOn Z J D) :
    Integrable (w11VectorTrace T hZ) μ ∧
      (∫ x, ‖w11VectorTrace T hZ x‖ ∂μ) ≤
        n * C * ((∫ x in D, ‖Z x‖) + ∫ x in D, ‖J x‖) := by
  classical
  let u (i : Fin n) := W11Space.ofFunction _ _ (hZ.component i)
  have hi (i : Fin n) : Integrable (fun x => T (u i) x) μ :=
    memLp_one_iff_integrable.mp (Lp.memLp _)
  have hTr : Integrable (w11VectorTrace T hZ) μ :=
    integrable_piLp_iff.mpr hi
  have hb (i : Fin n) : (∫ x, ‖T (u i) x‖ ∂μ) ≤
      C * ((∫ x in D, ‖Z x‖) + ∫ x in D, ‖J x‖) := by
    calc
      _ = ‖T (u i)‖ := by
        rw [Lp.norm_def, toReal_eLpNorm, lpNorm_one_eq_integral_norm (hi i).1]
      _ ≤ C * ‖u i‖ := (T.le_opNorm (u i)).trans
        (mul_le_mul_of_nonneg_right hTC (norm_nonneg _))
      _ ≤ C * (lpNorm (fun x => Z x i) 1 (volume.restrict D) +
          lpNorm (fun x => (J x).adjoint (EuclideanSpace.single i 1)) 1 (volume.restrict D)) :=
        mul_le_mul_of_nonneg_left (W11Space.norm_ofFunction_le _ _ (hZ.component i)) hC
      _ ≤ _ := mul_le_mul_of_nonneg_left (hZ.component_bound i) hC
  refine ⟨hTr, ?_⟩
  calc
    _ ≤ ∫ x, ∑ i : Fin n, ‖T (u i) x‖ ∂μ := by
      apply integral_mono hTr.norm (integrable_finsetSum _ fun i _ => (hi i).norm)
      exact fun x => norm_euclidean_le_sum_norm (w11VectorTrace T hZ x)
    _ = ∑ i : Fin n, ∫ x, ‖T (u i) x‖ ∂μ :=
      integral_finsetSum _ fun i _ => (hi i).norm
    _ ≤ ∑ _i : Fin n, C * ((∫ x in D, ‖Z x‖) + ∫ x in D, ‖J x‖) :=
      Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- Blueprint `prop:trace-L1`: the actual constructed trace satisfies the L¹
bound for vector fields, using the Euclidean operator norm of their derivative. -/
theorem exists_w11_vector_trace {k : ℕ}
    {D : Set (EuclideanSpace ℝ (Fin (k + 1)))} (hD : IsOpen D)
    (hbD : Bornology.IsBounded D) (hL : HasLipschitzBoundary D) :
    ∃ T : W11Space D →L[ℝ]
      Lp ℝ 1 ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Z J (hZ : HasW11VectorGradientOn Z J D),
      Integrable (w11VectorTrace T hZ)
        ((Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ∧
      (∫ x, ‖w11VectorTrace T hZ x‖
        ∂(Measure.euclideanHausdorffMeasure k).restrict (frontier D)) ≤
        C * ((∫ x in D, ‖Z x‖) + ∫ x in D, ‖J x‖) ∧
      (Continuous Z → w11VectorTrace T hZ =ᵐ[
        (Measure.euclideanHausdorffMeasure k).restrict (frontier D)] Z) := by
  obtain ⟨T, C, hC, hTC, hT⟩ := exists_w11_trace_operator hD hbD hL
  refine ⟨T, (k + 1 : ℝ) * C, mul_nonneg (by positivity) hC, fun Z J hZ => ?_⟩
  have hb := w11_vector_trace_bound T hC hTC hZ
  refine ⟨hb.1, by simpa only [Nat.cast_add, Nat.cast_one] using hb.2, ?_⟩
  intro hc
  have heq (i : Fin (k + 1)) := hT (fun x => Z x i)
    (fun x => (J x).adjoint (EuclideanSpace.single i 1)) (hZ.component i)
    ((EuclideanSpace.proj i).continuous.comp hc)
  filter_upwards [ae_all_iff.mpr heq] with x hx
  exact PiLp.ext fun i => hx i

end LiquidDrop
