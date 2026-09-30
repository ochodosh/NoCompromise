module

public import NoCompromise.Elliptic.StrongMaximum
public import NoCompromise.Elliptic.HarmonicMeanValue

@[expose] public section

/-!
# Strong maximum principle for weakly harmonic functions
-/

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology
namespace LiquidDrop

/-- Blueprint `prop:strong-max`. A continuous distributionally harmonic
function attaining its maximum on a connected open domain is constant.
Continuity fixes the representative; no integrability or derivative bound
is imposed beyond the genuine weak harmonicity hypothesis. -/
theorem strong_maximum {n : ℕ} (hn : n < 4)
    {G : Set (EuclideanSpace ℝ (Fin n))} (hG : IsOpen G) (hconn : IsPreconnected G)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContinuousOn u G)
    (h : HasDistributionalLaplacianOn u (fun _ => 0) G)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ G)
    (hmax : ∀ x ∈ G, u x ≤ u x₀) : ∀ x ∈ G, u x = u x₀ :=
  strong_maximum_of_mean_value hG hconn hu
    (fun c _ _r hr hs => h.average_ball_eq hn hG hu c hr hs) hx₀ hmax

/-- A nonnegative continuous weakly harmonic function on a connected open
domain is either identically zero or strictly positive everywhere. -/
theorem harmonic_nonnegative_zero_or_positive {n : ℕ} (hn : n < 4)
    {G : Set (EuclideanSpace ℝ (Fin n))} (hG : IsOpen G) (hconn : IsPreconnected G)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContinuousOn u G)
    (h : HasDistributionalLaplacianOn u (fun _ => 0) G)
    (hnonneg : ∀ x ∈ G, 0 ≤ u x) :
    (∀ x ∈ G, u x = 0) ∨ (∀ x ∈ G, 0 < u x) := by
  by_cases hp : ∀ x ∈ G, 0 < u x
  · exact Or.inr hp
  push Not at hp
  obtain ⟨x₀, hx₀, hu₀⟩ := hp
  have hz : u x₀ = 0 := le_antisymm hu₀ (hnonneg x₀ hx₀)
  have hmean : ∀ c ∈ G, ∀ r : ℝ, 0 < r → closedBall c r ⊆ G →
      (⨍ x in ball c r, -u x) = -u c := by
    intro c _ r hr hs
    change (⨍ x in ball c r, (-u) x) = -u c
    rw [average_neg, h.average_ball_eq hn hG hu c hr hs]
  have heq := strong_maximum_of_mean_value hG hconn hu.neg hmean hx₀
    (fun x hx => by dsimp; rw [hz]; linarith [hnonneg x hx])
  exact Or.inl (fun x hx => by
    simpa only [Pi.neg_apply, hz, neg_zero, neg_eq_zero] using heq x hx)

end LiquidDrop
