import Mathlib

open Finset

namespace SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]


/-- The degree-sum formula for a degree regular graph. -/
theorem IsRegularOfDegree.twice_card_edges {d : ℕ} (h : G.IsRegularOfDegree d) :
    2 * #G.edgeFinset = d * Fintype.card V := by
  rw [← sum_degrees_eq_twice_card_edges, sum_congr rfl fun v _ ↦ h.degree_eq v,
    sum_const, card_univ, smul_eq_mul, mul_comm]

-- TODO replace card_edgeFinset_completeEquipartiteGraph proof with above

end SimpleGraph
