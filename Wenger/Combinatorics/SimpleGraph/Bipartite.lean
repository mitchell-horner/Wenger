import Mathlib

namespace SimpleGraph

variable {V : Type*} {G G' : SimpleGraph V}

/-- If `G` is bipartite with parts `s` and `t`, then so is any subgraph `G' ≤ G`. -/
theorem IsBipartiteWith.mono {s t : Set V} (h : G.IsBipartiteWith s t) (hle : G' ≤ G) :
    G'.IsBipartiteWith s t :=
  ⟨h.disjoint, fun _ _ hadj ↦ h.mem_of_adj (hle hadj)⟩

/-- If `G` is bipartite, then so is any subgraph `G' ≤ G`. -/
theorem IsBipartite.mono (h : G.IsBipartite) (hle : G' ≤ G) :
    G'.IsBipartite := by
  replace ⟨_, _, h⟩ := h.exists_isBipartiteWith
  exact IsBipartiteWith.isBipartite <| h.mono hle

/-- The complete bipartite graph on `V ⊕ W` is bipartite in the two summands. -/
theorem isBipartiteWith_completeBipartiteGraph {V W : Type*} :
    (completeBipartiteGraph V W).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) where
  disjoint := Set.isCompl_range_inl_range_inr.disjoint
  mem_of_adj _ _ := Set.range_inl ▸ Set.range_inr ▸ id

/-- The complete bipartite graph on `V ⊕ W` is bipartite in the two summands. -/
theorem isBipartite_completeBipartiteGraph {V W : Type*} :
    (completeBipartiteGraph V W).IsBipartite :=
  isBipartiteWith_completeBipartiteGraph.isBipartite

end SimpleGraph
