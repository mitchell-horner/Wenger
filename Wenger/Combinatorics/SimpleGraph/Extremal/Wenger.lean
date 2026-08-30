import Mathlib
import Wenger.Combinatorics.SimpleGraph.Bipartite
import Wenger.Combinatorics.SimpleGraph.Copy
import Wenger.Combinatorics.SimpleGraph.CycleGraph
import Wenger.Combinatorics.SimpleGraph.DegreeSum
import Wenger.Combinatorics.SimpleGraph.Extremal.Basic

open Asymptotics Filter Finset Real

namespace SimpleGraph

variable {p m : ℕ} {a a' b b' : Fin (m + 1) → ZMod p}

section WengerGraph

/-- The adjacency relation of the Wenger graph between a vertex `a` of the left part and a
vertex `b` of the right part: `bⱼ = aⱼ + aⱼ₊₁ · bₘ` for `j < m`. -/
def WengerRel (p m : ℕ) (a b : Fin (m + 1) → ZMod p) : Prop :=
  ∀ j : Fin m, b j.castSucc = a j.castSucc + a j.succ * b (Fin.last m)

instance : DecidableRel (WengerRel p m) := fun _ _ ↦ Fintype.decidableForallFintype

/-- The **Wenger graph** is the bipartite graph on two copies of `(ZMod p) ^ (m+1)`
given by `WengerRel`. -/
def wengerGraph (p m : ℕ) :
    SimpleGraph ((Fin (m + 1) → ZMod p) ⊕ (Fin (m + 1) → ZMod p)) where
  Adj x y := match x, y with
    | .inl a, .inr b => WengerRel p m a b
    | .inr b, .inl a => WengerRel p m a b
    | _, _ => False
  symm := by
    constructor
    rintro (_ | _) (_ | _) h <;> exact h
  loopless := by
    constructor
    rintro (_ | _) h <;> exact h

instance : DecidableRel (wengerGraph p m).Adj
  | .inl _, .inr _ => inferInstanceAs <| Decidable <| WengerRel p m _ _
  | .inr _, .inl _ => inferInstanceAs <| Decidable <| WengerRel p m _ _
  | .inl _, .inl _ => inferInstanceAs <| Decidable False
  | .inr _, .inr _ => inferInstanceAs <| Decidable False

@[simp] lemma wengerGraph_adj_inl_inr :
    (wengerGraph p m).Adj (.inl a) (.inr b) ↔ WengerRel p m a b := Iff.rfl

@[simp] lemma wengerGraph_adj_inr_inl :
    (wengerGraph p m).Adj (.inr b) (.inl a) ↔ WengerRel p m a b := Iff.rfl

@[simp] lemma wengerGraph_adj_inl_inl :
    ¬(wengerGraph p m).Adj (.inl a) (.inl a') := id

@[simp] lemma wengerGraph_adj_inr_inr :
    ¬(wengerGraph p m).Adj (.inr b) (.inr b') := id

/-- The Wenger graph is a subgraph of the complete bipartite graph on its two parts. -/
theorem wengerGraph_le_completeBipartiteGraph :
    wengerGraph p m ≤ completeBipartiteGraph (Fin (m + 1) → ZMod p) (Fin (m + 1) → ZMod p) := by
  rintro (_ | _) (_ | _) h <;> simp_all

/-- The Wenger graph is bipartite in its two parts. -/
theorem isBipartiteWith_wengerGraph :
    (wengerGraph p m).IsBipartiteWith (Set.range Sum.inl) (Set.range Sum.inr) :=
  (isBipartiteWith_completeBipartiteGraph).mono wengerGraph_le_completeBipartiteGraph

/-- The Wenger graph is bipartite. -/
theorem isBipartite_wengerGraph : (wengerGraph p m).IsBipartite :=
    isBipartiteWith_wengerGraph.isBipartite

/-- The neighbor of `a` in the right part with last coordinate `bₘ`. -/
def wengerNeighborInr (a : Fin (m + 1) → ZMod p) (bₘ : ZMod p) : Fin (m + 1) → ZMod p :=
  Fin.lastCases bₘ fun j : Fin m ↦ a j.castSucc + a j.succ * bₘ

@[simp] lemma wengerNeighborInr_last (a : Fin (m + 1) → ZMod p) (bₘ : ZMod p) :
    wengerNeighborInr a bₘ (Fin.last m) = bₘ := by
  rw [wengerNeighborInr, Fin.lastCases_last]

@[simp] lemma wengerNeighborInr_castSucc (a : Fin (m + 1) → ZMod p) (bₘ : ZMod p) (j : Fin m) :
    wengerNeighborInr a bₘ j.castSucc = a j.castSucc + a j.succ * bₘ := by
  rw [wengerNeighborInr, Fin.lastCases_castSucc]

/-- `wengerNeighborInr a bₘ` is a neighbour of `a`. -/
lemma wengerRel_wengerNeighborInr (a : Fin (m + 1) → ZMod p) (bₘ : ZMod p) :
    WengerRel p m a (wengerNeighborInr a bₘ) :=
  fun j ↦ by rw [wengerNeighborInr_last, wengerNeighborInr_castSucc]

/-- `a` and `wengerNeighborInr a bₘ` are adjacent in the Wenger graph. -/
lemma wengerGraph_adj_wengerNeighborInr (a : Fin (m + 1) → ZMod p) (bₘ : ZMod p) :
    (wengerGraph p m).Adj (.inl a) (.inr <| wengerNeighborInr a bₘ) :=
  wengerRel_wengerNeighborInr a bₘ

/-- The neighbours of a vertex in the left part are exactly the `wengerNeighborInr`s. -/
lemma wengerRel_iff_exists_wengerNeighborInr :
    WengerRel p m a b ↔ ∃ bₘ, wengerNeighborInr a bₘ = b := by
  refine ⟨fun h ↦ ⟨b (Fin.last m), funext fun j ↦ ?_⟩, fun ⟨bₘ, hb⟩ ↦ ?_⟩
  · induction j using Fin.lastCases with
    | last => rw [wengerNeighborInr_last]
    | cast j =>
      rw [wengerNeighborInr_castSucc]
      exact (h j).symm
  · rw [← hb]
    exact wengerRel_wengerNeighborInr a bₘ

/-- **Wenger's Lemma 2**: two neighbours of `a` that agree in the last coordinate are equal. -/
lemma WengerRel.eq_of_last_eq (h : WengerRel p m a b) (h' : WengerRel p m a b') :
    b (Fin.last m) = b' (Fin.last m) → b = b' := by
  rw [wengerRel_iff_exists_wengerNeighborInr] at h h'
  rw [← h.choose_spec, wengerNeighborInr_last, ← h'.choose_spec, wengerNeighborInr_last]
  exact congrArg (wengerNeighborInr a)

lemma wengerNeighborInr_injective (a : Fin (m + 1) → ZMod p) :
    Function.Injective (wengerNeighborInr a) := fun bₘ bₘ' h ↦ by
  simpa [wengerNeighborInr_last] using congrFun h (Fin.last m)

/-- The neighbour of `b` in the left part with last coordinate `aₘ`. -/
def wengerNeighborInl (b : Fin (m + 1) → ZMod p) (aₘ : ZMod p) : Fin (m + 1) → ZMod p :=
  Fin.reverseInduction aₘ fun j ih ↦ b j.castSucc - ih * b (Fin.last m)

@[simp] lemma wengerNeighborInl_last (b : Fin (m + 1) → ZMod p) (aₘ : ZMod p) :
    wengerNeighborInl b aₘ (Fin.last m) = aₘ := by
  rw [wengerNeighborInl, Fin.reverseInduction_last]

@[simp] lemma wengerNeighborInl_castSucc (b : Fin (m + 1) → ZMod p) (aₘ : ZMod p) (j : Fin m) :
    wengerNeighborInl b aₘ j.castSucc
      = b j.castSucc - wengerNeighborInl b aₘ j.succ * b (Fin.last m) := by
  rw [wengerNeighborInl, wengerNeighborInl, Fin.reverseInduction_castSucc]

/-- `wengerNeighborInl b aₘ` is a neighbour of `b`. -/
lemma wengerRel_wengerNeighborInl (b : Fin (m + 1) → ZMod p) (aₘ : ZMod p) :
    WengerRel p m (wengerNeighborInl b aₘ) b :=
  fun j ↦ by rw [wengerNeighborInl_castSucc, sub_add_cancel]

/-- `b` and `wengerNeighborInl b aₘ` are adjacent in the Wenger graph. -/
lemma wengerGraph_adj_wengerNeighborInl (b : Fin (m + 1) → ZMod p) (aₘ : ZMod p) :
    (wengerGraph p m).Adj (.inl <| wengerNeighborInl b aₘ) (.inr b) :=
  wengerRel_wengerNeighborInl b aₘ

/-- The neighbours of a vertex of the right part are exactly the `wengerNeighborInl`s. -/
lemma wengerRel_iff_exists_wengerNeighborInl :
    WengerRel p m a b ↔ ∃ aₘ, wengerNeighborInl b aₘ = a := by
  refine ⟨fun h ↦ ⟨a (Fin.last m), funext fun j ↦ ?_⟩, fun ⟨aₘ, ha⟩ ↦ ?_⟩
  · induction j using Fin.reverseInduction with
    | last => rw [wengerNeighborInl_last]
    | cast j ih =>
      rw [wengerNeighborInl_castSucc, ih]
      exact sub_eq_of_eq_add <| h j
  · rw [← ha]
    exact wengerRel_wengerNeighborInl b aₘ

lemma wengerNeighborInl_injective (b : Fin (m + 1) → ZMod p) :
    Function.Injective (wengerNeighborInl b) := fun α α' h ↦ by
  simpa [wengerNeighborInl_last] using congrFun h (Fin.last m)

/-- The neighbor set of a vertex `a` in the left part of `wengerGraph p m` is
exactly the range of `wengerNeighborInr a` in the right part. -/
lemma neighborSet_wengerGraph_inl (a : Fin (m + 1) → ZMod p) :
    (wengerGraph p m).neighborSet (.inl a) = Set.range (Sum.inr ∘ wengerNeighborInr a) := by
  simp [Set.ext_iff, wengerRel_iff_exists_wengerNeighborInr]

/-- The neighbor set of a vertex `b` in the right part of `wengerGraph p m` is
exactly the range of `wengerNeighborInl b` in the left part. -/
lemma neighborSet_wengerGraph_inr (b : Fin (m + 1) → ZMod p) :
    (wengerGraph p m).neighborSet (.inr b) = Set.range (Sum.inl ∘ wengerNeighborInl b) := by
  simp [Set.ext_iff, wengerRel_iff_exists_wengerNeighborInl]

variable [NeZero p]

@[inherit_doc neighborSet_wengerGraph_inl]
lemma neighborFinset_wengerGraph_inl (a : Fin (m + 1) → ZMod p) :
    (wengerGraph p m).neighborFinset (.inl a) = univ.image (Sum.inr ∘ wengerNeighborInr a) := by
  simp [neighborFinset_def, neighborSet_wengerGraph_inl]

@[inherit_doc neighborSet_wengerGraph_inr]
lemma neighborFinset_wengerGraph_inr (b : Fin (m + 1) → ZMod p) :
    (wengerGraph p m).neighborFinset (.inr b) = univ.image (Sum.inl ∘ wengerNeighborInl b) := by
  simp [neighborFinset_def, neighborSet_wengerGraph_inr]

/-- The degree of a vertex in the left part of `wengerGraph p m` is `p`. -/
lemma degree_wengerGraph_inl (a : Fin (m + 1) → ZMod p) :
    (wengerGraph p m).degree (.inl a) = p := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_wengerGraph_inl,
    card_image_of_injective _ <| Sum.inr_injective.comp (wengerNeighborInr_injective a),
    card_univ, ZMod.card]

/-- The degree of a vertex in the right part of `wengerGraph p m` is `p`. -/
lemma degree_wengerGraph_inr (b : Fin (m + 1) → ZMod p) :
    (wengerGraph p m).degree (.inr b) = p := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_wengerGraph_inr,
    card_image_of_injective _ <| Sum.inl_injective.comp (wengerNeighborInl_injective b),
    card_univ, ZMod.card]

/-- The degree of a vertex in `wengerGraph p m` is `p`. -/
theorem isRegularOfDegree_wengerGraph : (wengerGraph p m).IsRegularOfDegree p
  | .inl a => degree_wengerGraph_inl a
  | .inr b => degree_wengerGraph_inr b

/-- The Wenger graph `wengerGraph p m` has `p ^ (m + 2)` edges (on `2 * p ^ (m + 1)` vertices). -/
theorem card_edgeFinset_wengerGraph :
    #(wengerGraph p m).edgeFinset = p ^ (m + 2) := by
  apply Nat.eq_of_mul_eq_mul_left two_pos
  rw [isRegularOfDegree_wengerGraph.twice_card_edges, Fintype.card_sum, Fintype.card_fun,
    ZMod.card, Fintype.card_fin, mul_add, ← pow_succ', ← two_mul]

omit [NeZero p] in
/-- If `a` and `a'` are both adjacent to `b`, then the coordinates of `a - a'`
are geometric in `-bₘ`. -/
lemma WengerRel.sub_apply
    (h : WengerRel p m a b) (h' : WengerRel p m a' b) {j : Fin (m + 1)} :
    a j - a' j = (- b (Fin.last m)) ^ (m - j) * (a (Fin.last m) - a' (Fin.last m)) := by
  induction j using Fin.reverseInduction with
  | last => rw [Fin.val_last, Nat.sub_self, pow_zero, one_mul]
  | cast j ih =>
    have hsucc : a j.castSucc - a' j.castSucc = (- b (Fin.last m)) * (a j.succ - a' j.succ) := by
      linear_combination h' j - h j
    rw [hsucc, ih, Fin.val_castSucc, Fin.val_succ, Nat.sub_succ, Nat.pred_eq_sub_one,
      ← mul_assoc, ← pow_succ', Nat.sub_one_add_one_eq_of_pos (Nat.sub_pos_of_lt j.is_lt)]

omit [NeZero p] in
/-- **Wenger's Lemma 1**: on a cycle `v₀ w₀ v₁ w₁ ⋯ vₘ wₘ` of length `2 * (m + 1)` in the
Wenger graph, every `w i₀` shares its last coordinate with some other `w i`. -/
theorem WengerRel.exists_ne_last_eq (hp : p.Prime)
    {v w : ZMod (m + 1) → Fin (m + 1) → ZMod p}
    (hr : ∀ i, WengerRel p m (v i) (w i)) (hl : ∀ i, WengerRel p m (v (i + 1)) (w i))
    (hv : ∀ i, v (i + 1) ≠ v i) (i₀ : ZMod (m + 1)) :
    ∃ i, i ≠ i₀ ∧ w i (Fin.last m) = w i₀ (Fin.last m) := by
  haveI := Fact.mk hp
  by_contra! hcon
  -- it suffices that `v (i₀ + 1) - v i₀ = 0`
  refine hv i₀ <| funext fun j ↦ sub_eq_zero.mp ?_
  rw [WengerRel.sub_apply (hl i₀) (hr i₀)]
  -- let `P := ∏_{i ≠ i₀} (X - (-w i m))` such that `P (-w i₀ m) ≠ 0`
  set P := Lagrange.nodal (univ.erase i₀) fun i ↦ -w i (Fin.last m) with hP_def
  have hP_deg : P.natDegree = m := by
    rw [Lagrange.natDegree_nodal, card_erase_of_mem (mem_univ i₀),
      card_univ, ZMod.card, Nat.add_sub_cancel]
  -- it suffices that `P (-w i₀ m) * (v (i₀ + 1) - v i₀) = 0`
  refine mul_eq_zero_of_right _ <| (eq_zero_or_eq_zero_of_mul_eq_zero ?_).resolve_left <|
    Lagrange.eval_nodal_not_at_node (s := univ.erase i₀) (v := fun i ↦ -w i (Fin.last m))
      fun i hi heq ↦ hcon i (ne_of_mem_erase hi) (neg_injective heq).symm
  calc P.eval (-w i₀ (Fin.last m)) * (v (i₀ + 1) (Fin.last m) - v i₀ (Fin.last m))
    -- it suffices that `∑ᵢ P (-w i m) * (v (i + 1) - v i) = 0`
    _ = ∑ i, P.eval (-w i (Fin.last m)) * (v (i + 1) (Fin.last m) - v i (Fin.last m)) := by
        refine Eq.symm <| sum_eq_single_of_mem i₀ (mem_univ i₀) fun i _ hi ↦
          mul_eq_zero_of_left ?_ ((v (i + 1) (Fin.last m) - v i (Fin.last m)))
        exact Lagrange.eval_nodal_at_node
          (v := fun i ↦ -w i (Fin.last m)) (mem_erase_of_ne_of_mem hi <| mem_univ i)
    _ = ∑ i, ∑ k ∈ range (m + 1), P.coeff k
          * (- w i (Fin.last m)) ^ k * (v (i + 1) (Fin.last m) - v i (Fin.last m)) := by
        refine sum_congr rfl fun i _ ↦ ?_
        rw [Polynomial.eval_eq_sum_range' <| Nat.lt_succ_of_le hP_deg.le, sum_mul]
    _ = ∑ k ∈ range (m + 1), P.coeff k
          * ∑ i : ZMod (m + 1), ((v (i + 1) ⟨m - k, by omega⟩) - (v i ⟨m - k, by omega⟩)) := by
        refine sum_comm.trans <| sum_congr rfl fun k hk ↦
          (sum_congr rfl fun i _ ↦ ?_).trans (mul_sum ..).symm
        rw [WengerRel.sub_apply (hl i) (hr i) (j := ⟨m - k, by omega⟩),
          Nat.sub_sub_self (Nat.lt_succ_iff.mp (mem_range.mp hk)), ← mul_assoc]
    _ = 0 := by
        refine sum_eq_zero fun k hk ↦ mul_eq_zero_of_right (P.coeff k) ?_
        rw [sum_sub_distrib, sub_eq_zero]
        exact Equiv.sum_comp (Equiv.addRight 1) (v · ⟨m - k, by omega⟩)

end WengerGraph

section Extremal

theorem cycleGraph_free_wengerGraph (hp : p.Prime)
    (hm : m + 1 = 2 ∨ m + 1 = 3 ∨ m + 1 = 5) :
    (cycleGraph (2 * (m + 1))).Free (wengerGraph p m) := by
  haveI : Fact (1 < m + 1) := ⟨by omega⟩
  -- a copy of the cycle is two injective alternating functions indexed by `ZMod (m + 1)`
  rw [Free, cycleGraph_isContained_iff_exists_inj_inj_adj_adj
    wengerGraph_le_completeBipartiteGraph (by omega)]
  rintro ⟨v, w, hv, hw, hadj₁, hadj₂⟩
  -- by Lemma 2, consecutive indices carry distinct last coordinates
  have hne_succ {i j} : w i (Fin.last m) = w j (Fin.last m) → i ≠ j + 1 :=
    fun heq_last heq_succ ↦ succ_ne_self j <| hw <|
      WengerRel.eq_of_last_eq (hadj₁ _) (hadj₂ _) (heq_succ ▸ heq_last)
  -- by Lemma 1, every index has a `g i ≠ i` with the same last coordinate
  choose g hg_ne hg_eq_last
    using WengerRel.exists_ne_last_eq hp hadj₁ hadj₂ (succ_ne_self · <| hv ·)
  -- so `g i` is never a cyclic neighbour of `i`
  have hg (i) : g i ≠ i ∧ g i ≠ i + 1 ∧ i ≠ g i + 1 :=
    ⟨hg_ne i, hne_succ (hg_eq_last i), hne_succ (hg_eq_last i).symm⟩
  -- `g` is only a contradiction for `m + 1 ∈ {2, 3, 5}`
  obtain rfl | rfl | rfl : m = 1 ∨ m = 2 ∨ m = 4 := by omega
  -- `m + 1 = 2` and `m + 1 = 3` are small enough to decide
  · have h : ∀ i j : ZMod 2, ¬(j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) := by decide
    exact h 0 (g 0) (hg 0)
  · have h : ∀ i j : ZMod 3, ¬(j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) := by decide
    exact h 0 (g 0) (hg 0)
  -- if `m + 1 = 5` then `g` is an involution and has a fixed-point, but `g` is fixed-point-free
  · have h : ∀ i j k : ZMod 5, (j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1) →
      (k ≠ j ∧ k ≠ j + 1 ∧ j ≠ k + 1) → (k ≠ i + 1 ∧ i ≠ k + 1) → k = i := by decide
    have hg_inv : Function.Involutive g := fun i ↦ h i (g i) (g (g i)) (hg i) (hg (g i))
      ⟨hne_succ <| (hg_eq_last (g i)).trans (hg_eq_last i),
          hne_succ <| ((hg_eq_last (g i)).trans (hg_eq_last i)).symm⟩
    obtain ⟨i, hi⟩ : ∃ i, g i = i := Equiv.Perm.exists_fixed_point_of_prime
      (p := 2) (n := 1) (σ := hg_inv.toPerm) (by norm_num) (Equiv.ext hg_inv)
    exact hg_ne i hi

/-- `wengerGraph p 1` contains no `cycleGraph 4`. -/
theorem cycleGraph_four_free_wengerGraph (hp : p.Prime) :
    (cycleGraph 4).Free (wengerGraph p 1) :=
  cycleGraph_free_wengerGraph (m := 1) hp (by norm_num)

/-- `wengerGraph p 2` contains no `cycleGraph 6`. -/
theorem cycleGraph_six_free_wengerGraph (hp : p.Prime) :
    (cycleGraph 6).Free (wengerGraph p 2) :=
  cycleGraph_free_wengerGraph (m := 2) hp (by norm_num)

/-- `wengerGraph p 4` contains no `cycleGraph 10`. -/
theorem cycleGraph_ten_free_wengerGraph (hp : p.Prime) :
    (cycleGraph 10).Free (wengerGraph p 4) :=
  cycleGraph_free_wengerGraph (m := 4) hp (by norm_num)

/-- The generic Wenger `cycleGraph` extremal number lower bound.

If the Wenger graphs `wengerGraph p m` contain no even cycles for all prime `p`, then the extremal
numbers of `cycleGraph (2 * (m + 1))` are `Ω(n^((m+2)/(m+1)))`. -/
theorem isBigO_rpow_extremalNumber_cycleGraph_of_free {m : ℕ}
    (h : ∀ {p : ℕ}, p.Prime → (cycleGraph (2 * (m + 1))).Free (wengerGraph p m)) :
    (fun n : ℕ ↦ (n : ℝ) ^ (((m : ℝ) + 2) / ((m : ℝ) + 1))) =O[atTop]
      fun n : ℕ ↦ (extremalNumber n (cycleGraph (2 * (m + 1))) : ℝ) := by
  -- `2 ^ (m + 2)` is sufficently large for `n` with coefficent `4 ^ (m + 3)`
  refine IsBigO.of_bound (4 ^ ((m : ℝ) + 3)) (eventually_atTop.mpr ⟨2 ^ (m + 2), fun n hn ↦ ?_⟩)
  rw [Real.norm_of_nonneg <| Real.rpow_nonneg (Nat.cast_nonneg _) _,
    Real.norm_of_nonneg <| Nat.cast_nonneg _, ← div_le_iff₀' (by positivity),
    ← one_div_mul_eq_div ((m : ℝ) + 1) ((m : ℝ) + 2), Real.rpow_mul (Nat.cast_nonneg n),
    show (m : ℝ) + 3 = ((m : ℝ) + 2) + 1 by ring,
    Real.rpow_add (by positivity) ((m : ℝ) + 2) 1, Real.rpow_one, ← div_div,
    ← Real.div_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)]
  -- pick `x` such that `2 * p^(m + 1) ≤ 2 * x^(m + 1) = n`
  set x : ℝ := ((n : ℝ) / 2) ^ (1 / ((m : ℝ) + 1)) with hx_def
  -- bertrand's postulate gives a prime `p ≤ x < 2 * p`
  obtain ⟨p, hp, hp_le_x, hx_lt_2p⟩ : ∃ p : ℕ, p.Prime ∧ p ≤ x ∧ x < 2 * p := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_pow, Nat.cast_ofNat,
      show m + 2 = (m + 1) + 1 by norm_num, pow_succ, ← le_div_iff₀ (by positivity),
      ← Real.rpow_natCast (2 : ℝ) (m + 1), Nat.cast_add, Nat.cast_one,
      ← Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity),
      ← one_div, ← hx_def] at hn
    obtain ⟨p, hp, hp_lt, hle_2p⟩ : ∃ p : ℕ, p.Prime ∧ (⌊x⌋₊ / 2) < p ∧ p ≤ 2 * (⌊x⌋₊ / 2) :=
      Nat.exists_prime_lt_and_le_two_mul (⌊x⌋₊ / 2) <|
        Nat.div_ne_zero_iff.mpr ⟨by positivity, Nat.le_floor hn⟩
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← Nat.le_floor_iff (by positivity)]
      exact hle_2p.trans <| Nat.mul_div_le ⌊x⌋₊ 2
    · rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm p 2] at hp_lt
      exact_mod_cast Nat.lt_of_floor_lt hp_lt
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  calc ((n : ℝ) ^ (1 / ((m : ℝ) + 1)) / 4) ^ ((m : ℝ) + 2) / 4
    _ = 2 ^ (((m : ℝ) + 2) / ((m : ℝ) + 1)) / 4 * (x / 4) ^ ((m : ℝ) + 2) := by
        rw [← mul_div_cancel₀ (n : ℝ) two_ne_zero, Real.mul_rpow (by positivity) (by positivity),
          ← hx_def, mul_div_assoc, Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul (by positivity), one_div_mul_eq_div, mul_div_right_comm]
    _ ≤ (x / 4) ^ ((m : ℝ) + 2) := by
        apply mul_le_of_le_one_left (by positivity)
        rw [div_le_one (by positivity), show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num,
          Real.rpow_le_rpow_left_iff one_lt_two, div_le_iff₀ (by positivity)]
        exact le_of_le_of_eq (le_add_of_nonneg_right <| Nat.cast_nonneg m) (by ring)
    -- the number of edges in `wengerGraph p m` is the upper bound
    _ ≤ (#(wengerGraph p m).edgeFinset : ℝ) := by
        rw [card_edgeFinset_wengerGraph, Nat.cast_pow,
          show (m : ℝ) + 2 = ((m + 2 : ℕ) : ℝ) by norm_cast, Real.rpow_natCast,
          pow_le_pow_iff_left₀ (by positivity) (by positivity) (by positivity),
          div_le_iff₀ (by positivity), mul_comm (p : ℝ) 4]
        exact hx_lt_2p.le.trans <| mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg p)
    _ ≤ (extremalNumber (2 * p ^ (m + 1)) (cycleGraph (2 * (m + 1))) : ℝ) := by
        conv =>
          enter [2, 1, 1]
          rw [two_mul,  ← Fintype.card_fin (m + 1), ← ZMod.card p,
            ← Fintype.card_fun, ← Fintype.card_sum]
        exact_mod_cast card_edgeFinset_le_extremalNumber (h hp)
    _ ≤ (extremalNumber n (cycleGraph (2 * (m + 1))) : ℝ) := by
        refine mod_cast extremalNumber_mono (fun {w} ↦ ?_) ?_
        · rw [← mem_support_iff_not_isIsolated, mem_support]
          exact ⟨w + 1, cycleGraph_adj.mpr (by simp)⟩
        · rw [← Nat.cast_le (α := ℝ), Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
            ← le_div_iff₀' (by positivity), ← Real.rpow_natCast (p : ℝ) (m + 1),
            Nat.cast_add, Nat.cast_one,
            ← Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity) (by positivity),
            ← one_div, ← hx_def]
          exact hp_le_x

/-- The `cycleGraph 4` extremal number lower bound. -/
theorem isBigO_rpow_extremalNumber_cycleGraph_four :
    (fun n : ℕ ↦ (n : ℝ) ^ (3 / 2 : ℝ))
      =O[atTop] fun n : ℕ ↦ (extremalNumber n (cycleGraph 4) : ℝ) := by
  rw [show (3 / 2 : ℝ) = ((1 : ℕ) + 2) / ((1 : ℕ) + 1) by norm_num]
  exact isBigO_rpow_extremalNumber_cycleGraph_of_free (m := 1) cycleGraph_four_free_wengerGraph

/-- The `cycleGraph 6` extremal number lower bound. -/
theorem isBigO_rpow_extremalNumber_cycleGraph_six :
    (fun n : ℕ ↦ (n : ℝ) ^ (4 / 3 : ℝ))
      =O[atTop] fun n : ℕ ↦ (extremalNumber n (cycleGraph 6) : ℝ) := by
  rw [show (4 / 3 : ℝ) = ((2 : ℕ) + 2) / ((2 : ℕ) + 1) by norm_num]
  exact isBigO_rpow_extremalNumber_cycleGraph_of_free (m := 2) cycleGraph_six_free_wengerGraph

/-- The `cycleGraph 10` extremal number lower bound. -/
theorem isBigO_rpow_extremalNumber_cycleGraph_ten :
    (fun n : ℕ ↦ (n : ℝ) ^ (6 / 5 : ℝ))
      =O[atTop] fun n : ℕ ↦ (extremalNumber n (cycleGraph 10) : ℝ) := by
  rw [show (6 / 5 : ℝ) = ((4 : ℕ) + 2) / ((4 : ℕ) + 1) by norm_num]
  exact isBigO_rpow_extremalNumber_cycleGraph_of_free (m := 4) cycleGraph_ten_free_wengerGraph

end Extremal

end SimpleGraph
