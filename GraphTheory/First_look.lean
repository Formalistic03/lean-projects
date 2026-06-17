/-
Copyright (c) 2026 Jakub Štepo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jakub Štepo
-/
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
/-
# A first look at how graph theory is done in Lean

In this file, I summarise my initial experience and findings.

There are multiple different approaches to doing graph theory in Lean. It appears
that the intention is to first flesh out the theory for undirected simple graphs
to figure out how to formalise different concepts, and then perhaps generalise
them as much as possible in the usual mathlib fashion.
-/

-- Let us start with the most general object, a directed multigraph:
#check Quiver
-- for each ordered pair of vertices, there is a type of darts
-- categories are defined in terms of quivers, so they are important
-- there is some basic theory and a bit about paths and connectedness,
-- but not much else from a graph-theoretic standpoint

-- Then we have undirected multigraphs:
#check Graph
-- the definition is somewhat complicated
-- aside from the basic theory, not much has been done

-- In the other direction, we have directed simple graphs:
#check Digraph
-- defined simply as a binary relation (adjacency)
-- almost nothing has been done

/-
## SimpleGraph
From now on, we will only concern ourselves with undirected simple graphs.
This is the only class for which the theory has been reasonably well developed.
-/
#check SimpleGraph
-- defined by a symmetric, irreflexive adjacency relation
-- graphs over a given vertex type form a complete Boolean algebra (edges),
-- among other we have the subgraph order, complements, complete graphs, union

#check SimpleGraph.support -- the vertices of non-zero degree
#check SimpleGraph.neighborSet -- the neighbourhood of a vertex
#check SimpleGraph.edgeSet -- the set of the edges
#check Sym2 -- the type of an edge is an unordered pair

-- let us now turn our attention to walks
#check SimpleGraph.Walk -- walk as an inductive type
-- the fact that the Walk type contains information about the endpoints
-- is a bit troublesome; we have to use the following
-- if we have non-definitional equalities about endpoints
#check SimpleGraph.Walk.copy -- and then theorems that this preserves properties
-- also, Walk.nil requires definitionally equal endpoints,
-- so to prove that a walk is nil, we must either prove
-- that the endpoints are equal and then use Walk.copy,
-- or (better) use the following proposition
#check SimpleGraph.Walk.Nil
-- finally, induction on the walk itself may cause complications
-- if we have hypotheses about the endpoints (we cannot generalise them)

#check SimpleGraph.Walk.support -- the list of vertices a walk in order
#check SimpleGraph.Walk.darts -- the darts of a walk in order
#check SimpleGraph.Dart -- an oriented edge
#check SimpleGraph.Walk.IsPath
#check SimpleGraph.Walk.IsCycle

-- connectivity etc:
#check SimpleGraph.Reachable -- there exists a walk between the two vertices
#check SimpleGraph.Connected -- required to be non-empty
#check SimpleGraph.IsAcyclic
#check SimpleGraph.IsTree

-- colouring:
#check SimpleGraph.Coloring -- as a (weak) homomorphism into a complete graph
#check RelHom
#check SimpleGraph.Colorable

/-
Other topics that are covered (to some degree) include:
* containment of a copy as an induced subgraph
* adjacency matrix, incidence matrix
* bipartite graphs
* cliques and independent sets
* edge-connectivity
* matchings (Hall's theorem, Tutte's theorem)
* vertex coverings
* Hamiltonian graphs
* extremal graph theory
* Cayley graphs

So there is a lot of basic theory that has been already built.
On the other hand, some important results an areas are still missing, such as:
* vertex-connectivity
* Menger's theorem even for edge-connectivity
* characterisation of biparite graphs via the absence of odd cycles
* characterisation of Eulerian graphs
* the Kőnig-Egerváry theorem
* Brooks' theorem
* edge colourings (Vizing's theorem)
* planar graphs (Kuratowski's theorem)
* graph minors
* chordal graphs, perfect graphs
* algebraic graph theory

However, it must be stressed that there is ongoining work on all of these.
In fact, many have been formalised and have open pull requests, they simply
have not met the library's standards yet.
-/

/-
Let us now look at a concrete example of using the API and the struggles I had
with it. We will study path graphs, which are defined as Hasse diagrams of the
canonical order on Fin n.
-/
open SimpleGraph
#check pathGraph

-- We will first prove that all vertices have degree at most 2.
#check SimpleGraph.degree
-- however, we need local finiteness of the graph
-- this holds because it is finite:
#check SimpleGraph.neighborSetFintype
-- however, for that, we need decidability of the adjacency relation
-- the crux of the problem is the following missing instance
instance {α : Type*} [Fintype α] [LT α] [DecidableLT α] :
    DecidableRel (CovBy : α → α → Prop) := by
  unfold CovBy
  infer_instance
-- now this goes through
instance (n : ℕ) : DecidableRel (pathGraph n).Adj := by
  intro a b
  unfold pathGraph hasse
  infer_instance
-- an alternative would be:
-- open scoped Classical
-- but the preferred Lean style is to avoid this as much as possible

-- now to the proof
example {n : ℕ} (v : Fin n) :
    (pathGraph n).degree v ≤ 2 := by
  unfold degree
  -- we rewrite the neighbourhood to the following form
  let S := {w : Fin n | v.val + 1 = w.val} ∪ {w : Fin n | w.val + 1 = v.val}
  have hneigh : (pathGraph n).neighborFinset v = S.toFinset := by
    ext w
    unfold neighborFinset neighborSet
    rw [Set.mem_toFinset, Set.mem_toFinset] -- technical rewrites
    exact pathGraph_adj -- matlib lemma
  rw [hneigh]
  unfold S
  -- now we just split the union
  rw [Set.toFinset_union]
  apply le_trans (Finset.card_union_le _ _)
  apply add_le_add (b := 1) (d := 1)
  all_goals
    rw [Finset.card_le_one_iff] -- and prove that the two sets are singletons
    grind -- Lean can manage on its own from this point

-- Next, we prove that path graphs are acyclic, a result which is not yet in mathlib.
-- (I have purposefully only used lia to better see what is really going on.)
lemma pathGraph_acyclic (n : ℕ) :
    (pathGraph n).IsAcyclic := by
  -- we wish to proceed by contradiction
  -- look at the tail of a cycle, it is a path
  -- suppose this path goes from left to right, then since each next vertex
  -- is either one step left or one step right, all steps must be to the left
  -- (in the construction)
  -- first I proved that a walk contains all the vertices between its endpoints
  -- stated differently, if a vertex is not in the walk, the whole walk is on one side
  have hsupp {u v w : Fin n} (p : (pathGraph n).Walk u v)
      (hvw : v < w) (hw : w ∉ p.support) :
      ∀ x ∈ p.support, x < w := by
    -- I found it more natural to do induction on the length
    -- where we let the start vary (this is better due to the definition),
    -- but induction on the walk would be shorter
    induction hl : p.length generalizing u with
    | zero =>
      intro x hx
      -- here, we use Walk.Nil
      rw [Walk.length_eq_zero_iff] at hl
      rw [Walk.nil_iff_support_eq.mp hl, List.mem_singleton] at hx
      rw [hx, hl.eq]
      exact hvw
    | succ k ih =>
      cases p with -- now this works nicely
      | nil => cases hl -- the length is not zero
      | cons hy q =>
        intro x hx; rename_i y -- the second vertex is an implicit argument
        -- we rewrite Walk.cons everywhere
        rw [Walk.length_cons, Nat.succ_inj] at hl
        rw [Walk.support_cons, List.mem_cons] at hw hx
        push Not at hw
        rw [pathGraph_adj] at hy
        cases hx with
        | inl hx =>
          have hyw := ih q hw.right hl y q.start_mem_support
          lia
        | inr hx => exact ih q hw.right hl x hx -- induction hypothesis
  -- now I stated the fact that the vertices do not repeat via length
  -- the proof is very similar in structure
  have hpath {u v : Fin n} (p : (pathGraph n).Walk u v)
      (hp : p.IsPath) (huv : u ≤ v) :
      p.length = v.val - u.val := by
    induction hl : p.length generalizing u with
    | zero =>
      suffices v = u by lia
      symm; exact p.eq_of_length_eq_zero hl
    | succ k ih =>
      cases p with
      | nil => cases hl
      | cons hw q =>
        rename_i w
        rw [Walk.length_cons, Nat.succ_inj] at hl
        rw [Walk.cons_isPath_iff] at hp
        rw [pathGraph_adj] at hw
        have hne : u ≠ v := by
          intro heq; apply hp.right
          rw [heq]
          exact q.end_mem_support
        cases hw with
        | inl hw => -- we went left
          rw [ih q hp.left (by lia) hl]
          lia
        | inr hw =>
          -- we went right, which is impossible, because the walk
          -- we are extending started to the left and ended on the right
          -- to use the previous result, we must reverse this shorter walk
          rw [← Walk.isPath_reverse_iff, ← List.mem_reverse] at hp
          rw [← Walk.support_reverse] at hp
          have hvu := hsupp q.reverse (by lia) hp.right v q.reverse.start_mem_support
          lia
-- alternative formulation (still needs hsupp; to be usable on the reverse path
-- we want to presume u ≤ v so that we can argue by symmetry):
  -- have hpath {u v : Fin n} (p : (pathGraph n).Walk u v) (hp : p.IsPath)
  --     (huv : u ≤ v) (m : ℕ) (hl : m ≤ p.length) :
  --     ∀ k ≤ m, p.getVert k = u + k := by
  --   induction m with
  --   | zero => simp
  --   | succ m ih =>
  --     have hm := p.adj_getVert_succ hl
  --     rw [pathGraph_adj] at hm
  --     cases hm with
  --     | inl hm => grind
  --     | inr hm =>
  --       intro k hk
  --       rw [Nat.le_add_one_iff] at hk
  --       cases hk with
  --       | inl hk => grind
  --       | inr hk =>
  --         subst hk
  --         cases m with
  --         | zero =>
  --           have hn : ¬ p.Nil := by intro hn; cases hn; cases hl
  --           have hsnd := p.adj_snd hn
  --           rw [pathGraph_adj] at hsnd
  --           cases hsnd with
  --           | inl hsnd => rw [hsnd]
  --           | inr hsnd => -- this is the problematic case
  --             have hu : u ∉ p.tail.reverse.support := by
  --               replace hp := hp.support_nodup
  --               rw [← p.cons_support_tail hn, List.nodup_cons] at hp
  --               intro hcontr
  --               rw [p.tail.support_reverse, List.mem_reverse,
  --                p.support_tail_of_not_nil hn, ← p.support_tail_of_not_nil hn] at hcontr
  --               exact hp.left hcontr
  --             have hv : v ∈ p.tail.reverse.support := by simp
  --             have := hsupp p.tail.reverse (by lia) hu v hv
  --             lia
  --         | succ k =>
  --           have hk : p.getVert k = p.getVert (k + 2) := by grind
  --           iterate 2 rw [p.getVert_eq_support_getElem (by lia)] at hk
  --           absurd (p.isPath_iff_injective_get_support.mp hp) hk
  --           lia
-- we start our contradiction
  intro v c hc
  have hn : ¬ c.Nil := by
    intro hn; cases hn
    exact hc.ne_nil rfl
  -- we rewrite via the cycle's tail and its length
  rw [Walk.isCycle_iff_isPath_tail_and_le_length] at hc
  have hl := hc.right
  rw [← c.length_tail_add_one hn] at hl
  have hsnd := c.adj_snd hn
  rw [pathGraph_adj] at hsnd -- the start of the tail is next to the end
  by_cases hord : c.snd ≤ v -- two cases depending on the direction
  · rw [hpath c.tail hc.left hord] at hl -- the start is too far from the end
    lia
  · rw [← c.tail.isPath_reverse_iff] at hc
    rw [← c.tail.length_reverse, hpath c.tail.reverse hc.left (by lia)] at hl
    lia

/-
This was merely my naive first attempt. There is no doubt that there exist better,
more efficient proofs. Nevertheless, I believe it is quite illustrative of working
with graph theory in Lean and the state of the library: there are the basic tools
and the theory around them developed enough to be practical, but due to the nature
of formal theorem proving, actually employing them to translate intuitive proofs
can be quite cumbersome, especially when dealing with explicit walks and similar
(there is also the aspect of needing coercions of everything,
for example to subgraphs).
-/

-- LOG OF APPROACHES TO THE PROBLEM
-- more concise:
lemma pathGraph_acyclic' (n : ℕ) :
    (pathGraph n).IsAcyclic := by
  have hsupp {u v w : Fin n} (p : (pathGraph n).Walk u v)
      (huw : u < w) (hw : w ∉ p.support) :
      v < w := by
    by_contra hvw
    have ⟨d, hd, _⟩ := p.exists_boundary_dart {x | x < w} huw hvw
    -- something already in mathlib
    grind [d.adj, pathGraph_adj, p.dart_snd_mem_support_of_mem_darts hd]
  have hpath {u v : Fin n} (p : (pathGraph n).Walk u v)
      (hp : p.IsPath) :
      p.length = |(v.val : ℤ) - u.val| := by
    wlog huv : u ≤ v with hpath
    · grind [p.isPath_reverse_iff, p.length_reverse]
    induction p with
    | nil => simp
    | cons hw q ih =>
      rename_i u w v
      rw [Walk.cons_isPath_iff] at hp
      rw [Walk.length_cons]
      rw [pathGraph_adj] at hw
      cases hw with
      | inl _ =>
        have : u ≠ v := by grind [q.end_mem_support]
        grind [ih _ _]
      | inr _ => grind [hsupp _]
  intro v c hc
  have hn : ¬ c.Nil := by
    intro hn; cases hn
    exact hc.ne_nil rfl
  rw [Walk.isCycle_iff_isPath_tail_and_le_length] at hc
  have hsnd := c.adj_snd hn
  rw [pathGraph_adj] at hsnd
  grind [c.length_tail_add_one hn, hpath _]

-- attempt #3, based on bridges; most reasonable do far
lemma pathGraph_acyclic'' (n : ℕ) :
    (pathGraph n).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  wlog hle : u < v with h
  · have : u ≠ v := ne_of_adj _ huv
    rw [show s(u, v) = s(v, u) by simp]
    exact h n huv.symm (by lia)
  rw [isBridge_iff]
  intro ⟨w⟩
  have ⟨d, _, _⟩ := w.exists_boundary_dart {x | x < v} hle (lt_irrefl v)
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  rw [pathGraph_adj] at huv hadj
  have : d.fst = u ∧ d.snd = v := by grind
  aesop

#check Walk.IsCycle
-- attempt #4, based on vertex removal and induction
-- we prove that cycles induce cycles separately,
-- because the basic theory regarding iducing walks is missing
lemma length_induce {V : Type u} {G : SimpleGraph V} (s : Set V) {u v : V} (w : G.Walk u v)
    (hw : ∀ x ∈ w.support, x ∈ s) : (w.induce s hw).length = w.length := by
  induction w with
  | nil => rfl
  | cons _ _ ih => simp [ih]
lemma nodup_attachWith {α : Type*} {l : List α} (P : α → Prop) (H : ∀ x ∈ l, P x) :
    (l.attachWith P H).Nodup ↔ l.Nodup := by
  constructor
  · intro hn
    rw [← l.attachWith_map_subtype_val H]
    exact hn.map Subtype.val_injective
  · exact fun hn ↦ (hn.pmap fun _ _ _ _ h ↦ Subtype.mk.inj h)
lemma induce_nil' {V : Type*} {G : SimpleGraph V} (s : Set V) {u v : V} (w : G.Walk u v)
    (hw : ∀ x ∈ w.support, x ∈ s) : (w.induce s hw).Nil ↔ w.Nil := by cases w <;> simp
lemma isCycle_induce {V : Type*} {G : SimpleGraph V} (s : Set V) {v : V} (w : G.Walk v v)
    (hw : ∀ x ∈ w.support, x ∈ s) :
    (w.induce s hw).IsCycle ↔ w.IsCycle := by
  have hnil := induce_nil' s w hw
  constructor
  all_goals
    intro hc
    have hn := (Walk.eq_nil_iff_nil).subst hc.ne_nil
  focus have := hnil.subst hn
  swap; focus have := hnil.symm.subst hn
  all_goals
    rw [Walk.isCycle_iff_isPath_tail_and_le_length, Walk.isPath_def] at hc ⊢
    grind [Walk.support_tail_of_not_nil, Walk.support_induce,
    List.tail_attachWith, nodup_attachWith, length_induce]
lemma pathGraph_acyclic''' (n : ℕ) :
    (pathGraph n).IsAcyclic := by
  induction n with
  | zero => exact IsAcyclic.of_subsingleton
  | succ n ih =>
    let G := (pathGraph (n + 1)).induce {Fin.last n}ᶜ
    have hiso : G ≃g (pathGraph n) :=
      {toFun := fun ⟨m, _⟩ ↦ ⟨m, by grind⟩
       invFun := fun ⟨m, _⟩ ↦ ⟨⟨m, by lia⟩, by grind⟩
       map_rel_iff' := by simp [G, pathGraph_adj]}
    rw [← hiso.isAcyclic_iff] at ih
    intro v c hc
    by_cases hn : Fin.last n ∈ c.support
    · let c' := c.rotate (Fin.last n) hn
      rw [← c.isCycle_rotate hn] at hc
      have hcn : ¬ c'.Nil := by
        rw [← Walk.eq_nil_iff_nil]
        exact hc.ne_nil
      grind [c'.adj_snd hcn, c'.adj_penultimate hcn,
        pathGraph_adj, hc.snd_ne_penultimate]
    · apply ih (c.induce {Fin.last n}ᶜ (by grind))
      rwa [isCycle_induce]

-- Note: inducing walks gives another example of a walk's endpoints making things difficult
-- even to state (and in Lean, it is the theorem statement that are truly important):
-- suppose that we wished to show that the tail of a walk induces a tail
#check induce
#check Walk.induce
-- in the first place, we need that the support of a tail is contained
-- in the support of the whole walk
lemma support_tail {V : Type*} {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    w.tail.support ⊆ w.support := by grind [Walk.tail, Walk.drop_support_eq_support_drop_min]
-- lemma tail_induce {V : Type*} {G : SimpleGraph V} (s : Set V) {u v : V} (w : G.Walk u v)
--     (hw : ∀ x ∈ w.support, x ∈ s) :
--     (w.induce s hw).tail = (w.tail.induce s (fun x hx ↦ hw x (support_tail w hx)))) := sorry
-- but the type does not match because of the endpoints
-- so we need to show that the second point is induced correctly and use Walk.copy
#check Walk.snd
lemma snd_induce {V : Type*} {G : SimpleGraph V} (s : Set V) {u v : V} (w : G.Walk u v)
    (hw : ∀ x ∈ w.support, x ∈ s) : w.snd = (w.induce s hw).snd := by cases w <;> simp
lemma tail_induce {V : Type*} {G : SimpleGraph V} (s : Set V) {u v : V} (w : G.Walk u v)
    (hw : ∀ x ∈ w.support, x ∈ s) : (w.induce s hw).tail =
      (w.tail.induce s (fun x hx ↦ hw x (support_tail w hx))).copy (Subtype.ext (snd_induce s w hw)) rfl :=
  sorry -- but fortunately, we did not need that

/-
It is my belief that if something is simple to prove in natural language,
there should be a framework in Lean to make the formal proof simple as well.
Here are some ideas for some basic things to add based on my experience with
this example:
* deleting an edge from a cycle creates a path
* infinite path graphs
* discrete intermediate value theorem
* explicit form of paths in path graphs
* acyclicity/trees is preserved by deleting/adding leaves
* acyclicity and graph sum
* properties of induced walks
-/
