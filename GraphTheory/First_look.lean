import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
/-
# A first look at how graph theory is done in Lean

In this file, I summarise my initial experience and findings.

There are multiple different approaches to doing graph theory
in Lean. It appears that the intention is to first flesh out
the theory for undirected simple graphs to figure out how to
formalise different concepts, and then perhaps generalise them
as much as possible in the usual mathlib fashion.
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
From now on, we will only concern ourselves with undirected
simple graphs. This is the only class for which the theory has been
reasonably well developed.
-/
#check SimpleGraph
-- defined by a symmetric, irreflexive adjacency relation
-- graphs over a given vertex type form a complete Boolean algebra
-- (edges), among other we have the subgraph order, complements,
-- complete graphs, union of graphs

#check SimpleGraph.support -- the vertices of non-zero degree
#check SimpleGraph.neighborSet -- the neighbourhood of a vertex
#check SimpleGraph.edgeSet -- the set of the edges
#check Sym2 -- the type of an edge is an unordered pair

-- let us now turn our attention to walks
#check SimpleGraph.Walk -- walk as an inductive type
#check SimpleGraph.Walk.support -- the list of vertices a walk in order
#check SimpleGraph.Walk.IsPath
#check SimpleGraph.Walk.IsCycle

-- connectivity etc:
#check SimpleGraph.Reachable -- there exists a walk between the two vertices
#check SimpleGraph.Connected -- required to be non-empty
#check SimpleGraph.IsAcyclic
#check SimpleGraph.IsTree

-- colouring:
#check SimpleGraph.Coloring -- as a homomorphism into a complete graph
#check RelHom
#check SimpleGraph.Colorable

/-
Other topics that are covered (to some degree) include:
* containment of a copy as an induced subgraph
* adjacency matrix, incidence matrix
* bipartite graphs
* cliques and independent sets
* edge-connectivitx
* matchings (Hall's theorem, Tutte's theorem)
* vertex coverings
* Hamiltonian graphs
* extremal graph theory
* Cayley graphs

So there is a lot of basic theory that has been already built.
On the other hand, some important results an areas are still missing,
such as:
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
In fact, many have been formalised and have open pull requests,
they simply have not met the library's standards yet.
-/

/-
Let us now look at a concrete example of using the API
and the struggles I had with it.
We will study path graphs, which are defined as Hasse diagrams
of the canonical order on Fin n.
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
lemma pathGraph_acyclic (n : ℕ) :
    (pathGraph (n + 1)).IsAcyclic := by
  -- we wish to proceed by contradiction
  -- look at the tail of a cycle, it is a path
  -- suppose this path goes from left to right, then since each next vertex
  -- is either one step left or one step right, all steps must be to the left
  -- (in the construction)
  -- first I proved that a walk contains
  -- all the vertices between its endpoints
  -- stated differently, if a vertex is not in the walk, the whole walk is on one side
  have hsupp {u v w : Fin (n + 1)} (p : (pathGraph (n + 1)).Walk u v)
      (hvw : v < w) (hw : w ∉ p.support) :
      ∀ x ∈ p.support, x < w := by
    -- because the walk contains information about the vertices,
    -- induction on the walk itself complicates things
    -- I found it more natural to do induction on the length
    -- where we let the start vary (this is more natural due to the definition)
    induction hl : p.length generalizing u with
    | zero =>
      intro x hx
      -- here, it is good to use the class Walk.Nil
      -- because Walk.nil requires definitionally equal endpoints
      -- so we would have to first prove that their are equal
      -- and then use Walk.copy
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
  have hpath {u v : Fin (n + 1)} (p : (pathGraph (n + 1)).Walk u v)
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
-- alternative attempt (still needs hsupp due to symmetry):
--   have hpath {u v : Fin (n + 1)} (p : (pathGraph (n + 1)).Walk u v) (hp : p.IsPath)
--       (hdir : u < p.snd) (m : ℕ) (hl : m ≤ p.length) :
--       ∀ k ≤ m, p.getVert k = u + k := by
--     induction m with
--     | zero => simp
--     | succ m ih =>
--       have hm := p.adj_getVert_succ hl
--       rw [pathGraph_adj] at hm
--       cases hm with
--       | inl hm => grind
--       | inr hm =>
--         intro k hk
--         rw [Nat.le_add_one_iff] at hk
--         cases hk with
--         | inl hk => grind
--         | inr hk =>
--           subst hk
--           cases m with
--           | zero => lia
--           | succ k =>
--             have hk : p.getVert k = p.getVert (k + 2) := by grind
--             iterate 2 rw [p.getVert_eq_support_getElem (by lia)] at hk
--             absurd (p.isPath_iff_injective_get_support.mp hp) hk
--             lia
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
(there is also the aspect of needing coercions of everything, for example to subgraphs).
-/

-- better:
lemma pathGraph_acyclic' (n : ℕ) :
    (pathGraph (n + 1)).IsAcyclic := by
  have hsupp {u v w : Fin (n + 1)} (p : (pathGraph (n + 1)).Walk u v)
      (huw : u < w) (hw : w ∉ p.support) :
      v < w := by
    by_contra hvw
    obtain ⟨d, hdp, _⟩ := p.exists_boundary_dart {x | x < w} huw hvw
    have hadj := d.adj
    grind [pathGraph_adj, p.dart_snd_mem_support_of_mem_darts hdp]
  have hpath {u v : Fin (n + 1)} (p : (pathGraph (n + 1)).Walk u v)
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
        have hne : u ≠ v := by grind [q.end_mem_support]
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
