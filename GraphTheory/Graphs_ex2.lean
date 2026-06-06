-- Jakub : worked-out exercise sheet from Robert Šámal's course
-- https://github.com/robert-samal/lean-class/blob/acdbef196bd87ab73f226a8a9127df515252dd45/Class_materials/Class09/Graphs101.lean
-- (now deleted; many changes to adhere to recent mathlib)
-- I don't know the original author

/-
Graph101.lean
==============

Very first steps with `SimpleGraph` and trees in Lean 4 / mathlib.

Focus:
* basic use of `SimpleGraph`
* path graphs on `Fin n`
* definitions of tree
* “tree = connected + acyclic”
* “tree = unique simple path between any two vertices”

All nontrivial proofs are left as `sorry` for students.

You’ll likely want to compile this with a recent mathlib. If some names
move, update the imports and hints (search with `#find`, Loogle, etc.).
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

open SimpleGraph

namespace Graph101

/-!
## 1. A very small graph by hand

We start with a tiny vertex type and a simple graph on it, just
to see how `SimpleGraph` is structured.
-/

inductive V3
  | a | b | c

open V3

/-- A toy graph on 3 vertices: `a`–`b`–`c` is a path. -/
def G3 : SimpleGraph V3 where
  Adj
    | a, b => True
    | b, a => True
    | b, c => True
    | c, b => True
    | _, _ => False
  symm := by
    intro v w
    cases v <;> cases w <;> decide
  loopless := by
    constructor
    intro v
    cases v <;> decide

/-!
**Exercise 1.1.** (Warmup)

Prove that `a` is adjacent to `b` but not adjacent to `c` in `G3`.
-/

example : G3.Adj a b := by
  -- unfold the definition and simplify
  unfold G3
  decide

example : ¬ G3.Adj a c := by
  -- again, unfold + simp
  unfold G3
  decide

/-!
**Exercise 1.2.**

Show that `G3` has no loops: this is already encoded in the definition
of `SimpleGraph` and enforced by the `loopless` field, but prove
a concrete instance by hand: `¬ G3.Adj a a`.
-/

example : ¬ G3.Adj a a := by
  unfold G3
  decide

/-!
## 2. Path graphs on `Fin n`

For serious work we don’t build graphs by hand — we reuse mathlib’s
constructions. The basic “model” graph is the path `0–1–2–…–(n-1)` on
vertices `Fin n`.

Mathlib calls this `SimpleGraph.pathGraph n : SimpleGraph (Fin n)`.
-/

/-- Path graph on `Fin n`. We give it a short alias `Pn`. -/
def Pn (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.pathGraph n

namespace Pn

-- Jakub : it is necessary to have these instances
-- to prove local finiteness of Pn, so that degree is computable
instance {α : Type*} [Fintype α] [LT α] [DecidableLT α] :
    DecidableRel (CovBy : α → α → Prop) := by
  unfold CovBy
  infer_instance
instance (n : ℕ) : DecidableRel (Pn n).Adj := by
  intro a b
  unfold Pn pathGraph hasse
  infer_instance

/-- A handy abbreviation for degree in `Pn n`. -/
def degree {n : ℕ} (v : Fin n) : ℕ :=
  (Pn n).degree v

/-!
There is a lemma in mathlib (search for it!) that characterizes adjacency
in the path graph:

`(SimpleGraph.pathGraph n).Adj i j ↔ ((i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i)`.

We’ll *use* that, but we won’t hard-code its name here.
Students should find it via `#find _ (SimpleGraph.pathGraph _)` or Loogle.
-/

/-!
**Exercise 2.1.**

Assume `n ≥ 2`. Show that every vertex in `Pn n` has degree at most 2.
(Do not try to prove the sharp bound yet.)

Hint: split into cases:
* `v = 0`
* `v = last` (the vertex with value `n-1`)
* middle vertices.
-/

-- Jakub : no case splitting necessary, probably not intended solution?
example {n : ℕ} (v : Fin n) :
    degree v ≤ 2 := by
  unfold degree SimpleGraph.degree
  let S := {w : Fin n | v.val + 1 = w.val} ∪ {w : Fin n | w.val + 1 = v.val}
  have hneigh : (Pn n).neighborFinset v = S.toFinset := by
    ext w
    unfold neighborFinset neighborSet
    rw [Set.mem_toFinset, Set.mem_toFinset]
    exact pathGraph_adj
  rw [hneigh]
  unfold S
  rw [Set.toFinset_union]
  apply le_trans (Finset.card_union_le _ _)
  apply add_le_add (b := 1) (d := 1)
  all_goals
    rw [Finset.card_le_one_iff]
    grind

/-!
**Exercise 2.2.**

For `n ≥ 2`, show that the endpoints (0 and `n-1`) in `Pn n`
have degree exactly 1.
-/

example {n : ℕ} (hn : 2 ≤ n) :
    degree (⟨0, by lia⟩ : Fin n) = 1 := by
  unfold degree SimpleGraph.degree
  let S := {w : Fin n | 1 = w.val ∨ w.val + 1 = 0}
  have hneigh : (Pn n).neighborFinset ⟨0, by lia⟩ = S.toFinset := by
    ext w
    unfold neighborFinset neighborSet
    rw [Set.mem_toFinset, Set.mem_toFinset]
    exact pathGraph_adj
  rw [hneigh]
  rw [show S.toFinset = {⟨1, by lia⟩} by grind]
  exact Finset.card_singleton ⟨1, _⟩

example {n : ℕ} (hn : 2 ≤ n) :
    degree (⟨n - 1, by lia⟩ : Fin n) = 1 := by
  unfold degree SimpleGraph.degree
  let S := {w : Fin n | n - 1 + 1 = w.val ∨ w.val + 1 = n - 1}
  have hneigh : (Pn n).neighborFinset ⟨n - 1, by lia⟩ = S.toFinset := by
    ext w
    unfold neighborFinset neighborSet
    rw [Set.mem_toFinset, Set.mem_toFinset]
    exact pathGraph_adj
  rw [hneigh]
  rw [show S.toFinset = {⟨n - 2, by lia⟩} by grind]
  exact Finset.card_singleton ⟨n - 2, _⟩

/-!
**Exercise 2.3.** (Connectivity)

Show that `Pn (n+1)` is connected.

Hint:
* Either use the existing lemma `SimpleGraph.pathGraph_connected`,
  or reprove the statement using `Walk`s and induction on `|i - j|`.
-/
lemma Connected (n : ℕ) :
    (Pn (n + 1)).Connected := by
  constructor
  intro u v
  wlog huv : u ≤ v with h
  · symm; grind
  induction hl : v.val - u.val generalizing u v with
  | zero => rw [show u = v by grind]
  | succ k ih =>
    let w : Fin (n + 1) := ⟨u + 1, by grind⟩
    obtain ⟨a⟩ := ih w v (by grind) (by grind)
    have hw : (Pn (n + 1)).Adj u w := by
      unfold Pn
      rw [pathGraph_adj]
      grind
    exact ⟨Walk.cons hw a⟩

end Pn


/-!
## 3. Trees: connected + acyclic

Mathlib has a notion `G.IsTree` for trees, and `G.IsAcyclic` for being
acyclic. There is also a lemma `SimpleGraph.isTree_iff` which says
roughly: “a finite graph is a tree iff it is connected and acyclic”.

Here we first define our own “`IsTree'`” and then prove the equivalence,
*pretending* we don’t know the library lemma. Afterwards one can
compare to the mathlib version.
-/

section Trees_basic

variable {V : Type*} (G : SimpleGraph V)

/-- A naive tree predicate: connected and acyclic. -/
def IsTree' : Prop :=
  G.Connected ∧ G.IsAcyclic

/-!
**Exercise 3.1.**

Show that `G.IsTree` implies `IsTree' G`.

(Hint: there are lemmas in the `Acyclic`/`Connectivity` files that unpack
`IsTree` into connected + acyclic. Search for them; or, as a first pass,
you can assume a lemma of the form
`G.IsTree → G.Connected` and another `G.IsTree → G.IsAcyclic`
and use them.)
-/
lemma IsTree.to_IsTree' :
    G.IsTree → IsTree' G := by
  intro h
  exact ⟨h.connected, h.isAcyclic⟩

/-!
**Exercise 3.2.**

-- Jakub : finiteness is not needed, so I deleted it from the assumptions
Assume `V` is finite. Show that `IsTree' G` implies `G.IsTree`.

Now you’re going the other way: from “connected + acyclic” to “tree”.

Again, there is a mathlib lemma `SimpleGraph.isTree_iff` that does this.
Here we want a hand-rolled proof (maybe only in a special case, and then
later show how to call the library lemma instead).
-/
lemma IsTree'.to_IsTree :
    IsTree' G → G.IsTree := by
  intro h
  constructor
  · exact h.left
  · exact h.right

/-- Optional: combine the two directions into an equivalence. -/
lemma isTree_iff_IsTree' :
    G.IsTree ↔ IsTree' G := by
  constructor
  · intro h
    exact IsTree.to_IsTree' (G := G) h
  · intro h
    exact IsTree'.to_IsTree (G := G) h

end Trees_basic


/-!
## 4. Trees and unique simple paths

Another standard characterization of trees:

> A graph is a tree iff between any two vertices there is a unique
> simple path.

In Lean, “paths” are certain `Walk`s with no repeated vertices, and
“unique” is expressed via `∃! p : G.Walk v w, p.IsPath`.

Mathlib has a lemma `SimpleGraph.isTree_iff_existsUnique_path` that formalizes
exactly this. Here we use the direction “tree ⇒ unique path”.
-/

section UniquePaths

variable {V : Type*} (G : SimpleGraph V)

/-!
**Exercise 4.1.**

Assume `G.IsTree`. Show that for any vertices `v w` there exists a unique
simple path between them.

In Lean-speak: prove that there exists a unique walk from `v` to `w`
which is a path.

There is a mathlib lemma of the form

`G.IsTree → ∀ v w, ∃! p : G.Walk v w, p.IsPath`.

Use that as the engine, but still write the statement and the proof
yourself.
-/
example (hT : G.IsTree) (v w : V) :
    ∃! p : G.Walk v w, p.IsPath :=
  (isTree_iff_existsUnique_path.mp hT).right v w

end UniquePaths


/-!
## 5. Specializing to path graphs: `Pn n` is a tree

Now we put things together for a concrete family:

* show `Pn n` is connected (from above),
* show `Pn n` is acyclic,
* deduce `Pn n` is a tree,
* conclude there is a unique simple path between any two vertices.
-/

section Path_is_tree
variable (n : ℕ)

/-!
**Exercise 5.1.**

Show that `Pn (n+1)` is connected and acyclic.

Connectivity was earlier (Exercise 2.3). For acyclicity, use that a path
graph has no cycles by combinatorial reasoning (no way to return to the
start without repeating a vertex).
-/

lemma Pn_acyclic :
    (Pn (n + 1)).IsAcyclic := by
  have hsupp {u v w : Fin (n + 1)} (p : (Pn (n + 1)).Walk u v) (huw : u < w) (hw : w ∉ p.support) :
      ∀ x ∈ p.support, x < w := by
    induction hl : p.length generalizing u with
    | zero =>
      intro x hx
      rw [Walk.length_eq_zero_iff, Walk.nil_iff_support_eq] at hl
      rw [hl, List.mem_singleton] at hx
      rw [hx]
      exact huw
    | succ k ih =>
      cases p with
      | nil => cases hl
      | cons hy q =>
        intro x hx; rename_i y
        rw [Walk.length_cons, Nat.succ_inj] at hl
        rw [Walk.support_cons, List.mem_cons] at hw hx
        push Not at hw
        rw [Pn, pathGraph_adj] at hy
        cases hx with
        | inl hx => rw [hx]; exact huw
        | inr hx =>
          have hyw : y < w := by
            cases hy with
            | inl hy =>
              rw [lt_iff_le_and_ne]
              use (by lia)
              intro hyw; apply hw.right
              rw [← hyw]
              exact q.start_mem_support
            | inr hy => lia
          exact ih q hyw hw.right hl x hx
  have hpath {u v : Fin (n + 1)} (p : (Pn (n + 1)).Walk u v) (hp : p.IsPath) (huv : u ≤ v) :
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
        rw [Pn, pathGraph_adj] at hw
        have hne : u ≠ v := by
          intro heq; apply hp.right
          rw [heq]
          exact q.end_mem_support
        cases hw with
        | inl hw =>
          rw [ih q hp.left (by lia) hl]
          lia
        | inr hw =>
          have hvu := hsupp q (by lia) hp.right v q.end_mem_support
          lia
  intro v c hc
  have hn : ¬ c.Nil := by
    intro hn; cases hn
    exact hc.ne_nil rfl
  rw [Walk.isCycle_iff_isPath_tail_and_le_length] at hc
  have hl := hc.right
  rw [← c.length_tail_add_one hn] at hl
  have hsnd := c.adj_snd hn
  unfold Pn at hsnd; rw [pathGraph_adj] at hsnd
  by_cases hord : c.snd ≤ v
  · rw [hpath c.tail hc.left hord] at hl
    lia
  · rw [← c.tail.isPath_reverse_iff] at hc
    rw [← c.tail.length_reverse, hpath c.tail.reverse hc.left (by lia)] at hl
    lia

/-!
**Exercise 5.2.**

Conclude that `Pn (n+1)` is a tree (using your `IsTree'` or directly
`SimpleGraph.IsTree`).
-/
lemma Pn_isTree :
  (Pn (n + 1)).IsTree :=
  {connected := Pn.Connected n
   isAcyclic := Pn_acyclic n}

/-!
**Exercise 5.3.**

Show that between any two vertices of `Pn (n+1)` there is a unique
simple path.

This is just an instance of Exercise 4.1 applied to a concrete `G`.
-/
example (v w : Fin (n + 1)) :
    ∃! p : (Pn (n+1)).Walk v w, p.IsPath :=
  (isTree_iff_existsUnique_path.mp (Pn_isTree n)).right v w

end Path_is_tree

end Graph101
