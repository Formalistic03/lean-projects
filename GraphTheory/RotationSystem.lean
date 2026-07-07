/-
Copyright (c) 2026 Jakub Štepo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jakub Štepo
-/
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Planar graphs

In this file we define planar graphs via rotation systems, give an alternative characterisation
of planarity for subgraphs and prove that planarity is preserved under disjoint union.

The design philosophy is to make working with planarity of subgraphs as comvenient as possible.

We also develop the tools enabling us to study the connected components of a subgraph without
the need to refer to its coercion to a graph.

## Main definitions

To simplify working with permutations:
* `Equiv.Perm.InvariantSet` : The proposition that a given permutation fixes a set.

Connectivity of subgraphs:
* `SimpleGraph.Subgraph.Walk` : A walk in the subgraph in terms of the subgraph API.
* `SimpleGraph.Subgraph.Reachable` : Reachability in the subgraph.
* `SimpleGraph.Subgraph.componentSet` : The set of the supports of the connected components of
  the subgraph.

Planarity of graphs:
* `Combinatorics.SimpleGraph.outDartSet` : The set of the darts going out of a vertex.
* `Combinatorics.SimpleGraph.RotationSystem` : Am embedding of the graph into an orientable surface
  described combinatorially in terms of local rotations around each vertex.
* `Combinatorics.SimpleGraph.RotationSystem.Boundary` : The type of faces of the embedding given by
  the rotation system (to be more precise, of facial boundaries).
* `Combinatorics.SimpleGraph.RotationSystem.Boundary.supp` : The set of darts in the boundary
  walk of the given face (its support).
* `Combinatorics.SimpleGraph.RotationSystem.boundarySet` : The set of the facial boundaries of the
  rotation system (as sets of darts).
* `Combinatorics.SimpleGraph.RotationSystem.IsPlanar` : The statement that the embedding given by
  the rotation system is into the sphere, defined via Euler's formula.
* `Combinatorics.SimpleGraph.IsPlanar` : Planarity of a graph; that is, the existence of a planar
  rotation system.

Planarity for subgraphs:
* `Combinatorics.SimpleGraph.Subgraph.dartSet` : The set of the darts of the subgraph.
* `Combinatorics.SimpleGraph.Subgraph.RotationSystem` : A rotation system of the subgraph defined
  globally for the underlying graph, in terms of the subgraph API.
* `Combinatorics.SimpleGraph.Subgraph.IsPlanar` : Planarity of a subgraph given by a subgraph
  rotation system.

## Main results

Justifying our definitions for subgraphs:
* `Combinatorics.SimpleGraph.Subgraph.mem_componentSet_eq` : The support of a connected component
  of a subgraph may be described by the subgraph reachability relation.
* `Combinatorics.SimpleGraph.Subgraph.coe_isPlanar` : Planarity of a subgraph and its coerced graph
  coincide.

Lemmas to express the quantities in Euler's formula:
* `Combinatorics.SimpleGraph.RotationSystem.ncard_boundarySet` : The facial boundaries of a rotation
  system may be counted by their supports.
* `Combinatorics.SimpleGraph.Subgraph.ncard_componentSet` : The connected components of a subgraph
  may be counted by their corresponding vertex sets.
* `Combinatorics.SimpleGraph.Subgraph.RotationSystem.ncard_boundarySet` : The facial boundaries of
  a rotation system may be counted by their supports.

Theorems:
* `Combinatorics.SimpleGraph.componentSet_disj_union` : The component set of a disjoint union of
  subgraphs is the disjoint union of their component sets.
* `Combinatorics.SimpleGraph.isPlanar_disj_union` : The disjoint union of planar subgraphs is
  planar.

-/

/-! ## Lemmas about permutations -/

instance {α β : Type*} (f : α ≃ β) : DecidablePred (· ∈ Set.range f) :=
  fun _ ↦ f.range_eq_univ ▸ inferInstance

universe u

namespace Equiv.Perm

variable {α : Type u} (f : Equiv.Perm α) (s : Set α)

/-- The proposition that a permutation fixes a set.
  Equivalent to Set.BijOn, see Equiv.Perm.invariantSet_iff_bijOn. -/
def InvariantSet : Prop := ∀ ⦃x : α⦄, f x ∈ s ↔ x ∈ s

variable {f s}

lemma InvariantSet.inv (h : f.InvariantSet s) : f⁻¹.InvariantSet s := by
  intro x
  rw [← h]
  simp

lemma invariantSet_iff_bijOn : f.InvariantSet s ↔ Set.BijOn f s s :=
  ⟨fun h ↦
    ⟨fun x hx ↦ h.mpr hx, f.injective.injOn, fun x hx ↦ ⟨f⁻¹ x, h.inv.mpr hx, by simp⟩⟩,
   fun h _ ↦ ⟨fun hx ↦ by convert h.perm_inv.mapsTo hx; simp, fun hx ↦ h.mapsTo hx⟩⟩

lemma invariantSet_one : InvariantSet 1 s := fun _ ↦ Iff.rfl

lemma InvariantSet.zpow (h : f.InvariantSet s) (i : ℤ) : (f ^ i).InvariantSet s := by
  rw [invariantSet_iff_bijOn] at h ⊢
  exact h.perm_zpow i

lemma InvariantSet.compl (h : f.InvariantSet s) : f.InvariantSet sᶜ := by
  rw [invariantSet_iff_bijOn] at h ⊢
  exact h.compl f.bijective

lemma permCongr_eq_extendDomain {β : Type u} (e : α ≃ β) :
    e.permCongr f = f.extendDomain (Equiv.ofInjective e e.injective) := by
  ext x
  have hx := e.range_eq_univ ▸ Set.mem_univ x
  rw [f.extendDomain_apply_subtype _ hx]
  have : e.symm x = (Equiv.ofInjective e e.injective).symm ⟨x, hx⟩ := by
    apply e.injective
    simp [apply_ofInjective_symm]
  simp [this]

end Equiv.Perm

namespace Set

variable {α : Type u} {p : α → Prop} {f : Equiv.Perm α} {s t : Set α}

lemma MapsTo.subtypePerm (hp : ∀ x : α, p (f x) ↔ p x) (h : MapsTo f s t) :
    MapsTo (f.subtypePerm hp) ((↑) ⁻¹' s) ((↑) ⁻¹' t) :=
  fun _ hx ↦ h hx

lemma SurjOn.subtypePerm (hp : ∀ x : α, p (f x) ↔ p x) (h : SurjOn f s t) :
    SurjOn (f.subtypePerm hp) ((↑) ⁻¹' s) ((↑) ⁻¹' t) := by
  intro x hx
  have ⟨y, hy, heq⟩ := h hx
  exact ⟨⟨y, (hp y).mp (heq ▸ x.prop)⟩, hy, Subtype.ext heq⟩

lemma BijOn.subtypePerm (hp : ∀ x : α, p (f x) ↔ p x) (h : BijOn f s t) :
    BijOn (f.subtypePerm hp) ((↑) ⁻¹' s) ((↑) ⁻¹' t) :=
  ⟨h.mapsTo.subtypePerm hp, (f.subtypePerm hp).injective.injOn, h.surjOn.subtypePerm hp⟩

lemma EqOn.inv_of_invariantSet {g : Equiv.Perm α} (heq : s.EqOn f g) (h : f.InvariantSet s) :
    s.EqOn (f⁻¹ : Equiv.Perm α) g⁻¹.toFun := by
  intro x hx
  calc
    _ = g⁻¹ (g (f⁻¹ x)) := by simp
    _ = g⁻¹ (f (f⁻¹ x)) := by rw [heq (h.inv.mpr hx)]
    _ = _ := by simp

lemma EqOn.zpow_of_invariantSet {g : Equiv.Perm α} (heq : s.EqOn f g) (h : f.InvariantSet s)
    (i : ℤ) : s.EqOn (f ^ i) (g ^ i : Equiv.Perm α) := by
  intro _ hx
  induction i with
  | zero => rfl
  | succ _ ih =>
    iterate 2 rw [← mul_self_zpow, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [← ih]
    exact heq <| (h.zpow _).mpr hx
  | pred _ ih =>
    iterate 2 rw [zpow_sub, ← zpow_neg, zpow_mul_comm, zpow_neg_one,
                  Equiv.Perm.coe_mul, Function.comp_apply]
    rw [← ih]
    exact heq.inv_of_invariantSet h ((h.zpow _).mpr hx)

end Set

namespace Equiv.Perm.IsCycleOn

variable {α : Type u} {f g : Equiv.Perm α} {s : Set α}

lemma invariantSet (h : f.IsCycleOn s) : f.InvariantSet s := fun _ ↦ h.apply_mem_iff

lemma of_eqOn (h : f.IsCycleOn s) (heq : s.EqOn f g) : g.IsCycleOn s := by
  use heq.bijOn_iff.mp h.left
  intro _ hx _ hy
  have ⟨_, hi⟩ := h.right hx hy
  exact ⟨_, heq.zpow_of_invariantSet h.invariantSet _ hx ▸ hi⟩

lemma permCongr {β : Type u} (e : α ≃ β) (h : f.IsCycleOn s) : (e.permCongr f).IsCycleOn (e '' s) :=
  permCongr_eq_extendDomain e ▸ h.extendDomain _

lemma subtypePerm' {p : α → Prop} (hp : ∀ x : α, p (f x) ↔ p x) (h : f.IsCycleOn s) :
    (f.subtypePerm hp).IsCycleOn ((↑) ⁻¹' s) := by
  use h.left.subtypePerm hp
  intro _ hx _ hy
  have ⟨i, hi⟩ := h.right hx hy
  exact ⟨i, f.subtypePerm_zpow i hp ▸ Subtype.ext hi⟩

lemma mem_of_sameCycle (h : f.IsCycleOn s) {x y : α} (hx : x ∈ s) (hy : f.SameCycle x y) : y ∈ s :=
  have ⟨_, hi⟩ := hy
  hi ▸ (h.invariantSet.zpow _).mpr hx

end Equiv.Perm.IsCycleOn



namespace SimpleGraph

variable {V : Type u}

namespace ConnectedComponent

lemma mem_supp_of_reachable {G : SimpleGraph V} {C : G.ConnectedComponent}
    {u v : V} (hu : u ∈ C.supp) (h : G.Reachable u v) : v ∈ C.supp :=
  hu ▸ (ConnectedComponent.sound h).symm

end ConnectedComponent


/-! ## Planar graphs -/

section Defs

variable (G : SimpleGraph V)

/-- The set of the darts going out of a vertex. -/
def outDartSet (v : V) : Set G.Dart := {d | d.fst = v}

/-- The involution which reverses each dart. -/
def dartSymmPerm : Equiv.Perm G.Dart := Dart.symm_involutive.toPerm (α := G.Dart)

/-- A rotation system on a graph is an assignment of a cyclic order to the neighbourhood of each
  vertex. These represent the counter-clockwise ordering in an embedding to an orientable surface.

  We implement this by a global permutation on the graph's darts. -/
structure RotationSystem where
  /-- The permutation of darts. -/
  rotation : Equiv.Perm G.Dart
  /-- For each vertex, the rotation is a cycle on the darts going out of it. -/
  isCycleOn_rotation (v : V) : rotation.IsCycleOn (G.outDartSet v)

namespace RotationSystem

variable {G}

lemma ext {R₁ R₂ : G.RotationSystem} (h : R₁.rotation = R₂.rotation) : R₁ = R₂ := by
  cases R₁
  cases R₂
  simp_all

variable (R : G.RotationSystem)

/-- Given a rotation system (which represents an embedding), the permutation which gives the next
  dart when going along the faces' boundaries counter-clockwise. -/
def faceRotation : Equiv.Perm G.Dart := R.rotation⁻¹ * G.dartSymmPerm

/-- The type of facial boundaries for a given rotation system.

  Note that isolated vertices are ignored because there are no darts going out of them. -/
abbrev Boundary := Quot R.faceRotation.SameCycle

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

instance : Fintype R.Boundary :=
  haveI := R.faceRotation.instDecidableRelSameCycle
  Quotient.fintype (Equiv.Perm.SameCycle.setoid _)

/-- The proposition that the embedding described by the rotation system is into the sphere.

  Expresses Euler's formula V - E + F = C + 1. However, we describe facial boundaries and not faces
  themselves; the number of boundaries is F + C - 1, where C is the number of connected
  components. Furthermore, boundaries around isolated vertices are ignored, so the number counted
  becomes B = F + C - (V - S) - 1, where S is the cardinality of the support. Hence the resulting
  formula is V - E + (B + V - S) = 2 * C. -/
def IsPlanar : Prop :=
  2 * Fintype.card V + Fintype.card R.Boundary =
    G.support.toFinset.card + G.edgeFinset.card + 2 * Fintype.card G.ConnectedComponent

end RotationSystem

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A graph is planar if it has a planar rotation system. -/
def IsPlanar : Prop := ∃ R : G.RotationSystem, R.IsPlanar

end Defs



/-! ### Boundaries -/

namespace RotationSystem

variable {G : SimpleGraph V}

/-- The (unique counter-clockwise) facial boundary the given dart is part of. -/
def boundaryMk (R : G.RotationSystem) (d : G.Dart) : R.Boundary :=
  Quot.mk _ d

namespace Boundary

/-- The set of the darts making up a (counter-clockwise) facial boundary. -/
def supp {R : G.RotationSystem} (B : R.Boundary) : Set G.Dart := {d | R.boundaryMk d = B}

lemma nonempty_supp {R : G.RotationSystem} (B : R.Boundary) : B.supp.Nonempty :=
  have ⟨_, hd⟩ := B.exists_rep
  ⟨_, hd⟩

lemma supp_injective (R : G.RotationSystem) : (supp (R := R)).Injective := by
  intro B₁ B₂ hB
  have ⟨d, hd₁⟩ := B₁.nonempty_supp
  have hd₂ := hB ▸ hd₁
  exact hd₁.symm.trans hd₂

lemma sameCycle_of_mem_supp {R : G.RotationSystem} {B : R.Boundary} {d e : G.Dart}
    (hd : d ∈ B.supp) (he : e ∈ B.supp) : R.faceRotation.SameCycle d e :=
  Quotient.exact (s := Equiv.Perm.SameCycle.setoid R.faceRotation) (hd.trans he.symm)

lemma mem_supp_of_sameCycle {R : G.RotationSystem} {B : R.Boundary} {d e : G.Dart}
    (hd : d ∈ B.supp) (h : R.faceRotation.SameCycle d e) : e ∈ B.supp :=
  hd ▸ (Quot.sound h).symm

lemma isCycleOn_faceRotation_supp {R : G.RotationSystem} (B : R.Boundary) :
    R.faceRotation.IsCycleOn B.supp := by
  constructor
  · rw [← Equiv.Perm.invariantSet_iff_bijOn]
    intro d
    exact
      ⟨fun hd ↦ mem_supp_of_sameCycle hd Equiv.Perm.SameCycle.rfl.apply_left,
       fun hd ↦ mem_supp_of_sameCycle hd Equiv.Perm.SameCycle.rfl.apply_right⟩
  · exact fun _ hd _ he ↦ sameCycle_of_mem_supp hd he

lemma exists_supp_of_isCycleOn {R : G.RotationSystem} (F : Set G.Dart) (hF : F.Nonempty)
    (h : R.faceRotation.IsCycleOn F) : ∃ B : R.Boundary, B.supp = F := by
  obtain ⟨d, hd⟩ := hF
  use R.boundaryMk d
  ext e
  exact
    ⟨fun he ↦ h.mem_of_sameCycle hd (sameCycle_of_mem_supp rfl he),
     fun he ↦ mem_supp_of_sameCycle rfl (h.right hd he)⟩

end Boundary

/-- The set of the boundaries of the rotation system, represented by their supports.

  Defined to be the sets on which the face-rotation is a cycle;
  see Combinatorics.SimpleGraph.RotationSystem.boundarySet_eq_range_dartSet for the equivalence. -/
def boundarySet (R : G.RotationSystem) : Set (Set G.Dart) :=
  {F | F.Nonempty ∧ R.faceRotation.IsCycleOn F}

lemma boundarySet_eq_range_supp (R : G.RotationSystem) :
    R.boundarySet = Set.range (Boundary.supp (R := R)) :=
  Set.ext fun F ↦
    ⟨fun hF ↦ Boundary.exists_supp_of_isCycleOn F hF.left hF.right,
     fun ⟨B, hF⟩ ↦ hF ▸ ⟨B.nonempty_supp, B.isCycleOn_faceRotation_supp⟩⟩

lemma ncard_boundarySet (R : G.RotationSystem) [Fintype R.Boundary] :
    R.boundarySet.ncard = Fintype.card R.Boundary := by
  rw [R.boundarySet_eq_range_supp, ← Set.fintypeCard_eq_ncard,
      Set.card_range_of_injective (Boundary.supp_injective R)]

instance (R : G.RotationSystem) [Finite R.Boundary] : Finite R.boundarySet := by
  rw [boundarySet_eq_range_supp]
  infer_instance

end RotationSystem



namespace Subgraph

variable {V : Type u} {G : SimpleGraph V}

/-! ## Subgraph connectivity -/

section Connectivity

/-- A subgraph version of Combinatorics.SimpleGraph.Walk.

  Like a walk in the underlying graph, but we require that the first vertex be a vertex of the
  subgraph and that the adjacencies be adjacencies of the subgraph. -/
inductive Walk (H : G.Subgraph) : V → V → Type u
  | nil {u : V} (hu : u ∈ H.verts) : H.Walk u u
  | cons {u v w : V} (h : H.Adj u v) (p : H.Walk v w) : H.Walk u w
  deriving DecidableEq

namespace Walk

lemma start_mem_verts {H : G.Subgraph} {u v : V} :
    ∀ _ : H.Walk u v, u ∈ H.verts
  | nil hu => hu
  | cons h _ => H.edge_vert h

lemma end_mem_verts {H : G.Subgraph} {u v : V} :
    ∀ _ : H.Walk u v, v ∈ H.verts
  | nil hu => hu
  | cons _ p => p.end_mem_verts

/-- The coercion of a walk in the subgraph to the corresponding walk in the coerced graph. -/
def coe {H : G.Subgraph} {u v : V} :
    ∀ w : H.Walk u v, H.coe.Walk ⟨u, w.start_mem_verts⟩ ⟨v, w.end_mem_verts⟩
  | nil _ => SimpleGraph.Walk.nil
  | cons h p => p.coe.cons (coe_adj _ _ _ ▸ h)

/-- A walk in the coerced graph naturally gives a walk in the subgraph. -/
def ofCoe {H : G.Subgraph} {u v : H.verts} :
    ∀ _ : H.coe.Walk u v, H.Walk ↑u ↑v
  | @SimpleGraph.Walk.nil _ _ u => nil u.prop
  | SimpleGraph.Walk.cons h p => (ofCoe p).cons h

end Walk

/-- Reachability in the subgraph stated in terms of subgraph walks. -/
def Reachable (H : G.Subgraph) (u v : V) : Prop := Nonempty (H.Walk u v)

/-- The set of connected components of the subgraph, represented by their supports. -/
def componentSet (H : G.Subgraph) : Set (Set V) :=
  Set.range ((Set.image (↑)) ∘ (ConnectedComponent.supp (G := H.coe)))

lemma ncard_componentSet (H : G.Subgraph) [Fintype H.coe.ConnectedComponent] :
    H.componentSet.ncard = Fintype.card H.coe.ConnectedComponent := by
  rw [componentSet, ← Set.fintypeCard_eq_ncard,
      Set.card_range_of_injective ?_]
  exact
    Subtype.val_injective.image_injective.comp ConnectedComponent.supp_injective

instance (H : G.Subgraph) [Finite H.coe.ConnectedComponent] : Finite H.componentSet := by
  unfold componentSet
  infer_instance

lemma nonempty_mem_componentSet {H : G.Subgraph} {C : Set V} (hC : C ∈ H.componentSet) :
    C.Nonempty :=
  have ⟨C', heq⟩ := hC
  have ⟨v, hv⟩ := C'.nonempty_supp
  ⟨↑v, heq ▸ ⟨v, hv, rfl⟩⟩

/-- The support of the component containing the given vertex, as a set of the vertices
  of the underlying graph. -/
def componentSetMemMk {H : G.Subgraph} {v : V} (hv : v ∈ H.verts) : Set V :=
  (↑) '' (H.coe.connectedComponentMk ⟨v, hv⟩).supp

lemma componentSetMemMk_mem {H : G.Subgraph} {v : V} (hv : v ∈ H.verts) :
    H.componentSetMemMk hv ∈ H.componentSet :=
  ⟨H.coe.connectedComponentMk ⟨v, hv⟩, rfl⟩

lemma mem_componentSetMemMk {H : G.Subgraph} {v : V} (hv : v ∈ H.verts) :
    v ∈ componentSetMemMk hv :=
  ⟨⟨v, hv⟩, rfl, rfl⟩

lemma mem_componentSet_sub_verts {H : G.Subgraph} {C : Set V} (hC : C ∈ H.componentSet) :
    C ⊆ H.verts := by
  obtain ⟨C', heq⟩ := hC
  rw [← heq]
  intro _ ⟨u, _, hequ⟩
  exact hequ ▸ u.prop

/-- The support of a connected component is precisely the set of vertices reachable
  (in the subgraph sense) from a given member of the support. -/
lemma mem_componentSet_eq {H : G.Subgraph} {v : V} {C : Set V} (hC : C ∈ H.componentSet)
    (hv : v ∈ C) : C = {u | H.Reachable v u} := by
  obtain ⟨C', heq⟩ := hC
  rw [← heq] at hv ⊢
  obtain ⟨v', hv', heqv⟩ := hv
  have heqv : v' = ⟨v, heqv ▸ v'.prop⟩ := Subtype.ext heqv
  ext u
  constructor
  · intro ⟨_, hu, hequ⟩
    have ⟨w⟩ := C'.reachable_of_mem_supp (heqv ▸ hv') hu
    exact hequ ▸ ⟨Walk.ofCoe w⟩
  · intro ⟨w⟩
    use ⟨u, w.end_mem_verts⟩, C'.mem_supp_of_reachable (heqv ▸ hv') ⟨w.coe⟩

lemma componentSetMemMk_eq {H : G.Subgraph} {v : V} (hv : v ∈ H.verts) :
    componentSetMemMk hv = {u | H.Reachable v u} :=
  mem_componentSet_eq (componentSetMemMk_mem hv) (mem_componentSetMemMk hv)

lemma mem_componentSet_eq_componentSetMemMk {H : G.Subgraph} {C : Set V} (hC : C ∈ H.componentSet)
    {v : V} (hv : v ∈ C) : C = componentSetMemMk (mem_componentSet_sub_verts hC hv) :=
  (mem_componentSet_eq hC hv).trans (componentSetMemMk_eq _).symm

end Connectivity



/-! ## Planar subgraphs -/

section Defs

variable (H : G.Subgraph)

/-- The natural bijection between the support of a subgraph and the support of its coercion
  to a graph. -/
def coeSupportEquiv : H.coe.support ≃ H.support where
  toFun v := ⟨↑v.val, match v.prop with | .intro u hu => ⟨↑u, hu⟩⟩
  invFun v :=
    ⟨⟨↑v, match v.prop with | .intro _ hu => H.edge_vert hu⟩,
     match v.prop with | .intro u hu => ⟨⟨u, H.edge_vert hu.symm⟩, hu⟩⟩

def edgeFinset [Fintype H.edgeSet] := H.edgeSet.toFinset

/-- The set of the darts of the subgraph (as a set of the darts of the underlying graph). -/
def dartSet : Set G.Dart := {d | H.Adj d.fst d.snd}

instance [DecidableRel H.Adj] : DecidablePred (· ∈ H.dartSet) :=
  inferInstanceAs <| DecidablePred (· ∈ {d : G.Dart | H.Adj d.fst d.snd})

/-- The natural bijection between the dart set of a subgraph and the darts of its coercion
  to a graph. -/
def coeDartEquiv : H.coe.Dart ≃ H.dartSet where
  toFun d := ⟨Dart.mk (d.fst, d.snd) (H.adj_sub d.adj), d.adj⟩
  invFun d := Dart.mk (⟨d.val.fst, H.edge_vert d.prop⟩, ⟨d.val.snd, H.edge_vert d.prop.symm⟩) d.prop

/-- The set of the darts going out of a vertex (as a set of the darts of the underlying graph). -/
def outDartSet (v : V) : Set G.Dart := {d | H.Adj d.fst d.snd ∧ d.fst = v}

lemma outDartSet_of_not_mem_verts {H : G.Subgraph} {v : V} (hv : v ∉ H.verts) :
    H.outDartSet v = ∅ :=
  Set.subset_empty_iff.mp fun _ ⟨hd, hdv⟩ ↦ hv (hdv ▸ H.edge_vert hd)

/-- A rotation system on the subgraph defined by a permutation on all of the underlying graph's
  darts. -/
structure RotationSystem where
  /-- The permutation of the darts whose restriction on the darts of the subgraph gives
    the rotation system. -/
  rotation : Equiv.Perm G.Dart
  /-- For each vertex of the subgraph, the rotation is a cycle on the subgraph's darts
    going out of it. -/
  isCycleOn_rotation {v : V} (hv : v ∈ H.verts) : rotation.IsCycleOn (H.outDartSet v)
  /-- The rotation fixes all the darts not in the subgraph (for convenience). -/
  eqOn_rest_rotation_one : H.dartSetᶜ.EqOn rotation (1 : Equiv.Perm G.Dart)

namespace RotationSystem

variable {H}
variable (R : H.RotationSystem)

lemma invariantSet_dartSet : R.rotation.InvariantSet H.dartSet := by
  intro d
  constructor
  focus let d := R.rotation d
  all_goals
    intro hd
    replace hd : d ∈ H.outDartSet d.fst := ⟨hd, rfl⟩
    have hinv := (R.isCycleOn_rotation (H.edge_vert hd.left)).invariantSet
  · exact (hinv.mp hd).left
  · exact (hinv.mpr hd).left

/-- A rotation system on a subgraph naturally gives a rotation system on its coercion to a graph
  (by restriction). -/
def coe : H.coe.RotationSystem where
  rotation := H.coeDartEquiv.symm.permCongr (R.rotation.subtypePerm R.invariantSet_dartSet)
  isCycleOn_rotation v := by
    convert
      ((R.isCycleOn_rotation v.prop).subtypePerm' R.invariantSet_dartSet).permCongr <|
        H.coeDartEquiv.symm
    ext
    exact
      ⟨fun hd ↦ ⟨H.coeDartEquiv _, ⟨(H.coeDartEquiv _).prop, Subtype.mk.inj hd⟩, rfl⟩,
       fun ⟨_, hd, heq⟩ ↦ heq ▸ Subtype.ext hd.right⟩

instance [Fintype H.verts] [DecidableRel H.Adj] : Fintype H.support :=
  Fintype.ofEquiv _ H.coeSupportEquiv

variable [DecidableEq V] [Fintype H.verts] [DecidableRel H.Adj]

instance : Fintype H.edgeSet :=
  H.image_coe_edgeSet_coe ▸ Set.fintypeImage _ _

/-- Planarity of rotation systems for subgraphs, via Euler's formula.

  Note that the number of connected components uses the coercion of the subgraph, and the number
  of boundaries the coercion of the rotation system.
  This is amended by Combinatorics.SimpleGraph.Subgraph.ncard_componentSet and
  Combinatorics.SimpleGraph.Subgraph.RotationSystem.ncard_boundarySet, respectively, which allow
  one to work purely with the subgraph. -/
def IsPlanar (R : H.RotationSystem) : Prop :=
  2 * H.verts.toFinset.card + Fintype.card R.coe.Boundary =
    H.support.toFinset.card +  H.edgeFinset.card + 2 * Fintype.card H.coe.ConnectedComponent

end RotationSystem

/-- Planarity for subgraphs as the existence of a planar (subgraph) rotation system. -/
def IsPlanar [DecidableEq V] [Fintype H.verts] [DecidableRel H.Adj] : Prop :=
  ∃ R : H.RotationSystem, R.IsPlanar

end Defs



variable {V : Type u} {G : SimpleGraph V}

/-- A rotation system on the subgraph's coercion to a graph naturally gives a rotation system on
  the subgraph (by extension by identity). -/
def RotationSystem.ofCoe {H : G.Subgraph} [DecidableRel H.Adj]
    (R : H.coe.RotationSystem) : H.RotationSystem where
  rotation := R.rotation.extendDomain H.coeDartEquiv
  isCycleOn_rotation hv := by
   convert (R.isCycleOn_rotation ⟨_, hv⟩).extendDomain H.coeDartEquiv
   ext
   exact
    ⟨fun ⟨hd, hv⟩ ↦ ⟨H.coeDartEquiv.symm ⟨_, hd⟩, Subtype.ext hv, rfl⟩,
     fun ⟨d, hd, heq⟩ ↦ ⟨heq ▸ d.adj, heq ▸ Subtype.mk.inj hd⟩⟩
  eqOn_rest_rotation_one := fun _ hd ↦ R.rotation.extendDomain_apply_not_subtype _ hd

lemma RotationSystem.coe_ofCoe {H : G.Subgraph} [DecidableRel H.Adj]
    (R : H.coe.RotationSystem) : (RotationSystem.ofCoe R).coe = R := by
  unfold coe ofCoe
  refine RotationSystem.ext (Equiv.Perm.ext fun d ↦ ?_)
  simp

/-- For a subgraph, planarity is equivalent to the planarity of its coercion to a graph. -/
theorem coe_isPlanar (H : G.Subgraph) [Fintype H.verts] [DecidableEq V] [DecidableRel H.Adj] :
    H.coe.IsPlanar ↔ H.IsPlanar := by
  constructor
  · intro ⟨R, hR⟩
    use RotationSystem.ofCoe R
    unfold RotationSystem.IsPlanar edgeFinset
    unfold SimpleGraph.RotationSystem.IsPlanar SimpleGraph.edgeFinset at hR
    rw [Set.toFinset_card, ← Set.ncard_eq_toFinset_card'] at hR
    rwa [Set.toFinset_card, Set.toFinset_card, ← Fintype.card_congr H.coeSupportEquiv,
        ← Set.ncard_eq_toFinset_card', ← image_coe_edgeSet_coe,
        Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective),
        RotationSystem.coe_ofCoe]
  · intro ⟨R, hR⟩
    use R.coe
    unfold RotationSystem.IsPlanar edgeFinset at hR
    unfold SimpleGraph.RotationSystem.IsPlanar SimpleGraph.edgeFinset
    rw [Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
    rwa [Set.toFinset_card, Set.toFinset_card, ← Fintype.card_congr H.coeSupportEquiv,
        ← Set.ncard_eq_toFinset_card', ← image_coe_edgeSet_coe,
        Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)] at hR

lemma dartSet_symm (H : G.Subgraph) (d : G.Dart) : d.symm ∈ H.dartSet ↔ d ∈ H.dartSet :=
  ⟨H.adj_symm, H.adj_symm⟩

/-- The involution which reverses each dart of the subgraph and fixes the other darts. -/
def dartSetSymmPerm (H : G.Subgraph) [DecidableRel H.Adj] : Equiv.Perm G.Dart :=
  H.coe.dartSymmPerm.extendDomain H.coeDartEquiv

lemma dartSetSymmPerm_apply_mem_dartSet (H : G.Subgraph) [DecidableRel H.Adj] {d : G.Dart}
    (hd : d ∈ H.dartSet) : H.dartSetSymmPerm d = d.symm :=
  Equiv.Perm.extendDomain_apply_subtype _ _ hd

lemma dartSetSymmPerm_apply_not_mem_dartSet (H : G.Subgraph) [DecidableRel H.Adj] {d : G.Dart}
    (hd : d ∉ H.dartSet) : H.dartSetSymmPerm d = d :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ hd

namespace RotationSystem

variable {H : G.Subgraph} [DecidableRel H.Adj]

/-- The face-rotation of the subgraph rotation system; it fixes all the darts not in the
  subgraph. -/
def faceRotation (R : H.RotationSystem) : Equiv.Perm G.Dart :=
  R.rotation⁻¹ * H.dartSetSymmPerm

lemma faceRotation_invariantSet_dartSet (R : H.RotationSystem) :
    R.faceRotation.InvariantSet H.dartSet := by
  unfold faceRotation Equiv.Perm.InvariantSet
  intro d
  rw [Equiv.Perm.coe_mul, Function.comp_apply, R.invariantSet_dartSet.inv]
  by_cases hd : d ∈ H.dartSet
  · rw [H.dartSetSymmPerm_apply_mem_dartSet hd]; exact H.dartSet_symm _
  · rw [H.dartSetSymmPerm_apply_not_mem_dartSet hd]

lemma coe_faceRotation (R : H.RotationSystem) :
    R.coe.faceRotation = H.coeDartEquiv.symm.permCongr
      (R.faceRotation.subtypePerm R.faceRotation_invariantSet_dartSet) := by
  unfold faceRotation dartSetSymmPerm
  refine Equiv.Perm.ext fun d ↦ ?_
  rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.Perm.subtypePerm_apply]
  conv_rhs =>
    enter [2, 1]
    rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.extendDomain_apply_image]
  rfl

lemma faceRotation_of_coe (R : H.RotationSystem) :
    R.faceRotation = R.coe.faceRotation.extendDomain H.coeDartEquiv := by
  unfold faceRotation dartSetSymmPerm
  refine Equiv.Perm.ext fun d ↦ ?_
  rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_inv, Function.comp_apply]
  by_cases hd : d ∈ H.dartSet
  · iterate 2 rw [Equiv.Perm.extendDomain_apply_subtype _ _ hd]
    rfl
  · iterate 2 rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hd]
    exact (eqOn_rest_rotation_one R).inv_of_invariantSet R.invariantSet_dartSet.compl hd

/-- The set of the boundaries of the rotation system, represented by their supports
  (as sets of darts of the underlying graph).

  Defined to be the subsets of the subgraph's dart set on which the face rotation is a cycle;
  see Combinatorics.SimpleGraph.Subgraph.RotationSystem.boundarySet_coe for the equivalence. -/
def boundarySet (R : H.RotationSystem) : Set (Set G.Dart) :=
  {F | F.Nonempty ∧ F ⊆ H.dartSet ∧ R.faceRotation.IsCycleOn F}

lemma boundarySet_coe (R : H.RotationSystem) :
    R.boundarySet = (Set.image ((↑) ∘ H.coeDartEquiv)) '' R.coe.boundarySet := by
  ext F
  constructor
  · intro ⟨⟨d, hd⟩, hD, hF⟩
    use H.coeDartEquiv.symm '' ((↑) ⁻¹' F)
    constructor
    · use Set.Nonempty.image _ ⟨⟨d, hD hd⟩, hd⟩
      rw [coe_faceRotation]
      exact (hF.subtypePerm' _).permCongr _
    · rw [← Set.image_comp, Function.comp_assoc, H.coeDartEquiv.self_comp_symm, Function.comp_id,
          Set.image_preimage_eq_iff]
      exact fun e he ↦ ⟨⟨e, hD he⟩, rfl⟩
  · intro ⟨F', ⟨hn, hF'⟩, heq⟩
    rw [← heq]
    have hD : ((↑) ∘ H.coeDartEquiv) '' F' ⊆ H.dartSet :=
      fun _ ⟨d, _, heq⟩ ↦ heq ▸ (H.coeDartEquiv d).prop
    use Set.Nonempty.image _ hn, hD
    rw [R.faceRotation_of_coe]
    exact hF'.extendDomain _

lemma ncard_boundarySet (R : H.RotationSystem) [Fintype R.coe.Boundary] :
    R.boundarySet.ncard = Fintype.card R.coe.Boundary := by
  rw [boundarySet_coe, Set.ncard_image_of_injective _ ?_,
      SimpleGraph.RotationSystem.ncard_boundarySet]
  exact (Subtype.val_injective.comp H.coeDartEquiv.injective).image_injective

instance (R : H.RotationSystem) [Finite R.coe.Boundary] : Finite R.boundarySet := by
  rw [boundarySet_coe]
  infer_instance

end RotationSystem



section Le

variable {H H' : G.Subgraph}

lemma dartSet_mono (hle : H ≤ H') : H.dartSet ⊆ H'.dartSet := fun _ hd ↦ hle.right hd

def Walk.toGe (hle : H ≤ H') {u v : V} :
    ∀ _ : H.Walk u v, H'.Walk u v
  | nil hu => nil (verts_mono hle hu)
  | cons h p => (p.toGe hle).cons (hle.right h)

lemma reachable_mono (hle : H ≤ H') {u v : V} :
    H.Reachable u v → H'.Reachable u v :=
  fun ⟨w⟩ ↦ ⟨w.toGe hle⟩

lemma sub_componentSetMemMk_of_le (hle : H ≤ H') {v : V}
    (hv : v ∈ H.verts) : H.componentSetMemMk hv ⊆
      H'.componentSetMemMk (verts_mono hle hv) := by
  rw [componentSetMemMk_eq, componentSetMemMk_eq]
  exact fun _ ↦ reachable_mono hle

end Le



section Sup

variable {G₁ G₂ : G.Subgraph}

instance [DecidableEq V] [Fintype G₁.verts] [Fintype G₂.verts] :
    Fintype (G₁ ⊔ G₂).verts :=
  inferInstanceAs <| Fintype <| Set.Elem (G₁.verts ∪ G₂.verts)

instance [DecidableRel G₁.Adj] [DecidableRel G₂.Adj] :
    DecidableRel (G₁ ⊔ G₂).Adj :=
  fun _ _ ↦ decidable_of_iff' _ sup_adj

lemma sup_comm : G₁ ⊔ G₂ = G₂ ⊔ G₁ := by grind only

lemma support_sup : (G₁ ⊔ G₂).support = G₁.support ∪ G₂.support :=
  Set.ext fun _ ↦ exists_or

lemma dartSet_sup : (G₁ ⊔ G₂).dartSet = G₁.dartSet ∪ G₂.dartSet := rfl

lemma outDartSet_sup (v : V) : (G₁ ⊔ G₂).outDartSet v = (G₁.outDartSet v) ∪ (G₂.outDartSet v) :=
  Set.ext fun _ ↦ or_and_right

end Sup

end Subgraph



/-! ## Disjoint union of subgraphs -/

open Subgraph Walk

variable {V : Type u} {G : SimpleGraph V} {G₁ G₂ : G.Subgraph}

/-- A walk in the disjoint union of two subgraphs is a walk in one of them. -/
def Subgraph.Walk.ofDisjUnion (hdisj : Disjoint G₁.verts G₂.verts) {u v : V} (hu : u ∈ G₁.verts) :
    ∀ _ : (G₁ ⊔ G₂).Walk u v, G₁.Walk u v
  | nil _ => nil hu
  | @cons _ _ _ _ v _ h p =>
    have ⟨hv, h⟩ : v ∈ G₁.verts ∧ G₁.Adj u v :=
      match (G₁ ⊔ G₂).edge_vert h.symm, h with
      | .inl hv, .inl h => ⟨hv, h⟩
      | .inl hv, .inr h => (Set.disjoint_iff.mp hdisj ⟨hv, G₂.edge_vert h.symm⟩).elim
      | .inr hv, .inl h => (Set.disjoint_iff.mp hdisj ⟨G₁.edge_vert h.symm, hv⟩).elim
      | _, .inr h => (Set.disjoint_iff.mp hdisj ⟨hu, G₂.edge_vert h⟩).elim
    (ofDisjUnion hdisj hv p).cons h

/-- For a vertex in the disjoint union of two subgraphs, its connected component coincides
  with its connected component in one of the two subgraphs. -/
lemma componentSetMemMk_disj_union (hdisj : Disjoint G₁.verts G₂.verts) {v : V}
    (hv : v ∈ G₁.verts) :
    G₁.componentSetMemMk hv = (G₁ ⊔ G₂).componentSetMemMk (verts_mono le_sup_left hv) := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · exact sub_componentSetMemMk_of_le le_sup_left hv
  · intro _ hu
    rw [componentSetMemMk_eq] at hu ⊢
    obtain ⟨w⟩ := hu
    exact ⟨w.ofDisjUnion hdisj hv⟩

/-- The component set of a disjoint union of subgraphs is the disjoint union of their
  component sets. -/
theorem componentSet_disj_union (hdisj : Disjoint G₁.verts G₂.verts) :
    (G₁ ⊔ G₂).componentSet = G₁.componentSet ∪ G₂.componentSet ∧
      Disjoint G₁.componentSet G₂.componentSet := by
  constructor
  · ext C
    constructor
    · intro hC
      have ⟨v, hvC⟩ := nonempty_mem_componentSet hC
      cases mem_componentSet_sub_verts hC hvC with
      | inl hv =>
        left
        convert componentSetMemMk_mem hv
        rw [mem_componentSet_eq_componentSetMemMk hC hvC]
        exact (componentSetMemMk_disj_union hdisj hv).symm
      | inr hv =>
        right
        convert componentSetMemMk_mem hv
        rw [sup_comm] at hC
        rw [mem_componentSet_eq_componentSetMemMk hC hvC]
        exact (componentSetMemMk_disj_union hdisj.symm hv).symm
    · intro hC
      cases hC with
      | inl hC =>
        have ⟨v, hvC⟩ := nonempty_mem_componentSet hC
        have hv := mem_componentSet_sub_verts hC hvC
        convert componentSetMemMk_mem (verts_mono le_sup_left hv)
        rw [mem_componentSet_eq_componentSetMemMk hC hvC]
        exact componentSetMemMk_disj_union hdisj hv
      | inr hC =>
        have ⟨v, hvC⟩ := nonempty_mem_componentSet hC
        have hv := mem_componentSet_sub_verts hC hvC
        rw [sup_comm]
        convert componentSetMemMk_mem (verts_mono le_sup_left hv)
        rw [mem_componentSet_eq_componentSetMemMk hC hvC]
        exact componentSetMemMk_disj_union hdisj.symm hv
  · rw [Set.disjoint_iff]
    intro C ⟨hC₁, hC₂⟩
    have ⟨v, hv⟩ := G₁.nonempty_mem_componentSet hC₁
    have hC :=
      Set.disjoint_of_subset
        (mem_componentSet_sub_verts hC₁) (mem_componentSet_sub_verts hC₂) hdisj
    exact Set.disjoint_iff.mp hC ⟨hv, hv⟩

variable [DecidableEq V]
variable [Fintype G₁.verts] [Fintype G₂.verts] [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]

/-- The disjoint union of planar graphs is planar. -/
theorem isPlanar_disj_union (hdisj : Disjoint G₁.verts G₂.verts)
    (h₁ : G₁.IsPlanar) (h₂ : G₂.IsPlanar) : (G₁ ⊔ G₂).IsPlanar := by
  have hd_disj : Disjoint G₁.dartSet G₂.dartSet := by
    rw [Set.disjoint_iff] at hdisj ⊢
    intro d ⟨hd₁, hd₂⟩
    exact hdisj ⟨G₁.edge_vert hd₁, G₂.edge_vert hd₂⟩
  have hsupp_disj :=
    Set.disjoint_of_subset G₁.support_subset_verts G₂.support_subset_verts hdisj
  have he_disj := (disjoint_verts_iff_disjoint.mp hdisj).edgeSet
  obtain ⟨R₁, hR₁⟩ := h₁
  obtain ⟨R₂, hR₂⟩ := h₂
  have hb_disj : Disjoint R₁.boundarySet R₂.boundarySet := by
    rw [Set.disjoint_iff]
    intro F ⟨hF₁, hF₂⟩
    have ⟨d, hd⟩ := hF₁.left
    have hF := Set.disjoint_of_subset hF₁.right.left hF₂.right.left hd_disj
    exact Set.disjoint_iff.mp hF ⟨hd, hd⟩
  have hcycle {v : V} (hv : v ∈ (G₁ ⊔ G₂).verts) :
      (R₁.rotation * R₂.rotation).IsCycleOn ((G₁ ⊔ G₂).outDartSet v) := by
    cases hv with
    | inl hv =>
      rw [outDartSet_sup, G₂.outDartSet_of_not_mem_verts (Set.disjoint_left.mp hdisj hv),
          Set.union_empty]
      apply (R₁.isCycleOn_rotation hv).of_eqOn
      intro d hd
      simp [R₂.eqOn_rest_rotation_one (Set.disjoint_left.mp hd_disj hd.left)]
    | inr hv =>
      rw [outDartSet_sup, G₁.outDartSet_of_not_mem_verts (Set.disjoint_right.mp hdisj hv),
          Set.empty_union]
      apply (R₂.isCycleOn_rotation hv).of_eqOn
      intro d hd
      rw [← (R₂.isCycleOn_rotation hv).invariantSet] at hd
      simp [R₁.eqOn_rest_rotation_one (Set.disjoint_right.mp hd_disj hd.left)]
  have hid_rest : (G₁ ⊔ G₂).dartSetᶜ.EqOn (R₁.rotation * R₂.rotation) id := by
    rw [dartSet_sup, Set.compl_union]
    intro d ⟨hd₁, hd₂⟩
    simp [R₂.eqOn_rest_rotation_one hd₂, R₁.eqOn_rest_rotation_one hd₁]
  let R : (G₁ ⊔ G₂).RotationSystem := ⟨R₁.rotation * R₂.rotation, hcycle, hid_rest⟩
  use R
  have heq₁ : G₁.dartSet.EqOn R₁.faceRotation R.faceRotation := by
    unfold Subgraph.RotationSystem.faceRotation
    intro d hd
    rw [mul_inv_rev]
    conv => congr <;> repeat rw [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [G₁.dartSetSymmPerm_apply_mem_dartSet hd,
        dartSetSymmPerm_apply_mem_dartSet _ (dartSet_mono le_sup_left hd)]
    rw [← dartSet_symm, ← R₁.invariantSet_dartSet.inv] at hd
    replace hd := Set.disjoint_left.mp hd_disj hd
    rw [R₂.eqOn_rest_rotation_one.inv_of_invariantSet R₂.invariantSet_dartSet.compl hd]
    rfl
  have heq₂ : G₂.dartSet.EqOn R₂.faceRotation R.faceRotation := by
    unfold Subgraph.RotationSystem.faceRotation
    intro d hd
    rw [mul_inv_rev]
    conv => congr <;> repeat rw [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [G₂.dartSetSymmPerm_apply_mem_dartSet hd,
        dartSetSymmPerm_apply_mem_dartSet _ (dartSet_mono le_sup_right hd)]
    rw [← dartSet_symm] at hd
    replace hd := Set.disjoint_right.mp hd_disj hd
    rw [R₁.eqOn_rest_rotation_one.inv_of_invariantSet R₁.invariantSet_dartSet.compl hd]
    rfl
  have hb_union : R.boundarySet = R₁.boundarySet ∪ R₂.boundarySet := by
    ext F
    constructor
    · intro ⟨⟨d, hd⟩, hD, hF⟩
      cases hD hd with
      | inl hd₁ =>
        left
        replace hD : F ⊆ G₁.dartSet := by
          intro e he
          have ⟨_, hi⟩ := hF.right hd he
          rw [← hi, ← heq₁.zpow_of_invariantSet R₁.faceRotation_invariantSet_dartSet _ hd₁]
          exact (R₁.faceRotation_invariantSet_dartSet.zpow _).mpr hd₁
        use ⟨d, hd⟩, hD
        exact hF.of_eqOn (heq₁.symm.mono hD)
      | inr hd₂ =>
        right
        replace hD : F ⊆ G₂.dartSet := by
          intro e he
          have ⟨_, hi⟩ := hF.right hd he
          rw [← hi, ← heq₂.zpow_of_invariantSet R₂.faceRotation_invariantSet_dartSet _ hd₂]
          exact (R₂.faceRotation_invariantSet_dartSet.zpow _).mpr hd₂
        use ⟨d, hd⟩, hD
        exact hF.of_eqOn (heq₂.symm.mono hD)
    · intro hF
      cases hF with
      | inl hF =>
        use hF.left, hF.right.left.trans (dartSet_mono le_sup_left)
        exact hF.right.right.of_eqOn (heq₁.mono hF.right.left)
      | inr hF =>
        use hF.left, hF.right.left.trans (dartSet_mono le_sup_right)
        exact hF.right.right.of_eqOn (heq₂.mono hF.right.left)
  unfold Subgraph.RotationSystem.IsPlanar Subgraph.edgeFinset at hR₁ hR₂ ⊢
  iterate 3 rw [← Set.ncard_eq_toFinset_card'] at hR₁ hR₂ ⊢
  rw [← ncard_componentSet, ← Subgraph.RotationSystem.ncard_boundarySet] at hR₁ hR₂ ⊢
  rw [verts_sup, Set.ncard_union_eq hdisj,
      hb_union, Set.ncard_union_eq hb_disj,
      support_sup, Set.ncard_union_eq hsupp_disj,
      Subgraph.edgeSet_sup, Set.ncard_union_eq he_disj,
      (componentSet_disj_union hdisj).left,
      Set.ncard_union_eq (componentSet_disj_union hdisj).right]
  lia

end SimpleGraph
