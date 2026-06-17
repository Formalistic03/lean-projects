/-
Copyright (c) 2026 Jakub Štepo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jakub Štepo

In this file, I collected some very simple results which I believe could potientially be added to
mathlib.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Sum

section DeleteDartFrom

namespace SimpleGraph
namespace Walk

variable {V : Type*} {G : SimpleGraph V} {u v x y : V}

lemma snd_dropLast (w : G.Walk u v) (h : 1 < w.length) : w.dropLast.snd = w.snd := by
  match w with
  | nil => rfl
  | cons _ nil => simp at h
  | cons _ (cons ..) => simp

lemma IsCycle.isPath_dropLast {c : G.Walk v v} (hc : c.IsCycle) : c.dropLast.IsPath := by
  rw [isPath_def, support_dropLast hc.not_nil, ← c.tail_support_perm_dropLast_support.nodup_iff,
      ← c.support_tail_of_not_nil hc.not_nil, ← isPath_def]
  exact hc.isPath_tail

lemma append_cancel_left {p : G.Walk u v} {q r : G.Walk v x} (h : p.append q = p.append r) :
    q = r := by
  induction p with
  | nil => exact h
  | cons _ _ ih =>
    injection h
    apply ih
    assumption

variable {d : G.Dart}

lemma eq_snd_of_mem_darts_of_isPath_dropLast {w : G.Walk u v} (hd : d ∈ w.darts)
    (hp : w.dropLast.IsPath) : u = d.fst → w.snd = d.snd := by
  intro hu
  by_cases h : w.darts.getLast (List.ne_nil_of_mem hd) = d
  · grind [darts_getElem_eq_getVert, w.dropLast.getVert_length, length_eq_zero_iff,
           hp.getVert_eq_start_iff_of_not_nil, length_dropLast]
  · wlog hl : w.length > 1
    · grind [List.length_eq_one_iff]
    rw [← w.snd_dropLast hl]
    symm; apply hp.eq_snd_of_mem_edges
    have : d.edge = s(u, d.snd) := by rw [hu]; rfl
    grind [edges, dropLast, darts_take, List.mem_take_iff_getElem, List.mem_iff_getElem]

variable [DecidableEq V]

def takeUntilDart {u v : V} : ∀ (w : G.Walk u v), d ∈ w.darts → G.Walk u d.fst
  | nil, hd => by exfalso; cases hd
  | cons' _ x _ hw w, hd =>
    if h : u = d.fst ∧ x = d.snd then
      nil.copy rfl h.left
    else
      (w.takeUntilDart (by grind [darts_cons])).cons hw

def dropUntilDart {u v : V} : ∀ (w : G.Walk u v), d ∈ w.darts → G.Walk d.snd v
  | nil, hd => by exfalso; cases hd
  | cons' _ x _ hw w, hd =>
    if h : u = d.fst ∧ x = d.snd then
      w.copy h.right rfl
    else
      w.dropUntilDart (by grind [darts_cons])

lemma untilDart_spec {w : G.Walk u v} (hd : d ∈ w.darts) :
    (w.takeUntilDart hd).append
      ((w.dropUntilDart hd).cons d.adj) = w := by
  induction w with | nil => cases hd | cons _ _ ih =>
    cases hd with
    | head => simp!
    | tail =>
      unfold takeUntilDart dropUntilDart
      split_ifs with h
      · have ⟨_, _⟩ := h
        subst_vars
        rfl
      · rw [cons_append, ih]

lemma takeUntilDart_eq_takeUntil_of_isPath_dropLast {w : G.Walk u v} (hd : d ∈ w.darts)
    (hp : w.dropLast.IsPath) : w.takeUntilDart hd =
      w.takeUntil d.fst (w.dart_fst_mem_support_of_mem_darts hd) := by
  induction w with | nil => cases hd | cons _ w ih =>
    have heq := eq_snd_of_mem_darts_of_isPath_dropLast hd hp
    cases hd with
    | head => simp!
    | tail _ hd =>
      unfold takeUntilDart takeUntil
      split_ifs with hux hu
      · subst hu
        rfl
      · tauto
      · simp at heq
        tauto
      · rw [dropLast_cons_of_not_nil _ _ (darts_eq_nil.not.mp (List.ne_nil_of_mem hd)),
            cons_isPath_iff, isPath_copy] at hp
        rw [ih _ hp.left]

/-- Delete a dart from a loop to obtain a walk between the dart's edpoints. -/
def deleteDartFrom (l : G.Walk v v) (hd : d ∈ l.darts) : G.Walk d.snd d.fst :=
  (dropUntilDart l hd).append (takeUntilDart l hd)

theorem support_deleteDartFrom (l : G.Walk v v) (hd : d ∈ l.darts) :
    (l.deleteDartFrom hd).support ~r l.support.tail := by
  unfold deleteDartFrom
  rw [show l.dropUntilDart hd = ((l.dropUntilDart hd).cons d.adj).tail.copy (by simp) rfl by simp]
  rw [support_append, support_copy, support_tail_of_not_nil _ (not_nil_cons)]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, untilDart_spec]

theorem darts_deleteDartFrom (l : G.Walk v v) (hd : d ∈ l.darts) :
    d :: (l.deleteDartFrom hd).darts ~r l.darts := by
  unfold deleteDartFrom
  rw [darts_append, ← List.cons_append, ← darts_cons]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, untilDart_spec]

theorem edges_deleteDartFrom (l : G.Walk v v) (hd : d ∈ l.darts) :
    d.edge :: (l.deleteDartFrom hd).edges ~r l.edges :=
  (l.darts_deleteDartFrom hd).map Dart.edge

theorem length_deleteDartFrom (l : G.Walk v v) (hd : d ∈ l.darts) :
    (l.deleteDartFrom hd).length + 1 = l.length := by
  grind [support_deleteDartFrom, List.IsRotated, List.length_rotate]

theorem IsCircuit.isTrail_deleteDartFrom {c : G.Walk v v} (hd : d ∈ c.darts)
    (hc : c.IsCircuit) : (c.deleteDartFrom hd).IsTrail := by
  grind [IsCircuit, IsTrail, (c.edges_deleteDartFrom hd).perm.nodup_iff]

theorem IsCycle.isPath_deleteDartFrom {c : G.Walk v v} (hd : d ∈ c.darts)
    (hc : c.IsCycle) : (c.deleteDartFrom hd).IsPath := by
  grind [IsCycle, isPath_def, (c.support_deleteDartFrom hd).perm.nodup_iff]

theorem cons_deleteDartFrom_isCycle_eq_rotate (c : G.Walk v v) (hd : d ∈ c.darts)
    (hc : c.IsCycle) : (c.deleteDartFrom hd).cons d.adj =
      (c.rotate d.fst (c.dart_fst_mem_support_of_mem_darts hd)) := by
  unfold deleteDartFrom rotate
  have heq := Eq.refl c
  conv_lhs at heq => rw [← untilDart_spec hd]
  conv_rhs at heq => rw [← c.take_spec (c.dart_fst_mem_support_of_mem_darts hd)]
  rw [takeUntilDart_eq_takeUntil_of_isPath_dropLast hd hc.isPath_dropLast] at heq ⊢
  apply append_cancel_left at heq
  rw [← heq, cons_append]

end Walk
end SimpleGraph

end DeleteDartFrom



section Hasse

instance instDecidableCovByOfFintype {α : Type*} [Fintype α] [LT α] [DecidableLT α] :
    DecidableRel (CovBy : α → α → Prop) := by
  unfold CovBy
  infer_instance

open Classical in
@[implicit_reducible]
noncomputable instance instNonComputableFintypeOfSubsingleton {α : Type*} [Subsingleton α] :
    Fintype α :=
  if h : Nonempty α then
    Fintype.ofSubsingleton h.some
  else
    have := not_nonempty_iff.mp h
    Fintype.ofIsEmpty

namespace SimpleGraph

variable {α : Type*} [LinearOrder α]

@[implicit_reducible]
noncomputable instance instLocallyFiniteHasseOfLinear :
    LocallyFinite (hasse α) := by
  classical
  intro v
  have h₁ : {u | v ⋖ u}.Subsingleton := fun _ h _ h' ↦ h.unique_right h'
  have h₂ : {u | u ⋖ v}.Subsingleton := fun _ h _ h' ↦ h.unique_left h'
  rw [← Set.subsingleton_coe] at h₁ h₂
  rw [show (hasse α).neighborSet v = {u | v ⋖ u} ∪ {u | u ⋖ v} from rfl]
  infer_instance

theorem discrete_intermediate_value_theorem {u v : α} (w : (hasse α).Walk u v) :
    ∀ x : α, u ≤ x ∧ x ≤ v → x ∈ w.support := by
  intro x hx
  by_cases hv : x = v
  · rw [hv]; exact w.end_mem_support
  have ⟨d, hd, hdx⟩ := w.exists_boundary_dart {y | y ≤ x} hx.left (by grind)
  rw [show x = d.fst by grind [not_le, d.adj, hasse, CovBy]]
  exact w.dart_fst_mem_support_of_mem_darts hd

theorem discrete_intermediate_value_theorem_darts {u v : α} (w : (hasse α).Walk u v) :
    ∀ d : (hasse α).Dart, u ≤ d.fst ∧ d.fst < d.snd ∧ d.snd ≤ v → d ∈ w.darts := by
  intro d hd
  have ⟨e, he, _⟩ := w.exists_boundary_dart {x | x ≤ d.fst} hd.left (by grind)
  convert he
  ext <;> grind [d.adj, e.adj, hasse, CovBy, covBy_iff_lt_iff_le_left]

theorem hasse_acyclic_of_linearOrder : (hasse α).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  wlog hle : u < v with h
  · rw [show s(u, v) = s(v, u) by simp]
    exact h huv.symm (lt_of_le_of_ne (le_of_not_gt hle) (ne_of_adj _ huv.symm))
  rw [isBridge_iff]
  intro ⟨w⟩
  have ⟨d, _⟩ := w.exists_boundary_dart {x | x < v} hle (lt_irrefl v)
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  grind [hasse, CovBy, covBy_iff_lt_iff_le_left]

instance instLocallyFinitePathGraphAdj {n : ℕ} : LocallyFinite (pathGraph n) := by
  unfold pathGraph hasse
  infer_instance

theorem pathGraph_isAcyclic (n : ℕ) : (pathGraph n).IsAcyclic := hasse_acyclic_of_linearOrder

theorem pathGraph_isTree (n : ℕ) : (pathGraph (n + 1)).IsTree :=
  ⟨pathGraph_connected n, pathGraph_isAcyclic (n + 1)⟩

end SimpleGraph

end Hasse



section DeleteLeaf

namespace List

lemma nodup_attachWith {α : Type*} {l : List α} (P : α → Prop) (H : ∀ x ∈ l, P x) :
    (l.attachWith P H).Nodup ↔ l.Nodup :=
  ⟨fun hn ↦ (attachWith_map_subtype_val H) ▸ (hn.map Subtype.val_injective),
   fun hn ↦ hn.pmap fun _ _ _ _ h ↦ Subtype.mk.inj h⟩

end List

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

namespace Walk

variable {s : Set V}

lemma nil_induce {w : G.Walk u v} (hw : ∀ x ∈ w.support, x ∈ s) :
    (w.induce s hw).Nil ↔ w.Nil := by cases w <;> simp

lemma length_induce {u v} : ∀ (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s),
    (w.induce s hw).length = w.length
  | nil, _ => rfl
  | cons .., _ => by simp [length_induce]

lemma darts_induce {u v} : ∀ (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s),
    (w.induce s hw).darts = w.darts.attach.map
      (fun ⟨⟨(u, v), _⟩, hd⟩ ↦ Dart.mk
        (⟨u, hw u (w.dart_fst_mem_support_of_mem_darts hd)⟩,
         ⟨v, hw v (w.dart_snd_mem_support_of_mem_darts hd)⟩)
        (by simpa))
  | nil, _ => rfl
  | cons .., _ => by simp [darts_induce]

lemma edges_induce {u v} : ∀ (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s),
    (w.induce s hw).edges = w.edges.attach.map
      fun ⟨e, he⟩ ↦ Sym2.attachWith e fun x hx ↦ hw x (mem_support_of_mem_edges he hx)
  | nil, _ => rfl
  | cons .., _ => by simpa [edges_induce] using (by rfl)

lemma isTrail_induce {w : G.Walk u v} (hw : ∀ x ∈ w.support, x ∈ s) :
    (w.induce s hw).IsTrail ↔ w.IsTrail := by
  rw [isTrail_def, isTrail_def, edges_induce, List.nodup_map_iff ?_, List.nodup_attach]
  intro a b h
  apply Subtype.val_injective
  have := a.val.attachWith_map_subtypeVal fun x hx ↦ hw x (mem_support_of_mem_edges a.prop hx)
  have := b.val.attachWith_map_subtypeVal fun x hx ↦ hw x (mem_support_of_mem_edges b.prop hx)
  simp_all

lemma isPath_induce {p : G.Walk u v} (hw : ∀ x ∈ p.support, x ∈ s) :
    (p.induce s hw).IsPath ↔ p.IsPath := by
  rw [isPath_def, isPath_def, support_induce, List.nodup_attachWith]

lemma isCircuit_induce {c : G.Walk v v} (hc : ∀ x ∈ c.support, x ∈ s) :
    (c.induce s hc).IsCircuit ↔ c.IsCircuit := by
  iterate 2 rw [isCircuit_def, Ne, eq_nil_iff_nil]
  rw [isTrail_induce, nil_induce]

lemma isCycle_induce {c : G.Walk v v} (hc : ∀ x ∈ c.support, x ∈ s) :
    (c.induce s hc).IsCycle ↔ c.IsCycle := by
  iterate 2 rw [isCycle_def, Ne, eq_nil_iff_nil]
  rw [isTrail_induce, nil_induce, support_induce, List.tail_attachWith, List.nodup_attachWith]

end Walk

theorem isAcyclic_iff_isAcyclic_induce_of_leaf (hv : (G.neighborSet v).Subsingleton) :
    G.IsAcyclic ↔ (G.induce {v}ᶜ).IsAcyclic := by
  use (IsAcyclic.induce · {v}ᶜ)
  intro h u c hc
  by_cases hcv : v ∈ c.support
  · classical
      let c' := c.rotate v hcv
      rw [← c.isCycle_rotate hcv] at hc
    apply hc.snd_ne_penultimate
    exact hv (c'.adj_snd hc.not_nil) (c'.adj_penultimate hc.not_nil).symm
  · apply h (c.induce {v}ᶜ (by grind))
    rwa [c.isCycle_induce]

theorem connnected_iff_connected_induce_of_leaf [Fintype (G.neighborSet v)] (hv : G.degree v = 1) :
    G.Connected ↔ (G.induce {v}ᶜ).Connected := by
  use fun h ↦ h.induce_compl_singleton_of_degree_eq_one hv
  have hn := Nonempty.intro v
  refine fun h ↦ ⟨fun x y ↦ ?_⟩
  wlog _ : y ≠ v with hwlog
  · by_cases hxv : x ≠ v
    · convert (hwlog hv hn h v x hxv).symm; simp_all
    · simp_all
  by_cases hxv : x ≠ v
  · exact (h.preconnected ⟨x, by grind⟩ ⟨y, by grind⟩).map (Embedding.induce {v}ᶜ).toHom
  · rw [show x = v from not_not.mp hxv]
    rw [degree_eq_one_iff_existsUnique_adj] at hv
    have ⟨u, hu, _⟩ := hv
    apply hu.reachable.trans
    exact (h.preconnected ⟨u, G.ne_of_adj hu.symm⟩ ⟨y, by grind⟩).map (Embedding.induce {v}ᶜ).toHom

theorem isTree_iff_isTree_induce_of_leaf [Fintype (G.neighborSet v)] (hv : G.degree v = 1) :
    G.IsTree ↔ (G.induce {v}ᶜ).IsTree := by
  have hv' : (G.neighborSet v).Subsingleton := by
    intro _ h _ h'
    rw [← Set.mem_toFinset] at h h'
    grind [degree, Finset.card_eq_one, neighborFinset]
  iterate 2 rw [isTree_iff]
  rw [isAcyclic_iff_isAcyclic_induce_of_leaf hv', connnected_iff_connected_induce_of_leaf hv]

end SimpleGraph

end DeleteLeaf



section AcyclicSum

namespace SimpleGraph

variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}

theorem isAcyclic_sum_iff :
    (G ⊕g H).IsAcyclic ↔ G.IsAcyclic ∧ H.IsAcyclic := by
  use fun h ↦ ⟨IsAcyclic.embedding Embedding.sumInl h, IsAcyclic.embedding Embedding.sumInr h⟩
  intro ⟨hG, hH⟩ x c hc
  cases x with
  | inl =>
    rw [(Embedding.sumInl (H := H)).isoInduceRange.isAcyclic_iff] at hG
    classical have hcU : ∀ x ∈ c.support, x ∈ Set.range .inl :=
      fun x hx ↦ match x with
      | .inl _ => ⟨_, rfl⟩
      | .inr _ => ((not_reachable_sum_inl_inr _ _) ⟨c.takeUntil _ hx⟩).elim
    rw [← c.isCycle_induce hcU] at hc
    exact hG (c.induce (Set.range .inl) hcU) hc
  | inr _ =>
    rw [(Embedding.sumInr (G := G)).isoInduceRange.isAcyclic_iff] at hH
    classical have hcV : ∀ x ∈ c.support, x ∈ Set.range .inr :=
      fun x hx ↦ match x with
      | .inl _ => ((not_reachable_sum_inl_inr _ _) ⟨c.dropUntil _ hx⟩).elim
      | .inr _ => ⟨_, rfl⟩
    rw [← c.isCycle_induce hcV] at hc
    exact hH (c.induce (Set.range .inr) hcV) hc

end SimpleGraph

end AcyclicSum
