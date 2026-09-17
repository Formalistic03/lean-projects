/-
Copyright (c) 2026 Jakub Štepo. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jakub Štepo
-/
import Mathlib.Combinatorics.Configuration
import Mathlib.Combinatorics.Matroid.Closure

/-!
# Synthetic projective geometry

In this file we introduce synthetic projective geometries and their matroidal structure.

## Main definitions

All names are in the Configuration namespace.
* `ProjectiveGeometry`: A special kind of a configuration where there is a (unique) line
  through each pair of distinct points and where coplanar lines intersect.
* `ProjectiveGeometry.Collinear` : The property that a set lies on a single line.
* `ProjectiveGeometry.IsFlat` : A projective subspace (i.e., a set closed under taking lines).
* `ProjectiveGeometry.closure` : The smallest subspace containing a given set.
* `ProjectiveGeometry.Indep` : The property that a set is projectively independent; no element of
  the set is in the closure of the others.
* `ProjectiveGeomtry.matroid` : The matroid associated with the projective geometry.
-/

namespace Configuration
variable {P L : Type*} [Membership P L]
-- `P` are the points, `L` are the lines

section Definition

/-- The set of points of the given line. -/
def points (l : L) : Set P := {p | p ∈ l}

variable (L)
/-- The collinearity predicate. -/
def Collinear (S : Set P) : Prop := ∃ l : L, S ⊆ points l
variable {L}

variable (P L)
/-- A projective geometry is a nondegenerate configuration in which each pair of distinct points has
  a line through them and for each quadrilateral, if two of its opposite sides intersect, the other
  pair of opposite sides also intersects (Veblen's axiom). -/
class ProjectiveGeometry extends HasLines P L where
  /-- Lines have at least three points. -/
  nontriv_line (l : L) : 3 ≤ (points l).encard
  /-- If the lines p₁p₂ and q₁q₂ intersect, so do the lines p₁q₁ and p₂q₂.
    The formulation is more general, allowing for degenerate cases. -/
  veblen {p₁ p₂ q₁ q₂ r : P} :
      Collinear L {p₁, p₂, r} ∧ Collinear L {q₁, q₂, r} →
      ∃ s : P, Collinear L {p₁, q₁, s} ∧ Collinear L {p₂, q₂, s}
variable {P L}


end Definition



/-- A helper macro for proving collinearity.
  Given the goal Collinear L S and a term t : Collinear L T,
  it attempts to close the goal by proving S = T. -/
macro "col_ext" t:term : tactic =>
  `(tactic| first | exact $t | convert ($t) using 1; aesop)



namespace ProjectiveGeometry

section Definitions
variable (L)

/-- A flat is a set which contains whole each line nontrivially intersecting it. -/
def IsFlat (U : Set P) : Prop := ∀ ⦃l : L⦄, 1 < ((points l) ∩ U).encard → points l ⊆ U

/-- The intersection of all flats containing the given set. -/
def closure (S : Set P) : Set P := ⋂₀ {U : Set P | IsFlat L U ∧ S ⊆ U}

/-- A set is independent if no element is in the closure of the others. -/
def Indep (I : Set P) : Prop := ∀ ⦃i : P⦄, i ∈ I → i ∉ closure L (I \ {i})

end Definitions



section Membership

/-- The construction of a collinear triple. -/
lemma col_triple {p q r : P} {l : L} (hp : p ∈ l) (hq : q ∈ l) (hr : r ∈ l) :
    Collinear L {p, q, r} :=
  ⟨l, fun x hx ↦ by rcases hx with (h | h | h) <;> subst h <;> assumption⟩

/-- The subset of a collinear set is collinear. -/
lemma col_subset {S T : Set P} (hS : Collinear L S) (hT : T ⊆ S) : Collinear L T :=
  have ⟨l, hl⟩ := hS
  ⟨l, subset_trans hT hl⟩

/-- The definition of a flat. -/
lemma isFlat_def {U : Set P} : IsFlat L U ↔ ∀ ⦃l : L⦄, 1 < ((points l) ∩ U).encard → points l ⊆ U :=
  Iff.rfl

/-- Alternative characterisation of flats via collinearity. -/
lemma isFlat_iff {U : Set P} :
    IsFlat L U ↔ ∀ ⦃p q r : P⦄, p ∈ U → q ∈ U → p ≠ q → Collinear L {p, q, r} → r ∈ U := by
  rw [isFlat_def]
  constructor
  · intro hU p q r hp hq hpq hcol
    obtain ⟨l, hlU⟩ := hcol
    have hl : 1 < ((points l) ∩ U).encard := by
      rw [Set.one_lt_encard_iff]
      exact ⟨p, q, ⟨hlU (by tauto), hp⟩, ⟨hlU (by tauto), hq⟩, hpq⟩
    exact hU hl (hlU (by tauto))
  · intro h l hl r hr
    obtain ⟨p, q, ⟨hp, hpU⟩, ⟨hq, hqU⟩, hpq⟩ := Set.one_lt_encard_iff.mp hl
    exact h hpU hqU hpq (col_triple hp hq hr)

/-- A singleton is a flat. -/
lemma isFlat_singleton (p : P) : IsFlat L {p} := by
  refine isFlat_def.mpr fun l hl ↦ (lt_irrefl (1 : ℕ∞) ?_).elim
  calc
    1 < _ := hl
    _ ≤ Set.encard {p} := Set.encard_le_encard Set.inter_subset_right
    _ = 1 := Set.encard_singleton p

/-- The intersection of flats is a flat. -/
lemma isFlat_sInter {S : Set (Set P)} (hS : ∀ U ∈ S, IsFlat L U) : IsFlat L (⋂₀ S) := by
  refine isFlat_def.mpr fun l hl ↦ Set.subset_sInter fun U hU ↦ ?_
  exact
    isFlat_def.mp (hS U hU) <| lt_of_lt_of_le hl <| Set.encard_le_encard
      <| Set.inter_subset_inter_right _ <| Set.sInter_subset_of_mem hU

/-- The definition of closure. -/
lemma closure_def {S : Set P} : closure L S = ⋂₀ {U : Set P | IsFlat L U ∧ S ⊆ U} := rfl

/-- Closure is a superset. -/
lemma subset_closure (S : Set P) : S ⊆ closure L S := by
  rw [closure_def]
  exact Set.subset_sInter (fun U ⟨_, hU⟩ ↦ hU)

/-- The closure of any set is a flat. -/
lemma isFlat_closure (S : Set P) : IsFlat L (closure L S) := by
  rw [closure_def]
  exact isFlat_sInter (fun U ⟨hU, _⟩ ↦ hU)

/-- A flat is closed (equal to its closure). -/
lemma IsFlat.closure {U : Set P} (hU : IsFlat L U) : closure L U = U := by
  rw [Set.Subset.antisymm_iff]
  constructor
  · rw [closure_def]
    exact Set.sInter_subset_of_mem ⟨hU, subset_rfl⟩
  · exact subset_closure U

/-- The closure operator is idempotent. -/
lemma closure_closure (S : Set P) : closure L (closure L S) = closure L S :=
  (isFlat_closure S).closure

/-- The closure operator is monotone. -/
lemma closure_subset_closure {S T : Set P} (h : S ⊆ T) : closure L S ⊆ closure L T := by
  iterate 2 rw [closure_def]
  exact Set.sInter_subset_sInter (fun U ⟨hU, hUS⟩ ↦ ⟨hU, subset_trans h hUS⟩)

/-- Conditions for a flat to be the closure of the given set. -/
lemma closure_eq_of_isFlat {S U : Set P} (hU : IsFlat L U) (hUS : S ⊆ U) (h : U ⊆ closure L S) :
    closure L S = U :=
  Set.Subset.antisymm_iff.mpr ⟨hU.closure ▸ closure_subset_closure hUS, h⟩

/-- The closure of a set is the union of the closures of its finite subsets. -/
lemma closure_finitary (S : Set P) : closure L S = ⋃₀ ((closure L) '' {T ⊆ S | T.Finite}) := by
  apply closure_eq_of_isFlat
  · refine isFlat_iff.mpr fun p₁ p₂ q hp₁ hp₂ hp hcol ↦ ?_
    obtain ⟨_, ⟨T₁, hT₁, hT₁eq⟩, hp₁T₁⟩ := hp₁
    obtain ⟨_, ⟨T₂, hT₂, hT₂eq⟩, hp₂T₂⟩ := hp₂
    -- if we take p₁ from the closure of finite subset T₁ and p₂ from the closure of T₂,
    -- the line p₁p₂ is contained in the closure of T₁ ∪ T₂
    apply Set.mem_sUnion_of_mem (t := closure L (T₁ ∪ T₂))
    · apply isFlat_iff.mp (isFlat_closure (T₁ ∪ T₂)) ?_ ?_ hp hcol
      · exact closure_subset_closure Set.subset_union_left (hT₁eq ▸ hp₁T₁)
      · exact closure_subset_closure Set.subset_union_right (hT₂eq ▸ hp₂T₂)
    · exact
        ⟨_, ⟨Set.union_subset hT₁.left hT₂.left, Set.finite_union.mpr ⟨hT₁.right, hT₂.right⟩⟩, rfl⟩
  · refine fun s hs ↦ Set.mem_sUnion_of_mem ?_ ?_ (t := closure L {s})
    -- each point is in the closure of its singleton
    · exact subset_closure {s} (Set.mem_singleton s)
    · exact ⟨_, ⟨Set.singleton_subset_iff.mpr hs, Set.finite_singleton s⟩, rfl⟩
  · refine Set.sUnion_subset fun C hC ↦ ?_
    obtain ⟨_, ⟨hT, _⟩, heq⟩ := hC
    exact heq ▸ closure_subset_closure hT

/-- The definition of independence. -/
lemma indep_def {I : Set P} : Indep L I ↔ ∀ ⦃i : P⦄, i ∈ I → i ∉ closure L (I \ {i}) := Iff.rfl

/-- The empty set is independent. -/
lemma indep_empty : Indep L ∅ := indep_def.mpr fun _ ↦ False.elim

/-- Any subset of an independent set is independent. -/
lemma Indep.subset {I J : Set P} (hJ : Indep L J) (hIJ : I ⊆ J) : Indep L I := by
  rw [indep_def] at hJ ⊢
  exact fun i hiI hi ↦ hJ (hIJ hiI) <| closure_subset_closure (Set.sdiff_subset_sdiff_left hIJ) hi

/-- If all finite subsets are independent, the whole set is independent. -/
lemma indep_compact (I : Set P) (h : ∀ J ⊆ I, J.Finite → Indep L J) : Indep L I := by
  rw [indep_def]
  by_contra hdep
  push Not at hdep
  obtain ⟨i, hiI, hi⟩ := hdep
  -- for contradiction, some i ∈ I is in the closure of the other elements;
  -- then it is in the closure of a finite subset J, but {i} ∪ J is independent, a contradiction
  rw [closure_finitary, Set.mem_sUnion] at hi
  obtain ⟨_, ⟨J, hJ, heq⟩, hi⟩ :=  hi
  have hJI : insert i J ⊆ I := Set.insert_subset hiI (subset_trans hJ.left Set.sdiff_subset)
  apply h (insert i J) hJI (Set.finite_insert.mpr hJ.right) (J.mem_insert i)
  convert heq ▸ hi
  exact Set.insert_sdiff_self_of_notMem fun hiJ ↦ (hJ.left hiJ).right (Set.mem_singleton i)

end Membership



section Nondegenerate
variable [Nondegenerate P L]

/-- The union of two collinear sets which intersect in at least two points is collinear. -/
lemma col_union {S T : Set P} {p q : P} (hS : Collinear L S) (hT : Collinear L T) (hp : p ∈ S ∩ T)
    (hq : q ∈ S ∩ T) (hpq : p ≠ q) : Collinear L (S ∪ T) := by
  obtain ⟨l, hl⟩ := hS
  obtain ⟨l', hl'⟩ := hT
  obtain (heq | heq) :=
    Nondegenerate.eq_or_eq (L := L) (hl hp.left) (hl hq.left) (hl' hp.right) (hl' hq.right)
  · exact (hpq heq).elim
  · exact ⟨l, Set.union_subset hl (heq ▸ hl')⟩
end Nondegenerate



section HasLines
variable [HasLines P L]

variable (L)
/-- A set with two elements is collinear. -/
lemma col_pair {p q : P} (h : p ≠ q) : Collinear L {p, q} := by
  refine ⟨HasLines.mkLine h, fun x hx ↦ ?_⟩
  cases hx with
  | inl hx => rw [hx]; exact (HasLines.mkLine_ax h).left
  | inr hx => rw [hx]; exact (HasLines.mkLine_ax h).right
variable {L}

end HasLines



section ProjectiveGeometry
variable [ProjectiveGeometry P L]

/-- For a point p outside of the closure of S, the closure of {p} ∪ S consists of the lines
  from p to the closure of S. -/
lemma closure_insert {p : P} {S : Set P} (hS : S.Nonempty) (hp : p ∉ closure L S) :
    closure L (insert p S) = {q : P | ∃ s ∈ closure L S, Collinear L {p, q, s}} := by
  apply closure_eq_of_isFlat
  · rw [isFlat_iff]
    intro q₁ q₂ q₃ ⟨s₁, hs₁, hs₁col⟩ ⟨s₂, hs₂, hs₂col⟩ hq hqcol
    -- suppose that we have s₁, s₂ in the closure of S and q₁, q₂ so that
    -- s₁q₁ and s₂q₂ intersect in p; let q₃ be on q₁q₂
    by_cases hs : s₁ = s₂
    · have hps₁ : p ≠ s₁ := (hp <| · ▸ hs₁)
      -- if s₁ = s₂, all the points p, q₁, q₂, q₃, s₁ lie on a single line
      have hcol : Collinear L {p, q₁, q₂, s₁} :=
        by col_ext (col_union hs₁col hs₂col (by aesop) (by aesop) hps₁)
      use s₁, hs₁
      exact col_subset (col_union hcol hqcol (by aesop) (by aesop) hq) (by grind)
    · obtain ⟨r, hsrcol, hqrcol⟩ :=
        veblen
          ⟨show Collinear L {s₁, q₁, p} by col_ext hs₁col,
          show Collinear L {s₂, q₂, p} by col_ext hs₂col⟩
      -- let r be the intersection of q₁q₂ and s₁s₂
      wlog hs₁r : s₁ ≠ r with h
      · have hsr : ¬ (s₁ = r ∧ s₂ = r) := fun ⟨he₁, he₂⟩ ↦ hs (he₂ ▸ he₁)
        push Not at hsr
        exact
          h hS hp s₂ hs₂ hs₂col s₁ hs₁ hs₁col hq.symm (by col_ext hqcol) (Ne.symm hs)
            r (by col_ext hsrcol) (by col_ext hqrcol) (hsr (of_not_not hs₁r))
      have hqrcol' : Collinear L {q₃, r, q₁} :=
        col_subset (col_union hqcol hqrcol (by tauto) (by aesop) hq) (by grind)
      obtain ⟨s₃, hcol, hs₃⟩ := veblen ⟨hqrcol', show Collinear L {p, s₁, q₁} by col_ext hs₁col⟩
      -- let s₃ be the intersection of pq₃ and s₁r (ps₁ and q₃r intersect in q₁);
      -- then s₃ is in the closure of S (on s₁s₂) and q₃ is on ps₃
      refine ⟨s₃, ?_, by col_ext hcol⟩
      have hsrcol' : Collinear L {s₁, s₂, s₃} :=
        col_subset (col_union hsrcol hs₃ (by aesop) (by aesop) hs₁r) (by grind)
      exact isFlat_iff.mp (isFlat_closure S) hs₁ hs₂ hs (by col_ext hsrcol')
  · apply Set.insert_subset
    · have ⟨s, hs⟩ := hS
      -- for p, we may choose an arbitrary point in S
      have hps : p ≠ s := fun he ↦ hp ((subset_closure S) (he ▸ hs))
      exact ⟨s, (subset_closure S) hs, by col_ext (col_pair L hps)⟩
    · refine fun s hs ↦ ⟨s, (subset_closure S) hs, ?_⟩
      -- each s ∈ S lies on the line ps
      have hps : p ≠ s := fun he ↦ hp ((subset_closure S) (he ▸ hs))
      col_ext (col_pair L hps)
  · intro q ⟨s, hs, hscol⟩
    have hps : p ≠ s := (hp <| · ▸ hs)
    exact
      isFlat_iff.mp
        (isFlat_closure _)
        (subset_closure _ (Set.mem_insert p S))
        (closure_subset_closure (Set.subset_insert p S) hs)
        hps
        (by col_ext hscol)

/-- An independent set may be extended by adding a point outside its closure. -/
lemma Indep.insert {I : Set P} {p : P} (hI : Indep L I) (hp : p ∉ closure L I) :
    Indep L (insert p I) := by
  rw [indep_def] at hI ⊢
  have hpI : p ∉ I := Set.notMem_subset (subset_closure I) hp
  intro q hq
  cases Set.mem_insert_iff.mp hq with
  | inl heq =>
    -- for the point p, we simply use the assumption that it is not in the closure of I
    rw [heq]
    convert hp
    exact Set.insert_sdiff_self_of_notMem hpI
  | inr hqI =>
    -- let q be a point of I and for contradiction,
    -- assume that it is in the closure of {p} ∪ I \ {q}
    have hpq := Membership.mem.ne_of_notMem hqI hpI
    rw [Set.insert_sdiff_of_notMem I (Set.notMem_singleton_iff.mpr hpq.symm)]
    intro hq
    by_cases hn : (I \ {q}).Nonempty
    · apply hp
      -- in this case, q is on some line pi, where i is in the closure of I;
      -- i.e., p is on the line qi, a contradiction (p would be in the closure of I)
      have hp' : p ∉ closure L (I \ {q}) := (hp <| closure_subset_closure Set.sdiff_subset ·)
      rw [closure_insert hn hp'] at hq
      obtain ⟨i, hi, hiq⟩ := hq
      have hn : q ≠ i := (hI hqI <| · ▸ hi)
      exact
        isFlat_iff.mp (isFlat_closure I) (subset_closure I hqI)
          (closure_subset_closure Set.sdiff_subset hi) hn (by col_ext hiq)
    · rw [Set.not_nonempty_iff_eq_empty] at hn
      rw [hn, ← Set.singleton_def, (isFlat_singleton p).closure] at hq
      -- in this case, I = {q} is equal to its closure
      exact hpq (Set.eq_of_mem_singleton hq)

/-- For an independent set I, if {p} ∪ I is not independent, p is in the closure of I. -/
lemma mem_closure_indep_of_not_indep_insert {I : Set P} {p : P} (hI : Indep L I)
    (hp : ¬Indep L (insert p I)) : p ∈ closure L I :=
  of_not_not fun h ↦ hp (hI.insert h)

/-- An independent set is maximal (with respect to inclusion) if and only if its closure is the
  whole of P. -/
lemma Indep.maximal_iff_closure_eq_univ {I : Set P} (hI : Indep L I) :
    Maximal (Indep L) I ↔ closure L I = .univ := by
  rw [Set.eq_univ_iff_forall]
  constructor
  · intro hIm
    by_contra h
    push Not at h
    obtain ⟨p, hp⟩ := h
    exact hp <| subset_closure I <| hIm.mem_of_prop_insert <| hI.insert hp
  · intro h
    by_contra hIm
    obtain ⟨p, hpI, hp⟩ := Set.exists_insert_of_not_maximal (fun _ _ ↦ Indep.subset) hI hIm
    apply hp (I.mem_insert p)
    convert h p
    exact Set.insert_sdiff_self_of_notMem hpI

/-- A non-maximal independent set may be extended by an element of a maximal independent set. -/
lemma indep_aug {I B : Set P} (hI : Indep L I) (hIm : ¬Maximal (Indep L) I)
    (hB : Maximal (Indep L) B) : ∃ b ∈ B \ I, Indep L (insert b I) := by
  rw [hI.maximal_iff_closure_eq_univ] at hIm
  rw [hB.prop.maximal_iff_closure_eq_univ] at hB
  by_contra h
  push Not at h
  -- for contradiction, assume that we cannot augment I by any element of B;
  -- then B lies in the closure of I, but that means that the closure of I is the whole of P
  -- and hence I is maximal, a contradiction
  refine hIm (Set.eq_univ_of_subset ?_ hB)
  rw [← closure_closure I]
  apply closure_subset_closure
  intro b hb
  by_cases hbI : b ∈ I
  · exact subset_closure I hbI
  · exact mem_closure_indep_of_not_indep_insert hI (h b ⟨hb, hbI⟩)

variable (L)
/-- The matroid determined by projective independence in the given projective geometry. -/
def matroid : Matroid P :=
  (IndepMatroid.ofFinitary
    .univ
    (Indep L)
    indep_empty
    (fun _ _ ↦ Indep.subset)
    (fun _ _ ↦ indep_aug)
    indep_compact
    (fun _ _ ↦ Set.subset_univ _)).matroid
variable {L}

end ProjectiveGeometry

end ProjectiveGeometry

end Configuration
