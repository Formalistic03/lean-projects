/-
Authors: Jakub Štepo
-/
import Mathlib.Combinatorics.Configuration

/-!
# Desargues's theorem

In this file we introduce synthetic projective geometries, prove some basic results
and then the fact that projective geometries of dimension at least three are Desarguesian.

## Main definitions

* `ProjectiveGeometry`: A special kind of configuration where there is a (unique) line
  through each pair of distrinct points and where coplanar lines intersect.
* `Collinear`: The ternary collinearity relation (all the points lie on a single line).
* `Triangle` : The proposition that three points are not collinear.
* `Coplanar`: The quaternary coplanarity relation (all the points lie in a single plane).
* `NotPlane`: The proposition that the dimesnion of the projective geometry is at least three,
  as a typeclass.
* `Desarguesian`: A projective geometry is Desarguesian if Desargues's theorem holds in it,
  implemented as a typeclass.
  That is, two triangles are in perspective centrally (the lines through the respective
  vertices intersect at a single point) if and only if they are in perspective axially
  (the intersections of the respective sides are collinear).

## Main results

* `instDesarguesianOfNotPlane`: Projective geometries of dimension at least three are Desarguesian.

## Implementation notes

There are two custom tactics defined in this file:
* `col_perm`: A tactic which allows us to work with the Collinear relation regardless
  of the permutation of the three points.
* `copl_perm`: A tactic which allows us to work with the Coplanar relation regardless
  of the permutation of the four points.

-/

open Configuration Nondegenerate HasLines

section Definition
variable (P L : Type*) [Membership P L]
-- `P` are the points, `L` are the lines

/-- A projective geometry is a nondegenerate configuration in which
  each pair of distinct points has a line through them and if a line intersects
  two sides of a triangle, it also intersects the third side (Veblen's axiom). -/
class ProjectiveGeometry extends HasLines P L where
  /-- Lines have at least three points. -/
  nontriv_line : ∀ l : L, ∃ (p₁ p₂ p₃ : P),
      (p₂ ≠ p₃ ∧ p₃ ≠ p₁ ∧ p₁ ≠ p₂) ∧ p₁ ∈ l ∧ p₂ ∈ l ∧ p₃ ∈ l
  /-- For a triangle p₁, p₂, p₃, if a line crosses the line p₂, p₃ in q₁
    and the line p₁, p₃ in q₂, it crosses the line p₁, p₂ in some point q₃.
    The formulation used is more general than the usual one, but holds even
    in the degenerate cases when p₁, p₂, p₃ are collinear or when q₁ coincides
    with one of p₂, p₃ or q₂ coincides with one of p₁, p₃. -/
  veblen : ∀ {p₁ p₂ p₃ q₁ q₂ : P},
      (∃ l : L, q₁ ∈ l ∧ p₂ ∈ l ∧ p₃ ∈ l) ∧ (∃ l : L, p₁ ∈ l ∧ q₂ ∈ l ∧ p₃ ∈ l) →
      ∃ q₃ : P, (∃ l : L, q₁ ∈ l ∧ q₂ ∈ l ∧ q₃ ∈ l) ∧ (∃ l : L, p₁ ∈ l ∧ p₂ ∈ l ∧ q₃ ∈ l)

end Definition



namespace ProjectiveGeometry

section Basic
variable {P L : Type*} [Membership P L]

variable (L)
/-- The ternary collinearity relation of points. -/
def Collinear (p₁ p₂ p₃ : P) : Prop := ∃ l : L, p₁ ∈ l ∧ p₂ ∈ l ∧ p₃ ∈ l

/-- The statement that three points are in general position. -/
abbrev Triangle (p₁ p₂ p₃ : P) : Prop := ¬ Collinear L p₁ p₂ p₃

/-- The quaternary coplanarity relation of points, defined by the fact that
  two lines are coplanar if and only if they intersect.
  Note that if some three of the points are collinear, it holds as well. -/
def Coplanar (p₁ p₂ p₃ p₄ : P) : Prop := ∃ q : P, Collinear L p₁ p₂ q ∧ Collinear L p₃ p₄ q
variable {L}

/-- The statement that two triangles are in perspective from a given point. -/
def InCentralPerspectiveFrom {p₁ p₂ p₃ q₁ q₂ q₃ : P} (c : P)
    (_ : Triangle L p₁ p₂ p₃) (_ : Triangle L q₁ q₂ q₃) : Prop :=
  Collinear L p₁ q₁ c ∧ Collinear L p₂ q₂ c ∧ Collinear L p₃ q₃ c

/-- The relation of two triangles by central perspective.
  We allow for degenerate cases when some two respective sides or vertices
  of the two triangles coincide. -/
def InCentralPerspective {p₁ p₂ p₃ q₁ q₂ q₃ : P}
  (hp : Triangle L p₁ p₂ p₃) (hq : Triangle L q₁ q₂ q₃) : Prop :=
  (∃ c, InCentralPerspectiveFrom c hp hq)

/-- The relation of two triangles by axial perspective.
  We allow for degenerate cases when some two respective sides
  of the triangles coincide. -/
def InAxialPerspective {p₁ p₂ p₃ q₁ q₂ q₃ : P}
  (_ : Triangle L p₁ p₂ p₃) (_ : Triangle L q₁ q₂ q₃) : Prop :=
  ∃ (r₁ r₂ r₃ : P), Collinear L r₁ r₂ r₃
    ∧ (Collinear L r₁ p₂ p₃ ∧ Collinear L r₁ q₂ q₃)
    ∧ (Collinear L p₁ r₂ p₃ ∧ Collinear L q₁ r₂ q₃)
    ∧ (Collinear L p₁ p₂ r₃ ∧ Collinear L q₁ q₂ r₃)

variable (P L)
/-- The class of the projective geometries where there exist four points
  in general position, i.e., the dimension is at least three. -/
class NotPlane : Prop where
  not_plane : ∃ p₁ p₂ p₃ p₄ : P, ¬ Coplanar L p₁ p₂ p₃ p₄

/-- The class of the projective geometries where Desargues's theorem holds.
  That is, two proper triangles are in perspective axially if and only if
  they are in perspective centrally. -/
class Desarguesian : Prop where
  desargues : ∀ {p₁ p₂ p₃ q₁ q₂ q₃ : P} (hp : Triangle L p₁ p₂ p₃) (hq : Triangle L q₁ q₂ q₃),
      InCentralPerspective hp hq ↔ InAxialPerspective hp hq
variable {P L}

/-- The symmetry of collinearity in the first two arguments. -/
lemma col_symm {p₁ p₂ p₃ : P} : Collinear L p₁ p₂ p₃ → Collinear L p₂ p₁ p₃ :=
  fun ⟨l, h₁, h₂, h₃⟩ ↦ ⟨l, h₂, h₁, h₃⟩

/-- The cyclic symmetry of collinearity. -/
lemma col_cyc {p₁ p₂ p₃ : P} : Collinear L p₁ p₂ p₃ → Collinear L p₂ p₃ p₁ :=
  fun ⟨l, h₁, h₂, h₃⟩ ↦ ⟨l, h₂, h₃, h₁⟩

macro "_col_cyc" t:term : tactic =>
  `(tactic | (first
    | exact $t
    | exact col_cyc $t
    | exact $t |> col_cyc |> col_cyc))
/-- A custom tactic which takes a term of type Collinear L p₁ p₂ p₃
  and attempts to close the goal as Collinear L π(p₁) π(p₂) π(p₃)
  for some permutation π. -/
macro "col_perm" t:term : tactic =>
  `(tactic| (first
    | _col_cyc $t
    | _col_cyc col_symm $t))

/-- A custom tactic which takes a term of type Triangle L p₁ p₂ p₃
  and attempts to close the goal as Triangle L π(p₁) π(p₂) π(p₃)
  for some permutation π. -/
macro "triangle_perm" t:term : tactic =>
  `(tactic| (intro c; apply $t; col_perm c))

/-- The symmetry of coplanarity in the first two arguments. -/
lemma copl_symm {p₁ p₂ p₃ p₄ : P} : Coplanar L p₁ p₂ p₃ p₄ → Coplanar L p₂ p₁ p₃ p₄ :=
  fun ⟨q, hq, hq'⟩ ↦ ⟨q, by col_perm hq, hq'⟩

variable [Nondegenerate P L]

/-- If two points are both collinear with the same pair of distinct points,
  all the points lie on the same line. -/
lemma col_trans {p₁ p₂ p₃ p₄ : P} (h : p₂ ≠ p₃) :
    Collinear L p₁ p₂ p₃ → Collinear L p₂ p₃ p₄ → Collinear L p₁ p₂ p₄ := by
  intro ⟨l, h₁, h₂, h₃⟩ ⟨l', h₂', h₃', h₄'⟩
  obtain (hpts | hl) := eq_or_eq h₂' h₃' h₂ h₃
  · contradiction
  · rw [hl] at h₄'
    exact ⟨l, h₁, h₂, h₄'⟩

/-- If three points are all collinear with the same pair of distinct points,
  they are collinear. -/
lemma col_trans3 {p₁ p₂ q₁ q₂ q₃ : P} (h : p₁ ≠ p₂) :
    Collinear L p₁ p₂ q₁ → Collinear L p₁ p₂ q₂ → Collinear L p₁ p₂ q₃ →
    Collinear L q₁ q₂ q₃ := by
  intro h₁ h₂ h₃
  obtain (hn | hn) : q₁ ≠ p₁ ∨ q₁ ≠ p₂ := by grind
  swap
  focus replace h := h.symm
  -- in each case, we first deduce collinearities with two q's
  -- and then put them together thanks to the assumed inequality
  all_goals
    have h₁₂ := col_trans h (by col_perm h₁) (by col_perm h₂)
    have h₁₃ := col_trans h (by col_perm h₁) (by col_perm h₃)
    col_perm col_trans hn (by col_perm h₁₂) h₁₃

/-- The intersection of different lines is unique. -/
lemma eq_of_col {p₁ p₂ p₃ q : P} (h : Triangle L p₁ p₂ p₃) :
    Collinear L p₁ p₂ q → Collinear L p₁ p₃ q → p₁ = q := by
  intro h₂ h₃
  by_contra hn
  have : Collinear L p₁ p₂ p₃ := by
    col_perm col_trans hn (by col_perm h₂) (by col_perm h₃)
  contradiction

omit [Nondegenerate P L]
variable [ProjectiveGeometry P L]

variable (L)
include L in
/-- A projective geometry has at least two points. -/
lemma exists_pt_ne (p : P) : ∃ q : P, p ≠ q := by
  have ⟨l, hl⟩ := exists_line (L := L) p
  have ⟨q, _, _, _, hq, _, _⟩ := nontriv_line (P := P) l
  use q
  grind
variable {L}

/-- One or two points are always collinear. -/
lemma col_refl (p q : P) : Collinear L p p q := by
  by_cases h : p = q
  · have ⟨r, hr⟩ := exists_pt_ne L p
    exact ⟨mkLine hr, (mkLine_ax hr).1, (mkLine_ax hr).1, h.subst (mkLine_ax hr).1⟩
  · exact ⟨mkLine h, (mkLine_ax h).1, (mkLine_ax h).1, (mkLine_ax h).2⟩

/-- Three points in general position are pairwise distinct. -/
lemma ne_of_not_col {p₁ p₂ p₃ : P} :
    Triangle L p₁ p₂ p₃ → p₂ ≠ p₃ ∧ p₃ ≠ p₁ ∧ p₁ ≠ p₂ := by
  intro h
  constructor; swap; constructor
  all_goals
    intro he
    rw [he] at h
    apply h
    col_perm col_refl _ _

variable (L)
/-- For each two points, there is a distinct point collinear with them. -/
lemma exists_col_pt_ne (p₁ p₂ : P) : ∃ q : P, Collinear L p₁ p₂ q ∧ q ≠ p₁ ∧ q ≠ p₂ := by
  by_cases hp : p₁ = p₂
  · have ⟨q, hq⟩ := exists_pt_ne L p₁
    rw [← hp]
    exact ⟨q, col_refl p₁ q, hq.symm, hq.symm⟩
  · have ⟨q₁, q₂, q₃, ⟨hq₂₃, hq₃₁, hq₁₂⟩, hq₁, hq₂, hq₃⟩ :=
      nontriv_line (P := P) (mkLine hp : L)
    -- one of the q's is different from both p's
    obtain (h₁ | h₂ | h₃) :
        (q₁ ≠ p₁ ∧ q₁ ≠ p₂) ∨ (q₂ ≠ p₁ ∧ q₂ ≠ p₂) ∨ (q₃ ≠ p₁ ∧ q₃ ≠ p₂) := by grind
    · exact ⟨q₁, ⟨mkLine hp, (mkLine_ax hp).1, (mkLine_ax hp).2, hq₁⟩, h₁⟩
    · exact ⟨q₂, ⟨mkLine hp, (mkLine_ax hp).1, (mkLine_ax hp).2, hq₂⟩, h₂⟩
    · exact ⟨q₃, ⟨mkLine hp, (mkLine_ax hp).1, (mkLine_ax hp).2, hq₃⟩, h₃⟩
variable {L}

/-- Collinear points are coplanar with any point. -/
lemma copl_of_col {p₁ p₂ p₃ : P} (hc : Collinear L p₁ p₂ p₃) (p₄ : P) :
    Coplanar L p₁ p₂ p₃ p₄ :=
  ⟨p₃, hc, by col_perm col_refl p₃ p₄⟩

/-- Three or less points are always coplanar. -/
lemma copl_refl (p₁ p₃ p₄ : P) : Coplanar L p₁ p₁ p₃ p₄ :=
  copl_of_col (col_refl p₁ p₃) p₄

/-- The cyclic symmetry of coplanarity. -/
lemma copl_cyc {p₁ p₂ p₃ p₄ : P} : Coplanar L p₁ p₂ p₃ p₄ → Coplanar L p₂ p₃ p₄ p₁ := by
  intro ⟨q, hq, hq'⟩
  -- the line p₃, p₂ crosses the triangle p₁, p₄, q; the side p₁, p₄ in r
  have ⟨r, hr, hr'⟩ := veblen ⟨hq', hq⟩
  exact ⟨r, by col_perm hr, by col_perm hr'⟩

lemma copl_cyc3 {p₁ p₂ p₃ p₄ : P} : Coplanar L p₁ p₂ p₃ p₄ → Coplanar L p₂ p₃ p₁ p₄ :=
  fun h ↦ h |> copl_symm |> copl_cyc |> copl_symm |> copl_cyc |> copl_cyc |> copl_cyc

macro "_copl_cyc" t:term : tactic =>
  `(tactic| first
    | exact $t
    | exact copl_cyc $t
    | exact $t |> copl_cyc |> copl_cyc
    | exact $t |> copl_cyc |> copl_cyc |> copl_cyc)
macro "_copl_cyc_cyc3" t:term : tactic =>
  `(tactic| first
     | _copl_cyc $t
     | _copl_cyc (copl_cyc3 $t)
     | _copl_cyc ($t |> copl_cyc3 |> copl_cyc3))
/-- A custom tactic which takes a term of type Coplanar L p₁ p₂ p₃ p₄
  and attempts to close the goal as Coplanar L π(p₁) π(p₂) π(p₃) π(p₄)
  for some permutation π. -/
macro "copl_perm" t:term : tactic =>
  `(tactic| first
    | _copl_cyc_cyc3 $t
    | _copl_cyc_cyc3 (copl_symm $t))

/-- If two points are both coplanar with the same three points in general position,
  all the points lie in the same plane. -/
lemma copl_trans {p₁ p₂ p₃ p₄ p₅ : P} (h : Triangle L p₂ p₃ p₄) :
    Coplanar L p₁ p₂ p₃ p₄ → Coplanar L p₂ p₃ p₄ p₅ → Coplanar L p₁ p₂ p₃ p₅ := by
  intro ⟨q₁, hq₁, hq₁'⟩ h₂
  have ⟨hn, _, _⟩ := ne_of_not_col h
  have ⟨q₂, hq₂, hq₂'⟩ : Coplanar L p₅ p₂ p₃ p₄ := by copl_perm h₂
  -- the line p₃, p₅ crosses the triangle p₂, q₁, q₂; the side p₂, q₁ in q₃
  have ⟨q₃, hq₃, hq₃'⟩ : ∃ q₃, Collinear L p₃ p₅ q₃ ∧ Collinear L p₂ q₁ q₃ :=
    veblen
      ⟨by col_perm col_trans hn (by col_perm hq₁') hq₂',
       by col_perm hq₂⟩
  have hnpq : p₂ ≠ q₁ := by
    intro hpq; apply h
    rw [← hpq] at hq₁'
    col_perm hq₁'
  exact ⟨q₃, col_trans hnpq hq₁ hq₃', hq₃⟩

/-- If three points are all coplanar with the same three points in general position,
  all the points lie in the same plane. -/
lemma copl_trans3 {p₁ p₂ p₃ q₁ q₂ q₃ : P} (h : Triangle L p₁ p₂ p₃) :
    Coplanar L p₁ p₂ p₃ q₁ → Coplanar L p₁ p₂ p₃ q₂ → Coplanar L p₁ p₂ p₃ q₃ →
    Coplanar L p₁ q₁ q₂ q₃ := by
  intro h₁ h₂ h₃
  by_cases hc : Collinear L q₁ p₁ p₂ ∧ Collinear L q₁ p₁ p₃
  · -- in this case, q₁ = p₁
    rw [eq_of_col h (by col_perm hc.1) (by col_perm hc.2)]
    exact copl_refl q₁ q₂ q₃
  · push +distrib Not at hc
    rcases hc with (hnc | hnc)
    swap
    focus replace h : Triangle L p₁ p₃ p₂ := by triangle_perm h
    -- in each case, we first deduce coplanarities with two q's
    -- and then put them together thanks to the assumed non-collinearity
    all_goals
      have h₁₂ := copl_trans h (by copl_perm h₁) (by copl_perm h₂)
      have h₁₃ := copl_trans h (by copl_perm h₁) (by copl_perm h₃)
      copl_perm copl_trans hnc (by copl_perm h₁₂) h₁₃

/-- A line through two points of a plane is wholly contained in that plane. -/
lemma copl_of_col_of_copl {p₁ p₂ p₃ p₄ p₅ : P} (h : p₃ ≠ p₄) :
Coplanar L p₁ p₂ p₃ p₄ → Collinear L p₃ p₄ p₅ → Coplanar L p₁ p₂ p₃ p₅ := by
  intro h₁ h₂
  by_cases h₃ : Collinear L p₂ p₃ p₄
  · -- in this case, p₂, p₃, p₅ are collinear
    copl_perm copl_of_col (col_trans h h₃ h₂) p₁
  · exact copl_trans h₃ h₁ (by copl_perm copl_of_col h₂ p₂)

/-- Three points lying in the intersection of two different planes are collinear. -/
lemma col_of_copl {p₁ p₂ p₃ p₄ q : P} (h : ¬ Coplanar L p₁ p₂ p₃ p₄) :
    Coplanar L p₁ p₂ p₃ q → Coplanar L p₁ p₂ p₄ q → Collinear L p₁ p₂ q := by
  intro h₁ h₂
  by_contra hn; apply h
  copl_perm copl_trans hn (by copl_perm h₁) (by copl_perm h₂)

/-- If there exist four points in general position, then any three points
  in general position may be extended into four. -/
lemma exists_not_copl_of_notPlane [NotPlane P L] {p₁ p₂ p₃ : P} (hp : Triangle L p₁ p₂ p₃) :
    ∃ p₄ : P, ¬ Coplanar L p₁ p₂ p₃ p₄ := by
  have ⟨q₁, q₂, q₃, q₄, hq⟩ := NotPlane.not_plane (P := P) (L := L)
  by_contra hall; push Not at hall; apply hq
  obtain (hnc | hnc | hnc) :
      Triangle L q₂ q₃ p₁ ∨ Triangle L q₃ q₁ p₁ ∨ Triangle L q₁ q₂ p₁ := by
    -- else we have q₁ = p₁ = q₂
    by_contra h; push Not at h
    have hq' : Triangle L q₁ q₂ q₃ := fun hc ↦ hq (copl_of_col hc q₄)
    have he₁ : q₁ = p₁ := eq_of_col hq' h.2.2 (by col_perm h.2.1)
    have he₂ : q₂ = p₁ :=
      eq_of_col (by triangle_perm hq') h.1 (by col_perm h.2.2)
    have hn := ne_of_not_col hq'
    grind
  -- in each case, we deduce coplanarities with three q's and then put them together
  all_goals
    copl_perm copl_trans hnc
      (by copl_perm copl_trans3 hp (hall _) (hall _) (hall _))
      (by copl_perm copl_trans3 hp (hall _) (hall _) (hall _))

end Basic



section Desargues
variable {P L : Type*} [Membership P L] [ProjectiveGeometry P L]

/-- The degenerate case of the left-to-right implication of Desargues's theorem where
  the center of perspectivity lies on a side of one triangle. -/
lemma desargues_central_to_axial_of_col_centre {p₁ p₂ p₃ q₁ q₂ q₃ : P}
    (hp : Triangle L p₁ p₂ p₃) (hq : Triangle L q₁ q₂ q₃) :
    (∃ c, Collinear L c p₁ p₂ ∧ InCentralPerspectiveFrom c hp hq) →
    InAxialPerspective hp hq := by
  intro ⟨c, hcol, hc₁, hc₂, hc₃⟩
  -- we obtain the points r₁, r₂ thanks to the triangles with c
  have ⟨r₁, hqr₁, hpr₁⟩ : ∃ r₁, Collinear L q₂ q₃ r₁ ∧ Collinear L p₃ p₂ r₁ :=
    veblen ⟨by col_perm hc₂, hc₃⟩
  have ⟨r₂, hqr₂, hpr₂⟩ : ∃ r₂, Collinear L q₃ q₁ r₂ ∧ Collinear L p₁ p₃ r₂ :=
    veblen ⟨by col_perm hc₃, hc₁⟩
  by_cases hn : p₁ ≠ c ∧ p₂ ≠ c
  · have ⟨_, _, hnp⟩ := ne_of_not_col hp
    -- since p₁, p₂, q₁, q₂ are collinear, we may simply choose the intersection
    -- of the line r₁, r₂ with this line (from the triangle p₁, p₂, p₃)
    have ⟨r₃, hr, hpr₃⟩ : ∃ r₃, Collinear L r₁ r₂ r₃ ∧ Collinear L p₁ p₂ r₃ :=
      veblen ⟨by col_perm hpr₁, by col_perm hpr₂⟩
    have hqr₃ : Collinear L q₁ q₂ r₃ :=
      col_trans3 hnp
        (by col_perm col_trans hn.1 (by col_perm hcol) (by col_perm hc₁))
        (col_trans hn.2 (by col_perm hcol) (by col_perm hc₂))
        hpr₃
    exact ⟨r₁, r₂, r₃, hr,
      ⟨by col_perm hpr₁, by col_perm hqr₁⟩, ⟨by col_perm hpr₂, by col_perm hqr₂⟩, ⟨hpr₃, hqr₃⟩⟩
  · push +distrib Not at hn
    rcases hn with (hp₁c | hp₂c)
    · -- we may use q₃ instead of r₂ as it lies on the line p₁ = c, p₃
      use r₁, q₃, q₂
      rw [hp₁c]
      exact ⟨by col_perm hqr₁,
        ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
        ⟨by col_perm hc₃, by col_perm col_refl q₃ q₁⟩,
        ⟨by col_perm hc₂, by col_perm col_refl q₂ q₁⟩⟩
    · -- we may use q₃ instead of r₁ as it lies on the line p₂ = c, p₃
      use q₃, r₂, q₁
      rw [hp₂c]
      exact
        ⟨by col_perm hqr₂,
        ⟨by col_perm hc₃, by col_perm col_refl q₃ q₂⟩,
        ⟨by col_perm hpr₂, by col_perm hqr₂⟩,
        ⟨by col_perm hc₁, by col_perm col_refl q₁ q₂⟩⟩

/-- The left-to-right implication of Desargues's theorem for non-coplanar triangles. -/
theorem desargues_central_to_axial_of_noncoplanar {p₁ p₂ p₃ q₁ q₂ q₃ : P}
    (hp : Triangle L p₁ p₂ p₃) (hq : Triangle L q₁ q₂ q₃) :
    (∃ c, ¬ Coplanar L c p₁ p₂ p₃ ∧ InCentralPerspectiveFrom c hp hq) →
    InAxialPerspective hp hq := by
  intro ⟨c, hncopl, hc₁, hc₂, hc₃⟩
  by_cases hncol : Triangle L c q₂ q₃ ∧ Triangle L c q₃ q₁
  · -- we obtain the points r₁, r₂, r₃ thanks to the triangles with c
    have ⟨r₁, hqr₁, hpr₁⟩ : ∃ r₁, Collinear L q₂ q₃ r₁ ∧ Collinear L p₃ p₂ r₁ :=
      veblen ⟨by col_perm hc₂, hc₃⟩
    have ⟨r₂, hqr₂, hpr₂⟩ : ∃ r₂, Collinear L q₃ q₁ r₂ ∧ Collinear L p₁ p₃ r₂ :=
      veblen ⟨by col_perm hc₃, hc₁⟩
    have ⟨r₃, hqr₃, hpr₃⟩ : ∃ r₃, Collinear L q₁ q₂ r₃ ∧ Collinear L p₂ p₁ r₃ :=
      veblen ⟨by col_perm hc₁, hc₂⟩
    by_cases hnpq : p₃ ≠ q₃
    · -- in the main case, r₁, r₂, r₃ lie in the intersection of the two planes
      -- containing the triangles, which is a line
      have hnpr₁ : p₃ ≠ r₁ := by
        intro he; apply hncol.1
        rw [← he] at hqr₁
        col_perm col_trans hnpq.symm hqr₁ (by col_perm hc₃)
      have hnpr₂ : p₃ ≠ r₂ := by
        intro he; apply hncol.2
        rw [← he] at hqr₂
        col_perm col_trans hnpq.symm (by col_perm hqr₂) (by col_perm hc₃)
      -- we show that the planes are different (the points r₁, r₂ lie in both)
      have hncopl : ¬ Coplanar L r₁ r₂ p₃ q₃ := by
        intro hcopl; apply hncopl
        have hcopl' : Coplanar L c r₂ p₃ p₂ :=
          copl_of_col_of_copl hnpr₁
            (by copl_perm copl_of_col_of_copl hnpq hcopl hc₃)
            (by col_perm hpr₁)
        copl_perm copl_of_col_of_copl hnpr₂ (by copl_perm hcopl') (by col_perm hpr₂)
      -- the planes may be given by the r's and p₃ or q₃, respectively
      have hcopl_rp : Coplanar L p₃ r₁ r₂ r₃ :=
        copl_trans3 (by triangle_perm hp)
          (by copl_perm copl_of_col hpr₁ p₁)
          (by copl_perm copl_of_col hpr₂ p₂)
          (by copl_perm copl_of_col hpr₃ p₃)
      have hcopl_rq : Coplanar L q₃ r₁ r₂ r₃ :=
        copl_trans3 (by triangle_perm hq)
          (by copl_perm copl_of_col hqr₁ q₁)
          (by copl_perm copl_of_col hqr₂ q₂)
          (by copl_perm copl_of_col hqr₃ q₃)
      exact ⟨r₁, r₂, r₃,
        col_of_copl hncopl (by copl_perm hcopl_rp) (by copl_perm hcopl_rq),
        ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
        ⟨by col_perm hpr₂, by col_perm hqr₂⟩,
        ⟨by col_perm hpr₃, hqr₃⟩⟩
    · -- if p₃ = q₃, we may use this point in place of both r₁ and r₂
      push Not at hnpq
      use q₃, q₃, r₃
      rw [hnpq]
      exact
        ⟨col_refl q₃ r₃,
        ⟨by col_perm col_refl q₃ p₂, by col_perm col_refl q₃ q₂⟩,
        ⟨by col_perm col_refl q₃ p₁, by col_perm col_refl q₃ q₁⟩,
        ⟨by col_perm hpr₃, hqr₃⟩⟩
  · push +distrib Not at hncol
    -- in these cases, c lies on a side of the triangle q₁, q₂, q₃, which was already solved
    rcases hncol with (hcol₁ | hcol₂)
    · have ⟨r₂, r₃, r₁, hr, ⟨hqr₂, hpr₂⟩, ⟨hqr₃, hpr₃⟩, ⟨hqr₁, hpr₁⟩⟩ :
          InAxialPerspective (_ : Triangle L q₂ q₃ q₁) (_ : Triangle L p₂ p₃ p₁) :=
        desargues_central_to_axial_of_col_centre (by triangle_perm hq) (by triangle_perm hp)
          ⟨c, hcol₁, by col_perm hc₂, by col_perm hc₃, by col_perm hc₁⟩
      exact ⟨r₁, r₂, r₃, by col_perm hr,
        ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
        ⟨by col_perm hpr₂, by col_perm hqr₂⟩,
        ⟨by col_perm hpr₃, by col_perm hqr₃⟩⟩
    · have ⟨r₃, r₁, r₂, hr, ⟨hqr₃, hpr₃⟩, ⟨hqr₁, hpr₁⟩, ⟨hqr₂, hpr₂⟩⟩ :
          InAxialPerspective (_ : Triangle L q₃ q₁ q₂) (_ : Triangle L p₃ p₁ p₂) :=
        desargues_central_to_axial_of_col_centre (by triangle_perm hq) (by triangle_perm hp)
          ⟨c, hcol₂, by col_perm hc₃, by col_perm hc₁, by col_perm hc₂⟩
      exact ⟨r₁, r₂, r₃, by col_perm hr,
        ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
        ⟨by col_perm hpr₂, by col_perm hqr₂⟩,
        ⟨by col_perm hpr₃, by col_perm hqr₃⟩⟩

/-- The validity of the left-to-right implication of Desargues's theorem
  in projective geometries of dimension at least three. -/
theorem desargues_central_to_axial_of_notPlane [NotPlane P L] {p₁ p₂ p₃ q₁ q₂ q₃ : P}
    (hp : Triangle L p₁ p₂ p₃) (hq : Triangle L q₁ q₂ q₃) :
    InCentralPerspective hp hq → InAxialPerspective hp hq := by
  intro ⟨c, hc₁, hc₂, hc₃⟩
  by_cases hcopl : Coplanar L c p₁ p₂ p₃
  · by_cases hncol : (Triangle L c p₂ p₃ ∧ Triangle L c q₂ q₃)
        ∧ (Triangle L c p₃ p₁ ∧ Triangle L c q₃ q₁)
        ∧ (Triangle L c p₁ p₂ ∧ Triangle L c q₁ q₂)
    · -- we obtain the points r₁, r₂, r₃ thanks to the triangles with c
      have ⟨r₁, hqr₁, hpr₁⟩ : ∃ r₁, Collinear L q₂ q₃ r₁ ∧ Collinear L p₃ p₂ r₁ :=
        veblen ⟨by col_perm hc₂, hc₃⟩
      have ⟨r₂, hqr₂, hpr₂⟩ : ∃ r₂, Collinear L q₃ q₁ r₂ ∧ Collinear L p₁ p₃ r₂ :=
        veblen ⟨by col_perm hc₃, hc₁⟩
      have ⟨r₃, hqr₃, hpr₃⟩ : ∃ r₃, Collinear L q₁ q₂ r₃ ∧ Collinear L p₂ p₁ r₃ :=
        veblen ⟨by col_perm hc₁, hc₂⟩
      have ⟨hncol₁, hncol₂, hncol₃⟩ := hncol
      by_cases hn : p₁ ≠ q₁ ∧ p₃ ≠ q₃
      · -- we consider a point s not in the plane of the triangles
        -- and lift the points p₃, q₃ from this plane via s to p₃', q₃';
        -- like this, we obtain two non-coplanar triangles p₁, p₂, p₃' and q₁, q₂, q₃'
        -- which also have c as their centre of perspectivity
        have ⟨s, hs⟩ : ∃ s, ¬ Coplanar L p₁ p₂ p₃ s := exists_not_copl_of_notPlane hp
        have ⟨p₃', hcol_sp', hne_pp', hne_sp'⟩ := exists_col_pt_ne L p₃ s
        -- the point q₃' is obtained as the intersection of the line c, p₃'
        -- with the line s, q₃ (via the triangle s, q₃, p₃)
        have ⟨q₃', hc₃', hsq₃'⟩ : ∃ q₃', Collinear L c p₃' q₃' ∧ Collinear L s q₃ q₃' :=
          veblen ⟨by col_perm hc₃, by col_perm hcol_sp'⟩
        -- the new triangles are not coplanar
        have hncopl' : ¬ Coplanar L c p₁ p₂ p₃' := by
          intro hcopl'; apply hs
          have hcopl_p' : Coplanar L p₃ p₁ p₂ p₃' :=
            copl_trans (by triangle_perm hncol₃.1) (by copl_perm hcopl) (by copl_perm hcopl')
          exact copl_of_col_of_copl hne_pp'.symm (by copl_perm hcopl_p') (by col_perm hcol_sp')
        -- we verify that the triangles are non-degenerate
        have hp' : Triangle L p₁ p₂ p₃' := fun h ↦ hncopl' (by copl_perm copl_of_col h c)
        have hq' : Triangle L q₁ q₂ q₃' := by
          intro hq'; apply hncopl'
          have hncq' : c ≠ q₃' := by
            intro hcq'; apply hncol₃.2
            rw [← hcq'] at hq'
            col_perm hq'
          have hcopl_cqp' : Coplanar L q₁ q₂ c p₃' :=
            copl_of_col_of_copl hncq' (by copl_perm copl_of_col hq' c) (by col_perm hc₃')
          copl_perm copl_trans3 hncol₃.2
            (by copl_perm hcopl_cqp')
            (by copl_perm copl_of_col hc₁ q₂)
            (by copl_perm copl_of_col hc₂ q₁)
        -- now we can apply the result for non-coplanar triangles
        have ⟨r₁', r₂', r₃', hr', ⟨hpr₁', hqr₁'⟩, ⟨hpr₂', hqr₂'⟩, ⟨hpr₃', hqr₃'⟩⟩ :
            InAxialPerspective (_ : Triangle L p₁ p₂ p₃') (_ : Triangle L q₁ q₂ q₃') :=
          desargues_central_to_axial_of_noncoplanar hp' hq'
            ⟨c, hncopl', hc₁, hc₂, by col_perm hc₃'⟩
        -- next we aim to project the configuration back into the original plane via s,
        -- which will map the line r₁', r₂', r₃' to a line r₁, r₂, r₃
        have ⟨hn₁p, hn₂p, hn₃p⟩ := ne_of_not_col hp
        have ⟨hn₁q, hn₂q, hn₃q⟩ := ne_of_not_col hq
        -- first, r₃ = r₃' since it is defined the same way (without p₃', q₃')
        have her₃ : r₃ = r₃' :=
          have hncol_r : Triangle L r₃ p₁ q₁ := by
            intro hcol_r; apply hncol₃.1
            have hnr : p₁ ≠ r₃ := by
              intro he; apply hncol₃.2
              rw [← he] at hqr₃
              col_perm col_trans hn.1.symm (by col_perm hqr₃) (by col_perm hc₁)
            have : Collinear L q₁ p₁ p₂ := col_trans hnr (by col_perm hcol_r) (by col_perm hpr₃)
            col_perm col_trans hn.1 (by col_perm this) hc₁
          eq_of_col hncol_r
            (col_trans hn₃p (by col_perm hpr₃) hpr₃')
            (col_trans hn₃q (by col_perm hqr₃) hqr₃')
        have hnr₁ : p₃ ≠ r₁ := by
          intro he; apply hncol₁.2
          rw [← he] at hqr₁
          col_perm col_trans hn.2.symm hqr₁ (by col_perm hc₃)
        have hnr₂ : p₃ ≠ r₂ := by
              intro he; apply hncol₂.2
              rw [← he] at hqr₂
              col_perm col_trans hn.2.symm (by col_perm hqr₂) (by col_perm hc₃)
        -- we verify that r₁, r₂ are intersections of the lines s, r₁', resp. s, r₂'
        -- with our plane
        have hcolr₁ : Collinear L s r₁ r₁' :=
          -- these three points lie in the intersection of the planes spanned by
          -- s and the sides p₂, p₃ and q₂, q₃ of the triangles (since p₃', q₃' lie there too)
          have hcopl_srp : Coplanar L s r₁ p₃ r₁' := by
            copl_perm
              copl_of_col_of_copl hn₁p.symm
                (by copl_perm
                  (⟨p₃', by col_perm hcol_sp', by col_perm hpr₁'⟩ : Coplanar L s p₃ p₂ r₁'))
                hpr₁
          have hcopl_srq : Coplanar L s r₁ q₃ r₁' := by
            copl_perm
              copl_of_col_of_copl hn₁q.symm
                (by copl_perm (⟨q₃', hsq₃', by col_perm hqr₁'⟩ : Coplanar L s q₃ q₂ r₁'))
                (by col_perm hqr₁)
          -- the planes are different
          have hncopl_srpq : ¬ Coplanar L s r₁ p₃ q₃ := by
            intro hcopl_srpq; apply hs
            have hcopl_csp : Coplanar L c s p₃ p₂ :=
              copl_of_col_of_copl hnr₁
                (by copl_perm copl_of_col_of_copl hn.2 hcopl_srpq hc₃) (by col_perm hpr₁)
            copl_perm
              copl_trans (by triangle_perm hncol₁.1) (by copl_perm hcopl_csp) (by copl_perm hcopl)
          col_of_copl hncopl_srpq hcopl_srp hcopl_srq
        have hcolr₂ : Collinear L s r₂ r₂' :=
          -- these three points lie in the intersection of the planes spanned by
          -- s and the sides p₁, p₃ and q₁, q₃ of the triangles (since p₃', q₃' lie there too)
          have hcopl_srp : Coplanar L s r₂ p₃ r₂' := by
            copl_perm
              copl_of_col_of_copl hn₂p
                (by copl_perm (⟨p₃', by col_perm hcol_sp', hpr₂'⟩ : Coplanar L s p₃ p₁ r₂'))
                (by col_perm hpr₂)
          have hcopl_srq : Coplanar L s r₂ q₃ r₂' := by
            have : Coplanar L s q₃ q₁ r₂' := ⟨q₃', hsq₃', hqr₂'⟩
            copl_perm
              copl_of_col_of_copl hn₂q
              (by copl_perm (⟨q₃', hsq₃', hqr₂'⟩ : Coplanar L s q₃ q₁ r₂')) hqr₂
          -- the planes are different
          have hncopl_srpq : ¬ Coplanar L s r₂ p₃ q₃ := by
            intro hcopl_srpq; apply hs
            have hcopl_csp : Coplanar L s c p₃ p₁ :=
              copl_of_col_of_copl hnr₂
                (by copl_perm copl_of_col_of_copl hn.2 hcopl_srpq hc₃) (by col_perm hpr₂)
            copl_perm
              copl_trans (by triangle_perm hncol₂.1) (by copl_perm hcopl_csp) (by copl_perm hcopl)
          col_of_copl hncopl_srpq hcopl_srp hcopl_srq
        -- the projection may be viewed as follows: we know that s, r₁, r₁', r₂, r₂', r₃ = r₃'
        -- are all coplanar, so we consider the intersection of this plane with the original plane
        -- (which contains r₁, r₂, r₃)
        have hcopl_r : Coplanar L p₃ r₃ r₁ r₂ :=
          copl_trans3 (by triangle_perm hp)
            (by copl_perm copl_of_col hpr₃ p₃)
            (by copl_perm copl_of_col hpr₁ p₁)
            (by copl_perm copl_of_col hpr₂ p₂)
        have hcopl_sr : Coplanar L r₁ r₂ s r₃ := by
          have hnr' : s ≠ r₁' ∧ s ≠ r₂' := by
            by_contra her'; push +distrib Not at her'; apply hne_sp'.symm
            rcases her' with (her₁' | her₂')
            · rw [← her₁'] at hpr₁'
              have hncol_sp : Triangle L s p₂ p₃ := fun h ↦ hs (by copl_perm copl_of_col h p₁)
              exact eq_of_col hncol_sp hpr₁' (by col_perm hcol_sp')
            · rw [← her₂'] at hpr₂'
              have hncol_sp : Triangle L s p₁ p₃ := fun h ↦ hs (by copl_perm copl_of_col h p₂)
              exact eq_of_col hncol_sp (by col_perm hpr₂') (by col_perm hcol_sp')
          rw [her₃]
          have hcopl_srr' : Coplanar L r₂' r₃' s r₁ :=
            copl_of_col_of_copl hnr'.1 (by copl_perm copl_of_col hr' s) (by col_perm hcolr₁)
          copl_perm copl_of_col_of_copl hnr'.2 (by copl_perm hcopl_srr') (by col_perm hcolr₂)
        -- again, these two planes are different
        have hncopl_srp: ¬ Coplanar L r₁ r₂ p₃ s := by
          intro h; apply hs
          have : Coplanar L s r₂ p₃ p₂ :=
            copl_of_col_of_copl hnr₁ (by copl_perm h) (by col_perm hpr₁)
          copl_perm
            copl_of_col_of_copl hnr₂ (by copl_perm this) (by col_perm hpr₂)
        -- hence the intersection is a line and we are done
        exact ⟨r₁, r₂, r₃,
          col_of_copl hncopl_srp (by copl_perm hcopl_r) hcopl_sr,
          ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
          ⟨by col_perm hpr₂, by col_perm hqr₂⟩,
          ⟨by col_perm hpr₃, hqr₃⟩⟩
      · push +distrib Not at hn
        -- if some two respective points of the triangles are equal,
        -- we may use this point in the place of two r's
        rcases hn with (he₁ | he₃)
        · use r₁, q₁, q₁
          rw [he₁]
          exact
            ⟨by col_perm col_refl q₁ r₁,
            ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
            ⟨col_refl q₁ p₃, col_refl q₁ q₃⟩,
            ⟨by col_perm col_refl q₁ p₂, by col_perm col_refl q₁ q₂⟩⟩
        · use q₃, q₃, r₃
          rw [he₃]
          exact
            ⟨col_refl q₃ r₃,
            ⟨by col_perm col_refl q₃ p₂, by col_perm col_refl q₃ q₂⟩,
            ⟨by col_perm col_refl q₃ p₁, by col_perm col_refl q₃ q₁⟩,
            ⟨by col_perm hpr₃, hqr₃⟩⟩
    · push +distrib Not at hncol
      -- in these cases, c lies on a side of one of the triangles, which was already solved
      rcases hncol with ((hcolp₁ | hcolq₁) | (hcolp₂ | hcolq₂) | (hcolp₃ | hcolq₃))
      focus (have ⟨r₂, r₃, r₁, hr, ⟨hpr₂, hqr₂⟩, ⟨hpr₃, hqr₃⟩, ⟨hpr₁, hqr₁⟩⟩ :
                InAxialPerspective (_ : Triangle L p₂ p₃ p₁) (_ : Triangle L q₂ q₃ q₁) :=
              desargues_central_to_axial_of_col_centre (by triangle_perm hp) (by triangle_perm hq)
                ⟨c, hcolp₁, hc₂, hc₃, hc₁⟩)
      rotate_left
      focus (have ⟨r₂, r₃, r₁, hr, ⟨hqr₂, hpr₂⟩, ⟨hqr₃, hpr₃⟩, ⟨hqr₁, hpr₁⟩⟩ :
                InAxialPerspective (_ : Triangle L q₂ q₃ q₁) (_ : Triangle L p₂ p₃ p₁) :=
              desargues_central_to_axial_of_col_centre (by triangle_perm hq) (by triangle_perm hp)
                ⟨c, hcolq₁, by col_perm hc₂, by col_perm hc₃, by col_perm hc₁⟩)
      rotate_left
      focus (have ⟨r₃, r₁, r₂, hr, ⟨hpr₃, hqr₃⟩, ⟨hpr₁, hqr₁⟩, ⟨hpr₂, hqr₂⟩⟩ :
                InAxialPerspective (_ : Triangle L p₃ p₁ p₂) (_ : Triangle L q₃ q₁ q₂) :=
              desargues_central_to_axial_of_col_centre (by triangle_perm hp) (by triangle_perm hq)
                ⟨c, hcolp₂, hc₃, hc₁, hc₂⟩)
      rotate_left
      focus (have ⟨r₃, r₁, r₂, hr, ⟨hqr₃, hpr₃⟩, ⟨hqr₁, hpr₁⟩, ⟨hqr₂, hpr₂⟩⟩ :
                InAxialPerspective (_ : Triangle L q₃ q₁ q₂) (_ : Triangle L p₃ p₁ p₂) :=
              desargues_central_to_axial_of_col_centre (by triangle_perm hq) (by triangle_perm hp)
                ⟨c, hcolq₂, by col_perm hc₃, by col_perm hc₁, by col_perm hc₂⟩)
      rotate_left
      focus (have ⟨r₁, r₂, r₃, hr, ⟨hpr₁, hqr₁⟩, ⟨hpr₂, hqr₂⟩, ⟨hpr₃, hqr₃⟩⟩ :
                InAxialPerspective (_ : Triangle L p₁ p₂ p₃) (_ : Triangle L q₁ q₂ q₃) :=
              desargues_central_to_axial_of_col_centre hp hq ⟨c, hcolp₃, hc₁, hc₂, hc₃⟩)
      rotate_left
      focus (have ⟨r₁, r₂, r₃, hr, ⟨hqr₁, hpr₁⟩, ⟨hqr₂, hpr₂⟩, ⟨hqr₃, hpr₃⟩⟩ :
                InAxialPerspective (_ : Triangle L q₁ q₂ q₃) (_ : Triangle L p₁ p₂ p₃) :=
                  desargues_central_to_axial_of_col_centre hq hp
                    ⟨c, hcolq₃, by col_perm hc₁, by col_perm hc₂, by col_perm hc₃⟩)
      all_goals
        exact ⟨r₁, r₂, r₃, by col_perm hr,
          ⟨by col_perm hpr₁, by col_perm hqr₁⟩,
          ⟨by col_perm hpr₂, by col_perm hqr₂⟩,
          ⟨by col_perm hpr₃, by col_perm hqr₃⟩⟩
  · exact desargues_central_to_axial_of_noncoplanar hp hq ⟨c, hcopl, hc₁, hc₂, hc₃⟩

/-- A projective geometry of dimension at least three is Desarguesian. -/
instance [NotPlane P L] : Desarguesian P L :=
  {desargues := by
    intro p₁ p₂ p₃ q₁ q₂ q₃ hp hq
    constructor
    · exact desargues_central_to_axial_of_notPlane hp hq
    · intro ⟨r₁, r₂, r₃, hr, ⟨hpr₁, hqr₁⟩, ⟨hpr₂, hqr₂⟩, ⟨hpr₃, hqr₃⟩⟩
      by_cases hn : p₁ ≠ q₁ ∧ p₂ ≠ q₂
      · by_cases hnpts : (p₁ ≠ r₂ ∧ p₂ ≠ r₁) ∧ (q₁ ≠ r₂ ∧ q₂ ≠ r₁)
        · by_cases hncol : Triangle L p₁ q₁ r₂ ∧ Triangle L p₂ q₂ r₁
          · -- in the generic case, the already proved implication may be used
            -- on these two triangles
            have ⟨s₁, s₂, s₃, hs, ⟨hs₁, hs₁'⟩, ⟨hs₂, hs₂'⟩, ⟨hs₃, hs₃'⟩⟩ :
                InAxialPerspective (_ : Triangle L p₁ q₁ r₂) (_ : Triangle L p₂ q₂ r₁) :=
              desargues_central_to_axial_of_notPlane hncol.1 hncol.2
                ⟨r₃, hpr₃, hqr₃, by col_perm hr⟩
            have he₁ : q₃ = s₁ :=
              eq_of_col (by triangle_perm hq)
                (col_trans hnpts.2.1 (by col_perm hqr₂) (by col_perm hs₁))
                (col_trans hnpts.2.2 (by col_perm hqr₁) (by col_perm hs₁'))
            have he₂ : p₃ = s₂ :=
              eq_of_col (by triangle_perm hp)
                (col_trans hnpts.1.1 (by col_perm hpr₂) (by col_perm hs₂))
                (col_trans hnpts.1.2 (by col_perm hpr₁) (by col_perm hs₂'))
            rw [← he₁, ← he₂] at hs
            exact ⟨s₃, hs₃, hs₃', by col_perm hs⟩
          · push +distrib Not at hncol
            rcases hncol with (hcol₂ | hcol₁)
            -- some pair of the respective sides of the triangles coincides, so we only need
            -- to find a suitable point on this line
            · -- the line q₂, p₂ crosses the triangle p₁, q₁, r₃
              have ⟨c, hc₂, hc₁⟩ : ∃ c, Collinear L q₂ p₂ c ∧ Collinear L p₁ q₁ c :=
                veblen ⟨by col_perm hqr₃, hpr₃⟩
              have hc₃ : Collinear L p₃ q₃ c :=
                col_trans3 hn.1
                  (by col_perm (col_trans hnpts.1.1 (by col_perm hcol₂) hpr₂))
                  (col_trans hnpts.2.1 hcol₂ hqr₂)
                  hc₁
              exact ⟨c, hc₁, by col_perm hc₂, hc₃⟩
            · -- the line q₁, p₁ crosses the triangle p₂, q₂, r₃
              have ⟨c, hc₁, hc₂⟩ : ∃ c, Collinear L q₁ p₁ c ∧ Collinear L p₂ q₂ c :=
                veblen ⟨hqr₃, by col_perm hpr₃⟩
              have hc₃ : Collinear L p₃ q₃ c :=
                col_trans3 hn.2
                  (by col_perm (col_trans hnpts.1.2 (by col_perm hcol₁) (by col_perm hpr₁)))
                  (col_trans hnpts.2.2 hcol₁ (by col_perm hqr₁))
                  hc₂
              exact ⟨c, by col_perm hc₁, hc₂, hc₃⟩
        · push +distrib Not at hnpts; rw [or_assoc] at hnpts
          rcases hnpts with (hp₁ | hp₂ | hq₁ | hq₂)
          -- here we show that p₁ = r₂, p₂ = r₁ hold simultaneously (or q₁ = r₂, q₂ = r₁)
          -- and we may hence use q₃ (or p₃)
          · rw [hp₁] at hpr₃ hp
            have hnr₂ : r₂ ≠ r₃ := by
              intro hr₂
              rw [hr₂] at hqr₂
              have : q₁ = r₃ := eq_of_col hq hqr₃ (by col_perm hqr₂)
              grind
            have hp₂ : p₂ = r₁ :=
              eq_of_col (by triangle_perm hp)
                (by col_perm hpr₁)
                (col_trans hnr₂ (by col_perm hpr₃) (by col_perm hr))
            rw [← hp₁] at hqr₂; rw [← hp₂] at hqr₁
            exact ⟨q₃, by col_perm hqr₂, hqr₁, by col_perm col_refl q₃ p₃⟩
          · rw [hp₂] at hpr₃ hp
            have hnr₁ : r₁ ≠ r₃ := by
              intro hr₁
              rw [hr₁] at hqr₁
              have : q₂ = r₃ :=
                eq_of_col (by triangle_perm hq) (by col_perm hqr₁) (by col_perm hqr₃)
              grind
            have hp₁ : p₁ = r₂ :=
              eq_of_col hp (col_trans hnr₁ hpr₃ (by col_perm hr)) (by col_perm hpr₂)
            rw [← hp₁] at hqr₂; rw [← hp₂] at hqr₁
            exact ⟨q₃, by col_perm hqr₂, hqr₁, by col_perm col_refl q₃ p₃⟩
          · rw [hq₁] at hqr₃ hq
            have hnr₂ : r₂ ≠ r₃ := by
              intro hr₂
              rw [hr₂] at hpr₂
              have : p₁ = r₃ := eq_of_col hp hpr₃ (by col_perm hpr₂)
              grind
            have hq₂ : q₂ = r₁ :=
              eq_of_col (by triangle_perm hq)
                (by col_perm hqr₁)
                (col_trans hnr₂ (by col_perm hqr₃) (by col_perm hr))
            rw [← hq₁] at hpr₂; rw [← hq₂] at hpr₁
            exact ⟨p₃, hpr₂, by col_perm hpr₁, by col_perm col_refl p₃ q₃⟩
          · rw [hq₂] at hqr₃ hq
            have hnr₁ : r₁ ≠ r₃ := by
              intro hr₁
              rw [hr₁] at hpr₁
              have : p₂ = r₃ :=
                eq_of_col (by triangle_perm hp) (by col_perm hpr₁) (by col_perm hpr₃)
              grind
            have hq₁ : q₁ = r₂ :=
              eq_of_col hq (col_trans hnr₁ hqr₃ (by col_perm hr)) (by col_perm hqr₂)
            rw [← hq₁] at hpr₂; rw [← hq₂] at hpr₁
            exact ⟨p₃, hpr₂, by col_perm hpr₁, by col_perm col_refl p₃ q₃⟩
      · push +distrib Not at hn
        unfold InCentralPerspective InCentralPerspectiveFrom
        rcases hn with (h₁ | h₂)
        -- in these cases it suffices to show that the lines p₂, q₂ and p₃, q₃
        -- (or p₁, q₁ and p₃, q₃) have a common point
        · have ⟨c, hc₃, hc₂⟩ : ∃ c, Collinear L q₃ p₃ c ∧ Collinear L p₂ q₂ c :=
            veblen ⟨by col_perm hqr₁, by col_perm hpr₁⟩
          -- from the triangle p₂, q₂, r₁ crossed by the line q₃, p₃
          rw [h₁]
          exact ⟨c, col_refl q₁ c, hc₂, by col_perm hc₃⟩
        · have ⟨c, hc₁, hc₃⟩ : ∃ c, Collinear L q₁ p₁ c ∧ Collinear L p₃ q₃ c :=
            veblen ⟨by col_perm hqr₂, by col_perm hpr₂⟩
          -- from the triangle p₃, q₃, r₂ crossed by the line q₁, p₁
          rw [h₂]
          exact ⟨c, by col_perm hc₁, col_refl q₂ c, hc₃⟩}

end Desargues



end ProjectiveGeometry
