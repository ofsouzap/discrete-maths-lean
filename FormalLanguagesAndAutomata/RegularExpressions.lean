import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

import FormalLanguagesAndAutomata.FormalLanguages

namespace FormalLanguagesAndAutomata.RegularExpressions


-- Section 4, "Regular expressions and pattern matching"

-- Definition 2.1, "Regular expressions (concrete syntax)"
namespace Examples.E2_1

open RegExp

-- Concrete regex syntax over an arbitrary alphabet Σ.
-- The lecture’s concrete notation lives over this abstract alphabet wrapper.
@[simp]
def alphabet_rx {t} (Σ : Finset t) : Type := Alphabet Σ

@[simp]
def Σ_rx {t} (Σ : Finset t) : Type := List (alphabet_rx Σ)

end Examples.E2_1

-- Example 2.2, "Derivation of a concrete regular expression"
namespace Examples.E2_2

open RegExp

-- The lecture notes phrase this over an arbitrary alphabet Σ.
-- Here we keep the regex payload abstract over Σ, with the example driven by
-- two arbitrary symbols `a` and `b` from that alphabet.
@[simp]
def concrete_eps_or_ab_star {t} {Σ : Finset t}
  (a b : Alphabet Σ) : RegExp Σ :=
  union null (concat (sym a) (star (sym b)))

end Examples.E2_2

namespace RegularExpressions

-- Definition 2.3, "Regular expressions (abstract syntax)"
inductive RegExp {t} (symbols : Finset t) : Type where
  | union : RegExp symbols → RegExp symbols → RegExp symbols
  | concat : RegExp symbols → RegExp symbols → RegExp symbols
  | star : RegExp symbols → RegExp symbols
  | null : RegExp symbols
  | never : RegExp symbols
  | sym : Alphabet symbols → RegExp symbols

-- Example 2.4, "Examples of abstract syntax trees"
namespace Examples.E2_4

open RegExp

abbrev Σab : Finset Char := {'a', 'b'}

@[simp]
def a : Alphabet Σab := ⟨'a', by simp [Σab]⟩

@[simp]
def b : Alphabet Σab := ⟨'b', by simp [Σab]⟩

@[simp]
def eps_or_ab_star : RegExp Σab :=
  union null (concat (sym a) (star (sym b)))

end Examples.E2_4

-- Definition 3.1, "The matching relation for regular expressions"
inductive Matches {t} {symbols : Finset t}
  : Strings symbols → RegExp symbols → Prop where
  | sym (a : Alphabet symbols)
    : Matches [a] (RegExp.sym a)
  | null
    : Matches ε RegExp.null
  | union_left
    : Matches u R
    → Matches u (RegExp.union R S)
  | union_right
    : Matches u S
    → Matches u (RegExp.union R S)
  | concat
    : Matches u R
    → Matches v S
    → Matches (u ++ v) (RegExp.concat R S)
  | star_zero
    : Matches ε (RegExp.star R)
  | star_append
    : Matches u R
    → Matches v (RegExp.star R)
    → Matches (u ++ v) (RegExp.star R)

def languageOf {t} {symbols : Finset t}
  (R : RegExp symbols)
  : FormalLanguage symbols :=
  { u | Matches u R }

namespace Matches

@[simp]
theorem never {t} {symbols : Finset t} (u : Strings symbols)
  : ¬ Matches u (@RegExp.never t symbols) := by
  intro h
  cases h

@[simp]
theorem null_iff {t} {symbols : Finset t} (u : Strings symbols)
  : Matches u (@RegExp.null t symbols) ↔ u = ε := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.null

end Matches

-- Example 3.2, "Examples of regular expression matching"
namespace Examples.E4

open RegExp
open Examples.E2_4 (Σab a b eps_or_ab_star)

@[simp]
def a_or_b : RegExp Σab :=
  union (sym a) (sym b)

@[simp]
def eps_or_ab_star : RegExp Σab :=
  union null (concat (sym a) (star (sym b)))

example : Matches ε eps_or_ab_star := by
  exact Matches.union_left Matches.null

example : Matches [a] eps_or_ab_star := by
  apply Matches.union_right
  apply Matches.concat
  · exact Matches.sym a
  · exact Matches.star_zero

example : Matches [a, b, b] eps_or_ab_star := by
  apply Matches.union_right
  apply Matches.concat
  · exact Matches.sym a
  · apply Matches.star_append
    · exact Matches.sym b
    · apply Matches.star_append
      · exact Matches.sym b
      · exact Matches.star_zero

@[simp]
lemma sym_ab_cases (x : Alphabet Σab)
  : x = a ∨ x = b := by
  have hxmem : (x : Char) ∈ Σab := x.property
  have hx : (x : Char) = 'a' ∨ (x : Char) = 'b' := by
    simpa [Σab, Finset.mem_insert, Finset.mem_singleton] using hxmem
  rcases hx with hxa | hxb
  · left
    apply Subtype.ext
    simpa [a] using hxa
  · right
    apply Subtype.ext
    simpa [b] using hxb

example : ∀ u : Strings Σab, Matches u (star a_or_b) := by
  intro u
  induction u with
  | nil =>
    exact Matches.star_zero
  | cons x xs ih =>
    apply Matches.star_append
    · have hx := sym_ab_cases x
      rcases hx with hxa | hxb
      · rw [hxa]
        exact Matches.union_left (Matches.sym a)
      · rw [hxb]
        exact Matches.union_right (Matches.sym b)
    · exact ih

@[simp]
def starts_with_b : RegExp Σab :=
  concat (sym b) (star a_or_b)

example : Matches [b] starts_with_b := by
  apply Matches.concat
  · exact Matches.sym b
  · exact Matches.star_zero

example : Matches [b, a, b, a] starts_with_b := by
  apply Matches.concat
  · exact Matches.sym b
  · apply Matches.star_append
    · exact Matches.union_left (Matches.sym a)
    · apply Matches.star_append
      · exact Matches.union_right (Matches.sym b)
      · apply Matches.star_append
        · exact Matches.union_left (Matches.sym a)
        · exact Matches.star_zero

@[simp]
def two_symbols : RegExp Σab :=
  concat a_or_b a_or_b

@[simp]
def even_length : RegExp Σab :=
  star two_symbols

example : Matches ε even_length := by
  exact Matches.star_zero

example : Matches [a, b, b, a] even_length := by
  apply Matches.star_append
  · apply Matches.concat
    · exact Matches.union_left (Matches.sym a)
    · exact Matches.union_right (Matches.sym b)
  · apply Matches.star_append
    · apply Matches.concat
      · exact Matches.union_right (Matches.sym b)
      · exact Matches.union_left (Matches.sym a)
    · exact Matches.star_zero

@[simp]
def eps_or_a : RegExp Σab :=
  union null (sym a)

@[simp]
def eps_or_b : RegExp Σab :=
  union null (sym b)

@[simp]
def finite_example : RegExp Σab :=
  union (concat eps_or_a eps_or_b) (concat (sym b) (sym b))

example : Matches ε finite_example := by
  apply Matches.union_left
  apply Matches.concat
  · exact Matches.union_left Matches.null
  · exact Matches.union_left Matches.null

example : Matches [a] finite_example := by
  apply Matches.union_left
  apply Matches.concat
  · exact Matches.union_right (Matches.sym a)
  · exact Matches.union_left Matches.null

example : Matches [b] finite_example := by
  apply Matches.union_left
  apply Matches.concat
  · exact Matches.union_left Matches.null
  · exact Matches.union_right (Matches.sym b)

example : Matches [a, b] finite_example := by
  apply Matches.union_left
  apply Matches.concat
  · exact Matches.union_right (Matches.sym a)
  · exact Matches.union_right (Matches.sym b)

example : Matches [b, b] finite_example := by
  apply Matches.union_right
  apply Matches.concat
  · exact Matches.sym b
  · exact Matches.sym b

@[simp]
def never_then_b_or_a : RegExp Σab :=
  union (concat never (sym b)) (sym a)

example : Matches [a] never_then_b_or_a := by
  apply Matches.union_right
  exact Matches.sym a

end Examples.E4

end RegularExpressions

end FormalLanguagesAndAutomata.RegularExpressions
