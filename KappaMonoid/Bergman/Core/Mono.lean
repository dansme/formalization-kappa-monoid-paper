/-
**Monomials** (Bergman §§4, 9).

Given base index types `S μ j` (a homogeneous `k`-basis of `e_j N_μ` for a family of modules
`N_μ`), a *monomial* is a word `tₙ ⋯ t₁ s`: a base element `s` followed (on the left) by letters,
such that consecutive factors come from different rings (a base element of `N_none` is associated
with no ring) and the indices match (the right index of each letter is the left index of the
factor to its right).  The word is stored leftmost letter first, so that multiplying on the left
is `List.cons`.

Monomials are well-ordered: first by degree (number of letters), then lexicographically *reading
from the base element* (Bergman's "lexicographic reading from the left", mirrored).  This order
refines the degree and is compatible with left multiplication by letters (`lt_cons_cons`), which
is all the leading-term arguments use.
-/
import KappaMonoid.Bergman.Core.Basic
import Mathlib.Data.List.Shortlex

universe u

namespace Bergman.Core

open Module

variable {k : Type u} [Field k] {ι : Type} [DecidableEq ι]
  {Λ : Type}
  {R : Λ → Type u} [∀ l, Ring (R l)] [∀ l, Algebra k (R l)]
  (σ : ∀ l, (ι → k) →ₐ[k] R l) [Fact (∀ l, Function.Injective (σ l))]

/-- A letter: an element of the chosen basis of `e_i (R l) e_j`, other than `e_i`. -/
abbrev Letter : Type u := Σ (l : Λ) (i j : ι), Tl σ (some l) i j

namespace Letter

variable {σ}

/-- The ring a letter comes from. -/
def side (t : Letter σ) : Λ := t.1

/-- The left index `i` of `t ∈ e_i R e_j`. -/
def left (t : Letter σ) : ι := t.2.1

/-- The right index `j` of `t ∈ e_i R e_j`. -/
def right (t : Letter σ) : ι := t.2.2.1

/-- The value of a letter in `R l`. -/
noncomputable def val (t : Letter σ) : R t.side := tval σ t.2.2.2

end Letter

variable (S : Option Λ → ι → Type u)

/-- A base element: an element of the basis of some `e_j N_μ`. -/
abbrev Base : Type u := Σ (μ : Option Λ) (j : ι), S μ j

variable {S}

/-- The component `μ` of a base element (`none`: associated with no ring). -/
def Base.side (b : Base S) : Option Λ := b.1

/-- The index `j` of a base element of `e_j N_μ`. -/
def Base.idx (b : Base S) : ι := b.2.1

variable {σ}

/-- The left index of the word `ts · b`. -/
def wordLeft (b : Base S) : List (Letter σ) → ι
  | [] => b.idx
  | t :: _ => t.left

/-- The side of the word `ts · b` (the ring of its leftmost factor). -/
def wordSide (b : Base S) : List (Letter σ) → Option Λ
  | [] => b.side
  | t :: _ => some t.side

/-- The chain condition: indices match and consecutive factors come from different rings. -/
def Chain (b : Base S) : List (Letter σ) → Prop
  | [] => True
  | t :: ts => Chain b ts ∧ t.right = wordLeft b ts ∧ some t.side ≠ wordSide b ts

variable (σ S)

/-- A **monomial** `tₙ ⋯ t₁ s`. -/
structure Mono where
  /-- The base element `s`. -/
  base : Base S
  /-- The letters, leftmost first: `[tₙ, …, t₁]`. -/
  word : List (Letter σ)
  chain : Chain base word

variable {σ S}

namespace Mono

/-- The degree: the number of letters. -/
def deg (w : Mono σ S) : ℕ := w.word.length

/-- The left index. -/
def left (w : Mono σ S) : ι := wordLeft w.base w.word

/-- The side: the ring of the leftmost factor (`none` for a base element of `N_none`). -/
def side (w : Mono σ S) : Option Λ := wordSide w.base w.word

/-- A base element as a monomial of degree `0`. -/
def ofBase (b : Base S) : Mono σ S := ⟨b, [], trivial⟩

/-- Left multiplication by a letter, when allowed. -/
def cons (t : Letter σ) (w : Mono σ S) (h₁ : t.right = w.left) (h₂ : some t.side ≠ w.side) :
    Mono σ S := ⟨w.base, t :: w.word, w.chain, h₁, h₂⟩

@[simp] theorem deg_cons (t : Letter σ) (w : Mono σ S) (h₁ h₂) :
    (cons t w h₁ h₂).deg = w.deg + 1 := rfl

@[simp] theorem left_cons (t : Letter σ) (w : Mono σ S) (h₁ h₂) :
    (cons t w h₁ h₂).left = t.left := rfl

@[simp] theorem side_cons (t : Letter σ) (w : Mono σ S) (h₁ h₂) :
    (cons t w h₁ h₂).side = some t.side := rfl

@[ext] theorem ext {w w' : Mono σ S} (hb : w.base = w'.base) (hw : w.word = w'.word) :
    w = w' := by
  cases w; cases w'; cases hb; cases hw; rfl

/-- The tail of a monomial of positive degree. -/
def tail (w : Mono σ S) : Mono σ S := ⟨w.base, w.word.tail, by
  rcases w with ⟨b, _ | ⟨t, ts⟩, h⟩
  · trivial
  · exact h.1⟩

/-- Every monomial of positive degree is a letter times its tail. -/
theorem eq_cons_of_word_eq_cons {w : Mono σ S} {t : Letter σ} {ts : List (Letter σ)}
    (h : w.word = t :: ts) : ∃ h₁ h₂, w = cons t w.tail h₁ h₂ := by
  obtain ⟨b, word, hc⟩ := w
  subst h
  exact ⟨hc.2.1, hc.2.2, rfl⟩

theorem tail_cons (t : Letter σ) (w : Mono σ S) (h₁ h₂) : (cons t w h₁ h₂).tail = w := rfl

/-! ## The order -/

/-- Codes of the factors, for the well-order. -/
noncomputable def code : Base S ⊕ Letter σ → Cardinal.{u} := embeddingToCardinal

theorem code_injective : Function.Injective (code (σ := σ) (S := S)) :=
  embeddingToCardinal.injective

/-- The key of a monomial: the codes of the base element, then of the letters `t₁, …, tₙ`
(reading from the base). -/
noncomputable def key (w : Mono σ S) : List Cardinal.{u} :=
  code (σ := σ) (S := S) (Sum.inl w.base) :: w.word.reverse.map (fun t => code (σ := σ) (S := S) (Sum.inr t))

theorem key_length (w : Mono σ S) : (key w).length = w.deg + 1 := by simp [key, deg]

theorem key_cons (t : Letter σ) (w : Mono σ S) (h₁ h₂) :
    key (cons t w h₁ h₂) = key w ++ [code (σ := σ) (S := S) (Sum.inr t)] := by
  simp [key, cons]

theorem key_injective : Function.Injective (key (σ := σ) (S := S)) := by
  intro w w' h
  simp only [key, List.cons.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hb := Sum.inl_injective (code_injective h1)
  have hw : w.word.reverse = w'.word.reverse :=
    (List.map_injective_iff.2 fun a b hab => Sum.inr_injective (code_injective hab)) h2
  exact Mono.ext hb (List.reverse_injective hw)

/-- The position of a monomial in the order: degree, then key. -/
noncomputable def ord (w : Mono σ S) : ℕ ×ₗ List Cardinal.{u} := toLex (w.deg, key w)

theorem ord_injective : Function.Injective (ord (σ := σ) (S := S)) := fun _ _ h =>
  key_injective (congrArg (fun p => (ofLex p).2) h)

/-- The well-order on monomials: by degree, then lexicographically from the base element. -/
noncomputable instance : LinearOrder (Mono σ S) := LinearOrder.lift' ord ord_injective

theorem lt_iff {w w' : Mono σ S} :
    w < w' ↔ w.deg < w'.deg ∨ w.deg = w'.deg ∧ List.Lex (· < ·) (key w) (key w') := by
  show ord w < ord w' ↔ _
  rw [ord, ord, Prod.Lex.toLex_lt_toLex, ← List.lt_iff_lex_lt]
  rfl

instance : WellFoundedLT (Mono σ S) := ⟨by
  refine Subrelation.wf (fun {w w'} h => ?_)
    (InvImage.wf key (List.Shortlex.wf (r := (· < · : Cardinal.{u} → Cardinal.{u} → Prop))
      wellFounded_lt))
  rw [lt_iff] at h
  show List.Shortlex _ (key w) (key w')
  rw [List.shortlex_def, key_length, key_length]
  rcases h with h | ⟨h, hl⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, hl⟩⟩

theorem lt_of_deg_lt {w w' : Mono σ S} (h : w.deg < w'.deg) : w < w' := lt_iff.2 (Or.inl h)

theorem deg_le_of_le {w w' : Mono σ S} (h : w ≤ w') : w.deg ≤ w'.deg := by
  by_contra h'
  exact absurd h (not_le.2 (lt_of_deg_lt (not_le.1 h')))

theorem List.Lex.append_of_length_eq {α : Type*} {r : α → α → Prop} {l₁ l₂ : List α}
    (h : List.Lex r l₁ l₂) (hl : l₁.length = l₂.length) (a b : List α) :
    List.Lex r (l₁ ++ a) (l₂ ++ b) := by
  induction h with
  | nil => simp at hl
  | cons h ih => exact List.Lex.cons (ih (by simpa using hl))
  | rel h => exact List.Lex.rel h

/-- Left multiplication preserves the order among monomials of the same degree. -/
theorem cons_lt_cons {w w' : Mono σ S} (hd : w.deg = w'.deg) (h : w < w') (t t' : Letter σ)
    (h₁ h₂ h₁' h₂') : cons t w h₁ h₂ < cons t' w' h₁' h₂' := by
  rw [lt_iff] at h ⊢
  rcases h with h | ⟨-, h⟩
  · omega
  · refine Or.inr ⟨by simp [hd], ?_⟩
    rw [key_cons, key_cons]
    exact List.Lex.append_of_length_eq h (by rw [key_length, key_length, hd]) _ _

theorem cons_injective {t t' : Letter σ} {w w' : Mono σ S} {h₁ h₂ h₁' h₂'}
    (h : cons t w h₁ h₂ = cons t' w' h₁' h₂') : t = t' ∧ w = w' := by
  have hw := congrArg Mono.word h
  have hb := congrArg Mono.base h
  simp only [cons, List.cons.injEq] at hw hb
  exact ⟨hw.1, Mono.ext hb hw.2⟩

end Mono

end Bergman.Core
