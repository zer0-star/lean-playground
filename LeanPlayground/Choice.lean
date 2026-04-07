import Mathlib.Tactic.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Quot


#check Classical.em
#print axioms Classical.em

abbrev axiom_of_choice := ∀ {α β : Type} (f : α → β), f.Surjective → ∃ g : β → α, ∀ x, f (g x) = x

def propRel (p : Prop) {X : Type} (x y : X) : Prop := (x = y) ∨ p

theorem equiv_propRel (p : Prop) {X : Type} : Equivalence (@propRel p X) where
  refl _ := Or.inl rfl
  symm h := match h with
    | Or.inl h => Or.inl (Eq.symm h)
    | Or.inr h => Or.inr h
  trans h₁ h₂ := match h₁, h₂ with
    | Or.inl h₁, Or.inl h₂ => Or.inl (Eq.trans h₁ h₂)
    | _, Or.inr h₂ => Or.inr h₂
    | Or.inr h₁, _ => Or.inr h₁

def propSetoid (p : Prop) (X : Type) : Setoid X := ⟨propRel p, equiv_propRel p⟩

theorem diaconescu (ac : axiom_of_choice) : ∀ p, p ∨ ¬p := by
  intro p
  let s := propSetoid p Bool
  obtain ⟨g, hg⟩ := ac (Quotient.mk s) Quotient.exists_rep
  let x₁ := g ⟦true⟧
  let x₂ := g ⟦false⟧
  if h : x₁ = x₂ then
    left
    have : s true false := by
      apply Quotient.eq.mp
      rw [← hg ⟦true⟧, ← hg ⟦false⟧]
      simp_all [s, x₁, x₂]
    cases this with
    | inl h' => contradiction
    | inr h' => exact h'
  else
    right
    by_contra hp
    have : g ⟦true⟧ = g ⟦false⟧ := by
      congr 1
      apply Quotient.sound
      exact .inr hp
    simp_all

#print axioms diaconescu

abbrev axiom_of_choice' := ∀ {α : Type} {β : α → Type}, (∀ x : α, Nonempty (β x)) → Nonempty (∀ x : α, β x)

structure Nonempty' (X : Type) : Type where
  p : Nonempty X

lemma Nonempty'.eq : ∀ h₁ h₂ : Nonempty' X, h₁ = h₂ := by
  intro h₁ h₂
  cases h₁
  cases h₂
  simp

theorem diaconescu' (ac : axiom_of_choice') : ∀ p, p ∨ ¬p := by
  intro p
  let U x := x = True ∨ p
  let V x := x = False ∨ p
  have h : p → U = V := by
    intro hp
    funext x
    apply propext
    constructor
    all_goals
      intro
      right
      assumption
  have f' (X : Prop → Prop) (exX : Nonempty' (Σ' x, X x)) : Nonempty (Σ' x, X x) := exX.p
  obtain ⟨f⟩ := ac fun X => ac (f' X)
  have exU : Nonempty' (Σ' x, U x) := ⟨⟨⟨True, .inl rfl⟩⟩⟩
  have exV : Nonempty' (Σ' x, V x) := ⟨⟨⟨False, .inl rfl⟩⟩⟩
  have hu := (f U exU).snd
  have hv := (f V exV).snd
  set u := (f U exU).fst
  set v := (f V exV).fst
  have h' : u ≠ v ∨ p :=
    match hu, hv with
    | .inr h, _ => .inr h
    | _, .inr h => .inr h
    | .inl hu', .inl hv' => by
      left
      rw [hu', hv']
      trivial
  cases h' with
  | inl h' =>
    right
    intro hp
    apply h'
    have := h hp
    have : ∀ exU exV, (f U exU).fst = (f V exV).fst := by
      rw [this]
      intro exU exV
      rw [Nonempty'.eq exU exV]
    dsimp [u, v]
    exact this _ _
  | inr h' =>
    exact .inl h'


theorem ac_equiv : axiom_of_choice ↔ axiom_of_choice' := by
  constructor
  . intro ac
    intro α β h
    let f (p : Σ x, β x) := p.fst
    have f_Surjective : f.Surjective := by
      intro x
      obtain ⟨hb⟩ := h x
      use ⟨x, hb⟩
    obtain ⟨g, hg⟩ := ac f f_Surjective
    have : ∀ x, (g x).fst = x := by
      dsimp [f] at hg
      assumption
    have g' x := this x ▸ (g x).snd
    exact ⟨g'⟩
  . intro ac'
    intro α β f hf
    have hf' (y : β) : Nonempty (Σ' x : α, f x = y) := by
      obtain ⟨x, hx⟩ := hf y
      exact ⟨⟨x, hx⟩⟩
    obtain ⟨g'⟩ := ac' hf'
    let g (y : β) := (g' y).fst
    have hg (y : β) : f (g y) = y := by
      simp [(g' y).snd]
    exact ⟨g, hg⟩


