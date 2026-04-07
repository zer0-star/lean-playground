namespace Equality

inductive Id {α : Type} (a : α) : α → Type
| refl : Id a a

#check @Id.rec

def id_contr : ∀ p : (Σ x : α, Id a x) , Id p ⟨a, Id.refl⟩
  | ⟨_, Id.refl⟩ => Id.refl

def axiom_k : ∀ p : Id a a, Id p Id.refl
  | Id.refl => Id.refl

#reduce axiom_k

inductive PropSum (p q : Prop) : Type
  | inl : p → PropSum p q
  | inr : q → PropSum p q

theorem lem_eq (p : Prop) : ∀ h₁ h₂ : PropSum p (¬p), h₁ = h₂ := by
  intro h₁ h₂
  cases h₁ <;> cases h₂ <;> trivial

#print axioms lem_eq

theorem empty_eq (p q : Empty) : p = q := by
  cases p


theorem lem_eq' (p : Type u) (h : ∀ x y : p, x = y) : ∀ (h₁ h₂ : p ⊕ (p → Empty)), h₁ = h₂ := by
  intro h₁ h₂
  cases h₁ <;> cases h₂
  case inl.inl =>
    congr
    apply h
  case inl.inr hp hn =>
    exact Empty.elim $ hn hp
  case inr.inl hn hp =>
    exact Empty.elim $ hn hp
  case inr.inr =>
    congr
    funext
    apply empty_eq

#print axioms lem_eq'

end Equality
