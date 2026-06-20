-- Thierry Coquand. A variation of Reynolds-Hurkens Paradox.
-- https://arxiv.org/abs/2308.16726

namespace Paradox

def P (X : Type u) := X → Prop
def T (X : Type u) := P (P X)

def T.map (f : α → β) : T α → T β :=
  fun F q => F (q ∘ f)

variable {α : Type u}

variable (int : T α → α) (mat : α → T α)

theorem not_T_retract (int_mat : ∀ x, mat (int x) = x) : False :=
  let C (p : P α) (x : α) : Prop := p x → ¬(mat x p)
  let p₀ (x : α) : Prop := ∀ p : P α, C p x
  let X₀ (p : P α) : Prop := ∀ x : α, C p x
  let x₀ : α := int X₀
  have : mat x₀ = X₀ := by
    apply int_mat
  let l₁ : X₀ p₀ := fun x h => h p₀ h
  let l₂ : p₀ x₀ := fun p h h₁ => (this ▸ h₁) x₀ h h₁
  (this ▸ l₁ x₀ l₂) l₁

theorem not_T_comm (int_mat : ∀ X, mat (int X) = T.map (int ∘ mat) X) : False :=
  let δ : α → α := int ∘ mat
  have : ∀ x p, mat (δ x) p = mat x (p ∘ δ) := by
    intro x p
    dsimp [δ]
    rw [int_mat]
    rfl
  let p₀ (x : α) : Prop := ∀ p : P α, p (δ x) → ¬(mat x p)
  let X₀ (p : P α) : Prop := ∀ x : α, p x → ¬(mat x p)
  let x₀ : α := int X₀
  let s₁ (x : α) (h : p₀ x) : p₀ (δ x) :=
    fun p => this x p ▸ h (p ∘ δ)
  let s₂ (p : P α) (h : X₀ p) : X₀ (p ∘ δ) :=
    fun x => this x p ▸ h (δ x)
  let l₀ (p : P α) (h : p x₀) : ¬(X₀ p) :=
    fun h₀ => h₀ x₀ h (int_mat X₀ ▸ s₂ p h₀)
  let l₁ : X₀ p₀ := fun x h => h p₀ (s₁ x h)
  let l₂ : p₀ x₀ := fun p => int_mat X₀ ▸ l₀ (p ∘ δ)
  l₀ p₀ l₂ l₁

theorem girard
  (pi : (Type u → Type u) → Type u)
  (lam : {A : Type u → Type u} → ((x : Type u) → A x) → pi A)
  (app : {A : Type u → Type u} → pi A → (x : Type u) → A x)
  (beta : ∀ {A : Type u → Type u} (f : (x : Type u) → A x) (x : Type u), app (lam f) x = f x)
  : False :=
  let A : Type u := pi (fun X => (T X → X) → X)
  let ι {X : Type u} (f : T X → X) (a : A) : X := app a X f
  let int (u : T A) : A := lam (fun X f => f (T.map (ι f) u))
  let mat : A → T A := ι (T.map int)
  have int_mat : ∀ X, mat (int X) = T.map (int ∘ mat) X := by
    intro X
    simp_all [int, mat, ι]
    rfl
  not_T_comm int mat int_mat
