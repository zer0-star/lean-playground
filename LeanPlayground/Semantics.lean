import Aesop
import Batteries.Tactic.PrintPrefix
import Mathlib.Tactic.Common
import Mathlib.Data.Set.Basic

abbrev vname := String

abbrev state := vname → Nat

inductive Aexp : Type
  | num : Nat → Aexp
  | var : vname → Aexp
  | plus : Aexp → Aexp → Aexp
  deriving Repr

inductive Bexp : Type
  | bool : Bool → Bexp
  | less : Aexp → Aexp → Bexp
  | not : Bexp → Bexp
  | and : Bexp → Bexp → Bexp
  deriving Repr

def Aexp.eval (s : state) : Aexp → Nat
  | Aexp.num n => n
  | Aexp.var x => s x
  | Aexp.plus a₁ a₂ => Aexp.eval s a₁ + Aexp.eval s a₂

def Bexp.eval (s : state) : Bexp → Bool
  | Bexp.bool b => b
  | Bexp.less a₁ a₂ => a₁.eval s < a₂.eval s
  | Bexp.not b => !b.eval s
  | Bexp.and b₁ b₂ => b₁.eval s && b₂.eval s

def state.update (s : state) (x : vname) (n : Nat) : state :=
  λ y => if x = y then n else s y

namespace Aexp

@[simp, grind =]
lemma eval_num (s : state) (n : Nat) : (num n).eval s = n := rfl

@[simp, grind =]
lemma eval_var (s : state) (x : vname) : (var x).eval s = s x := rfl

@[simp, grind =]
lemma eval_plus (s : state) (a₁ a₂ : Aexp) : (plus a₁ a₂).eval s = a₁.eval s + a₂.eval s := rfl

def simpConst : Aexp → Aexp
  | num n => num n
  | var x => var x
  | plus a₁ a₂ =>
    match simpConst a₁, simpConst a₂ with
    | num n₁, num n₂ => num (n₁ + n₂)
    | a₁', a₂' => plus a₁' a₂'

lemma eval_simpConst (a : Aexp) : a.simpConst.eval s = a.eval s := by
  induction a with
  | num n => rfl
  | var x => rfl
  | plus =>
    unfold simpConst
    split <;> simp_all

def plus' : Aexp → Aexp → Aexp
  | num n₁, num n₂ => num (n₁ + n₂)
  | num n, a => if n = 0 then a else plus (num n) a
  | a, num n => if n = 0 then a else plus a (num n)
  | a₁, a₂ => plus a₁ a₂

@[simp, grind =]
lemma eval_plus' (s : state) (a₁ a₂ : Aexp) : (plus' a₁ a₂).eval s = a₁.eval s + a₂.eval s := by
  unfold plus'
  aesop

def simp : Aexp → Aexp
  | num n => num n
  | var x => var x
  | plus a₁ a₂ => plus' (simp a₁) (simp a₂)

@[simp, grind =]
theorem eval_simp (a : Aexp) : a.simp.eval s = a.eval s := by
  induction a with
  | num n => rfl
  | var x => rfl
  | plus =>
    simp_all [simp]

def optimal : Aexp → Bool
  | num _ => true
  | var _ => true
  | plus (num _) (num _) => false
  | plus a₁ a₂ => a₁.optimal && a₂.optimal

theorem optimal_simpConst (a : Aexp) : a.simpConst.optimal = true := by
  induction a with
  | num n => rfl
  | var x => rfl
  | plus a₁ a₂ ih₁ ih₂ =>
    unfold simpConst
    split <;> simp_all [optimal]

@[simp, grind =]
def fullSimp (a : Aexp) : Aexp :=
  let rec aux : Aexp → Nat × List vname
    | num m => (m, [])
    | var x => (0, [x])
    | plus a₁ a₂ =>
      let (n₁, vs₁) := aux a₁
      let (n₂, vs₂) := aux a₂
      (n₁ + n₂, vs₁ ++ vs₂)
  let (n, vs) := aux a
  vs.map var |>.foldl plus' (num n)

@[simp, grind =]
lemma eval_sum (a : Aexp) (as : List Aexp) : (as.foldl plus' a).eval s = a.eval s + (as.map (eval s)).sum := by
  induction as generalizing a with
  | nil => rfl
  | cons a' as ih =>
    simp +arith [*]

@[simp, grind =]
theorem fullSimp_correct (a : Aexp) : a.fullSimp.eval s = a.eval s := by
  induction a with
  | num n => rfl
  | var x => rfl
  | plus a₁ a₂ ih₁ ih₂ =>
    simp
    rw [← ih₁, ← ih₂]
    simp [fullSimp, fullSimp.aux, eval_sum]
    omega

def subst (a : Aexp) (x : vname) (b : Aexp) : Aexp :=
  match a with
  | num n => num n
  | var y => if x = y then b else var y
  | plus a₁ a₂ => plus (a₁.subst x b) (a₂.subst x b)

@[simp]
lemma subst_num (n : Nat) (x : vname) (b : Aexp) : (num n).subst x b = num n := rfl

@[simp]
lemma subst_var (y x : vname) (b : Aexp) : (var y).subst x b = if x = y then b else var y := rfl

@[simp]
lemma subst_plus (a₁ a₂ : Aexp) (x : vname) (b : Aexp) : (plus a₁ a₂).subst x b = plus (a₁.subst x b) (a₂.subst x b) := rfl

lemma subst_eval (a : Aexp) (x : vname) (b : Aexp) : (a.subst x b).eval s = a.eval (s.update x (b.eval s)) := by
  induction a with
  | num n => rfl
  | var y =>
    simp [state.update]
    apply apply_ite
  | plus a₁ a₂ ih₁ ih₂ =>
    simp_all

lemma subst_congr (a a₁ a₂ : Aexp) (h : a₁.eval s = a₂.eval s) : (a.subst x a₁).eval s = (a.subst x a₂).eval s := by
  simp [subst_eval]
  rw [h]

end Aexp

inductive Lexp : Type
  | num : Nat → Lexp
  | var : vname → Lexp
  | plus : Lexp → Lexp → Lexp
  | let_ : vname → Lexp → Lexp → Lexp

namespace Lexp

def eval (s : state) : Lexp → Nat
  | num n => n
  | var x => s x
  | plus a₁ a₂ => a₁.eval s + a₂.eval s
  | let_ x a b => eval (s.update x (a.eval s)) b

def inline : Lexp → Aexp
  | num n => Aexp.num n
  | var x => Aexp.var x
  | plus a₁ a₂ => Aexp.plus (inline a₁) (inline a₂)
  | let_ x a b => (inline b).subst x (inline a)

theorem inline_correct (l : Lexp) : l.eval s = l.inline.eval s := by
  induction l generalizing s with
  | num n => rfl
  | var x => rfl
  | plus a₁ a₂ ih₁ ih₂ =>
    simp_all [eval, inline]
  | let_ x a b ih₁ ih₂ =>
    simp_all [eval, inline]
    rw [Aexp.subst_eval]

end Lexp

namespace Bexp

@[simp]
lemma eval_bool (s : state) (b : Bool) : (bool b).eval s = b := rfl

@[simp]
lemma eval_less (s : state) (a₁ a₂ : Aexp) : (less a₁ a₂).eval s = ↑(a₁.eval s < a₂.eval s) := rfl

@[simp]
lemma eval_not (s : state) (b : Bexp) : (not b).eval s = !b.eval s := rfl

@[simp]
lemma eval_and (s : state) (b₁ b₂ : Bexp) : (and b₁ b₂).eval s = (b₁.eval s && b₂.eval s) := rfl

def not' : Bexp → Bexp
  | bool b => bool (!b)
  | not b => b
  | b => not b

def and' : Bexp → Bexp → Bexp
  | bool true, b => b
  | b, bool true => b
  | bool false, _ => bool false
  | _, bool false => bool false
  | b₁, b₂ => and b₁ b₂

def less' : Aexp → Aexp → Bexp
  | .num n₁, .num n₂ => bool (n₁ < n₂)
  | a₁, a₂ => less a₁ a₂

def simp : Bexp → Bexp
  | bool b => bool b
  | less a₁ a₂ => less' (Aexp.simp a₁) (Aexp.simp a₂)
  | not b => not' (simp b)
  | and b₁ b₂ => and' (simp b₁) (simp b₂)

def eq (a₁ a₂ : Aexp) : Bexp := and (not (less a₁ a₂)) (not (less a₂ a₁))

def le (a₁ a₂ : Aexp) : Bexp := not (less a₂ a₁)

lemma eval_eq (a₁ a₂ : Aexp) (s : state) : (eq a₁ a₂).eval s = (a₁.eval s = a₂.eval s) := by
  simp [eq]
  omega

lemma eval_le (a₁ a₂ : Aexp) (s : state) : (le a₁ a₂).eval s = (a₁.eval s ≤ a₂.eval s) := by
  simp [le]

end Bexp

inductive Com : Type
  | skip : Com
  | assign : vname → Aexp → Com
  | seq : Com → Com → Com
  | «if» : Bexp → Com → Com → Com
  | while : Bexp → Com → Com
  deriving Repr

infix:65 " ≔ " => Com.assign
infixl:60 " ;; " => Com.seq

#eval "x" ≔ .plus (.var "y") (.num 1);; "y" ≔ .num 2

namespace Com

abbrev config := Com × state

@[aesop 70%]
inductive big_step : Com → state → state → Prop
  | skip : big_step .skip s s
  | assign : big_step (x ≔ a) s (s.update x (a.eval s))
  | seq : big_step c₁ s₁ s₂ → big_step c₂ s₂ s₃ → big_step (c₁ ;; c₂) s₁ s₃
  | if_true (h : b.eval s = true) : big_step c₁ s t → big_step (.if b c₁ c₂) s t
  | if_false (h : b.eval s = false) : big_step c₂ s t → big_step (.if b c₁ c₂) s t
  | while_false (h : b.eval s = false) : big_step (.while b c) s s
  | while_true (h : b.eval s = true) : big_step c s s' → big_step (.while b c) s' s'' → big_step (.while b c) s s''

notation "(" c:55 ", " s:55 ")" " ⊢ " t:55 => big_step c s t

attribute [simp] big_step.skip big_step.assign big_step.seq big_step.if_true big_step.if_false big_step.while_false big_step.while_true


lemma com_assoc (c₁ c₂ c₃ : Com) (s : state) : (c₁ ;; c₂ ;; c₃, s) ⊢ t ↔ (c₁ ;; (c₂ ;; c₃), s) ⊢ t := by
  constructor
  . intro h
    let .seq (.seq h₁ h₂) h₃ := h
    exact .seq h₁ (.seq h₂ h₃)
  . intro h
    let .seq h₁ (.seq h₂ h₃) := h
    exact .seq (.seq h₁ h₂) h₃

abbrev equiv (c₁ c₂ : Com) := ∀ s t, (c₁, s) ⊢ t ↔ (c₂, s) ⊢ t

infix:50 " ∼ " => equiv

instance : IsEquiv Com equiv where
  refl _ _ _ := Iff.rfl
  symm _ _ h s t := Iff.symm (h s t)
  trans _ _ _ h₁ h₂ s t := Iff.trans (h₁ s t) (h₂ s t)

lemma while_unfold (b : Bexp) (c : Com) : .while b c ∼ .if b (c ;; .while b c) .skip := by
  intro s t
  constructor
  . intro h
    cases h with
    | while_false h => exact .if_false h .skip
    | while_true h h₁ h₂ =>
      apply big_step.if_true
      . assumption
      . exact big_step.seq h₁ h₂
  . intro h
    cases h with
    | if_false h h' =>
      cases h'
      exact .while_false h
    | if_true h h' =>
      cases h'
      apply big_step.while_true h <;> assumption

@[simp]
lemma if_self {b : Bexp} {c : Com} : .if b c c ∼ c := by
  intro s t
  constructor
  . intro h
    cases h <;> assumption
  . intro h
    cases h' : b.eval s <;> simp_all

@[simp]
lemma while_cong {b : Bexp} {c c' : Com} (hc : c ∼ c') : .while b c ∼ .while b c' := by
  intro s t
  constructor
  . intro h
    generalize hw : Com.while b c = x at h
    induction h
    case while_false h =>
      injection hw
      simp_all
    case while_true h h₁ h₂ ih₁ ih₂ =>
      injection hw
      simp_all
      exact big_step.while_true h h₁ ih₂
    all_goals contradiction
  . intro h
    generalize hw : Com.while b c' = x at h
    induction h
    case while_false h =>
      injection hw
      simp_all
    case while_true h h₁ h₂ ih₁ ih₂ =>
      injection hw
      simp_all
      rw [← hc] at h₁
      exact big_step.while_true h h₁ ih₂
    all_goals contradiction

@[simp]
lemma if_cong {b : Bexp} {c₁ c₂ c₁' c₂' : Com} (h₁ : c₁ ∼ c₁') (h₂ : c₂ ∼ c₂') : .if b c₁ c₂ ∼ .if b c₁' c₂' := by
  intro s t
  constructor
  . intro h
    cases h <;> simp_all
  . intro h
    cases h <;> simp_all

@[simp]
lemma seq_cong {c₁ c₂ c₁' c₂'} (h₁ : c₁ ∼ c₁') (h₂ : c₂ ∼ c₂') : c₁ ;; c₂ ∼ c₁' ;; c₂' := by
  intro s t
  constructor
  . intro h
    cases h
    apply big_step.seq <;> simp_all
    assumption
    assumption
  . intro h
    cases h with
    | seq h h' =>
      replace h := h₁ s _ |>.mpr h
      replace h' := h₂ _ t |>.mpr h'
      apply big_step.seq <;> assumption

@[simp]
lemma seq_skip_left (c : Com) : .skip ;; c ∼ c := by
  intro s t
  constructor
  . intro h
    cases h with
    | seq h h' =>
      cases h
      assumption
  . intro h
    apply big_step.seq
    exact big_step.skip
    assumption

@[simp]
lemma seq_skip_right (c : Com) : c ;; .skip ∼ c := by
  intro s t
  constructor
  . intro h
    cases h with
    | seq h h' =>
      cases h'
      assumption
  . intro h
    apply big_step.seq
    assumption
    exact big_step.skip

theorem big_step.deterministic (c : Com) : (c, s) ⊢ t → (c, s) ⊢ t' → t = t' := by
  intro h h'
  induction h generalizing t' with
  | skip => cases h'; rfl
  | assign => cases h'; rfl
  | seq h₁ h₂ ih₁ ih₂ =>
    cases h' with
    | seq h₁' h₂' =>
      have := ih₁ h₁'
      rw [← this] at h₂'
      have := ih₂ h₂'
      assumption
  | if_true h h₁ ih =>
    cases h' with
    | if_true h' h₁' =>
      exact ih h₁'
    | if_false h' h₂' =>
      simp_all
  | if_false h h₂ ih =>
    cases h' with
    | if_true h' h₁' =>
      simp_all
    | if_false h' h₂' =>
      exact ih h₂'
  | while_false h =>
    cases h' <;> simp_all
  | while_true h h₁ h₂ ih₁ ih₂ =>
    cases h' with
    | while_false h' =>
      simp_all
    | while_true h' h₁' h₂' =>
      have := ih₁ h₁'
      rw [← this] at h₂'
      exact ih₂ h₂'


@[aesop 70%]
inductive small_step : Com → state → Com → state → Prop
  | assign : small_step (x ≔ a) s .skip (s.update x (a.eval s))
  | seq1 : small_step (skip ;; c) s c s
  | seq2 : small_step c s c' s' → small_step (c ;; c'') s (c' ;; c'') s'
  | if_true (h : b.eval s = true) : small_step (.if b c₁ c₂) s c₁ s
  | if_false (h : b.eval s = false) : small_step (.if b c₁ c₂) s c₂ s
  | while : small_step (.while b c) s (.if b (c ;; .while b c) .skip) s

attribute [simp] small_step.assign small_step.seq1 small_step.seq2 small_step.if_true small_step.if_false small_step.while

notation "(" c:55 ", " s:55 ")" " ⊢ " "(" c':55 ", " s':55 ")" => small_step c s c' s'

@[aesop 70%]
inductive small_steps : Com → state → Com → state → Prop
  | refl : small_steps c s c s
  | step : small_step c s c' s' → small_steps c' s' c'' s'' → small_steps c s c'' s''

attribute [simp] small_steps.refl small_steps.step

notation "(" c:55 ", " s:55 ")" " ⊢* " "(" c':55 ", " s':55 ")" => small_steps c s c' s'

lemma small_steps.trans (h : (c, s) ⊢* (c', s')) (h' : (c', s') ⊢* (c'', s'')) : (c, s) ⊢* (c'', s'') := by
  induction h with
  | refl => assumption
  | step h₁ h₂ ih => exact small_steps.step h₁ (ih h')

lemma small_steps.single (h : (c, s) ⊢ (c', s')) : (c, s) ⊢* (c', s') := by
  exact small_steps.step h small_steps.refl

lemma small_step.deterministic (h : (c, s) ⊢ (c₁, s₁)) (h' : (c, s) ⊢ (c₂, s₂)) : c₁ = c₂ ∧ s₁ = s₂ := by
  induction h generalizing c₂ s₂ with
  | assign => cases h'; simp_all
  | seq1 =>
    cases h'
    . trivial
    . contradiction
  | seq2 h ih =>
    cases h' with
    | seq1 => contradiction
    | seq2 h' =>
      have := ih h'
      simp_all
  | if_true h =>
    cases h' with
    | if_true h' => trivial
    | if_false h' => simp_all
  | if_false h =>
    cases h' with
    | if_true h' => simp_all
    | if_false h' => trivial
  | «while» =>
    cases h' with
    | «while» => trivial

lemma small_steps.seq_left (h : (c, s) ⊢* (c', s')) : (c ;; c₁, s) ⊢* (c' ;; c₁, s') := by
  induction h with
  | refl => exact small_steps.refl
  | step h₁ h₂ ih =>
    exact small_steps.step (.seq2 h₁) ih

lemma big_to_small : (c, s) ⊢ t → (c, s) ⊢* (.skip, t) := by
  intro h
  induction h with
  | skip => exact small_steps.refl
  | assign => exact small_steps.single small_step.assign
  | seq h₁ h₂ ih₁ ih₂ =>
    apply small_steps.trans
    exact ih₁.seq_left
    exact small_steps.step .seq1 ih₂
  | if_true h h₁ ih =>
    exact small_steps.step (.if_true h) ih
  | if_false h h₂ ih =>
    exact small_steps.step (.if_false h) ih
  | while_false h =>
    apply small_steps.step .while
    apply small_steps.single
    exact small_step.if_false h
  | while_true h h₁ h₂ ih₁ ih₂ =>
    apply small_steps.step .while
    apply small_steps.step (.if_true h)
    apply small_steps.trans
    exact ih₁.seq_left
    exact small_steps.step .seq1 ih₂

lemma big_step.cons_small_step : (c, s) ⊢ (c', s') → (c', s') ⊢ t → (c, s) ⊢ t := by
  intro h h'
  induction h generalizing t with
  | assign => cases h'; exact big_step.assign
  | seq1 =>
    apply big_step.seq
    . exact big_step.skip
    . exact h'
  | seq2 h ih =>
    cases h' with
    | seq h₁ h₂ =>
      apply big_step.seq
      . exact ih h₁
      . exact h₂
  | if_true h =>
    simp_all
  | if_false h =>
    simp_all
  | «while» =>
    cases h' with
    | if_true h' h₁ =>
      cases h₁ with
      | seq h₁ h₂ =>
        exact big_step.while_true h' h₁ h₂
    | if_false h' h₂ =>
      cases h₂
      exact big_step.while_false h'

lemma small_to_big : (c, s) ⊢* (.skip, t) → (c, s) ⊢ t := by
  intro h
  generalize hw : Com.skip = x at h
  induction h with
  | refl =>
    subst hw
    simp
  | step h h' ih =>
    subst hw
    simp_all
    exact big_step.cons_small_step h ih

theorem big_iff_small : (c, s) ⊢ t ↔ (c, s) ⊢* (.skip, t) := by
  constructor
  . exact big_to_small
  . exact small_to_big

def final (c : Com) (s : state) : Prop := ¬∃ c' s', (c, s) ⊢ (c', s')

lemma small_step.progress : c ≠ .skip → ∃ c' s', (c, s) ⊢ (c', s') := by
  intro h
  induction c with
  | skip => contradiction
  | assign =>
    use .skip, ?_
    exact small_step.assign
  | seq c₁ c₂ ih₁ ih₂ =>
    cases c₁ with
    | skip =>
      use c₂, ?_
      exact small_step.seq1
    | _ =>
      obtain ⟨c', s', h⟩ := ih₁ (fun h' => by injection h')
      use c' ;; c₂, s'
      exact small_step.seq2 h
  | «if» b c₁ c₂ ih₁ ih₂ =>
    if h : b.eval s = true then
      use c₁, ?_
      exact small_step.if_true h
    else
      have : b.eval s = false := by simp [h]
      use c₂, ?_
      exact small_step.if_false this
  | «while» b c ih =>
    use ?_, ?_
    exact small_step.while

theorem final_iff_skip : final c s ↔ c = .skip := by
  constructor
  . intro h
    cases c
    . rfl
    all_goals
      exfalso
      apply h
      exact small_step.progress (fun h => by injection h)
  . intro h
    rw [h]
    intro ⟨c', s', h'⟩
    cases h'

lemma bigstep_iff_final (c : Com) : (∃ t, (c, s) ⊢ t) ↔ (∃ c' s', (c, s) ⊢* (c', s') ∧ final c' s') := by
  simp [big_iff_small, final_iff_skip]

def assigned : Com → Set vname
  | .skip => {}
  | x ≔ _ => {x}
  | c₁ ;; c₂ => assigned c₁ ∪ assigned c₂
  | .if _ c₁ c₂ => assigned c₁ ∪ assigned c₂
  | .while _ c => assigned c

lemma not_assigned : x ∉ c.assigned → (c, s) ⊢ t → s x = t x := by
  intro hx h
  induction h generalizing x with
  | skip => rfl
  | assign =>
    simp_all [assigned, state.update]
    intros
    solve_by_elim
  | seq h₁ h₂ ih₁ ih₂ =>
    simp_all [assigned]
  | if_true h h₁ ih =>
    simp_all [assigned]
  | if_false h h₂ ih =>
    simp_all [assigned]
  | while_false h =>
    simp_all [assigned]
  | while_true h h₁ h₂ ih₁ ih₂ =>
    simp_all [assigned]

def like_skip : Com → Prop
  | .skip => true
  | x ≔ a => false
  | c₁ ;; c₂ => like_skip c₁ ∧ like_skip c₂
  | .if _ c₁ c₂ => like_skip c₁ ∧ like_skip c₂
  | .while b c => ∀ s, ¬b.eval s

lemma equiv_like_skip : like_skip c → c ∼ .skip := by
  intro h
  induction c with
  | skip => exact Std.Refl.refl _
  | assign => contradiction
  | seq c₁ c₂ ih₁ ih₂ =>
    simp_all [like_skip]
    transitivity
    exact seq_cong ih₁ ih₂
    exact seq_skip_right .skip
  | «if» b c₁ c₂ ih₁ ih₂ =>
    simp_all [like_skip]
    transitivity
    exact if_cong ih₁ ih₂
    exact if_self
  | «while» b c ih =>
    simp_all [like_skip]
    intro s t
    constructor
    . intro h'
      cases h' with
      | while_false => simp
      | while_true => simp_all only [Bool.false_eq_true]
    . intro h'
      cases h'
      simp_all
