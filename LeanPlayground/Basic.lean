import Aesop
import Mathlib.Tactic.Common
import Std.Data.HashSet
import Batteries.Tactic.PrintPrefix

def hello := "world"

inductive Palindrome : List Nat → Prop
  | nil : Palindrome []
  | singleton (n : Nat) : Palindrome [n]
  | step (n : Nat) (xs : List Nat) : Palindrome xs → Palindrome (n :: xs ++ [n])

example (h : Palindrome xs) : xs.reverse = xs := by
  induction h with
  | nil => rfl
  | singleton n => rfl
  | step n xs h ih => simp_all

inductive Alpha
  | a : Alpha
  | b : Alpha

inductive S : List Alpha → Prop
  | nil : S []
  | nest : S xs → S (.a :: xs ++ [.b])
  | app : S xs → S ys → S (xs ++ ys)

inductive T : List Alpha → Prop
  | nil : T []
  | appnest : T xs → T ys → T (xs ++ (.a :: ys ++ [.b]))


theorem t_app (h1 : T xs) (h2 : T ys) : T (xs ++ ys) := by
  induction h2 with
  | nil => simp_all
  | appnest h1 h2 ih1 ih2 =>
    have := T.appnest ih1 h2
    simp_all

example : S xs → T xs := by
  intro h
  induction h with
  | nil => exact .nil
  | nest h ih => exact .appnest .nil ih
  | app h1 h2 ih1 ih2 => exact t_app ih1 ih2

example : T xs → S xs := by
  intro h
  induction h with
  | nil => exact .nil
  | appnest h1 h2 ih1 ih2 => exact .app ih1 (.nest ih2)

def List.swap (l : List α) (i j : Fin l.length) : List α :=
  match l, i, j with
  | _, ⟨0, _⟩, ⟨0, _⟩ => l
  | x :: xs, ⟨i+1, _⟩, ⟨j+1, _⟩ => x :: xs.swap ⟨i, by simp_all⟩ ⟨j, by simp_all⟩
  | x :: xs, ⟨i+1, _⟩, ⟨0, _⟩ =>
    match xs.splitAt i with
    | (ys, z :: zs) => z :: ys ++ x :: zs
    | (ys, []) => unreachable! -- TODO: prove this is unreachable
  | x :: xs, ⟨0, _⟩, ⟨j+1, _⟩ =>
    match xs.splitAt j with
    | (ys, z :: zs) => z :: ys ++ x :: zs
    | (ys, []) => unreachable! -- TODO: prove this is unreachable

open scoped List

instance : IsTrans (List α) List.Perm := ⟨@List.Perm.trans α⟩

lemma perm_swap_head (x y : α) (xs ys : List α) : (x :: xs ++ y :: ys) ~ (y :: xs ++ x :: ys) := by
  calc x :: xs ++ y :: ys
    _ ~ x :: y :: (xs ++ ys) := by simp
    _ ~ y :: x :: (xs ++ ys) := by apply List.Perm.swap
    _ ~ y :: xs ++ x :: ys := by apply List.Perm.symm; simp

theorem perm_swap : List.Perm l (l.swap i j) := by
  induction l, i, j using List.swap.induct with
  | case1 =>
    simp_all [List.swap]
  | case2 =>
    simp_all [List.swap]
  | case3 x xs i _ _ ys z zs ih =>
    simp_all [List.swap]
    have : xs = ys ++ z :: zs := by
      obtain ⟨ihl, ihr⟩ := ih
      rw [← ihl, ← ihr]
      simp
    rw [this]
    have := perm_swap_head x z ys zs
    simp_all
  | case4 x xs i _ _ ys ih =>
    exfalso
    simp_all
    omega
  | case5 x xs j _ _ ys z zs ih =>
    simp_all [List.swap]
    have : xs = ys ++ z :: zs := by
      obtain ⟨ihl, ihr⟩ := ih
      rw [← ihl, ← ihr]
      simp
    rw [this]
    have := perm_swap_head x z ys zs
    simp_all
  | case6 x xs j _ _ ys ih =>
    exfalso
    simp_all
    omega

#eval if let some x := some 10 then x else 0

#eval ({1, 2, 3} : Std.HashSet Nat)

inductive MyList : Type u → Type u
  | nil : MyList α
  | cons (x : α) (xs : MyList α) : MyList α

#check List.rec
#check MyList.rec

#eval Float.sin 1

example (n : Nat) : (n + 1) / 2 = (if n % 2 = 1 then n + 1 else n) / 2 := by
  split <;> omega

example (n : Nat) : n / 2 = (if n % 2 = 1 then n - 1 else n) / 2 := by
  split <;> omega

structure ListBuilder (α : Type u) where
  data : List α

def ListBuilder.cons (x : α) (xs : ListBuilder α) : ListBuilder α :=
  ⟨x :: xs.data⟩

instance : CoeFun (ListBuilder α) (fun _ => α → ListBuilder α) where
  coe f := f.cons

instance : Coe (ListBuilder α) (List α) where
  coe b := b.data.reverse

def listOf : ListBuilder α := ⟨[]⟩

#eval (listOf 1 2 3   : List Nat)
#eval (listOf 1 2 3 4 : List Nat)
