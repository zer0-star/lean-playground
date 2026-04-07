import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Tactic.Linarith

inductive AVLTreeShape : Nat → Nat → Nat → Type
  | balanced :  AVLTreeShape n (n+1) n
  | leftHeavy : AVLTreeShape (n+1) (n+2) n
  | rightHeavy : AVLTreeShape n (n+2) (n+1)

inductive AVLTreeNode (α : Type) : Nat → Nat → Type
  | leaf : AVLTreeNode α 0 0
  | node {l : Nat} {n : Nat} {r : Nat} (v : α) (left : AVLTreeNode α l szl) (right : AVLTreeNode α r szr) (shape : AVLTreeShape l n r) : AVLTreeNode α n (szl+szr+1)

abbrev AVLTreeNode' (α : Type) (n : Nat) := Σ sz, AVLTreeNode α n sz

namespace AVLTreeNode

def height (_ : AVLTreeNode α n sz) : Nat := n

def size (_ : AVLTreeNode α n sz) : Nat := sz

def value :  AVLTreeNode α n sz → Option α
  | leaf => none
  | node v _ _ _ => some v

def contains [Ord α]  (t : AVLTreeNode α n sz) (x : α) : Bool :=
  match t with
  | leaf => false
  | node v l r _ => match compare x v with
    | .lt => l.contains x
    | .eq => true
    | .gt => r.contains x

def find? [Ord α] (t : AVLTreeNode α n sz) (x : α) : Option α :=
  match t with
  | leaf => .none
  | node v l r _ => match compare x v with
    | .lt => l.find? x
    | .eq => .some v
    | .gt => r.find? x

def rotateRight (v : α) (l : AVLTreeNode α (n+2) szl) (r : AVLTreeNode α n szr) : AVLTreeNode' α (n+2) ⊕ AVLTreeNode' α (n+3) :=
  match n, l with
  | _, node vl ll lr .balanced => .inr $ Sigma.mk _ $ node vl ll (node v lr r .leftHeavy) .rightHeavy
  | _, node vl ll lr .leftHeavy => .inl $ Sigma.mk _ $ node vl ll (node v lr r .balanced) .balanced
  | _, node vl ll (node vlr lrl lrr .balanced) .rightHeavy =>
    .inl $ Sigma.mk _ $ node vlr (node vl ll lrl .balanced) (node v lrr r .balanced) .balanced
  | _, node vl ll (node vlr lrl lrr .leftHeavy) .rightHeavy =>
    .inl $ Sigma.mk _ $ node vlr (node vl ll lrl .balanced) (node v lrr r .rightHeavy) .balanced
  | _, node vl ll (node vlr lrl lrr .rightHeavy) .rightHeavy =>
    .inl $ Sigma.mk _ $ node vlr (node vl ll lrl .leftHeavy) (node v lrr r .balanced) .balanced

def rotateLeft (v : α) (l : AVLTreeNode α n szl) (r : AVLTreeNode α (n+2) szr) : AVLTreeNode' α (n+2) ⊕ AVLTreeNode' α (n+3) :=
  match n, r with
  | _, node vr rl rr .balanced => .inr $ Sigma.mk _ $ node vr (node v l rl .rightHeavy) rr .leftHeavy
  | _, node vr rl rr .rightHeavy => .inl $ Sigma.mk _ $ node vr (node v l rl .balanced) rr .balanced
  | _, node vr (node vrl rll rlr .balanced) rr .leftHeavy =>
    .inl $ Sigma.mk _ $ node vrl (node v l rll .balanced) (node vr rlr rr .balanced) .balanced
  | _, node vr (node vrl rll rlr .rightHeavy) rr .leftHeavy =>
    .inl $ Sigma.mk _ $ node vrl (node v l rll .leftHeavy) (node vr rlr rr .balanced) .balanced
  | _, node vr (node vrl rll rlr .leftHeavy) rr .leftHeavy =>
    .inl $ Sigma.mk _ $ node vrl (node v l rll .balanced) (node vr rlr rr .rightHeavy) .balanced

def insert [Ord α] (t : AVLTreeNode α n sz) (x : α) : AVLTreeNode' α n ⊕ AVLTreeNode' α (n+1) :=
  match t with
  | leaf => .inr $ Sigma.mk _ $ node x leaf leaf .balanced
  | node v l r s =>
    match compare x v with
    | .eq => .inl $ Sigma.mk _ $ node x l r s
    | .lt =>
      match s with
      | .balanced =>
        match l.insert x with
        | .inl ⟨_, l'⟩ => .inl $ Sigma.mk _ $ node v l' r .balanced
        | .inr ⟨_, l'⟩ => .inr $ Sigma.mk _ $ node v l' r .leftHeavy
      | .leftHeavy =>
        match l.insert x with
        | .inl ⟨_, l'⟩ => .inl $ Sigma.mk _ $ node v l' r .leftHeavy
        | .inr ⟨_, l'⟩ => rotateRight v l' r
      | .rightHeavy =>
        match l.insert x with
        | .inl ⟨_, l'⟩ => .inl $ Sigma.mk _ $ node v l' r .rightHeavy
        | .inr ⟨_, l'⟩ => .inl $ Sigma.mk _ $ node v l' r .balanced
    | .gt =>
      match s with
      | .balanced =>
        match r.insert x with
        | .inl ⟨_, r'⟩ => .inl $ Sigma.mk _ $ node v l r' .balanced
        | .inr ⟨_, r'⟩ => .inr $ Sigma.mk _ $ node v l r' .rightHeavy
      | .leftHeavy =>
        match r.insert x with
        | .inl ⟨_, r'⟩ => .inl $ Sigma.mk _ $ node v l r' .leftHeavy
        | .inr ⟨_, r'⟩ => .inl $ Sigma.mk _ $ node v l r' .balanced
      | .rightHeavy =>
        match r.insert x with
        | .inl ⟨_, r'⟩ => .inl $ Sigma.mk _ $ node v l r' .rightHeavy
        | .inr ⟨_, r'⟩ => rotateLeft v l r'

def isLeaf : AVLTreeNode α n sz → Bool
  | leaf => true
  | _ => false

def isNode : AVLTreeNode α n sz → Bool
  | leaf => false
  | _ => true

theorem node_height {t : AVLTreeNode α n sz} : t.isNode → n ≠ 0 := by
  intro h
  cases t with
  | leaf => contradiction
  | node _ _ _ s => cases s <;> exact Nat.succ_ne_zero _

def max : AVLTreeNode α (n+1) sz → α
  | node v _ r _ => match r with
    | leaf => v
    | r@(node _ _ _ s) =>
      match s with
      | .balanced => max r
      | .leftHeavy => max r
      | .rightHeavy => max r

def min : AVLTreeNode α (n+1) sz → α
  | node v l _ _ => match l with
    | leaf => v
    | l@(node _ _ _ s) =>
      match s with
      | .balanced => min l
      | .leftHeavy => min l
      | .rightHeavy => min l

theorem size_lower_bound {t : AVLTreeNode α n sz} : sz ≥ Nat.fib (n+1) - 1 := by
  induction t with
  | leaf => simp [size]
  | node _ l r s ihl ihr =>
    cases s
    all_goals
      rename_i n _
      simp [size]
      rw [Nat.fib_add_two]
      have := @Nat.fib_le_fib_succ n
      omega

lemma pow_plus_pow_succ (n : Nat) : 2 ^ n + 2 ^ (n+1) ≤ 2 ^ (n+2) :=
  calc _ ≤ 2 ^ (n+1) + 2 ^ (n+1) := Nat.add_le_add_right (pow_le_pow_right₀ (by trivial) (Nat.le_succ _)) _
       _ = 2 ^ (n+1) * 2 := by rw [Nat.mul_two]
       _ = 2 ^ (n+2) := by trivial

theorem size_upper_bound {t : AVLTreeNode α n sz} : sz ≤ 2 ^ n - 1 := by
  induction t with
  | leaf => simp [size]
  | node _ l r s ihl ihr =>
    cases s
    all_goals
      rename_i n _
      have : 1 ≤ 2 ^ n := one_le_pow₀ (by trivial)
      have := pow_plus_pow_succ n
      omega

def splitMax (t : AVLTreeNode α (n+1) sz) : α × (AVLTreeNode' α n ⊕ AVLTreeNode' α (n+1)) :=
  match n, t with
  | _, node v l leaf s => by cases s <;> exact (v, .inl $ Sigma.mk _ l)
  | _, node v l r@(node _ _ _ s') .balanced => by
    cases s' <;> exact
      match r.splitMax with
      | (m, .inl ⟨_, r'⟩) => (m, .inr $ Sigma.mk _ $ node v l r' .leftHeavy)
      | (m, .inr ⟨_, r'⟩) => (m, .inr $ Sigma.mk _ $ node v l r' .balanced)
  | _, node v l r@(node _ _ _ s') .leftHeavy => by
    cases s' <;> exact
      match r.splitMax with
      | (m, .inl ⟨_, r'⟩) => (m, rotateRight v l r')
      | (m, .inr ⟨_, r'⟩) => (m, .inr $ Sigma.mk _ $ node v l r' .leftHeavy)
  | _, node v l r@(node _ _ _ s') .rightHeavy => by
    cases s' <;> exact
      match r.splitMax with
      | (m, .inl ⟨_, r'⟩) => (m, .inl $ Sigma.mk _ $ node v l r' .balanced)
      | (m, .inr ⟨_, r'⟩) => (m, .inr $ Sigma.mk _ $ node v l r' .rightHeavy)

def delete [Ord α] (t : AVLTreeNode α (n+1) sz) (x : α) : AVLTreeNode' α n ⊕ AVLTreeNode' α (n+1) :=
  match n, t with
  | _, node v l r .balanced =>
    match compare x v with
    | .eq =>
      match l with
      | leaf => .inl $ Sigma.mk _ r
      | l@(node _ _ _ s) =>
        by cases s <;> exact
          match l.splitMax with
          | (m, .inl ⟨_, l'⟩) => .inr $ Sigma.mk _ $ node m l' r .rightHeavy
          | (m, .inr ⟨_, l'⟩) => .inr $ Sigma.mk _ $ node m l' r .balanced
    | .lt =>
      match l with
      | leaf => .inr $ Sigma.mk _ $ node v leaf r .balanced
      | l@(node _ _ _ s) =>
        by cases s <;> exact
          match l.delete x with
          | .inl ⟨_, l'⟩ => .inr $ Sigma.mk _ $ node v l' r .rightHeavy
          | .inr ⟨_, l'⟩ => .inr $ Sigma.mk _ $ node v l' r .balanced
    | .gt =>
      match r with
      | leaf => .inr $ Sigma.mk _ $ node v l leaf .balanced
      | r@(node _ _ _ s) =>
        by cases s <;> exact
          match r.delete x with
          | .inl ⟨_, r'⟩ => .inr $ Sigma.mk _ $ node v l r' .leftHeavy
          | .inr ⟨_, r'⟩ => .inr $ Sigma.mk _ $ node v l r' .balanced
  | _, node v l r .rightHeavy =>
    match compare x v with
    | .eq =>
      match l with
      | leaf => .inl $ Sigma.mk _ r
      | l@(node _ _ _ s) =>
        by cases s <;> exact
          match l.splitMax with
          | (m, .inl ⟨_, l'⟩) => rotateLeft m l' r
          | (m, .inr ⟨_, l'⟩) => .inr $ Sigma.mk _ $ node m l' r .rightHeavy
    | .lt =>
      match l with
      | leaf => .inr $ Sigma.mk _ $ node v leaf r .rightHeavy
      | l@(node _ _ _ s) =>
        by cases s <;> exact
          match l.delete x with
          | .inl ⟨_, l'⟩ => rotateLeft v l' r
          | .inr ⟨_, l'⟩ => .inr $ Sigma.mk _ $ node v l' r .rightHeavy
    | .gt =>
      match r.delete x with
      | .inl ⟨_, r'⟩ => .inl $ Sigma.mk _ $ node v l r' .balanced
      | .inr ⟨_, r'⟩ => .inr $ Sigma.mk _ $ node v l r' .rightHeavy
  | _, node v l r .leftHeavy =>
    match compare x v with
    | .eq =>
      match l.splitMax with
      | (m, .inl ⟨_, l'⟩) => .inl $ Sigma.mk _ $ node m l' r .balanced
      | (m, .inr ⟨_, l'⟩) => .inr $ Sigma.mk _ $ node m l' r .leftHeavy
    | .lt =>
      match l.delete x with
      | .inl ⟨_, l'⟩ => .inl $ Sigma.mk _ $ node v l' r .balanced
      | .inr ⟨_, l'⟩ => .inr $ Sigma.mk _ $ node v l' r .leftHeavy
    | .gt =>
      match r with
      | leaf => .inr $ Sigma.mk _ $ node v l leaf .leftHeavy
      | r@(node _ _ _ s) =>
        by cases s <;> exact
          match r.delete x with
          | .inl ⟨_, r'⟩ => rotateRight v l r'
          | .inr ⟨_, r'⟩ => .inr $ Sigma.mk _ $ node v l r' .leftHeavy

def kth (t : AVLTreeNode α n sz) (k : Nat) (h : k < sz) : α :=
  match t with
  | node v l r _ =>
    if h' : k < l.size then l.kth k h'
    else if h'' : k = l.size then v
    else r.kth (k - l.size - 1) $ by
      have : l.size + 1 ≤ k := by
        omega
      have := Nat.sub_lt_sub_right this h
      simpa [size]

def indexOf [Ord α] (t : AVLTreeNode α n sz) (x : α) : Nat :=
  match t with
  | leaf => 0
  | node v l r _ =>
    match compare x v with
    | .lt => l.indexOf x
    | .eq => l.size
    | .gt => l.size + 1 + r.indexOf x

end AVLTreeNode

structure AVLTree (α : Type) : Type where
  {n sz : Nat}
  root : AVLTreeNode α n sz

namespace AVLTree

def empty {α : Type} : AVLTree α := ⟨.leaf⟩

def height (t : AVLTree α) : Nat := t.root.height

def size (t : AVLTree α) : Nat := t.root.size

def value (t : AVLTree α) : Option α := t.root.value

def contains [Ord α] (t : AVLTree α) (x : α) : Bool := t.root.contains x

def find? [Ord α] (t : AVLTree α) (x : α) : Option α := t.root.find? x

def max [Ord α] (t : AVLTree α) : Option α :=
  match t with
  | @mk _ _ _ .leaf => none
  | ⟨t@(.node v _ _ s)⟩ =>
    by cases s <;> exact some t.max

def min [Ord α] (t : AVLTree α) : Option α :=
  match t with
  | @mk _ _ _ .leaf => none
  | ⟨t@(.node v _ _ s)⟩ =>
    by cases s <;> exact some t.min

def insert [Ord α] (t : AVLTree α) (x : α) : AVLTree α :=
  match t.root.insert x with
  | .inl ⟨_, r⟩ => ⟨r⟩
  | .inr ⟨_, r⟩ => ⟨r⟩

def delete [Ord α] (t : AVLTree α) (x : α) : AVLTree α :=
  match t.n, t.sz, t.root with
  | _, _, .leaf => ⟨.leaf⟩
  | _, _, t@(.node _ _ _ s) =>
    by cases s <;> exact
      match t.delete x with
      | .inl ⟨_, t'⟩ => ⟨t'⟩
      | .inr ⟨_, t'⟩ => ⟨t'⟩

def kth (t : AVLTree α) (k : Nat) : Option α :=
  if h : k < t.size
    then some $ t.root.kth k h
    else none

def indexOf [Ord α] (t : AVLTree α) (x : α) : Nat := t.root.indexOf x

instance : Inhabited (AVLTree α) where
  default := empty

instance : EmptyCollection (AVLTree α) where
  emptyCollection := empty

instance : Singleton α (AVLTree α) where
  singleton x := ⟨.node x .leaf .leaf .balanced⟩

instance [Ord α] : Insert α (AVLTree α) where
  insert e s := s.insert e

instance [Ord α] : LawfulSingleton α (AVLTree α) where
  insert_empty_eq _ := rfl

end AVLTree
