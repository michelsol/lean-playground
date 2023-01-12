
inductive CList where
| node (data : Nat) (next : CList)

def CList.data : CList → Nat | node data _ => data
def CList.next : CList → CList | node _ next => next

example (l : CList) : False :=
  l.rec λ _ _ => id

def double (x : Thunk Nat) : Nat :=
  x.get + x.get
-- #eval double ⟨λ _ => 4⟩

section
private inductive InfList (α : Type u) where
| cons (head : α) (tail : Thunk (InfList α))
end

def InfList.take {α} : Nat → InfList α → List α
  | 0,   _     => .nil
  | n + 1, .cons a as => .cons a (take n as.get)

def InfList.head {α} : InfList α → α
  | .cons a _ => a

def InfList.tail {α} : InfList α → InfList α
  | .cons _ as => as.get

unsafe def InfList.const {α} (x : α) : InfList α :=
  cons x ⟨λ _ => const x⟩
-- #eval (InfList.const 0).take 3

theorem Thunk.eq_of_getEq {α} : {a b : Thunk α} → a.get = b.get → a = b
  | ⟨_⟩, ⟨_⟩, h => congrArg _ (funext λ _ => h)

theorem InfList.coRec {α} (r : InfList α → InfList α → Prop)
  (h_head : ∀ a b : InfList α, r a b → head a = head b)
  (h_tail : ∀ a b : InfList α, r a b → r (tail a) (tail b))
  (a b : InfList α) (h : r a b)
  : a = b :=
  have h1 := h_head a b h
  have h2 := h_tail a b h
  match a, b with
  | cons a as, cons b bs =>
    have h1 : a = b := h1
    have h2 := Thunk.eq_of_getEq <| coRec r h_head h_tail as.get bs.get h2
    h2 ▸ h1 ▸ rfl
