
def pi (A : Type → Type) : Type 1 := (x : Type) → A x
def lam {A : Type → Type} (f : (x : Type) → A x) : pi A := λ x => f x
def app {A : Type → Type} (f : pi A) (x : Type) : A x := f x
def beta {A : Type → Type} (f : (x : Type) → A x) (x : Type) : app (lam f) x = f x := rfl

def Set (X : Type) := X → Prop
def Set.Mem (a : α) (s : Set α) := s a
instance : Membership α (Set α) := ⟨Set.Mem⟩
theorem iff_of_eq (e : a = b) : a ↔ b := e ▸ .rfl

theorem girard
  (pi : (Type → Type) → Type)
  (lam : {A : Type → Type} → ((x : Type) → A x) → pi A)
  (app : {A : Type → Type} → pi A → (x : Type) → A x)
  (beta : ∀ {A : Type → Type} (f : (x : Type) → A x) (x : Type), app (lam f) x = f x)
  : False
  :=
  let F := λ X => (Set (Set X) → X) → Set (Set X)
  let U := pi F
  let G (T : Set (Set U)) (X) : F X := λ f => (λ p => (λ x : U => f (app x X f) ∈ p) ∈ T)
  let τ (T : Set (Set U)) : U := lam (G T)
  let σ (S : U) : Set (Set U) := app S U τ
  have στ : ∀ {s S}, s ∈ σ (τ S) ↔ ((λ x => τ (σ x) ∈ s) ∈ S) := @λ s S =>
    iff_of_eq (congrArg (λ f : F U => s ∈ f τ) (beta (G S) U) : _)
  let ω : Set (Set U) := λ p => ∀ x, p ∈ σ x → x ∈ p
  let δ (S : Set (Set U)) := ∀ p, p ∈ S → τ S ∈ p
  have : δ ω := λ p d => d (τ ω) <| στ.2 λ x h => d (τ (σ x)) (στ.2 h)
  this (λ y => ¬δ (σ y)) (λ x e f => f _ e λ p h => f _ (στ.1 h)) (λ p h => this _ (στ.1 h))
