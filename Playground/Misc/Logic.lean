import Std.Data.List.Lemmas
import Playground.Data.Fin.Family.Basic
namespace Logic

section
  structure FOL where
    function : Nat → Type
    relation : Nat → Type
  
  abbrev Var := Nat
  abbrev PropVar := Nat

  variable (language : FOL) in
  inductive Term
  | var : Var → Term
  | app : (n : Nat) → language.function n → (Fin n → Term) → Term

  variable (language : FOL) in
  inductive Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | bot : Formula
  | propVar : PropVar → Formula
  | app : (n : Nat) → language.relation n → (Fin n → Term language) → Formula
  | all : Var → Formula → Formula
  | ex : Var → Formula → Formula

  scoped infixr:35 " ∧ "   => Formula.and
  scoped infixr:30 " ∨  "  => Formula.or
  scoped infixr:2 " ⇒ "   => Formula.imp
  scoped notation:max "⊥" => Formula.bot
  scoped notation:max "¬" p => (p ⇒ ⊥)
  scoped notation:max "∀ " x ";" f => Formula.all x f
  scoped notation:max "∃ " x ";" f => Formula.ex x f

  section
    variable {language : FOL}

    inductive Term.Mem (v : Var) : Term language → Prop
    | var : (var v).Mem v
    | app {n} {f} {l} {k} : (l k).Mem v → (app n f l).Mem v

    instance : Membership Var (Term language) where mem := Term.Mem

    namespace Term.Mem
    theorem Mem_var_iff (v : Var) (x)
      : v ∈ (Term.var (language := language) x) ↔ v = x := ⟨
        let motive : (t : Term language) → v ∈ t → Prop := 
          λ | .var x', _ => v = x' | _, _ => True
        rec (motive := motive) rfl (λ _ _ => trivial)
        , λ h => h ▸ .var⟩

    theorem Mem_app_iff (v : Var) (n) (f) (l)
      : v ∈ (Term.app (language := language) n f l) ↔ ∃ k, v ∈ l k := ⟨
      let motive : (t : Term language) → v ∈ t → Prop := 
        λ | .app _ _ l', _ => ∃ k, v ∈ l' k | _, _ => True
      rec (motive := motive) (by simp) (λ hk _ => ⟨_, hk⟩)
      , λ ⟨_, hk⟩ => .app hk⟩

    def decidable_Mem (v : Var) : (t : Term language) → Decidable (v ∈ t)
      | .var x => by
        rw [Mem_var_iff]
        exact inferInstance
      | .app n f l => by
        rw [Mem_app_iff]
        let r k := decidable_Mem v (l k)
        exact inferInstance

    instance (v : Var) : (t : Term language) → Decidable (v ∈ t) := decidable_Mem v
    end Term.Mem

    inductive Formula.Mem (v : Var) : Formula language → Prop
    | and_l {f g : Formula _} : f.Mem v → (f ∧ g).Mem v
    | and_r {f g : Formula _} : g.Mem v → (f ∧ g).Mem v
    | or_l {f g : Formula _} : f.Mem v → (f ∨ g).Mem v
    | or_r {f g : Formula _} : g.Mem v → (f ∨ g).Mem v
    | imp_l {f g : Formula _} : f.Mem v → (f ⇒ g).Mem v
    | imp_r {f g : Formula _} : g.Mem v → (f ⇒ g).Mem v
    | app {n} {r} {l} {k} : (l k).Mem v → (app n r l).Mem v
    | all_f {x} {f} : f.Mem v → (∀ x; f).Mem v
    | all_x {f} : (∀ v; f).Mem v
    | ex_f {x} {f} : f.Mem v → (∃ x; f).Mem v
    | ex_x {f} : (∃ v; f).Mem v

    instance : Membership Var (Formula language) where mem := Formula.Mem

    namespace Formula.Mem
    
    theorem Mem_and_iff (v : Var) (f g : Formula language)
      : v ∈ (f ∧ g) ↔ (v ∈ f ∨ v ∈ g) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .and f' g', _ => (v ∈ f' ∨ v ∈ g') | _, _ => True
      rec (motive := motive) (and_l := λ h _ => Or.inl h) (and_r := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .and_l h | .inr h => .and_r h⟩

    theorem Mem_or_iff (v : Var) (f g : Formula language)
      : v ∈ (f ∨ g) ↔ (v ∈ f ∨ v ∈ g) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .or f' g', _ => (v ∈ f' ∨ v ∈ g') | _, _ => True
      rec (motive := motive) (or_l := λ h _ => Or.inl h) (or_r := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .or_l h | .inr h => .or_r h⟩

    theorem Mem_imp_iff (v : Var) (f g : Formula language)
      : v ∈ (f ⇒ g) ↔ (v ∈ f ∨ v ∈ g) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .imp f' g', _ => (v ∈ f' ∨ v ∈ g') | _, _ => True
      rec (motive := motive) (imp_l := λ h _ => Or.inl h) (imp_r := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .imp_l h | .inr h => .imp_r h⟩

    theorem Mem_bot_iff (v : Var)
      : v ∈ (⊥ : Formula language) ↔ False := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .bot, _ => False | _, _ => True
      rec (motive := motive) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , False.elim⟩

    theorem Mem_propVar_iff (v : Var) {x}
      : v ∈ (.propVar x : Formula language) ↔ False := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .propVar _, _ => False | _, _ => True
      rec (motive := motive) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , False.elim⟩

    theorem Mem_app_iff (v : Var) (n) (f) (l) 
      : v ∈ (Formula.app (language := language) n f l) ↔ (∃ k, v ∈ l k) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .app _ _ l', _ => (∃ k, v ∈ l' k) | _, _ => True
      rec (motive := motive) (app := λ h => ⟨_, h⟩) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ ⟨_, h⟩ => .app h⟩

    theorem Mem_all_iff (v : Var) (x) (f : Formula language)
      : v ∈ (∀ x; f) ↔ (v = x ∨ v ∈ f) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .all x' f', _ => (v = x' ∨ v ∈ f') | _, _ => True
      rec (motive := motive) (all_x := Or.inl rfl) (all_f := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => h ▸ .all_x | .inr h => .all_f h⟩

    theorem Mem_ex_iff (v : Var) (x) (f : Formula language)
      : v ∈ (∃ x; f) ↔ (v = x ∨ v ∈ f) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop := 
        λ | .ex x' f', _ => (v = x' ∨ v ∈ f') | _, _ => True
      rec (motive := motive) (ex_x := Or.inl rfl) (ex_f := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => h ▸ .ex_x | .inr h => .ex_f h⟩

    def decidable_Mem (v : Var) : (t : Formula language) → Decidable (v ∈ t)
      | .and f g => by
        rw [Mem_and_iff]
        let _ := decidable_Mem v f; let _ := decidable_Mem v g
        exact inferInstance
      | .or f g => by
        rw [Mem_or_iff]
        let _ := decidable_Mem v f; let _ := decidable_Mem v g
        exact inferInstance
      | .imp f g => by
        rw [Mem_imp_iff]
        let _ := decidable_Mem v f; let _ := decidable_Mem v g
        exact inferInstance
      | .bot => by
        rw [Mem_bot_iff]
        exact inferInstance
      | .propVar x => by
        rw [Mem_propVar_iff]
        exact inferInstance
      | .app n f l => by
        rw [Mem_app_iff]
        exact inferInstance
      | .all x f => by
        rw [Mem_all_iff]
        let _ := decidable_Mem v f
        exact inferInstance
      | .ex x f => by
        rw [Mem_ex_iff]
        let _ := decidable_Mem v f
        exact inferInstance

    instance (v : Var) : (f : Formula language) → Decidable (v ∈ f) := decidable_Mem v 

    end Formula.Mem

    -- instance : Membership Var (List (Term language)) where
    --   mem v l := ∃ t ∈ l, v ∈ t
    -- instance : Membership Var (List (Formula language)) where
    --   mem v l := ∃ t ∈ l, v ∈ t
    -- instance : Membership Var (List (Formula language ⊕ Term language)) where
    --   mem v l := ∃ t ∈ l, match t with | .inl t => v ∈ t | .inr t => v ∈ t


    def Term.subst (v : Var) (t : Term language) : Term language → Term language
    | var x => if x = v then t else var x
    | app n f l => app n f (λ i => subst v t (l i))
    scoped notation:40 u "[" v ":=" t "]"  => Term.subst v t u

    inductive Formula.ValidSubst (v : Var) (t : Term language) : Formula language → Type
    | and {f g : Formula _} : f.ValidSubst v t → g.ValidSubst v t → (f ∧ g).ValidSubst v t
    | or {f g : Formula _} : f.ValidSubst v t → g.ValidSubst v t → (f ∨ g).ValidSubst v t
    | imp {f g : Formula _} : f.ValidSubst v t → g.ValidSubst v t → (f ⇒ g).ValidSubst v t
    | bot : ⊥.ValidSubst v t
    | propVar : (propVar ..).ValidSubst v t
    | app : (app ..).ValidSubst v t
    | all {x} {f} : v ≠ x → x ∉ t → f.ValidSubst v t → (∀ x; f).ValidSubst v t
    | ex {x} {f} : v ≠ x → x ∉ t → f.ValidSubst v t → (∃ x; f).ValidSubst v t
    scoped notation:40 p "[" v ":=" t "] valid" => Formula.ValidSubst v t p

    def Formula.subst (v : Var) (t : Term language)
      : (f : Formula language) → f[v := t] valid → Formula language
    | and f g, .and h1 h2 => and (f.subst v t h1) (g.subst v t h2)
    | or f g, .or h1 h2 => or (f.subst v t h1) (g.subst v t h2)
    | imp f g, .imp h1 h2 => imp (f.subst v t h1) (g.subst v t h2)
    | bot, _ => bot
    | propVar p, _ => propVar p
    | app n f l, _ => app n f (λ k => (l k)[v := t])
    | all x p, .all _ _ h3 => all x (p.subst v t h3)
    | ex x p, .ex _ _ h3 => ex x (p.subst v t h3)
    scoped notation:40 p "[" v ":=" t "," h "]"  => Formula.subst v t p h

    open Formula in
    inductive Proof : List (Formula language) → Formula language → Prop
    | ax : p ∈ s → Proof s p
    | weaken (t) : Proof s p → Proof (t :: s) p
    | and_intro : Proof s p → Proof s q → Proof s (p ∧ q)
    | and_elim_left : Proof s (p ∧ q) → Proof s p
    | and_elim_right : Proof s (p ∧ q) → Proof s q
    | or_intro_left (q) : Proof s p → Proof s (p ∨ q)
    | or_intro_right (p) : Proof s q → Proof s (p ∨ q)
    | or_elim : Proof s (p ∨ q) → Proof s (p ⇒ r) → Proof s (q ⇒ r) → Proof s r
    | imp_intro : Proof (p :: s) q → Proof s (p ⇒ q)
    | imp_elim : Proof s p → Proof s (p ⇒ q) → Proof s q
    | bot_elim (p) : Proof s ⊥ → Proof s p
    | lem (p) : Proof s (p ∨ ¬p)
    | all_intro {s} (x) (hsx : ∀ f, f ∈ s → x ∉ f) : Proof s p → Proof s (∀ x; p)
    | all_elim (ht : p[x := t] valid) : Proof s (∀ x; p) → Proof s (p[x := t, ht])
    | ex_intro {ht : p[x := t] valid} : Proof s (p[x := t, ht]) → Proof s (∃ x; p)
    | ex_elim {s} (hsx : ∀ f, f ∈ s → x ∉ f) (hqx : x ∉ q) : Proof s (∃ x; p) → Proof (p :: s) q → Proof s q

    scoped infix:1 " ⊢ " => Proof
    scoped notation:1 "⊢ " f => Proof ∅ f
    scoped notation:1 s " ⊢[" L "] " f => Proof (language := L) s f
    scoped notation:1 "⊢[" L "] " f => Proof (language := L) ∅ f


    def Term.newFreshVar : Term language → Var
    | var x => (x : Nat).succ
    | app n f l => 
      sorry

    theorem Term.all_vars_lt_newFreshVar
      : ∀ (t : Term language), ∀ ⦃v⦄, v ∈ t → v < t.newFreshVar
    | var x, v, hv => 
      -- (x : Nat).lt_succ_self
      sorry
    | _, _, _ => sorry

    theorem Term.newFreshVar_not_in : ∀ (t : Term language), t.newFreshVar ∉ t :=
      sorry

  end


  section
    open Formula Proof
    variable {L : FOL}
    def p_imp_p (p : Formula L) : ⊢ p ⇒ p := imp_intro <| ax <| by simp
    def bot_intro : (s ⊢ p) → (s ⊢ ¬p) → (s ⊢ ⊥) := imp_elim
    def has_notro : (s ⊢ p ⇒ ⊥) → (s ⊢ ¬p) := id
    def not_elim : (s ⊢ ¬p) → (s ⊢ p ⇒ ⊥) := id
    def absurd_r : (s ⊢ ¬p ⇒ ⊥) → (s ⊢ p) := λ h =>
      or_elim (lem p) (imp_intro <| ax <| by simp)
        <| imp_intro 
          <| bot_elim _
            <| imp_elim (ax <| by simp)
              <| weaken _ h
    def of_notnot : (s ⊢ ¬¬p) → (s ⊢ p) := absurd_r
  end
end

end Logic
