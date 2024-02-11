import Std.Data.List.Lemmas
import Playground.Data.Fin.Family.Basic
import Playground.Data.Fin.Family.Sum
namespace Logic

section
  structure FOL where
    function : Nat → Type
    relation : Nat → Type
    fdeq : ∀ n, DecidableEq (function n)
    rdeq : ∀ n, DecidableEq (relation n)

  instance (language : FOL) (n) : DecidableEq (language.function n) := language.fdeq n
  instance (language : FOL) (n) : DecidableEq (language.relation n) := language.rdeq n

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
  | eq : Term language → Term language → Formula

  scoped infixr:35 " ∧ "   => Formula.and
  scoped infixr:30 " ∨  "  => Formula.or
  scoped infixr:2 " ⇒ "   => Formula.imp
  scoped notation:max "⊥" => Formula.bot
  scoped notation:max "¬" p => (p ⇒ ⊥)
  scoped notation:max "∀ " x "; " f => Formula.all x f
  scoped notation:max "∃ " x "; " f => Formula.ex x f
  scoped infixr:50 " ≡ " => Formula.eq

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
        infer_instance
      | .app n f l => by
        rw [Mem_app_iff]
        let r k := decidable_Mem v (l k)
        infer_instance

    instance (v : Var) : (t : Term language) → Decidable (v ∈ t) := decidable_Mem v

    end Term.Mem

    def Term.decidable_Eq : DecidableEq (Term language)
    | var .., app ..
    | app .., var .. => isFalse Term.noConfusion
    | var .., var .. => by rw [var.injEq]; infer_instance
    | app n f l, app n' f' l' => by
      rw [app.injEq]
      exact if hn : n = n' then by
        subst hn
        let _ := λ k => decidable_Eq (l k) (l' k)
        simp; infer_instance
      else isFalse λ c => hn c.1

    instance : DecidableEq (Term language) := Term.decidable_Eq

    def Formula.decidable_Eq : DecidableEq (Formula language)
    | propVar .., propVar .. => by rw [propVar.injEq]; infer_instance
    | and .., or .. | and .., imp .. | and .., bot .. | and .., propVar ..
    | and .., app .. | and .., all .. | and .., ex .. | and .., eq .. => isFalse Formula.noConfusion
    | or .., and .. | or .., imp .. | or .., bot .. | or .., propVar ..
    | or .., app .. | or .., all .. | or .., ex .. | or .., eq .. => isFalse Formula.noConfusion
    | imp .., and .. | imp .., or .. | imp .., bot .. | imp .., propVar ..
    | imp .., app .. | imp .., all .. | imp .., ex .. | imp .., eq .. => isFalse Formula.noConfusion
    | bot .., and .. | bot .., or .. | bot .., imp .. | bot .., propVar ..
    | bot .., app .. | bot .., all .. | bot .., ex .. | bot .., eq .. => isFalse Formula.noConfusion
    | propVar .., and .. | propVar .., or .. | propVar .., imp .. | propVar .., bot ..
    | propVar .., app .. | propVar .., all .. | propVar .., ex .. | propVar .., eq .. => isFalse Formula.noConfusion
    | app .., and .. | app .., or .. | app .., imp .. | app .., bot .. | app .., propVar ..
    | app .., all .. | app .., ex .. | app .., eq .. => isFalse Formula.noConfusion
    | all .., and .. | all .., or .. | all .., imp .. | all .., bot .. | all .., propVar ..
    | all .., app .. | all .., ex .. | all .., eq .. => isFalse Formula.noConfusion
    | ex .., and .. | ex .., or .. | ex .., imp .. | ex .., bot .. | ex .., propVar ..
    | ex .., app .. | ex .., all .. | ex .., eq .. => isFalse Formula.noConfusion
    | eq .., and .. | eq .., or .. | eq .., imp .. | eq .., bot .. | eq .., propVar ..
    | eq .., app .. | eq .., all .. | eq .., ex .. => isFalse Formula.noConfusion
    | and f g, and f' g' => by
      rw [and.injEq]; let _ := decidable_Eq f f'; let _ := decidable_Eq g g'
      infer_instance
    | or f g, or f' g' => by
      rw [or.injEq]; let _ := decidable_Eq f f'; let _ := decidable_Eq g g'
      infer_instance
    | imp f g, imp f' g' => by
      rw [imp.injEq]; let _ := decidable_Eq f f'; let _ := decidable_Eq g g'
      infer_instance
    | bot, bot => isTrue rfl
    | all x f, all x' f' => by rw [all.injEq]; let _ := decidable_Eq f f'; infer_instance
    | ex x f, ex x' f' => by rw [ex.injEq]; let _ := decidable_Eq f f'; infer_instance
    | eq a b, eq a' b' => by rw [eq.injEq]; infer_instance
    | app n f l, app n' f' l' => by
      rw [app.injEq]
      exact if hn : n = n' then by subst hn; simp; infer_instance
      else isFalse λ c => hn c.1

    instance : DecidableEq (Formula language) := Formula.decidable_Eq


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
    | eq_l {a b : Term _} : a.Mem v → (a ≡ b).Mem v
    | eq_r {a b : Term _} : b.Mem v → (a ≡ b).Mem v

    instance : Membership Var (Formula language) where mem := Formula.Mem

    namespace Formula.Mem

    theorem Mem_and_iff (v : Var) (f g : Formula language)
      : v ∈ (f ∧ g) ↔ (v ∈ f ∨ v ∈ g) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .and f' g', _ => (v ∈ f' ∨ v ∈ g') | _, _ => True
      rec (motive := motive) (and_l := λ h _ => Or.inl h) (and_r := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .and_l h | .inr h => .and_r h⟩

    theorem Mem_or_iff (v : Var) (f g : Formula language)
      : v ∈ (f ∨ g) ↔ (v ∈ f ∨ v ∈ g) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .or f' g', _ => (v ∈ f' ∨ v ∈ g') | _, _ => True
      rec (motive := motive) (or_l := λ h _ => Or.inl h) (or_r := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .or_l h | .inr h => .or_r h⟩

    theorem Mem_imp_iff (v : Var) (f g : Formula language)
      : v ∈ (f ⇒ g) ↔ (v ∈ f ∨ v ∈ g) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .imp f' g', _ => (v ∈ f' ∨ v ∈ g') | _, _ => True
      rec (motive := motive) (imp_l := λ h _ => Or.inl h) (imp_r := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .imp_l h | .inr h => .imp_r h⟩

    theorem Mem_bot_iff (v : Var)
      : v ∈ (⊥ : Formula language) ↔ False := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .bot, _ => False | _, _ => True
      rec (motive := motive) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , False.elim⟩

    theorem Mem_propVar_iff (v : Var) {x}
      : v ∈ (.propVar x : Formula language) ↔ False := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .propVar _, _ => False | _, _ => True
      rec (motive := motive) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , False.elim⟩

    theorem Mem_app_iff (v : Var) (n) (f) (l)
      : v ∈ (Formula.app (language := language) n f l) ↔ (∃ k, v ∈ l k) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .app _ _ l', _ => (∃ k, v ∈ l' k) | _, _ => True
      rec (motive := motive) (app := λ h => ⟨_, h⟩) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ ⟨_, h⟩ => .app h⟩

    theorem Mem_all_iff (v : Var) (x) (f : Formula language)
      : v ∈ (∀ x; f) ↔ (v = x ∨ v ∈ f) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .all x' f', _ => (v = x' ∨ v ∈ f') | _, _ => True
      rec (motive := motive) (all_x := Or.inl rfl) (all_f := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => h ▸ .all_x | .inr h => .all_f h⟩

    theorem Mem_ex_iff (v : Var) (x) (f : Formula language)
      : v ∈ (∃ x; f) ↔ (v = x ∨ v ∈ f) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .ex x' f', _ => (v = x' ∨ v ∈ f') | _, _ => True
      rec (motive := motive) (ex_x := Or.inl rfl) (ex_f := λ h _ => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => h ▸ .ex_x | .inr h => .ex_f h⟩

    theorem Mem_eq_iff (v : Var) (a b : Term language)
      : v ∈ (a ≡ b) ↔ (v ∈ a ∨ v ∈ b) := ⟨
      let motive : (t : Formula language) → v ∈ t → Prop :=
        λ | .eq a' b', _ => (v ∈ a' ∨ v ∈ b') | _, _ => True
      rec (motive := motive) (eq_l := λ h => Or.inl h) (eq_r := λ h => Or.inr h)
        (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
        (by simp) (by simp) (by simp) (by simp) (by simp)
      , λ | .inl h => .eq_l h | .inr h => .eq_r h⟩

    def decidable_Mem (v : Var) : (t : Formula language) → Decidable (v ∈ t)
      | .and f g => by
        rw [Mem_and_iff]
        let _ := decidable_Mem v f; let _ := decidable_Mem v g
        infer_instance
      | .or f g => by
        rw [Mem_or_iff]
        let _ := decidable_Mem v f; let _ := decidable_Mem v g
        infer_instance
      | .imp f g => by
        rw [Mem_imp_iff]
        let _ := decidable_Mem v f; let _ := decidable_Mem v g
        infer_instance
      | .bot => by
        rw [Mem_bot_iff]
        infer_instance
      | .propVar x => by
        rw [Mem_propVar_iff]
        infer_instance
      | .app n f l => by
        rw [Mem_app_iff]
        infer_instance
      | .all x f => by
        rw [Mem_all_iff]
        let _ := decidable_Mem v f
        infer_instance
      | .ex x f => by
        rw [Mem_ex_iff]
        let _ := decidable_Mem v f
        infer_instance
      | .eq a b => by
        rw [Mem_eq_iff]
        infer_instance

    instance (v : Var) : (f : Formula language) → Decidable (v ∈ f) := decidable_Mem v

    end Formula.Mem

    def Term.subst (v : Var) (t : Term language) : Term language → Term language
    | var x => if x = v then t else var x
    | app n f l => app n f (λ i => subst v t (l i))
    scoped notation:max u "[" v " := " t "]"  => Term.subst v t u

    inductive Formula.ValidSubst (v : Var) (t : Term language) : Formula language → Type
    | and {f g : Formula _} : f.ValidSubst v t → g.ValidSubst v t → (f ∧ g).ValidSubst v t
    | or {f g : Formula _} : f.ValidSubst v t → g.ValidSubst v t → (f ∨ g).ValidSubst v t
    | imp {f g : Formula _} : f.ValidSubst v t → g.ValidSubst v t → (f ⇒ g).ValidSubst v t
    | bot : (⊥ : Formula _).ValidSubst v t
    | propVar : (propVar ..).ValidSubst v t
    | app : (app ..).ValidSubst v t
    | all {x} {f} : v ≠ x → x ∉ t → f.ValidSubst v t → (∀ x; f).ValidSubst v t
    | ex {x} {f} : v ≠ x → x ∉ t → f.ValidSubst v t → (∃ x; f).ValidSubst v t
    | eq {a b : Term language} : (a ≡ b).ValidSubst v t
    scoped notation:max p "[" v " := " t "] valid" => Formula.ValidSubst v t p

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
    | eq a b, _ => eq a[v := t] b[v := t]
    scoped notation:max p "[" v " := " t ", " h "]"  => Formula.subst v t p h

    open Formula in
    inductive Proof : List (Formula language) → Formula language → Type
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
    | all_intro (x) (hsx : ∀ f, f ∈ s → x ∉ f) : Proof s p → Proof s (∀ x; p)
    | all_elim (ht : p[x := t] valid) : Proof s (∀ x; p) → Proof s p[x := t, ht]
    | ex_intro {ht : p[x := t] valid} : Proof s p[x := t, ht] → Proof s (∃ x; p)
    | ex_elim (hsx : ∀ f, f ∈ s → x ∉ f) (hqx : x ∉ q) : Proof s (∃ x; p) → Proof (p :: s) q → Proof s q
    | eq_intro (t) : Proof s (t ≡ t)
    | eq_elim (t) (ht : p[x := t] valid) (hu : p[x := u] valid)
      :  Proof s (t ≡ u) → Proof s p[x := t, ht] → Proof s p[x := u, hu]


    scoped notation:max s " ⊢ " f => Proof s f
    scoped notation:max "⊢ " f => Proof ∅ f
    scoped notation:max s " ⊢[" L "] " f => Proof (language := L) s f
    scoped notation:max "⊢[" L "] " f => Proof (language := L) ∅ f


    def Term.newFreshVar : Term language → Var
    | var x => (x : Nat) + 1
    | app n f l => (Fin.Family.of λ k => (l k).newFreshVar).sum 0 + 1

    theorem Term.lt_newFreshVar_of_Mem
      : ∀ (t : Term language), ∀ ⦃v⦄, v ∈ t → v < t.newFreshVar
    | var x, v, hv =>
      have hv := (Term.Mem.Mem_var_iff ..).mp hv
      hv ▸ by simp_arith [newFreshVar]
    | app n f l, v, hv =>
      have ⟨k, h⟩ := (Term.Mem.Mem_app_iff ..).mp hv
      have h := lt_newFreshVar_of_Mem _ h
      have := (Fin.Family.of λ k => (l k).newFreshVar).sum_ge k
      Nat.lt_trans h (Nat.lt_succ_of_le this)

    theorem Term.newFreshVar_not_Mem (t : Term language) : t.newFreshVar ∉ t :=
      λ c => Nat.lt_irrefl _ (t.lt_newFreshVar_of_Mem c)

    theorem Term.subst_of_not_Mem {x} {t : Term language} (u : Term language) (h : x ∉ t)
      : t[x := u] = t :=
        match t with
        | var v => by
          show ite .. = _
          rw [Mem.Mem_var_iff] at h
          rw [if_neg λ c => h c.symm]
        | app n f l => by
          show app .. = app ..
          rw [Mem.Mem_app_iff] at h
          apply congr_arg
          funext i
          exact (l i).subst_of_not_Mem u λ c => h ⟨i, c⟩

    def Proof.eq_symm {s} {t u : Term language} (h : s ⊢ t ≡ u) : s ⊢ u ≡ t :=
      let x := t.newFreshVar
      have hx := t.newFreshVar_not_Mem
      let p := .var x ≡ t
      let vz : ∀ z, p[x := z] valid := λ z => by apply Formula.ValidSubst.eq
      have sz : ∀ z, p[x := z, vz z] = (z ≡ t) := λ z =>
        by dsimp [Formula.subst]; rw [Term.subst_of_not_Mem z hx]; simp [Term.subst]
      sz u ▸ eq_elim t (vz t) (vz u) h <| sz t ▸ eq_intro t

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

  section
  -- semantics
  structure Interpretation (language : FOL) where
    propValue (p : Nat) : Bool
    domain : Type
    varValue (x : Nat) : domain
    functionValue (n : Nat) (f : language.function n) : (Fin n → domain) → domain
    relationValue (n : Nat) (r : language.relation n) : (Fin n → domain) → Bool

  def Term.value {language} (i : Interpretation language) : Term language → i.domain
  | var x => i.varValue x
  | app _ f l => i.functionValue _ f λ k => (l k).value i

  scoped notation:max "⟦" t " | " i "⟧"  => Term.value i t

  def Interpretation.setPropValue {language} (i : Interpretation language) (v : Nat) (d : Bool)
  : Interpretation language :=
  { i with propValue := λ a => if a = v then d else i.propValue a }

  def Interpretation.setVarValue {language} (i : Interpretation language) (v : Nat) (d : i.domain)
  : Interpretation language :=
  { i with varValue := λ a => if a = v then d else i.varValue a }

  scoped notation:max i "⟦" v " := " d "⟧" => Interpretation.setVarValue i v d

  -- todo: change this to inductive
  def Formula.isTrueUnder {language} (i : Interpretation language) : Formula language → Prop
  | and f g => f.isTrueUnder i ∧ g.isTrueUnder i
  | or f g => f.isTrueUnder i ∨ g.isTrueUnder i
  | imp f g => f.isTrueUnder i → g.isTrueUnder i
  | bot => False
  | propVar x => i.propValue x = true
  | app _ f l => (i.relationValue _ f λ k => ⟦l k | i⟧) = true
  | all x f => ∀ d, f.isTrueUnder i⟦x := d⟧
  | ex x f => ∃ d, f.isTrueUnder i⟦x := d⟧
  | eq a b => ⟦a | i⟧ = ⟦b | i⟧

  scoped notation:max "⊨[" i "] " f  => Formula.isTrueUnder i f
  def Formula.isTrue {language} (f : Formula language) := ∀ i, ⊨[i] f
  scoped notation:max "⊨ " f  => Formula.isTrue f
  def Formula.entailsUnder {language} (i : Interpretation language)
    (s : List (Formula language)) (f : Formula language) := (∀ x ∈ s, ⊨[i] x) → ⊨[i] f
  scoped notation:max s " ⊨[" i "] " f  => Formula.entailsUnder i s f
  def Formula.entails {language} (s : List (Formula language)) (f : Formula language) := ∀ i, s ⊨[i] f
  scoped notation:max s " ⊨ " f  => Formula.entails s f

  def Proof.size {s} (f : Formula language) (h : s ⊢ f) : Nat :=
    let x : Inhabited Nat :=
    match h with
    | ax .. => ⟨1⟩
    | weaken h1 h2 => ⟨h2.size + 1⟩
    | and_intro h1 h2 => ⟨h1.size + h2.size + 1⟩
    | and_elim_left h1 => ⟨h1.size + 1⟩
    | and_elim_right h1 => ⟨h1.size + 1⟩
    | or_intro_left h1 h2 => ⟨h2.size + 1⟩
    | or_intro_right h1 h2 => ⟨h2.size + 1⟩
    | or_elim h1 h2 h3 => ⟨h1.size + h2.size + h3.size + 1⟩
    | imp_intro h1 => ⟨h1.size + 1⟩
    | imp_elim h1 h2 => ⟨h1.size + h2.size + 1⟩
    | bot_elim h1 h2 => ⟨h2.size + 1⟩
    | lem h1 => ⟨1⟩
    | all_intro h1 h2 h3 => ⟨h3.size + 1⟩
    | all_elim h1 h2 => ⟨h2.size + 1⟩
    | ex_intro h1 => ⟨h1.size + 1⟩
    | ex_elim h1 h2 h3 h4 => ⟨h3.size + h4.size + 1⟩
    | eq_intro h1 => ⟨1⟩
    | eq_elim h1 h2 h3 h4 h5 => ⟨h4.size + h5.size + 1⟩
  x.1


  theorem Formula.isTrueUnder_invariant_of_not_Mem {language} {f} {v : Var}
    (hv : v ∉ f) (i : Interpretation language) (d : i.domain)
    : (⊨[i] f) ↔ ⊨[i⟦v := d⟧] f := ⟨by
      intro h; induction f with
      | and f g hf hg =>
          rw [Mem.Mem_and_iff] at hv; exact ⟨hf (λ c => hv (.inl c)) h.1, hg (λ c => hv (.inr c)) h.2⟩
      | or f g hf hg =>
          rw [Mem.Mem_or_iff] at hv; match h with
          | .inl h => exact Or.inl $ hf (λ c => hv (.inl c)) h
          | .inr h => exact Or.inr $ hg (λ c => hv (.inr c)) h
      | _ => sorry
      , sorry⟩

  theorem Proof.soundness {f : Formula language} {s} : (s ⊢ f) → s ⊨ f
    | ax h1 => λ i hs => hs _ h1
    | weaken h1 h2 => λ i hs => soundness h2 i λ x hx => hs x (.tail h1 hx)
    | and_intro h1 h2 => λ i hs => ⟨soundness h1 i hs, soundness h2 i hs⟩
    | and_elim_left h1 => λ i hs => (soundness h1 i hs).1
    | and_elim_right h1 => λ i hs => (soundness h1 i hs).2
    | or_intro_left h1 h2 => λ i hs => Or.inl (soundness h2 i hs)
    | or_intro_right h1 h2 => λ i hs => Or.inr (soundness h2 i hs)
    | or_elim h1 h2 h3 => λ i hs => match soundness h1 i hs with
      | .inl h1 => soundness h2 i hs h1
      | .inr h1 => soundness h3 i hs h1
    | imp_intro h1 => λ i hs =>
      λ b => soundness h1 i λ x => λ | .head _ => b | .tail _ hx => hs _ hx
    | imp_elim h1 h2 => λ i hs => soundness h2 i hs (soundness h1 i hs)
    | bot_elim h1 h2 => λ i hs => (soundness h2 i hs).elim
    | lem h1 => λ i hs => Classical.em _
    | all_intro x h2 h3 => λ i hs =>
      λ d => soundness h3 i⟦x := d⟧ λ g hg =>
        (g.isTrueUnder_invariant_of_not_Mem (h2 g hg) i d).mp (hs g hg)
    | all_elim (x := x) (t := t) h1 h2 => λ i hs =>
      let j := i⟦x := ⟦t | i⟧⟧
      have := soundness h2 j sorry sorry
      sorry --needs a lemma
    | ex_intro .. => sorry
    | ex_elim .. => sorry
    | eq_intro .. => sorry
    | eq_elim .. => sorry
  termination_by h => h.size
  decreasing_by
    all_goals simp_wf
    all_goals dsimp [size]
    all_goals simp_arith


  theorem Term.subst_value {language} {a} {v} {t} (i : Interpretation language)
  : ⟦a[v := t] | i⟧ = ⟦a | i⟦v := ⟦t | i⟧⟧⟧ :=
  match a with
  | var x =>
    if h : x = v then by
      dsimp [subst]
      rw [if_pos h]
      dsimp [value, Interpretation.setVarValue]
      rw [if_pos h]
    else by
      dsimp [subst]
      rw [if_neg h]
      dsimp [value, Interpretation.setVarValue]
      rw [if_neg h]
  | app n f l => by
    dsimp [subst]
    dsimp [value]
    congr
    funext k
    apply subst_value

  theorem Formula.isTrueUnder_subst_iff {language} {f} {v} {t} (i : Interpretation language) (ht)
  : (⊨[i] f[v := t, ht]) ↔ ⊨[i⟦v := ⟦t | i⟧⟧] f :=
    match f, ht with
    | .and f g, .and h1 h2 => by
      dsimp [subst, isTrueUnder]
      rw [isTrueUnder_subst_iff i h1, isTrueUnder_subst_iff i h2]
    | or f g, .or h1 h2 => by
      dsimp [subst, isTrueUnder]
      rw [isTrueUnder_subst_iff i h1, isTrueUnder_subst_iff i h2]
    | imp f g, .imp h1 h2 => by
      dsimp [subst, isTrueUnder]
      rw [isTrueUnder_subst_iff i h1, isTrueUnder_subst_iff i h2]
    | bot, _ => by
      simp [subst, isTrueUnder]
    | propVar p, _ => by
      simp [subst, isTrueUnder]
      exact ⟨id, id⟩
    | app n f l, h1 => by
      simp [subst]
      apply Bool.eq_iff_eq_true_iff.mp
      congr
      funext k
      apply Term.subst_value
    | all x p, .all h1 h2 h3 => by
      dsimp [subst]
      dsimp [isTrueUnder]
      have : {α : Type} → {p q : α → _} → (∀ x, (p x ↔ q x)) → ((∀ x, p x) ↔ ∀ x, q x) :=
        λ h => ⟨λ g x => (h x).mp (g x), λ g x => (h x).mpr (g x)⟩
      apply this
      intro d
      rw [isTrueUnder_subst_iff i⟦x := d⟧ h3]
      sorry
    | ex x p, .ex h1 h2 h3 => by
      dsimp [subst]
      dsimp [isTrueUnder]
      have : {α : Type} → {p q : α → _} → (∀ x, (p x ↔ q x)) → ((∃ x, p x) ↔ ∃ x, q x) :=
        λ h => ⟨λ ⟨x, g⟩ => ⟨x, (h x).mp g⟩, λ ⟨x, g⟩ => ⟨x, (h x).mpr g⟩⟩
      apply this
      intro d
      rw [isTrueUnder_subst_iff i⟦x := d⟧ h3]
      sorry
    | eq a b, _ => by
      simp [subst]
      dsimp [isTrueUnder]
      rw [Term.subst_value]
      rw [Term.subst_value]



    example {language} (i : Interpretation language) (f : Formula language)
    (x : Var) (v : Var)
    (t : Term language) (d : i.domain) :
      (⊨[i⟦x := d⟧⟦v := ⟦t | i⟦x := d⟧⟧⟧] f) ↔ ⊨[i⟦v := ⟦t | i⟧⟧⟦x := d⟧] f
      := sorry

    open Term in
    example {language} (i : Interpretation language) (a : Term language)
    (x : Var) (v : Var)
    (t : Term language) (d : i.domain) :
      ⟦a | i⟦x := d⟧⟦v := ⟦t | i⟦x := d⟧⟧⟧ ⟧ = ⟦a | i⟦v := ⟦t | i⟧⟧⟦x := d⟧ ⟧
      := match a with
      | .var y =>
        if h : y = x then by
          dsimp [value]
          dsimp [Interpretation.setVarValue]
          -- rw [h]
          simp [h]
          sorry
        else
          sorry
      | .app n f l => sorry

  end
end

end Logic
