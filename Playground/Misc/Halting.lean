import Mathlib
import Std.Logic

section
  class SupportsPrograms (A : Type _) [DecidableEq A] where
    Program : Type _
    trueChar : A
    prod_mk : List A → List A → List A
    to_str : Program → List A
    run : Program → List A → Option (List A)
    lam : (List A → Program) → Program
    app : Program → List A → Program
    run_app (p) (x) : run (app p x) [] = run p x
    run_lam_app (p : List A → Program) (q : List A → List A) (x)
      : run (lam λ t => app (p t) (q t)) x = run (app (p x) (q x)) []
    run_app_lam (q) (t) (x) : run (app (lam q) t) x = run (q t) x
    const : List A → Program
    run_const (c) (x) : run (const c) x = some c
    run_lam_const (f : List A → List A) (x) : run (lam λ t => const (f t)) x = run (const (f x)) []
    loop : Program
    run_loop (x) : run loop x = none
    run_lam_loop (x) : run (lam λ _ => loop) x = run loop x
    eq : Program → Program → Program
    run_eq (p) (q) (x) : run (eq p q) x =
      match run p x, run q x with
      | none, none => none
      | none, some _ => none
      | some _, none => none
      | some po, some qo => if po = qo then some [trueChar] else some []
    run_lam_eq (p) (q) (x) : run (lam λ t => eq (p t) (q t)) x = run (eq (lam p) (lam q)) x
    cond : Program → Program → Program → Program
    run_cond (c) (p) (q) (x) : run (cond c p q) x =
      match run c x with
      | none => none
      | some co => if co = [trueChar] then run p x else run q x
    run_lam_cond (c) (p) (q) (x) : run (lam λ t => cond (c t) (p t) (q t)) x = run (cond (lam c) (lam p) (lam q)) x


  namespace SupportsPrograms
  section
    variable {A} [DecidableEq A] [SupportsPrograms A]
    abbrev trueString : List A := [trueChar]
    abbrev falseString : List A := []
  end
  namespace Program
  section
    variable {A} [DecidableEq A] [SupportsPrograms A]

    def to_str (p : Program A) := SupportsPrograms.to_str p

    abbrev Halts (p : Program A) (x : List A) : Prop := (run p x).isSome

    def solves_halting (h : Program A) :=
      ∀ p : Program A, ∀ x,
      if p.Halts x then run h (prod_mk p.to_str x) = some trueString
      else run h (prod_mk p.to_str x) = some falseString

    theorem not_solves_halting (h : Program A) : ¬h.solves_halting := by
      intro hh
      let c := lam λ p =>
        cond (eq (app h (prod_mk p p)) (const falseString)) (const trueString) loop
      have hh := hh c c.to_str
      by_cases hc : c.Halts c.to_str
      . rw [if_pos hc] at hh
        have hc : (run (lam λ p => cond ..) c.to_str).isSome = true := hc
        rw [run_lam_cond, run_cond] at hc
        rw [run_lam_eq, run_eq] at hc
        rw [run_lam_app, run_app] at hc
        rw [run_lam_const, run_const] at hc
        rw [run_lam_const, run_const] at hc
        rw [run_lam_loop, run_loop] at hc
        rw [hh] at hc
        simp at hc
      . rw [if_neg hc] at hh
        have hc : ¬(run (lam λ p => cond ..) c.to_str).isSome := hc
        rw [run_lam_cond, run_cond] at hc
        rw [run_lam_eq, run_eq] at hc
        rw [run_lam_app, run_app] at hc
        rw [run_lam_const, run_const] at hc
        rw [run_lam_const, run_const] at hc
        rw [run_lam_loop, run_loop] at hc
        rw [hh] at hc
        simp at hc

  end
  end Program
  end SupportsPrograms


class System (A : Type _) [DecidableEq A] where
  Formula : Type _
  Proves : Formula → Prop
  Not : Formula → Formula
  proof_of_str (f : Formula) : List A → Unit ⊕' Proves f
  str_of_formula : Formula → List A

namespace System
scoped notation:max "⊢ " f => System.Proves f

def IsComplete (A) [DecidableEq A] [System A] := ∀ f : Formula A, (⊢ f) ∨ (⊢ Not f)
def IsConsistent (A) [DecidableEq A] [System A] := ∀ f : Formula A, ¬ ((⊢ f) ∧ (⊢ Not f))

section
  variable {A} [DecidableEq A] [System A]
  def Formula.Not (f : Formula A) := System.Not f
  def Formula.proof_of_str (f : Formula A) := System.proof_of_str f
  def Formula.to_str (f : Formula A) := System.str_of_formula f
end

open SupportsPrograms in
class ProofVerifier (A) [DecidableEq A] [SupportsPrograms A] [System A] where
  verifier : Program A
  verifier_ax : ∀ f : Formula A, ∀ x, run verifier (prod_mk f.to_str x) =
      match f.proof_of_str x with
      | .inl _ => some falseString
      | .inr _ => some trueString
  halts_on (p : Program A) (x : List A) : Formula A
  sound_halts : ∀ p x candidateProof,
    match (halts_on p x).proof_of_str candidateProof with
    | .inl _ => True
    | .inr _ => p.Halts x
  sound_not_halts : ∀ p x candidateProof,
    match (halts_on p x).Not.proof_of_str candidateProof with
    | .inl _ => True
    | .inr _ => ¬p.Halts x


  theorem incompleteness (A) [DecidableEq A] [SupportsPrograms A] [System A] [ProofVerifier A]
    (h_complete : IsComplete A) (h_consistent : IsConsistent A)
    : True := by
    sorry

end System

end
