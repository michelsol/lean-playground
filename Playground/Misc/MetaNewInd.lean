import Lean.Elab.Command
import Lean.Meta.Constructions

open Lean Elab Command

elab "gen_structure" id:ident : command => do
  let level_u := mkLevelParam `u
  let type_u := mkSort <| mkLevelSucc level_u
  let decl := mkInductiveDeclEs [`u] 1 [{
    name := id.getId
    type := mkForall .anonymous .default type_u type_u
    ctors := [{
      name := id.getId ++ `mk
      type := mkForall `α .implicit type_u
        <| mkForall `x .default (mkBVar 0)
        <| mkApp (mkConst id.getId [level_u]) (mkBVar 1)
    }]
  }] false
  match (← getEnv).addAndCompile {} decl with
  | .error e => throwError (e.toMessageData {})
  | .ok env => 
    setEnv env
    mkCasesOn id.getId
    mkRecOn id.getId
    mkNoConfusionCore id.getId
    mkBelow id.getId
    mkIBelow id.getId
    mkBRecOn id.getId
    mkBInductionOn id.getId


-- inductive struct.{u} : Type u → Type u | mk : {α : Type u} → α → struct α
gen_structure struct
#print struct
#print struct.recOn

noncomputable
def aaa : {a : Type u} → {motive : struct a → Sort u_1} → 
  (t : struct a) → ((x : a) → motive (struct.mk x)) → motive t
  := struct.recOn

def proj (s : struct α) : α :=
  match s with
  | struct.mk x => x
