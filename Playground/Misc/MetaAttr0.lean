import Lean
import Lean.Meta

section
  open Lean Elab Command Meta

  syntax (name := to_struct) "to_struct" "!"? "?"? (ppSpace ident)? (ppSpace str)? : attr

  def to_struct_impl : AttributeImpl := {
    name := `to_struct
    descr := "to_struct does stuff"
    add := fun src stx kind => do
      if (kind != AttributeKind.global) then
        throwError "can't be used as a local attribute"
      let env ← getEnv
      match env.find? src with
      | ConstantInfo.inductInfo indval =>
          let decl := Declaration.defnDecl {
            name := Name.mkSimple "aaa"
            levelParams := []
            type := mkConst "Nat"
            value := mkNatLit 17
            hints := ReducibilityHints.opaque
            safety := DefinitionSafety.safe
          }
          match env.addAndCompile {} decl with
          | Except.error e => throwError "addAndCompile error"
          | Except.ok env => 
            setEnv env
            for ctor in indval.ctors do
              let cinfo ← getConstInfo ctor
              -- let mut m : MessageData := "ctor "
              -- m := m ++ Format.line ++ cinfo.name ++ " : " ++ cinfo.type
              -- m := m ++ Format.line ++ "ctorName = " ++ cinfo.type.ctorName
              -- m := m ++ Format.line ++ "parameters = " ++ (ctor_type_params cinfo.type).toString
              -- trace[to_struct] m
              match (← getEnv).addAndCompile {} (struct_of_ctor cinfo) with
              | .error e => throwError ("struct_of_ctor addAndCompile error: " ++ e.toMessageData {})
              | .ok env => setEnv env
      | Option.some _ => throwError src ++ " not an inductive"
      | Option.none => throwError src ++ " not found"
  }
  where
    struct_of_ctor  (ctor_info : ConstantInfo) : Declaration := 
      let struct_name := ctor_info.name ++ "struct"
      let struct_decl := {
        name := struct_name
        type := mkForall "L" .default (mkSort levelOne)
                <| mkSort (mkLevelSucc levelOne)
        ctors := [{
          name := struct_name ++ "mk"
          type := mk_type_of_struct_of_ctor ctor_info.type struct_name
        }]
      }
      Declaration.inductDecl [] 1 [struct_decl] false
    mk_type_of_struct_of_ctor (input_type : Expr) (struct_name : Name)
      (depth : Nat := 0) : Expr :=
      match input_type with
      | .forallE param_name param_expr next _ =>
        let bt := match depth with
          | 0 => .implicit
          | _ => .default
        mk_type_of_struct_of_ctor next struct_name depth.succ
        |> mkForall param_name bt param_expr 
      | _ => mkApp (mkConst struct_name) (mkBVar depth.pred)
    ctor_type_params (ctor_type : Expr) : List Name :=
      match ctor_type with
      | .forallE param_name _ next _ => param_name :: ctor_type_params next
      | _ => []
    -- def_of_struct_and_param_name (c)

  initialize registerTraceClass `to_struct
  initialize registerBuiltinAttribute to_struct_impl
end
