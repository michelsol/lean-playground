
section
  macro "class_prop" c:ident ":=" p:term : command =>
    let class_field_name := Lean.Name.mkSimple <| s!"{c.getId.eraseMacroScopes.toString.toLower}"
    let field := Lean.mkIdent class_field_name
    `(
      class $c:ident : Prop where $field:ident : $p:term
      export $c:ident ($field:ident)
      )
end
