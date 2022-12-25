import Playground.Data.Meta.Lean
import Playground.Data.GeneralDotNotation

def Lean.Syntax.mkAppBinders (fn : Term) (arr : Array Syntax.ArrowBinder) : Term :=
  mkApp fn <| (arr.filter λ b => b.binderInfo != .implicit).map λ x => mkIdent x.name

def Lean.Syntax.mkExplicitAppBinders (fn : Term) (arr : Array Syntax.ArrowBinder) : Term :=
  mkApp (mkExplicit fn) <| arr.map λ x => mkIdent x.name

section
  open Lean Elab Command Meta Term Syntax PrettyPrinter Delaborator Expr

  namespace Meta.Impl.Rec

  structure ConstructorData where
    globalName : Name
    typeBinders : Array Syntax.ArrowBinder
    typeHead : Syntax
    type : Syntax
    typeBindersUsedRecursively : Array Syntax.ArrowBinder
    recursiveTypeBinders : Array Syntax.ArrowBinder
    recursiveMotiveFun : Syntax.Binder


  def implementRecursionFunction (inductiveLocalName : Name) : CommandElabM Unit := do
    let recursionDeclarationLocalName := inductiveLocalName ++ `recursion
    let inductiveSuffixName := inductiveLocalName.getSuffix
    let inductiveVal <- getConstInfoInduct <| (<- getCurrNamespace) ++ inductiveLocalName
    let inductiveType <- liftCoreM <| MetaM.run' <| delab inductiveVal.type
    let inductiveTypeBinders := 
        (inductiveVal.type.getArrowBindersNames.zip (getArrowBinders inductiveType)).map
          λ (paramName, ⟨⟨_, paramType⟩, paramBinderInfo⟩) => 
            ⟨⟨paramName, paramType⟩, paramBinderInfo⟩
    let inductiveTypeBindersAsImplicit := inductiveTypeBinders.map λ b => ⟨b.binder, .implicit⟩
    let inductiveTypeHead := getArrowOutput inductiveType
    let isProp := match inductiveTypeHead with
      | `(Prop) => true
      | _ => false
    let inductiveType := inductiveTypeBinders.foldr mkDepArrow inductiveTypeHead
    let tMotiveBinder := ⟨`t_motive, mkAppBinders (mkIdent inductiveSuffixName) inductiveTypeBinders⟩
    let motiveType := inductiveTypeBindersAsImplicit.foldr mkDepArrow <|
      mkDepArrow ⟨tMotiveBinder, .default⟩ (if isProp = true then mkProp else mkSort `u_motive)
    let motiveBinder := ⟨`motive, motiveType⟩
    -- IO.println s!"inductive name: {inductiveLocalName}"
    -- IO.println s!"inductive type: {inductiveType.prettyPrint}"
    -- IO.println s!"motive type : {motiveType.prettyPrint}"
    let mut constructors : Array ConstructorData  := #[]
    for ctor in inductiveVal.ctors do
      let ctorInfo <- getConstInfo ctor
      let ctorType <- liftCoreM <| MetaM.run' <| delab ctorInfo.type
      let typeBinders := 
          (ctorInfo.type.getArrowBindersNames.zip (getArrowBinders ctorType)).map
            λ (paramName, ⟨⟨_, paramType⟩, paramBinderInfo⟩) => 
              ⟨⟨paramName, paramType⟩, paramBinderInfo⟩
      let typeHead := getArrowOutput ctorType
      let type := typeBinders.foldr mkDepArrow typeHead
      let typeBindersUsedRecursively := typeBinders.filter λ b => 
          match b.type with
          | `($fn $params*) => match fn with
            | ⟨ident _ _ name _⟩ => name.getSuffix == inductiveSuffixName
            | _ => false
          | _ => false
      let recursiveTypeBinders := typeBindersUsedRecursively.map λ b => 
          ⟨⟨Name.mkSimple <| s!"{b.name}_rec", 
            mkApp (mkIdent motiveBinder.name) <| #[mkIdent b.name]⟩, .default⟩
      let recursiveMotiveFunType := 
        typeBinders.foldr mkDepArrow 
        <| recursiveTypeBinders.foldr mkDepArrow 
          <| Syntax.mkApp (mkIdent motiveBinder.name)
            <| #[mkExplicitAppBinders (mkIdent ctorInfo.name.getSuffix) typeBinders]
      let recursiveMotiveFun := ⟨Name.mkSimple <| s!"{ctorInfo.name.getSuffix.toString.toLower}_ih", 
        recursiveMotiveFunType⟩
      let constructor := {
        globalName := ctorInfo.name,
        typeBinders, typeHead, type, typeBindersUsedRecursively, recursiveTypeBinders, 
        recursiveMotiveFun
      }
      constructors := constructors.push constructor
      -- IO.println s!"constructor name: {constructor.globalName.getSuffix}"
      -- IO.println s!"constructor type: {constructor.type.prettyPrint}"
      -- IO.println s!"constructor rec type: {constructor.recursiveMotiveFunType.prettyPrint}"
    let recursionTypeBinders := #[]
      ++ inductiveTypeBindersAsImplicit
      ++ #[⟨motiveBinder, .implicit⟩]
      ++ (constructors.map λ c => ⟨c.recursiveMotiveFun, .default⟩)
      ++ #[⟨tMotiveBinder, .default⟩]
    let recursionTypeHead := mkApp (mkIdent motiveBinder.name) #[mkIdent tMotiveBinder.name]
    let recursionType : Term := recursionTypeBinders.foldr mkDepArrow recursionTypeHead
    let recursionBody := mkMatchSimple (mkIdent tMotiveBinder.name)
          <| constructors.map λ c => 
            mkMatchAlt #[mkExplicitAppBinders (mkIdent c.globalName.getSuffix) c.typeBinders]
            <| mkExplicitApp (mkIdent c.recursiveMotiveFun.name) 
              <| (c.typeBinders.map λ x => mkIdent x.name) 
                ++ (c.typeBindersUsedRecursively.map λ ref => mkParen <|
                  mkApp (mkIdent recursionDeclarationLocalName.getSuffix)
                    <| (constructors.map λ c => mkIdent c.recursiveMotiveFun.name)
                    ++ #[mkIdent ref.name])
    IO.println s!"recursion type: {prettyPrint recursionType}"
    IO.println s!"recursion body: {prettyPrint recursionBody}"
    elabCommand <| mkDefSimple recursionDeclarationLocalName 
      (mkExplicitLevels #[]) recursionTypeBinders recursionTypeHead recursionBody

  elab "implement_recursion" inductiveTypeIdent:ident : command => implementRecursionFunction inductiveTypeIdent.getId

  end Meta.Impl.Rec
end


section
  namespace Meta.Impl.Rec.Test
  inductive Binary_Tree : (type : Type) → Type
  | Nil : Binary_Tree type
  | Node (value : type) (left_subtree right_subtree : Binary_Tree type) : Binary_Tree type
  -- implement_recursion Binary_Tree
  #print Binary_Tree.rec
  -- #print Binary_Tree.recursion
 
  open Binary_Tree in
  inductive bst : {type : Type} → (tree : Binary_Tree type) → Prop
  | c (v : type) {l r : Binary_Tree type} : (hl : bst l) → (hr : bst r) → bst (Node v l r)
  -- implement_recursion bst
  #print bst.rec
  -- #print bst.recursion


  -- open Lean Meta Elab Term Command in
  -- elab "elab1" : command => do 
  --   let s <- `(sorry)
  --   elabCommand s
  --   IO.println $ Syntax.prettyPrint s
  -- -- elab1

  end Meta.Impl.Rec.Test
end
