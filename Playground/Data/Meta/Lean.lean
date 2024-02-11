import Lean
import Std.Data.Array.Basic

section
  namespace Lean.Expr

  structure Binder where
    name : Name
    type : Expr

  structure ArrowBinder where
    binder : Binder
    binderInfo : BinderInfo

  namespace ArrowBinder
  def name : ArrowBinder → Name := λ x => x.binder.name
  def type : ArrowBinder → Expr := λ x => x.binder.type
  end ArrowBinder

  def getArrowBinders (type : Expr) : Array ArrowBinder :=
    match type with
    | .forallE currName curr next binderInfo =>
      Array.mk <| ⟨⟨currName, curr⟩, binderInfo⟩ :: (getArrowBinders next).data
    | _ => #[]

  def getArrowBindersNames (type : Expr) : Array Name :=
    type.getArrowBinders.map λ x => x.name

  def getArrowOutput (type : Expr) : Expr :=
    match type with
    | .forallE _ _ next _ => getArrowOutput next
    | output => output

  end Lean.Expr
end



section
  namespace Lean.Syntax

  structure Binder where
    name : Name
    type : Term
  deriving Inhabited

  structure ArrowBinder where
    binder : Binder
    binderInfo : BinderInfo
  deriving Inhabited

  namespace ArrowBinder
  def name : ArrowBinder → Name := λ x => x.binder.name
  def type : ArrowBinder → Term := λ x => x.binder.type
  end ArrowBinder

  def mkBinder (tail : ArrowBinder) : Syntax :=
    let (binderNodeName, op, cl) :=
      if tail.binderInfo == .default then (`Lean.Parser.Term.explicitBinder, "(", ")")
      else if tail.binderInfo == .implicit then (`Lean.Parser.Term.implicitBinder, "{", "}")
      else panic! "mkDepArrow binder not supported"
    mkNode binderNodeName #[
      mkAtom op,
      mkNullNode #[mkIdent tail.name],
      mkNullNode #[mkAtom ":", tail.type],
      mkNullNode,
      mkAtom cl
    ]

  def mkExplicit (stx : Term) : Term :=
    ⟨mkNode `Lean.Parser.Term.explicit #[mkAtom "@", stx]⟩

  def mkExplicitApp (fn : Term) : (args : Array Term) → Term
    | #[]  => fn
    | args => ⟨mkNode `Lean.Parser.Term.app #[mkExplicit fn, mkNullNode args]⟩

  def mkFun (inputs : Array Syntax) (body : Term) : Term :=
    if inputs.size = 0 then body
    else
      ⟨mkNode `Lean.Parser.Term.fun #[mkAtom "λ",
        mkNode `Lean.Parser.Term.basicFun #[mkNullNode inputs, mkAtom "=>", body]
      ]⟩

  def mkParen (body : Term) : Term :=
    ⟨mkNode `Lean.Parser.Term.paren #[mkAtom "(", mkNullNode #[body], mkAtom ")"]⟩

  def mkMatchAlt (patternVars : Array Syntax) (body : Term) : Syntax :=
    mkNode `Lean.Parser.Term.matchAlt #[
      mkAtom "|", mkNullNode #[mkNullNode patternVars], mkAtom "=>", body]

  def mkSorry : Syntax := mkNode `Lean.Parser.Term.sorry #[mkAtom "sorry"]

  def mkMatchSimple (matchedVar : Syntax) (alts : Array Syntax) : Term :=
    ⟨mkNode `Lean.Parser.Term.match #[
      mkAtom "match", mkNullNode, mkNullNode,
      mkNullNode #[mkNode `Lean.Parser.Term.matchDiscr #[mkNullNode, matchedVar]],
      mkAtom "with", mkNode `Lean.Parser.Term.matchAlts #[mkNullNode <| alts]
    ]⟩

  def mkExplicitLevels (l : Array Name) : Syntax :=
    if l.isEmpty then mkNullNode
    else mkNullNode #[
      mkAtom ".{",
      mkNullNode <| Array.mk <| (l.toList.map λ x => (mkIdent x).raw).intersperse <| mkAtom ",",
      mkAtom "}"
    ]

  def mkDeclModifiersSimple : Syntax :=
    mkNode `Lean.Parser.Command.declModifiers
      #[mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode, mkNullNode]

  def mkDeclarationSimple (decl : Syntax) : Syntax :=
    mkNode `Lean.Parser.Command.declaration #[mkDeclModifiersSimple, decl]

  def mkTypeSigSimple (binders : Array ArrowBinder) (type : Term) : Syntax :=
    mkNode `Lean.Parser.Command.optDeclSig #[
      mkNullNode <| binders.map mkBinder, mkNullNode #[mkNode `Lean.Parser.Term.typeSpec #[mkAtom ":", type]]
    ]

  def mkDefSimple (name : Name) (levels : Syntax) (binders : Array ArrowBinder) (type : Term) (val : Term) : Syntax :=
    mkDeclarationSimple <|
      mkNode `Lean.Parser.Command.def #[
        mkAtom "def",
        mkNode `Lean.Parser.Command.declId #[mkIdent name, levels],
        mkTypeSigSimple binders type,
        mkNode `Lean.Parser.Command.declValSimple #[mkAtom ":=", val, mkNullNode],
        mkNullNode, mkNullNode, mkNullNode
      ]

  def mkStructFieldSimple (name : Name) (type : Term) : Syntax :=
    mkNode `Lean.Parser.Command.structSimpleBinder #[
      mkDeclModifiersSimple, mkIdent name, mkTypeSigSimple #[] type, mkNullNode
    ]

  def mkStructSimple (name : Name) (levels : Syntax) (declBinders : Array Syntax) (fields : Array Syntax) : Syntax :=
    mkDeclarationSimple <|
      mkNode `Lean.Parser.Command.structure #[
        mkNode `Lean.Parser.Command.structureTk #[mkAtom "structure"],
        mkNode `Lean.Parser.Command.declId #[mkIdent name, levels],
        mkNullNode declBinders,
        mkNullNode,
        mkNullNode,
        mkNullNode #[
          mkAtom "where",
          mkNullNode,
          mkNode `Lean.Parser.Command.structFields #[mkNullNode fields]
        ],
        mkNode `Lean.Parser.Command.optDeriving #[mkNullNode]
      ]

  def mkArrow (tail head : Term) : Term :=
    ⟨mkNode `Lean.Parser.Term.arrow #[tail, mkAtom "→", head]⟩

  def mkDepArrow (tail : ArrowBinder) (head : Term) : Term :=
    ⟨mkNode `Lean.Parser.Term.depArrow #[mkBinder tail, mkAtom "→", head]⟩

  def mkSort (levelName : Name) : Term :=
    ⟨mkNode `Lean.Parser.Term.sort #[mkAtom "Sort", mkNullNode #[mkIdent levelName]]⟩

  def mkProp : Term :=
    ⟨mkNode `Lean.Parser.Term.prop #[mkAtom "Prop"]⟩


  partial def getArrowBinders : Term → Array ArrowBinder
  | `(($ids* : $curr) → $next) =>
    let arr := ids.map λ
      | ⟨ident _ _ name _⟩ => ⟨⟨name, curr⟩, .default⟩
      | s => panic! s!"bad stx: {s}"
    arr ++ getArrowBinders next
  | `({$ids* : $curr} → $next) =>
    let arr := ids.map λ
      | ⟨ident _ _ name _⟩ => ⟨⟨name, curr⟩, .implicit⟩
      | s => panic! s!"bad stx: {s}"
    arr ++ getArrowBinders next
  | `(∀ $binders*, $next) =>
    let arr := binders.map λ
      | ⟨node _ `Lean.Parser.Term.explicitBinder #[
          atom .., node _ _ ids, node _ _ #[atom .., type], node .., atom ..]⟩ => ids.map λ
            | ident _ _ name _ => ⟨⟨name, ⟨type⟩⟩, .default⟩
            | s => panic! s!"bad stx: {s}"
      | ⟨node _ `Lean.Parser.Term.implicitBinder #[
          atom .., node _ _ ids, node _ _ #[atom .., type], atom ..]⟩ => ids.map λ
            | ident _ _ name _ => ⟨⟨name, ⟨type⟩⟩, .implicit⟩
            | s => panic! s!"bad stx: {s}"
      | s => panic! s!"bad stx: {s}"
    arr.join ++ getArrowBinders next
  | `($curr → $next) => #[⟨⟨.anonymous, curr⟩, .default⟩] ++ getArrowBinders next
  | _ => #[]

  def getArrowBindersNames (type : Term) : Array Name :=
    (getArrowBinders type).map λ x => x.name

  partial def getArrowOutput (type : Term) : Term :=
    match type with
    | `(($ids* : $curr) → $next) => getArrowOutput next
    | `({$ids* : $curr} → $next) => getArrowOutput next
    | `(∀ $binders*, $next) => getArrowOutput next
    | `($curr → $next) => getArrowOutput next
    | output => output

  end Lean.Syntax
end


section
  namespace Lean.Name

  def updateRoot : Name → Name → Name
    | anonymous, _    => anonymous
    | str anonymous .., newP => newP
    | num anonymous .., newP => newP
    | str (str p' s') s, newP => mkStr ((str p' s').updateRoot newP) s
    | str (num p' n') s, newP => mkStr ((num p' n').updateRoot newP) s
    | num (str p' s') s, newP => mkNum ((str p' s').updateRoot newP) s
    | num (num p' n') s, newP => mkNum ((num p' n').updateRoot newP) s

  def getLast (name : Name) : Name :=
    name.components.getLastD .anonymous

  def getSuffix (name : Name) : Name :=
    name.components.getLastD .anonymous

  end Lean.Name
end
