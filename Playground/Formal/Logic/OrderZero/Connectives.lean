import Playground.Formal.Logic.Language

namespace Formal.Logic.OrderZero
namespace Connectives
variable (L) [Logic.Language L]
class Imply where connective : Formula L → Formula L → Formula L
scoped infix:30 " ⇒ " => Imply.connective
class And where connective : Formula L → Formula L → Formula L
scoped infixr:35 " ∧ " => And.connective
class Or where connective : Formula L → Formula L → Formula L
scoped infixr:30 " ∨ " => Or.connective
class Not where connective : Formula L → Formula L
scoped notation:max "¬" p:40 => Not.connective p
class Bot where connective : Formula L
scoped notation:35 "⊥" => Bot.connective
end Connectives
end Formal.Logic.OrderZero
