import Playground.Misc.MetaAttr0

set_option trace.to_struct true

@[to_struct]
inductive Formula : (L : Type) → Type where
  | bot : Formula L
  | not : (p : L) → Formula L
  | and : (p : L) → (q : L) → Formula L
#print Formula.bot.struct
#print Formula.not.struct
#print Formula.and.struct

-- inductive Formula.and.struct : Type → Type 1
-- | mk : L → L → struct L
-- #print Formula.and.struct


-- noncomputable def Formula.and.struct.p (x : struct L) : L := 
--   @struct.rec (λ L _ => L) (λ _ p q => p) _ x

-- theorem Formula.and.struct.th0 (p q : L) : (mk L p q).p = p := rfl

-- def Formula.and.struct.p (x : struct L) : L := 
--   match x with
--   | .mk p q =>
--     sorry

inductive N
| zero : N
| succ : N → N

-- instance : N := N.zero
