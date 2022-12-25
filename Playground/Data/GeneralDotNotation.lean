
syntax:1021 term:1021 "·" term:1022 : term
macro_rules
  | `($a·$f $args*) => `($f $a $args*)
  | `($a·$f)        => `($f $a)

example [Add a] (x y : a) (f : a → b) (g : b → c) (h : c → a) : a := y + x·f·g·h + x·id
