structure predicates :=
mk :: (lower_triangular : string → bool)

inductive base_term : Type
| matrix : string → base_term
| plus : base_term → base_term → base_term
| times : base_term → base_term → base_term
| transpose : base_term → base_term
| one : base_term
| zero : base_term

instance : has_zero base_term := ⟨base_term.zero⟩
instance : has_one base_term := ⟨base_term.one⟩
instance : has_mul base_term := ⟨base_term.times⟩
instance : has_add base_term := ⟨base_term.plus⟩

def is_lower_triangular : predicates → term → bool
| p (term.matrix name) := p.lower_triangular name
| p (term.times a b) := is_lower_triangular a ∧ is_lower_triangular b
| ...ℕ
apredicates → term → bool/Prop
section
  open base_term
  def plus_com : base_term → base_term → Prop
  | (plus a b) (plus c d) := (a == c ∧ b == d) ∨ (a == d ∧ b == c)
  | x y := x == y

  def term1 := base_term  plus_com

  def plus_assoc : base_term → base_term → Prop
  | (plus a (plus b c)) (plus (plus d e) f) := a == d ∧ b == e ∧ c == f
  | (plus (plus a b) c) (plus d (plus e f)) := a == d ∧ b == e ∧ c == f
  | x y := x == y

  def times_assoc : base_term → base_term → Prop
  | (times a (times b c)) (times (times d e) f) := a == d ∧ b == e ∧ c == f
  | (times (times a b) c) (times d (times e f)) := a == d ∧ b == e ∧ c == f
  | x y := x == y

  def left_distr : base_term → base_term → Prop
mutual def term_reduce_one, term_equiv
with term_reduce_one : base_term → base_term → Prop
| (base_term.matrix a) (base_term.matrix b) := a == b
| (base_term.matrix _) _ := false
| (base_term.plus a b) (base_term.plus c d) := (term_equiv a c ∧ term_equiv b d) ∨ (term_equiv a d ∧ term_equiv b c)
| (base_term.plus a 0) b := term_equiv a b
| (base_term.plus 0 a) b := term_equiv a b
| (base_term.plus _ _) _ := false

| (base_term.times a b) (base_term.times c d) := term_equiv a c ∧ term_equiv b d
| (base_term.times a 1) b := term_equiv a b
| (base_term.times 1 a) b := term_equiv a b
| (base_term.times 0 a) b := term_equiv 0 b
| (base_term.times a 0) b := term_equiv 0 b
| (base_term.times _ _) _ := false

| base_term.zero base_term.zero := true
| base_term.zero _ := false
| base_term.one base_term.one := true
| base_term.one _ := false

| (base_term.transpose (base_term.transpose a)) b := term_equiv a b
| (base_term.transpose a) (base_term.transpose b) := term_equiv a b
| (base_term.transpose (base_term.times a b)) (base_term.times (base_term.transpose d) (base_term.transpose c)) := term_equiv a c ∧ term_equiv b d
| (base_term.transpose _) _ := false
with term_equiv : base_term → base_term → Prop
| a b := term_reduce_one a b ∨ term_reduce_one b a
