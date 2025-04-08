
require Stdlib.Nat as Nat;
open Stdlib.Nat;
require open Stdlib.Pos Stdlib.Z Stdlib.Prod Stdlib.Set Stdlib.List Stdlib.Eq Stdlib.Prop Stdlib.FOL Stdlib.Bool Stdlib.Comp;

// type for arithmetic expressions

// constant symbol g:Set;
// constant symbol G:TYPE;
// rule τ g ↪ G;

// constant symbol Cst: ℤ → G;
// constant symbol Var: ℕ → ℤ → G;
// constant symbol Add: G → G → G;
  /* these are the only constructors;
  multiplication by a constant and opposite are defined hereafter */

inductive G: TYPE ≔
| Cst: ℤ → G
| Var: ℕ → ℤ → G
| Add: G → G → G
; 

constant symbol g : Set;
rule τ g ↪ G;

symbol mul: ℤ → G → G;

rule mul $k (Cst $l) ↪ Cst ($k * $l)
with mul $k (Var $i $l) ↪ Var $i ($k * $l)
with mul $k (Add $x $y) ↪ Add (mul $k $x) (mul $k $y);

symbol opp ≔ mul (— 1);

// highest variable index in a term

symbol varmax : G → ℕ;

rule varmax (Cst _) ↪ _0
with varmax (Var $k _) ↪ $k
with varmax (Add $x $y) ↪ max (varmax $x) (varmax $y);

// evaluation of an arithmetic expression together with a list of values for variables; variables with indexes not in the list are interpreted by 0

symbol val: τ(g × list int) → ℤ;

symbol not_found: ℤ;

rule val (Cst $k ‚ _) ↪ $k
with val (Var $i $k ‚ $l) ↪ (nth not_found $l $i) * $k
with val (Add $x $y ‚ $l) ↪ val ($x ‚ $l) + val ($y ‚ $l);

// some useful type

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

// index of a value in a list; returns New if the value is not definitionally equivalent to some element of the list

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k $x □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

// reification: given a Lambdapi term x of type ℤ, compute an expression in G and a list of values whose evaluation is equal to x

sequential symbol rfy: τ(list int) → ℤ → τ(g × list int);

rule rfy $l ($x + $y) ↪
  let x ≔ rfy $l $x in
    let y ≔ rfy (x ₂) $y in
      Add (x ₁) (y ₁) ‚ (y ₂)
with rfy $l (— $x) ↪
  let x ≔ rfy $l $x in
  opp (x ₁) ‚ (x ₂)

with rfy $l ($x - $y) ↪ rfy $l ($x + — $y)

with rfy $l 0 ↪ Cst 0 ‚ $l
with rfy $l (Zpos $k) ↪ Cst (Zpos $k) ‚ $l
with rfy $l (Zneg $k) ↪ Cst (Zneg $k) ‚ $l

with rfy $l (0 * $x) ↪ Cst 0 ‚ $l
with rfy $l (Zpos $k * $x) ↪
  let x ≔ rfy $l $x in
  mul (Zpos $k) (x ₁) ‚ x ₂
with rfy $l (Zneg $k * $x) ↪
  let x ≔ rfy $l $x in
  mul (Zneg $k) (x ₁) ‚ x ₂
with rfy $l ($x * Zpos $k) ↪
  let x ≔ rfy $l $x in
  mul (Zpos $k) (x ₁) ‚ x ₂
with rfy $l ($x * Zneg $k) ↪
  let x ≔ rfy $l $x in
  mul (Zneg $k) (x ₁) ‚ x ₂

with rfy $l $x ↪
  case (index _0 $x $l) (λ i, Var i 1 ‚ $l) (λ i, Var i 1 ‚ ($l ++ ($x ⸬ □)))
;

symbol x: τ int;
symbol y: τ int;


symbol reify ≔ rfy □;

opaque symbol reify_correct x: π(val(reify x) = x) ≔
begin
induction
{reflexivity}
{reflexivity}
{reflexivity}
end;

// aliens (constants and variables) of an arithmetic expression

symbol aliens: G → τ(list g);

rule aliens (Cst $k) ↪ Cst $k ⸬ □
with aliens (Var $i $k) ↪ Var $i $k ⸬ □
with aliens (Add $x $y) ↪ aliens $x ++ aliens $y;

// ordering of natural numbers

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

// normalization of arithmetic expressions

symbol remove0 : G → τ(list g) → τ(list g);

rule remove0 (Cst 0) $l ↪ $l
with remove0 (Cst (Zpos $k)) $l ↪ Cst (Zpos $k) ⸬ $l
with remove0 (Cst (Zneg $k)) $l ↪ Cst (Zneg $k) ⸬ $l
with remove0 (Var $i 0) $l ↪ $l
with remove0 (Var $i (Zpos $k)) $l ↪ Var $i (Zpos $k) ⸬ $l
with remove0 (Var $i (Zneg $k)) $l ↪ Var $i (Zneg $k) ⸬ $l
//ac: added case to prove norm_correct
with remove0 _ □ ↪ □
;


symbol insert: G → τ(list g) → τ(list g);

rule insert $x □ ↪ remove0 $x □
with insert (Cst 0) $l ↪ $l
with insert (Cst (Zpos $k)) (Cst $k' ⸬ $l) ↪ remove0 (Cst (Zpos $k + $k')) $l
with insert (Cst (Zneg $k)) (Cst $k' ⸬ $l) ↪ remove0 (Cst (Zneg $k + $k')) $l
with insert (Cst (Zpos $k)) (Var $i $k' ⸬ $l) ↪ Cst (Zpos $k) ⸬ insert (Var $i $k') $l
with insert (Cst (Zneg $k)) (Var $i $k' ⸬ $l) ↪ Cst (Zneg $k) ⸬ insert (Var $i $k') $l
with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
with insert (Var $i $k) (Var $j $k' ⸬ $l) ↪
  case_Comp (compN $i $j)
            (remove0 (Var $i ($k + $k')) $l)
            (Var $i $k ⸬ Var $j $k' ⸬ $l)
            (Var $j $k' ⸬ insert (Var $i $k) $l);

symbol sort: τ(list g) → τ(list g);

rule sort □ ↪ □
with sort ($x ⸬ $l) ↪ insert $x (sort $l);

symbol comb: G → τ(list g) → G;

rule comb $x □ ↪ $x
with comb $x ($y ⸬ $l) ↪ Add $x (comb $y $l);

symbol caseL : τ(list g) → τ g → (τ g → τ(list g) → τ g) → τ g;

rule caseL □ $a _ ↪ $a
with caseL ($x ⸬ $l) _ $f ↪ $f $x $l;

symbol norm x ≔ caseL (sort (aliens x)) (Cst 0) comb;

opaque symbol max_geq m n1 n2 :
  π (istrue ((max n1 n2) Nat.≤ m) ⇒ istrue (n1 Nat.≤ m) ∧ istrue (n2 Nat.≤ m)) ≔
begin
admitted;

symbol toto: τ g;

opaque symbol norm_correct (x: G) l :
  π(varmax x Nat.≤ size l) → π(val(norm x ‚ l) = val(x ‚ l)) ≔
begin
induction
{
  induction
  {reflexivity}
  {reflexivity}
  {reflexivity}
}
{
  assume i;
  induction
  { assume l H; simplify norm; reflexivity }
  { assume k ctx l; reflexivity }
  { assume k ctx l; reflexivity }
}
{
  assume x IH1;
  assume y IH2;
  //assume l H;
  simplify;
  induction
  {
    assume H;
    compute (val (x ‚ □)); //missing Lemma where reify with empty list return a Cst
    admit
  }
  {
    // simplify norm;
    assume h tl H H2;
    simplify;
    set aliensX ≔ aliens x;
    set aliensY ≔ aliens y;
    type (head toto (aliensX ++ aliensY)) ⸬ (behead (aliensX ++ aliensY));
    have G: π ((aliensX ++ aliensY) = ((head toto (aliensX ++ aliensY)) ⸬ (behead (aliensX ++ aliensY)))) {admit};
    rewrite G;
    simplify;
  }
}  
admitted;

symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂));

symbol ≐_decides_neq [x y] : π (x ≐ y ≠ Eq ⇒ x ≠ y) ≔
begin
admitted;

symbol l1 x y : π((x + y) - (x + y) ≠ 1) ≔
begin
  assume x y;
  refine ≐_decides_neq _;
  rewrite left .[z in z ≐ _] reify_correct;
  set e ≔ reify ((x + y) - (x + y));
  rewrite .[z in val z] eta_prod;
  compute e;
  rewrite left norm_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
end;

symbol ≱ : τ int → τ int → Prop ≔ λ x y, ¬ (x ≥ y);
notation ≱ infix 10;

symbol ≐_decides_ngeq [x y] : π (x ≐ y ≠ Gt ∧ x ≐ y ≠ Eq ⇒ x ≱ y) ≔
begin
admitted;

private symbol test ≔ (x + y) - (x +  y);

compute let e ≔ (reify test) in val (norm (e ₁) ‚ (e ₂));