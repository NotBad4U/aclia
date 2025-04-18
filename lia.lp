require open aclia.Prop;
require open aclia.Set;
require open aclia.Eq;
require open aclia.Z;
require open aclia.Classic;
require open aclia.Alethe;
require open aclia.List;


notation ≥ infix 10;

constant symbol R : TYPE;

symbol var : ℤ → ℤ → R;
/* semantics: [var k x] = k * x
note that the second argument could be any type that has a ring structure
(we then would take R : TYPE → TYPE) */
constant symbol cst:ℤ → R;
symbol opp:R → R;
right associative commutative symbol add:R → R → R;

rule var _ 0 ↪ cst 0;

rule opp (var $x $k) ↪ var $x (— $k)
with opp (cst $k) ↪ cst (— $k)
with opp (opp $x) ↪ $x
with opp (add $x $y) ↪ add (opp $x) (opp $y);
// note that opp is totally defined on terms built with var, cst, opp and add, i.e. no normal form contains opp

rule add (var $x $k) (var $x $l) ↪ var $x ($k + $l)
with add (var $x $k) (add (var $x $l) $y) ↪ add (var $x ($k + $l)) $y
with add (cst $k) (cst $l) ↪ cst ($k + $l)
with add (cst $k) (add (cst $l) $y) ↪ add (cst ($k + $l)) $y
with add (cst 0) $x ↪ $x
with add $x (cst 0) ↪ $x;

// example:
compute λ x y z, add (add (var 1 x) (add (opp (var 1 y)) (var 1 z))) (add (var 1 y) (var 1 x));

// multiplication by a constant (optional)
symbol mul:ℤ → R → R;
rule mul $k (var $z $l) ↪ var $z ($k * $l)
with mul $k (opp $r) ↪ mul (— $k) $r
with mul $k (add $r $s) ↪ add (mul $k $r) (mul $k $s)
with mul $k (cst $z) ↪ cst ($k * $z)
with mul $k (mul $l $z) ↪ mul ($k * $l) $z;
// note that mul is totally defined on terms built from var, cst, opp, add and mul, i.e. no normal form contains mul

// reification
// WARNING: this symbol is declared as sequential
// and the reduction relation is not stable by substitution
sequential symbol reify : ℤ → R;

rule reify 0 ↪ cst 0
with reify (Zpos $x) ↪ cst (Zpos $x)
with reify (Zneg $x) ↪ cst (Zneg $x)
with reify (— $x) ↪ opp (reify $x)
with reify ($x + $y) ↪ add (reify $x) (reify $y)

with reify (0 * $y) ↪ mul 0 (reify $y)
with reify (Zpos $x * $y) ↪ mul (Zpos $x) (reify $y)
with reify (Zneg $x * $y) ↪ mul (Zneg $x) (reify $y)
with reify ($y * 0) ↪ mul 0 (reify $y)
with reify ($y * Zpos $x) ↪ mul (Zpos $x) (reify $y)
with reify ($y * Zneg $x) ↪ mul (Zneg $x) (reify $y)

with reify $x ↪ var $x 1; // must be the last rule for reify

// eval function
symbol denote: R → ℤ;
rule denote (var $x $k) ↪ $k * $x
with denote (cst $k) ↪ $k
with denote (opp $x) ↪ — (denote $x)
with denote (add $x $y) ↪ denote $x + denote $y
;


symbol Zle_not_gt n m:  πᶜ ((n ≤ m) = ¬ (n > m));
symbol Zlt_not_ge n m:  πᶜ ((n < m) = ¬ (n ≥ m));
symbol Zge_not_lt : Π n: ℤ, Π m: ℤ, πᶜ ((n ≥ m) = ¬ (n < m));
symbol Zgt_not_le : Π n: ℤ, Π m: ℤ, πᶜ ((n > m) = ¬ (n ≤ m));
symbol Zmult_gt_compat c a b : π (c > 0) → π (a > b) → π (c * a > c * b) ;
symbol Zmult_ge_compat c a b : π (c > 0) → π (a ≥ b) → π (c * a ≥ c * b);
symbol Zgt_le_succ_r a b: πᶜ (a > b) → πᶜ (a ≥ b + 1);
symbol Zinv_lt a b: πᶜ (a < b) → πᶜ (— a > — b);
symbol Zsum_geq_s a b c d : πᶜ (a ≥ b) → πᶜ (c ≥ d) → πᶜ (a + c ≥ b + d);
symbol Z_diff_geq_Z0 a b: πᶜ (a ≥ b) → πᶜ (a - b ≥ 0);
symbol Z_diff_gt_Z0 a b: πᶜ (a > b) → πᶜ (a - b > 0);
symbol Zgt_le_succ_r_eq a b: πᶜ ((a > b) = (a ≥ b + 1));
symbol Zinv_lt_eq a b: πᶜ ((a < b) = (— a > — b));
symbol Zinv_le_eq a b: πᶜ ((a ≤ b) = (— a ≥ — b));
symbol Z_diff_geq_Z0_eq a b: πᶜ ((a ≥ b) = (a - b ≥ 0));
symbol Z_diff_gt_Z0_eq a b: πᶜ ((a > b) = (a - b > 0));
symbol Z_diff_eq_Z0_eq a b: πᶜ ((a = b) = (a - b = 0));
symbol Z_eq_antisym (a b: τ int):  πᶜ ((¬ (a = b)) = ¬ (a ≥ b));
symbol Zmult_eq_compat_eq (c a b: τ int) : πᶜ ((¬ (a = b)) = ¬ (c * a = c * b));
symbol Zmult_gt_compat_eq c a b : πᶜ (¬ (a > b) = ¬ (c * a > c * b)) ;
symbol Zmult_ge_compat_eq c a b : πᶜ (¬ (a ≥ b) = ¬ (c * a ≥ c * b)) ;
symbol la_mult_neg_eq [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 = t3) ⇒ᶜ (t1 * t2) = (t1 * t3));
symbol la_mult_neg_lt t1 t2 t3 : πᶜ (t1 < 0) → πᶜ (t2 < t3) → πᶜ ((t1 * t2) > (t1 * t3));
symbol la_mult_neg_leq [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 ≤ t3) ⇒ᶜ (t1 * t2) ≥ (t1 * t3));
symbol la_mult_neg_gt [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 > t3) ⇒ᶜ (t1 * t2) < (t1 * t3));
symbol la_mult_neg_ge [t1 t2 t3] : πᶜ ((t1 < 0) ⇒ᶜ (t2 ≥ t3) ⇒ᶜ (t1 * t2) ≤ (t1 * t3));

symbol inj : Π x: ℤ, πᶜ ((denote (reify x)) = x);
