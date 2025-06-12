require aclia.Nat as Nat;
open aclia.Nat;
require open aclia.Pos aclia.Z aclia.Prod aclia.Set aclia.List aclia.Eq aclia.Prop aclia.FOL aclia.Bool aclia.Comp;

// type for arithmetic expressions

inductive G: TYPE ≔
| Cst: ℤ → G
| Var: ℕ → ℤ → G
| Add: G → G → G
; 

constant symbol g : Set;
rule τ g ↪ G;

// multiplication by a constant

symbol mul: ℤ → G → G;

rule mul $k (Cst $l) ↪ Cst ($k * $l)
with mul $k (Var $i $l) ↪ Var $i ($k * $l)
with mul $k (Add $x $y) ↪ Add (mul $k $x) (mul $k $y);

// opposite

symbol opp ≔ mul (— 1);

// highest variable index in a term

symbol varmax : G → ℕ;

rule varmax (Cst _) ↪ _0
with varmax (Var $k _) ↪ $k
with varmax (Add $x $y) ↪ max (varmax $x) (varmax $y);

/* evaluation of an arithmetic expression wrt a list of values for variables

variables with indexes not in the list are interpreted by 0 */

opaque symbol nth ≔ nth 0;

symbol val: τ(g × list int) → ℤ;

rule val (Cst $k ‚ _) ↪ $k
with val (Var $i $k ‚ $l) ↪ nth $l $i * $k
with val (Add $x $y ‚ $l) ↪ val ($x ‚ $l) + val ($y ‚ $l);

symbol va l x ≔ val (x ‚ l);

// some useful type (use inductive instead?)

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

/* index of a value in a list: returns New if the value is not
definitionally equivalent to some element of the list */

symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x (_ ⸬ $l) ↪ index ($k +1) $x $l;

/* reification: given a Lambdapi term x of type ℤ, compute an
expression in G and a list of values whose evaluation is equal to
x. WARNING: rfy is sequential. */

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

with rfy $l (0 * _) ↪ Cst 0 ‚ $l
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

symbol isNotAdd: τ g → Prop;

rule isNotAdd (Cst _) ↪ ⊤
with isNotAdd (Var _ _ ) ↪ ⊤
with isNotAdd (Add _ _ ) ↪ ⊥;

symbol no_Add : τ(list g) → Prop;

rule no_Add □ ↪ ⊤
with no_Add ($g ⸬ $gs) ↪  isNotAdd $g ∧ no_Add $gs;

opaque symbol no_Add_aliens x : π(no_Add (aliens x)) ≔
begin
admitted;

// ordering of natural numbers

symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
admitted;

// normalization of arithmetic expressions

/*
symbol merge : τ(list g) → τ(list g);

rule merge □ ↪ □
with merge ($x ⸬ □) ↪ $x ⸬ □
with merge (Cst $k ⸬ Cst $k' ⸬ $l) ↪ merge (Cst ($k + $k') ⸬ $l)
with merge (Cst $k ⸬ Var $i $ki ⸬ $l) ↪ Cst $k ⸬ merge (Var $i $ki ⸬ $l)
with merge (Var $i $ki ⸬ Var $j $kj ⸬ $l) ↪
  case_Comp (compN $i $j)
            (merge (Var $i ($ki + $kj) ⸬ $l))
            (Var $i $ki ⸬ merge (Var $j $kj ⸬ $l))
            (Var $i $ki ⸬ merge (Var $j $kj ⸬ $l))
;
*/

symbol remove0 : τ(list g) → τ(list g);

rule remove0 □ ↪ □
with remove0 (Cst 0 ⸬ $l) ↪ remove0 $l
with remove0 (Cst (Zpos $k) ⸬ $l) ↪ Cst (Zpos $k) ⸬ remove0 $l
with remove0 (Cst (Zneg $k) ⸬ $l) ↪ Cst (Zneg $k) ⸬ remove0 $l
with remove0 (Var _ 0 ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (Zpos $k) ⸬ $l) ↪ Var $i (Zpos $k) ⸬ remove0 $l
with remove0 (Var $i (Zneg $k) ⸬ $l) ↪ Var $i (Zneg $k) ⸬ remove0 $l
;

symbol sum: τ(list g) → τ g;

rule sum □ ↪ Cst 0
with sum ($x ⸬ $l) ↪ Add $x (sum $l);

symbol vas l xs ≔ va l (sum xs);

opaque symbol remove0_correct l gs : π (no_Add gs) →  π (val (sum (remove0 gs) ‚ l) = val (sum gs ‚ l)) ≔
begin
  assume l;
  induction // on l
  {
    reflexivity
  }
  {
    induction // on g
    {
      // Case Cst k
      induction 
      // Case Z0
      { assume gs IH H;  apply IH;  refine (∧ₑ₂ H) }
      // Case Zpos
      { assume c gs IH H; simplify; rewrite (IH (∧ₑ₂ H)); reflexivity }
      // Case Zneg
      { assume c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity }
    }
    {
      // Case Var i k
      assume i;
      induction // on k
      {assume gs IH H;  apply IH; refine (∧ₑ₂ H)} // Case Z0
      { assume c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity } // Case Zpos
      { assume c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity } // Case Zneg
    }
    {
      // Case Add g1 g2
      // That violate the invariant: no_Add gs
      simplify;
      assume g1 IHg1 g2 IHg2 gs IHg H;
      refine ⊥ₑ (∧ₑ₁ H)
    }
  }
end;

symbol insert: G → τ(list g) → τ(list g);

/*
rule insert (Cst $k) (Cst $k' ⸬ $l) ↪ Cst $k ⸬ Cst $k' ⸬ $l
with insert (Cst $k) (Var $i $k' ⸬ $l) ↪ Cst $k ⸬ Var $i $k' ⸬ $l
with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
with insert (Var $i $ki) (Var $j $kj ⸬ $l) ↪
     case_Comp (compN $i $j)
            (Var $i $ki ⸬ Var $j $kj ⸬ $l)
            (Var $i $ki ⸬ Var $j $kj ⸬ $l)
            (Var $j $kj ⸬ insert (Var $i $ki) $l);
*/

rule insert (Cst $k) (Cst $k' ⸬ $l) ↪ Cst ($k + $k') ⸬ $l
with insert (Cst $k) (Var $i $k' ⸬ $l) ↪ Cst $k ⸬ Var $i $k' ⸬ $l
with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
with insert (Var $i $ki) (Var $j $kj ⸬ $l) ↪
     case_Comp (compN $i $j)
            (Var $i ($ki + $kj) ⸬ $l)
            (Var $i $ki ⸬ Var $j $kj ⸬ $l)
            (Var $j $kj ⸬ insert (Var $i $ki) $l)
with insert $x □ ↪ $x ⸬ □;

// to be moved to Nat
opaque symbol distr*+ x y z : π(x * (y + z) = x * y + x * z) ≔
begin
admitted;

symbol insert_correct l gs g : π (no_Add (g ⸬ gs)) → π (val (sum (insert g gs) ‚ l) =  val (g ‚ l) +  val (sum gs ‚ l)) ≔
begin
assume l;
induction
{ reflexivity }
{
  // /assume g' gs IH g Haliens;
  induction
  {
    // Cst k
    assume k gs IH;
    induction
    // Cst k
    { assume k2 H; simplify; rewrite +_assoc; reflexivity }
    // Var i j
    {
      assume i c H;
      simplify;
      have g: π (no_Add (Var i c ⸬ gs)) { 
        apply ∧ᵢ
        { refine ∧ₑ₁ H; }
        { refine ∧ₑ₂ (∧ₑ₂ H); }
       };
      rewrite IH (Var i c) g;
      rewrite left +_assoc k (val (Var i c ‚ l)) (val (sum gs ‚ l));
      rewrite +_com k;
      rewrite +_assoc;
      reflexivity
    }
    // Case Add
    { assume g1 h2 g2 h4 contradiction; refine ⊥ₑ (∧ₑ₁ contradiction) }
  }
  {
    // Case Var i k
    assume i k gs IH;
    induction
    { assume c H; reflexivity }
    {
      assume j k2 Haliens;
      simplify insert;
      refine ind_Comp (λ u, (compN j i) = u ⇒ val (sum (case_Comp u (Var j (k2 + k) ⸬ gs) (Var j k2 ⸬ (Var i k ⸬ gs)) (Var i k ⸬ insert (Var j k2) gs)) ‚ l) = (val (Var j k2 ‚ l) + val (sum (Var i k ⸬ gs) ‚ l))) _ _ _ (compN j i) _
      {
        assume Hi_eq_j;
        simplify case_Comp;
        rewrite compN_correct j i Hi_eq_j;
        simplify; rewrite distr*+; rewrite +_assoc; reflexivity
      }
      {
        assume Hcomp;
        simplify case_Comp;
        reflexivity
      }
      {
        assume Hcomp;
        simplify case_Comp;
        simplify;
        type IH (Var j k2);
        have g: π (no_Add (Var j k2 ⸬ gs)) {
          simplify;
          apply ∧ᵢ
          { refine ∧ₑ₁ Haliens }
          { refine ∧ₑ₂ (∧ₑ₂ Haliens) }
        };
        rewrite IH (Var j k2) g;
        simplify;
        rewrite left +_assoc (nth l i * k) (nth l j * k2) (val (sum gs ‚ l));
        rewrite +_com (nth l i * k) (nth l j * k2);
        rewrite +_assoc;
        reflexivity
      }
      {reflexivity}
    }
    { assume g IH1 g' IH2 contradiction; refine ⊥ₑ (∧ₑ₁ contradiction) }
  }
  { assume g1  IH g2 IH2 gs H g contradiction; refine ⊥ₑ (∧ₑ₁ (∧ₑ₂ contradiction)); }
}
end;

// to be moved to List
symbol sort: τ(list g) → τ(list g);

rule sort □ ↪ □
with sort ($x ⸬ $l) ↪ insert $x (sort $l);

opaque symbol sort_correct l gs g : π (val (sum (sort (g ⸬ gs)) ‚ l) =  val (sum (g ⸬ gs)‚ l)) ≔
begin
admitted;

symbol norm x ≔ sum (remove0 (sort (aliens x)));

// to be moved to Nat
opaque symbol max_geq m n1 n2 :
  π (max n1 n2 Nat.≤ m ⇒ n1 Nat.≤ m ∧ n2 Nat.≤ m) ≔
begin
assume m n1 n2 h; apply ∧ᵢ
{ refine @leq_trans n1 (max n1 n2) m _ _ { apply leq_maxl n1 n2 } { refine h } }
{ refine @leq_trans n2 (max n1 n2) m _ _ { apply leq_maxr n1 n2 } { refine h } }
end;

opaque symbol norm_correct (x: G) l :
  π(varmax x Nat.≤ size l) → π(val(norm x ‚ l) = val(x ‚ l)) ≔
begin
admitted;

symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂));

symbol ≐_decides_neq [x y] : π (x ≐ y ≠ Eq ⇒ x ≠ y) ≔
begin
admitted;

// symbol l1 x y : π((x + y) - (x + y) ≠ 1) ≔
// begin
//   assume x y;
//   refine ≐_decides_neq _;
//   rewrite left .[z in z ≐ _] reify_correct;
//   set e ≔ reify ((x + y) - (x + y));
//   rewrite .[z in val z] eta_prod;
//   compute e;
//   rewrite left norm_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
// end;

symbol ≱ : τ int → τ int → Prop ≔ λ x y, ¬ (x ≥ y);
notation ≱ infix 10;

symbol ≐_decides_ngeq [x y] : π (x ≐ y ≠ Gt ∧ x ≐ y ≠ Eq ⇒ x ≱ y) ≔
begin
admitted;

private symbol x : τ int;
private symbol y : τ int;
private symbol test ≔ (x + y) - (x +  y);

compute let e ≔ (reify test) in val (norm (e ₁) ‚ (e ₂));
