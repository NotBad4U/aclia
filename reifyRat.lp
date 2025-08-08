require open aclia.Z;
require aclia.Nat as Nat;
open aclia.Nat;
require open aclia.Rat aclia.Prod aclia.Set aclia.List aclia.Eq aclia.Prop aclia.FOL aclia.Bool aclia.Comp;

// Move into HOL.lp ?
symbol ⇒d : Π (x: Prop), (π x → Prop) → Prop; notation ⇒d infix 10;
rule π ($x ⇒d $y) ↪ Π (z: π $x), π ($y z);

// type for rational arithmetic expressions
inductive G: TYPE ≔
| Cst: τ rat → G
| Var: ℕ → τ rat → G
| Add: G → G → G
; 

constant symbol grp : Set;
rule τ grp ↪ G;

// multiplication by a constant

symbol mul: τ rat → G → G;

rule mul $k (Cst $l) ↪ Cst ($k q* $l)
with mul $k (Var $i $l) ↪ Var $i ($k q* $l)
with mul $k (Add $x $y) ↪ Add (mul $k $x) (mul $k $y);

// opposite

symbol opp ≔ mul (q~ 1⫽1);

// highest variable index in a term

symbol varmax : G → ℕ;

rule varmax (Cst _) ↪ _0
with varmax (Var $k _) ↪ $k
with varmax (Add $x $y) ↪ max (varmax $x) (varmax $y);

/* evaluation of an arithmetic expression wrt a list of values for variables

variables with indexes not in the list are interpreted by 0 */


symbol ℕ2Rat (x: ℕ): τ rat;
rule ℕ2Rat _0 ↪ 0⫽1
with ℕ2Rat ($n +1) ↪ (ℕ2Rat $n) q+ 1⫽1;


symbol nth ≔ nth (ℕ2Rat _0);

symbol val: τ (grp × list rat) → τ rat;

// type nth;

rule val (Cst $k ‚ _) ↪ $k
with val (Var $i $k ‚ $l) ↪ (nth $l $i) q* $k
with val (Add $x $y ‚ $l) ↪ val ($x ‚ $l) q+ val ($y ‚ $l);

symbol va l x ≔ val (x ‚ l);

// // // some useful type (use inductive instead?)

constant symbol R : TYPE;
constant symbol Index : ℕ → R;
constant symbol New : ℕ → R;

symbol case [a] : R → (ℕ → τ a) → (ℕ → τ a) → τ a;

rule case (Index $i) $f _ ↪ $f $i
with case (New $i) _ $g ↪ $g $i;

// // /* index of a value in a list: returns New if the value is not
// // definitionally equivalent to some element of the list */

sequential symbol index: ℕ → Π [a], τ a → τ(list a) → R;

rule index $k _ □ ↪ New $k
with index $k $x ($x ⸬ _) ↪ Index $k
with index $k $x ($y ⸬ $l) ↪ index ($k +1) $x $l;

compute index _0 1 (1 ⸬ 4 ⸬ □);

// // /* reification: given a Lambdapi term x of type ℤ, compute an
// // expression in G and a list of values whose evaluation is equal to
// // x. WARNING: rfy is sequential. */

sequential symbol rfy: τ(list rat) → τ rat → τ(grp × list rat);

rule rfy $l ($x q+ $y) ↪
  let x ≔ rfy $l $x in
    let y ≔ rfy (x ₂) $y in
      Add (x ₁) (y ₁) ‚ (y ₂)
with rfy $l (q~ $x) ↪
  let x ≔ rfy $l $x in
  opp (x ₁) ‚ (x ₂)

with rfy $l ($x q- $y) ↪ rfy $l ($x q+ q~ $y)

with rfy $l (Rat 0 $d $inv) ↪ Cst (Rat 0 $d $inv) ‚ $l
with rfy $l (Rat (Zpos $n) (Zpos $d) $inv) ↪ Cst (Rat (Zpos $n) (Zpos $d) $inv) ‚ $l
with rfy $l (Rat (Zpos $n) (Zneg $d) $inv) ↪ Cst (Rat (Zpos $n) (Zneg $d) $inv) ‚ $l
with rfy $l (Rat (Zneg $z) (Zpos $d) $inv) ↪ Cst (Rat (Zneg $z) (Zpos $d) $inv) ‚ $l
with rfy $l (Rat (Zneg $z) (Zneg $d) $inv) ↪ Cst (Rat (Zneg $z) (Zneg $d) $inv) ‚ $l
with rfy $l (fracq 0 $d) ↪ Cst (fracq 0 $d) ‚ $l
with rfy $l (fracq (Zpos $n) (Zpos $d)) ↪ Cst (fracq (Zpos $n) (Zpos $d)) ‚ $l
with rfy $l (fracq (Zpos $n) (Zneg $d)) ↪ Cst (fracq (Zpos $n) (Zneg $d)) ‚ $l
with rfy $l (fracq (Zneg $z) (Zpos $d)) ↪ Cst (fracq (Zneg $z) (Zpos $d)) ‚ $l
with rfy $l (fracq (Zneg $z) (Zneg $d)) ↪ Cst (fracq (Zneg $z) (Zneg $d)) ‚ $l
with rfy $l (0⫽1 q* _) ↪ Cst 0⫽1 ‚ $l
// with rfy $l (Zpos $k * $x) ↪
//   let x ≔ rfy $l $x in
//   mul (Zpos $k) (x ₁) ‚ x ₂
// with rfy $l (Zneg $k * $x) ↪
//   let x ≔ rfy $l $x in
//   mul (Zneg $k) (x ₁) ‚ x ₂
// with rfy $l ($x * Zpos $k) ↪
//   let x ≔ rfy $l $x in
//   mul (Zpos $k) (x ₁) ‚ x ₂
// with rfy $l ($x * Zneg $k) ↪
//   let x ≔ rfy $l $x in
//   mul (Zneg $k) (x ₁) ‚ x ₂
with rfy $l $x ↪
  case (index _0 $x $l) (λ i, Var i (1⫽1) ‚ $l) (λ i, Var i (1⫽1) ‚ ($l ++ ($x ⸬ □)))
;

symbol reify ≔ rfy □;

compute reify (fracq 120 4);

opaque symbol reify_correct (x: TRat) : π(val(reify x) = x) ≔
begin
    assume x;
    simplify;
    change π ((x q* 1⫽1) = x);
    apply q*_neutral_r
end;

opaque nth;

// // aliens (constants and variables) of an arithmetic expression

symbol aliens: G → τ(list grp);

rule aliens (Cst $k) ↪ Cst $k ⸬ □
with aliens (Var $i $k) ↪ Var $i $k ⸬ □
with aliens (Add $x $y) ↪ aliens $x ++ aliens $y;

symbol isNotAdd: τ grp → Prop; //FIXME: replace Prop by 𝔹

rule isNotAdd (Cst _) ↪ ⊤
with isNotAdd (Var _ _ ) ↪ ⊤
with isNotAdd (Add _ _ ) ↪ ⊥;

symbol no_Add : τ(list grp) → Prop;

rule no_Add □ ↪ ⊤
with no_Add ($g ⸬ $gs) ↪  isNotAdd $g ∧ no_Add $gs;

opaque symbol no_Add_++ ys xs : π(no_Add xs ⇒ no_Add ys ⇒ no_Add(xs ++ ys)) ≔
begin
assume ys; induction
{assume h1 h2; refine h2}
{assume x xs IH h1 h2; simplify; apply ∧ᵢ {refine ∧ₑ₁ h1} {apply IH {refine ∧ₑ₂ h1} {refine h2}}}
end;

opaque symbol no_Add_aliens x : π(no_Add (aliens x)) ≔
begin
induction
{assume k; simplify; apply ∧ᵢ ⊤ᵢ ⊤ᵢ}
{assume i ki; simplify; apply ∧ᵢ ⊤ᵢ ⊤ᵢ}
{assume x hx y hy; simplify; apply no_Add_++ (aliens y) (aliens x) hx hy; }
end;

// ordering of natural numbers
// move to Nat
symbol compN : ℕ → ℕ → Comp;

rule compN _0 _0 ↪ Eq
with compN _0 (_ +1) ↪ Lt
with compN (_ +1) _0 ↪ Gt
with compN ($x +1) ($y +1) ↪ compN $x $y;

opaque symbol compN_correct x y : π (compN x y = Eq ⇒ x = y) ≔
begin
induction
{ induction
  {assume h; reflexivity}
  {assume y hy h; apply ⊥ₑ; apply Lt≠Eq h}
}
{ assume x hx; induction
  {assume h; apply ⊥ₑ; apply Gt≠Eq h}
  {assume y hy h; apply feq (+1); apply hx y h }
}
end;

// // normalization of arithmetic expressions

// /*
//symbol merge : τ(list grp) → τ(list grp);

// rule merge □ ↪ □
// with merge ($x ⸬ □) ↪ $x ⸬ □
// with merge (Cst $k ⸬ Cst $k' ⸬ $l) ↪ merge (Cst ($k + $k') ⸬ $l)
// with merge (Cst $k ⸬ Var $i $ki ⸬ $l) ↪ Cst $k ⸬ merge (Var $i $ki ⸬ $l)
// with merge (Var $i $ki ⸬ Var $j $kj ⸬ $l) ↪
//   case_Comp (compN $i $j)
//             (merge (Var $i ($ki + $kj) ⸬ $l))
//             (Var $i $ki ⸬ merge (Var $j $kj ⸬ $l))
//             (Var $i $ki ⸬ merge (Var $j $kj ⸬ $l))
// ;
// */

symbol remove0 : τ(list grp) → τ(list grp);

rule remove0 □ ↪ □
with remove0 (Cst (Rat 0 _ _) ⸬ $l) ↪ remove0 $l
with remove0 (Cst (Rat (Zpos $k) $p $inv)  ⸬ $l) ↪ Cst (Rat (Zpos $k) $p $inv) ⸬ remove0 $l
with remove0 (Cst (Rat (Zneg $k) $p $inv) ⸬ $l) ↪ Cst (Rat (Zneg $k) $p $inv) ⸬ remove0 $l
with remove0 (Var _ (Rat 0 _ _) ⸬ $l) ↪ remove0 $l
with remove0 (Var $i (Rat (Zpos $n) $p $inv) ⸬ $l) ↪ Var $i (Rat (Zpos $n) $p $inv) ⸬ remove0 $l
with remove0 (Var $i (Rat (Zneg $z) $p $inv) ⸬ $l) ↪ Var $i (Rat (Zneg $z) $p $inv) ⸬ remove0 $l
;

symbol sum: τ(list grp) → τ grp;

rule sum □ ↪ Cst 0⫽1
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
        induction;
        change π  (`∀ x0: τ int, `∀ x2: τ int, (istrue (isLt (0 ≐ x2) and isEq (Z_gcd (abs x0) (abs x2) ≐ _1))) ⇒d λ x3, (`∀ x4, (no_Add x4 ⇒d (λ _, val (sum (remove0 x4) ‚ l) = val (sum x4 ‚ l))) ⇒d (λ _, no_Add (Cst (Rat x0 x2 x3) ⸬ x4) ⇒d (λ _, val (sum (remove0 (Cst (Rat x0 x2 x3) ⸬ x4)) ‚ l) = val (sum (Cst (Rat x0 x2 x3) ⸬ x4) ‚ l)))));
        assume n;
        generalize n;
        induction 
          // Case Z0
          { assume p inv gs IH H; simplify;  rewrite left valqK (Rat 0 p inv); simplify; rewrite frac_0_num; rewrite q+_neutral_l; apply IH;  refine (∧ₑ₂ H) }
          // Case Zpos
          { assume p inv c gs IH H; simplify; rewrite (IH (∧ₑ₂ H)); reflexivity }
          // Case Zneg
          { assume p inv c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity }
    }
    {
      // Case Var i k
      assume i;
      induction;
      induction // on k
      {assume p inv gs IH H; simplify; rewrite left valqK (Rat 0 p inv); simplify; rewrite frac_0_num; rewrite q*_cancel_r; rewrite q+_neutral_l; apply IH; refine (∧ₑ₂ H)} // Case Z0
      { assume p inv c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity } // Case Zpos
      { assume p inv c gs IH H; simplify;  rewrite (IH (∧ₑ₂ H)); reflexivity } // Case Zneg
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

opaque symbol case_Comp_prop [a] (p:τ a → Prop) eq lt gt c :
  π(p eq ⇒ p lt ⇒ p gt ⇒ p (case_Comp c eq lt gt)) ≔
begin
assume a p eq lt gt; induction
{assume peq plt pgt; refine peq}
{assume peq plt pgt; refine plt}
{assume peq plt pgt; refine pgt}
end;

symbol insert: G → τ(list grp) → τ(list grp);

// /*
// rule insert (Cst $k) (Cst $k' ⸬ $l) ↪ Cst $k ⸬ Cst $k' ⸬ $l
// with insert (Cst $k) (Var $i $k' ⸬ $l) ↪ Cst $k ⸬ Var $i $k' ⸬ $l
// with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
// with insert (Var $i $ki) (Var $j $kj ⸬ $l) ↪
//      case_Comp (compN $i $j)
//             (Var $i $ki ⸬ Var $j $kj ⸬ $l)
//             (Var $i $ki ⸬ Var $j $kj ⸬ $l)
//             (Var $j $kj ⸬ insert (Var $i $ki) $l);
// */

rule insert $x □ ↪ $x ⸬ □
with insert (Cst $k) (Cst $k' ⸬ $l) ↪ Cst ($k q+ $k') ⸬ $l
with insert (Cst $k) (Var $i $k' ⸬ $l) ↪ Cst $k ⸬ Var $i $k' ⸬ $l
with insert (Var $i $k) (Cst $k' ⸬ $l) ↪ Cst $k' ⸬ insert (Var $i $k) $l
with insert (Var $i $ki) (Var $j $kj ⸬ $l) ↪
     case_Comp (compN $i $j)
            (Var $i ($ki q+ $kj) ⸬ $l) // Eq
            (Var $i $ki ⸬ Var $j $kj ⸬ $l) // Lt
            (Var $j $kj ⸬ insert (Var $i $ki) $l); // i > j

opaque symbol no_Add_insert xs y : π(isNotAdd y) → π(no_Add xs) → π(no_Add(insert y xs)) ≔
begin
induction
{ assume x h i; simplify; apply ∧ᵢ { refine h } { apply ⊤ᵢ } }
{ induction
  { assume k xs IH; induction
    { assume k' h1 h2; simplify; apply ∧ᵢ {apply ⊤ᵢ} {apply ∧ₑ₂ h2} }
    { assume ki i h1 h2; simplify; apply ∧ᵢ {apply ⊤ᵢ}
      {apply IH (Var ki i) {apply ⊤ᵢ} {apply ∧ₑ₂ h2}} }
    { assume x1 H1 x2 H2 h1 h2; apply ⊥ₑ; refine h1}
  }
  { assume j kj xs IH; induction
    { assume k h1 h2; simplify; apply ∧ᵢ {apply ⊤ᵢ} {apply ∧ᵢ {apply ⊤ᵢ} {apply ∧ₑ₂ h2}}}
    { assume i ki h1 h2; simplify;
      apply case_Comp_prop no_Add (Var i (ki q+ kj) ⸬ xs) (Var i ki ⸬ (Var j kj ⸬ xs)) (Var j kj ⸬ insert (Var i ki) xs) (compN i j)
         {refine h2}
         {simplify; apply ∧ᵢ {refine ⊤ᵢ}{refine h2}}
         {simplify; apply ∧ᵢ{apply ⊤ᵢ}{apply IH (Var i ki) {apply ⊤ᵢ} {apply ∧ₑ₂ h2}}}
    }
    { assume x1 H1 x2 H2 h1 h2; apply ⊥ₑ; refine h1}
  }
  { assume x1 H1 x2 H2 xs IH y h i; apply ⊥ₑ; refine ∧ₑ₁ i}
}
end;

// // // to be moved to Nat
// // opaque symbol distr*+ x y z : π(x * (y + z) = x * y + x * z) ≔
// // begin
// // admitted;

symbol insert_correct l gs g : π (no_Add (g ⸬ gs)) → π (val (sum (insert g gs) ‚ l) =  val (g ‚ l) q+  val (sum gs ‚ l)) ≔
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
    { assume k2 H; simplify; rewrite q+_assoc; reflexivity }
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
      rewrite left q+_assoc k (val (Var i c ‚ l)) (val (sum gs ‚ l));
      rewrite q+_com k;
      rewrite q+_assoc;
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
      refine ind_Comp (λ u, (compN j i) = u ⇒ val (sum (case_Comp u (Var j (k2 q+ k) ⸬ gs) (Var j k2 ⸬ (Var i k ⸬ gs)) (Var i k ⸬ insert (Var j k2) gs)) ‚ l) = (val (Var j k2 ‚ l) q+ val (sum (Var i k ⸬ gs) ‚ l))) _ _ _ (compN j i) _
      {
        assume Hi_eq_j;
        simplify case_Comp;
        rewrite compN_correct j i Hi_eq_j;
        simplify; rewrite distrq*q+; rewrite q+_assoc; reflexivity
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
        rewrite left q+_assoc (nth l i q* k) (nth l j q* k2) (val (sum gs ‚ l));
        rewrite q+_com (nth l i q* k) (nth l j q* k2);
        rewrite q+_assoc;
        reflexivity
      }
      {reflexivity}
    }
    { assume g IH1 g' IH2 contradiction; refine ⊥ₑ (∧ₑ₁ contradiction) }
  }
  { assume g1  IH g2 IH2 gs H g contradiction; refine ⊥ₑ (∧ₑ₁ (∧ₑ₂ contradiction)); }
}
end;

// // // to be moved to List
symbol sort: τ(list grp) → τ(list grp);
rule sort □ ↪ □
with sort ($x ⸬ $xs) ↪ insert $x (sort $xs);

opaque symbol no_Add_sort xs : π(no_Add xs) → π(no_Add (sort xs)) ≔
begin
induction
{ assume h; apply ⊤ᵢ }
{ assume x xs IH h; simplify; apply no_Add_insert (sort xs) x
  {refine ∧ₑ₁ h}
  {apply IH; refine ∧ₑ₂ h}
}
end;

opaque symbol sort_correct l gs : π(no_Add gs) → π (val (sum (sort gs) ‚ l) =  val (sum gs ‚ l)) ≔
begin
assume l;
induction
{ assume h; reflexivity }
{ assume g gs IH h;
  have e: π(val (sum (sort gs) ‚ l) = val (sum gs ‚ l))
    { apply IH; apply ∧ₑ₂ h };
  simplify; rewrite left e; apply insert_correct l (sort gs) g;
  simplify; apply ∧ᵢ { apply ∧ₑ₁ h } { apply no_Add_sort gs; apply ∧ₑ₂ h }
}
end;

symbol norm x ≔ sum (remove0 (sort (aliens x)));

// to be moved to Nat
opaque symbol max_leq m n1 n2 :
  π (max n1 n2 aclia.Nat.≤ m ⇒ n1 aclia.Nat.≤ m ∧ n2 aclia.Nat.≤ m) ≔
begin
assume m n1 n2 h; apply ∧ᵢ
{ refine @leq_trans n1 (max n1 n2) m _ _ { apply leq_maxl n1 n2 } { refine h } }
{ refine @leq_trans n2 (max n1 n2) m _ _ { apply leq_maxr n1 n2 } { refine h } }
end;

// moved to Eq
opaque symbol eq_trans [a] (x y z:τ a) : π(x = y ⇒ y = z ⇒ x = z) ≔
begin
assume a x y z xy yz; rewrite xy; refine yz
end;

opaque symbol sum++ l ys xs : π(val(sum(xs ++ ys) ‚ l) = val(sum xs ‚ l) q+ val(sum ys ‚ l)) ≔
begin
assume l ys; induction
{ simplify; change π (val (sum ys ‚ l) = (0⫽1 q+ val (sum ys ‚ l))); rewrite q+_neutral_l; reflexivity }
{ assume x xs IH; simplify; rewrite IH; rewrite q+_assoc; reflexivity }
end;

opaque symbol aliens_correct l x : π (val (sum (aliens x) ‚ l) = val (x ‚ l)) ≔
begin
assume l; induction
{assume k; simplify; change  π ((k q+ 0⫽1) = k); rewrite q+_neutral_r; reflexivity }
{assume i ki; simplify; change π (((nth l i q* ki) q+ 0⫽1) = (nth l i q* ki)); rewrite q+_neutral_r; reflexivity}
{assume x hx y hy; simplify; rewrite sum++; rewrite hx; rewrite hy; reflexivity}
end;

opaque symbol norm_correct (x: G) l :
  π(varmax x aclia.Nat.≤ size l) → π(val(norm x ‚ l) = val(x ‚ l)) ≔
begin
assume x l h; simplify; apply eq_trans (val (sum (remove0 (sort (aliens x))) ‚ l)) (val (sum (sort (aliens x)) ‚ l)) (val (x ‚ l))
{ apply remove0_correct l (sort(aliens x));
  apply no_Add_sort (aliens x); apply no_Add_aliens x }
{ apply eq_trans (val (sum (sort (aliens x)) ‚ l)) (val (sum (aliens x) ‚ l)) (val (x ‚ l))
  { apply sort_correct l (aliens x); apply no_Add_aliens x }
  { apply aliens_correct l x}
}
end;

// move to Prod ?
symbol eta_prod [a b] (x:τ(a × b)): π(x = (x ₁) ‚ (x ₂));

// to be moved to Comp
opaque symbol ≐_decides_neq [x y: τ rat] : π ((x q≐ y) ≠ Eq ⇒ x ≠ y) ≔
begin
admitted;

symbol l1 x y : π((x q+ y) q- (x q+ y) ≠ 1⫽1) ≔
begin
  assume x y;
  refine ≐_decides_neq _;
  rewrite left .[z in z q≐ _] reify_correct;
  set e ≔ reify ((x q+ y) q- (x q+ y));
  rewrite .[z in val z] eta_prod;
  compute e;
  rewrite left norm_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
end;
