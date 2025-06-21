require aclia.Nat as Nat;
open aclia.Nat;
require open aclia.Pos aclia.Prod aclia.Set aclia.List aclia.Eq aclia.Prop aclia.FOL aclia.Bool aclia.Comp aclia.Z;
require open aclia.reify;

symbol compG : G → G → Comp;
rule compG (Var $i $k) (Var $j $k2) ↪ compN $i $j
with compG (Var _ _) (Cst _) ↪ Gt
with compG (Cst _) (Var _ _)  ↪ Lt
with compG (Cst $c1) (Cst $c2)  ↪ $c1 ≐ $c2;

symbol split [a: Set] (l : τ (list a)): τ(list a × list a);
rule split □ ↪ (□ ‚ □)
with split ($x ⸬ □) ↪ (($x ⸬ □) ‚ □)
with split ($x ⸬ $y ⸬ $l) ↪  
    let res ≔  (split $l) in
        ($x ⸬ (res ₁)) ‚ ($y ⸬ (res ₂));

// opaque symbol split_correct l: π (val ( split  ) = val (sum gs ‚ l)) ≔
// begin
  
// end;

symbol merge  (l1 l2 : τ (list g)): τ (list g);
rule merge □ □ ↪ □
with merge □ $l2 ↪ $l2
with merge $l1 □ ↪ $l1
with merge (Cst $c1 ⸬ $l1') (Cst $c2 ⸬ $l2') ↪ (Cst ($c1 + $c2) ⸬ merge $l1' $l2')
with merge (Cst $c ⸬ $l1') (Var $i $k ⸬ $l2') ↪ (Cst $c ⸬ merge $l1' (Var $i $k ⸬ $l2'))
with merge (Var $i $k ⸬ $l1') (Cst $c ⸬ $l2') ↪ (Cst $c ⸬ merge (Var $i $k ⸬ $l1') $l2')
with merge ((Var $i $k1) ⸬ $l1') ((Var $j $k2) ⸬ $l2') ↪
    case_Comp (compN $i $j)
        (Var $i ($k1 + $k2) ⸬ merge $l1' $l2')
        ((Var $i $k1) ⸬ merge $l1' (Var $j $k2 ⸬ $l2'))
        ((Var $j $k2) ⸬ merge (Var $i $k1 ⸬ $l1') $l2')
;

opaque symbol merge_correct l g1 g2 : π (no_Add g1) →  π (no_Add g2) →  π (val ( sum (merge  g1 g2) ‚ l ) = val (sum g1 ‚ l) + val (sum g2 ‚ l)) ≔
begin
  assume l;
  induction
  { simplify; reflexivity }
  {
    induction
    {
      assume k g1' IH;
      induction
      {
        assume h_nodaddg1 h_nodaddg2;
        reflexivity;
      }
      {
        induction
        {
          assume k2 g2' IH2 h2 h3;
          simplify;
          rewrite left +_assoc;
          rewrite .[in x in _ = (x + _) ] +_assoc;
          rewrite .[in x in _ = ((_ + x) + _) ] +_com;
          rewrite left .[in x in _ = (x + _) ] +_assoc;
          rewrite IH (g2') _ _ { refine ∧ₑ₂ h2 } { refine ∧ₑ₂ h3 } { rewrite .[in x in _ = x] +_assoc; reflexivity };
        }
        {
          assume i c g2' IH2 hnoadd1 hnoadd2;
          simplify; rewrite IH (Var i c ⸬ g2') _ _ { refine ∧ₑ₂ hnoadd1 } { refine hnoadd2 } { simplify; rewrite +_assoc; reflexivity };
        }
        {
          simplify; assume g1 ih1 g2 ih2 g2' h5 h6 contradiction;
          refine ⊥ₑ (∧ₑ₁ contradiction);
        }
      }
    }
    {
      assume i k1 g1' ih1;
      induction
      { reflexivity; }
      {
        induction
        {
          assume c g2' ih2 hnoadd hnoadd2; simplify;
          rewrite ih2 hnoadd (∧ₑ₂ hnoadd2);
          rewrite left .[in x in _ = x ] +_assoc;
          simplify;
          rewrite .[in x in _ = x + _ ] +_com;
          rewrite  .[in x in _ = x ] +_assoc;
          reflexivity
        }
        {
          assume j k2 g2' ih2 hnoadd1 hnoadd2;
          simplify;
          refine ind_Comp (λ u, (compN i j) = u ⇒ val (sum (case_Comp u (Var i (k1 + k2) ⸬ merge g1' g2') (Var i k1 ⸬ merge g1' (Var j k2 ⸬ g2')) (Var j k2 ⸬ merge (Var i k1 ⸬ g1') g2')) ‚ l) = (((nth l i * k1) + val (sum g1' ‚ l)) + ((nth l j * k2) + val (sum g2' ‚ l)))) _ _ _ (compN i j) _
          {
            simplify; assume hieqj;
            rewrite compN_correct i j hieqj;
            simplify; rewrite distr*+; rewrite ih1 g2'  (∧ₑ₂ hnoadd1) (∧ₑ₂ hnoadd2);
            rewrite left .[in x in _ = x ] +_assoc;
            rewrite  .[in x in _ = (x + _) ] +_com;
            rewrite left .[in x in _ = (x + _) ] +_assoc;
            rewrite  +_com (nth l j * k2) (nth l j * k1);
            rewrite .[in x in _ = x ] +_assoc; reflexivity
          }
          {
            simplify; assume hieqj;
            simplify; rewrite ih1 (Var j k2 ⸬ g2')  (∧ₑ₂ hnoadd1) hnoadd2;
            simplify; rewrite  +_assoc; reflexivity
          }
          {
            assume hGt;
            simplify;  
            rewrite ih2 hnoadd1 (∧ₑ₂ hnoadd2);
            simplify;
            rewrite left .[ in x in _ = x] +_assoc;
            rewrite .[ in x in _ = (x + _)] +_com;
            rewrite .[ in x in _ = x] +_assoc; reflexivity
          }
          { reflexivity }
        }
        {
          simplify;
          assume x1 ih x2 ih2 g2 h1 hnoadd1 hnoadd2;
          refine ⊥ₑ (∧ₑ₁ hnoadd2 )
        }
      }
    }
    {
      assume g1 ih g2 ih2 g1' h g2' hnoadd1 hnoadd2;
      refine ⊥ₑ (∧ₑ₁ hnoadd1)
    }
  }
end;


symbol mergesort:  τ (list g) →  τ (list g);
rule mergesort □ ↪ □
with mergesort ($x ⸬ □) ↪ ($x ⸬ □)
with mergesort ($x ⸬ $y ⸬ $l) ↪ 
    let s ≔ split ($x ⸬ $y ⸬ $l) in
    let l1 ≔ s ₁ in
    let l2 ≔ s ₂ in
        merge (mergesort l1) (mergesort l2);

compute mergesort ((Var Nat._3 2) ⸬ (Var Nat._2 2) ⸬ (Var Nat._1 2) ⸬ Cst 10 ⸬ □);

symbol norm_speed x ≔ sum (remove0 (mergesort (aliens x)));

opaque symbol norm_speed_correct (x: G) l :
  π(varmax x Nat.≤ size l) → π(val(norm_speed x ‚ l) = val(x ‚ l)) ≔
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
  rewrite left norm_speed_correct (e ₁) (e ₂) _ { refine ⊤ᵢ } { refine Lt≠Eq }
end;