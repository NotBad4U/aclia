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