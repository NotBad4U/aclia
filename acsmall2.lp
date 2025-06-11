require open aclia.Prop;
require open aclia.Set;
require open aclia.Eq;
require open aclia.Nat;
require open aclia.Pos;
require open aclia.Z;
require open aclia.List;
require open aclia.lia;
require open aclia.reify2;
require open aclia.Prod;

symbol p_0_0 : τ (int);

symbol p_0_1 : τ (int);

symbol p_0_2 : τ (int);

symbol p_0_3 : τ (int);

symbol p_0_4 : τ (int);

symbol p_1_0 : τ (int);

symbol p_1_1 : τ (int);

symbol p_1_2 : τ (int);

symbol p_1_3 : τ (int);

symbol p_1_4 : τ (int);

symbol p_2_0 : τ (int);

symbol p_2_1 : τ (int);

symbol p_2_2 : τ (int);

symbol p_2_3 : τ (int);

symbol p_2_4 : τ (int);

symbol p_3_0 : τ (int);

symbol p_3_1 : τ (int);

symbol p_3_2 : τ (int);

symbol p_3_3 : τ (int);

symbol p_3_4 : τ (int);

symbol p_4_0 : τ (int);

symbol p_4_1 : τ (int);

symbol p_4_2 : τ (int);

symbol p_4_3 : τ (int);

symbol p_4_4 : τ (int);

symbol p_5_0 : τ (int);

symbol p_5_1 : τ (int);

symbol p_5_2 : τ (int);

symbol p_5_3 : τ (int);

symbol p_5_4 : τ (int);

symbol p_3 ≔ (p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4);

symbol p_6 ≔ (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1);

symbol p_9 ≔ (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4));

symbol p_10 ≔ (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4);

symbol p_11 ≔ (— 1 * 1);

symbol p_14 ≔ (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4));

symbol p_15 ≔ (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4);

symbol p_18 ≔ (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4));

symbol p_19 ≔ (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4);

symbol p_22 ≔ (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4));

symbol p_23 ≔ (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4);

symbol p_26 ≔ (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4));

symbol p_27 ≔ (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4);

symbol p_30 ≔ (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4));

symbol p_31 ≔ (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4);

symbol p_34 ≔ (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0);

symbol p_37 ≔ (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2);

symbol p_40 ≔ (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3);

symbol H0l' ≔ (1 * ((— (p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4)) - (— 1)));
symbol H0r' ≔ (1 * 0);
symbol H1l' ≔ (1 * ((— (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1)) - (— 1)));
symbol H1r' ≔ (1 * 0);
symbol H2l' ≔ (1 * ((— (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4))) - (— (— 1 * 1))));
symbol H2r' ≔ (1 * 0);
symbol H3l' ≔ (1 * ((— (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4))) - (— (— 1 * 1))));
symbol H3r' ≔ (1 * 0);
symbol H4l' ≔ (1 * ((— (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4))) - (— (— 1 * 1))));
symbol H4r' ≔ (1 * 0);
symbol H5l' ≔ (1 * ((— (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4))) - (— (— 1 * 1))));
symbol H5r' ≔ (1 * 0);
symbol H6l' ≔ (1 * ((— (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4))) - (— (— 1 * 1))));
symbol H6r' ≔ (1 * 0);
symbol H7l' ≔ (1 * ((— (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4))) - (— (— 1 * 1))));
symbol H7r' ≔ (1 * 0);
symbol H8l' ≔ (1 * ((— (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0)) - (— 1)));
symbol H8r' ≔ (1 * 0);
symbol H9l' ≔ (1 * ((— (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2)) - (— 1)));
symbol H9r' ≔ (1 * 0);
symbol H10l' ≔ (1 * ((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (— 2)));
symbol H10r' ≔ (1 * (0 + 1));
symbol H11l' ≔ (1 * (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (1 + 1 + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + 1 + 1 + 2)));
symbol H11r' ≔ (1 * 0);

//symbol a ≔ H0l' + H1l' + H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l';

require open aclia.Classic;
require open aclia.Alethe;

symbol reify_correct x: πᶜ(val(reify x) = x);
symbol norm_correct (x: G) l : πᶜ(val(norm x ‚ l) = val(x ‚ l));
symbol eta_prod [a b] (x:τ(a × b)): πᶜ(x = (x ₁) ‚ (x ₂));

opaque symbol Hla : πᶜ ((¬ (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) ≤ 1))) ∨ᶜ (¬ (((p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) ≤ 1))) ∨ᶜ (¬ (((— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) ≤ (— 1 * 1)))) ∨ᶜ (¬ (((— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) ≤ (— 1 * 1)))) ∨ᶜ (¬ (((— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) ≤ (— 1 * 1)))) ∨ᶜ (¬ (((— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) ≤ (— 1 * 1)))) ∨ᶜ (¬ (((— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) ≤ (— 1 * 1)))) ∨ᶜ (¬ (((— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) ≤ (— 1 * 1)))) ∨ᶜ (¬ (((p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) ≤ 1))) ∨ᶜ (¬ (((p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) ≤ 1))) ∨ᶜ (¬ (((p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3) < 2))) ∨ᶜ (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) < (1 + 1 + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + 1 + 1 + 2)))
    ≔
    begin
    rewrite .[x in _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ _ ∨ᶜ x] Zlt_not_ge;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_le_eq;
    try rewrite Zinv_lt_eq;
    rewrite Z_diff_geq_Z0_eq ((— (p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4))) ((— 1));
    rewrite Z_diff_geq_Z0_eq ((— (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1))) ((— 1));
    rewrite Z_diff_geq_Z0_eq ((— (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)))) ((— (— 1 * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)))) ((— (— 1 * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)))) ((— (— 1 * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)))) ((— (— 1 * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)))) ((— (— 1 * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)))) ((— (— 1 * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0))) ((— 1));
    rewrite Z_diff_geq_Z0_eq ((— (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2))) ((— 1));
    rewrite Z_diff_gt_Z0_eq ((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3))) ((— 2));
    rewrite Z_diff_geq_Z0_eq (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3))) ((1 + 1 + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + 1 + 1 + 2));
    rewrite Zgt_le_succ_r_eq (((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (— 2))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4))) - (— (— 1 * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4))) - (— (— 1 * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4))) - (— (— 1 * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4))) - (— (— 1 * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4))) - (— (— 1 * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4))) - (— (— 1 * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (— 2))) ((0 + 1));
    rewrite Zmult_ge_compat_eq (1) ((((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + (— 1 * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + (— 1 * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + (— 1 * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + (— 1 * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + (— 1 * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + (— 1 * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (1 + 1 + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + (— 1 * 1) + 1 + 1 + 2))) (0);
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H0;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H1;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H2;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H3;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H4;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H5;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H6;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H7;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H8;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H9;
    rewrite imp_eq_or;
    apply ⇒ᶜᵢ;
    assume H10;
    apply ¬ᶜᵢ;
    assume H11;
    have contra : πᶜ ((val (reify (H0l' + H1l' + H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l'))) ≥ (val (reify (H0r' + H1r' + H2r' + H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r')))) {
        rewrite reify_correct;
        rewrite reify_correct;
        apply (Zsum_geq_s H0l' H0r' (H1l' + H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H1r' + H2r' + H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H0 (Zsum_geq_s H1l' H1r' (H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H2r' + H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H1 (Zsum_geq_s H2l' H2r' (H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H2 (Zsum_geq_s H3l' H3r' (H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H3 (Zsum_geq_s H4l' H4r' (H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H4 (Zsum_geq_s H5l' H5r' (H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H5 (Zsum_geq_s H6l' H6r' (H7l' + H8l' + H9l' + H10l' + H11l') (H7r' + H8r' + H9r' + H10r' + H11r') H6 (Zsum_geq_s H7l' H7r' (H8l' + H9l' + H10l' + H11l') (H8r' + H9r' + H10r' + H11r') H7 (Zsum_geq_s H8l' H8r' (H9l' + H10l' + H11l') (H9r' + H10r' + H11r') H8 (Zsum_geq_s H9l' H9r' (H10l' + H11l') (H10r' + H11r') H9 (Zsum_geq_s H10l' H10r' H11l' H11r' H10 H11)))))))))));
    };
    apply (⇒ᶜₑ' contra);
    set a ≔ H0l' + (H1l' + (H2l' + (H3l' + (H4l' + (H5l' + (H6l' + (H7l' + (H8l' + (H9l' + (H10l' + H11l'))))))))));
    set b ≔ H0r' + (H1r' + (H2r' + (H3r' + (H4r' + (H5r' + (H6r' + (H7r' + (H8r' + (H9r' + (H10r' + H11r'))))))))));
    print;
    rewrite eta_prod (reify a);
    rewrite eta_prod (reify b);
    rewrite left norm_correct (reify a ₁) (reify a ₂);
    rewrite left norm_correct (reify b ₁) (reify b ₂);
    print;
    simplify;
    print;
    apply trivial;
end;
