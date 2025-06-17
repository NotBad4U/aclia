require open aclia.Prop;

require open aclia.Set;

require open aclia.Prod;

require open aclia.Eq;

require open aclia.Z;

require open aclia.FOL;

require open aclia.HOL;

require open aclia.Impred;

require open aclia.Classic;

require open aclia.PropExt;

require open aclia.Alethe;

require open aclia.reify;

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

symbol p_9 ≔ ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4));

symbol p_10 ≔ (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4);

symbol p_11 ≔ ((— 1) * 1);

symbol p_14 ≔ ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4));

symbol p_15 ≔ (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4);

symbol p_18 ≔ ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4));

symbol p_19 ≔ (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4);

symbol p_22 ≔ ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4));

symbol p_23 ≔ (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4);

symbol p_26 ≔ ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4));

symbol p_27 ≔ (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4);

symbol p_30 ≔ ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4));

symbol p_31 ≔ (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4);

symbol p_34 ≔ (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0);

symbol p_37 ≔ (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2);

symbol p_40 ≔ (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3);

opaque symbol t1 : π̇ ((¬ ((p_3 ≤ 1)))
     ⟇ (¬ ((p_6 ≤ 1)))
     ⟇ (¬ ((p_9 ≤ p_11)))
     ⟇ (¬ ((p_14 ≤ p_11)))
     ⟇ (¬ ((p_18 ≤ p_11)))
     ⟇ (¬ ((p_22 ≤ p_11)))
     ⟇ (¬ ((p_26 ≤ p_11)))
     ⟇ (¬ ((p_30 ≤ p_11)))
     ⟇ (¬ ((p_34 ≤ 1)))
     ⟇ (¬ ((p_37 ≤ 1)))
     ⟇ (¬ ((p_40 < 2)))
     ⟇ ((p_3 + p_6 + p_9 + p_14 + p_18 + p_22 + p_26 + p_30 + p_34 + p_37 + p_40) < (1 + 1 + p_11 + p_11 + p_11 + p_11 + p_11 + p_11 + 1 + 1 + 2))
    ⟇ ▩) ≔ 
begin
have Hla : π̇ (((¬ (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) ≤ 1))) ∨ (¬ (((p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) ≤ 1))) ∨ (¬ ((((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) ≤ ((— 1) * 1)))) ∨ (¬ ((((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) ≤ ((— 1) * 1)))) ∨ (¬ (((p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) ≤ 1))) ∨ (¬ (((p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) ≤ 1))) ∨ (¬ (((p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3) < 2))) ∨ (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) < (1 + 1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 1 + 1 + 2)))
        ⟇ ▩) {
    apply ∨ᵢ₁;
    rewrite .[x in _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ x] Zlt_not_ge;
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
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)))) ((— ((— 1) * 1)));
    rewrite Z_diff_geq_Z0_eq ((— (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0))) ((— 1));
    rewrite Z_diff_geq_Z0_eq ((— (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2))) ((— 1));
    rewrite Z_diff_gt_Z0_eq ((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3))) ((— 2));
    rewrite Z_diff_geq_Z0_eq (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3))) ((1 + 1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 1 + 1 + 2));
    rewrite Zgt_le_succ_r_eq (((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (— 2))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4))) - (— ((— 1) * 1)))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2)) - (— 1))) (0);
    rewrite Zmult_ge_compat_eq (1) (((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (— 2))) ((0 + 1));
    rewrite Zmult_ge_compat_eq (1) ((((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (1 + 1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 1 + 1 + 2))) (0);
    try rewrite Z_eq_antisym;
    rewrite imp_eq_or;
    assume H0;
    rewrite imp_eq_or;
    assume H1;
    rewrite imp_eq_or;
    assume H2;
    rewrite imp_eq_or;
    assume H3;
    rewrite imp_eq_or;
    assume H4;
    rewrite imp_eq_or;
    assume H5;
    rewrite imp_eq_or;
    assume H6;
    rewrite imp_eq_or;
    assume H7;
    rewrite imp_eq_or;
    assume H8;
    rewrite imp_eq_or;
    assume H9;
    rewrite imp_eq_or;
    assume H10;
    assume H11;
    set H0l' ≔ (1 * ((— (p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4)) - (— 1)));
    set H0r' ≔ (1 * 0);
    set H1l' ≔ (1 * ((— (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1)) - (— 1)));
    set H1r' ≔ (1 * 0);
    set H2l' ≔ (1 * ((— ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4))) - (— ((— 1) * 1))));
    set H2r' ≔ (1 * 0);
    set H3l' ≔ (1 * ((— ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4))) - (— ((— 1) * 1))));
    set H3r' ≔ (1 * 0);
    set H4l' ≔ (1 * ((— ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4))) - (— ((— 1) * 1))));
    set H4r' ≔ (1 * 0);
    set H5l' ≔ (1 * ((— ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4))) - (— ((— 1) * 1))));
    set H5r' ≔ (1 * 0);
    set H6l' ≔ (1 * ((— ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4))) - (— ((— 1) * 1))));
    set H6r' ≔ (1 * 0);
    set H7l' ≔ (1 * ((— ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4))) - (— ((— 1) * 1))));
    set H7r' ≔ (1 * 0);
    set H8l' ≔ (1 * ((— (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0)) - (— 1)));
    set H8r' ≔ (1 * 0);
    set H9l' ≔ (1 * ((— (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2)) - (— 1)));
    set H9r' ≔ (1 * 0);
    set H10l' ≔ (1 * ((— (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (— 2)));
    set H10r' ≔ (1 * (0 + 1));
    set H11l' ≔ (1 * (((p_0_4 + p_1_4 + p_2_4 + p_3_4 + p_4_4 + p_5_4) + (p_0_1 + p_1_1 + p_2_1 + p_3_1 + p_4_1 + p_5_1) + ((— 1) * (p_5_0 + p_5_1 + p_5_2 + p_5_3 + p_5_4)) + ((— 1) * (p_4_0 + p_4_1 + p_4_2 + p_4_3 + p_4_4)) + ((— 1) * (p_3_0 + p_3_1 + p_3_2 + p_3_3 + p_3_4)) + ((— 1) * (p_2_0 + p_2_1 + p_2_2 + p_2_3 + p_2_4)) + ((— 1) * (p_1_0 + p_1_1 + p_1_2 + p_1_3 + p_1_4)) + ((— 1) * (p_0_0 + p_0_1 + p_0_2 + p_0_3 + p_0_4)) + (p_0_0 + p_1_0 + p_2_0 + p_3_0 + p_4_0 + p_5_0) + (p_0_2 + p_1_2 + p_2_2 + p_3_2 + p_4_2 + p_5_2) + (p_0_3 + p_1_3 + p_2_3 + p_3_3 + p_4_3 + p_5_3)) - (1 + 1 + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + ((— 1) * 1) + 1 + 1 + 2)));
    set H11r' ≔ (1 * 0);
    set l ≔ (H0l' + H1l' + H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l');
    set r ≔ (H0r' + H1r' + H2r' + H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r');
    have sum : π (l ≥ r) {
        refine (Zsum_geq_s H0l' H0r' (H1l' + H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H1r' + H2r' + H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H0 (Zsum_geq_s H1l' H1r' (H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H2r' + H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H1 (Zsum_geq_s H2l' H2r' (H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H3r' + H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H2 (Zsum_geq_s H3l' H3r' (H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H4r' + H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H3 (Zsum_geq_s H4l' H4r' (H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H5r' + H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H4 (Zsum_geq_s H5l' H5r' (H6l' + H7l' + H8l' + H9l' + H10l' + H11l') (H6r' + H7r' + H8r' + H9r' + H10r' + H11r') H5 (Zsum_geq_s H6l' H6r' (H7l' + H8l' + H9l' + H10l' + H11l') (H7r' + H8r' + H9r' + H10r' + H11r') H6 (Zsum_geq_s H7l' H7r' (H8l' + H9l' + H10l' + H11l') (H8r' + H9r' + H10r' + H11r') H7 (Zsum_geq_s H8l' H8r' (H9l' + H10l' + H11l') (H9r' + H10r' + H11r') H8 (Zsum_geq_s H9l' H9r' (H10l' + H11l') (H10r' + H11r') H9 (Zsum_geq_s H10l' H10r' H11l' H11r' H10 H11)))))))))));
    };
    refine sum _;
    rewrite left reify_correct l;
    rewrite left reify_correct r;
    set l' ≔ reify l;
    set r' ≔ reify r;
    rewrite eta_prod l';
    rewrite eta_prod r';
    rewrite left norm_correct (l' ₁) (l' ₂) _ { refine ⊤ᵢ }    { print; apply ⊤ᵢ };
};
simplify;
rewrite or_identity_r;
apply (π̇ₗ Hla);
end;
