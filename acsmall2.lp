require open aclia.Prop;
require open aclia.Set;
require open aclia.Eq;
require open aclia.Nat;
require open aclia.Z;
// require open aclia.Classic;
// require open aclia.Alethe;
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

symbol a ≔ H0l' + H1l' + H2l' + H3l' + H4l' + H5l' + H6l' + H7l' + H8l' + H9l' + H10l' + H11l';

//compute reify a;

//compute val(reify a);

compute let e ≔ reify a in val (norm (e ₁) ‚ (e ₂));
