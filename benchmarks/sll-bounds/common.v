From SSL_Iris Require Import core.
From iris.heap_lang Require Import lang notation proofmode.
From iris_string_ident Require Import ltac2_string_ident.
Section common.
Context `{!heapG Σ}.
Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (len: Z) (lo: Z) (hi: Z) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (hi = 0) ∧ (len = 0) ∧ (lo = 7)⌝
    | sll_card_1 _alpha_513 => ∃ (len1 : Z) (v : Z) (hi1 : Z) (lo1 : Z) (nxt : loc), ⌜~ (x = null_loc) ∧ (0 ≤ len1)%Z ∧ (0 ≤ v)%Z ∧ (hi = if (Z.leb hi1 v) then v else hi1) ∧ (len = (1 + len1)%Z) ∧ (lo = if (Z.leb v lo1) then v else lo1) ∧ (v ≤ 7)%Z⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt len1 lo1 hi1 _alpha_513)
end.

Global Opaque sll.

Lemma sll_card_0_learn (x: loc) (len: Z) (lo: Z) (hi: Z) self_card:
sll x len lo hi self_card  ⊢ sll x len lo hi self_card ∗ ⌜(x = null_loc) -> self_card = sll_card_0⌝.
Proof.
Transparent sll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & % & % & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (len1 v hi1 lo1 nxt) "((% & % & % & % & % & % & %) & (? & ? & ? & ?))".
   iSplitL.
   iExists len1, v, hi1, lo1, nxt. iFrame. eauto.
   eauto.
Global Opaque sll.
Qed.

Lemma sll_card_1_learn (x: loc) (len: Z) (lo: Z) (hi: Z) self_card:
sll x len lo hi self_card  ⊢ sll x len lo hi self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_513, self_card = (sll_card_1 _alpha_513)⌝.
Proof.
Transparent sll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & % & % & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (len1 v hi1 lo1 nxt) "((% & % & % & % & % & % & %) & (? & ? & ? & ?))".
   iSplitL.
   iExists len1, v, hi1, lo1, nxt. iFrame. eauto.
   eauto.
Global Opaque sll.
Qed.

Lemma sll_card_0_open  (x: loc) (len: Z) (lo: Z) (hi: Z) :
sll x len lo hi (sll_card_0 ) = (⌜(x = null_loc) ∧ (hi = 0) ∧ (len = 0) ∧ (lo = 7)⌝)%I.
Proof. auto. Qed.

Lemma sll_card_1_open (_alpha_513 : sll_card) (x: loc) (len: Z) (lo: Z) (hi: Z) :
sll x len lo hi (sll_card_1 _alpha_513) = (∃ (len1 : Z) (v : Z) (hi1 : Z) (lo1 : Z) (nxt : loc), ⌜~ (x = null_loc) ∧ (0 ≤ len1)%Z ∧ (0 ≤ v)%Z ∧ (hi = if (Z.leb hi1 v) then v else hi1) ∧ (len = (1 + len1)%Z) ∧ (lo = if (Z.leb v lo1) then v else lo1) ∧ (v ≤ 7)%Z⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt len1 lo1 hi1 _alpha_513))%I.
Proof. auto. Qed.

End common.