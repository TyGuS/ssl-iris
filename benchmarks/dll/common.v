From SSL_Iris Require Import core.
From iris.heap_lang Require Import lang notation proofmode.
From iris_string_ident Require Import ltac2_string_ident.
Section common.
Context `{!heapG Σ}.
Inductive dll_card : Set :=
    | dll_card_0 : dll_card
    | dll_card_1 : dll_card -> dll_card.

Fixpoint dll (x: loc) (z: loc) (s: (list Z)) (self_card: dll_card) { struct self_card } : iProp Σ := match self_card with
    | dll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | dll_card_1 _alpha_533 => ∃ (v : Z) (s1 : (list Z)) (w : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #w ∗ (x +ₗ 2) ↦ #z ∗ (dll w x s1 _alpha_533)
end.

Global Opaque dll.

Lemma dll_card_0_learn (x: loc) (z: loc) (s: (list Z)) self_card:
dll x z s self_card  ⊢ dll x z s self_card ∗ ⌜(x = null_loc) -> self_card = dll_card_0⌝.
Proof.
Transparent dll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 w) "((% & %) & (? & ? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, w. iFrame. eauto.
   eauto.
Global Opaque dll.
Qed.

Lemma dll_card_1_learn (x: loc) (z: loc) (s: (list Z)) self_card:
dll x z s self_card  ⊢ dll x z s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_533, self_card = (dll_card_1 _alpha_533)⌝.
Proof.
Transparent dll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 w) "((% & %) & (? & ? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, w. iFrame. eauto.
   eauto.
Global Opaque dll.
Qed.

Lemma dll_card_0_open  (x: loc) (z: loc) (s: (list Z)) :
dll x z s (dll_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma dll_card_1_open (_alpha_533 : dll_card) (x: loc) (z: loc) (s: (list Z)) :
dll x z s (dll_card_1 _alpha_533) = (∃ (v : Z) (s1 : (list Z)) (w : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #w ∗ (x +ₗ 2) ↦ #z ∗ (dll w x s1 _alpha_533))%I.
Proof. auto. Qed.

End common.