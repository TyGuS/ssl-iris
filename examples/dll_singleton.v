From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.

From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".
Axiom NilNotLval:
  forall x v,
  x ↦ v -∗ x ↦ v ∗ ⌜x ≠ null_loc⌝.
Inductive dll_card : Set :=
    | dll_card_0 : dll_card
    | dll_card_1 : dll_card -> dll_card.

Fixpoint dll (x: loc) (z: loc) (s: (list Z)) (self_card: dll_card) { struct self_card } : iProp Σ := match self_card with
    | dll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | dll_card_1 _alpha_513 => ∃ (v : Z) (s1 : (list Z)) (w : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #w ∗ (x +ₗ 2) ↦ #z ∗ (dll w x s1 _alpha_513)
end.

Global Opaque dll.

Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (s: (list Z)) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | sll_card_1 _alpha_514 => ∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_514)
end.

Global Opaque sll.

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
dll x z s self_card  ⊢ dll x z s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_513, self_card = (dll_card_1 _alpha_513)⌝.
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

Lemma dll_card_1_open (_alpha_513 : dll_card) (x: loc) (z: loc) (s: (list Z)) :
dll x z s (dll_card_1 _alpha_513) = (∃ (v : Z) (s1 : (list Z)) (w : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #w ∗ (x +ₗ 2) ↦ #z ∗ (dll w x s1 _alpha_513))%I.
Proof. auto. Qed.

Lemma sll_card_0_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜(x = null_loc) -> self_card = sll_card_0⌝.
Proof.
Transparent sll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, nxt. iFrame. eauto.
   eauto.
Global Opaque sll.
Qed.

Lemma sll_card_1_learn (x: loc) (s: (list Z)) self_card:
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_514, self_card = (sll_card_1 _alpha_514)⌝.
Proof.
Transparent sll.
destruct self_card; iIntros "P".
- iDestruct "P" as  "(% & %)".
   iSplitL.
    iFrame. eauto.
   eauto.
- iDestruct "P" as (v s1 nxt) "((% & %) & (? & ? & ? & ?))".
   iSplitL.
   iExists v, s1, nxt. iFrame. eauto.
   eauto.
Global Opaque sll.
Qed.

Lemma sll_card_0_open  (x: loc) (s: (list Z)) :
sll x s (sll_card_0 ) = (⌜(x = null_loc) ∧ (s = [])⌝)%I.
Proof. auto. Qed.

Lemma sll_card_1_open (_alpha_514 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_514) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_514))%I.
Proof. auto. Qed.

Definition dll_singleton : val :=
rec: "dll_singleton" "x" "r" :=
let: "a2" := ! ("r") in
#();; 
let: "y2" := AllocN (#3) (#()) in
#();; 
("r") <- ("y2");; 
("y2" +ₗ #1) <- (#null_loc);; 
("y2" +ₗ #2) <- (#null_loc);; 
("y2") <- ("x");; 
#().


Lemma dll_singleton_spec :
∀ (r : loc) (a : loc) (x : Z),
{{{ r ↦ #a }}}
  dll_singleton #x #r
{{{ RET #(); ∃ (elems : (list Z)) (y : loc) (_alpha_515 : dll_card), ⌜(elems = [x])⌝ ∗ r ↦ #y ∗ (dll y null_loc elems _alpha_515) }}}.
Proof.
iIntros (r a x ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "dll_singleton" forall (r a x ϕ).
ssl_begin.

iRename select (r ↦ _)%I into "iH2".
iDestruct (NilNotLval with "iH2") as "[iH2 %]".

try rename a into a2.
ssl_load.
wp_alloc y2 as "?"; try by safeDispatchPure.
wp_pures.
do 3 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.


iRename select (y2 ↦ _)%I into "iH3".
iDestruct (NilNotLval with "iH3") as "[iH3 %]".

ssl_store.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists [x].
iExists y2.
iExists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists x.
pull_out_exist.
iExists [].
pull_out_exist.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap dll_card_0_open.
ssl_finish.
Qed.
