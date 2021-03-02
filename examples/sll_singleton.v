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
Inductive sll_card : Set :=
    | sll_card_0 : sll_card
    | sll_card_1 : sll_card -> sll_card.

Fixpoint sll (x: loc) (s: (list Z)) (self_card: sll_card) { struct self_card } : iProp Σ := match self_card with
    | sll_card_0  => ⌜(x = null_loc) ∧ (s = [])⌝
    | sll_card_1 _alpha_513 => ∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_513)
end.

Global Opaque sll.

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
sll x s self_card  ⊢ sll x s self_card ∗ ⌜~ (x = null_loc) -> ∃ _alpha_513, self_card = (sll_card_1 _alpha_513)⌝.
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

Lemma sll_card_1_open (_alpha_513 : sll_card) (x: loc) (s: (list Z)) :
sll x s (sll_card_1 _alpha_513) = (∃ (v : Z) (s1 : (list Z)) (nxt : loc), ⌜~ (x = null_loc) ∧ (s = ([v] ++ s1))⌝ ∗ ⌜True⌝ ∗ x ↦ #v ∗ (x +ₗ 1) ↦ #nxt ∗ (sll nxt s1 _alpha_513))%I.
Proof. auto. Qed.

Definition sll_singleton : val :=
rec: "sll_singleton" "x" "p" :=
let: "a2" := ! ("p") in
#();; 
let: "y2" := AllocN (#2) (#()) in
#();; 
("p") <- ("y2");; 
("y2" +ₗ #1) <- (#null_loc);; 
("y2") <- ("x");; 
#().


Lemma sll_singleton_spec :
∀ (p : loc) (a : loc) (x : Z),
{{{ p ↦ #a }}}
  sll_singleton #x #p
{{{ RET #(); ∃ (elems : (list Z)) (_alpha_514 : sll_card) (y : loc), ⌜(elems = [x])⌝ ∗ p ↦ #y ∗ (sll y elems _alpha_514) }}}.
Proof.
iIntros (p a x ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "sll_singleton" forall (p a x ϕ).
ssl_begin.

iRename select (p ↦ _)%I into "iH2".
iDestruct (NilNotLval with "iH2") as "[iH2 %]".

try rename a into a2.
ssl_load.
wp_alloc y2 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.


iRename select (y2 ↦ _)%I into "iH3".
iDestruct (NilNotLval with "iH3") as "[iH3 %]".

ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists [x].
iExists (sll_card_1 (sll_card_0  : sll_card) : sll_card).
iExists y2.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists x.
pull_out_exist.
iExists [].
pull_out_exist.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.
Qed.
