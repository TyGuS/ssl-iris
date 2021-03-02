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

Definition sll_copy : val :=
rec: "sll_copy" "r" :=
let: "x2" := ! ("r") in
#();; 
if: "x2" = #null_loc
then (
#()
)
else (
let: "vx22" := ! ("x2") in
#();; 
let: "nxtx22" := ! ("x2" +ₗ #1) in
#();; 
("r") <- ("nxtx22");; 
"sll_copy" "r";; 
let: "y12" := ! ("r") in
#();; 
let: "y2" := AllocN (#2) (#()) in
#();; 
("r") <- ("y2");; 
("y2" +ₗ #1) <- ("y12");; 
("y2") <- ("vx22");; 
#()
).


Lemma sll_copy_spec :
∀ (r : loc) (x : loc) (s : (list Z)) (a : sll_card),
{{{ r ↦ #x ∗ (sll x s a) }}}
  sll_copy #r
{{{ RET #(); ∃ (b : sll_card) (y : loc), r ↦ #y ∗ (sll x s a) ∗ (sll y s b) }}}.
Proof.
iIntros (r x s a ϕ) "(iH1 & iH2) Post".
iRewriteHyp.
iLöb as "sll_copy" forall (r x s a ϕ).
ssl_begin.

iRename select (r ↦ _)%I into "iH3".
iDestruct (NilNotLval with "iH3") as "[iH3 %]".

try rename x into x2.
ssl_load.
iRename select ((sll x2 s a))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (sll_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6)".
try wp_pures.
iFindApply.
iExists (sll_card_0  : sll_card).
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.


iDestruct (sll_card_1_learn with "iH4") as "[iH4 %iH4_eqn]".

edestruct iH4_eqn as [_alpha_513x2 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_1_open).
iDestruct "iH4" as (vx2 s1x2 nxtx2) "((%iH7 & %iH8) & (iH9 & iH10 & iH11 & iH12))".
try rename vx2 into vx22.
ssl_load.
try rename nxtx2 into nxtx22.
ssl_load.
ssl_store.
wp_apply ("sll_copy" $! (r) (nxtx22) (s1x2) (_alpha_513x2) with "[$] [$]").


iIntros  "iH16".
iDestruct "iH16" as (b1 y1) "(iH13 & iH14 & iH15)".
try wp_pures.
try rename y1 into y12.
ssl_load.
wp_alloc y2 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.


iRename select (y2 ↦ _)%I into "iH17".
iDestruct (NilNotLval with "iH17") as "[iH17 %]".

ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists (sll_card_1 b1 : sll_card).
iExists y2.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists s1x2.
pull_out_exist.
iExists nxtx22.
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists s1x2.
pull_out_exist.
iExists y12.
ssl_finish.
Qed.
