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

Definition sll_append : val :=
rec: "sll_append" "x1" "r" :=
let: "x22" := ! ("r") in
#();; 
if: "x1" = #null_loc
then (
#()
)
else (
let: "vx12" := ! ("x1") in
#();; 
let: "nxtx12" := ! ("x1" +ₗ #1) in
#();; 
"sll_append" "nxtx12" "r";; 
let: "y12" := ! ("r") in
#();; 
("x1" +ₗ #1) <- ("y12");; 
("r") <- ("x1");; 
#()
).


Lemma sll_append_spec :
∀ (r : loc) (x2 : loc) (s2 : (list Z)) (_alpha_514 : sll_card) (x1 : loc) (s1 : (list Z)) (_alpha_515 : sll_card),
{{{ (sll x1 s1 _alpha_514) ∗ (sll x2 s2 _alpha_515) ∗ r ↦ #x2 }}}
  sll_append #x1 #r
{{{ RET #(); ∃ (y : loc) (_alpha_516 : sll_card) (s : (list Z)), ⌜(s = (s1 ++ s2))⌝ ∗ (sll y s _alpha_516) ∗ r ↦ #y }}}.
Proof.
iIntros (r x2 s2 _alpha_514 x1 s1 _alpha_515 ϕ) "(iH1 & iH2 & iH3) Post".
iRewriteHyp.
iLöb as "sll_append" forall (r x2 s2 _alpha_514 x1 s1 _alpha_515 ϕ).
ssl_begin.

iRename select (r ↦ _)%I into "iH4".
iDestruct (NilNotLval with "iH4") as "[iH4 %]".

try rename x2 into x22.
ssl_load.
iRename select ((sll x1 s1 _alpha_514))%I into "iH5".
ssl_if Cond_iH5.

iDestruct (sll_card_0_learn with "iH5") as "[iH5 %iH5_eqn]".
rewrite iH5_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_0_open).
iDestruct "iH5" as  "(%iH6 & %iH7)".
try wp_pures.
iFindApply.
iExists x22.
iExists _alpha_515.
iExists ([] ++ s2).
ssl_finish.


iDestruct (sll_card_1_learn with "iH5") as "[iH5 %iH5_eqn]".

edestruct iH5_eqn as [_alpha_513x1 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite sll_card_1_open).
iDestruct "iH5" as (vx1 s1x1 nxtx1) "((%iH8 & %iH9) & (iH10 & iH11 & iH12 & iH13))".
try rename vx1 into vx12.
ssl_load.
try rename nxtx1 into nxtx12.
ssl_load.
wp_apply ("sll_append" $! (r) (x22) (s2) (_alpha_513x1) (nxtx12) (s1x1) (_alpha_515) with "[$] [$] [$]").


iIntros  "iH17".
iDestruct "iH17" as (y1 _alpha_5161 s3) "(%iH14 & (iH15 & iH16))".
try wp_pures.
try rename y1 into y12.
ssl_load.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists x1.
iExists (sll_card_1 _alpha_5161 : sll_card).
iExists (([vx12] ++ s1x1) ++ s2).
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx12.
pull_out_exist.
iExists (s1x1 ++ s2).
pull_out_exist.
iExists y12.
ssl_finish.
Qed.
