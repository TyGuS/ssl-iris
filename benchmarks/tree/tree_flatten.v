From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".

Axiom sll_append: val.

Axiom sll_append_spec :
∀ (x2 : loc) (ret : loc) (s2 : (list Z)) (x1 : loc) (s1 : (list Z)) (_alpha_554 : sll_card) (_alpha_555 : sll_card),
{{{ (sll x1 s1 _alpha_554) ∗ (sll x2 s2 _alpha_555) ∗ ret ↦ #x2 }}}
  sll_append #x1 #ret
{{{ RET #(); ∃ (y : loc) (_alpha_556 : sll_card) (s : (list Z)), ⌜(s = (s1 ++ s2))⌝ ∗ (sll y s _alpha_556) ∗ ret ↦ #y }}}.

Definition tree_flatten : val :=
rec: "tree_flatten" "z" :=
let: "x2" := ! ("z") in
#();; 
if: "x2" = #null_loc
then (
#()
)
else (
let: "vx22" := ! ("x2") in
#();; 
let: "lx22" := ! ("x2" +ₗ #1) in
#();; 
let: "rx22" := ! ("x2" +ₗ #2) in
#();; 
("z") <- ("lx22");; 
"tree_flatten" "z";; 
let: "y12" := ! ("z") in
#();; 
("z") <- ("rx22");; 
"tree_flatten" "z";; 
let: "y22" := ! ("z") in
#();; 
sll_append "y12" "z";; 
let: "y32" := ! ("z") in
#();; 
let: "y4" := AllocN (#2) (#()) in
#();; 
Free ("x2");; 
Free ("x2" +ₗ #1);; 
Free ("x2" +ₗ #2);; 
("z") <- ("y4");; 
("y4" +ₗ #1) <- ("y32");; 
("y4") <- ("vx22");; 
#()
).


Lemma tree_flatten_spec :
∀ (z : loc) (x : loc) (s : (list Z)) (_alpha_557 : tree_card),
{{{ z ↦ #x ∗ (tree x s _alpha_557) }}}
  tree_flatten #z
{{{ RET #(); ∃ (y : loc) (_alpha_558 : sll_card), z ↦ #y ∗ (sll y s _alpha_558) }}}.
Proof.
iIntros (z x s _alpha_557 ϕ) "(iH1 & iH2) Post".
iRewriteHyp.
iLöb as "tree_flatten" forall (z x s _alpha_557 ϕ).
ssl_begin.
try rename x into x2.
ssl_load.
iRename select ((tree x2 s _alpha_557))%I into "iH3".
ssl_if Cond_iH3.

iDestruct (tree_card_0_learn with "iH3") as "[iH3 %iH3_eqn]".
rewrite iH3_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_0_open).
iDestruct "iH3" as  "(%iH4 & %iH5)".
try wp_pures.
iFindApply.
iExists null_loc.
iExists (sll_card_0  : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_0_open.
ssl_finish.


iDestruct (tree_card_2_learn with "iH3") as "[iH3 %iH3_eqn]".

edestruct iH3_eqn as [_alpha_550x2 [_alpha_549x2 ->]]; first by safeDispatchPure.
tac_except_post ltac:(rewrite tree_card_2_open).
iDestruct "iH3" as (vx2 s1x2 s2x2 lx2 rx2) "((%iH6 & %iH7) & (iH8 & iH9 & iH10 & iH11 & iH12 & iH13))".
try rename vx2 into vx22.
ssl_load.
try rename lx2 into lx22.
ssl_load.
try rename rx2 into rx22.
ssl_load.
ssl_store.
wp_apply ("tree_flatten" $! (z) (lx22) (s1x2) (_alpha_549x2) with "[$] [$]").


iIntros  "iH16".
iDestruct "iH16" as (y1 _alpha_5581) "(iH14 & iH15)".
try wp_pures.
try rename y1 into y12.
ssl_load.
ssl_store.
wp_apply ("tree_flatten" $! (z) (rx22) (s2x2) (_alpha_550x2) with "[$] [$]").


iIntros  "iH19".
iDestruct "iH19" as (y2 _alpha_5582) "(iH17 & iH18)".
try wp_pures.
try rename y2 into y22.
ssl_load.
wp_apply (sll_append_spec  (y22) (z) (s2x2) (y12) (s1x2) (_alpha_5581) (_alpha_5582) with "[$]").


iIntros  "iH23".
iDestruct "iH23" as (y3 _alpha_556 s3) "(%iH20 & (iH21 & iH22))".
try wp_pures.
try rename y3 into y32.
ssl_load.
wp_alloc y4 as "?"; try by safeDispatchPure.
wp_pures.
do 2 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.

movePure.
ssl_free.
ssl_free.
ssl_free.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists y4.
iExists (sll_card_1 _alpha_556 : sll_card).
ssl_finish.
ssl_rewrite_first_heap sll_card_1_open.
pull_out_exist.
iExists vx22.
pull_out_exist.
iExists (s1x2 ++ s2x2).
pull_out_exist.
iExists y32.
ssl_finish.
Qed.
