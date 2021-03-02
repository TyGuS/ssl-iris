From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition dll_append : val :=
rec: "dll_append" "x1" "r" :=
let: "x22" := ! ("r") in
#();; 
if: "x1" = #null_loc
then (
#()
)
else (
let: "vx12" := ! ("x1") in
#();; 
let: "wx12" := ! ("x1" +ₗ #1) in
#();; 
let: "a2" := ! ("x1" +ₗ #2) in
#();; 
"dll_append" "wx12" "r";; 
let: "y12" := ! ("r") in
#();; 
if: "y12" = #null_loc
then (
("x1" +ₗ #1) <- (#null_loc);; 
("r") <- ("x1");; 
#()
)
else (
let: "vy122" := ! ("y12") in
#();; 
let: "wy122" := ! ("y12" +ₗ #1) in
#();; 
let: "c12" := ! ("y12" +ₗ #2) in
#();; 
("y12" +ₗ #2) <- ("x1");; 
("x1" +ₗ #1) <- ("y12");; 
("r") <- ("x1");; 
#()
)
).


Lemma dll_append_spec :
∀ (r : loc) (x2 : loc) (s2 : (list Z)) (a : loc) (x1 : loc) (s1 : (list Z)) (_alpha_535 : dll_card) (b : loc) (_alpha_534 : dll_card),
{{{ (dll x1 a s1 _alpha_534) ∗ (dll x2 b s2 _alpha_535) ∗ r ↦ #x2 }}}
  dll_append #x1 #r
{{{ RET #(); ∃ (c : loc) (y : loc) (s : (list Z)) (_alpha_536 : dll_card), ⌜(s = (s1 ++ s2))⌝ ∗ (dll y c s _alpha_536) ∗ r ↦ #y }}}.
Proof.
iIntros (r x2 s2 a x1 s1 _alpha_535 b _alpha_534 ϕ) "(iH1 & iH2 & iH3) Post".
iRewriteHyp.
iLöb as "dll_append" forall (r x2 s2 a x1 s1 _alpha_535 b _alpha_534 ϕ).
ssl_begin.
try rename x2 into x22.
ssl_load.
iRename select ((dll x1 a s1 _alpha_534))%I into "iH4".
ssl_if Cond_iH4.

iDestruct (dll_card_0_learn with "iH4") as "[iH4 %iH4_eqn]".
rewrite iH4_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_0_open).
iDestruct "iH4" as  "(%iH5 & %iH6)".
try wp_pures.
iFindApply.
iExists b.
iExists x22.
iExists ([] ++ s2).
iExists _alpha_535.
ssl_finish.


iDestruct (dll_card_1_learn with "iH4") as "[iH4 %iH4_eqn]".

edestruct iH4_eqn as [_alpha_533x1 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_1_open).
iDestruct "iH4" as (vx1 s1x1 wx1) "((%iH7 & %iH8) & (iH9 & iH10 & iH11 & iH12 & iH13))".
try rename vx1 into vx12.
ssl_load.
try rename wx1 into wx12.
ssl_load.
try rename a into a2.
ssl_load.
wp_apply ("dll_append" $! (r) (x22) (s2) (x1) (wx12) (s1x1) (_alpha_535) (b) (_alpha_533x1) with "[$] [$] [$]").


iIntros  "iH17".
iDestruct "iH17" as (c1 y1 s3 _alpha_5361) "(%iH14 & (iH15 & iH16))".
try wp_pures.
try rename y1 into y12.
ssl_load.
iRename select ((dll y12 c1 (s1x1 ++ s2) _alpha_5361))%I into "iH18".
ssl_if Cond_iH18.

iDestruct (dll_card_0_learn with "iH18") as "[iH18 %iH18_eqn]".
rewrite iH18_eqn; last by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_0_open).
iDestruct "iH18" as  "(%iH19 & %iH20)".
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists a2.
iExists x1.
iExists (([vx12] ++ s1x1) ++ s2).
iExists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists vx12.
pull_out_exist.
iExists [].
pull_out_exist.
iExists null_loc.
ssl_finish.
ssl_rewrite_first_heap dll_card_0_open.
ssl_finish.


iDestruct (dll_card_1_learn with "iH18") as "[iH18 %iH18_eqn]".

edestruct iH18_eqn as [_alpha_533y12 ->]; first by safeDispatchPure.
tac_except_post ltac:(rewrite dll_card_1_open).
iDestruct "iH18" as (vy12 s1y12 wy12) "((%iH21 & %iH22) & (iH23 & iH24 & iH25 & iH26 & iH27))".
try rename vy12 into vy122.
ssl_load.
try rename wy12 into wy122.
ssl_load.
try rename c1 into c12.
ssl_load.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists a2.
iExists x1.
iExists (([vx12] ++ s1x1) ++ s2).
iExists (dll_card_1 (dll_card_1 _alpha_533y12 : dll_card) : dll_card).
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists vx12.
pull_out_exist.
iExists ([vy122] ++ s1y12).
pull_out_exist.
iExists y12.
ssl_finish.
ssl_rewrite_first_heap dll_card_1_open.
pull_out_exist.
iExists vy122.
pull_out_exist.
iExists s1y12.
pull_out_exist.
iExists wy122.
ssl_finish.
Qed.
