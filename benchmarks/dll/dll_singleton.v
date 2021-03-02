From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


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
{{{ RET #(); ∃ (elems : (list Z)) (_alpha_538 : dll_card) (y : loc), ⌜(elems = [x])⌝ ∗ r ↦ #y ∗ (dll y null_loc elems _alpha_538) }}}.
Proof.
iIntros (r a x ϕ) "iH1 Post".
iRewriteHyp.
iLöb as "dll_singleton" forall (r a x ϕ).
ssl_begin.
try rename a into a2.
ssl_load.
wp_alloc y2 as "?"; try by safeDispatchPure.
wp_pures.
do 3 try rewrite array_cons. iSplitAllHyps. try rewrite array_nil.
try rewrite !loc_add_assoc !Z.add_1_r.

movePure.
ssl_store.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
iExists [x].
iExists (dll_card_1 (dll_card_0  : dll_card) : dll_card).
iExists y2.
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
