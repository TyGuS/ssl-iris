From SSL_Iris Require Import core.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Export tactics coq_tactics ltac_tactics reduction.
From iris.heap_lang Require Import lang notation proofmode.
Require Import common.
From iris_string_ident Require Import ltac2_string_ident.
From Hammer Require Import Hammer.
Context `{!heapG Σ}.
Set Default Proof Using "Type".


Definition swap : val :=
rec: "swap" "x" "y" :=
let: "a2" := ! ("x") in
#();; 
let: "b2" := ! ("y") in
#();; 
("x") <- ("b2");; 
("y") <- ("a2");; 
#().


Lemma swap_spec :
∀ (x : loc) (a : loc) (y : loc) (b : loc),
{{{ x ↦ #a ∗ y ↦ #b }}}
  swap #x #y
{{{ RET #(); x ↦ #b ∗ y ↦ #a }}}.
Proof.
iIntros (x a y b ϕ) "(iH1 & iH2) Post".
iRewriteHyp.
iLöb as "swap" forall (x a y b ϕ).
ssl_begin.
try rename a into a2.
ssl_load.
try rename b into b2.
ssl_load.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
ssl_finish.
Qed.
