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


Definition swap2 : val :=
rec: "swap2" "x" "z" "y" "t" :=
let: "a2" := ! ("x") in
#();; 
let: "c2" := ! ("y") in
#();; 
let: "b2" := ! ("z") in
#();; 
let: "q2" := ! ("t") in
#();; 
("x") <- ("q2");; 
("y") <- ("b2");; 
("z") <- ("c2");; 
("t") <- ("a2");; 
#().


Lemma swap2_spec :
∀ (x : loc) (a : loc) (c : loc) (t : loc) (z : loc) (y : loc) (b : loc) (q : loc),
{{{ x ↦ #a ∗ y ↦ #c ∗ z ↦ #b ∗ t ↦ #q }}}
  swap2 #x #z #y #t
{{{ RET #(); x ↦ #q ∗ z ↦ #c ∗ t ↦ #a ∗ y ↦ #b }}}.
Proof.
iIntros (x a c t z y b q ϕ) "(iH1 & iH2 & iH3 & iH4) Post".
iRewriteHyp.
iLöb as "swap2" forall (x a c t z y b q ϕ).
ssl_begin.

iRename select (x ↦ _)%I into "iH5".
iDestruct (NilNotLval with "iH5") as "[iH5 %]".


iRename select (y ↦ _)%I into "iH6".
iDestruct (NilNotLval with "iH6") as "[iH6 %]".


iRename select (z ↦ _)%I into "iH7".
iDestruct (NilNotLval with "iH7") as "[iH7 %]".


iRename select (t ↦ _)%I into "iH8".
iDestruct (NilNotLval with "iH8") as "[iH8 %]".

try rename a into a2.
ssl_load.
try rename c into c2.
ssl_load.
try rename b into b2.
ssl_load.
try rename q into q2.
ssl_load.
ssl_store.
ssl_store.
ssl_store.
ssl_store.
try wp_pures.
iFindApply.
ssl_finish.
Qed.
